use super::{IC3, frame::Frame, proofoblig::Po};
use crate::{
    BlWitness, Engine, McProof, McResult, McWitness,
    ic3::{mab::balanced_params, solver::inductive_core},
};
use log::{debug, info, trace};
use logicrs::{LitOrdVec, LitVec};
use std::time::Instant;

impl Engine for IC3 {
    /// The outer layer of IC3: block existing bads, find bads in current frame, extend the frame
    fn check(&mut self) -> McResult {
        if self.solvers.len() == 0 {
            info!("ic3 found a counterexample at depth 0");
            return McResult::Unsafe(0);
        }
        let start = Instant::now();
        let mut last_sec = 0;
        loop {
            let now_sec = start.elapsed().as_secs();
            if now_sec > self.time_limit {
                return McResult::Unknown(self.level());
            }
            if now_sec - last_sec >= 10 {
                info!("{}", self.frame.statistic(true));
                last_sec = now_sec;
            }

            // block existing proof obligations
            let mut assump = LitVec::new();
            while let Some(mut po) = self.obligations.pop(self.level()) {
                // intersects with init; failed if on frame 0
                // cube_subsume_init only sees constant latch initializers. INN
                // adds latches whose initial values are constrained by rel, so
                // confirm those candidates with frame 0 before invoking CEGAR.
                if self.ts.cube_subsume_init(&po.state)
                    && (!self.inn
                        || (!self.abs_cst && !self.abs_trans)
                        || self.solvers[0].dcs_solve_nocst(po.state.as_litvec()))
                {
                    if self.abs_cst || self.abs_trans {
                        self.obligations.add(po.clone());
                        if self.check_witness_by_bmc(po.depth) {
                            info!("ic3 localabst cex verified at depth {}", po.depth);
                            return McResult::Unsafe(po.depth);
                        }
                        self.obligations.clear();
                        for f in self.frame.iter_mut() {
                            for l in f.iter_mut() {
                                l.1 = None;
                            }
                        }
                        continue;
                    } else if po.frame == 0 {
                        self.obligations.add(po.clone());
                        return McResult::Unsafe(po.depth);
                    }
                    debug_assert_eq!(self.solvers[0].dcs_solve_nocst(po.state.as_litvec()), false);
                }

                if let Some((bf, _)) = self.frame.trivial_contained(Some(po.frame), &po.state) {
                    if let Some(bf) = bf {
                        po.push_to(bf + 1);
                        self.obligations.add(po);
                    }
                    continue;
                }
                po.act += 1.0;
                if self.drop_po && po.act > 20.0 {
                    continue;
                }

                let mut ordered_cube = po.state.as_litvec().clone();
                self.activity.sort_by_activity(&mut ordered_cube, false);
                let slv = &mut self.solvers[po.frame - 1];
                assump.clear();
                assump.extend(ordered_cube.iter().map(|l| self.ts.next(*l)));
                if slv.dcs_solve_nocst(&assump) {
                    let (model, inputs) = self.get_pred(po.frame, &assump, true);
                    self.obligations.add(Po::new(
                        po.frame - 1,
                        LitOrdVec::new(model),
                        inputs,
                        po.depth + 1,
                        Some(po.clone()),
                    ));
                    self.obligations.add(po);
                    continue;
                }

                let lvl = self.level();
                let mut mab_input = None;
                let (parameter, arm) = if self.dynamic {
                    (balanced_params(&po, 0.45), 0)
                } else if let Some(mab) = &mut self.mab {
                    mab_input = Some(mab.encode(lvl, &self.frame, &po));
                    mab.infer(mab_input.as_ref().unwrap(), &po)
                } else {
                    (self.default_mic, 0)
                };

                let lemma = if let Some(mut mic) =
                    inductive_core(&mut self.solvers[po.frame - 1], &self.ts, &ordered_cube)
                {
                    let old_sz = mic.len();
                    mic = self.mic(po.frame, mic, &mut LitVec::new(), parameter);
                    let (frame, mic) = self.push_lemma(po.frame, mic);
                    if let Some(input) = &mab_input {
                        let mab = self.mab.as_mut().unwrap();
                        let rew = mab.reward(&po, old_sz, mic.len(), frame, arm, lvl);
                        mab.train(arm, input, rew);
                    }
                    po.push_to(frame);
                    debug_assert_eq!(frame, po.frame);
                    mic
                } else {
                    po.frame += 1;
                    po.state.as_litvec().clone()
                };
                self.obligations.add(po.clone());
                if self.add_lemma(po.frame - 1, lemma, false, Some(po)) {
                    info!("ic3 proved the property");
                    return McResult::Safe;
                }
                debug!("{}", self.frame.statistic(false));
            }

            // find other bad state in current frame and transform it into proof obligation
            if let Some((bad, inputs)) = self.get_bad() {
                trace!("bad state {bad} found in frame {}", self.level());
                let bad = LitOrdVec::new(bad);
                let depth = inputs.len() - 1;
                self.obligations
                    .add(Po::new(self.level(), bad, inputs, depth, None))
            } else {
                let depth = self.level();
                // Denser than BMC: every depth below 16, then geometrically sparser.
                if depth ^ depth.wrapping_add(1) > depth >> 4 {
                    info!("ic3 found no counterexample up to depth {depth}");
                }
                let nl = self.solvers.len();
                debug!("extending IC3 to level {nl}");
                if let Some(predprop) = self.predprop.as_mut() {
                    predprop.extend(self.frame.inf.iter().map(|(l, _)| l.as_litvec()));
                }
                let solver = self.inf_solver.clone();
                self.solvers.push(solver);
                self.frame.push(Frame::new());
                let propagate = self.propagate(None);
                if propagate {
                    info!("ic3 proved the property");
                    return McResult::Safe;
                }
                self.propagate_to_inf();
            }
        }
    }

    fn proof(&mut self) -> McProof {
        let mut proof = self.ots.clone_deep();
        if let Some(iv) = self.rst.init_var() {
            let piv = proof.add_init_var();
            self.rst.add_restore(iv, piv);
        }
        let mut invariants = self.inner_invariant();
        for c in self.ts.constraint.clone() {
            proof
                .rel_mut()
                .migrate(&self.ts.rel, c.var(), &mut self.rst.bvmap);
            invariants.push(LitVec::from(!c));
        }
        let mut invariants: Vec<LitVec> = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().map(|l| self.rst.restore(*l))))
            .collect();
        invariants.extend(self.rst.eq_invariant());
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel_mut().new_and(cube));
        }
        let invariants = proof.rel_mut().new_or(certifaiger_dnf);
        let proof_bad = std::mem::take(&mut proof.bad);
        let bad = proof.rel_mut().new_or(proof_bad);
        proof.bad = LitVec::from(proof.rel_mut().new_or([invariants, bad]));
        McProof::Bl(proof)
    }

    fn witness(&mut self) -> McWitness {
        let mut res = if let Some(res) = self.localabs.witness() {
            res
        } else {
            let mut res = BlWitness::default();
            let b = self.obligations.peak().unwrap();
            assert!(b.frame == 0);
            let mut b = Some(b);
            while let Some(bad) = b {
                res.state.push(bad.state.as_litvec().clone());
                res.input.push(bad.input[0].clone());
                for i in &bad.input[1..] {
                    res.input.push(i.clone());
                    res.state.push(LitVec::new());
                }
                b = bad.next.clone();
            }
            res
        };
        let iv = self.rst.init_var();
        res = res.filter_map(|l| {
            (iv != Some(l.var()))
                .then(|| self.rst.try_restore(l))
                .flatten()
        });
        for s in res.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        res.exact_state(&self.ots, true);
        McWitness::Bl(res)
    }

    fn statistic(&mut self) {
        info!("obligations: {}", self.obligations.statistic());
        info!("{}", self.frame.statistic(false));
        let mut num_solve = 0;
        for s in self.solvers.iter() {
            num_solve += s.num_solve;
        }
        info!("num_solve: {num_solve:#?}");
    }
}
