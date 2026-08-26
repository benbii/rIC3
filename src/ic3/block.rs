use super::solver::{inductive, inductive_core};
use crate::Lit;
use crate::ic3::mab::balanced_params;
use crate::ic3::{IC3, mic::DropVarParameter, proofoblig::Po};
use log::debug;
use logicrs::{LitOrdVec, LitVec};

pub enum BlockResult {
    Success,
    Failure(usize),
    Proved,
}

impl IC3 {
    fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        for i in frame + 1..=self.level() {
            if inductive(&mut self.solvers[i - 1], &self.ts, &cube, true) {
                cube = inductive_core(&mut self.solvers[i - 1], &self.ts, &cube).unwrap_or(cube);
            } else {
                return (i, cube);
            }
        }
        (self.level() + 1, cube)
    }

    pub fn block(&mut self) -> BlockResult {
        let mut assump = LitVec::new();
        while let Some(mut po) = self.obligations.pop(self.level()) {
            const MAX_ACT_BEFORE_DROP: f64 = 20.0;
            // intersects with init; failed if on frame 0
            if self.ts.cube_subsume_init(&po.state) {
                if self.abs_cst || self.abs_trans {
                    self.obligations.add(po.clone());
                    if self.check_witness_by_bmc(po.depth) {
                        return BlockResult::Failure(po.depth);
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
                    return BlockResult::Failure(po.depth);
                }
                debug_assert_eq!(
                    self.solvers[0].dcs_solve(po.state.as_litvec(), &[], &[], u32::MAX),
                    Some(false)
                );
            }

            if let Some((bf, _)) = self.frame.trivial_contained(Some(po.frame), &po.state) {
                if let Some(bf) = bf {
                    po.push_to(bf + 1);
                    self.obligations.add(po);
                }
                continue;
            }
            po.act += 1.0;
            if self.drop_po && po.act > MAX_ACT_BEFORE_DROP {
                continue;
            }

            let mut ordered_cube = po.state.as_litvec().clone();
            self.activity.sort_by_activity(&mut ordered_cube, false);
            let slv = &mut self.solvers[po.frame - 1];
            assump.clear();
            assump.extend(ordered_cube.iter().map(|l| self.ts.next(*l)));
            let blocked = !slv.dcs_solve(&assump, &[], &[], u32::MAX).unwrap();
            if !blocked {
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
                mic = self.mic(po.frame, mic, &[], parameter);
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
                return BlockResult::Proved;
            }
            debug!("{}", self.frame.statistic(false));
        }
        BlockResult::Success
    }

    pub(super) fn trivial_block(
        &mut self,
        frame: usize,
        lemma: LitVec,
        constraint: &[Lit],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
    }

    fn trivial_block_rec(
        &mut self,
        frame: usize,
        lemma: LitVec,
        constraint: &[Lit],
        limit: &mut usize,
        parameter: DropVarParameter,
    ) -> bool {
        if frame == 0 {
            return false;
        }
        if self.ts.cube_subsume_init(&lemma) {
            return false;
        }
        if *limit == 0 {
            return false;
        }
        *limit -= 1;
        let mut cube_cst = LitVec::new_with_cap(lemma.len());
        let mut ordcube = LitVec::new_with_cap(lemma.len());
        let mut assump = LitVec::new_with_cap(lemma.len());
        loop {
            ordcube.clear();
            ordcube.extend_from_slice(&lemma);
            self.activity.sort_by_activity(&mut ordcube, false);
            assump.clear();
            assump.extend(ordcube.iter().map(|l| self.ts.next(*l)));
            cube_cst.clear();
            cube_cst.extend(ordcube.iter().map(|l| !*l));
            let slv = &mut self.solvers[frame - 1];
            let allcst: &[&[Lit]] = if constraint.is_empty() {
                &[cube_cst.as_slice()]
            } else {
                &[constraint, &cube_cst]
            };
            let core = (!slv.dcs_solve(&assump, &allcst, &[], u32::MAX).unwrap())
                .then(|| inductive_core(slv, &self.ts, &ordcube).unwrap());

            if let Some(mut mic) = core {
                mic = self.mic(frame, mic, constraint, parameter);
                let (frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(frame - 1, mic, false, None);
                return true;
            }
            if *limit == 0 {
                return false;
            }
            let model = self.get_pred(frame, &assump, false).0;
            if !self.trivial_block_rec(frame - 1, model, constraint, limit, parameter) {
                return false;
            }
        }
    }
}
