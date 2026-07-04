use super::solver::{inductive, inductive_core};
use crate::ic3::mab::balanced_params;
use crate::ic3::{IC3, mic::DropVarParameter, proofoblig::ProofObligation};
use log::debug;
use logicrs::{LitOrdVec, LitVec, satif::Satif};
use std::time::Instant;

pub enum BlockResult {
    Success,
    Failure(usize),
    Proved,
}

impl IC3 {
    fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        let start = Instant::now();
        for i in frame + 1..=self.level() {
            if inductive(&mut self.solvers[i - 1], &self.ts, &cube, true) {
                cube = inductive_core(&mut self.solvers[i - 1], &self.ts, &cube).unwrap_or(cube);
            } else {
                return (i, cube);
            }
        }
        self.statistic.block.push_time += start.elapsed();
        (self.level() + 1, cube)
    }

    pub fn block(&mut self) -> BlockResult {
        while let Some(mut po) = self.obligations.pop(self.level()) {
            const MAX_ACT_BEFORE_DROP: f64 = 20.0;
            // intersects with init; failed if on frame 0
            if self.ts.cube_subsume_init(&po.state) {
                if self.abs_cst || self.abs_trans {
                    self.add_obligation(po.clone());
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
                    self.add_obligation(po.clone());
                    return BlockResult::Failure(po.depth);
                }
                debug_assert!(!self.solvers[0].solve(po.state.as_litvec()));
            }

            if let Some((bf, _)) = self.frame.trivial_contained(Some(po.frame), &po.state) {
                if let Some(bf) = bf {
                    po.push_to(bf + 1);
                    self.add_obligation(po);
                }
                continue;
            }
            po.act += 1.0;
            if self.drop_po && po.act > MAX_ACT_BEFORE_DROP {
                continue;
            }

            let blocked_start = Instant::now();
            let (blocked, ordered_cube) = self.blocked_with_ordered(po.frame, &po.state, false);
            self.statistic.block.blocked_time += blocked_start.elapsed();
            if !blocked {
                let (model, inputs) = self.get_pred(po.frame, true);
                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    LitOrdVec::new(model),
                    inputs,
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
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
                self.statistic.avg_po_cube_len += po.state.len();
                po.push_to(frame);
                debug_assert_eq!(frame, po.frame);
                mic
            } else {
                po.frame += 1;
                po.state.as_litvec().clone()
            };
            self.add_obligation(po.clone());
            if self.add_lemma(po.frame - 1, lemma, false, Some(po)) {
                return BlockResult::Proved;
            }
            debug!("{}", self.frame.statistic(false));
        }
        BlockResult::Success
    }

    fn trivial_block_rec(
        &mut self,
        frame: usize,
        lemma: LitVec,
        constraint: &[LitVec],
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
        loop {
            let (blocked, ordered_cube) = self.blocked_with_ordered_with_constrain(
                frame,
                &lemma,
                false,
                true,
                constraint.to_vec(),
            );
            if blocked {
                let mut mic =
                    inductive_core(&mut self.solvers[frame - 1], &self.ts, &ordered_cube).unwrap();
                mic = self.mic(frame, mic, constraint, parameter);
                let (frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(frame - 1, mic, false, None);
                return true;
            } else {
                if *limit == 0 {
                    return false;
                }
                let model = self.get_pred(frame, false).0;
                if !self.trivial_block_rec(frame - 1, model, constraint, limit, parameter) {
                    return false;
                }
            }
        }
    }

    pub fn trivial_block(
        &mut self,
        frame: usize,
        lemma: LitVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
    }
}
