use crate::gipsat::{inductive, inductive_core};
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

    fn generalize(
        &mut self,
        mut po: ProofObligation,
        core_cube: &LitVec,
        parameter: DropVarParameter,
    ) -> bool {
        let Some(mut mic) =
            inductive_core(&mut self.solvers[po.frame - 1], &self.ts, core_cube)
        else {
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.state.as_litvec().clone(), false, Some(po));
        };
        mic = self.mic(po.frame, mic, &[], parameter);
        let (frame, mic) = self.push_lemma(po.frame, mic);
        self.statistic.avg_po_cube_len += po.state.len();
        po.push_to(frame);
        self.add_obligation(po.clone());
        if self.add_lemma(frame - 1, mic.clone(), false, Some(po)) {
            return true;
        }
        false
    }

    pub fn block(&mut self) -> BlockResult {
        while let Some(mut po) = self.obligations.pop(self.level()) {
            const CTG_THRESHOLD: f64 = 10.0;
            const EXCTG_THRESHOLD: f64 = 40.0;
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

            let parameter = if self.dynamic && po.next.is_none() {
                Default::default()
            } else if self.dynamic {
                let n = po.next.as_mut().unwrap();
                let mut act = n.act;
                if let Some(nn) = n.next.as_mut() {
                    act = act.max(nn.act);
                    if let Some(nnn) = nn.next.as_mut() {
                        act = act.max(nnn.act);
                    }
                }
                let (limit, max, level) = match act {
                    EXCTG_THRESHOLD.. => (
                        ((act - EXCTG_THRESHOLD).powf(0.45) * 2.0 + 5.0).round() as usize,
                        5,
                        1,
                    ),
                    ..CTG_THRESHOLD => (0, 0, 0),
                    _ => (1, (act - CTG_THRESHOLD) as usize / 10 + 2, 1),
                };
                DropVarParameter::new(limit, max, level)
            } else {
                self.default_mic
            };
            if self.generalize(po, &ordered_cube, parameter) {
                return BlockResult::Proved;
            }
            debug!("{}", self.frame.statistic(false));
        }
        BlockResult::Success
    }

    fn trivial_block_rec(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
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
                let mut mic = inductive_core(
                    &mut self.solvers[frame - 1],
                    &self.ts,
                    &ordered_cube,
                )
                .unwrap();
                mic = self.mic(frame, mic, constraint, parameter);
                let (frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(frame - 1, mic, false, None);
                return true;
            } else {
                if *limit == 0 {
                    return false;
                }
                let model = LitOrdVec::new(self.get_pred(frame, false).0);
                if !self.trivial_block_rec(frame - 1, model, constraint, limit, parameter) {
                    return false;
                }
            }
        }
    }

    pub fn trivial_block(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
    }
}
