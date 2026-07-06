use super::IC3;
use crate::{gipsat::DagCnfSolver, transys::Transys};
use log::trace;
use logicrs::{Lit, LitVec, satif::Satif};
use rand::seq::SliceRandom;
use std::time::Instant;

pub(super) fn inductive(
    slv: &mut DagCnfSolver,
    ts: &Transys,
    cube: &[Lit],
    strengthen: bool,
) -> bool {
    let assump = ts.lits_next(cube);
    let mut constraint = Vec::new();
    if strengthen {
        constraint.push(LitVec::from_iter(cube.iter().map(|l| !*l)));
    }
    !slv.solve_with_constraint(&assump, &constraint)
}

pub(super) fn inductive_core(slv: &mut DagCnfSolver, ts: &Transys, cube: &[Lit]) -> Option<LitVec> {
    let mut ans = LitVec::new();
    for &l in cube.iter() {
        let nl = ts.next(l);
        if slv.unsat_has(nl) {
            ans.push(l);
        }
    }
    if ts.cube_subsume_init(&ans) {
        ans = LitVec::new();
        let new = cube.iter().find(|&&l| {
            ts.init(l.var())
                .and_then(|l| l.try_constant())
                .is_some_and(|i| i != l.polarity())
        })?;
        for &l in cube.iter() {
            let nl = ts.next(l);
            if slv.unsat_has(nl) {
                ans.push(l);
            }
            if l.eq(new) {
                ans.push(l);
            }
        }
        debug_assert!(!ts.cube_subsume_init(&ans));
    }
    Some(ans)
}

impl IC3 {
    pub(super) fn get_bad(&mut self) -> Option<(LitVec, Vec<LitVec>)> {
        trace!("getting bad state in frame {}", self.level());
        if self.predprop.is_some() {
            self.pred_prop_get_bad()
        } else {
            let start = Instant::now();
            debug_assert!(self.ts.bad.len() == 1);
            let frame = self.solvers.len();
            let assump = LitVec::from([self.ts.bad[0]]);
            let res = self.solvers.last_mut().unwrap().solve(&assump);
            self.statistic.block.get_bad_time += start.elapsed();
            if res {
                self.last_assump[frame - 1] = assump;
                Some(self.get_pred(frame, true))
            } else {
                None
            }
        }
    }

    pub(super) fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &LitVec,
        strengthen: bool,
    ) -> (bool, LitVec) {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, false);
        let assump = self.ts.lits_next(&ordered_cube);
        let mut constraint = Vec::new();
        if strengthen {
            constraint.push(LitVec::from_iter(ordered_cube.iter().map(|l| !*l)));
        }
        let blocked = !self.solvers[frame - 1].solve_with_constraint(&assump, &constraint);
        self.last_assump[frame - 1] = assump;
        (blocked, ordered_cube)
    }

    pub(super) fn blocked_with_ordered_with_constrain(
        &mut self,
        frame: usize,
        cube: &LitVec,
        ascending: bool,
        strengthen: bool,
        mut constraint: Vec<LitVec>,
    ) -> (bool, LitVec) {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        let assump = self.ts.lits_next(&ordered_cube);
        if strengthen {
            constraint.push(LitVec::from_iter(ordered_cube.iter().map(|l| !*l)));
        }
        let blocked = !self.solvers[frame - 1].solve_with_constraint(&assump, &constraint);
        self.last_assump[frame - 1] = assump;
        (blocked, ordered_cube)
    }

    pub(super) fn get_pred(&mut self, frame: usize, strengthen: bool) -> (LitVec, Vec<LitVec>) {
        let start = Instant::now();
        let solver = &mut self.solvers[frame - 1];
        let mut cls: LitVec = self.last_assump[frame - 1].clone();
        let mut cst = self.ts.constraint.clone();
        cls.retain(|l| self.localabs.refine_has(l.var()));
        cst.retain(|l| self.localabs.refine_has(l.var()));
        let order = |mut i: usize, cube: &mut [Lit]| -> bool {
            if self.inn {
                if i == 0 {
                    cube.sort_by(|a, b| b.cmp(a));
                    return true;
                }
                i -= 1;
            }
            match i {
                0 => self.activity.sort_by_activity(cube, false),
                1 => {
                    if !strengthen {
                        return false;
                    }
                    cube.reverse();
                }
                _ => cube.shuffle(&mut self.rng),
            };
            true
        };
        let (state, input) = self.lift.lift(solver, cls.iter().chain(cst.iter()), order);
        self.statistic.block.get_pred_time += start.elapsed();
        (state, input)
    }
}
