use super::IC3;
use crate::{gipsat::DagCnfSolver, transys::Transys};
use log::trace;
use logicrs::{Lit, LitVec};
use rand::seq::SliceRandom;

pub(super) fn inductive(
    slv: &mut DagCnfSolver,
    ts: &Transys,
    cube: &[Lit],
    strengthen: bool,
) -> bool {
    let assump = ts.lits_next(cube);
    if strengthen {
        let mut cst = LitVec::from_iter(cube.iter().map(|l| !*l));
        cst.sort();
        cst.push(Lit::default());
        let mut assump_with_act = LitVec::new_with_cap(assump.len() + 1);
        assump_with_act.push(Lit::default());
        assump_with_act.extend_from_slice(&assump);
        let mut constraints = [&mut cst[..]];
        return !slv
            .dcs_solve(&mut assump_with_act, &mut constraints, &[], u32::MAX)
            .unwrap();
    }
    !slv.dcs_solve_nocst(&assump)
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
    pub(super) fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        for i in frame + 1..=self.level() {
            if inductive(&mut self.solvers[i - 1], &self.ts, &cube, true) {
                cube = inductive_core(&mut self.solvers[i - 1], &self.ts, &cube).unwrap_or(cube);
            } else {
                return (i, cube);
            }
        }
        (self.level() + 1, cube)
    }

    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    pub(super) fn get_bad(&mut self) -> Option<(LitVec, Vec<LitVec>)> {
        trace!("getting bad state in frame {}", self.level());
        if self.predprop.is_some() {
            self.pred_prop_get_bad()
        } else {
            debug_assert!(self.ts.bad.len() == 1);
            let frame = self.solvers.len();
            let assump = LitVec::from([self.ts.bad[0]]);
            let slv = self.solvers.last_mut().unwrap();
            let res = slv.dcs_solve_nocst(&assump);
            if res {
                Some(self.get_pred(frame, &assump, true))
            } else {
                None
            }
        }
    }

    pub(super) fn get_pred(
        &mut self,
        frame: usize,
        assump: &[Lit],
        strengthen: bool,
    ) -> (LitVec, Vec<LitVec>) {
        let solver = &mut self.solvers[frame - 1];
        let mut cls = LitVec::from(assump);
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
        (state, input)
    }

    pub fn invariant(&self) -> Vec<LitVec> {
        self.inner_invariant()
            .iter()
            .map(|l| l.map_var(|l| self.rst.restore_var(l)))
            .collect()
    }
}
