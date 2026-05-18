use crate::{gipsat::DagCnfSolver, transys::Transys};
use logicrs::{Lit, LitVec, satif::Satif};

pub fn new_transys_solver(ts: &Transys) -> DagCnfSolver {
    let mut slv = DagCnfSolver::new(&ts.rel);
    for c in ts.constraint.iter() {
        slv.add_clause(&[*c]);
    }
    slv
}

pub fn inductive_with_constrain(
    slv: &mut DagCnfSolver,
    ts: &Transys,
    cube: &[Lit],
    strengthen: bool,
    mut constraint: Vec<LitVec>,
) -> bool {
    let assump = ts.lits_next(cube);
    if strengthen {
        constraint.push(LitVec::from_iter(cube.iter().map(|l| !*l)));
    }
    !slv.solve_with_constraint(&assump, constraint)
}

pub fn inductive(slv: &mut DagCnfSolver, ts: &Transys, cube: &[Lit], strengthen: bool) -> bool {
    inductive_with_constrain(slv, ts, cube, strengthen, vec![])
}

pub fn inductive_core(slv: &mut DagCnfSolver, ts: &Transys, cube: &[Lit]) -> Option<LitVec> {
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
        assert!(!ts.cube_subsume_init(&ans));
    }
    Some(ans)
}
