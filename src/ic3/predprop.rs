use std::sync::Arc;

use crate::{
    Var, VarRange,
    gipsat::DagCnfSolver,
    ic3::IC3,
    transys::{Transys, lift::TsLift, unroll::TransysUnroll},
};
use logicrs::{Lit, LitVec};
use rand::seq::SliceRandom;

pub struct PredProp {
    bts: Transys,
    slv: DagCnfSolver,
    lift: TsLift,
}

impl PredProp {
    pub fn new(uts: TransysUnroll, inn: bool, bad: &LitVec) -> Self {
        let mut bts = if inn {
            assert!(uts.num_unroll == 1);
            let keep = uts.ts.rel.fanouts(&uts.ts.input);
            let mut rel = Arc::new((*uts.ts.rel).clone());
            let mut input = uts.ts.input.clone();
            input.extend(uts.ts.input.iter().map(|&v| uts.var_next(v, 1)));
            let mut constraint = uts.ts.constraint.clone();
            constraint.extend(uts.lits_next(uts.ts.constraint(), 1));
            for old_v in VarRange::new_inclusive(Var(1), uts.ts.rel.max_var()) {
                uts.add_unrolled_rel(&mut rel, old_v, 1);
            }
            assert!(uts.ts.justice.is_empty());
            let bad: LitVec = uts.lits_next(&uts.ts.bad, 1).collect();
            let mut ts = Transys {
                input,
                bad,
                constraint,
                rel,
                ..Default::default()
            };
            for v in VarRange::new_inclusive(Var::new(1), uts.ts.max_var()) {
                if !keep.contains(&v) {
                    ts.add_latch(v, uts.ts.init(v), uts.lit_next(v.lit(), 1));
                }
            }
            ts
        } else {
            uts.compile()
        };
        bts.bad = LitVec::from(uts.lit_next(bad[0], uts.num_unroll));
        bts.constraint.extend(!bad);
        let slv = bts.new_solver();
        let lift = TsLift::new(uts);
        Self { bts, slv, lift }
    }

    pub fn add_lemma(&mut self, lemma: &LitVec) {
        self.slv.add_perma_clause(&!lemma);
    }

    pub fn extend<'a>(&'a mut self, lemmas: impl IntoIterator<Item = &'a LitVec>) {
        self.slv = self.bts.new_solver();
        for l in lemmas.into_iter() {
            self.slv.add_perma_clause(&!l);
        }
    }
}

impl IC3 {
    pub fn pred_prop_get_bad(&mut self) -> Option<(LitVec, Vec<LitVec>)> {
        let predprop = self.predprop.as_mut().unwrap();
        let res = predprop.slv.dcs_solve_nocst(&predprop.bts.bad);
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
                1 => cube.reverse(),
                _ => cube.shuffle(&mut self.rng),
            };
            true
        };
        res.then(|| {
            predprop.lift.complex_lift(
                &mut predprop.slv,
                predprop.bts.latch.iter(),
                predprop
                    .bts
                    .bad
                    .iter()
                    .chain(predprop.bts.constraint.iter()),
                order,
            )
        })
    }
}
