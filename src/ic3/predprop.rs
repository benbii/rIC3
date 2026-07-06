use crate::{
    gipsat::DagCnfSolver,
    ic3::IC3,
    transys::{Transys, lift::TsLift, unroll::TransysUnroll},
};
use logicrs::{Lit, LitVec, satif::Satif};
use rand::seq::SliceRandom;
use std::time::Instant;

pub struct PredProp {
    bts: Transys,
    slv: DagCnfSolver,
    lift: TsLift,
}

impl PredProp {
    pub fn new(uts: TransysUnroll, local_proof: usize, inn: bool, bad: &LitVec) -> Self {
        let mut bts = if inn {
            uts.internal_signals_with_full_prime()
        } else {
            uts.compile()
        };
        let next_bad: LitVec = uts.lits_next(bad, uts.num_unroll).collect();
        bts.bad = if local_proof < next_bad.len() {
            LitVec::from([next_bad[local_proof]])
        } else {
            next_bad
        };
        bts.constraint.extend(!bad);
        let slv = bts.new_solver();
        let lift = TsLift::new(uts);
        Self { bts, slv, lift }
    }

    pub fn add_lemma(&mut self, lemma: &LitVec) {
        self.slv.add_clause(&!lemma);
    }

    pub fn extend<'a>(&'a mut self, lemmas: impl IntoIterator<Item = &'a LitVec>) {
        self.slv = self.bts.new_solver();
        for l in lemmas.into_iter() {
            self.slv.add_clause(&!l);
        }
    }
}

impl IC3 {
    pub fn pred_prop_get_bad(&mut self) -> Option<(LitVec, Vec<LitVec>)> {
        let start = Instant::now();
        let predprop = self.predprop.as_mut().unwrap();
        let res = predprop.slv.solve(&predprop.bts.bad);
        self.statistic.block.get_bad_time += start.elapsed();
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
