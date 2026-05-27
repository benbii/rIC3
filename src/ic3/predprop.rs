use crate::{
    gipsat::{DagCnfSolver, new_transys_solver},
    ic3::{IC3, proofoblig::ProofObligation},
    transys::{Transys, lift::TsLift, unroll::TransysUnroll},
};
use log::info;
use logicrs::{Lit, LitOrdVec, LitVec, satif::Satif};
use rand::seq::SliceRandom;
use std::time::Instant;

pub struct PredProp {
    bts: Transys,
    slv: DagCnfSolver,
    lift: TsLift,
    inn: bool,
}

impl PredProp {
    pub fn new(uts: TransysUnroll, local_proof: usize, inn: bool) -> Self {
        let mut bts = if inn {
            uts.internal_signals_with_full_prime()
        } else {
            uts.compile()
        };
        if local_proof < bts.bad.len() {
            bts.bad = LitVec::from([bts.bad[local_proof]]);
        }
        bts.constraint.extend(!&uts.ts.bad);
        let slv = new_transys_solver(&bts);
        let lift = TsLift::new(uts);
        Self {
            bts,
            slv,
            lift,
            inn,
        }
    }

    pub fn add_lemma(&mut self, lemma: &LitVec) {
        self.slv.add_clause(&!lemma);
    }

    pub fn extend<'a>(&'a mut self, lemmas: impl IntoIterator<Item = &'a LitVec>) {
        self.slv = new_transys_solver(&self.bts);
        for l in lemmas.into_iter() {
            self.slv.add_clause(&!l);
        }
    }
}

impl IC3 {
    pub fn prep_prop_base(&mut self) -> bool {
        assert!(self.solvers.is_empty());
        if self.predprop.is_none() {
            return true;
        }
        let bad = self.ts.bad.clone();
        let mut slv = new_transys_solver(&self.ts);
        for init in self.ts.inits() {
            slv.add_clause(&init);
        }
        if slv.solve(&[self.ts.bad[0]]) {
            let mut input = LitVec::new();
            for i in self.ts.input() {
                if let Some(v) = slv.sat_value_lit(i) {
                    input.push(v);
                }
            }
            let mut bad = LitVec::new();
            for l in self.ts.latch() {
                if let Some(v) = slv.sat_value_lit(l) {
                    bad.push(v);
                }
            }
            self.add_obligation(ProofObligation::new(
                0,
                LitOrdVec::new(bad),
                vec![input],
                0,
                None,
            ));
            info!("counter-example found in base checking");
            return false;
        }
        self.ts.constraint.extend(!bad);
        self.lift = TsLift::new(TransysUnroll::new(&self.ts));
        self.inf_solver = new_transys_solver(&self.ts);
        true
    }

    pub fn pred_prop_get_bad(&mut self) -> Option<(LitVec, Vec<LitVec>)> {
        let start = Instant::now();
        let predprop = self.predprop.as_mut().unwrap();
        let res = predprop.slv.solve(&predprop.bts.bad);
        self.statistic.block.get_bad_time += start.elapsed();
        let order = |mut i: usize, cube: &mut [Lit]| -> bool {
            if predprop.inn {
                if i == 0 {
                    cube.sort_by(|a, b| b.cmp(a));
                    return true;
                }
                i -= 1;
            }
            match i {
                0 => {
                    self.activity.sort_by_activity(cube, false);
                }
                1 => {
                    cube.reverse();
                }
                _ => {
                    cube.shuffle(&mut self.rng);
                }
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
