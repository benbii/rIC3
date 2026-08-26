use crate::RseedSet as HashSet;
use crate::{gipsat::DagCnfSolver, transys::unroll::TransysUnroll};
use logicrs::{Lit, LitVec, Var};
use std::sync::Arc;

pub struct TsLift {
    ts: TransysUnroll,
    slv: DagCnfSolver,
}

impl TsLift {
    pub fn new(ts: TransysUnroll) -> Self {
        let tsc = ts.compile();
        let slv = DagCnfSolver::new(Arc::clone(&tsc.rel));
        Self { ts, slv }
    }

    pub fn lift(
        &mut self,
        satif: &mut DagCnfSolver,
        target: impl IntoIterator<Item = impl AsRef<Lit>>,
        order: impl FnMut(usize, &mut [Lit]) -> bool,
    ) -> (LitVec, Vec<LitVec>) {
        self.complex_lift(satif, self.ts.latch.clone(), target, order)
    }

    pub fn complex_lift(
        &mut self,
        satif: &mut DagCnfSolver,
        state: impl IntoIterator<Item = impl AsRef<Var>>,
        target: impl IntoIterator<Item = impl AsRef<Lit>>,
        mut order: impl FnMut(usize, &mut [Lit]) -> bool,
    ) -> (LitVec, Vec<LitVec>) {
        let mut cls: LitVec = target.into_iter().map(|l| *l.as_ref()).collect();
        if cls.is_empty() {
            return (LitVec::new(), vec![]);
        }
        cls = !cls;
        let in_cls: HashSet<Var> = HashSet::from_iter(cls.iter().map(|l| l.var()));
        let mut inputs = Vec::new();
        let mut inputs_flatten = LitVec::new();
        for k in 0..=self.ts.num_unroll {
            let mut input = LitVec::new();
            for i in self.ts.input() {
                let lit = self.ts.lit_next(i.lit(), k);
                if let Some(v) = satif.dcs_satval(lit) {
                    input.push(i.lit().not_if(!v));
                    inputs_flatten.push(lit.not_if(!v));
                }
            }
            inputs.push(input);
        }
        self.slv.set_domain(cls.iter().cloned(), &[]);
        let mut consequent = LitVec::new_with_cap(cls.len() + 1);
        let mut states = LitVec::new();
        for s in state.into_iter() {
            let s = *s.as_ref();
            let lit = s.lit();
            if self.slv.domain_has(s)
                && let Some(v) = satif.dcs_satval(lit)
                && (in_cls.contains(&s) || !satif.flip_to_none(s))
            {
                states.push(lit.not_if(!v));
            }
        }
        for i in 0.. {
            if states.is_empty() {
                break;
            }
            if !order(i, &mut states) {
                break;
            }
            let olen = states.len();
            let mut assump = LitVec::new_with_cap(inputs_flatten.len() + states.len() + 1);
            assump.push(Lit::default());
            assump.extend(inputs_flatten.iter().chain(states.iter()).copied());
            consequent.clear();
            consequent.extend_from_slice(&cls);
            consequent.sort();
            consequent.dedup();
            consequent.push(Lit::default());
            let mut constraints = [&mut consequent[..]];
            assert!(
                !self
                    .slv
                    .dcs_solve(&mut assump, &mut constraints, &[], u32::MAX)
                    .unwrap()
            );
            states.retain(|l| self.slv.unsat_has(*l));
            if states.len() == olen {
                break;
            }
        }
        self.slv.unset_domain();
        (states, inputs)
    }
}
