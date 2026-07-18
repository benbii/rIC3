mod analyze;
mod cdb;
mod domain;
mod propagate;
mod search;
mod simplify;
mod state;
mod vsids;

use analyze::Analyze;
pub use cdb::ClauseKind;
use cdb::{CREF_NONE, CRef, ClauseDB};
use domain::Domain;
use logicrs::nckvec::NckVec;
use logicrs::satif::Satif;
use logicrs::{DagCnf, Lbool};
use logicrs::{Lit, LitSet, LitVec, Var, VarMap};
use propagate::WatchArena;
use rand::{SeedableRng, rngs::SmallRng};
use simplify::Simplify;
use state::VarState;
use std::sync::Arc;
use vsids::Vsids;

#[derive(Clone)]
pub struct DagCnfSolver {
    cdb: ClauseDB,
    watchers: WatchArena,
    state: VarState,
    trail: NckVec<Lit>,
    pos_in_trail: Vec<u32>,
    level: VarMap<u32>,
    reason: VarMap<CRef>,
    propagated: u32,
    vsids: Vsids,
    analyze: Analyze,
    simplify: Simplify,
    unsat_core: LitSet,
    domain: Domain,
    temporary_domain: bool,
    prepared_vsids: bool,
    constrain_act: Var,
    dc: Arc<DagCnf>,
    trivial_unsat: bool,
    pub num_solve: usize,
    pub use_phase_saving: bool,
    pub rng: SmallRng,
}

impl DagCnfSolver {
    pub fn new(dc: Arc<DagCnf>) -> Self {
        let constrain_act = Var::new(dc.num_var());
        let mut state = VarState::new_with(constrain_act);
        let domain = Domain::new(constrain_act, &mut state);
        let mut solver = Self {
            dc: dc.clone(),
            cdb: Default::default(),
            watchers: WatchArena::new_with(constrain_act),
            state,
            trail: Default::default(),
            pos_in_trail: Default::default(),
            level: VarMap::new_with(constrain_act),
            reason: VarMap::new_with(constrain_act),
            propagated: Default::default(),
            vsids: Vsids::new_with(constrain_act),
            analyze: Analyze::new_with(constrain_act),
            simplify: Default::default(),
            unsat_core: LitSet::new_with(constrain_act),
            domain,
            temporary_domain: Default::default(),
            prepared_vsids: false,
            constrain_act,
            num_solve: 0,
            trivial_unsat: false,
            rng: SmallRng::seed_from_u64(0),
            use_phase_saving: true,
        };
        for cls in dc.all_clauses() {
            solver.add_clause_inner(cls, ClauseKind::Trans);
        }
        assert!(solver.propagate() == CREF_NONE);
        solver.watchers.maybe_compact();
        solver
    }

    fn simplify_clause(&mut self, clause: &[Lit]) -> Option<LitVec> {
        assert!(self.highest_level() == 0);
        let mut clause = logicrs::LitVec::from(clause);
        clause.sort();
        let mut simplified = LitVec::new_with_cap(clause.len());
        for &lit in clause.iter() {
            let value = self.state.lit_value(lit);
            if value.is_true() {
                return None;
            } else if value.is_false() {
                continue;
            }
            if let Some(&last) = (*simplified).last() {
                if lit == last {
                    continue;
                } else if lit == !last {
                    return None;
                }
            }
            simplified.push(lit);
        }
        if simplified.is_empty() {
            self.trivial_unsat = true;
            return None;
        }
        Some(simplified)
    }

    fn add_clause_inner(&mut self, clause: &[Lit], mut kind: ClauseKind) -> CRef {
        if let Some(clause) = self.simplify_clause(clause) {
            if clause.iter().any(|l| l.var() == self.constrain_act) {
                kind = ClauseKind::Temporary;
            }
            if clause.len() == 1 {
                assert!(clause[0].var() != self.constrain_act);
                match self.state.lit_value(clause[0]) {
                    Lbool::TRUE | Lbool::FALSE => todo!(),
                    _ => {
                        self.assign(clause[0], CREF_NONE);
                        if self.propagate() != CREF_NONE {
                            self.trivial_unsat = true;
                        }
                        CREF_NONE
                    }
                }
            } else {
                self.attach_clause(&clause, kind)
            }
        } else {
            CREF_NONE
        }
    }

    pub fn add_entailed_clause(&mut self, clause: &[Lit]) {
        self.reset();
        self.add_clause_inner(clause, ClauseKind::Lemma);
    }

    // #[allow(unused)]
    // pub fn lemmas(&mut self) -> Vec<LitOrdVec> {
    //     self.reset();
    //     let mut lemmas = Vec::new();
    //     for t in self.trail.iter() {
    //         if self.dc.is_latch(t.var()) {
    //             lemmas.push(LitOrdVec::new(LitVec::from([!*t])));
    //         }
    //     }
    //     for l in self.cdb.lemmas.iter() {
    //         let lemma = LitVec::from_iter(self.cdb.get(*l).slice().iter().map(|l| !*l));
    //         lemmas.push(LitOrdVec::new(lemma));
    //     }
    //     lemmas
    // }

    fn reset(&mut self) {
        self.backtrack(0, false);
        self.clean_temporary();
        self.prepared_vsids = false;
        self.domain.reset(&mut self.state);
        assert!(!self.temporary_domain);
    }

    fn new_round(
        &mut self,
        domain: &[Var],
        assump: &[Lit],
        constraint: &[LitVec],
        bucket: bool,
    ) -> bool {
        self.backtrack(0, self.temporary_domain);
        self.clean_temporary();
        self.prepared_vsids = false;

        for c in constraint {
            let mut c = LitVec::from(c);
            c.push(!self.constrain_act.lit());
            if let Some(c) = self.simplify_clause(&c) {
                assert!(!c.is_empty());
                if c.len() == 1 {
                    return false;
                }
                self.add_clause_inner(&c, ClauseKind::Temporary);
            }
        }

        if !self.temporary_domain {
            self.domain
                .enable_local(domain, assump, constraint, &self.dc, &mut self.state);
            assert!(!self.state.get(self.constrain_act).in_domain());
            self.domain.insert(self.constrain_act, &mut self.state);
            if bucket {
                self.vsids.enable_bucket = true;
                self.vsids.bucket.clear(&mut self.state);
            } else {
                self.vsids.enable_bucket = false;
                self.vsids.heap.clear();
            }
        }
        true
    }

    pub fn solve_full(
        &mut self,
        assump: &[Lit],
        constraint: &[LitVec],
        domain: &[Var],
        restart_limit: u32,
    ) -> Option<bool> {
        if self.trivial_unsat {
            self.unsat_core.clear();
            return Some(false);
        }
        self.num_solve += 1;
        let mut assumption;
        if self.propagate() != CREF_NONE {
            self.trivial_unsat = true;
            self.unsat_core.clear();
            return Some(false);
        }
        let search_assump = if !constraint.is_empty() {
            assumption = LitVec::new();
            assumption.push(self.constrain_act.lit());
            assumption.extend_from_slice(assump);
            if !self.new_round(domain, assump, constraint, true) {
                self.unsat_core.clear();
                return Some(false);
            };
            &assumption
        } else {
            assert!(self.new_round(domain, assump, &[], true));
            assump
        };
        self.clean_learnt(true);
        self.simplify();
        self.watchers.maybe_compact();
        let res = self.search_with_restart(search_assump, restart_limit);
        res
    }

    pub fn solve_with_restart_limit(
        &mut self,
        assumps: &[Lit],
        constraint: &[LitVec],
        limit: u32,
    ) -> Option<bool> {
        self.solve_full(assumps, constraint, &[], limit)
    }

    pub fn solve_with_domain(&mut self, assumps: &[Lit], domain: &[Var]) -> bool {
        self.solve_full(assumps, &[], domain, u32::MAX).unwrap()
    }

    pub fn minimal_premise(
        &mut self,
        assump: &[Lit],
        premise: &[Lit],
        consequent: &[Lit],
    ) -> Option<LitVec> {
        let assump = LitVec::from_iter(assump.iter().chain(premise.iter()).copied());
        if self.solve_with_constraint(&assump, &[LitVec::from(consequent)]) {
            return None;
        }
        Some(
            premise
                .iter()
                .filter(|l| self.unsat_has(**l))
                .copied()
                .collect(),
        )
    }
}

impl Satif for DagCnfSolver {
    #[inline]
    fn new_var(&mut self) -> Var {
        assert_eq!(
            self.num_solve, 0,
            "cannot add GipSAT variables after solving starts"
        );
        self.reset();
        let v = self.constrain_act;
        let var = Var::new(self.num_var() + 1);
        self.state.reserve(var);
        self.level.reserve(var);
        self.reason.reserve(var);
        self.watchers.reserve(var);
        self.vsids.reserve(var);
        self.analyze.reserve(var);
        self.unsat_core.reserve(var);
        self.domain.reserve(var);
        self.constrain_act = var;
        v
    }

    #[inline]
    fn num_var(&self) -> usize {
        self.constrain_act.into()
    }

    fn add_clause(&mut self, clause: &[Lit]) {
        self.reset();
        for l in clause.iter() {
            self.add_domain(l.var(), true);
        }
        self.add_clause_inner(clause, ClauseKind::Lemma);
    }

    fn solve(&mut self, assumps: &[Lit]) -> bool {
        self.solve_full(assumps, &[], &[], u32::MAX).unwrap()
    }

    fn solve_with_constraint(&mut self, assumps: &[Lit], constraint: &[LitVec]) -> bool {
        self.solve_full(assumps, constraint, &[], u32::MAX).unwrap()
    }

    #[inline]
    fn sat_value(&self, lit: Lit) -> Option<bool> {
        match self.state.lit_value(lit) {
            Lbool::TRUE => Some(true),
            Lbool::FALSE => Some(false),
            _ => None,
        }
    }

    #[inline]
    fn sat_value_var(&self, var: Var) -> Option<bool> {
        match self.state.value(var) {
            Lbool::TRUE => Some(true),
            Lbool::FALSE => Some(false),
            _ => None,
        }
    }

    #[inline]
    fn unsat_has(&self, lit: Lit) -> bool {
        self.unsat_core.has(lit)
    }

    #[inline]
    fn flip_to_none(&mut self, var: Var) -> bool {
        self.flip_to_none_inner(var)
    }
}
