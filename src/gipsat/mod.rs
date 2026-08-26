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
    constrain_act: Var, // also nr. of var
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
            if let Some(cls) = solver.simplify_clause(cls) {
                solver.add_clause_inner(&cls, ClauseKind::Trans);
            }
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

    fn add_clause_inner(&mut self, clause: &[Lit], kind: ClauseKind) -> CRef {
        debug_assert_eq!(
            clause.iter().any(|l| l.var() == self.constrain_act),
            matches!(kind, ClauseKind::Temporary)
        );
        if clause.len() == 1 {
            debug_assert!(clause[0].var() != self.constrain_act);
            debug_assert!(self.state.lit_value(clause[0]).is_none());
            self.assign(clause[0], CREF_NONE);
            if self.propagate() != CREF_NONE {
                self.trivial_unsat = true;
            }
            CREF_NONE
        } else {
            self.attach_clause(&clause, kind)
        }
    }

    pub fn add_perma_clause(&mut self, clause: &[Lit]) {
        self.reset();
        for l in clause.iter() {
            self.add_domain(l.var(), true);
        }
        if let Some(clause) = self.simplify_clause(clause) {
            self.add_clause_inner(&clause, ClauseKind::Lemma);
        }
    }

    pub fn add_entailed_clause(&mut self, clause: &[Lit]) {
        self.reset();
        if let Some(clause) = self.simplify_clause(clause) {
            self.add_clause_inner(&clause, ClauseKind::Lemma);
        }
    }

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
        constraint: &[&[Lit]],
        bucket: bool,
    ) -> bool {
        self.backtrack(0, self.temporary_domain);
        self.clean_temporary();
        self.prepared_vsids = false;

        for c in constraint {
            let mut c = LitVec::from(*c);
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

    /// No other function in this repo has the exact name `dcs_solve`. No wrapper exists for it.
    /// Grep for the full name to find its call sites without unrelated solver noise.
    pub fn dcs_solve(
        &mut self,
        assump: &[Lit],
        constraint: &[&[Lit]],
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

    pub fn minimal_premise(
        &mut self,
        assump: &[Lit],
        premise: &[Lit],
        consequent: &[Lit],
    ) -> Option<LitVec> {
        let assump = LitVec::from_iter(assump.iter().chain(premise.iter()).copied());
        if self.dcs_solve(&assump, &[consequent], &[], u32::MAX).unwrap() {
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

    #[inline]
    pub fn dcs_satval(&self, lit: Lit) -> Option<bool> {
        match self.state.lit_value(lit) {
            Lbool::TRUE => Some(true),
            Lbool::FALSE => Some(false),
            _ => None,
        }
    }

    #[inline]
    pub fn dcs_varsatval(&self, var: Var) -> Option<bool> {
        match self.state.value(var) {
            Lbool::TRUE => Some(true),
            Lbool::FALSE => Some(false),
            _ => None,
        }
    }

    #[inline]
    pub fn unsat_has(&self, lit: Lit) -> bool {
        self.unsat_core.has(lit)
    }
}
