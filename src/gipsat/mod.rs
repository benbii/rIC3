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
            let mut cls = LitVec::from(cls);
            cls.sort();
            if let cls = solver.simplify_clause(&mut cls)
                && !cls.is_empty()
            {
                solver.add_clause_inner(&cls, ClauseKind::Trans);
            }
        }
        assert!(solver.propagate() == CREF_NONE);
        solver.watchers.maybe_compact();
        solver
    }

    fn simplify_clause<'a>(&mut self, clause: &'a mut [Lit]) -> &'a mut [Lit] {
        debug_assert!(self.highest_level() == 0);
        // the solver does not rely on this; the asserts are purely for aligning old semantics
        debug_assert!(clause.is_sorted());
        debug_assert!(clause.windows(2).all(|pair| pair[0] != pair[1]));
        let mut prevneg = Lit(u32::MAX);
        for &lit in clause.iter() {
            if prevneg == lit || self.state.lit_value(lit).is_true() {
                return &mut [];
            }
            prevneg = !lit;
        }

        let mut end = 0;
        for i in 0..clause.len() {
            let lit = clause[i];
            if self.state.lit_value(lit).is_false() {
                continue;
            }
            clause[end] = lit;
            end += 1;
        }
        if end == 0 {
            self.trivial_unsat = true;
        }
        &mut clause[..end]
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
        let mut clause = LitVec::from(clause);
        clause.sort();
        if let clause = self.simplify_clause(&mut clause)
            && !clause.is_empty()
        {
            self.add_clause_inner(&clause, ClauseKind::Lemma);
        }
    }

    pub fn add_entailed_clause(&mut self, clause: &[Lit]) {
        self.reset();
        let mut clause = LitVec::from(clause);
        clause.sort();
        if let clause = self.simplify_clause(&mut clause)
            && !clause.is_empty()
        {
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
        constraint: &mut [&mut [Lit]],
        bucket: bool,
    ) -> bool {
        self.backtrack(0, self.temporary_domain);
        self.clean_temporary();
        self.prepared_vsids = false;

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

        for c in constraint.iter_mut() {
            assert!(!c.is_empty());
            // the original final slot is an activation
            *c.last_mut().unwrap() = !self.constrain_act.lit();
            let c = self.simplify_clause(c);
            if c.is_empty() {
                continue;
            };
            if c.len() == 1 {
                return false;
            }
            self.add_clause_inner(c, ClauseKind::Temporary);
        }

        true
    }

    /// No other function in this repo has the exact name `dcs_solve`. Grep for the full name to
    /// find its call sites without unrelated solver noise.
    /// Constraints reserve `assump[0]` and each final literal.
    pub fn dcs_solve(
        &mut self,
        assump: &mut [Lit],
        constraint: &mut [&mut [Lit]],
        domain: &[Var],
        restart_limit: u32,
    ) -> Option<bool> {
        if self.trivial_unsat {
            self.unsat_core.clear();
            return Some(false);
        }
        self.num_solve += 1;
        if self.propagate() != CREF_NONE {
            self.trivial_unsat = true;
            self.unsat_core.clear();
            return Some(false);
        }
        let search_assump = if !constraint.is_empty() {
            assert!(!assump.is_empty());
            assump[0] = self.constrain_act.lit();
            if !self.new_round(domain, &assump[1..], constraint, true) {
                self.unsat_core.clear();
                return Some(false);
            };
            assump
        } else {
            assert!(self.new_round(domain, assump, constraint, true));
            assump
        };
        self.clean_learnt(true);
        self.simplify();
        self.watchers.maybe_compact();
        let res = self.search_with_restart(search_assump, restart_limit);
        res
    }

    /// Unconstrained local-domain SAT query with the ordinary unlimited restart budget.
    pub fn dcs_solve_nocst(&mut self, assump: &[Lit]) -> bool {
        if self.trivial_unsat {
            self.unsat_core.clear();
            return false;
        }
        self.num_solve += 1;
        if self.propagate() != CREF_NONE {
            self.trivial_unsat = true;
            self.unsat_core.clear();
            return false;
        }
        assert!(self.new_round(&[], assump, &mut [], true));
        self.clean_learnt(true);
        self.simplify();
        self.watchers.maybe_compact();
        self.search_with_restart(assump, u32::MAX).unwrap()
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
