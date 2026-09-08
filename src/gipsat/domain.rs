use super::{DagCnfSolver, state::VarState};
use logicrs::{DagCnf, Lit, Var, VarMap};
use std::slice;

#[derive(Clone, Default)]
/// Alternate design 1: adding a Var->Latch Slot flat layout map;
/// however for non-INN it seems that latches are already concentrated in low var range
/// and Vec<GuardLatch> memory footpoint isn't quite large.
/// Alternate design 2: split the `seen` field into `seen, dirty, init`. `u32` for `seen`
/// feels sufficient if so. Don't know if 31b counter with 1 merged field is enough.
/// Note: access to VarMap is unchecked by default
struct GuardDomain {
    /// inner Vec is never accessed by index (always iterate).
    /// Not considering arena for now until the basic version shows primising results.
    pub out: VarMap<Vec<Var>>,
    /// low1b: dirty bit; low2b: init assignment; high62b: counter
    pub seen: VarMap<u64>,
}

pub(super) struct Domain {
    set: Vec<Var>,
    fixed: usize,
    /// inner field size 0 <-> guard disabled
    /// (unroll the two inner fields feels suitable now)
    guard: GuardDomain,
}

impl Clone for Domain {
    fn clone(&self) -> Self {
        let mut set = Vec::with_capacity(self.set.capacity());
        set.extend_from_slice(&self.set);
        Self {
            set,
            fixed: self.fixed,
            guard: self.guard.clone(),
        }
    }
}

#[inline]
fn realinsrt(set: &mut Vec<Var>, var: Var, state: &mut VarState) {
    let inserted = usize::from(state.insert_domain(var));
    let len = set.len();
    debug_assert!(len < set.capacity());
    unsafe {
        set.as_mut_ptr().add(len).write(var);
        set.set_len(len + inserted);
    }
}

impl Domain {
    pub fn new(max_var: Var, state: &mut VarState) -> Self {
        let mut res = Self {
            set: Vec::with_capacity((max_var.0 as usize) + 2),
            fixed: 0,
            guard: Default::default(),
        };
        res.insert(Var::CONST, state);
        res.fixed = 1;
        res
    }

    pub fn reset(&mut self, state: &mut VarState) {
        while self.set.len() > self.fixed {
            let v = self.set.pop().unwrap();
            state.remove_domain(v);
        }
    }

    #[inline]
    pub fn insert(&mut self, var: Var, state: &mut VarState) {
        // Fuck the broken borrow checker. Why is the checker so dumb that it cannot find
        // self.guard remain unchanged? Dumbest hop ever needed.
        realinsrt(&mut self.set, var, state)
    }

    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, Var> {
        self.set.iter()
    }

    fn close(&mut self, mut now: usize, dc: &DagCnf, state: &mut VarState) {
        if !self.guard.seen.is_empty() {
            while now < self.set.len() {
                let var = self.set[now];
                now += 1;
                for &dep in dc.dep(var) {
                    // standard transitive fanin insertion first
                    self.insert(dep, state);
                }
                // the domain contains both comb vars and latches; if it's a comb var,
                // guard[var].out should be empty, dirty bit should be 0. Still some extra ops.
                if (var.0 as usize) >= self.guard.seen.len() {
                    continue;
                }
                // dirty flag is often checked alongside last-seen counter access,
                // hence their merging. However seen flag is also independently accessed when
                // extending latch frontier, so probably a separate Box<[bool]> is better.
                let seen = &mut self.guard.seen[var];
                let out = &mut self.guard.out[var];
                if *seen & 1 != 0 {
                    out.sort_unstable();
                    out.dedup();
                    *seen ^= 1;
                }
                *seen += 4;
                for target in out {
                    realinsrt(&mut self.set, *target, state);
                }
            }
        } else {
            while now < self.set.len() {
                let var = self.set[now];
                now += 1;
                for &dep in dc.dep(var) {
                    self.insert(dep, state);
                }
            }
        }
    }

    fn enable_guard(&mut self, latch: &[Var], init: &[bool]) {
        assert_eq!(latch.len(), init.len());
        let Some(max_latch) = latch.iter().copied().max() else {
            return;
        };
        self.guard.seen = VarMap::new_with(max_latch);
        for (i, &var) in latch.iter().enumerate() {
            self.guard.seen[var] = (init[i] as u64) << 1;
        }
        self.guard.out = VarMap::new_with(max_latch);
    }

    pub(super) fn add_guard(&mut self, clause: &[Lit], dc: &DagCnf, state: &mut VarState) -> bool {
        if self.guard.seen.is_empty() {
            return false;
        }
        debug_assert_eq!(self.set.len(), self.fixed);
        let mut first = None;
        let mut best = None;
        for &lit in clause {
            // must be a latch (primary input)
            debug_assert!((lit.var().0 as usize) < self.guard.seen.len());
            // init assignment is always accessed with last-seen counter, hence their merging
            // However if `continue` is hit most of the time then probably not worthwhile.
            let seen = self.guard.seen[lit.var()];
            if (seen & 2 != 0) != lit.polarity() {
                continue;
            }
            // Alternate design 1 would introduce complication here, although compared to `close`,
            // `add_clause` is absolutely cold code.
            first.get_or_insert(lit.var());
            if !state.get(lit.var()).in_domain() {
                if best.is_none_or(|(old, _)| seen < old) {
                    best = Some((seen, lit.var()));
                }
            }
        }
        let source = best
            .map(|(_, var)| var)
            .or(first)
            .expect("frame lemma is false in initial model");
        if state.get(source).in_domain() {
            let now = self.fixed;
            for &lit in clause {
                realinsrt(&mut self.set, lit.var(), state);
            }
            self.close(now, dc, state);
            self.fixed = self.set.len();
        } else {
            let out = &mut self.guard.out[source];
            let old_len = out.len();
            out.extend(clause.iter().map(|l| l.var()).filter(|&v| v != source));
            self.guard.seen[source] |= (old_len != out.len()) as u64;
        }
        true
    }

    pub fn enable_local(
        &mut self,
        domain: &[Var],
        assump: &[Lit],
        constraint: &[&mut [Lit]],
        dc: &DagCnf,
        state: &mut VarState,
    ) {
        self.reset(state);
        for &r in domain {
            self.insert(r, state);
        }
        for l in assump {
            self.insert(l.var(), state);
        }
        for c in constraint {
            debug_assert!(!c.is_empty());
            for l in &c[..c.len() - 1] {
                self.insert(l.var(), state);
            }
        }
        self.close(self.fixed, dc, state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::LitVec;
    use std::sync::Arc;

    #[test]
    fn insertion_keeps_a_spare_slot() {
        let max_var = Var::new(3);
        let mut state = VarState::new_with(max_var);
        let mut domain = Domain::new(max_var, &mut state);

        for raw in 1..=max_var.0 as usize {
            domain.insert(Var::new(raw), &mut state);
        }
        assert_eq!(domain.set.len(), max_var.0 as usize + 1);
        assert!(domain.set.len() < domain.set.capacity());

        domain.insert(Var::CONST, &mut state);
        assert_eq!(domain.set.len(), max_var.0 as usize + 1);

        let cloned = domain.clone();
        assert!(cloned.set.len() < cloned.set.capacity());
    }

    #[test]
    fn constant_stays_in_the_domain_across_temporary_domains() {
        let mut dc = DagCnf::new();
        let x = dc.new_var();
        let n = dc.new_var();
        dc.add_rel(n, &[LitVec::from([n.lit(), x.lit(), Lit::constant(false)])]);
        assert_eq!(dc.dep(n), &[x]);

        let mut solver = DagCnfSolver::new(Arc::new(dc));
        assert!(solver.domain_has(Var::CONST));

        solver.set_domain([n.lit(), x.lit()], &[]);
        assert!(solver.domain_has(Var::CONST));
        assert_eq!(solver.domain.set[0], Var::CONST);
        assert!(solver.domain.fixed >= 1);
        assert_eq!(solver.dcs_solve_nocst(&[!n.lit(), !x.lit()]), false);
        assert_eq!(solver.dcs_solve_nocst(&[!n.lit(), x.lit()]), true);
        assert!(solver.domain_has(Var::CONST));

        solver.unset_domain();
        solver.reset();
        assert!(solver.domain_has(Var::CONST));
        assert_eq!(solver.domain.set.len(), solver.domain.fixed);
    }

    #[test]
    fn temporary_constraint_only_propagates_inside_preseeded_domain() {
        let mut dc = DagCnf::new();
        let a = dc.new_var();
        let b = dc.new_var();
        let c = dc.new_var();
        let mut helper = [!a.lit(), !b.lit(), !c.lit()];
        helper.sort();
        let mut solver = DagCnfSolver::new(Arc::new(dc));

        solver.set_domain([a.lit(), b.lit()], &[]);
        assert!(
            solver
                .dcs_solve(
                    &mut [Lit::default(), a.lit(), b.lit()],
                    &mut [&mut [helper[0], helper[1], helper[2], Lit::default()]],
                    &[],
                    u32::MAX,
                )
                .unwrap()
        );
        assert!(!solver.domain_has(c));
        assert_eq!(solver.dcs_satval(!c.lit()), None);
        solver.unset_domain();

        solver.set_domain([a.lit(), b.lit()], &[c.lit()]);
        assert!(
            solver
                .dcs_solve(
                    &mut [Lit::default(), a.lit(), b.lit()],
                    &mut [&mut [helper[0], helper[1], helper[2], Lit::default()]],
                    &[],
                    u32::MAX,
                )
                .unwrap()
        );
        assert!(solver.domain_has(c));
        assert_eq!(solver.dcs_satval(!c.lit()), Some(true));
        solver.unset_domain();
    }
    #[test]
    fn empty_latch_guard_keeps_combinational_solving() {
        let mut dc = DagCnf::new();
        let a = dc.new_var();
        let b = dc.new_var();
        let both = dc.new_and([a.lit(), b.lit()]);
        let mut solver = DagCnfSolver::new(Arc::new(dc));
        solver.enable_guard_domain(&[], &[]);

        assert!(!solver.dcs_solve_nocst(&[both, !a.lit()]));
        assert!(solver.dcs_solve_nocst(&[both]));
        assert_eq!(solver.dcs_satval(b.lit()), Some(true));
    }

    #[test]
    fn guarded_clause_uses_negative_initial_literal() {
        let mut dc = DagCnf::new();
        let a = dc.new_var();
        let b = dc.new_var();
        let mut solver = DagCnfSolver::new(Arc::new(dc));
        solver.enable_guard_domain(&[a, b], &[false, false]);
        solver.add_perma_clause(&[!a.lit(), b.lit()]);

        assert!(solver.dcs_solve_nocst(&[b.lit()]));
        assert!(!solver.domain_has(a));
        assert!(solver.dcs_solve_nocst(&[a.lit()]));
        assert!(solver.domain_has(b));
    }

    #[test]
    fn guarded_clause_picks_least_seen_source() {
        let mut dc = DagCnf::new();
        let a = dc.new_var();
        let b = dc.new_var();
        let c = dc.new_var();
        let mut solver = DagCnfSolver::new(Arc::new(dc));
        solver.enable_guard_domain(&[a, b, c], &[true, true, false]);

        assert!(solver.dcs_solve_nocst(&[a.lit()]));
        solver.add_perma_clause(&[a.lit(), b.lit(), c.lit()]);
        assert!(solver.dcs_solve_nocst(&[a.lit()]));
        assert!(!solver.domain_has(c));
        assert!(solver.dcs_solve_nocst(&[b.lit()]));
        assert!(solver.domain_has(c));
    }

    #[test]
    fn guarded_closure_is_transitive() {
        let mut dc = DagCnf::new();
        let a = dc.new_var();
        let b = dc.new_var();
        let c = dc.new_var();
        let mut solver = DagCnfSolver::new(Arc::new(dc));
        solver.enable_guard_domain(&[a, b, c], &[true, true, false]);
        solver.add_perma_clause(&[a.lit(), !b.lit()]);
        solver.add_perma_clause(&[b.lit(), c.lit()]);

        assert!(solver.dcs_solve_nocst(&[a.lit()]));
        assert!(solver.domain_has(c));
    }

    #[test]
    fn fixed_guard_promotes_clause_domain() {
        let mut dc = DagCnf::new();
        let a = dc.new_var();
        let b = dc.new_var();
        let c = dc.new_var();
        let mut solver = DagCnfSolver::new(Arc::new(dc));
        solver.add_perma_clause(&[a.lit(), b.lit()]);
        solver.enable_guard_domain(&[a, b, c], &[true, false, false]);
        solver.add_perma_clause(&[a.lit(), c.lit()]);

        assert!(solver.domain_has(c));
        assert_eq!(solver.domain.set.len(), solver.domain.fixed);
    }
}

impl DagCnfSolver {
    pub fn add_domain(&mut self, var: Var, deps: bool) {
        assert!(self.highest_level() == 0);
        if !self.state.value(var).is_none() {
            return;
        }
        self.domain.reset(&mut self.state);
        debug_assert!(self.domain.guard.seen.is_empty());
        self.domain.insert(var, &mut self.state);
        if deps {
            let mut queue = self.dc.dep(var).to_vec();
            while let Some(d) = queue.pop() {
                if self.state.get(d).in_domain() {
                    continue;
                }
                self.domain.insert(d, &mut self.state);
                for dd in self.dc.dep(d) {
                    queue.push(*dd);
                }
            }
        }
        self.domain.fixed = self.domain.set.len();
    }

    pub fn enable_guard_domain(&mut self, latch: &[Var], init: &[bool]) {
        self.domain.enable_guard(latch, init);
    }

    #[inline]
    pub fn domain_has(&self, var: Var) -> bool {
        self.state.get(var).in_domain()
    }

    pub fn set_domain(&mut self, domain: impl IntoIterator<Item = Lit>, extra: &[Lit]) {
        self.reset();
        self.temporary_domain = true;
        let domain: Vec<_> = domain
            .into_iter()
            .chain(extra.iter().copied())
            .map(|l| l.var())
            .collect();
        self.domain
            .enable_local(&domain, &[], &[], &self.dc, &mut self.state);
        assert!(!self.state.get(self.constrain_act).in_domain());
        self.domain.insert(self.constrain_act, &mut self.state);
        self.vsids.enable_bucket = true;
        self.vsids.bucket.clear(&mut self.state);
        self.push_to_vsids();
    }

    pub fn unset_domain(&mut self) {
        self.temporary_domain = false;
    }

    pub fn push_to_vsids(&mut self) {
        debug_assert!(self.highest_level() == 0);
        let mut now = 0;
        while now < self.domain.fixed {
            let d = self.domain.set[now];
            if d.is_constant() {
                now += 1;
            } else if self.state.value(d).is_none() {
                self.vsids.push(d, &mut self.state);
                now += 1;
            } else {
                self.domain.set.swap(now, self.domain.fixed - 1);
                let v = self.domain.set.swap_remove(self.domain.fixed - 1);
                self.state.remove_domain(v);
                self.domain.fixed -= 1;
            }
        }
        while now < self.domain.set.len() {
            self.vsids.push(self.domain.set[now], &mut self.state);
            now += 1;
        }
    }

    pub fn prepare_vsids(&mut self) {
        if !self.prepared_vsids && !self.temporary_domain {
            self.prepared_vsids = true;
            for d in self.domain.iter() {
                if self.state.value(*d).is_none() {
                    self.vsids.push(*d, &mut self.state);
                }
            }
        }
    }
}
