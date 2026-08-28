use super::{DagCnfSolver, state::VarState};
use logicrs::{DagCnf, Lit, Var};
use std::slice;

pub struct Domain {
    set: Vec<Var>,
    pub fixed: u32,
}

impl Clone for Domain {
    fn clone(&self) -> Self {
        let mut set = Vec::with_capacity(self.set.capacity());
        set.extend_from_slice(&self.set);
        Self {
            set,
            fixed: self.fixed,
        }
    }
}

impl Domain {
    pub fn new(max_var: Var, state: &mut VarState) -> Self {
        let mut res = Self {
            set: Vec::with_capacity(max_var.0 as usize + 2),
            fixed: 0,
        };
        res.insert(Var::CONST, state);
        res.fixed = 1;
        res
    }

    pub fn reset(&mut self, state: &mut VarState) {
        while self.len() > self.fixed {
            let v = self.set.pop().unwrap();
            state.remove_domain(v);
        }
    }

    #[inline]
    pub fn insert(&mut self, var: Var, state: &mut VarState) {
        let inserted = usize::from(state.insert_domain(var));
        let len = self.set.len();
        debug_assert!(len < self.set.capacity());
        // Construction, growth, and cloning keep one slot for this unconditional write.
        unsafe {
            self.set.as_mut_ptr().add(len).write(var);
            self.set.set_len(len + inserted);
        }
    }

    #[inline]
    fn remove(&mut self, i: u32, state: &mut VarState) {
        let v = self.set.swap_remove(i as usize);
        state.remove_domain(v);
    }

    #[inline]
    fn swap(&mut self, a: u32, b: u32) {
        self.set.swap(a as usize, b as usize);
    }

    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, Var> {
        self.set.iter()
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
            for l in c[..c.len() - 1].iter() {
                self.insert(l.var(), state);
            }
        }
        let mut now = self.fixed;
        while now < self.len() {
            let v = self.set[now as usize];
            now += 1;
            for d in dc.dep(v).iter() {
                // if value.v(d.lit()).is_none() {
                self.insert(*d, state);
                // }
            }
        }
    }

    #[inline]
    pub fn len(&self) -> u32 {
        self.set.len() as _
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
        assert_eq!(solver.domain.len(), solver.domain.fixed);
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
}

impl DagCnfSolver {
    pub fn add_domain(&mut self, var: Var, deps: bool) {
        assert!(self.highest_level() == 0);
        if !self.state.value(var).is_none() {
            return;
        }
        self.domain.reset(&mut self.state);
        self.domain.insert(var, &mut self.state);
        if deps {
            let mut queue = self.dc.dep(var).to_vec();
            while let Some(d) = queue.pop() {
                if self.state.get(d).in_domain() {
                    continue;
                }
                self.domain.insert(d, &mut self.state);
                for dd in self.dc.dep(d).iter() {
                    queue.push(*dd);
                }
            }
        }
        self.domain.fixed = self.domain.len();
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
        assert!(self.highest_level() == 0);
        let mut now = 0;
        while now < self.domain.fixed {
            let d = self.domain.set[now as usize];
            if d.is_constant() {
                now += 1;
            } else if self.state.value(d).is_none() {
                self.vsids.push(d, &mut self.state);
                now += 1;
            } else {
                self.domain.swap(now, self.domain.fixed - 1);
                self.domain.remove(self.domain.fixed - 1, &mut self.state);
                self.domain.fixed -= 1;
            }
        }
        while now < self.domain.len() {
            self.vsids
                .push(self.domain.set[now as usize], &mut self.state);
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
