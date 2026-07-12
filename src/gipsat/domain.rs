use super::{DagCnfSolver, state::VarState};
use logicrs::{DagCnf, Lit, LitVec, Var};
use std::{ops::Index, slice};

#[derive(Clone)]
pub struct Domain {
    set: Vec<Var>,
    pub fixed: u32,
}

impl Domain {
    pub fn new(state: &mut VarState) -> Self {
        let mut res = Self {
            set: Vec::new(),
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
        if state.insert_domain(var) {
            self.set.push(var);
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
        constraint: &[LitVec],
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
            for l in c.iter() {
                self.insert(l.var(), state);
            }
        }
        let mut now = self.fixed;
        while now < self.len() {
            let v = self[now];
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

impl Index<u32> for Domain {
    type Output = Var;

    #[inline]
    fn index(&self, index: u32) -> &Self::Output {
        &self.set[index as usize]
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

    pub fn set_domain(&mut self, domain: impl IntoIterator<Item = Lit>) {
        self.reset();
        self.temporary_domain = true;
        let domain: Vec<_> = domain.into_iter().map(|l| l.var()).collect();
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
            let d = self.domain[now];
            if self.state.value(d).is_none() {
                self.vsids.push(d, &mut self.state);
                now += 1;
            } else {
                self.domain.swap(now, self.domain.fixed - 1);
                self.domain.remove(self.domain.fixed - 1, &mut self.state);
                self.domain.fixed -= 1;
            }
        }
        while now < self.domain.len() {
            self.vsids.push(self.domain[now], &mut self.state);
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
