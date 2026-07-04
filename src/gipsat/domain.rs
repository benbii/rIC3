use super::DagCnfSolver;
use logicrs::{DagCnf, Lit, LitVec, Var, VarAssign, VarMap};
use std::{ops::Index, slice};

#[derive(Clone)]
pub struct Domain {
    set: Vec<Var>,
    has: VarMap<bool>,
    pub fixed: u32,
}

impl Domain {
    pub fn new_with(var: Var) -> Self {
        let mut res = Self {
            set: Vec::new(),
            has: VarMap::new_with(var),
            fixed: 0,
        };
        res.insert(Var::CONST);
        res.fixed = 1;
        res
    }

    pub fn reserve(&mut self, var: Var) {
        self.has.reserve(var);
    }

    pub fn reset(&mut self) {
        while self.len() > self.fixed {
            let v = self.set.pop().unwrap();
            self.has[v] = false;
        }
    }

    #[inline]
    pub fn insert(&mut self, var: Var) {
        if !self.has[var] {
            self.set.push(var);
            self.has[var] = true;
        }
    }

    #[inline]
    fn remove(&mut self, i: u32) {
        let v = self.set.swap_remove(i as usize);
        self.has[v] = false;
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
        _value: &VarAssign,
    ) {
        self.reset();
        for &r in domain {
            self.insert(r);
        }
        for l in assump {
            self.insert(l.var());
        }
        for c in constraint {
            for l in c.iter() {
                self.insert(l.var());
            }
        }
        let mut now = self.fixed;
        while now < self.len() {
            let v = self[now];
            now += 1;
            for d in dc.dep(v).iter() {
                // if value.v(d.lit()).is_none() {
                self.insert(*d);
                // }
            }
        }
    }

    #[inline]
    pub fn has(&self, var: Var) -> bool {
        self.has[var]
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
        if !self.value.var(var).is_none() {
            return;
        }
        self.domain.reset();
        self.domain.insert(var);
        if deps {
            let mut queue = self.dc.dep(var).to_vec();
            while let Some(d) = queue.pop() {
                if self.domain.has(d) {
                    continue;
                }
                self.domain.insert(d);
                for dd in self.dc.dep(d).iter() {
                    queue.push(*dd);
                }
            }
        }
        self.domain.fixed = self.domain.len();
    }

    #[inline]
    pub fn domain_has(&self, var: Var) -> bool {
        self.domain.has(var)
    }

    pub fn set_domain(&mut self, domain: impl IntoIterator<Item = Lit>) {
        self.reset();
        self.temporary_domain = true;
        let domain: Vec<_> = domain.into_iter().map(|l| l.var()).collect();
        self.domain
            .enable_local(&domain, &[], &[], &self.dc, &self.value);
        assert!(!self.domain.has(self.constrain_act));
        self.domain.insert(self.constrain_act);
        self.vsids.enable_bucket = true;
        self.vsids.bucket.clear();
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
            if self.value.var(d).is_none() {
                self.vsids.push(d);
                now += 1;
            } else {
                self.domain.swap(now, self.domain.fixed - 1);
                self.domain.remove(self.domain.fixed - 1);
                self.domain.fixed -= 1;
            }
        }
        while now < self.domain.len() {
            self.vsids.push(self.domain[now]);
            now += 1;
        }
    }

    pub fn prepare_vsids(&mut self) {
        if !self.prepared_vsids && !self.temporary_domain {
            self.prepared_vsids = true;
            for d in self.domain.iter() {
                if self.value.var(*d).is_none() {
                    self.vsids.push(*d);
                }
            }
        }
    }
}
