use super::Transys;
use crate::transys::certify::BlWitness;
use logicrs::{Lit, LitMap, LitVec, Var, VarRange, satif::Satif};
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct TransysUnroll {
    pub ts: Transys,
    pub num_unroll: usize,
    pub max_var: Var,
    pub next_map: LitMap<Vec<Lit>>,
}

impl Deref for TransysUnroll {
    type Target = Transys;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.ts
    }
}

impl TransysUnroll {
    pub fn new(ts: &Transys) -> Self {
        let mut next_map: LitMap<Vec<_>> = LitMap::new();
        next_map.reserve(ts.max_var());
        for v in VarRange::new_inclusive(Var::CONST, ts.max_var()) {
            let l = v.lit();
            next_map[l].push(l);
            next_map[!l].push(!l);
        }
        Self {
            ts: ts.clone(),
            num_unroll: 0,
            max_var: ts.max_var(),
            next_map,
        }
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.max_var
    }

    #[inline]
    pub fn var_next(&self, var: Var, num: usize) -> Var {
        self.next_map[var.lit()][num].var()
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit, num: usize) -> Lit {
        self.next_map[lit][num]
    }

    #[inline]
    pub fn lits_next(
        &self,
        lits: impl IntoIterator<Item = impl AsRef<Lit>>,
        num: usize,
    ) -> impl Iterator<Item = Lit> {
        lits.into_iter()
            .map(move |l| self.lit_next(*l.as_ref(), num))
    }

    pub fn unroll(&mut self, no_conn_abst: bool) {
        let false_lit = Lit::constant(false);
        self.next_map[false_lit].push(false_lit);
        self.next_map[!false_lit].push(!false_lit);
        if no_conn_abst {
            for l in self.ts.latch() {
                let l = l.lit();
                let next = self.lit_next(self.ts.next(l), self.num_unroll);
                self.next_map[l].push(next);
                self.next_map[!l].push(!next);
            }
        }
        for v in VarRange::new_inclusive(Var::CONST, self.ts.max_var()) {
            let l = v.lit();
            if self.next_map[l].len() == self.num_unroll + 1 {
                self.max_var += 1;
                let new = self.max_var.lit();
                self.next_map[l].push(new);
                self.next_map[!l].push(!new);
            }
            assert!(self.next_map[l].len() == self.num_unroll + 2);
        }
        self.num_unroll += 1;
    }

    pub fn unroll_to(&mut self, k: usize) {
        while self.num_unroll < k {
            self.unroll(true)
        }
    }

    pub fn load_trans<S: Satif + ?Sized>(&self, satif: &mut S, u: usize, constraint: bool) {
        satif.new_var_to(self.max_var);
        for c in self.ts.trans() {
            let c: Vec<Lit> = c.iter().map(|l| self.lit_next(*l, u)).collect();
            satif.add_clause(&c);
        }
        if constraint {
            for c in self.ts.constraint() {
                let c = self.lit_next(c, u);
                satif.add_clause(&[c]);
            }
        }
    }

    pub fn witness<S: Satif + ?Sized>(&self, satif: &S) -> BlWitness {
        let mut wit = BlWitness::default();
        for k in 0..=self.num_unroll {
            let mut w = LitVec::new();
            for l in self.ts.input() {
                let l = l.lit();
                let kl = self.lit_next(l, k);
                if let Some(v) = satif.sat_value(kl) {
                    w.push(l.not_if(!v));
                }
            }
            wit.input.push(w);
            let mut w = LitVec::new();
            for l in self.ts.latch() {
                let l = l.lit();
                let kl = self.lit_next(l, k);
                if let Some(v) = satif.sat_value(kl) {
                    w.push(l.not_if(!v));
                }
            }
            wit.state.push(w);
        }
        wit
    }

    pub fn compile(&self) -> Transys {
        if self.num_unroll == 0 {
            return self.ts.clone();
        }
        let mut input = Vec::new();
        let mut constraint = LitVec::new();
        let mut rel = self.ts.rel.clone();
        for u in 0..=self.num_unroll {
            for i in self.ts.input.iter() {
                input.push(self.lit_next(i.lit(), u).var());
            }
            for c in self.ts.constraint.iter() {
                let c = self.lit_next(*c, u);
                constraint.push(c);
            }
            for (v, cls) in self.ts.rel.iter() {
                let v = self.var_next(v, u);
                if v <= rel.max_var() && rel.has_rel(v) {
                    continue;
                }
                let cls: Vec<LitVec> = cls.iter().map(|c| self.lits_next(c, u).collect()).collect();
                rel.add_rel(v, &cls);
            }
        }
        assert!(self.ts.justice.is_empty());
        let bad: LitVec = self.lits_next(&self.ts.bad, self.num_unroll).collect();
        let mut ts = Transys {
            input,
            bad,
            constraint,
            rel,
            ..Default::default()
        };
        for &l in self.ts.latch.iter() {
            ts.add_latch(
                l,
                self.ts.init(l),
                self.lit_next(self.ts.var_next_lit(l), self.num_unroll),
            );
        }
        ts
    }

    pub fn internal_signals(&self) -> Transys {
        assert!(self.num_unroll == 1);
        let keep = self.ts.rel.fanouts(self.ts.input());
        let mut rel = self.ts.rel.clone();
        for (v, cls) in self.ts.rel.iter() {
            if keep.contains(&v) {
                continue;
            }
            let v = self.var_next(v, 1);
            if v <= rel.max_var() && rel.has_rel(v) {
                continue;
            }
            let cls: Vec<LitVec> = cls.iter().map(|c| self.lits_next(c, 1).collect()).collect();
            rel.add_rel(v, &cls);
        }
        let mut ts = Transys {
            input: self.ts.input.clone(),
            bad: self.ts.bad.clone(),
            constraint: self.ts.constraint.clone(),
            rel,
            ..Default::default()
        };
        for v in VarRange::new_inclusive(Var::new(1), self.ts.max_var()) {
            if !keep.contains(&v) {
                ts.add_latch(v, self.ts.init(v), self.lit_next(v.lit(), 1));
            }
        }

        // TODO: EXTEND INIT

        assert!(self.ts.justice.is_empty());
        ts
    }

    pub fn internal_signals_with_full_prime(&self) -> Transys {
        assert!(self.num_unroll == 1);
        let keep = self.ts.rel.fanouts(self.ts.input());
        let mut rel = self.ts.rel.clone();

        let mut input = self.ts.input.clone();
        input.extend(self.ts.input().map(|v| self.var_next(v, 1)));
        let mut constraint = self.ts.constraint.clone();
        constraint.extend(self.lits_next(self.ts.constraint(), 1));

        for (v, cls) in self.ts.rel.iter() {
            let v = self.var_next(v, 1);
            if v <= rel.max_var() && rel.has_rel(v) {
                continue;
            }
            let cls: Vec<LitVec> = cls.iter().map(|c| self.lits_next(c, 1).collect()).collect();
            rel.add_rel(v, &cls);
        }

        assert!(self.ts.justice.is_empty());
        let bad: LitVec = self.lits_next(&self.ts.bad, 1).collect();
        let mut ts = Transys {
            input,
            bad,
            constraint,
            rel,
            ..Default::default()
        };
        for v in VarRange::new_inclusive(Var::new(1), self.ts.max_var()) {
            if !keep.contains(&v) {
                ts.add_latch(v, self.ts.init(v), self.lit_next(v.lit(), 1));
            }
        }

        ts
    }
}
