use super::Transys;
use crate::transys::certify::{BlWitness, Restore};
use crate::RseedMap as HashMap;
use logicrs::{Cnf, Lit, LitMap, LitVec, LitVvec, Var, VarRange, satif::Satif};

#[derive(Default, Debug, Clone)]
pub struct NoDepTransys {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub next: HashMap<Var, Lit>,
    pub init: HashMap<Var, Lit>,
    pub bad: LitVec,
    pub constraint: LitVec,
    pub rel: Cnf,
}

impl NoDepTransys {
    #[inline]
    pub fn max_var(&self) -> Var {
        self.rel.max_var()
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.rel.new_var()
    }

    #[inline]
    pub fn input(&self) -> impl Iterator<Item = Var> + '_ {
        self.input.iter().copied()
    }

    #[inline]
    pub fn latch(&self) -> impl Iterator<Item = Var> + '_ {
        self.latch.iter().copied()
    }

    #[inline]
    pub fn next(&self, lit: Lit) -> Lit {
        self.next.get(&lit.var()).unwrap().not_if(!lit.polarity())
    }

    #[inline]
    pub fn init(&self, latch: Var) -> Option<Lit> {
        self.init.get(&latch).copied()
    }

    #[inline]
    pub fn constraint(&self) -> impl Iterator<Item = Lit> + '_ {
        self.constraint.iter().copied()
    }

    #[inline]
    pub fn trans(&self) -> impl Iterator<Item = &LitVec> + '_ {
        self.rel.iter()
    }

    #[inline]
    pub fn var_next(&self, var: Var) -> Var {
        self.next(var.lit()).var()
    }

    pub fn inits(&self) -> LitVvec {
        let mut cnf = LitVvec::new();
        for l in self.latch() {
            if let Some(i) = self.init(l) {
                if let Some(i) = i.try_constant() {
                    cnf.push(LitVec::from([l.lit().not_if(!i)]));
                    continue;
                }
                cnf.push(LitVec::from([l.lit(), !i]));
                cnf.push(LitVec::from([!l.lit(), i]));
            }
        }
        cnf
    }

    pub fn load_init<S: Satif + ?Sized>(&self, satif: &mut S) {
        satif.new_var_to(self.max_var());
        for cls in self.inits() {
            satif.add_clause(&cls);
        }
    }

    pub fn load_trans<S: Satif + ?Sized>(&self, satif: &mut S, constraint: bool) {
        satif.new_var_to(self.max_var());
        for c in self.trans() {
            satif.add_clause(c);
        }
        if !constraint {
            return;
        }
        for c in self.constraint() {
            satif.add_clause(&[c]);
        }
    }

    pub fn simplify(&mut self, rst: &mut Restore) {
        let mut simp_solver = crate::cadical::CaDiCaL::new();
        simp_solver.new_var_to(self.max_var());
        for c in self.trans() {
            simp_solver.add_clause(c);
        }
        let mut frozens = vec![Var::CONST];
        frozens.extend(self.bad.iter().map(|l| l.var()));
        frozens.extend(self.input.iter().chain(self.latch.iter()).copied());
        for &l in self.latch.iter() {
            if let Some(i) = self.init(l) {
                frozens.push(i.var());
            }
            frozens.push(self.var_next(l));
        }
        for c in self.constraint.iter() {
            frozens.push(c.var());
        }
        for f in frozens.iter() {
            simp_solver.set_frozen(*f, true);
        }
        if let Some(false) = simp_solver.simplify() {
            println!("warning: model trans simplified with unsat");
        }
        let mut trans = simp_solver.clauses();
        trans.push(LitVec::from([Lit::constant(true)]));
        self.rel.set_cls(trans);
        let domain_map = self.rel.rearrange(frozens);
        let map_lit = |l: &Lit| Lit::new(domain_map[l.var()], l.polarity());
        self.input = self.input.iter().map(|&v| domain_map[v]).collect();
        self.latch = self.latch.iter().map(|&v| domain_map[v]).collect();
        self.init = self
            .init
            .iter()
            .map(|(v, i)| (domain_map[*v], map_lit(i)))
            .collect();
        self.next = self
            .next
            .iter()
            .map(|(v, n)| (domain_map[*v], map_lit(n)))
            .collect();
        self.bad = self.bad.iter().map(map_lit).collect();
        self.constraint = self.constraint.iter().map(map_lit).collect();
        rst.filter_map_var(&|v| domain_map.get(&v).copied());
    }
}

#[derive(Debug, Clone)]
pub(crate) struct NoDepTransysUnroll {
    pub(crate) ts: NoDepTransys,
    pub(crate) num_unroll: usize,
    pub(crate) max_var: Var,
    next_map: LitMap<Vec<Lit>>,
}

impl NoDepTransysUnroll {
    pub(crate) fn new(ts: &NoDepTransys) -> Self {
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
    pub(crate) fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.max_var
    }

    #[inline]
    pub(crate) fn lit_next(&self, lit: Lit, num: usize) -> Lit {
        self.next_map[lit][num]
    }

    #[inline]
    pub(crate) fn lits_next(
        &self,
        lits: impl IntoIterator<Item = impl AsRef<Lit>>,
        num: usize,
    ) -> impl Iterator<Item = Lit> {
        lits.into_iter()
            .map(move |l| self.lit_next(*l.as_ref(), num))
    }

    pub(crate) fn unroll(&mut self) {
        let false_lit = Lit::constant(false);
        self.next_map[false_lit].push(false_lit);
        self.next_map[!false_lit].push(!false_lit);
        for l in self.ts.latch() {
            let l = l.lit();
            let next = self.lit_next(self.ts.next(l), self.num_unroll);
            self.next_map[l].push(next);
            self.next_map[!l].push(!next);
        }
        for v in VarRange::new_inclusive(Var::CONST, self.ts.max_var()) {
            let l = v.lit();
            if self.next_map[l].len() == self.num_unroll + 1 {
                let new = self.new_var().lit();
                self.next_map[l].push(new);
                self.next_map[!l].push(!new);
            }
            assert!(self.next_map[l].len() == self.num_unroll + 2);
        }
        self.num_unroll += 1;
    }

    pub(crate) fn unroll_to(&mut self, k: usize) {
        while self.num_unroll < k {
            self.unroll();
        }
    }

    pub(crate) fn load_trans<S: Satif + ?Sized>(&self, satif: &mut S, u: usize, constraint: bool) {
        satif.new_var_to(self.max_var);
        for c in self.ts.trans() {
            let c: Vec<Lit> = c.iter().map(|l| self.lit_next(*l, u)).collect();
            satif.add_clause(&c);
        }
        if !constraint {
            return;
        }
        for c in self.ts.constraint() {
            satif.add_clause(&[self.lit_next(c, u)]);
        }
    }

    pub(crate) fn witness<S: Satif + ?Sized>(&self, satif: &S) -> BlWitness {
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
}

impl Transys {
    pub fn remove_dep(self) -> NoDepTransys {
        NoDepTransys {
            input: self.input,
            latch: self.latch,
            next: self.next,
            init: self.init,
            bad: self.bad,
            constraint: self.constraint,
            rel: self.rel.lower(),
        }
    }
}
