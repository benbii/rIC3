mod aux;
pub mod certify;
mod ctx;
pub mod frts;
pub mod lift;
mod live;
pub mod nodep;
mod others;
pub mod preproc_serde;
mod refactor;
pub mod scorr;
mod simp;
mod simulate;
pub mod unroll;

pub use ctx::*;
use ahash::{HashMap, HashSet};
use logicrs::{DagCnf, Lit, LitVec, LitVvec, Var, VarVMap, satif::Satif};
use std::{
    fmt::{self, Display},
    mem::take,
};

#[derive(Default, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Transys {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub next: HashMap<Var, Lit>,
    pub init: HashMap<Var, Lit>,
    /// multiple bads, not single cube
    pub bad: LitVec,
    pub constraint: LitVec,
    pub justice: LitVec,
    pub rel: DagCnf,
}

impl Transys {
    #[inline]
    pub fn max_var(&self) -> Var {
        self.rel.max_var()
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.rel.new_var()
    }

    #[inline]
    pub fn new_var_to(&mut self, var: Var) {
        while self.max_var() < var {
            self.new_var();
        }
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
    pub fn is_latch(&self, v: Var) -> bool {
        self.next.contains_key(&v)
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
        self.rel.clause()
    }

    #[inline]
    pub fn var_next(&self, var: Var) -> Var {
        self.next(var.lit()).var()
    }

    pub fn lits_next<'a>(&self, lits: impl IntoIterator<Item = &'a Lit>) -> LitVec {
        lits.into_iter().map(|l| self.next(*l)).collect()
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

    pub fn load_trans(&self, satif: &mut impl Satif, constraint: bool) {
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

    pub fn statistic(&self) -> String {
        format!(
            "{} vars, {} inputs, {} latches, {} clauses, {} constraints",
            self.max_var(),
            self.input().count(),
            self.latch().count(),
            self.trans().count(),
            self.constraint().count(),
        )
    }

    #[inline]
    pub fn add_input(&mut self, input: Var) {
        self.input.push(input);
    }

    #[inline]
    pub fn add_latch(&mut self, latch: Var, init: Option<Lit>, next: Lit) {
        self.latch.push(latch);
        self.next.insert(latch, next);
        if let Some(i) = init {
            self.init.insert(latch, i);
        }
    }

    #[inline]
    pub fn add_init(&mut self, latch: Var, init: Lit) {
        self.init.insert(latch, init);
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn unique_prime(&mut self, rst: &mut VarVMap) {
        let mut unique = HashSet::default();
        unique.insert(Var::CONST);
        for l in self.latch.clone() {
            let mut n = self.next[&l];
            if unique.contains(&n.var()) {
                let u = self.rel.new_var().lit();
                self.rel.add_rel(u.var(), &LitVvec::cnf_assign(u, n));
                self.next.insert(l, u);
                if let Some(&r) = rst.get(&n.var()) {
                    rst.insert(u.var(), r);
                }
                n = u;
            }
            unique.insert(n.var());
        }
    }

    pub fn add_init_var(&mut self) -> Var {
        let iv = self.new_var();
        self.add_latch(iv, Some(Lit::constant(true)), Lit::constant(false));
        iv
    }

    pub fn compress_bads(&mut self) {
        if self.bad.len() <= 1 {
            return;
        }
        let bad = take(&mut self.bad);
        self.bad = LitVec::from(self.rel.new_or(bad));
    }
}

impl Display for Transys {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "input: {:?}", self.input)?;
        for l in self.latch.iter() {
            if let Some(i) = self.init.get(l) {
                writeln!(f, "latch {l}, next {}, init {i}", self.next(l.lit()))?;
            } else {
                writeln!(f, "latch {l}, next {}", self.var_next(*l))?;
            }
        }
        writeln!(f, "rel:")?;
        self.rel.fmt(f)?;
        writeln!(f, "bad: {:?}", self.bad)?;
        writeln!(f, "constraint: {:?}", self.constraint)
    }
}
