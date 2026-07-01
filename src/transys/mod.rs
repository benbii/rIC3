pub mod certify;
pub mod frts;
pub mod lift;
mod live;
pub mod nodep;
mod others;
pub mod scorr;
mod simp;
pub mod unroll;

use logicrs::{DagCnf, Lit, LitVec, LitVvec, OptionU32, Var, VarMap, satif::Satif};
use std::{
    fmt::{self, Display},
    sync::Arc,
};

#[derive(Default, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Transys {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub next: VarMap<OptionU32>,
    pub init: VarMap<OptionU32>,
    /// multiple bads, not single cube
    pub bad: LitVec,
    pub constraint: LitVec,
    pub justice: LitVec,
    pub rel: Arc<DagCnf>,
}

impl Transys {
    #[inline]
    pub fn max_var(&self) -> Var {
        self.rel.max_var()
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.rel_mut().new_var()
    }

    #[inline]
    pub fn new_var_to(&mut self, var: Var) {
        while self.max_var() < var {
            self.new_var();
        }
    }

    #[inline]
    pub fn rel_mut(&mut self) -> &mut DagCnf {
        Arc::get_mut(&mut self.rel).expect("Transys.rel is shared")
    }

    #[inline]
    pub fn clone_deep(&self) -> Self {
        let mut res = self.clone();
        res.rel = Arc::new((*self.rel).clone());
        res
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
        let idx: usize = v.into();
        idx < self.next.len() && self.next[v].is_some()
    }

    #[inline]
    pub fn next(&self, lit: Lit) -> Lit {
        debug_assert!(self.next[lit.var()].is_some());
        let raw: u32 = *self.next[lit.var()] ^ (!lit.polarity() as u32);
        Lit(raw)
    }

    #[inline]
    pub fn var_next_lit(&self, var: Var) -> Lit {
        debug_assert!(self.next[var].is_some());
        Lit(*self.next[var])
    }

    #[inline]
    pub fn init(&self, latch: Var) -> Option<Lit> {
        let idx: usize = latch.into();
        if idx >= self.init.len() {
            return None;
        }
        let raw = match self.init[latch] {
            OptionU32::NONE => return None,
            raw => *raw,
        };
        Some(Lit(raw))
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
        debug_assert!(self.next[var].is_some());
        Var(*self.next[var] >> 1)
    }

    pub fn lits_next<'a>(&self, lits: impl IntoIterator<Item = &'a Lit>) -> LitVec {
        lits.into_iter().map(|l| self.next(*l)).collect()
    }

    #[inline]
    pub fn cube_subsume_init(&self, x: &[Lit]) -> bool {
        for x in x {
            if let Some(init) = self.init(x.var())
                && let Some(i) = init.try_constant()
                && i != x.polarity()
            {
                return false;
            }
        }
        true
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
        self.next.reserve(latch);
        self.init.reserve(latch);
        debug_assert!(u32::from(next) != u32::MAX);
        self.next[latch] = OptionU32::some(next.into());
        if let Some(i) = init {
            debug_assert!(u32::from(i) != u32::MAX);
            self.init[latch] = OptionU32::some(i.into());
        }
    }

    #[inline]
    pub fn add_init(&mut self, latch: Var, init: Lit) {
        self.init.reserve(latch);
        debug_assert!(u32::from(init) != u32::MAX);
        self.init[latch] = OptionU32::some(init.into());
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_init_var(&mut self) -> Var {
        let iv = self.new_var();
        self.add_latch(iv, Some(Lit::constant(true)), Lit::constant(false));
        iv
    }
}

impl Display for Transys {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "input: {:?}", self.input)?;
        for l in self.latch.iter() {
            if let Some(i) = self.init(*l) {
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
