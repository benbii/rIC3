use crate::RseedMap as HashMap;
use crate::transys::{Transys, unroll::TransysUnroll};
use logicrs::{Lit, LitVec, Var, VarVMap};
use std::sync::Arc;

#[derive(Clone, Debug, Default)]
pub struct BlWitness {
    pub input: Vec<LitVec>,
    pub state: Vec<LitVec>,
    pub bad_id: usize,
}

impl BlWitness {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[allow(clippy::len_without_is_empty)]
    #[inline]
    pub fn len(&self) -> usize {
        self.input.len()
    }

    pub fn map_var(&self, f: impl Fn(Var) -> Var) -> Self {
        let input = self.input.iter().map(|w| w.map_var(&f)).collect();
        let state = self.state.iter().map(|w| w.map_var(&f)).collect();
        Self {
            input,
            state,
            bad_id: self.bad_id,
        }
    }

    pub fn filter_map_var(&self, f: impl Fn(Var) -> Option<Var>) -> Self {
        let input = self.input.iter().map(|w| w.filter_map_var(&f)).collect();
        let state = self.state.iter().map(|w| w.filter_map_var(&f)).collect();
        Self {
            input,
            state,
            bad_id: self.bad_id,
        }
    }

    pub fn map(&self, f: impl Fn(Lit) -> Lit) -> Self {
        let input = self.input.iter().map(|w| w.map(&f)).collect();
        let state = self.state.iter().map(|w| w.map(&f)).collect();
        Self {
            input,
            state,
            bad_id: self.bad_id,
        }
    }

    pub fn filter_map(&self, f: impl Fn(Lit) -> Option<Lit>) -> Self {
        let input = self.input.iter().map(|w| w.filter_map(&f)).collect();
        let state = self.state.iter().map(|w| w.filter_map(&f)).collect();
        Self {
            input,
            state,
            bad_id: self.bad_id,
        }
    }

    pub fn concat(iter: impl IntoIterator<Item = BlWitness>) -> Self {
        let mut res = Self::new();
        for witness in iter {
            res.input.extend(witness.input);
            res.state.extend(witness.state);
        }
        res
    }

    pub fn exact_init_state(&mut self, ts: &Transys) {
        let assump: Vec<_> = self.state[0]
            .iter()
            .chain(self.input[0].iter())
            .copied()
            .collect();
        let mut solver = crate::cadical::CaDiCaL::new();
        ts.load_init(&mut solver);
        ts.load_trans(&mut solver, true);
        assert!(solver.cad_solve(&assump));
        let mut state = LitVec::new();
        for &lat in &ts.latch {
            let b = solver.cad_satval(lat.lit()).unwrap();
            state.push(Lit::new(lat, b));
        }
        let mut input = LitVec::new();
        for &i in &ts.input {
            let b = solver.cad_satval(i.lit()).unwrap();
            input.push(Lit::new(i, b));
        }
        (self.input[0], self.state[0]) = (input, state);
    }

    pub fn exact_state(&mut self, ts: &Transys, init: bool) {
        let mut uts = TransysUnroll::new(Arc::new(ts.clone()));
        uts.unroll_to(self.len() - 1);
        let mut solver = crate::cadical::CaDiCaL::new();
        if init {
            ts.load_init(&mut solver);
        }
        for k in 0..=uts.num_unroll {
            uts.load_trans(&mut solver, k, true);
            for l in self.state[k]
                .iter()
                .chain(self.input[k].iter())
                .map(|x| uts.lit_next(*x, k))
            {
                solver.add_clause(&[l]);
            }
        }
        assert!(solver.cad_solve(&[]));
        *self = uts.witness(&solver);
        self.bad_id = ts
            .bad
            .iter()
            .position(|&b| {
                solver
                    .cad_satval(uts.lit_next(b, uts.num_unroll))
                    .is_some_and(|v| v)
            })
            .unwrap();
    }
}

pub type BlProof = Transys;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Restore {
    pub(crate) bvmap: VarVMap,
    pub(crate) fvmap: VarVMap,
    eqmap: HashMap<Var, LitVec>,
    init_var: Option<Var>,
}

impl Restore {
    pub fn new(ts: &Transys) -> Self {
        Self {
            bvmap: VarVMap::new_self_map(ts.max_var()),
            fvmap: VarVMap::new_self_map(ts.max_var()),
            eqmap: HashMap::default(),
            init_var: None,
        }
    }

    pub fn forward(&self, l: Lit) -> Lit {
        self.fvmap.lit_map(l).unwrap()
    }

    pub fn restore(&self, l: Lit) -> Lit {
        self.bvmap.lit_map(l).unwrap()
    }

    pub fn try_forward(&self, l: Lit) -> Option<Lit> {
        self.fvmap.lit_map(l)
    }

    pub fn try_restore(&self, l: Lit) -> Option<Lit> {
        self.bvmap.lit_map(l)
    }

    pub fn restore_var(&self, v: Var) -> Var {
        self.bvmap[v]
    }

    #[inline]
    pub fn remove(&mut self, v: Var) {
        if let Some(rv) = self.bvmap.remove(&v) {
            self.fvmap.remove(&rv);
        }
        if let Some(iv) = self.init_var
            && iv == v
        {
            self.init_var = None;
        }
    }

    #[inline]
    pub fn add_restore(&mut self, v: Var, l: Var) {
        assert!(!self.bvmap.contains_key(&v));
        self.bvmap.insert(v, l);
        self.fvmap.insert(l, v);
    }

    #[inline]
    pub fn map_var(&mut self, map: &impl Fn(Var) -> Var) {
        self.init_var = self.init_var.map(&map);
        self.bvmap.map_key(map);
        self.fvmap.map_value(map);
    }

    #[inline]
    pub fn filter_map_var(&mut self, map: &impl Fn(Var) -> Option<Var>) {
        self.init_var = self.init_var.map(|l| map(l).unwrap());
        self.bvmap.filter_map_key(map);
        self.fvmap.filter_map_value(map);
    }

    #[inline]
    pub fn replace(&mut self, x: Var, y: Lit) {
        let xm = self.bvmap[x].lit().not_if(!y.polarity());
        let ym = self.bvmap[y.var()];
        self.eqmap.entry(ym).or_default().push(xm);
        if let Some(fv) = self.bvmap.remove(&x) {
            self.fvmap.remove(&fv);
        }
        if let Some(iv) = self.init_var
            && iv == x
        {
            assert!(y.polarity());
            self.init_var = Some(y.var());
        }
    }

    pub fn eq_invariant(&self) -> Vec<LitVec> {
        let mut res = Vec::new();
        for (v, eq) in self.eqmap.iter() {
            for &e in eq.iter() {
                res.push(LitVec::from([v.lit(), !e]));
                res.push(LitVec::from([!v.lit(), e]));
            }
        }
        res
    }

    pub fn init_var(&self) -> Option<Var> {
        self.init_var
    }

    pub fn get_init_var(&mut self, ts: &mut Transys) -> Var {
        if let Some(iv) = self.init_var {
            return iv;
        }
        let iv = ts.add_init_var();
        self.init_var = Some(iv);
        iv
    }

    pub fn restore_eq_state(&self, s: &LitVec) -> LitVec {
        let mut res = s.clone();
        for l in s.iter() {
            if let Some(eq) = self.eqmap.get(&l.var()) {
                for &el in eq.iter() {
                    res.push(el.not_if(!l.polarity()));
                }
            }
        }
        res.sort();
        res.dedup();
        res
    }

    pub fn restore_witness(&self, wit: &BlWitness) -> BlWitness {
        let iv = self.init_var();
        let mut wit = wit.filter_map(|l| (iv != Some(l.var())).then(|| self.restore(l)));
        for s in wit.state.iter_mut() {
            *s = self.restore_eq_state(s);
        }
        wit
    }
}
