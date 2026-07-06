use super::IC3;
use crate::{
    BlWitness,
    cadical::CaDiCaL,
    transys::{Transys, unroll::TransysUnroll},
};
use crate::{RseedMap as HashMap, RseedSet as HashSet};
use log::{debug, info};
use logicrs::{LitVec, Var, satif::Satif};
use rand::seq::SliceRandom;
use std::sync::Arc;

pub struct LocalAbs {
    refine: HashSet<Var>,
    uts: TransysUnroll,
    solver: CaDiCaL,
    kslv: usize,
    opt: HashMap<Var, Var>,
    opt_rev: HashMap<Var, Var>,
    connect: Option<Vec<Vec<LitVec>>>,
    optcst: Option<Vec<Vec<LitVec>>>,
    foundcex: bool,
}

impl LocalAbs {
    pub fn new(ts: Arc<Transys>, abs_cst: bool, abs_trans: bool) -> Self {
        let mut refine = HashSet::default();
        refine.insert(Var::CONST);
        refine.extend(ts.bad.iter().map(|l| l.var()));
        if !abs_cst {
            refine.extend(ts.constraint.iter().map(|l| l.var()))
        }
        if !abs_trans {
            refine.extend(ts.latch().map(|l| ts.var_next_lit(l).var()));
        }
        let mut uts = TransysUnroll::new(Arc::clone(&ts));
        let mut opt = HashMap::default();
        let mut connect: Option<Vec<Vec<LitVec>>> = None;
        if abs_trans {
            for v in uts.ts.latch() {
                let n = uts.ts.var_next_lit(v);
                if let std::collections::hash_map::Entry::Vacant(e) = opt.entry(n.var()) {
                    uts.max_var += 1;
                    e.insert(uts.max_var);
                }
            }
            connect = Some(vec![Vec::new()]);
        }
        let mut optcst: Option<Vec<Vec<LitVec>>> = None;
        if abs_cst {
            let mut rel = Vec::new();
            for c in uts.ts.constraint() {
                let cc = *opt.entry(c.var()).or_insert_with(|| {
                    uts.max_var += 1;
                    uts.max_var
                });
                rel.push(LitVec::from([!cc.lit(), c]));
            }
            optcst = Some(vec![rel]);
        }
        let mut solver = CaDiCaL::new();
        uts.load_trans(&mut solver, 0, !abs_cst);
        if let Some(crel) = connect.as_ref() {
            for cls in crel[0].iter() {
                solver.add_clause(cls);
            }
        }
        if let Some(crel) = optcst.as_ref() {
            for cls in crel[0].iter() {
                solver.add_clause(cls);
            }
        }
        uts.ts.load_init(&mut solver);
        let opt_rev: HashMap<Var, Var> = opt.iter().map(|(k, v)| (*v, *k)).collect();
        for r in refine.iter() {
            if let Some(o) = opt.get(r) {
                solver.add_clause(&[o.lit()]);
            }
        }
        Self {
            refine,
            uts,
            solver,
            kslv: 0,
            opt,
            opt_rev,
            connect,
            optcst,
            foundcex: false,
        }
    }

    pub fn witness(&self) -> Option<BlWitness> {
        if !self.foundcex {
            return None;
        }
        Some(self.uts.witness(&self.solver))
    }

    #[inline]
    pub fn refine_has(&self, x: Var) -> bool {
        self.refine.contains(&x)
    }

    fn unroll_abst(&mut self) {
        self.uts.unroll(self.connect.is_none());
        if let Some(crel) = self.connect.as_mut() {
            let mut cr = Vec::new();
            for l in self.uts.ts.latch() {
                let l = l.lit();
                let n = self.uts.ts.next(l);
                let c = self.opt[&n.var()];
                let n1 = self.uts.next_map[n][self.uts.num_unroll - 1];
                let n2 = self.uts.next_map[l][self.uts.num_unroll];
                cr.push(LitVec::from([!c.lit(), n1, !n2]));
                cr.push(LitVec::from([!c.lit(), !n1, n2]));
            }
            crel.push(cr);
        }
        if let Some(crel) = self.optcst.as_mut() {
            let mut cr = Vec::new();
            for c in self.uts.ts.constraint() {
                let cc = self.opt[&c.var()];
                let cn = self.uts.next_map[c][self.uts.num_unroll];
                cr.push(LitVec::from([!cc.lit(), cn]));
            }
            crel.push(cr);
        }
    }

    fn unroll_to_abst(&mut self, k: usize) {
        while self.uts.num_unroll < k {
            self.unroll_abst();
        }
    }

    fn check(&mut self, mut assumps: LitVec) -> Option<LitVec> {
        let olen = assumps.len();
        assumps.extend(self.uts.lits_next(&self.uts.ts.bad, self.uts.num_unroll));
        if self.solver.solve(&assumps) {
            None
        } else {
            assumps.truncate(olen);
            assumps.retain(|&l| self.solver.unsat_has(l));
            Some(assumps)
        }
    }
}

impl IC3 {
    pub(super) fn check_witness_by_bmc(&mut self, depth: usize) -> bool {
        debug!("localabs: checking witness by bmc with depth {depth}");
        self.localabs.unroll_to_abst(depth);
        for k in self.localabs.kslv + 1..=depth {
            self.localabs
                .uts
                .load_trans(&mut self.localabs.solver, k, !self.abs_cst);
            if let Some(crel) = self.localabs.connect.as_ref() {
                for cls in crel[k].iter() {
                    self.localabs.solver.add_clause(cls);
                }
            }
            if let Some(crel) = self.localabs.optcst.as_ref() {
                for cls in crel[k].iter() {
                    self.localabs.solver.add_clause(cls);
                }
            }
        }
        self.localabs.kslv = depth;
        let mut assump = LitVec::new();
        for (k, v) in self.localabs.opt.iter() {
            if !self.localabs.refine.contains(k) {
                assump.push(v.lit());
            }
        }
        assump.shuffle(&mut self.rng);
        if let Some(assump) = self.localabs.check(assump) {
            for l in assump {
                let ln = self.localabs.opt_rev[&l.var()];
                assert!(!self.localabs.refine.contains(&ln));
                self.localabs.refine.insert(ln);
                self.localabs.solver.add_clause(&[l]);
            }
            info!("localabs: refine size: {}", self.localabs.refine.len());
            false
        } else {
            info!("localabs: witness checking passed");
            self.localabs.foundcex = true;
            true
        }
    }
}
