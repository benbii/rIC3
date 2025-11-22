use super::IC3;
use crate::{
    Witness,
    config::Config,
    transys::{Transys, TransysIf, certify::Restore, unroll::TransysUnroll},
};
use giputils::hash::{GHashMap, GHashSet};
use log::{debug, info};
use logicrs::{LitVec, LitVvec, Var, satif::Satif};
use rand::seq::SliceRandom;

pub struct LocalAbs {
    refine: GHashSet<Var>,
    uts: TransysUnroll<Transys>,
    solver: cadical::Solver,
    kslv: usize,
    opt: GHashMap<Var, Var>,
    opt_rev: GHashMap<Var, Var>,
    connect: Option<Vec<LitVvec>>,
    optcst: Option<Vec<LitVvec>>,
    foundcex: bool,
}

impl LocalAbs {
    pub fn new(ts: &Transys, cfg: &Config) -> Self {
        let mut refine = GHashSet::new();
        refine.insert(Var::CONST);
        refine.extend(ts.bad.iter().map(|l| l.var()));
        if !cfg.ic3.abs_cst {
            refine.extend(ts.constraint.iter().map(|l| l.var()))
        }
        if !cfg.ic3.abs_trans {
            refine.extend(ts.next.values().map(|l| l.var()));
        }
        let mut uts = TransysUnroll::new(ts);

        let mut opt = GHashMap::new();
        let mut connect = None;
        let mut optcst = None;
        // Setup optional connection
        if cfg.ic3.abs_trans {
            for v in uts.ts.latch() {
                let n = uts.ts.next(v.lit());
                if !opt.contains_key(&n.var()) {
                    uts.max_var += 1;
                    let c = uts.max_var;
                    opt.insert(n.var(), c);
                }
            }
            connect = Some(vec![LitVvec::new()]);
        }
        // Setup optional constraint
        if cfg.ic3.abs_cst {
            let mut rel = LitVvec::new();
            for c in uts.ts.constraint() {
                let cc = opt.get(&c.var()).copied().unwrap_or({
                    uts.max_var += 1;
                    opt.insert(c.var(), uts.max_var);
                    uts.max_var
                });
                rel.push(LitVec::from([!cc.lit(), c]));
            }
            optcst = Some(vec![rel]);
        }

        let mut solver = cadical::Solver::new();
        uts.load_trans(&mut solver, 0, !cfg.ic3.abs_cst);
        // Add abstraction clauses for timestep 0
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
        let opt_rev: GHashMap<Var, Var> = opt.iter().map(|(k, v)| (*v, *k)).collect();
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

    pub fn witness(&self, rst: &Restore) -> Option<Witness> {
        if !self.foundcex {
            return None;
        }
        let mut res = Witness::default();
        for k in 0..=self.uts.num_unroll {
            let mut w = LitVec::new();
            for l in self.uts.ts.input() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl) {
                    w.push(rst.restore(l.not_if(!v)));
                }
            }
            res.input.push(w);
            let mut w = LitVec::new();
            for l in self.uts.ts.latch() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl) {
                    w.push(rst.restore(l.not_if(!v)));
                }
            }
            res.state.push(w);
        }
        Some(res)
    }

    #[inline]
    pub fn refine_has(&self, x: Var) -> bool {
        self.refine.contains(&x)
    }

    fn unroll_abst(&mut self) {
        // Common unroll logic
        self.uts.unroll(self.connect.is_none());
        // NOTE: uts.unroll adds num_unroll by 1.
        // Add abstraction-specific connection clauses
        if let Some(crel) = self.connect.as_mut() {
            let mut cr = LitVvec::new();
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
        // Add abstraction-specific constraint clauses
        if let Some(crel) = self.optcst.as_mut() {
            let mut cr = LitVvec::new();
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
            // Load base transition relation
            self.localabs
                .uts
                .load_trans(&mut self.localabs.solver, k, !self.cfg.ic3.abs_cst);
            // Add abstraction-specific clauses
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
            // debug!("checking witness with {} refines", assump.len());
            // let mut i = 0;
            // while i < assump.len() {
            //     let ln = self.localabs.opt_rev[&assump[i].var()];
            //     if self.localabs.refine.contains(&ln) {
            //         i += 1;
            //         continue;
            //     }
            //     let mut drop = assump.clone();
            //     drop.remove(i);
            //     if let Some(drop) = self.localabs.check(drop) {
            //         assump = drop;
            //     } else {
            //         i += 1;
            //     }
            // }
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
