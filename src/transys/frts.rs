use crate::{
    config::PreprocessConfig,
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf, certify::Restore},
};
use giputils::hash::GHashMap;
use log::{debug, info, trace};
use logicrs::{LitVec, Var, VarLMap, simplify::DagCnfSimplify};
use std::time::Instant;

pub struct FrTs {
    cfg: PreprocessConfig,
    ts: Transys,
    map: VarLMap,
    solver: DagCnfSolver,
    rst: Restore,
}

impl FrTs {
    pub fn new(mut ts: Transys, cfg: &PreprocessConfig, mut rst: Restore) -> Self {
        ts.topsort(&mut rst);
        let sim = ts.rel.simulation(1000);
        let solver = DagCnfSolver::new(&ts.rel);
        let mut map = VarLMap::new();
        let mut simval: GHashMap<_, Vec<_>> = GHashMap::new();
        for v in ts.rel.var_iter() {
            let lv = v.lit();
            let slv = sim.val(lv);
            let snlv = sim.val(!lv);
            if let Some(e) = simval.get_mut(&slv) {
                e.push(lv);
                map.insert_lit(lv, e[0]);
            } else if let Some(e) = simval.get_mut(&snlv) {
                e.push(!lv);
                map.insert_lit(!lv, e[0]);
            } else {
                simval.insert(slv, vec![lv]);
            }
        }
        Self {
            ts,
            cfg: cfg.clone(),
            map,
            solver,
            rst,
        }
    }

    pub fn fr(mut self) -> (Transys, Restore) {
        let start = Instant::now();
        let before = self.ts.max_var();
        let mut replace = VarLMap::new();
        let mut v = Var(1);
        while v <= self.ts.max_var() {
            if start.elapsed().as_secs() > self.cfg.frts_tl {
                info!("frts: timeout");
                break;
            }
            if self.ts.rel.is_leaf(v) {
                v += 1;
                continue;
            }
            let Some(m) = self.map.map(v) else {
                v += 1;
                continue;
            };
            let lv = v.lit();
            trace!("frts: checking var {m} with lit {v}");
            match self.solver.solve_with_restart_limit(
                &[],
                vec![LitVec::from([m, lv]), LitVec::from([!m, !lv])],
                9,
            ) {
                Some(true) => {}
                Some(false) => {
                    debug!("frts: {v} -> {m}");
                    replace.insert_lit(lv, m);
                    self.solver.add_eq(lv, m);
                    if replace.len().is_multiple_of(5000) {
                        self.ts.replace(&replace, &mut self.rst);
                        self.ts.coi_refine(&mut self.rst);
                        let mut simp = DagCnfSimplify::new(&self.ts.rel);
                        for &v in self.ts.frozens().iter() {
                            simp.froze(v);
                        }
                        simp.const_simplify();
                        simp.bve_simplify();
                        self.ts.rel = simp.finalize();
                        self.solver = DagCnfSolver::new(&self.ts.rel);
                        info!("frts ts simplified to: {}", self.ts.statistic());
                    }
                }
                None => {
                    debug!("frts: checking {v} with {m} timeout");
                }
            }
            v += 1;
        }

        self.ts.replace(&replace, &mut self.rst);
        self.ts.coi_refine(&mut self.rst);
        self.ts.rearrange(&mut self.rst);
        info!(
            "frts: eliminates {} out of {} vars in {:.2}s",
            *before - *self.ts.max_var(),
            *before,
            start.elapsed().as_secs_f32()
        );
        self.ts.simplify(&mut self.rst);
        info!("frts: simplified ts: {}", self.ts.statistic());
        (self.ts, self.rst)
    }
}
