use crate::{
    Engine, McResult, McWitness,
    bitwuzla::Bitwuzla,
    config::EngineConfigBase,
    impl_config_deref,
    wltransys::{WlTransys, unroll::WlTransysUnroll},
};
use clap::Args;
use ahash::HashMap;
use log::info;
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct WlBMCConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,
}

impl_config_deref!(WlBMCConfig);

pub struct WlBMC {
    cfg: WlBMCConfig,
    #[allow(unused)]
    owts: WlTransys,
    uts: WlTransysUnroll,
    solver: Bitwuzla,
    solver_k: usize,
}

impl WlBMC {
    pub fn new(cfg: WlBMCConfig, mut wts: WlTransys) -> Self {
        let owts = wts.clone();
        wts.compress_bads();
        let uts = WlTransysUnroll::new(wts);
        let mut solver = Bitwuzla::new();
        for (l, i) in uts.ts.init.iter() {
            solver.assert(&l.teq(i));
        }
        Self {
            cfg,
            owts,
            uts,
            solver,
            solver_k: 0,
        }
    }

    pub fn load_trans_to(&mut self, k: usize) {
        while self.solver_k < k + 1 {
            for c in self.uts.ts.constraint.iter() {
                self.solver.assert(&self.uts.next(c, self.solver_k));
            }
            self.solver_k += 1;
        }
    }
}

impl Engine for WlBMC {
    fn check(&mut self) -> McResult {
        for k in (self.cfg.start..=self.cfg.end).step_by(self.cfg.step as usize) {
            self.uts.unroll_to(k);
            self.load_trans_to(k);
            let assump = self.uts.next(&self.uts.ts.bad[0], k);
            if self.solver.solve(&[assump]) {
                info!("wl-bmc found a counterexample at depth {k}");
                return McResult::Unsafe(k);
            }
            info!("wl-bmc found no counterexample at exact depth {k}");
        }
        info!("bmc reached bound {}, stopping search", self.cfg.end);
        McResult::Unknown(Some(self.cfg.end))
    }

    fn witness(&mut self) -> McWitness {
        let mut witness = self.uts.witness(&mut self.solver);
        let mut cache = HashMap::default();
        let mut ilmap = HashMap::default();
        for i in self.owts.input.iter().chain(self.owts.latch.iter()) {
            ilmap.insert(i, self.uts.next(i, self.uts.num_unroll));
        }
        let bads: Vec<_> = self
            .owts
            .bad
            .iter()
            .map(|b| b.cached_apply(&|t| ilmap.get(t).cloned(), &mut cache))
            .collect();
        witness.bad_id = bads
            .into_iter()
            .position(|b| self.solver.sat_value(&b).is_some_and(|v| v.bool()))
            .unwrap();
        McWitness::Wl(witness)
    }
}
