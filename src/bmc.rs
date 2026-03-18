use crate::{
    Engine, McResult, McWitness,
    config::{EngineConfig, EngineConfigBase, PreprocConfig},
    impl_config_deref,
    transys::{
        Transys, certify::Restore,
        nodep::NoDepTransysUnroll,
        preproc_serde::PreprocModel,
    },
};
use crate::cadical::CaDiCaL;
use clap::{Args, Parser};
use crate::kissat::Kissat;
use log::info;
use logicrs::{LitVec, satif::Satif};
use rand::{Rng, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct BMCConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,
    #[command(flatten)]
    pub preproc: PreprocConfig,
    /// per-step time limit (applies to each BMC step, not the overall solver run).
    /// The overall `time_limit` option sets the total time limit for the entire solver run.
    #[arg(long = "step-time-limit")]
    pub step_time_limit: Option<u64>,
    /// use kissat solver in bmc, otherwise cadical
    #[arg(long = "kissat", default_value_t = false)]
    pub kissat: bool,
    /// dynamic step
    #[arg(long = "dyn-step", default_value_t = false)]
    pub dyn_step: bool,
}
impl_config_deref!(BMCConfig);
impl Default for BMCConfig {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "bmc"]);
        cfg.into_bmc().unwrap()
    }
}

enum S {
    C(CaDiCaL),
    K(Kissat, StdRng),
}
pub struct BMC {
    ots: Transys,
    uts: NoDepTransysUnroll,
    cfg: BMCConfig,
    solver_k: usize,
    rst: Restore,
    step: usize,
    solver: S,
}

impl BMC {
    pub fn new(cfg: BMCConfig, ts: Transys) -> Self {
        let ots = ts.clone();
        let mut rng = StdRng::seed_from_u64(cfg.rseed);
        let (model, _loaded) = PreprocModel::load_or_preproc(ts, &cfg.preproc);
        let (mut ts, mut rst) = (model.ts, model.rst);
        if ts.bad.len() > 1 {
            let bad = std::mem::take(&mut ts.bad);
            ts.bad = LitVec::from(ts.rel.new_or(bad));
        }
        let mut ts = ts.remove_dep();
        for c in std::mem::take(&mut ts.constraint) {
            ts.rel.add_clause(&[c]);
        }
        if cfg.preproc.preproc {
            ts.simplify(&mut rst);
        }
        let uts = NoDepTransysUnroll::new(&ts);
        let solver = if cfg.kissat {
            let mut s = Kissat::new();
            s.set_seed(rng.random());
            ts.load_init(&mut s);
            S::K(s, rng)
        } else {
            let mut c = CaDiCaL::new();
            c.set_seed(rng.random());
            ts.load_init(&mut c);
            S::C(c)
        };
        let step = if cfg.dyn_step {
            (10_000_000 / (*ts.max_var() as usize + ts.rel.clauses().len())).max(1)
        } else {
            cfg.step as usize
        };
        Self {
            ots,
            uts,
            cfg,
            solver_k: 0,
            rst,
            step,
            solver,
        }
    }
}

impl Engine for BMC {
    fn check(&mut self) -> McResult {
        if let S::C(c) = &mut self.solver {
            for d in (self.cfg.start..=self.cfg.end).step_by(self.step) {
                self.uts.unroll_to(d);
                while self.solver_k < d + 1 {
                    self.uts.load_trans(c, self.solver_k, true);
                    self.solver_k += 1;
                }
                let assump: LitVec = self.uts.lits_next(&self.uts.ts.bad, d).collect();
                if c.solve(&assump) {
                    info!("bmc found a counterexample at depth {d}");
                    return McResult::Unsafe(d);
                }
                info!("bmc found no counterexample at exact depth {d}");
            }
        } else if let S::K(k, rng) = &mut self.solver {
            for d in (self.cfg.start..=self.cfg.end).step_by(self.step) {
                self.uts.unroll_to(d);
                while self.solver_k < d + 1 {
                    self.uts.load_trans(k, self.solver_k, true);
                    self.solver_k += 1;
                }
                for b in self.uts.lits_next(&self.uts.ts.bad, d) {
                    k.add_clause(&[b]);
                }
                if k.solve(&[]) {
                    info!("bmc found a counterexample at depth {d}");
                    return McResult::Unsafe(d);
                }
                info!("bmc found no counterexample at exact depth {d}");
                *k = Kissat::new();
                k.set_seed(rng.random());
                self.uts.ts.load_init(k);
                for i in 0..self.solver_k {
                    self.uts.load_trans(k, i, true);
                }
            }
        }
        info!("bmc reached bound {}, stopping search", self.cfg.end);
        McResult::Unknown(Some(self.cfg.end))
    }

    fn witness(&mut self) -> McWitness {
        let mut wit = match &self.solver {
            S::C(c) => self.uts.witness(c),
            S::K(k, _) => self.uts.witness(k),
        };
        wit = wit.map(|l| self.rst.restore(l));
        for s in wit.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        wit.exact_state(&self.ots, true);
        McWitness::Bl(wit)
    }
}
