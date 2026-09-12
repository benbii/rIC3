use crate::cadical::CaDiCaL;
use crate::kissat::Kissat;
use crate::{
    Engine, McResult, McWitness,
    config::EngineConfig,
    transys::{Transys, certify::Restore, nodep::NoDepTransysUnroll},
};
use clap::{Args, Parser};
use log::info;
use rand::{RngExt, SeedableRng, rngs::SmallRng};
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct BMCConfig {
    /// Start bound
    #[arg(long = "start", default_value_t = 0)]
    pub start: usize,
    /// Max bound to check
    #[arg(long = "end", default_value_t = usize::MAX)]
    pub end: usize,
    /// Step length
    #[arg(long, default_value_t = 1, value_parser = clap::value_parser!(u32).range(1..))]
    pub step: u32,
    /// Random seed
    #[arg(long, default_value_t = 0)]
    pub rseed: u64,
    /// use kissat solver in bmc, otherwise cadical
    #[arg(long = "kissat", default_value_t = false)]
    pub kissat: bool,
    /// dynamic step
    #[arg(long = "dyn-step", default_value_t = false)]
    pub dyn_step: bool,
}
impl Default for BMCConfig {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "bmc"]);
        cfg.into_bmc().unwrap()
    }
}

enum S {
    C(CaDiCaL),
    K(Kissat, SmallRng),
}
pub struct BMC {
    ots: Transys,
    uts: NoDepTransysUnroll,
    start: usize,
    end: usize,
    solver_k: usize,
    rst: Restore,
    step: usize,
    solver: S,
}

impl BMC {
    pub fn new(cfg: BMCConfig, ts: Transys, ots: Transys, mut rst: Restore) -> Self {
        let mut rng = SmallRng::seed_from_u64(cfg.rseed);
        assert!(!ts.bad.is_empty(), "BMC requires a target property");
        let mut ts = ts.remove_dep();
        for c in std::mem::take(&mut ts.constraint) {
            ts.rel.add_clause(&[c]);
        }
        ts.simplify(&mut rst);
        let solver = if cfg.kissat {
            let mut k = Kissat::new();
            k.set_seed(rng.random());
            k.new_var_to(ts.max_var());
            for cls in ts.inits() {
                k.add_clause(&cls);
            }
            S::K(k, rng)
        } else {
            let mut c = CaDiCaL::new();
            c.set_seed(rng.random());
            c.new_var_to(ts.max_var());
            for cls in ts.inits() {
                c.add_clause(&cls);
            }
            S::C(c)
        };
        let step = if cfg.dyn_step {
            (10_000_000 / (ts.max_var().0 as usize + ts.rel.clauses().len())).max(1)
        } else {
            cfg.step as usize
        };
        let uts = NoDepTransysUnroll::new(ts);
        Self {
            ots,
            uts,
            start: cfg.start,
            end: cfg.end,
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
            for d in (self.start..=self.end).step_by(self.step) {
                self.uts.unroll_to(d);
                while self.solver_k < d + 1 {
                    self.uts.load_trans(c, self.solver_k, true);
                    // The previous frame is now part of the prefix, even when
                    // --start/--step skipped checking a bad at that frame.
                    if self.solver_k > 0 {
                        for h in self.uts.lits_next(&self.uts.ts.bad[1..], self.solver_k - 1) {
                            c.add_clause(&[!h]);
                        }
                    }
                    self.solver_k += 1;
                }
                let bad = self.uts.lit_next(self.uts.ts.bad[0], d);
                if c.cad_solve(&[bad]) {
                    info!("bmc-cadical found a counterexample at depth {d}");
                    return McResult::Unsafe(d);
                }
                // 0, 1, 2, 3, 5, 7, 9, 11, 15, 19, 23, 27, 31, 39, 47, 55, 63, 79, 95...
                if d ^ (d + 1) > d >> 2 {
                    info!("cadical no cex at depth {d}");
                }
            }
        } else if let S::K(k, rng) = &mut self.solver {
            for d in (self.start..=self.end).step_by(self.step) {
                self.uts.unroll_to(d);
                while self.solver_k < d + 1 {
                    self.uts.load_trans_k(k, self.solver_k, true);
                    if self.solver_k > 0 {
                        for h in self.uts.lits_next(&self.uts.ts.bad[1..], self.solver_k - 1) {
                            k.add_clause(&[!h]);
                        }
                    }
                    self.solver_k += 1;
                }
                let bad = self.uts.lit_next(self.uts.ts.bad[0], d);
                k.add_clause(&[bad]);
                if k.ksat_solve(&[]) {
                    info!("bmc-kissat found a counterexample at depth {d}");
                    return McResult::Unsafe(d);
                }
                if d ^ (d + 1) > d >> 2 {
                    info!("kissat no cex at depth {d}");
                }

                // Kissat does not support incremental solving
                *k = Kissat::new();
                k.set_seed(rng.random());
                k.new_var_to(self.uts.ts.max_var());
                for cls in self.uts.ts.inits() {
                    k.add_clause(&cls);
                }
                for i in 0..self.solver_k {
                    self.uts.load_trans_k(k, i, true);
                    if i > 0 {
                        for h in self.uts.lits_next(&self.uts.ts.bad[1..], i - 1) {
                            k.add_clause(&[!h]);
                        }
                    }
                }
            }
        }

        info!("bmc reached bound {}, stopping search", self.end);
        McResult::Unknown(self.end)
    }

    fn witness(&mut self) -> McWitness {
        let mut wit = match &self.solver {
            S::C(c) => self.uts.witness(c),
            S::K(k, _) => self.uts.witness_k(k),
        };
        wit = wit.map(|l| self.rst.restore(l));
        for s in wit.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        wit.exact_state(&self.ots, true, self.rst.prop);
        McWitness::Bl(wit)
    }
}
