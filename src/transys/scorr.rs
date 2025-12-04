use crate::{
    Engine,
    config::{Config, PreprocessConfig},
    gipsat::DagCnfSolver,
    ic3::IC3,
    transys::{Transys, TransysIf, certify::Restore},
};
use giputils::{bitvec::BitVec, hash::GHashMap};
use log::{debug, info, trace};
use logicrs::{Lit, LitVec, Var, VarLMap, VarSymbols, satif::Satif};
use std::sync::RwLock;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::SystemTime;
fn s() -> u64 {
    SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

pub struct Scorr {
    ts: Transys,
    rst: Restore,
    init_slv: DagCnfSolver,
    ind_slv: DagCnfSolver,
    cfg: PreprocessConfig,
    tcfg: Config,
}

impl Scorr {
    pub fn new(ts: Transys, cfg: &PreprocessConfig, tcfg: &Config, rst: Restore) -> Self {
        let mut ind_slv = DagCnfSolver::new(&ts.rel);
        for c in ts.constraint.iter() {
            ind_slv.add_clause(&[*c]);
        }
        let mut init_slv = DagCnfSolver::new(&ts.rel);
        for c in ts.constraint.iter() {
            init_slv.add_clause(&[*c]);
        }
        ts.load_init(&mut init_slv);
        Self {
            ts,
            rst,
            ind_slv,
            init_slv,
            cfg: cfg.clone(),
            tcfg: tcfg.clone(),
        }
    }

    /// SAT-based equivalence check. Returns true only if equivalence is proven (UNSAT).
    /// Returns false if inconclusive (needs IC3 verification).
    fn do_sat_chk(&mut self, x: Lit, y: Lit) -> bool {
        if self
            .init_slv
            .solve_with_restart_limit(&[], vec![LitVec::from([x, y]), LitVec::from([!x, !y])], 10)
            .is_none_or(|r| r)
        {
            return false;
        }
        let xn = self.ts.next(x);
        let yn = if y.var().is_constant() {
            y
        } else {
            self.ts.next(y)
        };
        self.ind_slv
            .solve_with_restart_limit(
                &[],
                vec![
                    LitVec::from([x, !y]),
                    LitVec::from([!x, y]),
                    LitVec::from([xn, yn]),
                    LitVec::from([!xn, !yn]),
                ],
                100,
            )
            .is_some_and(|r| !r)
    }

    // Phase 2: IC3 checks for inconclusive pairs (parallel)
    fn ic3_worker(
        &self,
        scorr: &RwLock<VarLMap>,
        work_idx: &AtomicUsize,
        deferred: &Vec<(Lit, Lit)>,
        last_sol: &AtomicU64,
    ) {
        let mut tle = self.cfg.scorr_effort * 2;
        loop {
            let idx = work_idx.fetch_add(1, Ordering::Relaxed);
            if idx >= deferred.len() {
                return;
            }
            let elapsed = s() - last_sol.load(Ordering::Relaxed);
            if elapsed >= self.cfg.scorr_tl {
                return;
            }
            let (xl, y) = deferred[idx];
            {
                let scorr_read = scorr.read().unwrap();
                if scorr_read.get(&xl.var()).is_some() {
                    continue;
                }
                if scorr_read.get(&y.var()).is_some() {
                    continue;
                }
            }
            let mut ts_clone = self.ts.clone();
            ts_clone.bad = LitVec::from(ts_clone.rel.new_xor(xl, y));
            let mut cfg = self.tcfg.clone();
            cfg.preproc.preproc = false;
            cfg.time_limit = Some(tle);
            // first few are likely to yield equiv
            tle = (tle - 200).max(self.cfg.scorr_effort);
            let mut ic3 = IC3::new(cfg, ts_clone, VarSymbols::new());
            let result = ic3.check();
            match result {
                None => {
                    debug!("scorr: {} IC3?= {} ({}s)", xl, y, elapsed);
                }
                Some(false) => {
                    debug!("scorr: {} IC3!= {} ({}s)", xl, y, elapsed);
                }
                Some(true) => {
                    info!("scorr: {} IC3== {} ({}s)", xl, y, elapsed);
                    scorr.write().unwrap().insert_lit(xl, y);
                    last_sol.store(s(), Ordering::Relaxed);
                }
            }
        }
    }

    pub fn scorr(mut self) -> (Transys, Restore) {
        let init = self.ts.init_simulation(1);
        if init.bv_len() == 0 {
            return (self.ts, self.rst);
        }
        let mut rt = self.ts.rt_simulation(&init, 10);
        debug!(
            "scorr: init simulation size: {}, rt simulation size: {}",
            init.bv_len(),
            rt.bv_len()
        );
        let mut latch: Vec<_> = self.ts.latch().filter(|v| !init[*v].is_empty()).collect();
        latch.sort();
        for i in 0..init.bv_len() {
            rt[Var::CONST].push(false);
            for &l in latch.iter() {
                rt[l].push(init[l].get(i));
            }
        }
        let mut cand: GHashMap<BitVec, LitVec> = GHashMap::new();
        cand.insert(rt[Var::CONST].clone(), LitVec::from([Lit::constant(false)]));
        for &v in latch.iter() {
            let l = v.lit();
            if let Some(c) = cand.get_mut(&rt[v]) {
                c.push(l);
            } else if let Some(c) = cand.get_mut(&rt.val(!l)) {
                c.push(!l);
            } else {
                cand.insert(rt[v].clone(), LitVec::from([l]));
            }
        }
        let mut scorr = VarLMap::new();
        let mut deferred: Vec<(Lit, Lit)> = Vec::new(); // (xl, y) pairs needing IC3

        // Phase 1: SAT checks
        for x in latch {
            if let Some(n) = self.ts.init.get(&x)
                && !n.var().is_constant()
            {
                continue;
            }
            let (eqc, xl) = if let Some(eqc) = cand.get_mut(&rt[x]) {
                (eqc, x.lit())
            } else if let Some(eqc) = cand.get_mut(&rt.val(!x.lit())) {
                (eqc, !x.lit())
            } else {
                panic!();
            };
            for i in 0..eqc.len() {
                if i > (10000 / eqc.len()).max(1) {
                    break;
                }
                let y = eqc[i];
                if y.var() >= x {
                    break;
                }
                if self.do_sat_chk(xl, y) {
                    trace!("scorr: {xl} SAT== {y}");
                    scorr.insert_lit(xl, y);
                    eqc.retain(|l| l.var() != x);
                    break;
                } else {
                    deferred.push((xl, y));
                }
            }
        }

        // Phase 2: IC3 checks for inconclusive pairs (parallel)
        info!("scorr: {} pairs deferred for IC3", deferred.len());
        let scorr = RwLock::new(scorr);
        let work_idx = AtomicUsize::new(0);
        let last_sol = AtomicU64::new(s());
        std::thread::scope(|s| {
            for _ in 0..16 {
                if work_idx.load(Ordering::Relaxed) >= deferred.len() {
                    break;
                }
                s.spawn(|| self.ic3_worker(&scorr, &work_idx, &deferred, &last_sol));
                std::thread::sleep(std::time::Duration::from_millis(400));
            }
        });

        let mut scorr = scorr.into_inner().unwrap();
        info!(
            "scorr: eliminates {} latchs out of {}",
            scorr.len(),
            self.ts.latch.len(),
        );
        // Resolve transitive chains: if x→y and y→z, update x→z
        let mut vars: Vec<Var> = scorr.keys().copied().collect();
        vars.sort();
        for v in vars {
            let r = scorr[&v];
            if let Some(rr) = scorr.map_lit(r) {
                if rr.var() != r.var() {
                    scorr.insert_lit(v.lit(), rr);
                }
            }
        }
        self.ts.replace(&scorr, &mut self.rst);
        self.ts.simplify(&mut self.rst);
        info!("scorr: simplified ts: {}", self.ts.statistic());
        (self.ts, self.rst)
    }
}
