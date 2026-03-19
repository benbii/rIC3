use crate::{
    config::PreprocConfig,
    gipsat::DagCnfSolver,
    transys::{Transys, certify::Restore},
};
use ahash::HashMap;
use logicrs::bitvec::BitVec;
use log::{debug, info};
use logicrs::{Lit, LitVec, Var, VarBitVec, VarLMap, satif::Satif};
use std::time::Instant;

pub struct Scorr {
    ts: Transys,
    rst: Restore,
    init_slv: DagCnfSolver,
    ind_slv: DagCnfSolver,
    cfg: PreprocConfig,
}

impl Scorr {
    pub fn new(ts: Transys, cfg: &PreprocConfig, rst: Restore) -> Self {
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
        }
    }

    fn init_simulation(&self, num_word: usize) -> VarBitVec {
        let mut slv = DagCnfSolver::new(&self.ts.rel);
        for cls in self.ts.constraint() {
            slv.add_clause(&cls.cube());
        }
        self.ts.load_init(&mut slv);
        let mut sim = VarBitVec::new();
        sim.reserve(self.ts.max_var());
        while sim.bv_len() < num_word * BitVec::WORD_SIZE {
            if !slv.solve(&[]) {
                break;
            }
            let mut block = LitVec::new();
            for &v in self.ts.latch.iter() {
                if let Some(a) = slv.sat_value(v.lit()) {
                    block.push(!slv.sat_value_lit(v).unwrap());
                    sim[v].push(a);
                } else {
                    sim[v].clear();
                }
            }
            if block.is_empty() {
                break;
            }
            sim[Var::CONST].push(false);
            slv.add_clause(&block);
        }
        sim
    }

    fn rt_simulation(&self, init: &VarBitVec, num_word: usize) -> VarBitVec {
        fn dfs(
            ts: &Transys,
            sim: &mut VarBitVec,
            slv: &mut DagCnfSolver,
            consider: &[Var],
            domain: &[Var],
            num_word: usize,
            from: usize,
        ) {
            let assump = sim.assign(from, Some(consider.iter().copied()));
            loop {
                if sim.bv_len() >= num_word * BitVec::WORD_SIZE {
                    return;
                }
                if !slv
                    .solve_with_param(&assump, vec![], domain.iter().copied(), Some(5))
                    .is_some_and(|r| r)
                {
                    return;
                }
                sim[Var::CONST].push(false);
                let mut block = LitVec::new();
                for &v in consider {
                    let n = ts.next(v.lit());
                    let va = slv.sat_value(n).unwrap();
                    let na = slv.sat_value_lit(n.var()).unwrap();
                    sim[v].push(va);
                    block.push(!na);
                }
                slv.add_clause(&block);
                dfs(ts, sim, slv, consider, domain, num_word, sim.bv_len() - 1);
            }
        }

        assert!(init.bv_len() > 0);
        let mut sim = VarBitVec::new();
        let consider: Vec<_> = self.ts.latch().filter(|v| !init[*v].is_empty()).collect();
        sim.reserve(self.ts.max_var());
        let mut slv = DagCnfSolver::new(&self.ts.rel);
        for cls in self.ts.constraint() {
            slv.add_clause(&cls.cube());
        }
        for i in 0..init.bv_len() {
            let block = !init.assign(i, Some(consider.iter().copied()));
            let block = self.ts.lits_next(block.iter());
            slv.add_clause(&block);
        }
        slv.cfg.phase_saving = false;
        let domain: Vec<_> = self.ts.next.values().map(|l| l.var()).collect();
        for from in 0..init.bv_len() {
            let assump = init.assign(from, Some(consider.iter().copied()));
            loop {
                if sim.bv_len() >= num_word * BitVec::WORD_SIZE {
                    return sim;
                }
                if !slv.solve_with_domain(&assump, domain.iter().copied()) {
                    break;
                }
                sim[Var::CONST].push(false);
                let mut block = LitVec::new();
                for &v in &consider {
                    let n = self.ts.next(v.lit());
                    let va = slv.sat_value(n).unwrap();
                    let na = slv.sat_value_lit(n.var()).unwrap();
                    sim[v].push(va);
                    block.push(!na);
                }
                slv.add_clause(&block);
                let from = sim.bv_len() - 1;
                dfs(&self.ts, &mut sim, &mut slv, &consider, &domain, num_word, from);
            }
        }
        sim
    }

    fn check_scorr(&mut self, x: Lit, y: Lit) -> bool {
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
                10,
            )
            .is_some_and(|r| !r)
    }

    pub fn scorr(mut self) -> (Transys, Restore) {
        let start = Instant::now();
        let init = self.init_simulation(1);
        if init.bv_len() == 0 {
            return (self.ts, self.rst);
        }
        let mut rt = self.rt_simulation(&init, 10);
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
        let mut cand: HashMap<BitVec, LitVec> = HashMap::default();
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
        'm: for x in latch {
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
                if start.elapsed().as_secs() > self.cfg.scorr_tl {
                    info!("scorr: timeout");
                    break 'm;
                }
                let y = eqc[i];
                if y.var() >= x {
                    break;
                }
                if self.check_scorr(xl, y) {
                    debug!("scorr: {xl} -> {y}");
                    scorr.insert_lit(xl, y);
                    eqc.retain(|l| l.var() != x);
                    break;
                }
            }
        }
        info!(
            "scorr: eliminates {} latchs out of {} in {:.2}s",
            scorr.len(),
            self.ts.latch.len(),
            start.elapsed().as_secs_f32()
        );
        self.ts.replace(&scorr, &mut self.rst);
        self.ts.simplify(&mut self.rst);
        info!("scorr: simplified ts: {}", self.ts.statistic());
        (self.ts, self.rst)
    }
}
