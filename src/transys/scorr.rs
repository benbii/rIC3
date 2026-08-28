use crate::RseedMap as HashMap;
use crate::{
    config::PreprocConfig,
    gipsat::DagCnfSolver,
    transys::{Transys, certify::Restore},
};
use log::{debug, info};
use logicrs::bitvec::BitVec;
use logicrs::{Lit, LitVec, Var, VarLMap, VarMap};
use std::{sync::Arc, time::Instant};

pub struct Scorr {
    ts: Transys,
    rst: Restore,
    init_slv: DagCnfSolver,
    ind_slv: DagCnfSolver,
    cfg: PreprocConfig,
}

impl Scorr {
    pub fn new(ts: Transys, cfg: &PreprocConfig, rst: Restore) -> Self {
        let mut ind_slv = DagCnfSolver::new(Arc::clone(&ts.rel));
        for c in ts.constraint.iter() {
            ind_slv.add_perma_clause(&[*c]);
        }
        let mut init_slv = DagCnfSolver::new(Arc::clone(&ts.rel));
        for c in ts.constraint.iter() {
            init_slv.add_perma_clause(&[*c]);
        }
        for c in ts.inits() {
            init_slv.add_perma_clause(&c);
        }
        Self {
            ts,
            rst,
            ind_slv,
            init_slv,
            cfg: cfg.clone(),
        }
    }

    fn init_simulation(&self, num_word: usize) -> VarMap<BitVec> {
        let mut slv = DagCnfSolver::new(Arc::clone(&self.ts.rel));
        for cls in self.ts.constraint() {
            slv.add_perma_clause(&[cls]);
        }
        for c in self.ts.inits() {
            slv.add_perma_clause(&c);
        }
        let mut sim: VarMap<BitVec> = VarMap::new_with(self.ts.max_var());
        sim.reserve(self.ts.max_var());
        while sim[Var::CONST].len() < num_word * BitVec::WORD_SIZE {
            if !slv.dcs_solve_nocst(&[]) {
                break;
            }
            let mut block = LitVec::new();
            for &v in self.ts.latch.iter() {
                if let Some(value) = slv.dcs_varsatval(v) {
                    block.push(Lit::new(v, !value));
                    sim[v].push(value);
                } else {
                    sim[v].clear();
                }
            }
            if block.is_empty() {
                break;
            }
            sim[Var::CONST].push(false);
            slv.add_perma_clause(&block);
        }
        sim
    }

    fn rt_simulation(&self, init: &VarMap<BitVec>, num_word: usize) -> VarMap<BitVec> {
        fn assign(sim: &VarMap<BitVec>, idx: usize, vars: &[Var]) -> LitVec {
            vars.iter()
                .map(|&v| v.lit().not_if(!sim[v].get(idx)))
                .collect()
        }

        fn dfs(
            ts: &Transys,
            sim: &mut VarMap<BitVec>,
            slv: &mut DagCnfSolver,
            consider: &[Var],
            domain: &[Var],
            num_word: usize,
            mut assump: LitVec,
        ) {
            loop {
                if sim[Var::CONST].len() >= num_word * BitVec::WORD_SIZE {
                    return;
                }
                if !slv
                    .dcs_solve(&mut assump, &mut [], domain, 5)
                    .is_some_and(|r| r)
                {
                    return;
                }
                sim[Var::CONST].push(false);
                let mut block = LitVec::new();
                for &v in consider {
                    let n = ts.var_next_lit(v);
                    let value = slv.dcs_varsatval(n.var()).unwrap();
                    sim[v].push(value == n.polarity());
                    block.push(Lit::new(n.var(), !value));
                }
                block.sort();
                block.dedup();
                slv.add_perma_clause(&block);
                let assump = assign(sim, sim[Var::CONST].len() - 1, consider);
                dfs(ts, sim, slv, consider, domain, num_word, assump);
            }
        }

        assert!(!init[Var::CONST].is_empty());
        let mut sim: VarMap<BitVec> = VarMap::new_with(self.ts.max_var());
        let consider = self.ts.latch.iter().copied();
        let consider: Vec<Var> = consider.filter(|v| !init[*v].is_empty()).collect();
        sim.reserve(self.ts.max_var());
        let mut slv = DagCnfSolver::new(Arc::clone(&self.ts.rel));
        for cls in self.ts.constraint() {
            slv.add_perma_clause(&[cls]);
        }
        for i in 0..init[Var::CONST].len() {
            let block = !assign(init, i, &consider);
            let mut block = self.ts.lits_next(block.iter());
            block.sort();
            block.dedup();
            slv.add_perma_clause(&block);
        }
        slv.use_phase_saving = false;
        let domain = self.ts.latch.iter().copied();
        let domain: Vec<Var> = domain.map(|l| self.ts.var_next_lit(l).var()).collect();

        for from in 0..init[Var::CONST].len() {
            let assump = assign(init, from, &consider);
            dfs(
                &self.ts, &mut sim, &mut slv, &consider, &domain, num_word, assump,
            );
        }
        sim
    }

    /// `if y.var() > x` later in line 225
    fn check_scorr(&mut self, x: Lit, y: Lit) -> bool {
        let dummy = Lit(0);
        let mut xy = [x, y, dummy];
        let mut nxy = [!x, !y, dummy];
        xy[..2].sort();
        nxy[..2].sort();
        if self
            .init_slv
            .dcs_solve(&mut [dummy], &mut [&mut xy, &mut nxy], &[], 10)
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
        if xn == yn {
            return true;
        }
        let mut xny = [x, !y, dummy];
        let mut nxy = [!x, y, dummy];
        let mut xnyn = [xn, yn, dummy];
        let mut nxnyn = [!xn, !yn, dummy];
        xny[..2].sort();
        nxy[..2].sort();
        xnyn[..2].sort();
        nxnyn[..2].sort();
        let mut cst = [&mut xny[..], &mut nxy, &mut xnyn, &mut nxnyn];
        self.ind_slv
            .dcs_solve(&mut [dummy], &mut cst, &[], 10)
            .is_some_and(|r| !r)
    }

    pub fn scorr(mut self) -> (Transys, Restore) {
        let start = Instant::now();
        let init = self.init_simulation(1);
        if init[Var::CONST].is_empty() {
            return (self.ts, self.rst);
        }
        let mut rt = self.rt_simulation(&init, 10);
        if rt[Var::CONST].is_empty() {
            info!("scorr: empty reachable simulation");
            // Somehow, a simplification here is beneficial lol
            return (self.ts, self.rst);
        }
        debug!(
            "scorr: init simulation size: {}, rt simulation size: {}",
            init[Var::CONST].len(),
            rt[Var::CONST].len()
        );
        let latch = self.ts.latch.iter().copied();
        let mut latch: Vec<_> = latch.filter(|&v| !init[v].is_empty()).collect();
        latch.sort();
        for i in 0..init[Var::CONST].len() {
            rt[Var::CONST].push(false);
            for &l in &latch {
                rt[l].push(init[l].get(i));
            }
        }
        let mut cand: HashMap<BitVec, LitVec> = HashMap::default();
        cand.insert(rt[Var::CONST].clone(), LitVec::from([Lit::constant(false)]));
        for &v in &latch {
            let l = v.lit();
            if let Some(c) = cand.get_mut(&rt[v]) {
                c.push(l);
            } else if let Some(c) = cand.get_mut(&!&rt[v]) {
                c.push(!l);
            } else {
                cand.insert(rt[v].clone(), LitVec::from([l]));
            }
        }
        let mut scorr = VarLMap::new();
        'm: for &x in &latch {
            if let Some(n) = self.ts.init(x)
                && !n.var().is_constant()
            {
                continue;
            }
            let (eqc, xl) = if let Some(eqc) = cand.get_mut(&rt[x]) {
                (eqc, x.lit())
            } else if let Some(eqc) = cand.get_mut(&!&rt[x]) {
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
        let Scorr {
            mut ts,
            mut rst,
            init_slv,
            ind_slv,
            cfg: _,
        } = self;
        drop((init_slv, ind_slv));
        ts.replace(&scorr, &mut rst);
        ts.simplify(&mut rst);
        info!("scorr: simplified ts: {}", ts.statistic());
        (ts, rst)
    }
}
