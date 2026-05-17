use crate::{RseedMap as HashMap, RseedSet as HashSet};
use crate::{
    config::PreprocConfig,
    gipsat::DagCnfSolver,
    transys::{Transys, certify::Restore},
};
use log::{debug, info, trace};
use logicrs::{
    Lit, LitVec, Var, VarLMap, VarMap, VarRange, bitvec::BitVec, simplify::DagCnfSimplify,
};
use rand::{SeedableRng, rngs::StdRng};
use std::time::Instant;

pub struct FrTs {
    cfg: PreprocConfig,
    ts: Transys,
    map: VarLMap,
    solver: DagCnfSolver,
    rst: Restore,
}

impl FrTs {
    pub fn new(mut ts: Transys, cfg: &PreprocConfig, mut rst: Restore) -> Self {
        const NUM_WORD: usize = 1000;
        ts.topsort(&mut rst);
        let solver = DagCnfSolver::new(&ts.rel);
        let mut rng = StdRng::seed_from_u64(0);
        let mut sim = VarMap::new_with(ts.max_var());
        sim[Var::CONST] = BitVec::from_elem(NUM_WORD * BitVec::WORD_SIZE, false);
        let mut leafs = HashSet::default();
        for v in VarRange::new_inclusive(Var(1), ts.max_var()) {
            if ts.rel.is_leaf(v) {
                loop {
                    let x = BitVec::new_rand(NUM_WORD, &mut rng);
                    if !leafs.contains(&x) {
                        leafs.insert(x.clone());
                        sim[v] = x;
                        break;
                    }
                }
                continue;
            }
            sim[v] = BitVec::from_elem(NUM_WORD * BitVec::WORD_SIZE, false);
        }
        for v in VarRange::new_inclusive(Var(1), ts.max_var()) {
            if ts.rel.is_leaf(v) {
                continue;
            }
            for rel in &ts.rel[v] {
                let mut r = if rel[0].polarity() {
                    sim[rel[0].var()].clone()
                } else {
                    !&sim[rel[0].var()]
                };
                let mut vl = rel[0];
                for &l in &rel[1..] {
                    if l.var() == v {
                        vl = l;
                    }
                    if l.polarity() {
                        r |= &sim[l.var()];
                    } else {
                        r |= &!&sim[l.var()];
                    }
                }
                if vl.polarity() {
                    sim[v] |= &!&r;
                } else {
                    sim[v] &= &r;
                }
            }
        }
        let mut map = VarLMap::new();
        let mut simval: HashMap<BitVec, Lit> = HashMap::default();
        for v in ts.rel.var_iter() {
            let lv = v.lit();
            let slv = if lv.polarity() {
                sim[lv.var()].clone()
            } else {
                !&sim[lv.var()]
            };
            if let Some(&m) = simval.get(&slv) {
                map.insert_lit(lv, m);
                continue;
            }
            let snlv = if (!lv).polarity() {
                sim[lv.var()].clone()
            } else {
                !&sim[lv.var()]
            };
            if let Some(&m) = simval.get(&snlv) {
                map.insert_lit(!lv, m);
                continue;
            }
            simval.insert(slv, lv);
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
                1,
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
