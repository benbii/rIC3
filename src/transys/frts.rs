use crate::RseedMap as HashMap;
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
use std::{sync::Arc, time::Instant};

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
        let solver = DagCnfSolver::new(Arc::clone(&ts.rel));
        let mut rng = StdRng::seed_from_u64(0);
        let mut sim = VarMap::new_with(ts.max_var());
        sim[Var::CONST] = BitVec::from_elem(NUM_WORD * BitVec::WORD_SIZE, false);
        for v in VarRange::new_inclusive(Var(1), ts.max_var()) {
            if ts.rel.clauses_of_var(v).is_empty() {
                sim[v] = BitVec::new_rand(NUM_WORD, &mut rng);
                continue;
            }
            sim[v] = BitVec::from_elem(NUM_WORD * BitVec::WORD_SIZE, false);
        }
        for v in VarRange::new_inclusive(Var(1), ts.max_var()) {
            if ts.rel.clauses_of_var(v).is_empty() {
                continue;
            }
            for rel in ts.rel.clauses_of_var(v) {
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
        for v in VarRange::new_inclusive(Var::CONST, ts.rel.max_var()) {
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

    pub fn fr(self) -> (Transys, Restore) {
        let FrTs {
            cfg,
            mut ts,
            map,
            mut solver,
            mut rst,
        } = self;
        let start = Instant::now();
        let before = ts.max_var();
        let mut replace = VarLMap::new();
        let mut v = Var(1);
        while v <= ts.max_var() {
            if start.elapsed().as_secs() > cfg.frts_tl {
                info!("frts: timeout");
                break;
            }
            if ts.rel.clauses_of_var(v).is_empty() {
                v += 1;
                continue;
            }
            let Some(m) = map.map(v) else {
                v += 1;
                continue;
            };
            let lv = v.lit();
            trace!("frts: checking var {m} with lit {v}");
            match solver.solve_with_restart_limit(
                &[],
                &[LitVec::from([m, lv]), LitVec::from([!m, !lv])],
                1,
            ) {
                Some(true) => {}
                Some(false) => {
                    debug!("{v} -> {m}");
                    replace.insert_lit(lv, m);
                    solver.add_eq(lv, m);
                    if replace.len().is_multiple_of(2000) {
                        drop(solver);
                        ts.replace(&replace, &mut rst);
                        ts.coi_refine(&mut rst);
                        let mut simp = DagCnfSimplify::new(&ts.rel);
                        for &v in ts.frozens().iter() {
                            simp.froze(v);
                        }
                        simp.const_simplify();
                        simp.bve_simplify();
                        ts.rel = Arc::new(simp.finalize());
                        solver = DagCnfSolver::new(Arc::clone(&ts.rel));
                        info!("{} simps: {}", replace.len(), ts.statistic());
                    }
                }
                None => {
                    debug!("frts: checking {v} with {m} timeout");
                }
            }
            v += 1;
        }
        drop(solver);
        ts.replace(&replace, &mut rst);
        ts.coi_refine(&mut rst);
        ts.rearrange(&mut rst);
        info!(
            "frts: eliminates {} out of {} vars in {:.2}s",
            *before - *ts.max_var(),
            *before,
            start.elapsed().as_secs_f32()
        );
        ts.simplify(&mut rst);
        info!("frts: simplified ts: {}", ts.statistic());
        (ts, rst)
    }
}
