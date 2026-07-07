use crate::RseedMap as HashMap;
use crate::{
    config::PreprocConfig,
    gipsat::DagCnfSolver,
    transys::{Transys, certify::Restore},
};
use log::{info, trace};
use logicrs::{Lit, Var, VarLMap, VarMap, VarRange, bitvec::BitVec, simplify::DagCnfSimplify};
use rand::{SeedableRng, rngs::SmallRng};
use std::{sync::Arc, time::Instant};

pub fn combsweep(mut ts: Transys, cfg: &PreprocConfig, mut rst: Restore) -> (Transys, Restore) {
    ts.topsort(&mut rst);
    let mut rng = SmallRng::seed_from_u64(0);
    let mut sim = VarMap::new_with(ts.max_var());
    sim[Var::CONST] = BitVec::from_elem(65536, false);
    for v in VarRange::new_inclusive(Var(1), ts.max_var()) {
        if ts.rel.clauses_of_var(v).is_empty() {
            sim[v] = BitVec::new_rand(1024, &mut rng);
            continue;
        }
        sim[v] = BitVec::from_elem(65536, false);
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

    let start = Instant::now();
    let before = ts.max_var();
    let mut replace = VarLMap::new();
    let mut v = Var(0);
    let mut solver = DagCnfSolver::new(Arc::clone(&ts.rel));
    let mut half_impl = Vec::with_capacity(10000);
    while v < ts.max_var() {
        v += 1;
        if start.elapsed().as_secs() > cfg.frts_tl {
            info!("frts: timeout");
            break;
        }
        if ts.rel.clauses_of_var(v).is_empty() {
            continue;
        }
        let Some(m) = map.map(v) else {
            continue;
        };
        let lv = v.lit();

        if solver.solve_full(&[m, !lv], &[], &[], 1) == Some(false) {
            trace!("{m}->{lv}");
            solver.add_entailed_clause(&[!m, lv]);
            if solver.solve_full(&[!m, lv], &[], &[], 1) == Some(false) {
                trace!("{lv}=={m}");
                replace.insert_lit(lv, m);
                solver.add_entailed_clause(&[m, !lv]);
                if replace.len().is_multiple_of(2000) {
                    drop(solver);
                    ts.replace(&replace, &mut rst);
                    ts.coi_refine(&mut rst);
                    let mut simp = DagCnfSimplify::new(&ts.rel);
                    let frozens = ts.frozens();
                    for &v in &frozens {
                        simp.freeze(v);
                    }
                    simp.const_simplify();
                    simp.bve_simplify();
                    ts.rel = Arc::new(simp.finalize());
                    solver = DagCnfSolver::new(Arc::clone(&ts.rel));
                    let alive = |l: Lit| {
                        l.var().is_constant()
                            || !ts.rel.clauses_of_var(l.var()).is_empty()
                            || frozens.contains(&l.var())
                    };
                    half_impl.retain_mut(|(a, b)| {
                        *a = replace.map_lit(*a).unwrap_or(*a);
                        *b = replace.map_lit(*b).unwrap_or(*b);
                        if *a == !*b || !alive(*a) || !alive(*b) {
                            return false;
                        }
                        solver.add_entailed_clause(&[*a, *b]);
                        true
                    });
                    info!("{} replaces: {}", replace.len(), ts.statistic());
                }
            } else {
                half_impl.push((!m, lv));
            }
        }
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
