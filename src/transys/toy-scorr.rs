use crate::{
    aig::Aig,
    frontend::{aig::AigFrontend, Frontend},
    gipsat::DagCnfSolver,
    transys::{certify::Restore, Transys},
    Lit,
};
use ahash::HashMap;
use logicrs::bitvec::BitVec;
use logicrs::{satif::Satif, LitVec, Var, VarLMap, VarMap};
use rand::{rngs::StdRng, SeedableRng};
use std::{iter::zip, path::PathBuf};

pub fn toy_scorr(model: PathBuf, _output: PathBuf) -> (Transys, Restore) {
    let model = model.canonicalize().unwrap();
    let mut ts = AigFrontend::new(Aig::from_file(&model)).ts();
    println!("original ts: {}", ts.statistic());
    let mut rst = Restore::new(&ts);
    ts.simplify(&mut rst);
    println!("trivial simplified ts: {}", ts.statistic());

    // Step 0: run simulation once
    // seed exactly one init state
    let mut sim: VarMap<BitVec> = VarMap::new_with(ts.max_var());
    let mut slv = DagCnfSolver::new(&ts.rel);
    for cls in ts.constraint() {
        slv.add_clause(&[cls]);
    }
    ts.load_init(&mut slv);
    for &v in &ts.latch {
        if ts.init(v).is_none() {
            slv.add_clause(&[!v.lit()]);
        }
    }
    if !slv.solve_with_domain(&[Lit::constant(true)], &ts.latch) {
        return (ts, rst); // not a single state satisfying init; bail out
    }
    sim[Var::CONST].push(false);
    for &v in &ts.latch {
        sim[v].push(slv.sat_value(v.lit()).unwrap());
    }

    // generate the rest of patterns by transition solving, not load_init
    let mut slv = DagCnfSolver::new(&ts.rel);
    slv.use_phase_saving = false;
    for c in ts.constraint() {
        slv.add_clause(&[c]);
    }
    let next_lits: Vec<Lit> = ts.latch.iter().map(|&v| ts.next(v.lit())).collect();
    let domain: Vec<Var> = next_lits.iter().map(|l| l.var()).collect();
    let mut from = 0;
    while sim[Var::CONST].len() < 64 {
        let assump = ts.latch.iter().map(|&v| v.lit().not_if(!sim[v].get(from)));
        let assump: LitVec = assump.collect();
        if !slv.solve_with_domain(&assump, &domain) {
            // no more reachable states from current assignment! Back off
            if from == 0 { break; }
            from -= 1;
            continue;
        }
        from = sim[Var::CONST].len(); // dfs
        sim[Var::CONST].push(false);
        // essentially "do not give me a latch state I already sampled"
        let mut block = Vec::with_capacity(ts.latch.len());
        for (&v, &n) in zip(ts.latch.iter(), next_lits.iter()) {
            sim[v].push(slv.sat_value(n).unwrap());
            block.push(!slv.sat_value_lit(n.var()).unwrap());
        }
        slv.add_clause(&block);
    }

    let mut rng = StdRng::seed_from_u64(123456789);
    let mut maybe = ts.latch.clone();
    maybe.sort(); // so that small ID becomes class representitive
    let mut replace = VarLMap::new();
    let mut prevround_simsz = usize::MAX;
    // A SAT pushing sim trace length **will always** split classes further because in the trace
    // x != y, causing the class containing x and y to split, so progress are always made
    while prevround_simsz != sim[Var::CONST].len() {
        prevround_simsz = sim[Var::CONST].len();

        // 1: Extract equivalence classes
        let mut cand: HashMap<BitVec, LitVec> = HashMap::default();
        cand.insert(
            sim[Var::CONST].clone(),
            LitVec::from([Lit::constant(false)]),
        );
        for &v in maybe.iter() {
            let l = v.lit();
            if let Some(c) = cand.get_mut(&sim[v]) {
                c.push(l);
            } else if let Some(c) = cand.get_mut(&!&sim[v]) {
                c.push(!l);
            } else {
                cand.insert(sim[v].clone(), LitVec::from([l]));
            }
        }
        replace.clear();
        cand.retain(|_, eqc| {
            let repr = eqc[0];
            if eqc.len() <= 1 {
                if !repr.var().is_constant() {
                    sim[repr].clear();
                }
                return false;
            }
            for &m in eqc.iter().skip(1) {
                replace.insert_lit(m, repr);
            }
            true
        });
        maybe.retain(|v| !sim[*v].is_empty());

        // 2: build solver
        let mut rel = ts.rel.clone();
        rel.replace(&replace);
        let mut slv = DagCnfSolver::new(&rel);
        // safer to pass constraint unit-clauses through mapper as well
        for c in ts.constraint().map(|c| replace.map_lit(c).unwrap_or(c)) {
            slv.add_clause(&[c]);
        }
        slv.rng = rng;
        slv.use_phase_saving = false;
        let nxt_maybe: Vec<Lit> = maybe.iter().map(|c| ts.next(c.lit())).collect();
        let domain: Vec<Var> = nxt_maybe
            .iter()
            .map(|l| replace.map_lit(*l).unwrap_or(*l).var())
            .collect();
        println!("{prevround_simsz} patterns, {} eqv classes", cand.len());

        // 3: sweep on x != y
        for eqc in cand.values() {
            let x = eqc[0];
            for &y in eqc.iter().skip(1) {
                // 4: Extract one total current-frame witness from the quotiented SAT model.
                // If in current outer loop round some SAT traces already discern the two, just stop
                // checking them. The comparison is incomplete, but 64~128 traces is decent enough.
                if sim[x.var()].ne_coarse(&sim[y.var()], x.polarity() != y.polarity()) {
                    continue;
                }
                let xn = if x.var().is_constant() { x } else { ts.next(x) };
                // `y` comes from `eqc.iter().skip(1)`, so it should not be constant.
                let yn = ts.next(y);
                let xn = replace.map_lit(xn).unwrap_or(xn);
                let yn = replace.map_lit(yn).unwrap_or(yn);
                if !slv.solve_with_domain(&LitVec::from([xn, !yn]), &domain)
                    && !slv.solve_with_domain(&LitVec::from([!xn, yn]), &domain)
                {
                    continue; // x == y under current assumption :D
                }
                sim[Var::CONST].push(false);
                // if sim[Var::CONST].len() % 128 == 0 {
                    // println!("{} patterns", sim[Var::CONST].len());
                // }
                for (l, ln) in zip(maybe.iter(), nxt_maybe.iter()) {
                    let ln = replace.map_lit(*ln).unwrap_or(*ln);
                    sim[*l].push(slv.sat_value(ln).unwrap());
                }
            }
        }

        rng = slv.rng; // so that solver rng does not restart with 0
    }
    ts.replace(&replace, &mut rst);
    println!("toy scorr'd ts: {}", ts.statistic());
    return (ts, rst);
}
