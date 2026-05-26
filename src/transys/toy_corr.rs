use crate::{
    Btor, Lit, VarRange, aig::Aig, frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend}, gipsat::DagCnfSolver, transys::{Transys, certify::Restore}
};
use ahash::HashMap;
use log::{debug, info, trace, warn};
use logicrs::bitvec::BitVec;
use logicrs::{satif::Satif, LitVec, Var, VarLMap, VarMap};
use rand::{rngs::StdRng, SeedableRng};
use std::{iter::zip, path::PathBuf};

pub fn toy_scorr(mut ts: Transys, mut rst: Restore) -> (Transys, Restore) {
    info!("original ts: {}", ts.statistic());
    ts.simplify(&mut rst);
    info!("trivial simplified ts: {}", ts.statistic());
    // run constraint-aware simulation
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
    let mut stack = vec![0usize];
    while sim[Var::CONST].len() < 64 {
        let Some(&from) = stack.last() else { break; };
        let assump = ts.latch.iter().map(|&v| v.lit().not_if(!sim[v].get(from)));
        let assump: LitVec = assump.collect();
        match slv.solve_full(&assump, &[], &domain, 5) {
            Some(true) => {}
            Some(false) => {
                warn!("rt sim exhausted at len {} from {from}", sim[Var::CONST].len());
                stack.pop();
                continue;
            }
            None => {
                warn!("rt sim restart-limited at len {} from {from}", sim[Var::CONST].len());
                stack.pop();
                continue;
            }
        }
        let to = sim[Var::CONST].len();
        sim[Var::CONST].push(false);
        // essentially "do not give me a latch state I already sampled"
        let mut block = Vec::with_capacity(ts.latch.len());
        for (&v, &n) in zip(ts.latch.iter(), next_lits.iter()) {
            sim[v].push(slv.sat_value(n).unwrap());
            block.push(!slv.sat_value_lit(n.var()).unwrap());
        }
        slv.add_clause(&block);
        stack.push(to);
    }
    if sim[Var::CONST].len() < 3 {
        return (ts, rst); // too few valid states; bail out
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
        let mut ind_slv = DagCnfSolver::new(&rel);
        // safer to pass constraint unit-clauses through mapper as well
        for c in ts.constraint().map(|c| replace.map_lit(c).unwrap_or(c)) {
            ind_slv.add_clause(&[c]);
        }
        ind_slv.rng = rng;
        let mut sim_slv = ind_slv.clone();
        ind_slv.use_phase_saving = false;
        sim_slv.use_phase_saving = false;
        let nxt_maybe: Vec<Lit> = maybe.iter().map(|c| ts.next(c.lit())).collect();
        let domain: Vec<Var> = nxt_maybe
            .iter()
            .map(|l| replace.map_lit(*l).unwrap_or(*l).var())
            .collect();
        info!("{prevround_simsz} patterns, {} eqv classes", cand.len());

        // 3: sweep on x != y
        for eqc in cand.values() {
            let x = eqc[0];
            for &y in eqc.iter().skip(1) {
                // 4: Extract one total current-frame witness from the quotiented SAT model.
                // If in current outer loop round some SAT traces already discern the two, just stop
                // checking them. The comparison is incomplete, but 64~128 traces is decent enough.
                if sim[x.var()].ne_inv(&sim[y.var()], x.polarity() != y.polarity()) {
                    continue;
                }
                let xn = if x.var().is_constant() { x } else { ts.next(x) };
                // `y` comes from `eqc.iter().skip(1)`, so it should not be constant.
                let yn = ts.next(y);
                let xn = replace.map_lit(xn).unwrap_or(xn);
                let yn = replace.map_lit(yn).unwrap_or(yn);
                if xn == yn { continue; }

                if !ind_slv.solve(&LitVec::from([xn, !yn])) {
                    ind_slv.add_clause(&[!xn, yn]);
                    sim_slv.add_clause(&[!xn, yn]);
                    if !ind_slv.solve(&LitVec::from([!xn, yn])) {
                        ind_slv.add_clause(&[xn, !yn]);
                        sim_slv.add_clause(&[xn, !yn]);
                        continue; // x == y under current assumption :D
                    }
                }

                let mut assump: LitVec = ts
                    .input()
                    .chain(ts.latch())
                    .filter_map(|v| ind_slv.sat_value_lit(v))
                    .map(|l| replace.map_lit(l).unwrap_or(l))
                    .collect();
                assump.push(ind_slv.sat_value_lit(xn.var()).unwrap());
                assump.push(ind_slv.sat_value_lit(yn.var()).unwrap());
                assump.sort();
                assump.dedup();
                assert!(sim_slv.solve_with_domain(&assump, &domain));
                sim[Var::CONST].push(false);
                for (l, ln) in zip(maybe.iter(), nxt_maybe.iter()) {
                    let ln = replace.map_lit(*ln).unwrap_or(*ln);
                    sim[*l].push(sim_slv.sat_value(ln).unwrap());
                }
            }
        }

        rng = ind_slv.rng; // so that solver rng does not restart with 0
    }
    ts.replace(&replace, &mut rst);
    ts.simplify(&mut rst);
    info!("toy scorr'd ts: {}", ts.statistic());
    return (ts, rst);
}

pub fn toy_ccorr(mut ts: Transys, mut rst: Restore) -> (Transys, Restore) {
    ts.topsort(&mut rst);
    let mut rng = StdRng::seed_from_u64(9876543210);
    let mut sim = VarMap::new_with(ts.max_var());
    // 65536 init patterns, with 1 additional pattern per SAT counterexample.
    // Var::CONST is represented by the positive literal of var 0, i.e. false.
    sim[Var::CONST] = BitVec::from_elem(65536, false);
    for v in VarRange::new_inclusive(Var::new(1), ts.max_var()) {
        sim[v] = if ts.rel.is_leaf(v) {
            BitVec::new_rand(65536 / BitVec::WORD_SIZE, &mut rng)
        } else {
            BitVec::from_elem(65536, false)
        }
    };
    // bit-parallel simulation of these patterns
    for v in VarRange::new_inclusive(Var(1), ts.max_var()) {
        if ts.rel.is_leaf(v) { continue; }
        for rel in &ts.rel[v] {
            let mut r = if rel[0].polarity() {
                sim[rel[0].var()].clone()
            } else {
                !&sim[rel[0].var()]
            };
            let mut vl = rel[0];
            for &l in &rel[1..] {
                if l.var() == v { vl = l; }
                if l.polarity() { r |= &sim[l.var()] } else { r |= &!&sim[l.var()] };
            }
            if vl.polarity() { sim[v] |= &!&r; } else { sim[v] &= &r; }
        }
    }

    // combinational sweep doesn't benefit from multi-round over-assumption refinement loop
    // so just build it once here lol.
    let mut cand: HashMap<BitVec, LitVec> = HashMap::default();
    for v in VarRange::new_inclusive(Var(0), ts.max_var()) {
        // HELP: what to do with latches, next states etc?
        let l = v.lit();
        if let Some(c) = cand.get_mut(&sim[v]) {
            c.push(l);
        } else if let Some(c) = cand.get_mut(&!&sim[v]) {
            c.push(!l);
        } else {
            cand.insert(sim[v].clone(), LitVec::from([l]));
        }
    }
    cand.retain(|_, eqc| eqc.len() > 1);
    let maybe: Vec<Var> = cand.values().flatten().map(|x| x.var()).collect();
    sim.iter_mut().for_each(|x| x.clear());

    let mut replace = VarLMap::new();
    let rel = ts.rel.clone();
    let mut ind_slv = DagCnfSolver::new(&rel);
    ind_slv.rng = rng;
    let mut sim_slv = ind_slv.clone();
    ind_slv.use_phase_saving = false;
    sim_slv.use_phase_saving = false;
    let mut fail  = VarMap::<u8>::new_with(ts.max_var() + 1);
    info!("{} cand classes", cand.len());

    for (ci, eqc) in cand.values().enumerate() {
        for (xi, x) in eqc.iter().copied().enumerate() {
            if replace.contains_key(&x.var()) { continue; }
            for (yi, &y) in eqc.iter().enumerate().skip(xi + 1) {
                debug_assert!(x != y);
                if replace.contains_key(&y.var()) { continue; }
                // simplify model every 5000 or 2000 replaces here?
                // ne_inv serves as "class refinement during sweep"
                if fail[x.var()] >= 1 || fail[y.var()] >= 1 ||
                    replace.contains_key(&y.var()) ||
                    sim[x.var()].ne_inv(&sim[y.var()], x.polarity() != y.polarity())
                {
                    continue;
                }

                match ind_slv.solve_full(&[x, !y], &[], &[], 1) {
                    None => {
                        debug!("XImplyY died; class {ci} xIdx {xi} yIdx {yi}");
                        fail[x.var()] += 1; fail[y.var()] += 1;
                        continue;
                    },
                    Some(true) => {},
                    _ => {
                        ind_slv.add_clause(&[!x, y]);
                        sim_slv.add_clause(&[!x, y]);
                        match ind_slv.solve_full(&[!x, y], &[], &[], 1) {
                            None => {
                                debug!("YImplyX died; class {ci} xIdx {xi} yIdx {yi}");
                                fail[x.var()] += 1; fail[y.var()] += 1;
                                continue;
                            },
                            Some(true) => {},
                            _ => {
                                ind_slv.add_clause(&[x, !y]);
                                sim_slv.add_clause(&[x, !y]);
                                replace.insert_lit(y, x);
                                continue; // x == y under current assumption :D
                            }
                        }
                    }
                }

                // in comb sweep the assump is for speed only:
                // replay through whole CNF using clues provided by ind_slv
                let assump: LitVec = VarRange::new_inclusive(Var(1), ts.max_var())
                    .filter_map(|v| ind_slv.sat_value_lit(v)).collect();
                debug_assert_ne!(ind_slv.sat_value(x), ind_slv.sat_value(y));
                assert!(sim_slv.solve_with_domain(&assump, &maybe));
                // Var::CONST is already in maybe (if any var could equal to CONST)
                for v in maybe.iter() {
                    sim[*v].push(sim_slv.sat_value(v.lit()).unwrap());
                }
            }
        }
        trace!("{ci}, {} replaced, {} patterns", replace.len(), sim[Var::CONST].len());
    }

    ts.replace(&replace, &mut rst);
    ts.simplify(&mut rst);
    info!("toy fraig'd ts: {}", ts.statistic());
    (ts, rst)
}

pub fn toy_corr(model: PathBuf) -> (Transys, Restore) {
    let model = model.canonicalize().unwrap();
    let ts = match model.extension() {
        Some(ext) if (ext == "aig") || (ext == "aag") => {
            AigFrontend::new(Aig::from_file(&model)).ts()
        }
        Some(ext) if (ext == "btor") || (ext == "btor2") => {
            BtorFrontend::new(Btor::from_file(&model)).ts()
        }
        _ => panic!("unknown model file extention")
    };
    let rst = Restore::new(&ts);
    let (ts, rst) = toy_scorr(ts, rst);
    toy_ccorr(ts, rst)
    // toy_scorr(ts, rst)
}
