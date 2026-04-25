use crate::{
    Lit, aig::Aig, frontend::{Frontend, aig::AigFrontend},
    gipsat::DagCnfSolver,
    transys::{Transys, certify::Restore}
};
use ahash::HashMap;
use logicrs::bitvec::BitVec;
use logicrs::{LitVec, Var, VarLMap, VarMap, satif::Satif};
use rand::{SeedableRng, rngs::StdRng, seq::SliceRandom};
use std::{iter::zip, path::PathBuf};

pub fn toy_scorr(model:PathBuf, _output: PathBuf) -> (Transys, Restore) {
    let model = model.canonicalize().unwrap();
    let mut ts = AigFrontend::new(Aig::from_file(&model)).ts();
    println!("original ts: {}", ts.statistic());
    let mut rst = Restore::new(&ts);
    ts.simplify(&mut rst);
    println!("trivial simplified ts: {}", ts.statistic());

    // Step 0: run init simulation once
    let mut rng = StdRng::seed_from_u64(12345678);
    let mut sim: VarMap<BitVec> = VarMap::new_with(ts.max_var());
    let mut latch_shuf = ts.latch.clone();
    while sim[Var::CONST].len() < 32 {
        latch_shuf.shuffle(&mut rng);
        let mut slv = DagCnfSolver::new(&ts.rel);
        slv.rng = rng;
        // Disabling phase saving not needed. One brand new solver per iter after all
        // slv.use_phase_saving = false;
        for cls in ts.constraint() {
            slv.add_clause(&cls.cube());
        }
        ts.load_init(&mut slv);
        // Give all latches a concrete value
        // HACK: need a non-empty `assump` to ensure assignment on all of `domain`
        if !slv.solve_with_domain(&[Lit::constant(true)], &latch_shuf) {
            break;
        }
        for v in latch_shuf.iter() {
            sim[*v].push(slv.sat_value(v.lit()).unwrap());
        }
        sim[Var::CONST].push(false);
        rng = slv.rng;
    }

    let mut rng = StdRng::seed_from_u64(123456789);
    let mut maybe = ts.latch.clone();
    maybe.sort(); // so that small ID becomes class representitive
    'sweep: loop {
        // 1: Extract equivalence classes
        let mut cand: HashMap<BitVec, LitVec> = HashMap::default();
        cand.insert(sim[Var::CONST].clone(), LitVec::from([Lit::constant(false)]));
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
        let mut replace = VarLMap::new();
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

        // 2 THE QUERY: on replaced transition, try [xn, !yn] and [!yn, xn],
        // and acquire next-state latches.
        let mut rel = ts.rel.clone();
        rel.replace(&replace);
        let mut slv = DagCnfSolver::new(&rel);
        // safer to pass constraint unit-clauses through mapper as well
        for c in ts.constraint().map(|c| replace.map_lit(c).unwrap_or(c)) {
            slv.add_clause(&[c]);
        }
        slv.rng = rng;
        let nxt_maybe: Vec<Lit> = maybe.iter().map(|c| ts.next(c.lit())).collect();
        let domain: Vec<Var> = nxt_maybe.iter()
            .map(|l| replace.map_lit(*l).unwrap_or(*l).var())
            .collect();
        println!("built base solver with {} eqv classes", cand.len());

        // 3: sweep on x != y
        for eqc in cand.values() {
            let x = eqc[0];
            for &y in eqc.iter().skip(1) {
                // 4: Extract one total current-frame witness from the quotiented SAT model.
                let xn = if x.var().is_constant() { x } else { ts.next(x) };
                // `y` comes from `eqc.iter().skip(1)`, so it should not be constant.
                let yn = ts.next(y);
                // Yes. `rel.replace(&replace)` only rewrites occurrences inside the relation.
                // The top-level query literals still need to be mapped explicitly as well.
                let xn = replace.map_lit(xn).unwrap_or(xn);
                let yn = replace.map_lit(yn).unwrap_or(yn);
                if slv.solve_with_domain(&LitVec::from([xn, !yn]), &domain)
                    || slv.solve_with_domain(&LitVec::from([!xn, yn]), &domain)
                {
                    sim[Var::CONST].push(false);
                    for (y, yn) in zip(maybe.iter(), nxt_maybe.iter()) {
                        let yn = replace.map_lit(*yn).unwrap_or(*yn);
                        sim[*y].push(slv.sat_value(yn).unwrap());
                    }
                    rng = slv.rng;
                    continue 'sweep;
                }
            }
        }

        ts.replace(&replace, &mut rst);
        return (ts, rst);
    }
}

#[allow(dead_code)]
fn rt_simulation(ts: &Transys, sim: &mut VarMap<BitVec>, nr_patt: usize) {
    fn assign(sim: &VarMap<BitVec>, idx: usize, vars: &[Var]) -> LitVec {
        vars.iter().map(|&v| v.lit().not_if(!sim[v].get(idx))).collect()
    }
    let consider: Vec<_> = ts.latch().filter(|v| !sim[*v].is_empty()).collect();
    // HELP: let domain: Vec<_> = consider.iter().map(|&v| ts.next(v.lit()).var()).collect();
    let domain: Vec<_> = ts.next.values().map(|l| l.var()).collect();
    let init_len = sim[Var::CONST].len();
    let mut slv = DagCnfSolver::new(&ts.rel);
    slv.use_phase_saving = false;
    for cls in ts.constraint() { slv.add_clause(&cls.cube()); }
    for i in 0..init_len {
        let block = !assign(sim, i, &consider);
        let block = ts.lits_next(block.iter());
        slv.add_clause(&block);
    }

    fn dfs(
        ts: &Transys,
        sim: &mut VarMap<BitVec>,
        slv: &mut DagCnfSolver,
        consider: &[Var],
        domain: &[Var],
        nr_patt: usize,
        from: usize,
    ) {
        let assump = assign(sim, from, consider);
        if sim[Var::CONST].len() >= nr_patt { return; }
        // Some(5) limit is usually hit deep inside DFS when most assignments
        // in current exploration is blocked. At this time, better get off
        // and try other, shallower pre-image patterns :D
        if !slv
            .solve_with_param(&assump, vec![], domain.iter().copied(), Some(5))
            .unwrap_or(false)
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
        dfs(ts, sim, slv, consider, domain, nr_patt, sim[Var::CONST].len() - 1);
    }

    for from in 0..init_len {
        if sim[Var::CONST].len() >= nr_patt { return; }
        dfs(ts, &mut *sim, &mut slv, &consider, &domain, nr_patt, from);
    }
}
