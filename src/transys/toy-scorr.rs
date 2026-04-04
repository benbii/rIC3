use crate::{
    Lit, aig::Aig, frontend::{Frontend, aig::AigFrontend},
    gipsat::DagCnfSolver,
    transys::{Transys, certify::Restore}
};
use ahash::HashMap;
use logicrs::bitvec::BitVec;
use logicrs::{LitVec, Var, VarLMap, VarMap, satif::Satif};
use rand::{Rng, SeedableRng, rngs::StdRng, seq::SliceRandom};
use std::{fs::File, io::{BufWriter, Write}, path::PathBuf};

fn check_scorr(
    base_slv: &mut DagCnfSolver, ts: &Transys, replace: &VarLMap, x: Lit, y: Lit
) -> bool {
    let xn = if x.var().is_constant() {
        x
    } else {
        let xn = ts.next(x);
        replace.map_lit(xn).unwrap_or(xn)
    };
    let yn = if y.var().is_constant() {
        y
    } else {
        let yn = ts.next(y);
        replace.map_lit(yn).unwrap_or(yn)
    };
    if base_slv.solve(&[xn, !yn]) {
        return false;
    }
    !base_slv.solve(&[!xn, yn])
}

fn init_simulation(ts: &Transys, num_pattern: usize) -> VarMap<BitVec> {
    let mut rng = StdRng::seed_from_u64(12345678);
    let mut sim: VarMap<BitVec> = VarMap::new_with(ts.max_var());
    sim.reserve(ts.max_var());
    let mut latches = ts.latch.clone();

    while sim[Var::CONST].len() < num_pattern {
        // Or use cadical instead?
        let mut slv = DagCnfSolver::new(&ts.rel);
        slv.rng = rng;
        // Disabling phase saving needed? One brand new solver per iter after all
        // slv.use_phase_saving = false;
        for cls in ts.constraint() {
            slv.add_clause(&cls.cube());
        }
        ts.load_init(&mut slv);
        if !slv.solve(&[]) { break; }

        latches.shuffle(&mut slv.rng);
        // Give all latches a concrete value
        for &v in latches.iter() {
            if slv.sat_value(v.lit()).is_some() { continue; }
            // biase towards 1 and perturb solver rng further
            let decided = if slv.rng.random_bool(0.6) {v.lit()} else {!v.lit()};
            if slv.solve(&[decided]) {
                slv.add_clause(&[decided]);
            } else {
                // given previous solves are SAT, at least one of v and !v should SAT.
                debug_assert!(slv.solve(&[!decided]));
                slv.add_clause(&[!decided]);
            }
            // no push to sim until all latch assignments stablize
        }
        // and then collect latch values
        for &v in ts.latch.iter() {
            let a = slv.sat_value(v.lit()).unwrap();
            sim[v].push(a);
        }
        sim[Var::CONST].push(false);
        rng = slv.rng;
    }

    // filter singletons
    let mut cand: HashMap<BitVec, bool> = HashMap::default();
    cand.insert(sim[Var::CONST].clone(), true);
    for &v in ts.latch.iter() {
        if let Some(c) = cand.get_mut(&sim[v]) {
            *c = false;
        } else if let Some(c) = cand.get_mut(&!&sim[v]) {
            *c = false;
        } else {
            cand.insert(sim[v].clone(), true);
        }
    }
    for &v in ts.latch.iter() {
        // doesn't exist y where x = y or !y <=> x gets inserted once with true
        // exists y where x = y <=> the latter of x,y turns common entry false
        // exists y where x = !y <=> the earlier of x,y is turned false,
        // the latter of x,y never gets inserted (aka. None)
        if *cand.get(&sim[v]).unwrap_or(&false) {
            sim[v].clear();
        }
    }
    sim
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

pub fn toy_scorr(model:PathBuf, output:PathBuf) -> (Transys, Restore) {
    let model = model.canonicalize().unwrap();
    let mut ts = AigFrontend::new(Aig::from_file(&model)).ts();
    println!("original ts: {}", ts.statistic());
    let mut rst = Restore::new(&ts);
    ts.simplify(&mut rst);
    println!("trivial simplified ts: {}", ts.statistic());
    let sim = init_simulation(&ts, 32);
    println!(
        "init-simulated {} patterns for {} / {} latches into {}",
        sim[Var::CONST].len(),
        ts.latch.iter().filter(|v| !sim[**v].is_empty()).count(),
        ts.latch.len(), output.display()
    );
    // let mut w = BufWriter::new(File::create(output).unwrap());
    // for l in ts.latch.iter().filter(|v| !sim[**v].is_empty()) {
    //     writeln!(&mut w, "{l}: {}", sim[*l]).unwrap();
    // }

    let mut latch: Vec<_> = ts.latch().filter(|v| !sim[*v].is_empty()).collect();
    latch.sort(); // so that small ID becomes class representitive
    let mut cand: HashMap<BitVec, LitVec> = HashMap::default();
    cand.insert(sim[Var::CONST].clone(), LitVec::from([Lit::constant(false)]));
    for &v in latch.iter() {
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
    let mut replace = VarLMap::new();
    for eqc in cand.values() {
        let repr = eqc[0];
        for &m in eqc.iter().skip(1) {
            replace.insert_lit(m, repr);
        }
    }

    // Construct base solver
    let mut rel = ts.rel.clone();
    rel.replace(&replace);
    let mut base_slv = DagCnfSolver::new(&rel);
    // safer to pass constraint unit-clauses through mapper as well
    for c in ts.constraint().map(|c| replace.map_lit(c).unwrap_or(c)) {
        base_slv.add_clause(&[c]);
    }
    println!("built base solver with {} eqv classes", cand.len());
    let mut nr_eq = 0;
    let mut nr_neq = 0;
    for eqc in cand.values() {
        let repr = eqc[0];
        for &m in eqc.iter().skip(1) {
            if check_scorr(&mut base_slv, &ts, &replace, repr, m) {
                // println!("{repr} == {m}");
                nr_eq += 1;
            } else {
                // println!("{repr} != {m}");
                nr_neq += 1;
            }
        }
    }
    println!("base sweep proved {nr_eq}, disproved {nr_neq}");

    (ts, rst)
}
