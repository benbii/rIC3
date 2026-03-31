use crate::{
    Lit, config::PreprocConfig, gipsat::DagCnfSolver, transys::{Transys, certify::Restore}
};
use logicrs::bitvec::BitVec;
use logicrs::{LitVec, Var, VarMap, satif::Satif};
use log::info;
use rand::{Rng, SeedableRng, rngs::StdRng, seq::SliceRandom};
use std::{path::Path, sync::atomic::{AtomicUsize, Ordering}};
use std::thread;

fn check_scorr(
    init_slv:&mut DagCnfSolver, ind_slv: &mut DagCnfSolver, ts: &Transys, x: Lit, y: Lit
) -> bool {
    if init_slv .solve_with_constraint(&[], vec![LitVec::from([x, y]), LitVec::from([!x, !y])]) {
        return false;
    }
    let xn = ts.next(x);
    let yn = if y.var().is_constant() { y } else { ts.next(y) };
    !ind_slv
        .solve_with_constraint(
            &[],
            vec![
            LitVec::from([x, !y]),
            LitVec::from([!x, y]),
            LitVec::from([xn, yn]),
            LitVec::from([!xn, !yn]),
            ],
        )
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
    sim
}

pub struct ToyScorr {
    ts: Transys,
    cfg: PreprocConfig,
}

impl ToyScorr {
    pub fn new(ts: Transys, cfg: &PreprocConfig) -> Self {
        Self {
            ts,
            cfg: cfg.clone(),
        }
    }

    pub fn run(mut self, _model: &Path, _output: &Path) -> anyhow::Result<(Transys, Restore)> {
        info!("original ts: {}", self.ts.statistic());
        let mut rst = Restore::new(&self.ts);
        if self.cfg.preproc {
            self.ts.simplify(&mut rst);
            info!("trivial simplified ts: {}", self.ts.statistic());
        }
        let nr = AtomicUsize::new(0);

        thread::scope(|scope| {
            let ts = &self.ts;
            let mut workers = Vec::with_capacity(48);
            for tid in 0..48 {
                let nr = &nr;
                workers.push(scope.spawn(move || {
                    let mut ind_slv = DagCnfSolver::new(&ts.rel);
                    let mut init_slv = DagCnfSolver::new(&ts.rel);
                    for c in ts.constraint.iter() {
                        ind_slv.add_clause(&[*c]);
                        init_slv.add_clause(&[*c]);
                    }
                    ts.load_init(&mut init_slv);
                    for i in (tid..ts.latch.len()).step_by(48) {
                        let x = ts.latch[i].lit();
                        for j in (i + 1)..ts.latch.len() {
                            let y = ts.latch[j].lit();
                            if check_scorr(&mut init_slv, &mut ind_slv, &ts, x, y) {
                                info!("{x} == {y}");
                                nr.fetch_add(1, Ordering::Relaxed);
                                break;
                            }
                            if check_scorr(&mut init_slv, &mut ind_slv, &ts, x, !y) {
                                info!("{x} == !{y}");
                                nr.fetch_add(1, Ordering::Relaxed);
                                break;
                            }
                        }
                    }
                }));
            }
            workers
                .into_iter()
                .map(|worker| worker.join().unwrap())
                .collect::<Vec<_>>()
        });
        info!(
            "{} latches eliminated by full 1-ind sweep",
            nr.load(Ordering::Relaxed)
        );

        // let init = init_simulation(&self.ts, 64);
        // info!(
        //     "toy-scorr: init simulation produced {} patterns for {} / {} latches",
        //     init[Var::CONST].len(),
        //     self.ts.latch.iter().filter(|v| !init[**v].is_empty()).count(),
        //     self.ts.latch.len(),
        // );
        Ok((self.ts, rst))
    }
}
