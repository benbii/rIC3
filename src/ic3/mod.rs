use crate::{
    BlWitness, Engine, McProof, McResult, McWitness,
    config::EngineConfig,
    gipsat::{DagCnfSolver, SolverStatistic},
    ic3::{block::BlockResult, localabs::LocalAbs, mab::CtgMab, predprop::PredProp},
    transys::{Transys, certify::Restore, lift::TsLift, unroll::TransysUnroll},
};
use activity::Activity;
use clap::{ArgAction, Args, Parser};
use frame::{Frame, Frames};
use log::{debug, error, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, satif::Satif};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{SeedableRng, rngs::SmallRng};
use serde::{Deserialize, Serialize};
use stat::Statistic;
use std::{sync::Arc, time::Instant};

mod activity;
mod block;
mod frame;
mod localabs;
mod mab;
mod mic;
mod predprop;
mod proofoblig;
mod propagate;
mod solver;
mod stat;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct IC3Config {
    /// Random seed
    #[arg(long, default_value_t = 0)]
    pub rseed: u64,
    /// Time limit in seconds
    #[arg(long, default_value_t = u64::MAX)]
    pub time_limit: u64,
    /// dynamic generalization
    #[arg(long = "dynamic", default_value_t = false)]
    pub dynamic: bool,
    /// contextual-MAB (LinUCB) adaptive generalization (A-IC3)
    #[arg(long = "mab", default_value_t = false)]
    pub mab: bool,
    /// LinUCB exploration parameter alpha
    #[arg(long = "mab-alpha", default_value_t = 1.0)]
    pub mab_alpha: f64,
    /// LinUCB regularization parameter lambda
    #[arg(long = "mab-lambda", default_value_t = 0.1)]
    pub mab_lambda: f64,
    /// counterexample to generalization
    #[arg(long = "ctg", action = ArgAction::Set, default_value_t = true)]
    pub ctg: bool,
    /// max number of ctg
    #[arg(long = "ctg-max", default_value_t = 3)]
    pub ctg_max: usize,
    /// ctg limit
    #[arg(long = "ctg-limit", default_value_t = 1)]
    pub ctg_limit: usize,
    /// counterexample to propagation
    #[arg(long = "ctp", default_value_t = false)]
    pub ctp: bool,
    /// internal signals (FMCAD'21 https://doi.org/10.34727/2021/isbn.978-3-85448-046-4_14)
    #[arg(long = "inn", default_value_t = false)]
    pub inn: bool,
    /// abstract constrains
    #[arg(long = "abs-cst", default_value_t = false)]
    pub abs_cst: bool,
    /// abstract trans
    #[arg(long = "abs-trans", default_value_t = false)]
    pub abs_trans: bool,
    /// dropping proof-obligation
    #[arg(long = "drop-po", action = ArgAction::Set, default_value_t = true)]
    pub drop_po: bool,
    /// finding parent lemma in mic (CAV'23 https://doi.org/10.1007/978-3-031-37703-7_14)
    #[arg(long = "parent-lemma", action = ArgAction::Set, default_value_t = true)]
    pub parent_lemma: bool,
    /// predicate property
    #[arg(long = "pred-prop", default_value_t = false)]
    pub pred_prop: bool,
    /// Local proof (buggy)
    #[arg(long = "local-proof", default_value_t = usize::MAX)]
    pub local_proof: usize,
    // stream infinity-frame lemmas as DIMACS-like clauses (append mode)
    // #[arg(long = "inv-dump")]
    // pub inv_dump: Option<PathBuf>,
}
impl Default for IC3Config {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "ic3"]);
        cfg.into_ic3().unwrap()
    }
}

pub struct IC3 {
    ts: Arc<Transys>,
    solvers: Vec<DagCnfSolver>,
    last_assump: Vec<LitVec>,
    inf_solver: DagCnfSolver,
    lift: TsLift,
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    localabs: LocalAbs,
    ots: Transys,
    rst: Restore,
    predprop: Option<PredProp>,
    mab: Option<CtgMab>,
    rng: SmallRng,
    time_limit: u64,
    default_mic: mic::DropVarParameter,
    inn: bool,
    abs_cst: bool,
    abs_trans: bool,
    drop_po: bool,
    dynamic: bool,
    ctp: bool,
    parent_lemma: bool,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        let nl = self.solvers.len();
        debug!("extending IC3 to level {nl}");
        if let Some(predprop) = self.predprop.as_mut() {
            predprop.extend(self.frame.inf.iter().map(|(l, _)| l.as_litvec()));
        }
        let solver = self.inf_solver.clone();
        self.solvers.push(solver);
        self.last_assump.push(LitVec::new());
        self.frame.push(Frame::new());
    }
}

impl IC3 {
    pub fn new(mut cfg: IC3Config, mut ts: Transys, ots: Transys, mut rst: Restore) -> Self {
        // validate config
        assert!(!cfg.dynamic || !cfg.mab, "dynamic & mab incompatible");
        assert!(!cfg.dynamic || !cfg.mab, "dynamic & drop_po incompatible");
        assert!(!cfg.mab || !cfg.drop_po, "mab & drop_po incompatible");
        assert!(!cfg.inn || !cfg.abs_trans, "inn & localAbs incompatible");
        assert!(!cfg.inn || !cfg.abs_cst, "inn & localAbs incompatible");

        let mut statistic = Statistic::default();
        ts.remove_gate_init(&mut rst);
        let real_bad = ts.bad.clone(); // only differs from ts.bad if local proof is on
        if cfg.local_proof < ts.bad.len() {
            cfg.pred_prop = true;
            ts.bad = LitVec::from(ts.bad[cfg.local_proof]);
        }
        if ts.bad.len() != 1 {
            error!("{} bads in IC3! Wrong preprocessed model load?", ts.bad.len());
        }
        let mut ts = Arc::new(ts);
        let mut predprop = None;
        if cfg.inn {
            let mut uts = TransysUnroll::new(Arc::clone(&ts));
            uts.unroll(true);
            ts = Arc::new(uts.internal_signals());
            if cfg.pred_prop {
                predprop = Some(PredProp::new(uts, cfg.local_proof, cfg.inn, &real_bad));
            }
        } else if cfg.pred_prop {
            let mut uts = TransysUnroll::new(Arc::clone(&ts));
            uts.unroll(true);
            predprop = Some(PredProp::new(uts, cfg.local_proof, cfg.inn, &real_bad));
        }

        let mut base_cex = None;
        if predprop.is_some() {
            let mut slv = ts.new_solver();
            for init in ts.inits() {
                slv.add_clause(&init);
            }
            if slv.solve(&[ts.bad[0]]) {
                let mut input = LitVec::new();
                for i in ts.input() {
                    if let Some(v) = slv.sat_value_lit(i) {
                        input.push(v);
                    }
                }
                let mut bad = LitVec::new();
                for l in ts.latch() {
                    if let Some(v) = slv.sat_value_lit(l) {
                        bad.push(v);
                    }
                }
                base_cex = Some(ProofObligation::new(
                    0,
                    LitOrdVec::new(bad),
                    vec![input],
                    0,
                    None,
                ));
            } else {
                unsafe { &mut *(Arc::as_ptr(&mut ts) as *mut Transys) }
                    .constraint
                    .extend(!&real_bad);
            }
        }

        let mut solvers = Vec::new();
        let mut last_assump = Vec::new();
        let mut obligations = ProofObligationQueue::new();
        let frames = if let Some(po) = base_cex {
            statistic.avg_po_cube_len += po.state.len();
            obligations.add(po);
            Frames::new(&ts)
        } else {
            let mut solver = ts.new_solver();
            let mut frame = Frame::new();
            for init in ts.inits() {
                let lemma = LitOrdVec::new(!init);
                if let Some(predprop) = predprop.as_mut() {
                    predprop.add_lemma(&lemma);
                }
                solver.add_clause(&!lemma.as_litvec());
                frame.push((lemma, None));
            }
            let mut init = LitVec::new();
            for l in ts.latch.iter() {
                if ts.init(*l).is_none()
                    && let Some(v) = solver.sat_value(l.lit())
                {
                    init.push(l.lit().not_if(!v));
                }
            }
            for i in init {
                unsafe { &mut *(Arc::as_ptr(&mut ts) as *mut Transys) }
                    .add_init(i.var(), Lit::constant(i.polarity()));
            }
            solvers.push(solver);
            last_assump.push(LitVec::new());
            let mut f = Frames::new(&ts);
            f.push(frame);
            f
        };

        Self {
            activity: Activity::new(&ts),
            solvers,
            last_assump,
            inf_solver: ts.new_solver(),
            lift: TsLift::new(TransysUnroll::new(Arc::clone(&ts))),
            statistic,
            obligations,
            frame: frames,
            localabs: LocalAbs::new(Arc::clone(&ts), cfg.abs_cst, cfg.abs_trans),
            ts,
            ots,
            rst,
            predprop,
            mab: cfg.mab.then(|| CtgMab::new(cfg.mab_alpha, cfg.mab_lambda)),
            rng: SmallRng::seed_from_u64(cfg.rseed),
            time_limit: cfg.time_limit,
            default_mic: if cfg.ctg {
                mic::DropVarParameter::new(cfg.ctg_limit, cfg.ctg_max, 1)
            } else {
                Default::default()
            },
            inn: cfg.inn,
            abs_cst: cfg.abs_cst,
            abs_trans: cfg.abs_trans,
            drop_po: cfg.drop_po,
            dynamic: cfg.dynamic,
            ctp: cfg.ctp,
            parent_lemma: cfg.parent_lemma,
        }
    }

    pub fn invariant(&self) -> Vec<LitVec> {
        self.inner_invariant()
            .iter()
            .map(|l| l.map_var(|l| self.rst.restore_var(l)))
            .collect()
    }
}

impl Engine for IC3 {
    fn check(&mut self) -> McResult {
        if self.solvers.len() == 0 {
            info!("ic3 found a counterexample at depth 0");
            return McResult::Unsafe(0);
        }
        let mut last_sec = 0;
        loop {
            let now_sec = self.statistic.time.time().as_secs();
            if now_sec > self.time_limit {
                return McResult::Unknown(Some(self.level()));
            }
            if now_sec - last_sec >= 10 {
                info!("{}", self.frame.statistic(true));
                last_sec = now_sec;
            }
            let start = Instant::now();

            loop {
                match self.block() {
                    BlockResult::Failure(depth) => {
                        self.statistic.block.overall_time += start.elapsed();
                        info!("ic3 found a counterexample at depth {depth}");
                        return McResult::Unsafe(depth);
                    }
                    BlockResult::Proved => {
                        self.statistic.block.overall_time += start.elapsed();
                        info!("ic3 proved the property");
                        return McResult::Safe;
                    }
                    _ => (),
                }
                if let Some((bad, inputs)) = self.get_bad() {
                    trace!("bad state {bad} found in frame {}", self.level());
                    let bad = LitOrdVec::new(bad);
                    let depth = inputs.len() - 1;
                    self.add_obligation(ProofObligation::new(
                        self.level(),
                        bad,
                        inputs,
                        depth,
                        None,
                    ))
                } else {
                    break;
                }
            }

            self.statistic.block.overall_time += start.elapsed();
            info!("ic3 found no counterexample up to depth {}", self.level());
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate(None);
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                info!("ic3 proved the property");
                return McResult::Safe;
            }
            self.propagate_to_inf();
        }
    }

    fn proof(&mut self) -> McProof {
        let mut proof = self.ots.clone_deep();
        if let Some(iv) = self.rst.init_var() {
            let piv = proof.add_init_var();
            self.rst.add_restore(iv, piv);
        }
        let mut invariants = self.inner_invariant();
        for c in self.ts.constraint.clone() {
            proof
                .rel_mut()
                .migrate(&self.ts.rel, c.var(), &mut self.rst.bvmap);
            invariants.push(LitVec::from(!c));
        }
        let mut invariants: Vec<LitVec> = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().map(|l| self.rst.restore(*l))))
            .collect();
        invariants.extend(self.rst.eq_invariant());
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel_mut().new_and(cube));
        }
        let invariants = proof.rel_mut().new_or(certifaiger_dnf);
        let proof_bad = std::mem::take(&mut proof.bad);
        let bad = proof.rel_mut().new_or(proof_bad);
        proof.bad = LitVec::from(proof.rel_mut().new_or([invariants, bad]));
        McProof::Bl(proof)
    }

    fn witness(&mut self) -> McWitness {
        let mut res = if let Some(res) = self.localabs.witness() {
            res
        } else {
            let mut res = BlWitness::default();
            let b = self.obligations.peak().unwrap();
            assert!(b.frame == 0);
            let mut b = Some(b);
            while let Some(bad) = b {
                res.state.push(bad.state.as_litvec().clone());
                res.input.push(bad.input[0].clone());
                for i in &bad.input[1..] {
                    res.input.push(i.clone());
                    res.state.push(LitVec::new());
                }
                b = bad.next.clone();
            }
            res
        };
        let iv = self.rst.init_var();
        res = res.filter_map(|l| {
            (iv != Some(l.var()))
                .then(|| self.rst.try_restore(l))
                .flatten()
        });
        for s in res.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        res.exact_state(&self.ots, true);
        McWitness::Bl(res)
    }

    fn statistic(&mut self) {
        info!("obligations: {}", self.obligations.statistic());
        info!("{}", self.frame.statistic(false));
        let mut statistic = SolverStatistic::default();
        for s in self.solvers.iter() {
            statistic += *s.statistic();
        }
        info!("{statistic:#?}");
        info!("{:#?}", self.statistic);
    }
}
