use crate::{
    BlProof, BlWitness, Engine, McProof, McResult, McWitness,
    config::{EngineConfig, PreprocConfig},
    gipsat::{DagCnfSolver, SolverStatistic, new_transys_solver},
    ic3::{block::BlockResult, localabs::LocalAbs, predprop::PredProp},
    transys::{
        Transys, TransysCtx, certify::Restore, lift::TsLift, preproc_serde::PreprocModel,
        unroll::TransysUnroll,
    },
};
use activity::Activity;
use clap::{ArgAction, Args, Parser};
use frame::{Frame, Frames};
use log::{debug, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, LitVvec, satif::Satif};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use stat::Statistic;
use std::{num::NonZeroU64, time::Instant};

mod activity;
mod auxv;
mod block;
mod frame;
mod localabs;
mod mic;
mod predprop;
mod proofoblig;
mod propagate;
mod solver;
mod stat;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct IC3Config {
    /// Property ID. If not specified, all properties are checked.
    #[arg(long = "prop")]
    pub prop: Option<usize>,
    /// Random seed
    #[arg(long, default_value_t = 0)]
    pub rseed: u64,
    /// Time limit in seconds
    #[arg(long)]
    pub time_limit: Option<NonZeroU64>,
    #[command(flatten)]
    pub preproc: PreprocConfig,
    /// dynamic generalization
    #[arg(long = "dynamic", default_value_t = false)]
    pub dynamic: bool,
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
    /// Local proof (internal parameter)
    #[arg(skip)]
    pub local_proof: bool,
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
    ts: Transys,
    tsctx: Box<TransysCtx>,
    solvers: Vec<DagCnfSolver>,
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
    rng: StdRng,
    time_limit: Option<NonZeroU64>,
    prop: usize,
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
        self.frame.push(Frame::new());
        if self.level() == 0 {
            for init in self.tsctx.init.clone() {
                self.add_lemma(0, !init, true, None);
            }
            let mut init = LitVec::new();
            for l in self.tsctx.latch.iter() {
                if self.tsctx.init_map[*l].is_none()
                    && let Some(v) = self.solvers[0].sat_value(l.lit())
                {
                    let l = l.lit().not_if(!v);
                    init.push(l);
                }
            }
            for i in init {
                self.ts.add_init(i.var(), Lit::constant(i.polarity()));
                self.tsctx.add_init(i.var(), Lit::constant(i.polarity()));
            }
        }
    }
}

impl IC3 {
    pub fn new(mut cfg: IC3Config, mut ts: Transys) -> Self {
        // validate config
        if cfg.dynamic && cfg.drop_po {
            panic!("cannot enable both dynamic and drop-po");
        }
        if cfg.inn && (cfg.abs_cst || cfg.abs_trans) {
            panic!("cannot enable both inn and (abs_cst or abs_trans)");
        }
        if cfg.local_proof {
            cfg.pred_prop = true;
            if cfg.prop.is_none() {
                panic!("A property ID must be specified for local proof.");
            }
        }
        let prop = cfg.prop.unwrap_or(0);

        let ots = ts.clone();
        if cfg.prop.is_some() && !cfg.local_proof {
            ts.bad = LitVec::from(ts.bad[prop]);
        }
        let rng = StdRng::seed_from_u64(cfg.rseed);
        let statistic = Statistic::default();
        let (model, loaded) = PreprocModel::load_or_preproc(ts, &cfg.preproc);
        let (mut ts, mut rst) = (model.ts, model.rst);
        if loaded && cfg.prop.is_some() && !cfg.local_proof {
            ts.bad = LitVec::from(ts.bad[prop]);
        }
        if cfg.prop.is_none() && ts.bad.len() > 1 {
            let bad = std::mem::take(&mut ts.bad);
            ts.bad = LitVec::from(ts.rel.new_or(bad));
        }
        ts.remove_gate_init(&mut rst);
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll(true);
        if cfg.inn {
            ts = uts.internal_signals();
        }
        let predprop = cfg
            .pred_prop
            .then(|| PredProp::new(uts.clone(), cfg.local_proof.then_some(prop), cfg.inn));
        let tsctx = Box::new(ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let inf_solver = new_transys_solver(&tsctx);
        let lift = TsLift::new(TransysUnroll::new(&ts));
        let localabs = LocalAbs::new(&ts, cfg.abs_cst, cfg.abs_trans);
        Self {
            ts,
            tsctx,
            activity,
            solvers: Vec::new(),
            inf_solver,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            localabs,
            ots,
            rst,
            predprop,
            rng,
            time_limit: cfg.time_limit,
            prop,
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
        if !self.prep_prop_base() {
            info!("ic3 found a counterexample at depth 0");
            return McResult::Unsafe(0);
        }
        self.extend();
        let mut last_sec = 0;
        loop {
            let now_sec = self.statistic.time.time().as_secs();
            if let Some(limit) = self.time_limit
                && now_sec > limit.get()
            {
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
        let mut proof = self.ots.clone();
        if let Some(iv) = self.rst.init_var() {
            let piv = proof.add_init_var();
            self.rst.add_restore(iv, piv);
        }
        let mut invariants = self.inner_invariant();
        for c in self.ts.constraint.clone() {
            proof
                .rel
                .migrate(&self.ts.rel, c.var(), &mut self.rst.bvmap);
            invariants.push(LitVec::from(!c));
        }
        let mut invariants: LitVvec = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().map(|l| self.rst.restore(*l))))
            .collect();
        invariants.extend(self.rst.eq_invariant());
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel.new_and(cube));
        }
        let invariants = proof.rel.new_or(certifaiger_dnf);
        let bad = proof.rel.new_or(proof.bad);
        proof.bad = LitVec::from(proof.rel.new_or([invariants, bad]));
        McProof::Bl(BlProof { proof })
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
