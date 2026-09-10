use crate::{
    config::EngineConfig,
    gipsat::DagCnfSolver,
    ic3::{localabs::LocalAbs, mab::CtgMab, predprop::PredProp},
    transys::{Transys, certify::Restore, lift::TsLift, unroll::TransysUnroll},
};
use activity::Activity;
use clap::{ArgAction, Args, Parser};
use frame::{Frame, Frames};
use log::error;
use logicrs::{Lit, LitOrdVec, LitVec, Var};
use proofoblig::{Po, Poq};
use rand::{SeedableRng, rngs::SmallRng};
use serde::{Deserialize, Serialize};
use std::{process::exit, sync::Arc};

mod activity;
mod frame;
mod localabs;
mod mab;
mod mainloop;
mod mic;
mod predprop;
mod proofoblig;
mod propagate;
mod solver;

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
    /// Disable counterexample to generalization
    #[arg(long = "no-ctg", action = ArgAction::SetFalse)]
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
    /// Prune latch domains with a single least-seen initial-model guard per lemma
    #[arg(long = "guard-domain", default_value_t = false, conflicts_with = "inn")]
    #[serde(default)]
    pub guard_domain: bool,
    /// abstract constrains
    #[arg(long = "abs-cst", default_value_t = false)]
    pub abs_cst: bool,
    /// abstract trans
    #[arg(long = "abs-trans", default_value_t = false)]
    pub abs_trans: bool,
    /// Disable dropping over-active proof obligations
    #[arg(long = "no-drop-po", action = ArgAction::SetFalse)]
    pub drop_po: bool,
    /// Disable parent lemma guidance in MIC (CAV'23 https://doi.org/10.1007/978-3-031-37703-7_14)
    #[arg(long = "no-parent-lemma", action = ArgAction::SetFalse)]
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
    inf_solver: DagCnfSolver,
    lift: TsLift,
    frame: Frames,
    obligations: Poq,
    activity: Activity,
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

fn initial_model(solver: &DagCnfSolver, latch: &[Var]) -> Vec<bool> {
    let mut solver = solver.clone();
    solver.use_phase_saving = false;
    // Certificate generation is missing; don't care for now.
    // True forces prepare_vsids and a complete local model. Empty assumptions still
    // build the domain, but skip preparing decisions; those extra Nones are not free.
    if !solver.dcs_solve_nocst(&[Lit::constant(true)]) {
        println!("UNSAT");
        exit(20);
    }
    latch
        .iter()
        .map(|&v| solver.dcs_varsatval(v).unwrap_or(false))
        .collect()
}

impl IC3 {
    pub fn new(mut cfg: IC3Config, mut ts: Transys, ots: Transys, mut rst: Restore) -> Self {
        // validate config
        assert!(
            !cfg.inn || !cfg.guard_domain,
            "inn & guard-domain incompatible"
        );
        assert!(
            (cfg.dynamic as u8 + cfg.mab as u8 + cfg.drop_po as u8) < 2,
            // (cfg.dynamic as u8 + cfg.mab as u8 + cfg.drop_po as u8 + cfg.online_nn) < 2,
            "dynamic, mab, online-nn and drop-po are mutually exclusive"
        );

        ts.remove_gate_init(&mut rst);
        let real_bad = ts.bad.clone(); // only differs from ts.bad if local proof is on
        if cfg.local_proof < ts.bad.len() {
            cfg.pred_prop = true;
            ts.bad = LitVec::from(ts.bad[cfg.local_proof]);
        }
        if ts.bad.len() != 1 {
            error!(
                "{} bads in IC3! Wrong preprocessed model load?",
                ts.bad.len()
            );
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

        // PredProp strengthens IC3 with !bad below. LocalAbs must validate
        // witnesses against the original transition system, not that strengthening.
        let localabs_ts =
            (predprop.is_some() && (cfg.abs_cst || cfg.abs_trans)).then(|| Arc::new((*ts).clone()));

        let mut base_cex = None;
        if predprop.is_some() {
            let mut slv = ts.new_solver();
            for init in ts.inits() {
                slv.add_perma_clause(&init);
            }
            if slv.dcs_solve_nocst(&[ts.bad[0]]) {
                let mut input = LitVec::new();
                for &i in &ts.input {
                    if let Some(v) = slv.dcs_varsatval(i) {
                        input.push(Lit::new(i, v));
                    }
                }
                let mut bad = LitVec::new();
                for &lat in &ts.latch {
                    if let Some(v) = slv.dcs_varsatval(lat) {
                        bad.push(Lit::new(lat, v));
                    }
                }
                base_cex = Some(Po::new(0, LitOrdVec::new(bad), vec![input], 0, None));
            } else {
                unsafe { &mut *(Arc::as_ptr(&mut ts) as *mut Transys) }
                    .constraint
                    .extend(!&real_bad);
            }
        }

        let mut solvers = Vec::new();
        let mut inf_solver = ts.new_solver();
        let mut obligations = Poq::new();
        let frames = if let Some(po) = base_cex {
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
                solver.add_perma_clause(&!lemma.as_litvec());
                frame.push((lemma, None));
            }
            let mut init = LitVec::new();
            for l in ts.latch.iter() {
                if ts.init(*l).is_none()
                    && let Some(v) = solver.dcs_varsatval(*l)
                {
                    init.push(l.lit().not_if(!v));
                }
            }
            for i in init {
                unsafe { &mut *(Arc::as_ptr(&mut ts) as *mut Transys) }
                    .add_init(i.var(), Lit::constant(i.polarity()));
            }
            if cfg.guard_domain {
                let init = initial_model(&solver, &ts.latch);
                solver.enable_guard_domain(&ts.latch, &init);
                inf_solver.enable_guard_domain(&ts.latch, &init);
            }
            solvers.push(solver);
            let mut f = Frames::new(&ts);
            f.push(frame);
            f
        };

        Self {
            activity: Activity::new(&ts),
            solvers,
            inf_solver,
            lift: TsLift::new(TransysUnroll::new(Arc::clone(&ts))),
            obligations,
            frame: frames,
            localabs: LocalAbs::new(
                localabs_ts.unwrap_or_else(|| Arc::clone(&ts)),
                cfg.abs_cst,
                cfg.abs_trans,
            ),
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DagCnf, Engine, McResult};

    #[test]
    fn inn_abstraction_checks_initial_gate_correlations_before_refinement() {
        for (abs_cst, abs_trans) in [(true, false), (false, true), (true, true)] {
            let mut ts = Transys::new();
            let a = ts.new_var();
            let b = ts.new_var();
            let eq = ts.rel_mut().new_xnor(a.lit(), b.lit());
            let bad = ts.rel_mut().new_and([b.lit(), eq]);
            ts.add_latch(a, Some(Lit::constant(false)), Lit::constant(true));
            ts.add_latch(b, None, b.lit());
            ts.bad = LitVec::from(bad);

            // At depth 0 bad = b & !b, but propagation alone does not
            // assign bad. INN can therefore lift a frame-1 model to {bad},
            // which passes the constant-init check and used to stall CEGAR.
            let cfg = IC3Config {
                inn: true,
                abs_cst,
                abs_trans,
                time_limit: 1,
                ..IC3Config::default()
            };
            let rst = Restore::new(&ts);
            let mut ic3 = IC3::new(cfg, ts.clone_deep(), ts, rst);
            assert!(ic3.ts.is_latch(bad.var()));
            assert!(ic3.ts.cube_subsume_init(&[bad]));
            assert!(ic3.ts.init(bad.var()).is_none());

            assert!(matches!(ic3.check(), McResult::Unsafe(1)));
            let witness = ic3.witness().into_bl().unwrap();
            assert_eq!(witness.state.len(), 2);
            assert!(witness.state[0].contains(&!a.lit()));
            assert!(witness.state[0].contains(&b.lit()));
            assert!(witness.state[1].contains(&a.lit()));
            assert!(witness.state[1].contains(&b.lit()));
        }
    }

    #[test]
    fn initial_model_satisfies_constraints_and_completes_only_free_latches() {
        let mut dc = DagCnf::new();
        let a = dc.new_var();
        let b = dc.new_var();
        let free = dc.new_var();
        let either = dc.new_or([a.lit(), b.lit()]);
        let mut solver = DagCnfSolver::new(Arc::new(dc));
        solver.add_perma_clause(&[either]);

        let init = initial_model(&solver, &[a, b, free]);
        assert!(init[0] || init[1]);
        assert!(!init[2]);
    }

    #[test]
    fn guard_flag_is_opt_in_and_conflicts_only_with_inn() {
        let ordinary = EngineConfig::try_parse_from(["", "ic3"])
            .unwrap()
            .into_ic3()
            .unwrap();
        assert!(!ordinary.guard_domain);
        let inn = EngineConfig::try_parse_from(["", "ic3", "--inn"])
            .unwrap()
            .into_ic3()
            .unwrap();
        assert!(inn.inn);
        assert!(!inn.guard_domain);
        let guarded = EngineConfig::try_parse_from(["", "ic3", "--guard-domain", "--abs-cst"])
            .unwrap()
            .into_ic3()
            .unwrap();
        assert!(guarded.guard_domain);
        assert!(EngineConfig::try_parse_from(["", "ic3", "--inn", "--guard-domain"]).is_err());
    }
}
