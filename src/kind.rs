use crate::{
    BlProof, Engine, McProof, McResult, McWitness,
    cadical::CaDiCaL,
    config::{EngineConfig, EngineConfigBase, PreprocConfig},
    impl_config_deref,
    transys::{
        Transys, TransysIf, certify::Restore, nodep::NoDepTransys, preproc_serde::PreprocModel,
        unroll::TransysUnroll,
    },
};
use clap::{Args, Parser};
use log::{error, info};
use logicrs::{Lit, LitVec, LitVvec, Var, VarRange, satif::Satif};
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct KindConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// Simple path constraint
    #[arg(long = "simple-path", default_value_t = false)]
    pub simple_path: bool,

    /// Skip BMC. It is adviced to run a BMC concurrently with K-Ind;
    /// BMC finds SAT and K-Ind finds UNSAT.
    #[arg(long = "skip-bmc", default_value_t = true)]
    pub skip_bmc: bool,

    /// Local proof (internal parameter)
    #[arg(skip)]
    pub local_proof: bool,
}

impl_config_deref!(KindConfig);

impl Default for KindConfig {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "kind"]);
        cfg.into_kind().unwrap()
    }
}

pub struct Kind {
    uts: TransysUnroll<NoDepTransys>,
    solver: CaDiCaL,
    simple_path: Vec<LitVvec>,
    ots: Transys,
    rst: Restore,
    bad_prop_id: usize,
    pub skip_bmc: bool,
    pub use_simple_path: bool,
    pub end: usize,
}

impl Kind {
    pub fn new(cfg: KindConfig, mut ts: Transys) -> Self {
        // TARGET FOR LATER: each engine should have its dedicated config, not the current
        // ill-defined EngineConfigBase
        if cfg.step != 1 {
            panic!("k-induction step should be 1, got {}", cfg.step);
        }
        if cfg.start != 0 {
            panic!("k-induction start should be 0, got {}", cfg.start);
        }
        if cfg.local_proof {
            panic!("local proof KInd not supported");
        }

        let ots = ts.clone();
        if let Some(prop) = cfg.prop {
            ts.bad = LitVec::from(ts.bad[prop]);
        }
        let (model, loaded) = PreprocModel::load_or_preproc(ts, &cfg.preproc);
        let (mut ts, mut rst) = (model.ts, model.rst);
        // dumb to test twice, but needed so bad prop set correctly
        // on both load success and load failure
        if loaded && let Some(prop) = cfg.prop {
            ts.bad = LitVec::from(ts.bad[prop]);
        }

        // K-Ind specific additional preprocessing after general load_or_preproc
        ts.remove_gate_init(&mut rst);
        let mut ts = ts.remove_dep();
        // assume constraints
        // TODO: support local_proof by assuming other bad props
        for c in std::mem::take(&mut ts.constraint) {
            ts.rel.add_clause(&[c]);
        }
        if cfg.preproc.preproc {
            ts.simplify(&mut rst); // restored from master branch
        }
        // compress bads
        if cfg.prop.is_none() && ts.bad.len() > 1 {
            let bad = std::mem::take(&mut ts.bad);
            ts.bad = LitVec::from(ts.rel.new_or(bad));
        }
        let uts = TransysUnroll::new(&ts);
        Self {
            bad_prop_id: cfg.prop.unwrap_or(0),
            uts,
            skip_bmc: cfg.skip_bmc,
            end: cfg.end,
            use_simple_path: cfg.simple_path,
            solver: CaDiCaL::new(),
            simple_path: Vec::new(),
            ots,
            rst,
        }
    }
}

impl Engine for Kind {
    fn check(&mut self) -> McResult {
        // feels odd: extracting from a new TransysUnroll?
        let bad0 = self.uts.ts.bad[self.bad_prop_id];
        // load the 0th TransysUnroll, if not already (i.e. first call to `check`)
        let mut k = self.uts.num_unroll + 1;
        if k == 1 {
            self.uts.load_trans(&mut self.solver, 0, true);
        }
        // K-Ind requires a) init satisfied; b) if safe at n, model is safe at n+k also.
        // Therefore *unconditionally* check frame 0!
        let mut assump: LitVec = self.uts.ts.inits().iter().flatten().copied().collect();
        assump.push(self.uts.lit_next(bad0, 0));
        if self.solver.solve(&assump) {
            info!("K-Ind init not satisfied");
            return McResult::Unsafe(0);
        }

        while k <= self.end {
            self.uts.unroll(true);
            debug_assert_eq!(self.uts.num_unroll, k);
            if self.use_simple_path {
                let mut sp = LitVvec::new();
                for i in 0..k {
                    let mut ors = LitVec::new();
                    for l in self.uts.ts.latch() {
                        let l = l.lit();
                        let li = self.uts.lit_next(l, i);
                        let lj = self.uts.lit_next(l, k);
                        self.uts.max_var += 1;
                        let n = self.uts.max_var.lit();
                        sp.extend(LitVvec::cnf_xor(n, li, lj));
                        ors.push(n);
                    }
                    sp.push(ors);
                }
                self.simple_path.push(sp);
            }

            // old slv_trans_k == k
            self.uts.load_trans(&mut self.solver, k, true);
            if self.use_simple_path {
                for cls in self.simple_path[k - 1].iter() {
                    self.solver.add_clause(cls);
                }
            }

            // old slv_bad_k == k-1
            for b in self.uts.lits_next(&self.uts.ts.bad, k - 1) {
                self.solver.add_clause(&[!b]);
            }
            let bad = self.uts.lit_next(bad0, k);
            let res = self.solver.solve(&[bad]);
            if !res {
                info!("kind proved the property");
                return McResult::Safe;
            }

            info!("not {k}-inductive");
            if self.skip_bmc { k += 1; continue; }
            assump = self.uts.ts.inits().iter().flatten().copied().collect();
            assump.push(self.uts.lit_next(bad0, k));
            if self.solver.solve(&assump) {
                info!("bmc found a counterexample at depth {k}");
                return McResult::Unsafe(k);
            }
            k += 1;
        }
        info!("kind reached bound {}, stopping search", self.end);
        McResult::Unknown(Some(self.end))
    }

    fn proof(&mut self) -> McProof {
        if self.use_simple_path {
            //TODO: support certifaiger with simple path constraint
            error!("k-induction with simple path constraint not support certifaiger");
            panic!();
        }
        let mut ts = self.ots.clone();
        let eqi = self.rst.eq_invariant();
        let mut certifaiger_dnf = vec![];
        for cube in eqi {
            certifaiger_dnf.push(ts.rel.new_and(cube));
        }
        certifaiger_dnf.extend(ts.bad);
        let invariants = ts.rel.new_or(certifaiger_dnf);
        ts.bad = LitVec::from(invariants);
        if !ts.constraint.is_empty() {
            ts.constraint = LitVec::from([ts.rel.new_and(ts.constraint)]);
        }
        let mut proof = ts.clone();
        let ni = proof.input.len();
        let nl = proof.latch.len();
        let k = self.uts.num_unroll;
        let mut inputs = proof.input.clone();
        let mut latchs = proof.latch.clone();
        let mut next = proof.next.clone();
        let mut inits = proof.init.clone();
        let mut bads = proof.bad.clone();
        let mut constrains = proof.constraint.clone();
        for _ in 1..k {
            let offset = proof.max_var();
            let map = |x: Var| {
                if x == Var::CONST { x } else { x + offset }
            };
            proof.new_var_to(map(ts.max_var()));
            let lmap = |x: Lit| Lit::new(map(x.var()), x.polarity());
            for v in VarRange::new_inclusive(Var(1), ts.max_var()) {
                let rel: Vec<LitVec> = ts.rel[v].iter().map(|cls| cls.map(lmap)).collect();
                let mv = map(v);
                proof.rel.add_rel(mv, &rel);
            }
            for &i in ts.input.iter() {
                inputs.push(map(i));
            }
            for &l in ts.latch.iter() {
                let ml = map(l);
                latchs.push(ml);
                next.insert(ml, lmap(ts.next[&l]));
                if let Some(i) = ts.init.get(&l) {
                    inits.insert(ml, lmap(*i));
                }
            }
            bads.extend(ts.bad.map(lmap));
            for &l in ts.constraint.iter() {
                constrains.push(lmap(l));
            }
        }
        if !constrains.is_empty() {
            for i in 0..k {
                bads[i] = proof.rel.new_or([bads[i], !constrains[i]]);
            }
        }
        let sum = inputs.len() + latchs.len();
        let mut aux_latchs: Vec<Lit> = Vec::new();
        for i in 0..k {
            let aux = proof.new_var().lit();
            aux_latchs.push(aux);
            let (next, init) = if i == 0 {
                (aux, Some(Lit::constant(true)))
            } else {
                (aux_latchs[i - 1], Some(Lit::constant(false)))
            };
            proof.add_latch(aux.var(), init, next);
        }
        for i in 1..k {
            for j in 0..ni {
                proof.add_latch(inputs[j + i * ni], None, inputs[j + (i - 1) * ni].lit());
            }
            for j in 0..nl {
                proof.add_latch(latchs[j + i * nl], None, latchs[j + (i - 1) * nl].lit());
            }
        }
        for i in 0..k {
            let al = aux_latchs[i];
            let p = proof.rel.new_imply(al, !bads[i]);
            bads[i] = !p;
        }

        for i in 1..k {
            let al = aux_latchs[i];
            let al_next = aux_latchs[i - 1];
            let p = proof.rel.new_imply(al, al_next);
            bads.push(!p);
            let mut eqs = Vec::new();
            let mut init = Vec::new();
            for j in 0..nl {
                let lis1j = latchs[(i - 1) * nl + j];
                if let Some(&linit) = inits.get(&lis1j) {
                    init.push(LitVec::from([lis1j.lit(), !linit]));
                    init.push(LitVec::from([!lis1j.lit(), linit]));
                }
                eqs.push(
                    proof
                        .rel
                        .new_xnor(next[&latchs[j + i * nl]], latchs[j + (i - 1) * nl].lit()),
                );
            }
            let p = proof.rel.new_and(eqs);
            let p = proof.rel.new_imply(al, p);
            bads.push(!p);
            let init: Vec<_> = init.into_iter().map(|cls| proof.rel.new_or(cls)).collect();
            let init = proof.rel.new_and(init);
            let p = proof.rel.new_and([!al, al_next]);
            let p = proof.rel.new_imply(p, init);
            bads.push(!p);
        }
        bads.push(!aux_latchs[0]);
        proof.bad = LitVec::from(proof.rel.new_or(bads));
        assert!(proof.input.len() + proof.latch.len() == sum + k);
        McProof::Bl(BlProof { proof })
    }

    fn witness(&mut self) -> McWitness {
        let mut wit = self.uts.witness(&self.solver);
        wit = self.rst.restore_witness(&wit);
        wit.exact_state(&self.ots, true);
        wit.bad_id = self.bad_prop_id; // wit.bad_id defaults to 0
        McWitness::Bl(wit)
    }
}
