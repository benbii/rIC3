use crate::{
    Engine, McProof, McResult, McWitness,
    cadical::CaDiCaL,
    config::EngineConfig,
    transys::{Transys, certify::Restore, nodep::NoDepTransysUnroll},
};
use clap::{Args, Parser};
use log::{error, info};
use logicrs::{Lit, LitVec, LitVvec, OptionU32, Var, VarMap, VarRange, satif::Satif};
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct KindConfig {
    /// Max bound to check
    #[arg(long = "end", default_value_t = usize::MAX)]
    pub end: usize,
    /// Simple path constraint
    #[arg(long = "simple-path", default_value_t = false)]
    pub simple_path: bool,
    /// Skip BMC
    #[arg(long = "skip-bmc", default_value_t = false)]
    pub skip_bmc: bool,
    /// Local proof
    #[arg(long = "local-proof", default_value_t = usize::MAX)]
    pub local_proof: usize,
}

impl Default for KindConfig {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "kind"]);
        cfg.into_kind().unwrap()
    }
}

pub struct Kind {
    uts: NoDepTransysUnroll,
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
    pub fn new(cfg: KindConfig, mut ts: Transys, ots: Transys, mut rst: Restore) -> Self {
        if cfg.local_proof < ts.bad.len() {
            panic!("local proof KInd not supported");
        }

        ts.remove_gate_init(&mut rst);
        let mut ts = ts.remove_dep();
        // assume constraints
        // TODO: support local_proof by assuming other bad props
        for c in std::mem::take(&mut ts.constraint) {
            ts.rel.add_clause(&[c]);
        }
        ts.simplify(&mut rst); // restored from master branch
        // compress bads
        if ts.bad.len() > 1 {
            let bad = std::mem::take(&mut ts.bad);
            ts.bad = LitVec::from(ts.rel.new_or(bad));
        }
        let uts = NoDepTransysUnroll::new(&ts);
        Self {
            bad_prop_id: 0,
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
        let bad0 = self.uts.ts.bad[self.bad_prop_id];
        let mut k = self.uts.num_unroll + 1;
        // load the 0th TransysUnroll, if not already (i.e. first call to `check`)
        if k == 1 {
            self.uts.load_trans(&mut self.solver, 0, true);
        }
        let mut assump: LitVec = self.uts.ts.inits().iter().flatten().copied().collect();

        while k <= self.end {
            if !self.skip_bmc {
                assump.push(self.uts.lit_next(bad0, k - 1));
                if self.solver.solve(&assump) {
                    info!("bmc found a counterexample at depth {}", k - 1);
                    return McResult::Unsafe(k - 1);
                }
                assump.pop();
            }

            self.uts.unroll();
            debug_assert_eq!(self.uts.num_unroll, k);
            if self.use_simple_path {
                let mut sp = LitVvec::new();
                for i in 0..k {
                    let mut ors = LitVec::new();
                    let latch = self.uts.ts.latch.clone();
                    for l in latch {
                        let l = l.lit();
                        let li = self.uts.lit_next(l, i);
                        let lj = self.uts.lit_next(l, k);
                        let n = self.uts.new_var().lit();
                        sp.extend(LitVvec::cnf_xor(n, li, lj));
                        ors.push(n);
                    }
                    sp.push(ors);
                }
                self.simple_path.push(sp);
            }

            self.uts.load_trans(&mut self.solver, k, true);
            if self.use_simple_path {
                for cls in self.simple_path[k - 1].iter() {
                    self.solver.add_clause(cls);
                }
            }

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
        let mut ts = self.ots.clone_deep();
        let eqi = self.rst.eq_invariant();
        let mut certifaiger_dnf = vec![];
        for cube in eqi {
            certifaiger_dnf.push(ts.rel_mut().new_and(cube));
        }
        certifaiger_dnf.extend(std::mem::take(&mut ts.bad));
        let invariants = ts.rel_mut().new_or(certifaiger_dnf);
        ts.bad = LitVec::from(invariants);
        if !ts.constraint.is_empty() {
            let constraint = std::mem::take(&mut ts.constraint);
            ts.constraint = LitVec::from([ts.rel_mut().new_and(constraint)]);
        }
        let mut proof = ts.clone_deep();
        let ni = proof.input.len();
        let nl = proof.latch.len();
        let k = self.uts.num_unroll;
        let mut inputs = proof.input.clone();
        let mut latchs = proof.latch.clone();
        let mut next = proof.next.clone();
        let mut inits = proof.init.clone();
        let dense_lit = |map: &VarMap<OptionU32>, v: Var| -> Option<Lit> {
            let idx: usize = v.into();
            if idx >= map.len() {
                return None;
            }
            let raw = match map[v] {
                OptionU32::NONE => return None,
                raw => *raw,
            };
            Some(Lit(raw))
        };
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
                proof.rel_mut().add_rel(mv, &rel);
            }
            for &i in ts.input.iter() {
                inputs.push(map(i));
            }
            for &l in ts.latch.iter() {
                let ml = map(l);
                latchs.push(ml);
                next.reserve(ml);
                next[ml] = OptionU32::some(lmap(ts.var_next_lit(l)).into());
                if let Some(i) = ts.init(l) {
                    inits.reserve(ml);
                    inits[ml] = OptionU32::some(lmap(i).into());
                }
            }
            bads.extend(ts.bad.map(lmap));
            for &l in ts.constraint.iter() {
                constrains.push(lmap(l));
            }
        }
        if !constrains.is_empty() {
            for i in 0..k {
                bads[i] = proof.rel_mut().new_or([bads[i], !constrains[i]]);
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
            let p = proof.rel_mut().new_imply(al, !bads[i]);
            bads[i] = !p;
        }

        for i in 1..k {
            let al = aux_latchs[i];
            let al_next = aux_latchs[i - 1];
            let p = proof.rel_mut().new_imply(al, al_next);
            bads.push(!p);
            let mut eqs = Vec::new();
            let mut init = Vec::new();
            for j in 0..nl {
                let lis1j = latchs[(i - 1) * nl + j];
                if let Some(linit) = dense_lit(&inits, lis1j) {
                    init.push(LitVec::from([lis1j.lit(), !linit]));
                    init.push(LitVec::from([!lis1j.lit(), linit]));
                }
                eqs.push(proof.rel_mut().new_xnor(
                    dense_lit(&next, latchs[j + i * nl]).unwrap(),
                    latchs[j + (i - 1) * nl].lit(),
                ));
            }
            let p = proof.rel_mut().new_and(eqs);
            let p = proof.rel_mut().new_imply(al, p);
            bads.push(!p);
            let init: Vec<_> = init
                .into_iter()
                .map(|cls| proof.rel_mut().new_or(cls))
                .collect();
            let init = proof.rel_mut().new_and(init);
            let p = proof.rel_mut().new_and([!al, al_next]);
            let p = proof.rel_mut().new_imply(p, init);
            bads.push(!p);
        }
        bads.push(!aux_latchs[0]);
        proof.bad = LitVec::from(proof.rel_mut().new_or(bads));
        assert!(proof.input.len() + proof.latch.len() == sum + k);
        McProof::Bl(proof)
    }

    fn witness(&mut self) -> McWitness {
        let mut wit = self.uts.witness(&self.solver);
        wit = self.rst.restore_witness(&wit);
        wit.exact_state(&self.ots, true);
        wit.bad_id = self.bad_prop_id; // wit.bad_id defaults to 0
        McWitness::Bl(wit)
    }
}
