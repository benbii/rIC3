use super::Frontend;
use crate::RseedMap as HashMap;
use crate::{
    McProof, McWitness,
    aig::{Aig, AigEdge},
    transys::Transys,
};
use log::{debug, error, warn};
use logicrs::{Lit, LitVec, Var, VarRange, VarVMap};
use std::{path::Path, process::Command, sync::Arc};

impl From<&Transys> for Aig {
    fn from(ts: &Transys) -> Self {
        let mut aig = Aig::new();
        let mut map = HashMap::default();
        map.insert(Var::CONST, AigEdge::from_lit(Var::CONST.lit()));
        for i in ts.input.iter() {
            let t = aig.new_input();
            map.insert(*i, AigEdge::new(t, false));
        }
        for &f in ts.latch.iter() {
            let t = aig.new_leaf_node();
            map.insert(f, AigEdge::new(t, false));
        }
        for v in VarRange::new_inclusive(Var(1), ts.rel.max_var()) {
            let rel = ts.rel.clauses_of_var(v);
            if rel.is_empty() {
                continue;
            }
            assert!(!map.contains_key(&v));
            let mut r = Vec::new();
            for rel in rel {
                let last = *rel.last().unwrap();
                assert!(last.var() == v);
                if last.polarity() {
                    let mut rel = !LitVec::from(rel);
                    rel.pop();
                    r.push(aig.trivial_new_ands_node(
                        rel.iter().map(|l| map[&l.var()].not_if(!l.polarity())),
                    ));
                }
            }
            let n = aig.trivial_new_ors_node(r);
            map.insert(v, n);
        }
        let map_lit = |l: Lit| map[&l.var()].not_if(!l.polarity());
        for l in ts.latch.iter() {
            let next = map_lit(ts.var_next_lit(*l));
            let init = ts.init(*l).map(map_lit);
            aig.add_latch(map[l].node_id(), next, init);
        }
        for &b in ts.bad.iter() {
            aig.bads.push(map_lit(b));
        }
        for c in ts.constraint() {
            aig.constraints.push(map_lit(c));
        }
        if !ts.justice.is_empty() {
            aig.justice = vec![ts.justice.iter().map(|&j| map_lit(j)).collect()];
        }
        aig
    }
}

impl Transys {
    pub fn from_aig(aig: &Aig, compact: bool) -> Transys {
        let input: Vec<Var> = aig.inputs.iter().map(|x| Var::new(*x)).collect();
        let bad = aig.bads.iter().map(|c| c.to_lit()).collect();
        let constraint: LitVec = aig.constraints.iter().map(|c| c.to_lit()).collect();
        let mut justice: LitVec = aig
            .justice
            .first()
            .map(|j| j.iter().map(|e| e.to_lit()).collect())
            .unwrap_or_default();
        justice.extend(aig.fairness.iter().map(|f| f.to_lit()));
        let rel = aig.cnf(compact);
        let mut ts = Transys {
            input,
            bad,
            constraint,
            justice,
            rel: Arc::new(rel),
            ..Default::default()
        };
        for l in aig.latchs.iter() {
            let lv = Var::from(l.input);
            ts.add_latch(lv, l.init.map(|i| i.to_lit()), l.next.to_lit());
        }
        ts
    }
}

fn aig_preprocess(aig: &Aig) -> (Aig, VarVMap) {
    let (mut aig, restore) = aig.coi_refine();
    aig.constraints.retain(|e| !e.is_constant(true));
    (aig, restore)
}

fn normalize_aig(mut aig: Aig, report: bool) -> Aig {
    if !aig.outputs.is_empty() {
        if aig.bads.is_empty() {
            aig.bads = std::mem::take(&mut aig.outputs);
            if report {
                warn!(
                    "property not found, moved {} outputs to bad properties",
                    aig.bads.len()
                );
            }
        } else {
            if report {
                warn!("outputs in aiger are ignored");
            }
            aig.outputs.clear();
        }
    } else if aig.bads.is_empty() {
        if report {
            warn!("empty property in aiger");
        }
        aig.bads.push(AigEdge::constant(false));
    }
    if !aig.bads.is_empty() {
        if !aig.justice.is_empty() {
            if report {
                error!("both safety and liveness found; certificate may be messed up");
            }
        } else if !aig.fairness.is_empty() {
            if report {
                warn!("fairness constraints are ignored when solving safety property");
            }
            aig.fairness.clear();
        }
    }
    aig
}

fn certificate_aig(model: &Path) -> Aig {
    normalize_aig(Aig::from_file(model), false)
}

pub struct AigFrontend {
    ts: Option<Transys>,
}

impl AigFrontend {
    pub fn new(oaig: Aig) -> Self {
        let oaig = normalize_aig(oaig, true);
        let (aig, _) = aig_preprocess(&oaig);
        let ts = Transys::from_aig(&aig, true);
        Self { ts: Some(ts) }
    }
}

impl Frontend for AigFrontend {
    fn ts(&mut self) -> Transys {
        self.ts.take().expect("bit-level transys already moved")
    }

    fn safe_certificate(&mut self, model: &Path, proof: McProof) -> String {
        let aig = certificate_aig(model);
        let (_, rst) = aig_preprocess(&aig);
        let proof = proof.into_bl().unwrap();
        if !aig.justice.is_empty() || !aig.fairness.is_empty() {
            error!("certifying safe liveness unsupported");
        }
        let mut certifaiger = Aig::from(&proof);
        certifaiger = certifaiger.reencode();
        certifaiger.symbols.clear();
        for (i, v) in proof.input().enumerate() {
            if let Some(r) = rst.get(&v) {
                certifaiger.set_symbol(certifaiger.inputs[i], &format!("= {}", (**r) * 2));
            }
        }
        for (i, v) in proof.latch().enumerate() {
            if let Some(r) = rst.get(&v) {
                certifaiger.set_symbol(certifaiger.latchs[i].input, &format!("= {}", (**r) * 2));
            }
        }
        certifaiger.to_string()
    }

    fn unsafe_certificate(&mut self, model: &Path, witness: McWitness) -> String {
        let aig = certificate_aig(model);
        let ots = Transys::from_aig(&aig, true);
        let (_, rst) = aig_preprocess(&aig);
        let witness = witness.into_bl().unwrap();
        let mut wit = witness.filter_map_var(|v: Var| rst.get(&v).copied());
        let mut res = vec!["1".to_string()];
        if ots.justice.is_empty() {
            res.push(format!("b{}", witness.bad_id));
        } else {
            res.push("j0".to_string());
        }
        wit.exact_init_state(&ots);
        let mut line = String::new();
        for l in wit.state[0].iter() {
            line.push(if l.polarity() { '1' } else { '0' })
        }
        res.push(line);
        let mut line = String::new();
        for i in wit.input[0].iter() {
            line.push(if i.polarity() { '1' } else { '0' })
        }
        res.push(line);
        for c in wit.input[1..].iter() {
            let map: HashMap<Var, bool> =
                HashMap::from_iter(c.iter().map(|l| (l.var(), l.polarity())));
            let mut line = String::new();
            for l in &ots.input {
                let r = map.get(l).copied().unwrap_or(true);
                line.push(if r { '1' } else { '0' });
            }
            res.push(line);
        }
        res.push(".\n".to_string());
        res.join("\n")
    }

    fn certify(&mut self, model: &Path, cert: &Path) -> bool {
        let output = Command::new("docker")
            .args([
                "run",
                "--rm",
                "--pull=never",
                "-v",
                &format!("{}:{}", model.display(), model.display()),
                "-v",
                &format!("{}:{}", cert.display(), cert.display()),
                "ghcr.io/gipsyh/certifaiger",
            ])
            .arg(model)
            .arg(cert)
            .output()
            .unwrap();
        if !output.status.success() {
            debug!("{}", String::from_utf8_lossy(&output.stdout));
            debug!("{}", String::from_utf8_lossy(&output.stderr));
            if output.status.code() != Some(1) {
                error!(
                    "certifaiger not avaliable, please `docker pull ghcr.io/gipsyh/certifaiger:latest`"
                );
            }
        }
        output.status.success()
    }
}
