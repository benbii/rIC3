use super::Frontend;
use crate::{
    McProof, McWitness,
    btor::Btor,
    fol::Sort,
    transys::{self as bl},
    wltransys::{WlTransys, bitblast::BitblastMap, certify::WlRestore},
};
use crate::{RseedMap as HashMap, RseedSet as HashSet};
use log::{debug, error, warn};
use logicrs::fol::{Term, TermValue};
use std::{mem::take, path::Path, process::Command};

/* impl WlTransys {
    fn from_btor(btor: &Btor) -> Self {
        debug_assert!(
            btor.input
                .iter()
                .all(|i| !btor.init.contains_key(i) && !btor.next.contains_key(i))
        );
        // (
            Self {
                input: btor.input.clone(),
                latch: btor.latch.clone(),
                init: btor.init.clone(),
                next: btor.next.clone(),
                bad: btor.bad.clone(),
                constraint: btor.constraint.clone(),
                // justice: Default::default(),
            }
        //     ,WlTsSymbol {
        //         signal: btor.symbols.clone(),
        //         prop: btor.prop_label.clone(),
        //     },
        // )
    }
}

impl From<WlTransys> for Btor {
    fn from(wl: WlTransys) -> Btor {
        Btor {
            input: wl.input,
            latch: wl.latch,
            init: wl.init,
            next: wl.next,
            bad: wl.bad,
            constraint: wl.constraint,
        }
    }
} */

pub struct BtorFrontend {
    owts: WlTransys,
    wts: Option<WlTransys>,
    rst: WlRestore,
    bbmap: Option<BitblastMap>,
}

impl BtorFrontend {
    pub fn new(mut owts: Btor) -> Self {
        if owts.bad.is_empty() {
            warn!("empty property in btor");
            owts.bad.push(Term::bool_const(false));
        }
        let mut wts = owts.clone();
        let mut rst: WlRestore = None;

        for l in take(&mut wts.latch) {
            if wts.next.contains_key(&l) {
                wts.latch.push(l.clone());
                continue;
            }
            if let Some(init) = wts.init.get(&l).cloned() {
                if rst.is_none() {
                    let iv = Term::new_var(Sort::bool());
                    wts.add_latch(
                        iv.clone(),
                        Some(Term::bool_const(true)),
                        Term::bool_const(false),
                    );
                    rst = Some(iv);
                }
                let iv = rst.as_ref().unwrap();
                wts.constraint.push(iv.imply(l.teq(&init)));
            }
            wts.init.remove(&l);
            wts.input.push(l);
        }
        Self {
            owts,
            wts: Some(wts),
            rst,
            bbmap: None,
        }
    }
}

/* impl BtorFrontend {
    pub fn deserialize_wl_unsafe_certificate(&self, content: String) -> WlWitness {
        let mut lines = content.lines();
        let first = lines.next().unwrap();
        assert_eq!(first, "sat");
        let second = lines.next().unwrap();
        assert!(second.starts_with('b'));
        let bad_id = second[1..].parse::<usize>().unwrap();
        let mut witness = WlWitness::new();
        witness.bad_id = bad_id;
        let mut current_frame = 0;
        let mut is_state = false;

        for line in lines {
            if line == "." {
                break;
            }
            if let Some(stripped) = line.strip_prefix('#') {
                let k = stripped.parse::<usize>().unwrap();
                if k >= witness.len() {
                    witness.resize(k + 1);
                }
                current_frame = k;
                is_state = true;
                continue;
            }
            if let Some(stripped) = line.strip_prefix('@') {
                let k = stripped.parse::<usize>().unwrap();
                if k >= witness.len() {
                    witness.resize(k + 1);
                }
                current_frame = k;
                is_state = false;
                continue;
            }
            let parts: Vec<&str> = line.split_whitespace().collect();
            assert!(parts.len() == 2);
            let id = parts[0].parse::<usize>().unwrap();
            let val = LboolVec::from(parts[1]);
            if is_state {
                let term = self.owts.latch[id].clone();
                let tv = TermValue::new(term, fol::Value::Bv(val));
                witness.state[current_frame].push(tv);
            } else {
                let term = self.owts.input[id].clone();
                let bv = BvTermValue::new(term, val);
                witness.input[current_frame].push(bv);
            }
        }
        for k in 0..witness.len() {
            for s in take(&mut witness.state[k]) {
                if self.no_next.contains(s.t()) {
                    witness.input[k].push(s.into_bv());
                } else {
                    witness.state[k].push(s);
                }
            }
        }
        witness
    }
} */

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> bl::Transys {
        let mut wts = self
            .wts
            .as_ref()
            .expect("word-level transys already moved")
            .clone();
        wts.simplify();
        wts.coi_refine();
        // let btor = Btor::from(&wts);
        // btor.to_file("simp.btor");
        let (ts, bbmap) = wts.bitblast_to_ts();
        self.bbmap = Some(bbmap);
        ts
    }

    fn wts(&mut self) -> WlTransys {
        self.wts.take().expect("word-level transys already moved")
    }

    fn certify(&mut self, model: &Path, cert: &Path) -> bool {
        let model = model.to_path_buf().canonicalize().unwrap();
        let cert = cert.to_path_buf().canonicalize().unwrap();
        let output = Command::new("docker")
            .args([
                "run",
                "--rm",
                "--pull=never",
                "-v",
                &format!("{}:{}", model.display(), model.display()),
                "-v",
                &format!("{}:{}", cert.display(), cert.display()),
                "ghcr.io/gipsyh/cerbtora:latest",
            ])
            .arg(model)
            .arg(cert)
            .output()
            .unwrap();
        if output.status.success() {
            true
        } else {
            debug!("{}", String::from_utf8_lossy(&output.stdout));
            debug!("{}", String::from_utf8_lossy(&output.stderr));
            if output.status.code() != Some(1) {
                error!("cerbtora unavailable; run `docker pull ghcr.io/gipsyh/cerbtora:latest`");
            }
            false
        }
    }

    fn safe_certificate(&mut self, _model: &Path, proof: McProof) -> String {
        let proof = match proof {
            McProof::Bl(bl_proof) => self.bbmap.as_ref().unwrap().restore_proof(
                self.wts.as_ref().expect("word-level transys already moved"),
                &bl_proof,
            ),
            McProof::Wl(wl_proof) => wl_proof,
        };
        let original: HashSet<Term> = self
            .owts
            .input
            .iter()
            .chain(self.owts.latch.iter())
            .cloned()
            .collect();
        let mut wts = self.owts.clone();
        for l in proof.input.iter() {
            if !original.contains(l) {
                wts.input.push(l.clone());
            }
        }
        for l in proof.latch.iter() {
            if !original.contains(l) {
                wts.add_latch(l.clone(), proof.init(l), proof.next(l));
            }
        }
        wts.bad = proof.bad;
        Btor::from(wts).to_string()
    }

    fn unsafe_certificate(&mut self, _model: &Path, witness: crate::McWitness) -> String {
        let mut idmap = HashMap::default();
        for (id, i) in self.owts.input.iter().enumerate() {
            idmap.insert(i.clone(), id);
        }
        for (id, l) in self.owts.latch.iter().enumerate() {
            idmap.insert(l.clone(), id);
        }
        let no_next: HashSet<Term> = self
            .owts
            .latch
            .iter()
            .filter(|l| !self.owts.next.contains_key(*l))
            .cloned()
            .collect();
        let mut witness = match witness {
            McWitness::Bl(bl_witness) => self.bbmap.as_ref().unwrap().restore_witness(&bl_witness),
            McWitness::Wl(wl_witness) => wl_witness,
        };

        let mut res = vec!["sat".to_string(), format!("b{}", witness.bad_id)];
        for i in 0..witness.len() {
            if let Some(iv) = &self.rst {
                witness.state[i].retain(|tv| tv.t() != iv);
            }
            let input = take(&mut witness.input[i]);
            for lv in input {
                if no_next.contains(lv.t()) {
                    witness.state[i].push(TermValue::from(lv));
                } else {
                    witness.input[i].push(lv);
                }
            }
        }
        for (k, (input, state)) in witness.input.iter().zip(witness.state.iter()).enumerate() {
            res.push(format!("#{k}"));
            let mut idw = Vec::new();
            for tv in state {
                let id = idmap[tv.t()];
                let bv = tv.into_bv();
                idw.push((id, format!("{id} {:b}", bv.v())));
            }
            idw.sort();
            res.extend(idw.into_iter().map(|(_, v)| v));
            res.push(format!("@{k}"));
            let mut idw = Vec::new();
            for tv in input {
                let id = idmap[tv.t()];
                idw.push((id, format!("{id} {:b}", tv.v())));
            }
            idw.sort();
            res.extend(idw.into_iter().map(|(_, v)| v));
        }
        res.push(".\n".to_string());
        res.join("\n")
    }
}
