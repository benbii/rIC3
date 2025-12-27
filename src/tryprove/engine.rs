use crate::cli::{vcd::wlwitness_vcd, Ric3Config, Ric3Proj, Yosys};
use btor::Btor;
use cadical::CaDiCaL;
use giputils::{hash::GHashMap, logger::with_log_level};
use log::{info, LevelFilter};
use logicrs::{fol::Term, satif::Satif, LitVec, VarSymbols};
use rIC3::{
    frontend::{btor::BtorFrontend, Frontend},
    ic3::{IC3Config, IC3},
    portfolio::{LightPortfolio, LightPortfolioConfig, Portfolio, PortfolioConfig},
    transys::{certify::Restore, unroll::TransysUnroll, Transys},
    wltransys::{bitblast::BitblastMap, certify::WlWitness, WlTransys},
    Engine, McResult, McWitness,
};
use std::{
    fs::{self, File},
    io::BufWriter,
    path::Path,
    thread::spawn,
};

use super::state::LastRunState;

/// Status of an assertion after verification
#[derive(Clone, Debug)]
pub enum AssertionStatus {
    /// Verified correct
    Proved,
    /// First time seeing hard-to-disprove transitions
    HardTransFound,
    /// Previous hard transitions still present (helper didn't work)
    NotBlocked,
    /// Old transitions blocked, but new ones appeared
    BlockedNewFound,
    /// Real counterexample found
    Triggered,
}

pub struct PropertyResult {
    pub id: usize,
    pub name: String,
    pub status: AssertionStatus,
    /// Serialized witness for state storage (None if proved)
    pub cti_witness: Option<String>,
}

pub struct TryProveResult {
    pub properties: Vec<PropertyResult>,
    /// (vcd_index, property_name, property_id) - only for non-proved properties
    pub vcds: Vec<(usize, String, usize)>,
    /// Path to counterexample VCD if one was found
    pub cex_vcd: Option<std::path::PathBuf>,
}

struct TryProveEngine {
    rcfg: Ric3Config,
    rp: Ric3Proj,
    #[allow(unused)]
    wts: WlTransys,
    wsym: GHashMap<Term, String>,
    ts: Transys,
    bb_map: BitblastMap,
    ts_rst: Restore,
    btorfe: BtorFrontend,
    slv: CaDiCaL,
    uts: TransysUnroll<Transys>,
    prop_name: Vec<Option<String>>,
    res: Vec<bool>,
}

impl TryProveEngine {
    fn new(rcfg: Ric3Config, rp: Ric3Proj, mut btorfe: BtorFrontend) -> anyhow::Result<Self> {
        let (mut wts, symbol) = btorfe.wts();
        wts.coi_refine();
        let mut slv = CaDiCaL::new();
        let (ts, bb_rst) = wts.bitblast_to_ts();
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll_to(4);
        for k in 0..=uts.num_unroll {
            uts.load_trans(&mut slv, k, true);
        }
        for k in 0..uts.num_unroll {
            for b in uts.ts.bad.iter() {
                slv.add_clause(&[!uts.lit_next(*b, k)]);
            }
        }
        let prop_name: Vec<_> = wts.bad.iter().map(|t| symbol.get(t).cloned()).collect();
        Ok(Self {
            rcfg,
            rp,
            btorfe,
            slv,
            wts,
            ts,
            bb_map: bb_rst,
            uts,
            prop_name,
            res: Vec::new(),
        })
    }

    fn get_prop_name(&self, id: usize) -> String {
        self.prop_name[id]
            .clone()
            .unwrap_or_else(|| format!("p{}", id))
    }

    fn check_inductive(&mut self) -> bool {
        let mut res = vec![false; self.ts.bad.len()];
        let mut cfg = IC3Config::default();
        cfg.pred_prop = true;
        cfg.local_proof = true;
        cfg.preproc.scorr = false;
        cfg.preproc.frts = false;
        let lpcfg = LightPortfolioConfig {
            time_limit: Some(20),
        };
        with_log_level(LevelFilter::Warn, || {
            let mut joins = Vec::new();
            for i in 0..self.ts.bad.len() {
                let ts = self.ts.clone();
                let mut cfg = cfg.clone();
                let lpcfg = lpcfg.clone();
                cfg.prop = Some(i);
                joins.push(spawn(move || {
                    let w0 = IC3::new(cfg.clone(), ts.clone(), VarSymbols::default());
                    cfg.inn = true;
                    let w1 = IC3::new(cfg, ts, VarSymbols::default());
                    let mut lp = LightPortfolio::new(lpcfg.clone(), Vec::new());
                    lp.add_engine(w0);
                    lp.add_engine(w1);
                    lp.check()
                }));
            }
            for (j, r) in joins.into_iter().zip(res.iter_mut()) {
                *r = matches!(j.join().unwrap(), McResult::Safe);
            }
        });
        for (id, r) in res.iter().enumerate() {
            if *r {
                info!("IC3 proved p{id} is inductive");
            }
        }
        for (r, b) in res.iter_mut().zip(self.uts.ts.bad.iter()) {
            if *r {
                continue;
            }
            let bad = self.uts.lit_next(*b, self.uts.num_unroll);
            *r = !self.slv.solve(&[bad]);
        }
        self.res = res;
        self.res.iter().all(|l| *l)
    }

    fn check_safety(&mut self) -> anyhow::Result<Option<(usize, String)>> {
        info!("Checking safety for all properties.");
        let mut cfg = PortfolioConfig::default();
        cfg.config = Some("cill".to_string());
        cfg.time_limit = Some(10);
        let cert_file = self.rp.path("tmp/dut.cert");
        let mut engine =
            Portfolio::new(self.rp.path("dut/dut.btor"), Some(cert_file.clone()), cfg);
        let res = with_log_level(LevelFilter::Warn, || engine.check());

        match res {
            McResult::Safe => {
                info!("All properties are SAFE.");
                Ok(None)
            }
            McResult::Unsafe(_) => {
                let bid = self
                    .btorfe
                    .deserialize_wl_unsafe_certificate(fs::read_to_string(&cert_file)?)
                    .bad_id;
                let name = self.get_prop_name(bid);
                Ok(Some((bid, name)))
            }
            McResult::Unknown(_) => {
                info!("Portfolio engine returned unknown, continuing with induction check.");
                Ok(None)
            }
        }
    }

    fn get_cti(&mut self, id: usize) -> WlWitness {
        let b = self.uts.lit_next(self.uts.ts.bad[id], self.uts.num_unroll);
        assert!(self.slv.solve(&[b]));
        let mut wit = self.uts.witness(&self.slv);
        wit.bad_id = id;
        self.bb_map.restore_witness(&wit)
    }

    fn serialize_witness(&self, witness: &WlWitness) -> String {
        let cert = self
            .btorfe
            .unsafe_certificate(McWitness::Wl(witness.clone()));
        format!("{}", cert)
    }

    /// Check if an old CTI is blocked by current model (helper assertions worked)
    fn check_cti_blocked(&mut self, old_cti_str: &str, prop_id: usize) -> bool {
        // Deserialize old CTI
        let cti = self
            .btorfe
            .deserialize_wl_unsafe_certificate(old_cti_str.to_string());

        // Bitblast to current model
        let cti = self.bb_map.bitblast_witness(&cti);

        // Build assumptions: bad state + all CTI values
        let mut assume = vec![self
            .uts
            .lit_next(self.uts.ts.bad[prop_id], self.uts.num_unroll)];

        for k in 0..=self.uts.num_unroll {
            assume.extend(
                self.uts
                    .lits_next(cti.input[k].iter().chain(cti.state[k].iter()), k),
            );
        }

        // If UNSAT, CTI is blocked
        !self.slv.solve(&assume)
    }

    fn save_cti_to(&mut self, witness: &WlWitness, vcd_path: &Path) -> anyhow::Result<()> {
        let tmp_wit = self.rp.path("tmp/witness.wit");
        let cert = self
            .btorfe
            .unsafe_certificate(McWitness::Wl(witness.clone()));
        fs::write(&tmp_wit, format!("{}", cert))?;
        Yosys::btor_wit_to_vcd(
            self.rp.path("dut"),
            &tmp_wit,
            vcd_path,
            false,
            self.rcfg.trace.as_ref(),
        )?;
        Ok(())
    }

    fn save_cex_to(&mut self, cert_file: &Path, vcd_path: &Path) -> anyhow::Result<()> {
        Yosys::btor_wit_to_vcd(
            self.rp.path("dut"),
            cert_file,
            vcd_path,
            true,
            self.rcfg.trace.as_ref(),
        )?;
        Ok(())
    }

    fn get_non_inductive_ids(&self) -> Vec<usize> {
        self.res
            .iter()
            .enumerate()
            .filter_map(|(id, &proved)| if !proved { Some(id) } else { None })
            .collect()
    }
}

pub fn run_verification(
    rcfg: Ric3Config,
    rp: &Ric3Proj,
    hard_trans_dir: &Path,
    cex_path: &Path,
    last_state: Option<&LastRunState>,
) -> anyhow::Result<(TryProveResult, LastRunState)> {
    let btor = Btor::from_file(rp.path("dut/dut.btor"));
    let btorfe = BtorFrontend::new(btor);
    let mut engine = TryProveEngine::new(rcfg, rp.clone(), btorfe)?;

    // Phase 1: Safety check (look for real counterexamples)
    if let Some((bad_id, prop_name)) = engine.check_safety()? {
        // CEX found - generate VCD and return
        // Preserve last_state so user can still compare after fixing the bad helper
        engine.save_cex_to(&rp.path("tmp/dut.cert"), cex_path)?;
        let preserved_state = last_state.cloned().unwrap_or_default();
        return Ok((
            TryProveResult {
                properties: vec![PropertyResult {
                    id: bad_id,
                    name: prop_name,
                    status: AssertionStatus::Triggered,
                    cti_witness: None,
                }],
                vcds: vec![],
                cex_vcd: Some(cex_path.to_path_buf()),
            },
            preserved_state,
        ));
    }

    // Phase 2: Induction check
    info!("Checking inductiveness of all properties.");
    if engine.check_inductive() {
        // All proved
        let properties: Vec<_> = (0..engine.res.len())
            .map(|id| PropertyResult {
                id,
                name: engine.get_prop_name(id),
                status: AssertionStatus::Proved,
                cti_witness: None,
            })
            .collect();
        return Ok((
            TryProveResult {
                properties,
                vcds: vec![],
                cex_vcd: None,
            },
            LastRunState::default(),
        ));
    }

    // Phase 3: Generate VCDs for non-inductive properties with comparison
    let mut new_state = LastRunState::default();
    let non_inductive = engine.get_non_inductive_ids();
    let mut properties = Vec::new();
    let mut vcds = Vec::new();

    // First, add all proved properties
    for (id, &proved) in engine.res.iter().enumerate() {
        if proved {
            properties.push(PropertyResult {
                id,
                name: engine.get_prop_name(id),
                status: AssertionStatus::Proved,
                cti_witness: None,
            });
        }
    }

    // Process non-inductive properties
    for (idx, &prop_id) in non_inductive.iter().enumerate() {
        let prop_name = engine.get_prop_name(prop_id);
        let witness = engine.get_cti(prop_id);
        let serialized = engine.serialize_witness(&witness);

        // Compare with previous run
        let status = if let Some(old_cti) = last_state.and_then(|s| s.ctis.get(&prop_name)) {
            if engine.check_cti_blocked(old_cti, prop_id) {
                AssertionStatus::BlockedNewFound // Old blocked, new found
            } else {
                AssertionStatus::NotBlocked // Helper didn't work
            }
        } else {
            AssertionStatus::HardTransFound // First time
        };

        // Store for next run
        new_state.ctis.insert(prop_name.clone(), serialized.clone());

        // Generate VCD: hard_trans/0.vcd, hard_trans/1.vcd, ...
        let vcd_path = hard_trans_dir.join(format!("{}.vcd", idx));
        engine.save_cti_to(&witness, &vcd_path)?;
        vcds.push((idx, prop_name.clone(), prop_id));

        properties.push(PropertyResult {
            id: prop_id,
            name: prop_name,
            status,
            cti_witness: Some(serialized),
        });
    }

    // Sort properties by id for consistent output
    properties.sort_by_key(|p| p.id);

    Ok((
        TryProveResult {
            properties,
            vcds,
            cex_vcd: None,
        },
        new_state,
    ))
}
