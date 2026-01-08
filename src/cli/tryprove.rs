//! Stateless proof attempt command - LLM/agent friendly alternative to `cill`.
//!
//! Unlike `cill` which has sub-subcommands and tracks state, `tryprove` is a single
//! command that processes all assertions at once and reports status for each.

use super::{
    Ric3Config,
    cache::Ric3Proj,
    cill::{CIll, refresh_cti_for_prop},
    yosys::Yosys,
};
use crate::logger_init;
use btor::Btor;
use giputils::file::{create_dir_if_not_exists, recreate_dir};
use log::info;
use rIC3::{McResult, frontend::btor::BtorFrontend};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    env, fs,
    path::PathBuf,
};

/// Persistent state for tryprove - stores CTIs for all properties
#[derive(Serialize, Deserialize, Default, Debug)]
struct TryProveState {
    /// Map from property name to serialized CTI witness string
    ctis: HashMap<String, String>,
    /// Properties that were proved in the previous run
    #[serde(default)]
    proved: HashSet<String>,
}

/// Result status for each property
#[derive(Debug, Clone)]
pub enum PropStatus {
    /// Property was already proved (no previous CTI)
    Proved,
    /// Property was not inductive before, now it is (helper worked!)
    ProvedAfterHelper,
    /// Not inductive, first time seeing this property fail
    NewCti { vcd: PathBuf },
    /// Not inductive, previous CTI NOT blocked (same vulnerability)
    CtiNotBlocked { vcd: PathBuf },
    /// Not inductive, previous CTI blocked but new one appeared
    CtiBlockedNewAppeared { vcd: PathBuf },
    /// Was proved before, but now fails again (helper removed/weakened)
    Regressed { vcd: PathBuf },
}

/// Result for a single property
#[derive(Debug)]
struct PropResult {
    name: String,
    status: PropStatus,
}

pub fn run(path: PathBuf) -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();

    // 1. Resolve paths
    let dut_path = if path.is_absolute() {
        path
    } else {
        env::current_dir()?.join(&path)
    };
    let dut_path = dut_path.canonicalize()?;

    let dut_name = dut_path
        .file_name()
        .ok_or_else(|| anyhow::anyhow!("Invalid DUT path"))?
        .to_string_lossy()
        .to_string();

    // Cache in sibling directory
    let proj_path = dut_path
        .parent()
        .ok_or_else(|| anyhow::anyhow!("DUT path has no parent"))?
        .join(format!("{}_ric3proj", dut_name));

    let vcd_dir = dut_path.join("hard_trans");
    let cex_vcd_path = dut_path.join("counterexample.vcd");
    // Clean up CEX from previous runs to avoid stale files
    let _ = fs::remove_file(&cex_vcd_path);

    // 2. Read config (need to cd for relative paths in ric3.toml)
    let orig_dir = env::current_dir()?;
    env::set_current_dir(&dut_path)?;
    let rcfg = Ric3Config::from_file("ric3.toml")?;
    // Convert source paths to absolute (while CWD is dut_path) for use after we restore CWD
    let src_abs: Vec<PathBuf> = rcfg
        .dut
        .src()
        .into_iter()
        .map(|p| if p.is_absolute() { p } else { dut_path.join(p) })
        .collect();

    // 3. Load previous state
    let state_file = proj_path.join("tryprove_state.ron");
    let mut prev_state = if state_file.exists() {
        ron::from_str(&fs::read_to_string(&state_file)?)?
    } else {
        TryProveState::default()
    };

    // 4. Initialize project
    let rp = Ric3Proj::with_path(proj_path.clone())?;
    recreate_dir(rp.path("tmp"))?;

    // 5. Generate DUT (but don't commit yet if it changed - need to check safety first)
    let dut_changed = match rp.check_cached_dut(&src_abs)? {
        Some(false) => {
            // DUT changed - generate new BTOR in tmp/dut first
            Yosys::generate_btor(&rcfg, rp.path("tmp/dut"))?;
            true
        }
        None => {
            // First run - generate directly to dut/
            Yosys::generate_btor(&rcfg, rp.path("dut"))?;
            rp.cache_dut(&src_abs)?;
            false
        }
        Some(true) => false,
    };
    env::set_current_dir(&orig_dir)?;

    // 6. Check safety BEFORE committing DUT change
    // Use tmp/dut if DUT changed, otherwise use dut/
    let dut_dir = if dut_changed {
        rp.path("tmp/dut")
    } else {
        rp.path("dut")
    };
    let btor = Btor::from_file(dut_dir.join("dut.btor"));
    let btorfe = BtorFrontend::new(btor);
    let mut cill = CIll::new(rcfg.clone(), rp.clone(), btorfe)?;

    match cill.check_safety()? {
        McResult::Safe => {
            // Commit the DUT change now that safety passed
            if dut_changed {
                if rp.path("dut").exists() {
                    fs::remove_dir_all(rp.path("dut"))?;
                }
                fs::rename(rp.path("tmp/dut"), rp.path("dut"))?;
                rp.cache_dut(&src_abs)?;
            }
            println!("Congratulations! All assertions are proved safe.");
            return Ok(());
        }
        McResult::Unsafe(_) => {
            // Safety failed - DO NOT commit the DUT change
            // This way next run will regenerate and CTIs stay valid against old model
            let cex_vcd_src = rp.path("cill/cex.vcd");
            if cex_vcd_src.exists() {
                fs::copy(&cex_vcd_src, &cex_vcd_path)?;
            }
            println!("A helper assertion is cutting off reachable states.");
            println!("Counterexample VCD: {}", cex_vcd_path.display());
            let _ = fs::remove_dir_all(&vcd_dir);
            return Ok(());
        }
        McResult::Unknown(_) => {
            info!("Safety check inconclusive, continuing to inductiveness check.");
        }
    }

    // 7. Safety passed/unknown - now commit DUT change and refresh CTIs
    if dut_changed {
        // Refresh all stored CTIs using the new helper
        if rp.path("dut").exists() {
            let mut refreshed_ctis = HashMap::new();
            for (prop_name, cti_str) in prev_state.ctis.drain() {
                match refresh_cti_for_prop(&cti_str, &rp.path("dut"), &rp.path("tmp/dut")) {
                    Ok(new_cti) => {
                        refreshed_ctis.insert(prop_name, new_cti);
                    }
                    Err(e) => {
                        info!("Failed to refresh CTI for {}: {}, dropping", prop_name, e);
                    }
                }
            }
            prev_state.ctis = refreshed_ctis;
            fs::remove_dir_all(rp.path("dut"))?;
        }
        fs::rename(rp.path("tmp/dut"), rp.path("dut"))?;
        rp.cache_dut(&src_abs)?;

        // Reinitialize CIll with the now-committed dut/
        let btor = Btor::from_file(rp.path("dut/dut.btor"));
        let btorfe = BtorFrontend::new(btor);
        cill = CIll::new(rcfg.clone(), rp.clone(), btorfe)?;
    }

    // 8. Check old CTIs BEFORE inductiveness check (solver has no invariants yet)
    //    This ensures deterministic "blocked" checks matching cill semantics
    let mut cti_blocked: HashMap<String, bool> = HashMap::new();
    for (prop_name, prev_cti_str) in &prev_state.ctis {
        let blocked = cill.check_cti_from_str(prev_cti_str).unwrap_or(true);
        cti_blocked.insert(prop_name.clone(), blocked);
    }
    // Early exit if we have previous CTIs and none are blocked
    if !prev_state.ctis.is_empty() && cti_blocked.values().all(|&b| !b) {
        println!("Previous hard-to-disprove transitions have not been blocked.");
        // Don't update states. Keep old CTIs (remove_dir_all not run).
        return Ok(());
    }
    let _ = fs::remove_dir_all(&vcd_dir);

    // 9. Check inductiveness (this loads invariants into solver)
    info!("Checking inductiveness of all properties.");
    if cill.check_inductive()? {
        println!("Congratulations! All assertions are proved inductive.");
        return Ok(());
    }

    // 10. Process all properties using pre-computed CTI blocked status
    create_dir_if_not_exists(&vcd_dir)?;
    let mut results = Vec::new();
    let mut new_ctis = HashMap::new();
    let mut new_proved = HashSet::new();
    let cill_res = cill.res.clone();

    for (id, &is_inductive) in cill_res.iter().enumerate() {
        let name = cill.get_prop_name(id).unwrap_or_else(|| format!("p{}", id));
        if is_inductive {
            // Track this property as proved for next run
            new_proved.insert(name.clone());
            // Check if it was previously not inductive
            let status = if prev_state.ctis.contains_key(&name) {
                PropStatus::ProvedAfterHelper
            } else {
                PropStatus::Proved
            };
            results.push(PropResult { name, status });
        } else {
            // Generate new CTI
            let bl_witness = cill.get_cti(id)?;
            let safe_name: String = name
                .chars()
                .map(|c| { if c.is_alphanumeric() || c == '-' { c } else { '_' } })
                .collect();
            let wit_path = vcd_dir.join(format!("{}.wit", safe_name));
            let vcd_path = vcd_dir.join(format!("{}.vcd", safe_name));
            cill.save_witness(&bl_witness, &wit_path, Some(&vcd_path))?;
            let witness_str = fs::read_to_string(&wit_path)?;

            let c = vcd_path.clone();
            // Determine status based on previous state
            let status = if prev_state.proved.contains(&name) {
                // Was proved before, now fails again
                PropStatus::Regressed { vcd: vcd_path.clone() }
            } else {
                // Use pre-computed blocked status (checked before invariants were loaded)
                match cti_blocked.get(&name) {
                    // Previous CTI is blocked, but new one appeared
                    Some(true) => PropStatus::CtiBlockedNewAppeared { vcd: c },
                    // Previous CTI is NOT blocked
                    Some(false) => PropStatus::CtiNotBlocked { vcd: c },
                    // No previous CTI for this property
                    None => PropStatus::NewCti { vcd: c },
                }
            };

            // Store the new CTI
            new_ctis.insert(name.clone(), witness_str);
            results.push(PropResult { name, status });
        }
    }

    // 11. Save new state
    fs::write(
        proj_path.join("tryprove_state.ron"),
        ron::to_string(&TryProveState {
            ctis: new_ctis,
            proved: new_proved,
        })?,
    )?;

    // 12. Print results.
    let help = |dut_path: &PathBuf, vcd: &PathBuf| {
        vcd.strip_prefix(dut_path)
            .unwrap_or(vcd)
            .display()
            .to_string()
    };
    // Collect rows, skipping CtiNotBlocked (no progress) and counting special cases
    let mut table_rows: Vec<(&str, String, &str)> = Vec::new();
    for r in results.as_slice() {
        match &r.status {
            PropStatus::Proved => {
                table_rows.push((&r.name, "None".to_string(), "Already Proved Before"));
            }
            PropStatus::ProvedAfterHelper => {
                table_rows.push((&r.name, "None".to_string(), "Just Proved :D"));
            }
            PropStatus::NewCti { vcd } => {
                let vcd_rel = help(&dut_path, vcd);
                table_rows.push((&r.name, vcd_rel, "Hard-to-disprove transitions found"));
            }
            PropStatus::CtiNotBlocked { vcd } => {
                let vcd_rel = help(&dut_path, vcd);
                table_rows.push((&r.name, vcd_rel, "Previous hard transitions not blocked"));
            }
            PropStatus::CtiBlockedNewAppeared { vcd } => {
                table_rows.push((
                    &r.name,
                    help(&dut_path, vcd),
                    "Previous hard transitions blocked but new one found",
                ));
            }
            PropStatus::Regressed { vcd } => {
                let vcd_rel = help(&dut_path, vcd);
                table_rows.push((&r.name, vcd_rel, "Regressed; was proved, fails again"));
            }
        }
    }

    println!("Name\tWaweform File\tStatus"); // header
    for (name, vcd, status) in &table_rows {
        // row contents
        println!("{}\t{}\t{}", name, vcd, status);
    }
    Ok(())
}
