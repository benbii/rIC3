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
use log::debug;
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
    NewCti,
    /// Not inductive, previous CTI NOT blocked, old preserved as .vcd.old
    CtiNotBlocked,
    /// Not inductive, previous CTI blocked but new one appeared
    CtiBlockedNewAppeared,
    /// Was proved before, but now fails again (helper removed/weakened)
    Regressed,
}

pub fn run(path: PathBuf, bmc_timeout: u64, ic3_timeout: u64) -> anyhow::Result<()> {
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
    let mut cill = CIll::new(rcfg.clone(), rp.clone(), btorfe, bmc_timeout, ic3_timeout)?;

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
            // Clean up old counterexample.vcd before creating new one
            let _ = fs::remove_file(&cex_vcd_path);
            let cex_vcd_src = rp.path("cill/cex.vcd");
            if cex_vcd_src.exists() {
                fs::copy(&cex_vcd_src, &cex_vcd_path)?;
            }
            println!("Counterexample VCD generated to ./counterexample.vcd");
            return Ok(());
        }
        McResult::Unknown(_) => {
            // No output message needed - continue silently
        }
    }

    // 7. Safety passed/unknown - now commit DUT change and refresh CTIs
    if dut_changed {
        // Refresh all stored CTIs using the new helper
        if rp.path("dut").exists() {
            let mut refreshed_ctis = HashMap::new();
            let mut has_refresh_failure = false;
            for (prop_name, cti_str) in prev_state.ctis.drain() {
                match refresh_cti_for_prop(&cti_str, &rp.path("dut"), &rp.path("tmp/dut")) {
                    Ok(new_cti) => {
                        refreshed_ctis.insert(prop_name, new_cti);
                    }
                    Err(e) => {
                        debug!("Failed to refresh CTI for {}: {}, dropping", prop_name, e);
                        has_refresh_failure = true;
                    }
                }
            }
            // If any CTI refresh failed (i.e. has deleted assertion), reset completely
            if has_refresh_failure {
                debug!("Some CTIs couldn't be refreshed. Resetting state completely.");
                refreshed_ctis.clear();
                // prev_state.proved.clear();
            }
            prev_state.ctis = refreshed_ctis;
            fs::remove_dir_all(rp.path("dut"))?;
        }
        fs::rename(rp.path("tmp/dut"), rp.path("dut"))?;
        rp.cache_dut(&src_abs)?;

        // Save refreshed CTIs immediately so they're available for next run even if we exit early
        fs::write(
            proj_path.join("tryprove_state.ron"),
            ron::to_string(&TryProveState {
                ctis: prev_state.ctis.clone(),
                proved: prev_state.proved.clone(),
            })?,
        )?;
    }

    // 8. Check inductiveness (this loads invariants into solver)
    if cill.check_inductive()? {
        println!("Congratulations! All assertions are proved inductive.");
        return Ok(());
    }

    // 9. Check old CTIs AFTER inductiveness check (matching cill semantics)
    let mut cti_blocked: HashMap<String, bool> = HashMap::new();
    for (prop_name, prev_cti_str) in &prev_state.ctis {
        let blocked = cill.check_cti_from_str(prev_cti_str).unwrap_or(true);
        cti_blocked.insert(prop_name.clone(), blocked);
    }

    // 10. Process all properties - always generate new CTIs (no early exit)
    let _ = fs::remove_dir_all(&vcd_dir);
    create_dir_if_not_exists(&vcd_dir)?;
    let mut results = Vec::new();
    let mut new_ctis = HashMap::new();
    let mut new_proved = HashSet::new();
    let cill_res = cill.res.clone();

    for (id, &is_inductive) in cill_res.iter().enumerate() {
        let name = cill.get_prop_name(id).unwrap_or_else(|| format!("p{}", id));
        if is_inductive {
            new_proved.insert(name.clone());
            let status = if prev_state.proved.contains(&name) {
                PropStatus::Proved
            } else {
                PropStatus::ProvedAfterHelper
            };
            results.push((name, status));
        } else {
            // Generate new CTI
            let bl_witness = cill.get_cti(id)?;
            let safe_name: String = name
                .chars()
                .map(|c| if c.is_alphanumeric() || c == '-' { c } else { '_' })
                .collect();
            let vcd_path = vcd_dir.join(format!("{}.vcd", safe_name));

            // Determine status and handle old VCD preservation
            let status = if prev_state.proved.contains(&name) {
                PropStatus::Regressed
            } else {
                match cti_blocked.get(&name) {
                    Some(true) => PropStatus::CtiBlockedNewAppeared,
                    Some(false) => {
                        // Preserve old VCD as .vcd.old before generating new one
                        let old_vcd_path = vcd_dir.join(format!("{}.vcd.old", safe_name));
                        let _ = fs::copy(&vcd_path, &old_vcd_path);
                        PropStatus::CtiNotBlocked
                    }
                    None => PropStatus::NewCti,
                }
            };

            // Save witness to temp file (for state) and VCD
            let wit_path = rp.path("tmp/witness.wit");
            cill.save_witness(&bl_witness, &wit_path, Some(&vcd_path))?;
            let witness_str = fs::read_to_string(&wit_path)?;
            new_ctis.insert(name.clone(), witness_str);
            results.push((name, status));
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

    // 12. Print results grouped by status
    let mut not_blocked: Vec<&str> = Vec::new();
    let mut blocked_new: Vec<&str> = Vec::new();
    let mut new_cti: Vec<&str> = Vec::new();
    let mut just_proved: Vec<&str> = Vec::new();
    let mut regressed: Vec<&str> = Vec::new();

    for (name, status) in &results {
        match status {
            PropStatus::CtiNotBlocked { .. } => {
                not_blocked.push(name);
            }
            PropStatus::CtiBlockedNewAppeared { .. } => {
                blocked_new.push(name);
            }
            PropStatus::NewCti { .. } => {
                new_cti.push(name);
            }
            PropStatus::ProvedAfterHelper => {
                just_proved.push(name);
            }
            PropStatus::Proved => {} // Skip already proved
            PropStatus::Regressed => {
                regressed.push(name);
            }
        }
    }

    // Print each group
    if !not_blocked.is_empty() {
        println!("Your helpers did not block hard transitions of these assertions.");
        println!("Their old hard transitions are preserved in hard_trans/{{name}}.vcd.old");
        println!("New, likely similar hard transitions generated in hard_trans/{{name}}.vcd");
        for name in &not_blocked {
            println!("{}", name);
        }
        println!();
    }
    if !blocked_new.is_empty() {
        println!("Your helpers blocked transitions to these assertions, but new ones emerge,");
        println!("placed in hard_trans/{{name}}.vcd");
        for name in &blocked_new {
            println!("{}", name);
        }
        println!();
    }
    if !new_cti.is_empty() {
        println!("Hard-to-disprove transitions found for these new assertions.");
        println!("Waveforms to these transitions are in hard_trans/{{name}}.vcd");
        for name in &new_cti {
            println!("{}", name);
        }
        println!();
    }
    if !just_proved.is_empty() {
        println!("Assertions just proved:");
        for name in &just_proved {
            println!("{}", name);
        }
        println!();
    }
    if !regressed.is_empty() {
        println!("Assertions regressed (were proved before, now fail again):");
        for name in &regressed {
            println!("{}", name);
        }
        println!();
    }
    Ok(())
}
