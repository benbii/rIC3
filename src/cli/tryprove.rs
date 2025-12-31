//! Stateless proof attempt command - LLM/agent friendly alternative to `cill`.
//!
//! Unlike `cill` which has sub-subcommands and tracks state, `tryprove` is a single
//! command that processes all assertions at once and reports status for each.

use super::{Ric3Config, cache::Ric3Proj, cill::{CIll, refresh_cti_for_prop}, yosys::Yosys};
use crate::logger_init;
use btor::Btor;
use giputils::file::{create_dir_if_not_exists, recreate_dir};
use log::info;
use rIC3::{McResult, frontend::btor::BtorFrontend};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    env, fs,
    path::PathBuf,
};

/// Persistent state for tryprove - stores CTIs for all properties
#[derive(Serialize, Deserialize, Default, Debug)]
struct TryProveState {
    /// Map from property name to serialized CTI witness string
    ctis: HashMap<String, String>,
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
    // Real counterexample found - assertion triggered
    // AssertionTriggered { vcd: PathBuf },
}

/// Result for a single property
#[derive(Debug)]
struct PropResult {
    id: usize,
    name: String,
    status: PropStatus,
}

fn load_state(proj_path: &PathBuf) -> anyhow::Result<TryProveState> {
    let state_file = proj_path.join("tryprove_state.ron");
    if state_file.exists() {
        let content = fs::read_to_string(&state_file)?;
        Ok(ron::from_str(&content)?)
    } else {
        Ok(TryProveState::default())
    }
}

fn save_state(proj_path: &PathBuf, state: &TryProveState) -> anyhow::Result<()> {
    let state_file = proj_path.join("tryprove_state.ron");
    fs::write(state_file, ron::to_string(state)?)?;
    Ok(())
}

fn sanitize_filename(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_alphanumeric() || c == '_' || c == '-' { c } else { '_' })
        .collect()
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

    // Clean up VCDs from previous runs to avoid stale files
    if vcd_dir.exists() {
        fs::remove_dir_all(&vcd_dir)?;
    }
    if cex_vcd_path.exists() {
        fs::remove_file(&cex_vcd_path)?;
    }

    // 2. Read config (need to cd for relative paths in ric3.toml)
    let orig_dir = env::current_dir()?;
    env::set_current_dir(&dut_path)?;
    let rcfg = Ric3Config::from_file("ric3.toml")?;

    // 3. Load previous state
    let mut prev_state = load_state(&proj_path)?;

    // 4. Initialize project
    let rp = Ric3Proj::with_path(proj_path.clone())?;
    recreate_dir(rp.path("tmp"))?;

    // 5. Generate DUT (but don't commit yet if it changed - need to check safety first)
    let dut_changed = match rp.check_cached_dut(&rcfg.dut.src())? {
        Some(false) => {
            // DUT changed - generate new BTOR in tmp/dut first
            Yosys::generate_btor(&rcfg, rp.path("tmp/dut"))?;
            true
        }
        None => {
            // First run - generate directly to dut/
            Yosys::generate_btor(&rcfg, rp.path("dut"))?;
            rp.cache_dut(&rcfg.dut.src())?;
            false
        }
        Some(true) => false,
    };

    env::set_current_dir(&orig_dir)?;

    // 6. Check safety BEFORE committing DUT change
    // Use tmp/dut if DUT changed, otherwise use dut/
    let dut_dir = if dut_changed { rp.path("tmp/dut") } else { rp.path("dut") };
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
                rp.cache_dut(&rcfg.dut.src())?;
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
        rp.cache_dut(&rcfg.dut.src())?;

        // Reinitialize CIll with the now-committed dut/
        let btor = Btor::from_file(rp.path("dut/dut.btor"));
        let btorfe = BtorFrontend::new(btor);
        cill = CIll::new(rcfg.clone(), rp.clone(), btorfe)?;
    }

    // 8. Check inductiveness
    info!("Checking inductiveness of all properties.");
    if cill.check_inductive()? {
        println!("Congratulations! All assertions are proved inductive.");
        return Ok(());
    }

    // 9. Process all properties
    create_dir_if_not_exists(&vcd_dir)?;

    let mut results = Vec::new();
    let mut new_ctis = HashMap::new();
    let cill_res = cill.res.clone();

    for (id, &is_inductive) in cill_res.iter().enumerate() {
        let name = cill
            .get_prop_name(id)
            .unwrap_or_else(|| format!("p{}", id));

        if is_inductive {
            // Check if it was previously not inductive
            let status = if prev_state.ctis.contains_key(&name) {
                PropStatus::ProvedAfterHelper
            } else {
                PropStatus::Proved
            };
            results.push(PropResult { id, name, status });
        } else {
            // Generate new CTI using cill.save_witness() to stay in sync
            let bl_witness = cill.get_cti(id)?;
            let safe_name = sanitize_filename(&name);
            let wit_path = vcd_dir.join(format!("{}.wit", safe_name));
            let vcd_path = vcd_dir.join(format!("{}.vcd", safe_name));
            cill.save_witness(&bl_witness, &wit_path, Some(&vcd_path))?;
            let witness_str = fs::read_to_string(&wit_path)?;

            // Determine status by checking if previous CTI is blocked
            let status = if let Some(prev_cti_str) = prev_state.ctis.get(&name) {
                // Use SAT-based check to see if previous CTI is blocked
                match cill.check_cti_from_str(prev_cti_str) {
                    Ok(true) => {
                        // Previous CTI is blocked, but new one appeared
                        PropStatus::CtiBlockedNewAppeared { vcd: vcd_path.clone() }
                    }
                    Ok(false) => {
                        // Previous CTI is NOT blocked
                        PropStatus::CtiNotBlocked { vcd: vcd_path.clone() }
                    }
                    Err(_) => {
                        // Error checking CTI, treat as new
                        PropStatus::NewCti { vcd: vcd_path.clone() }
                    }
                }
            } else {
                PropStatus::NewCti { vcd: vcd_path.clone() }
            };

            // Store the new CTI
            new_ctis.insert(name.clone(), witness_str);

            results.push(PropResult {
                id,
                name,
                status,
            });
        }
    }

    // 10. Save new state
    save_state(&proj_path, &TryProveState { ctis: new_ctis })?;

    // 11. Print results
    print_results(&results, &dut_path);

    Ok(())
}

fn print_results(results: &[PropResult], dut_path: &PathBuf) {
    // Separate ProvedAfterHelper from other results
    let mut table_rows: Vec<(usize, &str, String, &str)> = Vec::new();
    let mut num_previously_proved = 0;

    for r in results {
        match &r.status {
            PropStatus::ProvedAfterHelper => {
                num_previously_proved += 1;
            }
            PropStatus::Proved => {
                table_rows.push((r.id, &r.name, "None".to_string(), "Just Proved :D"));
            }
            // PropStatus::AssertionTriggered { vcd } => {
            //     let vcd_rel = vcd.strip_prefix(dut_path).unwrap_or(vcd);
            //     table_rows.push((r.id, &r.name, vcd_rel.display().to_string(), "Assertion Triggered"));
            // }
            PropStatus::NewCti { vcd } => {
                let vcd_rel = vcd.strip_prefix(dut_path).unwrap_or(vcd);
                table_rows.push((r.id, &r.name, vcd_rel.display().to_string(), "Hard-to-disprove transitions found"));
            }
            PropStatus::CtiNotBlocked { vcd } => {
                let vcd_rel = vcd.strip_prefix(dut_path).unwrap_or(vcd);
                table_rows.push((r.id, &r.name, vcd_rel.display().to_string(), "Previous hard transitions not blocked"));
            }
            PropStatus::CtiBlockedNewAppeared { vcd } => {
                let vcd_rel = vcd.strip_prefix(dut_path).unwrap_or(vcd);
                table_rows.push((r.id, &r.name, vcd_rel.display().to_string(), "Previous hard transitions blocked but new one found"));
            }
        }
    }

    if table_rows.is_empty() && num_previously_proved > 0 {
        println!("({} assertions already proved unreachable previously)", num_previously_proved);
        return;
    }

    // Calculate column widths
    let id_width = 3;
    let name_width = table_rows.iter().map(|(_, n, _, _)| n.len()).max().unwrap_or(4).max(4);
    let vcd_width = table_rows.iter().map(|(_, _, v, _)| v.len()).max().unwrap_or(13).max(13);

    // Print header
    println!(
        "{:<id_width$} {:<name_width$} {:<vcd_width$} {}",
        "ID", "Name", "Waveform File", "Status"
    );

    // Print rows
    for (id, name, vcd, status) in &table_rows {
        println!(
            "{:<id_width$} {:<name_width$} {:<vcd_width$} {}",
            id, name, vcd, status
        );
    }

    if num_previously_proved > 0 {
        println!();
        println!("({} assertions already proved unreachable previously)", num_previously_proved);
    }
}
