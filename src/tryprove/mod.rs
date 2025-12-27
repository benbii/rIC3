mod engine;
mod output;
mod state;

use crate::cli::{Ric3Config, Ric3Proj, Yosys};
use crate::logger_init;
use giputils::file::{create_dir_if_not_exists, recreate_dir};
use std::{env, fs, path::PathBuf};

pub fn tryprove(dut_path: PathBuf) -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();

    // 1. Resolve paths
    let dut_path = fs::canonicalize(&dut_path)?;
    let dut_name = dut_path
        .file_name()
        .ok_or_else(|| anyhow::anyhow!("invalid dut path"))?
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("dut path contains invalid UTF-8"))?;
    let proj_path = dut_path
        .parent()
        .ok_or_else(|| anyhow::anyhow!("dut path has no parent"))?
        .join(format!("{}_ric3proj", dut_name));

    // 2. Load config from dut_path/ric3.toml (with paths resolved against dut_path)
    let rcfg = Ric3Config::from_file_with_base(dut_path.join("ric3.toml"), &dut_path)?;

    // 3. Setup project directory (outside DUT)
    let rp = Ric3Proj::at(proj_path.clone())?;

    // 4. Load previous state (if exists)
    let last_state = state::LastRunState::load(&proj_path);

    // 5. Setup VCD directories (inside DUT)
    let hard_trans_dir = dut_path.join("hard_trans");
    recreate_dir(&hard_trans_dir)?; // Clean previous waveforms
    let cex_path = dut_path.join("counterexample.vcd");

    // 6. Build DUT if needed
    recreate_dir(rp.path("tmp"))?;
    match rp.check_cached_dut(&rcfg.dut.src())? {
        Some(false) => {
            Yosys::generate_btor(&rcfg, rp.path("tmp/dut"))?;
            fs::remove_dir_all(rp.path("dut"))?;
            fs::rename(rp.path("tmp/dut"), rp.path("dut"))?;
            rp.cache_dut(&rcfg.dut.src())?;
        }
        None => {
            Yosys::generate_btor(&rcfg, rp.path("dut"))?;
            rp.cache_dut(&rcfg.dut.src())?;
        }
        Some(true) => (),
    }

    // 7. Run verification engine with comparison
    let (result, new_state) =
        engine::run_verification(rcfg, &rp, &hard_trans_dir, &cex_path, last_state.as_ref())?;

    // 8. Save state for next run
    new_state.save(&proj_path)?;

    // 9. Print human-friendly output
    output::print_result(&result, &dut_path);

    Ok(())
}
