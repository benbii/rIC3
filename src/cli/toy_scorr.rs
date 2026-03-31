use crate::cli::common::{init_cli_logging, load_bit_level_ts};
use clap::Parser;
use log::info;
use rIC3::{config::PreprocConfig as BlPreprocConfig, transys::toy_scorr};
use std::path::PathBuf;

#[derive(Parser, Debug, Clone)]
pub struct ToyScorrConfig {
    /// model file in aiger format or in btor2 format,
    /// for aiger model, the file name should be suffixed with .aig or .aag,
    /// for btor model, the file name should be suffixed with .btor or .btor2.
    pub model: PathBuf,

    /// output path for the init simulation report
    pub output: PathBuf,

    #[command(flatten)]
    pub cfg: BlPreprocConfig,
}

pub(crate) fn toy_scorr(cfg: ToyScorrConfig) -> anyhow::Result<i32> {
    init_cli_logging();
    let (model, ts) = load_bit_level_ts(&cfg.model, "used by toy-scorr")?;
    info!("origin ts has {}", ts.statistic());
    toy_scorr::ToyScorr::new(ts, &cfg.cfg).run(&model, &cfg.output)?;
    Ok(0)
}
