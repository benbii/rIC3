mod cache;
mod check;
mod cill;
mod clean;
mod run;
mod tryprove;
mod vcd;
mod yosys;

use crate::cli::{
    check::CheckConfig,
    cill::{CIllCommands, cill},
};
use clap::{Parser, Subcommand};
use giputils::hash::GHashSet;
use rIC3::config::EngineConfig;
use serde::Deserialize;
use std::{
    fs,
    iter::once,
    path::{Path, PathBuf},
};

/// rIC3 Hardware Formal Verification Tool
#[derive(Parser, Debug, Clone)]
#[command(
    version,
    about,
    after_help = "Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved."
)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand, Debug, Clone)]
pub enum Commands {
    /// Run verification using 'ric3.toml' (requires the file in the current directory)
    Run,

    /// Verify properties for AIGER/BTOR files
    Check {
        #[command(flatten)]
        chk: CheckConfig,

        #[command(subcommand)]
        cfg: EngineConfig,
    },

    /// Clean up verification cache (ric3proj)
    Clean,

    /// CTI Guided Interactive Lemma Generation
    Cill {
        #[command(subcommand)]
        cmd: CIllCommands,
    },

    /// Stateless proof attempt (LLM/agent friendly, no sub-subcommands)
    TryProve {
        /// Path to DUT directory containing ric3.toml
        path: PathBuf,

        /// BMC timeout in seconds (default: 15)
        #[arg(long, default_value = "15")]
        bmc_timeout: u64,

        /// IC3 timeout in seconds (default: 30)
        #[arg(long, default_value = "30")]
        ic3_timeout: u64,
    },
}

pub fn cli_main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Run => run::run(),
        Commands::Check { chk, cfg } => check::check(chk, cfg),
        Commands::Clean => clean::clean(),
        Commands::Cill { cmd } => cill(cmd),
        Commands::TryProve { path, bmc_timeout, ic3_timeout } => {
            tryprove::run(path, bmc_timeout, ic3_timeout)
        }
    }
}

#[derive(Deserialize, Debug, Clone)]
pub struct Ric3Config {
    dut: Dut,
    trace: Option<VcdConfig>,
    modeling: Modeling,
}

#[derive(Deserialize, Debug, Clone)]
pub struct VcdConfig {
    top: Option<String>,
}

impl Ric3Config {
    fn from_file<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let config_content = fs::read_to_string(p)?;
        let config: Self = toml::from_str(&config_content)?;
        config.dut.validate()?;
        Ok(config)
    }
}

#[derive(Deserialize, Debug, Clone)]
pub struct Dut {
    pub reset: Option<String>,
    pub top: String,
    pub files: Vec<PathBuf>,
    pub include_files: Option<Vec<PathBuf>>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Modeling {
    pub parser: Parse,
}

#[derive(Deserialize, Debug, Clone)]
#[allow(non_camel_case_types)]
pub enum Parse {
    yosys,
    yosys_slang,
}

impl Dut {
    fn src(&self) -> Vec<PathBuf> {
        self.files
            .iter()
            .chain(self.include_files.iter().flatten())
            .cloned()
            .chain(once(PathBuf::from("ric3.toml")))
            .collect()
    }

    fn validate(&self) -> anyhow::Result<()> {
        if self.files.is_empty() {
            anyhow::bail!("dut files cannot be empty");
        }
        let mut seen_names = GHashSet::new();
        let files = self.src();
        for file in files.iter() {
            if !file.exists() {
                anyhow::bail!("file not found: {:?}", file);
            }
            if let Some(name) = file.file_name() {
                if !seen_names.insert(name) {
                    anyhow::bail!("duplicate file name found: {:?}", name);
                }
            } else {
                anyhow::bail!("invalid file path: {:?}", file);
            }
        }
        Ok(())
    }
}
