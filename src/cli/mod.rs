mod cache;
mod check;
mod cill;
mod clean;
mod run;
mod vcd;
mod yosys;

pub use cache::Ric3Proj;
pub use yosys::Yosys;

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

    /// Stateless verification - run from anywhere
    TryProve {
        /// Path to DUT directory containing ric3.toml
        dut_path: PathBuf,
    },
}

pub fn cli_main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Run => run::run(),
        Commands::Check { chk, cfg } => check::check(chk, cfg),
        Commands::Clean => clean::clean(),
        Commands::Cill { cmd } => cill(cmd),
        Commands::TryProve { dut_path } => crate::tryprove::tryprove(dut_path),
    }
}

#[derive(Deserialize, Debug)]
pub struct Ric3Config {
    pub dut: Dut,
    pub trace: Option<VcdConfig>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct VcdConfig {
    pub top: Option<String>,
}

impl Ric3Config {
    pub fn from_file<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let config_content = fs::read_to_string(p)?;
        let config: Self = toml::from_str(&config_content)?;
        config.dut.validate()?;
        Ok(config)
    }

    /// Load config and resolve relative file paths against base_path
    pub fn from_file_with_base<P: AsRef<Path>>(p: P, base_path: &Path) -> anyhow::Result<Self> {
        let config_content = fs::read_to_string(p)?;
        let mut config: Self = toml::from_str(&config_content)?;
        // Prepend base_path to relative file paths
        for file in config.dut.files.iter_mut() {
            if file.is_relative() {
                *file = base_path.join(&file);
            }
        }
        if let Some(ref mut include_files) = config.dut.include_files {
            for file in include_files.iter_mut() {
                if file.is_relative() {
                    *file = base_path.join(&file);
                }
            }
        }
        config.dut.validate()?;
        Ok(config)
    }
}

#[derive(Deserialize, Debug)]
pub struct Dut {
    pub top: String,
    pub files: Vec<PathBuf>,
    pub include_files: Option<Vec<PathBuf>>,
}

impl Dut {
    pub fn src(&self) -> Vec<PathBuf> {
        self.files
            .iter()
            .chain(self.include_files.iter().flatten())
            .cloned()
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
