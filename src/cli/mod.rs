mod check;
mod preprocess;

use crate::cli::{check::CheckConfig, preprocess::PreprocessConfig};
use clap::{Parser, Subcommand};
use rIC3::config::EngineConfig;

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
    /// Verify properties for AIGER/BTOR files
    Check {
        #[command(flatten)]
        chk: CheckConfig,

        #[command(subcommand)]
        cfg: EngineConfig,
    },

    /// preprocess and export a bit-level model
    Preprocess {
        #[command(flatten)]
        pp: PreprocessConfig,

        #[command(subcommand)]
        cfg: EngineConfig,
    },
}

pub(crate) fn cli_main() -> anyhow::Result<i32> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Check { chk, cfg } => check::check(chk, cfg),
        Commands::Preprocess { pp, cfg } => preprocess::preprocess(pp, cfg),
    }
}
