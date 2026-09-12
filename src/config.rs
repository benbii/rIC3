use crate::{
    bmc::BMCConfig, ic3::IC3Config, kind::KindConfig, wlbmc::WlBMCConfig, wlkind::WlKindConfig,
};
use clap::{ArgAction, Args, Parser};
use enum_as_inner::EnumAsInner;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use strum::AsRefStr;

#[derive(Parser, Clone, Debug, Serialize, Deserialize, AsRefStr, EnumAsInner)]
pub enum EngineConfig {
    /// ic3
    IC3(IC3Config),
    /// k-induction
    Kind(KindConfig),
    /// bmc
    BMC(BMCConfig),
    /// word level bmc
    WlBMC(WlBMCConfig),
    /// word level k-induction
    WlKind(WlKindConfig),
    /// rlive (immature)
    Rlive,
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct PreprocConfig {
    /// Property ID. If omitted, check the disjunction of all bad properties
    #[arg(long = "prop", default_value_t = usize::MAX)]
    pub prop: usize,
    /// Assume structurally connected helper properties before the target's failing frame
    #[arg(long = "local-proof", default_value_t = false)]
    pub local_proof: bool,
    /// Disable functional reduction of the transition system
    #[arg(long = "no-frts", action = ArgAction::SetFalse)]
    pub frts: bool,
    /// frts time limit in seconds
    #[arg(long = "frts-tl", default_value_t = 1000)]
    pub frts_tl: u64,
    /// Disable sequential correlation reduction
    #[arg(long = "no-scorr", action = ArgAction::SetFalse)]
    pub scorr: bool,
    /// scorr time limit in seconds
    #[arg(long = "scorr-tl", default_value_t = 200)]
    pub scorr_tl: u64,
    /// Preprocessed model file (loads on `check`; exports on `preprocess`)
    #[arg(long = "preproc-file")]
    pub preproc_file: Option<PathBuf>,
    /// when loading a preprocessed model, wait for the recorded preprocess time
    #[arg(long = "fake-preproc-wait", default_value_t = false)]
    pub fake_preproc_wait: bool,
}
