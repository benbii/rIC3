use crate::{
    bmc::BMCConfig, ic3::IC3Config, kind::KindConfig, rlive::RliveConfig, wlbmc::WlBMCConfig,
    wlkind::WlKindConfig,
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
    /// rlive (CAV'24 https://doi.org/10.1007/978-3-031-65627-9_12)
    Rlive(RliveConfig),
}

impl EngineConfig {
    pub fn is_wl(&self) -> bool {
        matches!(self, EngineConfig::WlBMC(_) | EngineConfig::WlKind(_))
    }
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct PreprocConfig {
    /// disable preprocess
    #[arg(long = "preproc", action = ArgAction::Set, default_value_t = true)]
    pub preproc: bool,

    /// function reduced transys
    #[arg(long = "frts", action = ArgAction::Set, default_value_t = true)]
    pub frts: bool,

    /// frts time limit in seconds
    #[arg(long = "frts-tl", default_value_t = 1000)]
    pub frts_tl: u64,

    /// scorr
    #[arg(long = "scorr", action = ArgAction::Set, default_value_t = true)]
    pub scorr: bool,

    /// scorr time limit in seconds
    #[arg(long = "scorr-tl", default_value_t = 200)]
    pub scorr_tl: u64,

    /// load preprocessed model from file (skips preprocessing)
    #[arg(long = "load-preproc")]
    pub load_preproc: Option<PathBuf>,

    /// when loading a preprocessed model, wait for the recorded preprocess time
    #[arg(long = "fake-preproc-wait", default_value_t = false)]
    pub fake_preproc_wait: bool,
}

impl Default for PreprocConfig {
    fn default() -> Self {
        Self {
            preproc: true,
            frts: true,
            frts_tl: 1000,
            scorr: true,
            scorr_tl: 200,
            load_preproc: None,
            fake_preproc_wait: false,
        }
    }
}
