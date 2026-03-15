use crate::logger_init;
use clap::Parser;
use log::{error, info};
use rIC3::{
    aig::Aig,
    btor::Btor,
    config::{EngineConfig, PreprocConfig},
    frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend},
    transys::{TransysIf, preproc_serde::PreprocModel},
};
use std::{env, path::PathBuf, process::exit};

#[derive(Parser, Debug, Clone)]
pub struct PreprocessConfig {
    /// model file in aiger format or in btor2 format,
    /// for aiger model, the file name should be suffixed with .aig or .aag,
    /// for btor model, the file name should be suffixed with .btor or .btor2.
    pub model: PathBuf,

    /// output path for the preprocessed bit-level model
    #[arg(short = 'o', long)]
    pub output: PathBuf,
}

fn preproc_cfg(cfg: &EngineConfig) -> Option<&PreprocConfig> {
    match cfg {
        EngineConfig::IC3(cfg) => Some(&cfg.preproc),
        EngineConfig::Kind(cfg) => Some(&cfg.preproc),
        EngineConfig::BMC(cfg) => Some(&cfg.preproc),
        EngineConfig::Rlive(cfg) => Some(&cfg.preproc),
        _ => None,
    }
}

pub(crate) fn preprocess(mut pp: PreprocessConfig, cfg: EngineConfig) -> anyhow::Result<i32> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();
    pp.model = pp.model.canonicalize()?;
    info!("the model to be preprocessed: {}", pp.model.display());
    if cfg.is_wl() {
        error!("preprocess is only supported for bit-level engines");
        exit(1);
    }
    let Some(pcfg) = preproc_cfg(&cfg) else {
        error!("selected engine does not support bit-level preprocessing export");
        exit(1);
    };
    if pcfg.load_preproc.is_some() {
        error!("preprocess does not support --load-preproc");
        exit(1);
    }
    if pcfg.fake_preproc_wait {
        error!("preprocess does not support --fake-preproc-wait");
        exit(1);
    }
    let mut frontend: Box<dyn Frontend> = match pp.model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => {
            let aig = Aig::from_file(&pp.model);
            Box::new(AigFrontend::new(aig))
        }
        Some(ext) if (ext == "btor") | (ext == "btor2") => {
            let btor = Btor::from_file(&pp.model);
            Box::new(BtorFrontend::new(btor))
        }
        _ => {
            error!("Unsupported file format. Supported extensions are: .aig, .aag, .btor, .btor2.");
            exit(1);
        }
    };
    let ts = frontend.ts();
    info!("origin ts has {}", ts.statistic());
    let model = PreprocModel::run(ts, pcfg);
    model.save(&pp.output)?;
    info!(
        "Exported preprocessed model to {:?} (preproc took {}s)",
        pp.output, model.preproc_time_secs
    );
    Ok(0)
}
