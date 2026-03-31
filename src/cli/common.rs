use crate::logger_init;
use log::{error, info};
use rIC3::{
    aig::Aig,
    btor::Btor,
    frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend},
    transys::Transys,
};
use std::{env, path::Path};

pub(crate) fn init_cli_logging() {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();
}

pub(crate) fn load_bit_level_ts(
    model: &Path,
    action: &str,
) -> anyhow::Result<(std::path::PathBuf, Transys)> {
    let model = model.canonicalize()?;
    info!("the model to be {action}: {}", model.display());
    let mut frontend: Box<dyn Frontend> = match model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => {
            let aig = Aig::from_file(&model);
            Box::new(AigFrontend::new(aig))
        }
        Some(ext) if (ext == "btor") | (ext == "btor2") => {
            let btor = Btor::from_file(&model);
            Box::new(BtorFrontend::new(btor))
        }
        _ => {
            error!("Unsupported file format. Supported extensions are: .aig, .aag, .btor, .btor2.");
            std::process::exit(1);
        }
    };
    Ok((model, frontend.ts()))
}
