use crate::config::Config;
use crate::transys::{Transys, certify::Restore};
use log::{error, info};
use serde::{Deserialize, Serialize};
use std::{
    fs::File,
    io::{BufReader, BufWriter},
    path::Path,
};

/// Preprocessed model bundle for serialization
#[derive(Serialize, Deserialize)]
pub struct PreprocModel {
    pub ts: Transys,
    pub rst: Restore,
    pub preproc_time_secs: u64,
}

impl PreprocModel {
    pub fn new(ts: Transys, rst: Restore, preproc_time_secs: u64) -> Self {
        Self {
            ts,
            rst,
            preproc_time_secs,
        }
    }

    pub fn save(&self, path: &Path) -> std::io::Result<()> {
        let file = File::create(path)?;
        let writer = BufWriter::new(file);
        bincode::serialize_into(writer, self)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))
    }

    pub fn load(path: &Path) -> std::io::Result<Self> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        bincode::deserialize_from(reader)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))
    }

    /// Load from file or run preprocessing
    pub fn load_or_preproc(ts: Transys, tcfg: &Config) -> (Transys, Restore) {
        if let Some(load_path) = &tcfg.preproc.load_preproc
            && let Ok(model) = Self::load(load_path)
        {
            info!(
                "Loaded preprocessed model from {:?} (preproc took {}s)",
                load_path, model.preproc_time_secs
            );
            if tcfg.preproc.fake_preproc_wait {
                info!(
                    "Sleeping for {}s to simulate preprocessing time",
                    model.preproc_time_secs
                );
                std::thread::sleep(std::time::Duration::from_secs(model.preproc_time_secs));
            }
            (model.ts, model.rst)
        } else if let Some(load_path) = &tcfg.preproc.load_preproc {
            error!("Load preproc model {:?} failed, skipping scorr", load_path);
            let mut pcfg = tcfg.preproc.clone();
            pcfg.scorr = false;
            let rst = Restore::new(&ts);
            ts.preproc(&pcfg, tcfg, rst)
        } else if tcfg.preproc.preproc {
            let rst = Restore::new(&ts);
            ts.preproc(&tcfg.preproc, tcfg, rst)
        } else {
            let r = Restore::new(&ts);
            (ts, r)
        }
    }
}
