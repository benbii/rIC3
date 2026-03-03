use crate::{
    config::PreprocConfig,
    transys::{Transys, certify::Restore},
};
use log::{error, info};
use serde::{Deserialize, Serialize};
use std::{
    fs::File,
    io::{BufReader, BufWriter},
    path::Path,
    time::{Duration, Instant},
};

#[derive(Serialize, Deserialize)]
pub struct PreprocModel {
    pub ts: Transys,
    pub rst: Restore,
    pub preproc_time_secs: u64,
}

impl PreprocModel {
    pub fn run(ts: Transys, cfg: &PreprocConfig) -> Self {
        let start = Instant::now();
        let rst = Restore::new(&ts);
        let (ts, rst) = ts.preproc(cfg, rst);
        let preproc_time_secs = start.elapsed().as_secs();
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

    pub fn load_or_preproc(ts: Transys, cfg: &PreprocConfig) -> (Self, bool) {
        if let Some(load_path) = &cfg.load_preproc {
            match Self::load(load_path) {
                Ok(model) => {
                    info!(
                        "Loaded preprocessed model from {:?} (preproc took {}s)",
                        load_path, model.preproc_time_secs
                    );
                    if cfg.fake_preproc_wait {
                        info!(
                            "Sleeping for {}s to simulate preprocessing time",
                            model.preproc_time_secs
                        );
                        std::thread::sleep(Duration::from_secs(model.preproc_time_secs));
                    }
                    return (model, true);
                }
                Err(err) => {
                    error!(
                        "Load preproc model {:?} failed: {:?}; falling back to normal preprocessing",
                        load_path, err
                    );
                    return (Self::run(ts, cfg), false);
                }
            }
        }
        (Self::run(ts, cfg), false)
    }
}
