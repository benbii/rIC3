use clap::Parser;
use log::info;
use rIC3::{
    Engine, LitVec, McResult,
    aig::Aig,
    bmc::BMC,
    btor::Btor,
    config::{EngineConfig, PreprocConfig},
    frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend},
    ic3::IC3,
    kind::Kind,
    rlive::Rlive,
    transys::{Transys, certify::Restore},
    wlbmc::WlBMC,
    wlkind::WlKind,
};
use std::{
    env, fs,
    fs::File,
    io::BufReader,
    io::BufWriter,
    path::PathBuf,
    process::ExitCode,
    time::{Duration, Instant},
};

/// rIC3 Hardware Formal Verification Tool
#[derive(Parser, Debug, Clone)]
#[command(version)]
enum Commands {
    /// Verify properties for AIGER/BTOR files
    Check {
        #[command(flatten)]
        chk: CheckCmd,
        #[command(flatten)]
        pp: PreprocConfig,
        #[command(subcommand)]
        cfg: EngineConfig,
    },
    /// preprocess and export a bit-level model
    Preprocess {
        #[command(flatten)]
        pp: PreprocessCmd,
    },
}

#[derive(Parser, Debug, Clone)]
struct CheckCmd {
    /// model file in aiger format or in btor2 format
    pub model: PathBuf,
    /// certificate path
    #[arg(long)]
    pub cert: Option<PathBuf>,
    /// certify with certifaiger or cerbtora
    #[arg(long, default_value_t = false)]
    pub certify: bool,
    /// print witness when model is unsafe
    #[arg(long, default_value_t = false)]
    pub witness: bool,
}

#[derive(Parser, Debug, Clone)]
struct PreprocessCmd {
    /// model file in aiger format or in btor2 format
    pub model: PathBuf,
    #[command(flatten)]
    pub cfg: PreprocConfig,
}

fn main() -> ExitCode {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    env_logger::init();
    match Commands::parse() {
        Commands::Check { chk, cfg, pp } => cmd_check(chk, cfg, pp),
        Commands::Preprocess { pp } => cmd_preproc(pp),
    }
}

fn cmd_check(mut chk: CheckCmd, cfg: EngineConfig, pp: PreprocConfig) -> ExitCode {
    chk.model = chk.model.canonicalize().unwrap();
    info!("the model to be checked: {}", chk.model.display());
    if chk.cert.is_none() && (chk.certify || chk.witness) {
        let tmp_cert_file = tempfile::NamedTempFile::new().unwrap();
        chk.cert = Some(PathBuf::from(tmp_cert_file.path()));
        drop(tmp_cert_file);
    }

    let mut fend: Box<dyn Frontend> = match chk.model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => {
            Box::new(AigFrontend::new(Aig::from_file(&chk.model)))
        }
        Some(ext) if (ext == "btor") | (ext == "btor2") => {
            Box::new(BtorFrontend::new(Btor::from_file(&chk.model)))
        }
        _ => panic!("aig, aag, btor, btor2 files only."),
    };
    let ots = fend.ts();

    let (ts, rst) = if let Some(ref p) = pp.load
        && let Ok(file) = File::open(&p)
        && let mut file = BufReader::new(file)
        && let Ok(ts_ld) = bincode::deserialize_from(&mut file)
        && let Ok(rst_ld) = bincode::deserialize_from(&mut file)
        && let Ok(sec_ld) = bincode::deserialize_from(&mut file)
    {
        if pp.fake_preproc_wait {
            std::thread::sleep(Duration::from_secs(sec_ld));
        }
        info!("loaded transys has {}", ots.statistic());
        (ts_ld, rst_ld)
    } else {
        info!("transys to be checked has {}", ots.statistic());
        let mut ts = ots.clone_deep();
        let rst = Restore::new(&ts);
        if pp.prop < ts.bad.len() {
            ts.bad = LitVec::from(ts.bad[pp.prop]);
        } else if ts.bad.len() > 1 {
            let bad = std::mem::take(&mut ts.bad);
            ts.bad = LitVec::from(ts.rel_mut().new_or(bad));
        }
        Transys::preproc(ts, &pp, rst)
    };

    let mut engine: Box<dyn Engine> = match cfg {
        // not all would require the restore structure though
        EngineConfig::IC3(cfg) => Box::new(IC3::new(cfg, ts, ots, rst)),
        EngineConfig::Kind(cfg) => Box::new(Kind::new(cfg, ts, ots, rst)),
        EngineConfig::BMC(cfg) => Box::new(BMC::new(cfg, ts, ots, rst)),
        EngineConfig::Rlive => Box::new(Rlive::new(ts, rst)),
        EngineConfig::WlBMC(cfg) => Box::new(WlBMC::new(cfg, fend.wts().0)),
        EngineConfig::WlKind(cfg) => Box::new(WlKind::new(cfg, fend.wts().0)),
    };

    let res = engine.check();
    engine.statistic();
    ExitCode::from(match res {
        McResult::Safe => {
            assert!(!chk.certify || fend.certify(&chk.model, chk.cert.as_ref().unwrap()));
            println!("UNSAT{}", if chk.witness { "\n0" } else { "" });
            if let Some(ref p) = chk.cert {
                let c = fend.safe_certificate(engine.proof());
                fs::write(p, format!("{c}")).unwrap();
            }
            20
        }
        McResult::Unsafe(_) => {
            assert!(!chk.certify || fend.certify(&chk.model, chk.cert.as_ref().unwrap()));
            println!("SAT");
            if chk.witness {
                println!(
                    "{}",
                    fs::read_to_string(chk.cert.as_ref().unwrap()).unwrap()
                );
            }
            if let Some(ref p) = chk.cert {
                let c = fend.unsafe_certificate(engine.witness());
                fs::write(p, format!("{c}")).unwrap();
            }
            10
        }
        McResult::Unknown(_) => {
            println!("UNKNOWN{}", if chk.witness { "\n2" } else { "" });
            30
        }
    })
}

fn cmd_preproc(pp: PreprocessCmd) -> ExitCode {
    let model = pp.model.canonicalize().unwrap();
    let ts = match model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => {
            AigFrontend::new(Aig::from_file(&model)).ts()
        }
        Some(ext) if (ext == "btor") | (ext == "btor2") => {
            BtorFrontend::new(Btor::from_file(&model)).ts()
        }
        _ => panic!("aig, aag, btor, btor2 files only."),
    };
    info!("original transys has {}", ts.statistic());
    let t = Instant::now();
    let rst = Restore::new(&ts);
    let (ts, rst) = Transys::preproc(ts, &pp.cfg, rst);
    if let Some(o) = pp.cfg.export {
        let sec = t.elapsed().as_secs();
        let mut file = BufWriter::new(File::create(&o).unwrap());
        bincode::serialize_into(&mut file, &ts).unwrap();
        bincode::serialize_into(&mut file, &rst).unwrap();
        bincode::serialize_into(&mut file, &sec).unwrap();
        info!("Preprocessed to {:?} in {sec}s)", o);
    }
    info!("Preprocessing took {} secs", t.elapsed().as_secs());
    ExitCode::from(0)
}
