use crate::logger_init;
use aig::Aig;
use btor::Btor;
use clap::Parser;
use log::{error, info};
use rIC3::{
    Engine, McResult,
    config::EngineConfig,
    create_bl_engine, create_wl_engine,
    frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend, certificate_check},
    portfolio::{Portfolio, PortfolioConfig},
    tracer::LogTracer,
    transys::TransysIf,
};
use std::{env, fs, mem::transmute, path::PathBuf, process::exit};

#[derive(Parser, Debug, Clone)]
pub struct CheckConfig {
    /// model file in aiger format or in btor2 format,
    /// for aiger model, the file name should be suffixed with .aig or .aag,
    /// for btor model, the file name should be suffixed with .btor or .btor2.
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

    /// interrupt statistic
    #[arg(long, default_value_t = false)]
    pub interrupt_statistic: bool,

    /// skip simplification
    #[arg(long, default_value_t = false)]
    pub skip_simp: bool,
}

fn report_res(chk: &CheckConfig, res: McResult) -> u8 {
    match res {
        McResult::Safe => {
            println!("UNSAT");
            if chk.witness {
                println!("0");
            }
            20
        }
        McResult::Unsafe(_) => {
            println!("SAT");
            if chk.witness {
                let witness = fs::read_to_string(chk.cert.as_ref().unwrap()).unwrap();
                println!("{witness}");
            }
            10
        }
        McResult::Unknown(_) => {
            println!("UNKNOWN");
            if chk.witness {
                println!("2");
            }
            30
        }
    }
}

pub fn check(mut chk: CheckConfig, cfg: EngineConfig) -> u8 {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();
    chk.model = chk.model.canonicalize().unwrap_or(chk.model);
    info!("the model to be checked: {}", chk.model.display());
    let mut tmp_cert = None;
    if chk.cert.is_none() && (chk.certify || chk.witness) {
        let tmp_cert_file = tempfile::NamedTempFile::new().unwrap();
        chk.cert = Some(PathBuf::from(tmp_cert_file.path()));
        tmp_cert = Some(tmp_cert_file);
    }
    if let EngineConfig::Portfolio(cfg) = cfg {
        let res = portfolio_main(chk, cfg);
        drop(tmp_cert);
        return res;
    }
    let mut frontend: Box<dyn Frontend> = match chk.model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => {
            let aig = Aig::from_file(&chk.model);
            let mut fe = AigFrontend::new(aig);
            fe.set_skip_simp(chk.skip_simp);
            Box::new(fe)
        }
        Some(ext) if (ext == "btor") | (ext == "btor2") => {
            let btor = Btor::from_file(&chk.model);
            let mut fe = BtorFrontend::new(btor);
            fe.set_skip_simp(chk.skip_simp);
            Box::new(fe)
        }
        _ => {
            error!("Unsupported file format. Supported extensions are: .aig, .aag, .btor, .btor2.");
            exit(1);
        }
    };
    let log_tracer = Box::new(LogTracer::new(cfg.as_ref()));
    let mut engine: Box<dyn Engine> = if cfg.is_wl() {
        let (wts, _symbols) = frontend.wts();
        // info!("origin ts has {}", ts.statistic());
        create_wl_engine(cfg.clone(), wts)
    } else {
        let (ts, symbols) = frontend.ts();
        info!("origin ts has {}", ts.statistic());
        create_bl_engine(cfg.clone(), ts, symbols)
    };
    engine.add_tracer(log_tracer);
    interrupt_statistic(&chk, engine.as_mut());
    let res = engine.check();
    engine.statistic();
    match res {
        McResult::Safe => {
            certificate(&chk, frontend.as_mut(), engine.as_mut(), true);
        }
        McResult::Unsafe(_) => {
            certificate(&chk, frontend.as_mut(), engine.as_mut(), false);
        }
        McResult::Unknown(_) => todo!(),
    }
    let ret = report_res(&chk, res);
    if chk.certify {
        assert!(certificate_check(&chk.model, chk.cert.as_ref().unwrap()));
    }
    drop(tmp_cert);
    ret
}

fn interrupt_statistic(chk: &CheckConfig, engine: &mut dyn Engine) {
    if chk.interrupt_statistic {
        let e: [usize; 2] = unsafe { transmute(engine as *mut dyn Engine) };
        let _ = ctrlc::set_handler(move || {
            let e: *mut dyn Engine = unsafe { transmute(e) };
            let e = unsafe { &mut *e };
            e.statistic();
            exit(124);
        });
    }
}

pub fn certificate(
    chk: &CheckConfig,
    frontend: &mut dyn Frontend,
    engine: &mut dyn Engine,
    res: bool,
) {
    if chk.cert.is_none() {
        return;
    }
    let cert = if res {
        frontend.safe_certificate(engine.proof())
    } else {
        let witness = engine.witness();
        frontend.unsafe_certificate(witness)
    };
    fs::write(chk.cert.as_ref().unwrap(), format!("{cert}")).unwrap();
}

pub fn portfolio_main(chk: CheckConfig, cfg: PortfolioConfig) -> u8 {
    let mut engine = Portfolio::new(chk.model.clone(), chk.cert.clone(), cfg);
    let res = engine.check();
    let res = report_res(&chk, res);
    if chk.certify {
        assert!(certificate_check(&chk.model, chk.cert.as_ref().unwrap()));
    }
    res
}
