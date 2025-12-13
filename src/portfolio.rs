use crate::{Config, frontend::aig::certifaiger_check};
use log::{error, info};
use process_control::{ChildExt, Control};
use std::{
    env::current_exe,
    fs::{self, File},
    io::{Read, Write},
    mem::take,
    ops::{Deref, DerefMut},
    path::PathBuf,
    process::{Command, Stdio, exit},
    sync::{Arc, Condvar, Mutex},
    thread::spawn,
};
use tempfile::{NamedTempFile, TempDir};

enum PortfolioState {
    PreprocessPhase,
    Checking(usize),
    Finished(bool, String, Option<NamedTempFile>),
    Terminate,
}

impl PortfolioState {
    fn is_checking(&self) -> bool {
        matches!(self, Self::Checking(_))
    }

    fn result(&mut self) -> (bool, String, Option<NamedTempFile>) {
        let Self::Finished(res, config, certificate) = self else {
            panic!()
        };
        (*res, config.clone(), take(certificate))
    }
}

pub struct Portfolio {
    cfg: Config,
    engines: Vec<Command>,
    temp_dir: TempDir,
    engine_pids: Vec<i32>,
    certificate: Option<NamedTempFile>,
    state: Arc<(Mutex<PortfolioState>, Condvar)>,
    preproc_path: PathBuf,
    preproc_pid: Option<i32>,
}

impl Portfolio {
    pub fn new(cfg: Config) -> Self {
        let temp_dir = tempfile::TempDir::new_in("/tmp/rIC3/").unwrap();
        let temp_dir_path = temp_dir.path();
        let preproc_path = temp_dir_path.join("model.preproc");
        let mut engines = Vec::new();
        let mut id = 0;
        let mut new_engine = |args: &str| {
            let args = args.split(" ");
            let mut engine = Command::new(current_exe().unwrap());
            engine.env("RIC3_TMP_DIR", temp_dir_path);
            engine.env("RUST_LOG", "warn");
            engine.env("RIC3_WORKER", format!("worker{id}"));
            id += 1;
            engine.arg(&cfg.model);
            for a in args {
                engine.arg(a);
            }
            engines.push(engine);
        };
        new_engine("-e ic3 --rseed 1");
        new_engine("-e ic3 --preproc=false --rseed 2"); // NoPreproc worker
        new_engine("-e ic3 --ic3-drop-po=false --ic3-parent-lemma=false --rseed 3");
        new_engine("-e ic3 --ic3-abs-cst --rseed 4");
        new_engine("-e ic3 --ic3-abs-cst --ic3-abs-trans --rseed 5");
        new_engine(
            "-e ic3 --ic3-abs-cst --ic3-abs-trans --ic3-dynamic --ic3-drop-po=false --rseed 6",
        );
        new_engine("-e ic3 --ic3-ctg-max 5 --ic3-ctg-limit 15 --ic3-drop-po=false --rseed 7");
        new_engine("-e ic3 --ic3-inn --rseed 8");
        new_engine("-e ic3 --ic3-inn --ic3-ctp --rseed 9");
        new_engine("-e ic3 --ic3-inn --ic3-ctg=false --rseed 10");
        new_engine("-e ic3 --ic3-inn --ic3-dynamic --ic3-drop-po=false --rseed 11");
        new_engine("-e bmc --step 1 --rseed 12");
        new_engine("-e bmc --bmc-kissat --step 10 --rseed 13");
        new_engine("-e bmc --bmc-kissat --step 65 --rseed 14");
        new_engine("-e bmc --bmc-kissat --bmc-dyn-step --rseed 15");
        new_engine("-e kind --step 1 --rseed 16");
        let ps = PortfolioState::PreprocessPhase;
        Self {
            cfg,
            engines,
            temp_dir,
            certificate: None,
            engine_pids: Default::default(),
            state: Arc::new((Mutex::new(ps), Condvar::new())),
            preproc_path,
            preproc_pid: None,
        }
    }

    pub fn terminate(&mut self) {
        let Ok(mut lock) = self.state.0.try_lock() else {
            return;
        };
        if lock.is_checking() {
            *lock = PortfolioState::Terminate;

            // Kill preprocessor if running
            if let Some(preproc_pid) = self.preproc_pid {
                let _ = Command::new("kill")
                    .args(["-9", &preproc_pid.to_string()])
                    .output();
            }

            let pids: Vec<String> = self.engine_pids.iter().map(|p| format!("{}", *p)).collect();
            let pid = pids.join(",");
            let _ = Command::new("pkill")
                .args(["-9", "--parent", &pid])
                .output();
            let mut kill = Command::new("kill");
            kill.arg("-9");
            for p in pids {
                kill.arg(p);
            }
            let _ = kill.output().unwrap();
            self.engine_pids.clear();
            let _ = Command::new("rm")
                .arg("-rf")
                .arg(self.temp_dir.path())
                .output();
        }
        drop(lock);
        // Clean up preproc file
        let _ = fs::remove_file(&self.preproc_path);
    }

    fn launch_worker(
        engine: &mut Command,
        wmem: usize,
        temp_dir: &TempDir,
        engine_pids: &mut Vec<i32>,
        state: Arc<(Mutex<PortfolioState>, Condvar)>,
        needs_certificate: bool,
    ) {
        let certificate = if needs_certificate {
            let certificate = tempfile::NamedTempFile::new_in(temp_dir.path()).unwrap();
            let certify_path = certificate.path().as_os_str().to_str().unwrap();
            engine.arg(certify_path);
            Some(certificate)
        } else {
            None
        };
        let mut child = engine.stderr(Stdio::piped()).spawn().unwrap();
        engine_pids.push(child.id() as i32);

        let config = engine
            .get_args()
            .skip(1)
            .map(|cstr| cstr.to_str().unwrap())
            .collect::<Vec<&str>>()
            .join(" ");
        info!("start engine: {config}");

        spawn(move || {
            #[cfg(target_os = "linux")]
            let status = child.controlled().memory_limit(wmem).wait().unwrap().unwrap();
            #[cfg(target_os = "macos")]
            let status = child.controlled().wait().unwrap().unwrap();

            let res = match status.code() {
                Some(10) => false,
                Some(20) => true,
                e => {
                    let mut ps = state.0.lock().unwrap();
                    if let PortfolioState::Checking(np) = ps.deref_mut() {
                        info!("{config} unexpectedly exited, exit code: {e:?}");
                        let mut stderr = String::new();
                        child.stderr.unwrap().read_to_string(&mut stderr).unwrap();
                        info!("{stderr}");
                        *np -= 1;
                        if *np == 0 {
                            state.1.notify_one();
                        }
                    }
                    return;
                }
            };
            let mut lock = state.0.lock().unwrap();
            if lock.is_checking() {
                *lock = PortfolioState::Finished(res, config, certificate);
                state.1.notify_one();
            }
        });
    }

    fn check_inner(&mut self) -> Option<bool> {
        #[cfg(target_os = "linux")]
        let wmem = self.cfg.portfolio.wmem_limit * 1024 * 1024 * 1024;

        // Start preprocessor
        let mut preproc_cmd = Command::new(current_exe().unwrap());
        preproc_cmd
            .arg(&self.cfg.model)
            .args(["--export-preproc", self.preproc_path.to_str().unwrap()])
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let preproc_child = preproc_cmd.spawn().unwrap();
        self.preproc_pid = Some(preproc_child.id() as i32);

        // Monitor preprocessor completion
        let state = self.state.clone();
        let preproc_path = self.preproc_path.clone();
        spawn(move || {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(100));
                if preproc_path.exists() {
                    let mut lock = state.0.lock().unwrap();
                    if matches!(*lock, PortfolioState::PreprocessPhase) {
                        *lock = PortfolioState::Checking(15);
                        state.1.notify_one();
                    }
                    return;
                }
            }
        });

        // Launch NoPreproc worker
        let needs_cert = self.cfg.certificate.is_some() || self.cfg.certify || self.cfg.witness;
        Self::launch_worker(
            &mut self.engines[1],
            wmem,
            &self.temp_dir,
            &mut self.engine_pids,
            self.state.clone(),
            needs_cert,
        );

        // Wait for preprocessor or NoPreproc worker
        let lock = self.state.0.lock().unwrap();
        let mut result = self.state.1.wait(lock).unwrap();

        match *result {
            PortfolioState::Finished(_, _, _) => {
                // NoPreproc won
                if let Some(pid) = self.preproc_pid.take() {
                    let _ = Command::new("kill").args(["-9", &pid.to_string()]).output();
                }
                let (res, config, certificate) = result.result();
                drop(result);
                self.certificate = certificate;
                info!("best configuration: {config}");
                self.cleanup_workers();
                return Some(res);
            }
            PortfolioState::Checking(_) => {
                drop(result);
                // Preprocessor won, launch remaining workers
                for idx in std::iter::once(0).chain(2..16) {
                    self.engines[idx].args(["--load-preproc", self.preproc_path.to_str().unwrap()]);
                    Self::launch_worker(
                        &mut self.engines[idx],
                        wmem,
                        &self.temp_dir,
                        &mut self.engine_pids,
                        self.state.clone(),
                        needs_cert,
                    );
                }
            }
            _ => return None,
        }

        // Wait for Phase 2 workers
        let lock = self.state.0.lock().unwrap();
        let mut result = self.state.1.wait(lock).unwrap();

        if let PortfolioState::Checking(np) = result.deref() {
            assert!(*np == 0);
            error!("all workers unexpectedly exited :(");
            return None;
        }
        let (res, config, certificate) = result.result();
        drop(result);
        self.certificate = certificate;
        info!("best configuration: {config}");
        self.cleanup_workers();
        Some(res)
    }

    fn cleanup_workers(&mut self) {
        let pids: Vec<String> = self.engine_pids.iter().map(|p| p.to_string()).collect();
        let _ = Command::new("pkill").args(["-9", "--parent", &pids.join(",")]).output();
        let _ = Command::new("kill").arg("-9").args(&pids).output();
        self.engine_pids.clear();
        let _ = fs::remove_file(&self.preproc_path);
    }

    pub fn check(&mut self) -> Option<bool> {
        let ric3 = self as *mut Self as usize;
        ctrlc::set_handler(move || {
            let ric3 = unsafe { &mut *(ric3 as *mut Portfolio) };
            ric3.terminate();
            exit(124);
        })
        .unwrap();
        self.check_inner()
    }
}

impl Drop for Portfolio {
    fn drop(&mut self) {
        let _ = Command::new("rm")
            .arg("-rf")
            .arg(self.temp_dir.path())
            .output();
    }
}

fn certificate(engine: &mut Portfolio, cfg: &Config, res: bool) {
    if res {
        if cfg.certificate.is_none() && !cfg.certify {
            return;
        }
        if let Some(certificate_path) = &cfg.certificate {
            std::fs::copy(engine.certificate.as_ref().unwrap(), certificate_path).unwrap();
        }
    } else {
        if cfg.certificate.is_none() && !cfg.certify && !cfg.witness {
            return;
        }
        let mut witness = String::new();
        File::open(
            engine
                .certificate
                .as_ref()
                .unwrap()
                .path()
                .as_os_str()
                .to_str()
                .unwrap(),
        )
        .unwrap()
        .read_to_string(&mut witness)
        .unwrap();
        if cfg.witness {
            println!("{witness}");
        }
        if let Some(certificate_path) = &cfg.certificate {
            let mut file: File = File::create(certificate_path).unwrap();
            file.write_all(witness.as_bytes()).unwrap();
        }
    }
    if cfg.certify {
        certifaiger_check(&cfg.model, engine.certificate.as_ref().unwrap().path());
    }
}

pub fn portfolio_main(cfg: Config) {
    let mut engine = Portfolio::new(cfg.clone());
    let res = engine.check();
    match res {
        Some(true) => {
            println!("RESULT: UNSAT");
            if cfg.witness {
                println!("0");
            }
            certificate(&mut engine, &cfg, true)
        }
        Some(false) => {
            println!("RESULT: SAT");
            certificate(&mut engine, &cfg, false)
        }
        _ => {
            println!("RESULT: UNKNOWN");
            if cfg.witness {
                println!("2");
            }
        }
    }
    if let Some(res) = res {
        exit(if res { 20 } else { 10 })
    } else {
        exit(30)
    }
}
