use crate::gipsat::{inductive, inductive_core};
use crate::ic3::{Frame, IC3};
// use log::error;
use logicrs::{LitOrdVec, LitVec};
// use nix::libc;
use rand::seq::SliceRandom;
// use std::{fs::OpenOptions, io::Write, os::fd::AsRawFd};

impl IC3 {
    pub fn propagate(&mut self, from: Option<usize>) -> bool {
        let level = self.level();
        let from = from.unwrap_or(self.frame.early).max(1);
        for frame_idx in from..level {
            self.frame[frame_idx].sort_by_key(|(x, _)| x.len());
            let frame = self.frame[frame_idx].clone();
            for mut lemma in frame {
                // HELP: semantic difference here? Is only .0 compared before?
                if self.frame[frame_idx].iter().all(|l| l.ne(&lemma)) {
                    continue;
                }
                for ctp in 0..3 {
                    let (blocked, ordered_cube) =
                        self.blocked_with_ordered(frame_idx + 1, &lemma.0, false);
                    if blocked {
                        let core =
                            inductive_core(&mut self.solvers[frame_idx], &self.ts, &ordered_cube)
                                .unwrap_or(ordered_cube);
                        if let Some(po) = &mut lemma.1
                            && po.frame < frame_idx + 2
                            && self.obligations.remove(po)
                        {
                            po.push_to(frame_idx + 2);
                            self.obligations.add(po.clone());
                        }
                        self.add_lemma(frame_idx + 1, core, true, lemma.1);
                        self.statistic.ctp.statistic(ctp > 0);
                        break;
                    }
                    if !self.ctp {
                        break;
                    }
                    let (ctp, _) = self.get_pred(frame_idx + 1, false);
                    if !self.ts.cube_subsume_init(&ctp)
                        && inductive(&mut self.solvers[frame_idx - 1], &self.ts, &ctp, true)
                    {
                        let core =
                            inductive_core(&mut self.solvers[frame_idx - 1], &self.ts, &ctp)
                                .unwrap();
                        let mic = self.mic(frame_idx, core, &[], Default::default());
                        if self.add_lemma(frame_idx, mic, false, None) {
                            return true;
                        }
                    } else {
                        break;
                    }
                }
            }
            if self.frame[frame_idx].is_empty() {
                return true;
            }
        }
        self.frame.early = self.level();
        false
    }

    pub fn propagete_to_inf_rec(
        &mut self,
        lastf: &mut Frame,
        ctp: LitVec,
        // dump_buf: &mut Vec<u8>,
        // dump: bool,
    ) -> bool {
        let ctp = LitOrdVec::new(ctp);
        let Some(lidx) = lastf.iter().position(|(l, _)| l.subsume(&ctp)) else {
            return false;
        };
        let mut lemma = lastf.swap_remove(lidx);
        loop {
            if inductive(&mut self.inf_solver, &self.ts, &lemma.0, true) {
                if let Some(po) = &mut lemma.1 {
                    self.obligations.remove(po);
                }
                self.add_inf_lemma(lemma.0.as_litvec().clone());
                // if !dump {
                //     return true;
                // }
                // let mut nlits = 0u32;
                // let dump_start = dump_buf.len();
                // dump_buf.extend_from_slice(&0u32.to_le_bytes());
                // for lit in lemma.iter() {
                //     if lit.var().is_constant() {
                //         continue;
                //     }
                //     let var = i32::try_from(lit.var().0).unwrap();
                //     dump_buf.extend_from_slice(
                //         &(if lit.polarity() { var } else { -var }).to_le_bytes(),
                //     );
                //     nlits += 1;
                // }
                // dump_buf[dump_start..dump_start + 4].copy_from_slice(&nlits.to_le_bytes());
                return true;
            } else {
                let target = self.ts.lits_next(lemma.0.as_litvec());
                let (ctp, _) = self.lift.lift(
                    &mut self.inf_solver,
                    target.iter().chain(self.ts.constraint.iter()),
                    |i, _| i == 0,
                );
                if !self.propagete_to_inf_rec(lastf, ctp) {
                    // if !self.propagete_to_inf_rec(lastf, ctp, dump_buf, dump) {
                    return false;
                }
            }
        }
    }

    pub fn propagate_to_inf(&mut self) {
        let level = self.level();
        self.frame[level].shuffle(&mut self.rng);
        let mut lastf = self.frame[level].clone();
        // let dump = inv_dump_path.is_some();
        // let mut dump_buf = Vec::new();
        while let Some(mut lemma) = lastf.pop() {
            loop {
                if inductive(&mut self.inf_solver, &self.ts, &lemma.0, true) {
                    if let Some(po) = &mut lemma.1 {
                        self.obligations.remove(po);
                    }
                    self.add_inf_lemma(lemma.0.as_litvec().clone());
                    // if !dump {
                    //     break;
                    // }
                    // let mut nlits = 0u32;
                    // let dump_start = dump_buf.len();
                    // dump_buf.extend_from_slice(&0u32.to_le_bytes());
                    // for lit in lemma.iter() {
                    //     if lit.var().is_constant() {
                    //         continue;
                    //     }
                    //     let var = i32::try_from(lit.var().0).unwrap();
                    //     dump_buf.extend_from_slice(
                    //         &(if lit.polarity() { var } else { -var }).to_le_bytes(),
                    //     );
                    //     nlits += 1;
                    // }
                    // debug_assert!(dump_buf.len() >= dump_start + 4); // due to extend_from_slice
                    // dump_buf[dump_start..dump_start + 4].copy_from_slice(&nlits.to_le_bytes());
                    break;
                } else {
                    let target = self.ts.lits_next(lemma.0.as_litvec());
                    let (ctp, _) = self.lift.lift(
                        &mut self.inf_solver,
                        target.iter().chain(self.ts.constraint.iter()),
                        |i, _| i == 0,
                    );
                    // if !self.propagete_to_inf_rec(&mut lastf, ctp, &mut dump_buf, dump) {
                    if !self.propagete_to_inf_rec(&mut lastf, ctp) {
                        break;
                    }
                }
            }
        }

        // if dump_buf.is_empty() {
        //     return;
        // }
        // let path = inv_dump_path.as_ref().unwrap();
        // if let Err(err) = (|| -> std::io::Result<()> {
        //     let mut file = OpenOptions::new().create(true).append(true).open(path)?;
        //     let lock_rc = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX) };
        //     if lock_rc != 0 {
        //         return Err(std::io::Error::last_os_error());
        //     }
        //     file.write_all(&dump_buf)?;
        //     file.sync_data()?;
        //     let _ = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_UN) };
        //     Ok(())
        // })() {
        //     error!("cannot append invariant dump {:?}: {:?}", path, err);
        // }
    }
}
