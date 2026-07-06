use super::{IC3, proofoblig::ProofObligation, solver::inductive};
use crate::transys::Transys;
use logicrs::{Lit, LitOrdVec, LitSet, LitVec, Var, satif::Satif};
use std::{
    fmt::Write,
    ops::{Deref, DerefMut},
};

pub type Frame = Vec<(LitOrdVec, Option<ProofObligation>)>;

pub struct Frames {
    frames: Vec<Frame>,
    pub inf: Frame,
    pub early: usize,
    tmp_lit_set: LitSet,
}

impl Frames {
    pub fn new(ts: &Transys) -> Self {
        let mut tmp_lit_set = LitSet::new();
        tmp_lit_set.reserve(ts.latch.iter().copied().max().unwrap_or(Var::CONST));
        Self {
            frames: Default::default(),
            inf: Default::default(),
            early: 1,
            tmp_lit_set,
        }
    }

    pub fn trivial_contained<'a>(
        &'a mut self,
        frame: Option<usize>,
        lemma: &LitOrdVec,
    ) -> Option<(Option<usize>, &'a mut Option<ProofObligation>)> {
        for l in lemma.iter() {
            self.tmp_lit_set.insert(*l);
        }
        if let Some(frame) = frame {
            for (i, fi) in self.frames.iter_mut().enumerate().skip(frame) {
                for j in 0..fi.len() {
                    if fi[j].0.subsume_set(lemma, &self.tmp_lit_set) {
                        self.tmp_lit_set.clear();
                        return Some((Some(i), &mut fi[j].1));
                    }
                }
            }
        }
        for j in 0..self.inf.len() {
            if self.inf[j].0.subsume_set(lemma, &self.tmp_lit_set) {
                self.tmp_lit_set.clear();
                return Some((None, &mut self.inf[j].1));
            }
        }
        self.tmp_lit_set.clear();
        None
    }

    pub fn parent_lemma(&self, lemma: &[Lit], frame: usize) -> Option<LitOrdVec> {
        if frame == 1 {
            return None;
        }
        let lemma = LitOrdVec::new(LitVec::from(lemma));
        for (c, _) in self.frames[frame - 1].iter() {
            if c.subsume(&lemma) {
                return Some(c.clone());
            }
        }
        None
    }

    pub fn statistic(&self, compact: bool) -> String {
        let mut s = String::new();
        let total = self.frames.len() + 1;
        s.write_fmt(format_args!("frames [{total}]: ")).unwrap();
        let frames_iter: Box<dyn Iterator<Item = &Frame>> = if compact && total > 50 {
            s.push_str("... ");
            Box::new(self.frames.iter().skip(total - 50))
        } else {
            Box::new(self.frames.iter())
        };
        for f in frames_iter {
            s.write_fmt(format_args!("{} ", f.len())).unwrap();
        }
        s.write_fmt(format_args!("{} ", self.inf.len())).unwrap();
        s
    }
}

impl Deref for Frames {
    type Target = Vec<Frame>;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.frames
    }
}
impl DerefMut for Frames {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}
impl Frames {
    #[inline]
    pub fn get_mut(&mut self) -> &mut Vec<Frame> {
        &mut self.frames
    }
}

impl IC3 {
    pub(super) fn add_lemma(
        &mut self,
        frame: usize,
        lemma: LitVec,
        contained_check: bool,
        po: Option<ProofObligation>,
    ) -> bool {
        let lemma = LitOrdVec::new(lemma);
        if frame == 0 {
            assert!(self.frame.len() == 1);
            if self.level() == frame
                && let Some(predprop) = self.predprop.as_mut()
            {
                predprop.add_lemma(&lemma);
            }
            self.solvers[0].add_clause(&!lemma.as_litvec());
            self.frame[0].push((lemma, po));
            return false;
        }
        if contained_check && self.frame.trivial_contained(Some(frame), &lemma).is_some() {
            return false;
        }
        let mut begin = None;
        let mut inv_found = false;
        'fl: for i in (1..=frame).rev() {
            let mut j = 0;
            while j < self.frame[i].len() {
                let (l, _) = &self.frame[i][j];
                if begin.is_none() && l.subsume(&lemma) {
                    if l.ne(&lemma) {
                        begin = Some(i + 1);
                        break 'fl;
                    }
                    self.frame[i].swap_remove(j);
                    let clause = !lemma.as_litvec();
                    for k in i + 1..=frame {
                        self.solvers[k].add_clause(&clause);
                    }
                    if self.level() == frame
                        && let Some(predprop) = self.predprop.as_mut()
                    {
                        predprop.add_lemma(&lemma);
                    }
                    self.frame[frame].push((lemma, po));
                    self.frame.early = self.frame.early.min(i + 1);
                    return self.frame[i].is_empty();
                }
                if lemma.subsume(&l) {
                    let _ = self.frame[i].swap_remove(j);
                    // self.solvers[i].remove_lemma(&remove);
                    continue;
                }
                j += 1;
            }
            if i != frame && self.frame[i].is_empty() {
                inv_found = true;
            }
        }
        let clause = !lemma.as_litvec();
        let begin = begin.unwrap_or(1);
        for i in begin..=frame {
            self.solvers[i].add_clause(&clause);
        }
        if self.level() == frame
            && let Some(predprop) = self.predprop.as_mut()
        {
            predprop.add_lemma(&lemma);
        }
        self.frame[frame].push((lemma, po));
        self.frame.early = self.frame.early.min(begin);
        inv_found
    }

    pub(super) fn add_inf_lemma(&mut self, lemma: LitOrdVec) {
        assert!(self.frame.trivial_contained(None, &lemma).is_none());
        let lastf = self.frame.last_mut().unwrap();
        let olen = lastf.len();
        lastf.retain(|(l, _)| !l.eq(&lemma));
        assert!(lastf.len() + 1 == olen);
        let clause = !lemma.as_litvec();
        self.inf_solver.add_clause(&clause);
        self.frame.inf.push((lemma, None));
    }

    pub fn inner_invariant(&self) -> Vec<LitVec> {
        let mut invariants: Vec<_> = self
            .frame
            .inf
            .iter()
            .map(|(c, _)| c.as_litvec().clone())
            .collect();
        if let Some(invariant) = self.frame.iter().position(|frame| frame.is_empty()) {
            for i in invariant..self.frame.len() {
                for (cube, _) in self.frame[i].iter() {
                    invariants.push(cube.as_litvec().clone());
                }
            }
            return invariants;
        }

        let iter_max = 5;
        let mut cand: Vec<_> = self
            .frame
            .last()
            .unwrap()
            .iter()
            .map(|(l, _)| l.as_litvec().clone())
            .collect();
        for k in 0..=iter_max {
            if k == iter_max {
                return invariants;
            }
            let mut slv = self.ts.new_solver();
            for i in invariants.iter() {
                slv.add_clause(&!i);
            }
            for c in cand.iter() {
                slv.add_clause(&!c);
            }
            let mut new_cand = Vec::new();
            for c in cand.iter() {
                if inductive(&mut slv, &self.ts, c, false) {
                    new_cand.push(c.clone());
                }
            }
            if new_cand.len() == cand.len() {
                break;
            }
            cand = new_cand;
        }
        invariants.extend(cand);
        invariants
    }
}
