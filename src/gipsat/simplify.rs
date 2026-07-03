use super::{
    DagCnfSolver,
    cdb::{CREF_NONE, CRef},
};
use logicrs::nckvec::NckVec;
use logicrs::{Lbool, LitOrdVec, LitVec, VarMap};
use std::mem::take;

#[derive(Clone)]
pub struct Simplify {
    pub last_num_assign: usize,
    pub last_simplify: usize,
    pub last_num_lemma: usize,
}

impl Default for Simplify {
    fn default() -> Self {
        Self {
            last_num_assign: 0,
            last_simplify: 0,
            last_num_lemma: 1000,
        }
    }
}

impl DagCnfSolver {
    pub fn simplify(&mut self) {
        debug_assert!(self.highest_level() == 0);
        debug_assert!(self.propagate() == CREF_NONE);
        // param finetune: 100 1000
        if self.statistic.num_solve <= self.simplify.last_simplify + 100 {
            return;
        }
        if self.simplify.last_num_assign < self.trail.len() {
            debug_assert!(self.highest_level() == 0);
            let lemmas = take(&mut self.cdb.lemmas);
            self.cdb.lemmas = self.simplify_satisfied_clauses(lemmas);
            let learnt = take(&mut self.cdb.learnt);
            self.cdb.learnt = self.simplify_satisfied_clauses(learnt);
            let trans = take(&mut self.cdb.trans);
            self.cdb.trans = self.simplify_satisfied_clauses(trans);
            self.simplify.last_num_assign = self.trail.len();
        }
        if self.simplify.last_num_lemma + 1000 < self.cdb.lemmas.len() {
            let lemmas = take(&mut self.cdb.lemmas);
            self.cdb.lemmas = self.simplify_subsume(lemmas);
            self.simplify.last_num_lemma = self.cdb.lemmas.len();
        }
        self.garbage_collect();
        self.simplify.last_simplify = self.statistic.num_solve;
    }

    pub fn simplify_satisfied_clauses(&mut self, mut clauses: NckVec<CRef>) -> NckVec<CRef> {
        let mut i = 0;
        'm: while i < clauses.len() {
            let cid = clauses[i];
            let mut cls = self.cdb.get(cid);
            let mut j = 0;
            while j < cls.len() {
                match self.value.v(cls[j]) {
                    Lbool::TRUE => {
                        clauses.swap_remove(i);
                        self.detach_clause(cid);
                        continue 'm;
                    }
                    Lbool::FALSE => {
                        if j <= 1 {
                            debug_assert!(
                                cls.slice().iter().any(|&l| self.value.v(l) == Lbool::TRUE)
                            );
                            clauses.swap_remove(i);
                            self.detach_clause(cid);
                            continue 'm;
                        } else {
                            cls.swap_remove(j);
                        }
                    }
                    _ => {
                        j += 1;
                    }
                }
            }
            i += 1;
        }
        clauses
    }

    fn simplify_subsume(&mut self, clauses: NckVec<CRef>) -> NckVec<CRef> {
        let mut clauses: Vec<(CRef, LitOrdVec)> = clauses
            .into_iter()
            .filter_map(|cref| {
                let cls = self.cdb.get(cref);
                if cls.len() > 100 {
                    None
                } else {
                    let lemma = LitOrdVec::new(LitVec::from(cls.slice()));
                    Some((cref, lemma))
                }
            })
            .collect();
        clauses.sort_by_key(|(_, l)| l.len());
        let mut occurs: VarMap<Vec<usize>> = VarMap::new_with(self.dc.max_var());
        for (i, cls) in clauses.iter().enumerate() {
            for l in cls.1.iter() {
                occurs[l.var()].push(i);
            }
        }
        for cls_idx in 0..clauses.len() {
            let cls = self.cdb.get(clauses[cls_idx].0);
            if cls.is_removed() {
                continue;
            }
            let max_occurs = *clauses[cls_idx]
                .1
                .iter()
                .min_by_key(|l| occurs[**l].len())
                .unwrap();
            for subsumed in occurs[max_occurs].iter() {
                let lemma = &clauses[cls_idx].1;
                if *subsumed == cls_idx {
                    continue;
                }
                if self.cdb.get(clauses[*subsumed].0).is_removed() {
                    continue;
                }
                let (res, diff) = lemma.subsume_except_one(&clauses[*subsumed].1);
                if res {
                    self.detach_clause(clauses[*subsumed].0);
                    self.statistic.num_simplify_subsume += 1;
                } else if let Some(diff) = diff {
                    self.statistic.num_simplify_self_subsume += 1;
                    if lemma.len() == clauses[*subsumed].1.len() {
                        if lemma.len() > 2 {
                            self.detach_clause(clauses[*subsumed].0);
                            self.strengthen_clause(clauses[cls_idx].0, diff);
                            let mut strengthen = clauses[cls_idx].1.as_litvec().clone();
                            strengthen.retain(|l| *l != diff);
                            clauses[cls_idx].1 = LitOrdVec::ordered_new(strengthen);
                        } else {
                            // println!("{}", lemma);
                            // println!("{}", clauses[*subsumed].1);
                            // println!("{}", diff);
                        }
                    } else {
                        self.strengthen_clause(clauses[*subsumed].0, !diff);
                        let mut strengthen = clauses[*subsumed].1.as_litvec().clone();
                        strengthen.retain(|l| *l != !diff);
                        clauses[*subsumed].1 = LitOrdVec::ordered_new(strengthen);
                    }
                }
            }
        }
        clauses
            .into_iter()
            .map(|(cref, _)| cref)
            .filter(|cref| !self.cdb.get(*cref).is_removed())
            .collect()
    }
}
