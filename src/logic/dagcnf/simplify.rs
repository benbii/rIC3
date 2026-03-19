use super::DagCnf;
use crate::{
    LitMap, LitOrdVec, LitVec, LitVvec, Var, VarAssign, VarMap, VarRange,
    lemmas_subsume_simplify, occur::Occurs,
};
use ahash::HashSet;
use crate::nckvec::NckVec;
use log::debug;
use std::{
    cmp::Reverse,
    collections::BinaryHeap,
    iter::once,
    time::{Duration, Instant},
};

pub struct DagCnfSimplify {
    cdb: NckVec<(LitOrdVec, bool)>,
    max_var: Var,
    cnf: LitMap<Vec<usize>>,
    #[allow(clippy::type_complexity)]
    occur: Option<(Occurs<LitOrdVec>, VarMap<u32>, BinaryHeap<(Reverse<usize>, Reverse<Var>, u32)>)>,
    frozen: HashSet<Var>,
    value: VarAssign,
    num_ocls: usize,
    time: Duration,
}

impl DagCnfSimplify {
    pub fn new(dagcnf: &DagCnf) -> Self {
        let num_ocls = dagcnf.num_clause();
        let cdb = NckVec::new();
        let max_var = dagcnf.max_var;
        let cnf = LitMap::new_with(max_var);
        let value = VarAssign::new_with(max_var);
        let mut res = Self {
            cdb,
            occur: None,
            max_var,
            cnf,
            frozen: HashSet::from_iter([Var::CONST]),
            value,
            num_ocls,
            time: Duration::default(),
        };
        for v in VarRange::new_inclusive(Var::CONST, max_var) {
            for mut cls in dagcnf.cnf[v].clone() {
                cls.sort();
                cls.dedup();
                assert!(cls.last().var().eq(&v));
                res.add_rel(cls);
            }
        }
        res
    }

    fn enable_occur(&mut self) {
        if self.occur.is_none() {
            let mut occur = Occurs::new_with(self.max_var);
            for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
                for &cls in self.cnf[v.lit()].iter().chain(self.cnf[!v.lit()].iter()) {
                    for &l in self.cdb[cls].0.iter() {
                        let lv = l.var();
                        if lv != v {
                            occur.add(l, cls);
                        }
                    }
                }
            }
            let mut queue_ver = VarMap::new_with(self.max_var);
            let mut qbve = BinaryHeap::new();
            for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
                let score = occur.num_occur(v.lit()) + occur.num_occur(!v.lit());
                queue_ver[v] += 1;
                qbve.push((Reverse(score), Reverse(v), queue_ver[v]));
            }
            self.occur = Some((occur, queue_ver, qbve));
        }
    }

    fn disable_occur(&mut self) {
        if self.occur.is_some() {
            self.occur = None;
        }
    }

    pub fn froze(&mut self, v: Var) {
        self.frozen.insert(v);
    }

    fn add_rel(&mut self, rel: LitVec) {
        let Some(rel) = rel.ordered_simp(&self.value) else {
            return;
        };
        let rel = LitOrdVec::new(rel);
        let n = rel.last();
        if rel.len() == 1 {
            assert!(!self.value.v(n).is_true());
            self.value.set(n);
        }
        self.cdb.push((rel, false));
        let relid = self.cdb.len() - 1;
        self.cnf[n].push(relid);
        if let Some((occur, queue_ver, qbve)) = &mut self.occur {
            for &l in self.cdb[relid].0.iter() {
                let lv = l.var();
                if lv != n.var() {
                    occur.add(l, relid);
                    let score = occur.num_occur(lv.lit()) + occur.num_occur(!lv.lit());
                    queue_ver[lv] += 1;
                    qbve.push((Reverse(score), Reverse(lv), queue_ver[lv]));
                }
            }
        }
    }

    fn remove_rels(&mut self, rels: Vec<usize>) {
        let relset = HashSet::from_iter(rels.iter().copied());
        let outs = HashSet::from_iter(rels.iter().map(|&cls| self.cdb[cls].0.last()));
        for o in outs {
            let mut i = 0;
            while i < self.cnf[o].len() {
                if relset.contains(&self.cnf[o][i]) {
                    let cls = self.cnf[o].swap_remove(i);
                    if let Some((occur, queue_ver, qbve)) = &mut self.occur {
                        for &l in self.cdb[cls].0.iter() {
                            let lv = l.var();
                            if lv != o.var() {
                                occur.del(l, cls);
                                let score = occur.num_occur(lv.lit()) + occur.num_occur(!lv.lit());
                                queue_ver[lv] += 1;
                                qbve.push((Reverse(score), Reverse(lv), queue_ver[lv]));
                            }
                        }
                    }
                    self.cdb[cls].1 = true;
                } else {
                    i += 1;
                }
            }
        }
    }

    #[inline]
    fn remove_node(&mut self, n: Var) {
        let ln = n.lit();
        if let Some((occur, _, _)) = &mut self.occur {
            assert!(occur.num_occur(ln) == 0 && occur.num_occur(!ln) == 0);
        }
        for &cls in self.cnf[ln].iter().chain(self.cnf[!ln].iter()) {
            if let Some((occur, queue_ver, qbve)) = &mut self.occur {
                for &l in self.cdb[cls].0.iter() {
                    let lv = l.var();
                    if lv != n {
                        occur.del(l, cls);
                        let score = occur.num_occur(lv.lit()) + occur.num_occur(!lv.lit());
                        queue_ver[lv] += 1;
                        qbve.push((Reverse(score), Reverse(lv), queue_ver[lv]));
                    }
                }
            }
            self.cdb[cls].1 = true;
        }
        self.cnf[ln].clear();
        self.cnf[!ln].clear();
    }

    fn var_rels(&self, v: Var) -> Vec<usize> {
        self.cnf[v.lit()]
            .iter()
            .chain(self.cnf[!v.lit()].iter())
            .copied()
            .collect()
    }

    fn resolvent(
        &self,
        pcnf: &[usize],
        ncnf: &[usize],
        pivot: Var,
        limit: usize,
    ) -> Option<LitVvec> {
        let mut res = LitVvec::new();
        for &pcls in pcnf {
            for &ncls in ncnf {
                if let Some(resolvent) = self.cdb[pcls].0.ordered_resolvent(&self.cdb[ncls].0, pivot) {
                    res.push(resolvent);
                }
                if res.len() > limit {
                    return None;
                }
            }
        }
        Some(res)
    }

    fn eliminate(&mut self, v: Var) {
        if self.frozen.contains(&v) {
            return;
        }
        let lv = v.lit();
        let occur = &mut self.occur.as_mut().unwrap().0;
        let ocost =
            occur.num_occur(lv) + occur.num_occur(!lv) + self.cnf[lv].len() + self.cnf[!lv].len();
        if ocost == 0 || ocost > 2000 {
            return;
        }
        let (pos, neg) = (self.cnf[lv].clone(), self.cnf[!lv].clone());
        let mut ncost = 0;
        let mut opos = occur.get(lv, &self.cdb).to_vec();
        let oneg = occur.get(!lv, &self.cdb).to_vec();
        let Some(respn) = self.resolvent(&pos, &oneg, v, ocost - ncost) else {
            return;
        };
        ncost += respn.len();
        if ncost > ocost {
            return;
        }
        let Some(resnp) = self.resolvent(&neg, &opos, v, ocost - ncost) else {
            return;
        };
        ncost += resnp.len();
        if ncost > ocost {
            return;
        }
        let mut res = respn;
        res.extend(resnp);
        let res = clause_subsume_simplify(res);
        opos.extend(oneg);
        self.remove_rels(opos);
        self.remove_node(v);
        for r in res {
            self.add_rel(r);
        }
    }

    pub fn bve_simplify(&mut self) {
        let start = Instant::now();
        self.enable_occur();
        while let Some((Reverse(score), Reverse(v), ver)) = self.occur.as_mut().unwrap().2.pop() {
            let (occur, queue_ver, _) = self.occur.as_mut().unwrap();
            let current = occur.num_occur(v.lit()) + occur.num_occur(!v.lit());
            if queue_ver[v] != ver || current != score {
                continue;
            }
            self.eliminate(v);
        }
        self.time += start.elapsed();
    }

    fn cls_subsume_check(&mut self, ci: usize) {
        if self.cdb[ci].1 {
            return;
        }
        let occur = &mut self.occur.as_mut().unwrap().0;
        let best_lit = *self.cdb[ci]
            .0
            .iter()
            .min_by_key(|&&l| {
                occur.num_occur(l) + occur.num_occur(!l) + self.cnf[l].len() + self.cnf[!l].len()
            })
            .unwrap();
        let mut occurs = occur.get(best_lit, &self.cdb).to_vec();
        occurs.extend_from_slice(occur.get(!best_lit, &self.cdb));
        occurs.extend(self.cnf[best_lit].iter());
        occurs.extend(self.cnf[!best_lit].iter());
        for cj in occurs {
            if self.cdb[cj].1 {
                continue;
            }
            if cj == ci {
                continue;
            }
            let (res, diff) = self.cdb[ci].0.subsume_execpt_one(&self.cdb[cj].0);
            if res {
                self.cnf[self.cdb[cj].0.last()].retain(|&c| c != cj);
                self.cdb[cj].1 = true;
                continue;
            } else if let Some(diff) = diff {
                if self.cdb[ci].0.len() == self.cdb[cj].0.len() {
                    if diff.var() == self.cdb[ci].0.last().var() {
                        let ci_last = self.cdb[ci].0.last();
                        let cj_last = self.cdb[cj].0.last();
                        self.cdb[ci].1 = true;
                        self.cdb[cj].1 = true;
                        self.cnf[ci_last].retain(|&c| c != ci);
                        self.cnf[cj_last].retain(|&c| c != cj);
                        return;
                    }
                    let mut cube = self.cdb[ci].0.as_litvec().clone();
                    cube.retain(|l| *l != diff);
                    self.cdb[ci].0 = LitOrdVec::new(cube);
                    self.cnf[self.cdb[cj].0.last()].retain(|&c| c != cj);
                    self.cdb[cj].1 = true;
                } else if diff.var() == self.cdb[cj].0.last().var() {
                    self.cnf[self.cdb[cj].0.last()].retain(|&c| c != cj);
                    self.cdb[cj].1 = true;
                } else {
                    let mut cube = self.cdb[cj].0.as_litvec().clone();
                    assert!(cube.last() == self.cdb[cj].0.last());
                    cube.retain(|l| *l != !diff);
                    self.cdb[cj].0 = LitOrdVec::new(cube);
                }
            }
        }
    }

    pub fn subsume_simplify(&mut self) {
        let start = Instant::now();
        self.enable_occur();
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            for cls in self.cnf[v.lit()].clone() {
                self.cls_subsume_check(cls);
            }
            for cls in self.cnf[!v.lit()].clone() {
                self.cls_subsume_check(cls);
            }
        }
        self.disable_occur();
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            self.cnf[v.lit()].retain(|&c| !self.cdb[c].1);
            self.cnf[!v.lit()].retain(|&c| !self.cdb[c].1);
        }
        self.time += start.elapsed();
    }

    fn const_simp_var(&mut self, v: Var) {
        let cls = self.var_rels(v);
        let mut removed = Vec::new();
        for c in cls {
            let cls = self.cdb[c].0.clone();
            if let Some(scls) = cls.ordered_simp(&self.value) {
                if scls.last().var() != v {
                    removed.push(c);
                } else if cls.len() != scls.len() {
                    self.add_rel(scls);
                }
            } else {
                removed.push(c);
            }
        }
        self.remove_rels(removed);
    }

    pub fn const_simplify(&mut self) {
        let start = Instant::now();
        self.disable_occur();
        for v in VarRange::new_inclusive(Var(1), self.max_var) {
            self.const_simp_var(v);
        }
        for v in VarRange::new_inclusive(Var(1), self.max_var) {
            let ln = v.lit();
            let vv = self.value.v(ln);
            if !vv.is_none() {
                self.remove_node(v);
                if self.frozen.contains(&v) {
                    self.add_rel(LitVec::from(ln.not_if(vv.is_false())));
                }
            }
        }
        self.time += start.elapsed();
    }

    pub fn finalize(&mut self) -> DagCnf {
        let start = Instant::now();
        let mut dagcnf = DagCnf::new();
        dagcnf.new_var_to(self.max_var);
        for v in VarRange::new_inclusive(Var(1), self.max_var) {
            let mut cnf: Vec<_> = self.cnf[v.lit()]
                .iter()
                .chain(self.cnf[!v.lit()].iter())
                .map(|&cls| {
                    assert!(!self.cdb[cls].1);
                    self.cdb[cls].0.as_litvec().clone()
                })
                .collect();
            if self.frozen.contains(&v)
                && let Some(vl) = self.value.vl(v)
            {
                cnf.clear();
                cnf.push(LitVec::from(vl));
            }
            dagcnf.add_rel(v, &cnf);
        }
        self.time += start.elapsed();
        debug!(
            "dagcnf simplified from {} to {} clauses in {:.2}s",
            self.num_ocls,
            dagcnf.num_clause(),
            self.time.as_secs_f64()
        );
        dagcnf
    }

    pub fn simplify(&mut self) -> DagCnf {
        self.const_simplify();
        self.bve_simplify();
        self.subsume_simplify();
        self.finalize()
    }
}

fn clause_subsume_simplify(lemmas: LitVvec) -> LitVvec {
    let lemmas: Vec<LitOrdVec> = lemmas.into_iter().map(LitOrdVec::new).collect();
    let lemmas = lemmas_subsume_simplify(lemmas);
    lemmas
        .into_iter()
        .map(|l| LitVec::from(l.as_litvec().as_slice()))
        .collect()
}

impl DagCnf {
    pub fn simplify(&self, frozen: impl IntoIterator<Item = impl AsRef<Var>>) -> Self {
        let mut simp = DagCnfSimplify::new(self);
        for v in frozen
            .into_iter()
            .map(|l| *l.as_ref())
            .chain(once(Var::CONST))
        {
            simp.froze(v);
        }
        simp.simplify()
    }
}

#[cfg(test)]
mod test {
    use crate::{DagCnf, Lit, Var, VarRange, simplify::DagCnfSimplify};

    #[test]
    fn test0() {
        let mut dc = DagCnf::new();
        dc.new_var_to(Var(4));
        dc.new_and([Lit::from(1), Lit::from(2), Lit::from(3)]);
        dc.new_and([Lit::from(1), Lit::from(2), Lit::from(3), Lit::from(4)]);
        println!("{dc}");
        let mut simp = DagCnfSimplify::new(&dc);
        for v in VarRange::new_inclusive(Var::CONST, dc.max_var()) {
            simp.froze(v);
        }
        let ndc = simp.simplify();
        println!("{ndc}");
    }
}
