pub mod simplify;

use crate::RseedSet as HashSet;
use crate::{Lit, LitVec, Var, VarLMap, VarMap, VarRange, VarVMap};
use serde::{Deserialize, Serialize};
use std::{fmt::Display, iter::once, slice};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DagCnf {
    max_var: Var,
    cnf_pos: VarMap<(u32, u32)>,
    cnf_dat: Vec<u32>,
    dep_pos: VarMap<(u32, u32)>,
    dep_dat: Vec<Var>,
}

#[derive(Clone, Copy)]
pub struct DcnfIter<'a> {
    data: &'a [u32],
    pos: usize,
    rem: usize,
}

impl<'a> DcnfIter<'a> {
    #[inline]
    fn new(data: &'a [u32]) -> Self {
        Self {
            data,
            pos: usize::from(!data.is_empty()),
            rem: data.first().copied().unwrap_or_default() as usize,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.rem
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rem == 0
    }
}

impl<'a> Iterator for DcnfIter<'a> {
    type Item = &'a [Lit];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.rem == 0 {
            return None;
        }
        let len = self.data[self.pos] as usize;
        let begin = self.pos + 1;
        let end = begin + len;
        self.pos = end;
        self.rem -= 1;
        let w = &self.data[begin..end];
        Some(unsafe { slice::from_raw_parts(w.as_ptr() as *const Lit, w.len()) })
    }
}

impl ExactSizeIterator for DcnfIter<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.rem
    }
}

impl DagCnf {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.dep_pos.reserve(self.max_var);
        self.cnf_pos.reserve(self.max_var);
        self.max_var
    }

    #[inline]
    pub fn new_var_to(&mut self, n: Var) {
        while self.max_var < n {
            self.new_var();
        }
    }

    #[inline]
    pub fn max_var(&self) -> Var {
        self.max_var
    }

    #[inline]
    pub fn num_var(&self) -> usize {
        let n: usize = self.max_var().into();
        n + 1
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.cnf_pos
            .iter()
            .map(|&pos| clauses_from_pos(&self.cnf_dat, pos).len())
            .sum()
    }

    #[inline]
    pub fn all_clauses(&self) -> impl Iterator<Item = &[Lit]> + '_ {
        self.cnf_pos
            .iter()
            .flat_map(|&pos| clauses_from_pos(&self.cnf_dat, pos))
    }

    #[inline]
    pub fn clauses_of_var(&self, n: Var) -> DcnfIter<'_> {
        clauses_from_pos(&self.cnf_dat, self.cnf_pos[n])
    }

    #[inline]
    pub fn dep(&self, n: Var) -> &[Var] {
        let (start, len) = self.dep_pos[n];
        &self.dep_dat[start as usize..(start + len) as usize]
    }

    pub fn add_rel(&mut self, n: Var, rel: &[LitVec]) {
        if n.is_constant() {
            debug_assert!(rel.eq(&[LitVec::from(Lit::constant(true))]));
            return;
        }
        let total_lits: usize = rel.iter().map(|r| r.len()).sum();
        let (mut pos, end) = self.alloc_rel(n, rel.len(), 1 + rel.len() + total_lits);
        let mut deps = HashSet::default();
        let mut scratch = LitVec::new();
        for r in rel {
            scratch.clear();
            scratch.extend(r.iter().copied());
            scratch.sort();
            debug_assert!(scratch.last().var() == n);
            self.cnf_dat[pos] = scratch.len() as u32;
            pos += 1;
            for &l in scratch.iter() {
                deps.insert(l.var());
                self.cnf_dat[pos] = l.into();
                pos += 1;
            }
        }
        self.finish_rel(n, pos, end, deps);
    }

    pub fn del_rel(&mut self, n: Var) {
        self.new_var_to(n);
        self.cnf_pos[n] = (0, 0);
        self.dep_pos[n] = (0, 0);
    }

    pub fn add_cnf_and(&mut self, n: Lit, lits: &[Lit]) {
        let nvar = n.var();
        let (mut pos, end) = self.alloc_rel(nvar, lits.len() + 1, 4 * lits.len() + 3);
        let mut deps = HashSet::default();
        for &l in lits {
            self.write_fixed_clause(&mut pos, nvar, [!n, l], &mut deps);
        }
        self.cnf_dat[pos] = (lits.len() + 1) as u32;
        pos += 1;
        let begin = pos;
        self.cnf_dat[pos] = n.into();
        pos += 1;
        for &l in lits {
            self.cnf_dat[pos] = (!l).into();
            pos += 1;
        }
        self.cnf_dat[begin..pos].sort_unstable();
        debug_assert!(Lit(self.cnf_dat[pos - 1]).var() == nvar);
        for &raw in &self.cnf_dat[begin..pos] {
            deps.insert(Lit(raw).var());
        }
        self.finish_rel(nvar, pos, end, deps);
    }

    pub fn add_cnf_or(&mut self, n: Lit, lits: &[Lit]) {
        let nvar = n.var();
        let (mut pos, end) = self.alloc_rel(nvar, lits.len() + 1, 4 * lits.len() + 3);
        let mut deps = HashSet::default();
        for &l in lits {
            self.write_fixed_clause(&mut pos, nvar, [n, !l], &mut deps);
        }
        self.cnf_dat[pos] = (lits.len() + 1) as u32;
        pos += 1;
        let begin = pos;
        self.cnf_dat[pos] = (!n).into();
        pos += 1;
        for &l in lits {
            self.cnf_dat[pos] = l.into();
            pos += 1;
        }
        self.cnf_dat[begin..pos].sort_unstable();
        debug_assert!(Lit(self.cnf_dat[pos - 1]).var() == nvar);
        for &raw in &self.cnf_dat[begin..pos] {
            deps.insert(Lit(raw).var());
        }
        self.finish_rel(nvar, pos, end, deps);
    }

    pub fn add_cnf_xor(&mut self, n: Lit, x: Lit, y: Lit) {
        let nvar = n.var();
        let (mut pos, end) = self.alloc_rel(nvar, 4, 17);
        let mut deps = HashSet::default();
        self.write_fixed_clause(&mut pos, nvar, [!x, y, n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [x, !y, n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [x, y, !n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [!x, !y, !n], &mut deps);
        self.finish_rel(nvar, pos, end, deps);
    }

    pub fn add_cnf_xnor(&mut self, n: Lit, x: Lit, y: Lit) {
        let nvar = n.var();
        let (mut pos, end) = self.alloc_rel(nvar, 4, 17);
        let mut deps = HashSet::default();
        self.write_fixed_clause(&mut pos, nvar, [!x, y, !n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [x, !y, !n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [x, y, n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [!x, !y, n], &mut deps);
        self.finish_rel(nvar, pos, end, deps);
    }

    pub fn add_cnf_ite(&mut self, n: Lit, c: Lit, t: Lit, e: Lit) {
        let nvar = n.var();
        let (mut pos, end) = self.alloc_rel(nvar, 4, 17);
        let mut deps = HashSet::default();
        self.write_fixed_clause(&mut pos, nvar, [t, !c, !n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [!t, !c, n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [e, c, !n], &mut deps);
        self.write_fixed_clause(&mut pos, nvar, [!e, c, n], &mut deps);
        self.finish_rel(nvar, pos, end, deps);
    }

    pub fn new_and(&mut self, ands: impl IntoIterator<Item = impl AsRef<Lit>>) -> Lit {
        let mut and = Vec::new();
        for a in ands.into_iter() {
            let a = a.as_ref();
            if a.is_constant(true) {
                continue;
            }
            if a.is_constant(false) {
                return Lit::constant(false);
            }
            and.push(*a);
        }
        if and.is_empty() {
            Lit::constant(true)
        } else if and.len() == 1 {
            and[0]
        } else {
            let n = self.new_var().lit();
            self.add_cnf_and(n, &and);
            n
        }
    }

    pub fn new_or(&mut self, ors: impl IntoIterator<Item = impl AsRef<Lit>>) -> Lit {
        let mut or = Vec::new();
        for o in ors.into_iter() {
            let o = o.as_ref();
            if o.is_constant(false) {
                continue;
            }
            if o.is_constant(true) {
                return Lit::constant(true);
            }
            or.push(*o);
        }
        if or.is_empty() {
            Lit::constant(false)
        } else if or.len() == 1 {
            or[0]
        } else {
            let n = self.new_var().lit();
            self.add_cnf_or(n, &or);
            n
        }
    }

    /* pub fn new_xor(&mut self, mut x: Lit, mut y: Lit) -> Lit {
        if x.var() == y.var() {
            return Lit::constant(x != y);
        }
        if x.var() > y.var() {
            (x, y) = (y, x);
        }
        if x.is_constant(true) {
            return !y;
        } else if x.is_constant(false) {
            return y;
        }
        let n = self.new_var().lit();
        self.add_cnf_xor(n, x, y);
        n
    } */

    pub fn new_xnor(&mut self, mut x: Lit, mut y: Lit) -> Lit {
        if x.var() == y.var() {
            return Lit::constant(x == y);
        }
        if x.var() > y.var() {
            (x, y) = (y, x);
        }
        if x.is_constant(true) {
            return y;
        } else if x.is_constant(false) {
            return !y;
        }
        let n = self.new_var().lit();
        self.add_cnf_xnor(n, x, y);
        n
    }

    pub fn new_imply(&mut self, x: Lit, y: Lit) -> Lit {
        let n = self.new_var().lit();
        self.add_cnf_or(n, &[!x, y]);
        n
    }

    /* pub fn new_ite(&mut self, c: Lit, t: Lit, e: Lit) -> Lit {
        let n = self.new_var().lit();
        self.add_cnf_ite(n, c, t, e);
        n
    }

    pub fn fanins(&self, var: impl IntoIterator<Item = impl AsRef<Var>>) -> HashSet<Var> {
        let mut marked = HashSet::default();
        let mut queue = vec![];
        for v in var.into_iter().map(|v| *v.as_ref()) {
            marked.insert(v);
            queue.push(v);
        }
        while let Some(v) = queue.pop() {
            for d in self.dep(v) {
                if !marked.contains(d) {
                    marked.insert(*d);
                    queue.push(*d);
                }
            }
        }
        marked
    } */

    pub fn fanouts(&self, var: impl IntoIterator<Item = impl AsRef<Var>>) -> HashSet<Var> {
        let mut marked = HashSet::from_iter(var.into_iter().map(|v| *v.as_ref()));
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            if self.dep(v).iter().any(|d| marked.contains(d)) {
                marked.insert(v);
            }
        }
        marked
    }

    pub fn rearrange(&mut self, additional: impl IntoIterator<Item = impl AsRef<Var>>) -> VarVMap {
        let mut domain = HashSet::from_iter(
            additional
                .into_iter()
                .map(|l| *l.as_ref())
                .chain(once(Var::CONST)),
        );
        for cls in self.all_clauses() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
        let mut domain = Vec::from_iter(domain);
        domain.sort();
        let mut domain_map = VarVMap::new();
        let mut res = DagCnf::new();
        for (i, d) in domain.iter().enumerate() {
            let v = Var::new(i);
            res.new_var_to(v);
            domain_map.insert(*d, v);
        }
        let map_lit = |l: &Lit| l.map_var(|v| domain_map[v]);
        for (d, v) in domain_map.iter() {
            if d.is_constant() {
                continue;
            }
            let mut new_cls = Vec::new();
            for cls in self.clauses_of_var(*d) {
                new_cls.push(cls.iter().map(map_lit).collect());
            }
            res.add_rel(*v, &new_cls);
        }
        *self = res;
        domain_map
    }

    pub fn replace(&mut self, map: &VarLMap) {
        for (old, new) in map.iter() {
            assert!(*old > new.var());
        }

        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            if map.contains_key(&v) {
                self.del_rel(v);
                continue;
            }
            let (start, len) = self.cnf_pos[v];
            if len == 0 {
                continue;
            }
            let mut pos = start as usize + 1;
            let end = (start + len) as usize;
            while pos < end {
                let cls_len = self.cnf_dat[pos] as usize;
                let begin = pos + 1;
                let cls_end = begin + cls_len;
                for raw in self.cnf_dat[begin..cls_end].iter_mut() {
                    if let Some(new) = map.map_lit(Lit(*raw)) {
                        *raw = new.into();
                    }
                }
                self.cnf_dat[begin..cls_end].sort_unstable();
                debug_assert!(Lit(self.cnf_dat[cls_end - 1]).var() == v);
                pos = cls_end;
            }

            // refresh_dep
            let mut deps = HashSet::default();
            let (start, len) = self.cnf_pos[v];
            let mut pos = start as usize + usize::from(len != 0);
            let end = (start + len) as usize;
            while pos < end {
                let cls_len = self.cnf_dat[pos] as usize;
                let begin = pos + 1;
                let cls_end = begin + cls_len;
                for i in begin..cls_end {
                    deps.insert(Lit(self.cnf_dat[i]).var());
                }
                pos = cls_end;
            }
            self.finish_rel(v, end, end, deps);
        }
    }

    pub fn migrate(&mut self, other: &DagCnf, t: Var, map: &mut VarVMap) {
        if map.get(&t).is_some() {
            return;
        }
        for rel in other.clauses_of_var(t) {
            for &l in rel {
                if l.var() != t {
                    self.migrate(other, l.var(), map);
                }
            }
        }
        let n = self.new_var();
        map.insert(t, n);
        let mut new_rel = Vec::new();
        for rel in other.clauses_of_var(t) {
            new_rel.push(rel.iter().map(|&l| map.lit_map(l).unwrap()).collect());
        }
        self.add_rel(n, &new_rel);
    }

    pub fn compact(&mut self) {
        let mut rels = Vec::new();
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            let (start, len) = self.cnf_pos[v];
            if len == 0 || self.cnf_dat[start as usize] == 0 {
                self.cnf_pos[v] = (0, 0);
            } else {
                rels.push((start, len, v));
            }
        }
        rels.sort_unstable_by_key(|&(start, _, _)| start);
        let mut pos = 0;
        for (start, len, v) in rels {
            let start = start as usize;
            let len = len as usize;
            debug_assert!(pos <= start);
            if pos != start {
                self.cnf_dat.copy_within(start..start + len, pos);
            }
            self.cnf_pos[v] = (pos as u32, len as u32);
            pos += len;
        }
        self.cnf_dat.truncate(pos);
        self.cnf_dat.shrink_to_fit();

        let mut deps = Vec::new();
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            let (start, len) = self.dep_pos[v];
            if len == 0 {
                self.dep_pos[v] = (0, 0);
            } else {
                deps.push((start, len, v));
            }
        }
        deps.sort_unstable_by_key(|&(start, _, _)| start);
        let mut pos = 0;
        for (start, len, v) in deps {
            let start = start as usize;
            let len = len as usize;
            debug_assert!(pos <= start);
            if pos != start {
                self.dep_dat.copy_within(start..start + len, pos);
            }
            self.dep_pos[v] = (pos as u32, len as u32);
            pos += len;
        }
        self.dep_dat.truncate(pos);
        self.dep_dat.shrink_to_fit();

        self.cnf_pos.shrink_to_fit();
        self.dep_pos.shrink_to_fit();
    }

    fn alloc_rel(&mut self, n: Var, num_clauses: usize, num_words: usize) -> (usize, usize) {
        self.new_var_to(n);
        debug_assert!(!n.is_constant());
        debug_assert!(self.dep(n).is_empty() && self.clauses_of_var(n).is_empty());

        let start = self.cnf_dat.len();
        self.cnf_dat.resize(start + num_words, 0);
        self.cnf_dat[start] = num_clauses as u32;
        self.cnf_pos[n] = (start as u32, num_words as u32);
        (start + 1, start + num_words)
    }

    fn finish_rel(&mut self, n: Var, pos: usize, end: usize, mut deps: HashSet<Var>) {
        debug_assert_eq!(pos, end);
        deps.remove(&n);
        let dep_start = self.dep_dat.len();
        self.dep_dat.extend(deps);
        let dep_len = self.dep_dat.len() - dep_start;
        self.dep_pos[n] = (dep_start as u32, dep_len as u32);
    }

    fn write_fixed_clause<const N: usize>(
        &mut self,
        pos: &mut usize,
        n: Var,
        mut cls: [Lit; N],
        deps: &mut HashSet<Var>,
    ) {
        cls.sort_unstable();
        debug_assert!(cls[N - 1].var() == n);
        self.cnf_dat[*pos] = N as u32;
        *pos += 1;
        for l in cls {
            deps.insert(l.var());
            self.cnf_dat[*pos] = l.into();
            *pos += 1;
        }
    }
}

impl Default for DagCnf {
    fn default() -> Self {
        let max_var = Var::CONST;
        let mut res = Self {
            max_var,
            cnf_pos: VarMap::new_with(max_var),
            cnf_dat: Vec::new(),
            dep_pos: VarMap::new_with(max_var),
            dep_dat: Vec::new(),
        };
        let start = res.cnf_dat.len();
        res.cnf_dat.extend([1, 1, Lit::constant(true).into()]);
        res.cnf_pos[max_var] = (start as u32, 3);
        res
    }
}

impl Display for DagCnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for cls in self.all_clauses() {
            writeln!(f, "{cls:?}")?;
        }
        Ok(())
    }
}

#[inline]
fn clauses_from_pos(cnf_dat: &[u32], (start, len): (u32, u32)) -> DcnfIter<'_> {
    if len == 0 {
        DcnfIter::new(&[])
    } else {
        DcnfIter::new(&cnf_dat[start as usize..(start + len) as usize])
    }
}

#[cfg(test)]
mod tests {
    use super::DagCnf;
    use crate::{Lit, LitVec, Var, VarLMap};

    fn sorted<const N: usize>(lits: [Lit; N]) -> LitVec {
        let mut lits = LitVec::from(lits);
        lits.sort();
        lits
    }

    fn rel(dc: &DagCnf, var: Var) -> Vec<LitVec> {
        dc.clauses_of_var(var).map(LitVec::from).collect()
    }

    #[test]
    fn arena_add_set_delete_relation() {
        let x = Var(1).lit();
        let y = Var(2).lit();
        let n = Var(3).lit();
        let mut dc = DagCnf::new();
        dc.add_rel(n.var(), &[LitVec::from([n, !y, x]), LitVec::from([!n, y])]);
        assert_eq!(rel(&dc, n.var()), vec![sorted([n, !y, x]), sorted([!n, y])]);
        assert_eq!(dc.dep(n.var()).len(), 2);
        assert!(dc.dep(n.var()).contains(&x.var()));
        assert!(dc.dep(n.var()).contains(&y.var()));

        dc.del_rel(n.var());
        assert!(dc.clauses_of_var(n.var()).is_empty());
        assert!(dc.dep(n.var()).is_empty());
    }

    #[test]
    fn direct_xor_writer_matches_template() {
        let x = Var(1).lit();
        let y = Var(2).lit();
        let n = Var(3).lit();
        let mut dc = DagCnf::new();
        dc.add_cnf_xor(n, x, y);
        assert_eq!(
            rel(&dc, n.var()),
            vec![
                sorted([!x, y, n]),
                sorted([x, !y, n]),
                sorted([x, y, !n]),
                sorted([!x, !y, !n]),
            ]
        );
    }

    #[test]
    fn replace_updates_arena_relation_in_place_and_deps() {
        let x = Var(1).lit();
        let y = Var(2).lit();
        let n = Var(3).lit();
        let mut dc = DagCnf::new();
        dc.add_cnf_and(n, &[x, y]);

        let mut map = VarLMap::new();
        map.insert_lit(y, x);
        dc.replace(&map);

        assert!(dc.dep(n.var()).iter().all(|&d| d == x.var()));
        for cls in dc.clauses_of_var(n.var()) {
            assert!(cls.iter().all(|l| l.var() != y.var()));
        }
    }

    #[test]
    fn compact_removes_dead_arena_regions() {
        let x = Var(1).lit();
        let y = Var(2).lit();
        let n = Var(3).lit();
        let dead = Var(4).lit();
        let empty = Var(5).lit();
        let mut dc = DagCnf::new();
        dc.add_cnf_and(n, &[x, y]);
        dc.add_cnf_or(dead, &[x]);
        dc.del_rel(dead.var());
        dc.add_rel(empty.var(), &[]);

        let mut map = VarLMap::new();
        map.insert_lit(y, x);
        dc.replace(&map);

        let rel_before = rel(&dc, n.var());
        let cnf_len_before = dc.cnf_dat.len();
        let dep_len_before = dc.dep_dat.len();

        dc.compact();

        assert_eq!(rel(&dc, n.var()), rel_before);
        assert!(dc.dep(n.var()).iter().all(|&d| d == x.var()));
        assert!(dc.clauses_of_var(dead.var()).is_empty());
        assert!(dc.clauses_of_var(empty.var()).is_empty());
        assert_eq!(dc.cnf_pos[empty.var()], (0, 0));
        assert_eq!(dc.dep_pos[empty.var()], (0, 0));
        assert!(dc.cnf_dat.len() < cnf_len_before);
        assert!(dc.dep_dat.len() < dep_len_before);
    }
}
