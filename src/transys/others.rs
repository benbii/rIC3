use super::Transys;
use crate::RseedMap as HashMap;
use crate::transys::certify::Restore;
use logicrs::{Lit, LitVec, OptionU32, Var, VarLMap, VarMap, VarRange};

impl Transys {
    pub fn frozens(&self) -> Vec<Var> {
        let mut frozens = vec![Var::CONST];
        frozens.extend(
            self.bad
                .iter()
                .chain(self.constraint.iter())
                .chain(self.justice.iter())
                .map(|l| l.var())
                .chain(self.input.iter().copied())
                .chain(self.latch.iter().copied()),
        );
        for l in self.latch.iter() {
            if let Some(i) = self.init(*l) {
                frozens.push(i.var());
            }
            frozens.push(self.var_next_lit(*l).var());
        }
        frozens
    }

    pub fn merge(&mut self, other: &Self, mapf: impl Fn(Var) -> Option<Var>) {
        let begin = self.max_var();
        let mut vmap = HashMap::default();
        assert!(mapf(Var::CONST) == Some(Var::CONST));
        for v in VarRange::new_inclusive(Var::CONST, other.max_var()) {
            let m = if let Some(m) = mapf(v) {
                m
            } else {
                self.new_var()
            };
            vmap.insert(v, m);
        }
        let lmap = |x: Lit| x.map_var(|v| vmap[&v]);
        for i in other.input.iter() {
            let m = vmap[i];
            if m > begin {
                self.input.push(m);
            }
        }
        for l in other.latch.iter() {
            let ml = vmap[l];
            if ml <= begin {
                continue;
            }
            self.add_latch(ml, other.init(*l).map(lmap), lmap(other.var_next_lit(*l)));
        }
        for v in VarRange::new_inclusive(Var::CONST, other.max_var()) {
            let mv = vmap[&v];
            if mv <= begin {
                continue;
            }
            let rel: Vec<LitVec> = other.rel[v]
                .iter()
                .map(|cls| cls.iter().map(|l| lmap(*l)).collect())
                .collect();
            self.rel.add_rel(mv, &rel);
        }
        for &l in other.bad.iter() {
            let lm = lmap(l);
            if lm.var() > begin {
                self.bad.push(lm);
            }
        }
        for &l in other.constraint.iter() {
            let lm = lmap(l);
            if lm.var() > begin {
                self.constraint.push(lm);
            }
        }
        for &l in other.justice.iter() {
            let lm = lmap(l);
            if lm.var() > begin {
                self.justice.push(lm);
            }
        }
    }

    pub fn has_gate_init(&self) -> bool {
        for l in self.input().chain(self.latch()) {
            if let Some(i) = self.init(l)
                && !(i.var().is_constant())
            {
                return true;
            }
        }
        false
    }

    pub fn remove_gate_init(&mut self, rst: &mut Restore) {
        let mut const_init = Vec::new();
        let mut eq = Vec::new();
        for l in self.input().chain(self.latch()) {
            if let Some(i) = self.init(l) {
                if i.try_constant().is_some() {
                    const_init.push((l, i));
                } else {
                    eq.push((l, i));
                }
            }
        }
        if eq.is_empty() {
            return;
        }
        self.init = VarMap::new();
        for (l, i) in const_init {
            self.add_init(l, i);
        }
        let iv = rst.get_init_var(self);
        for (v, i) in eq {
            let e = self.rel.new_xnor(v.lit(), i);
            let c = self.rel.new_imply(iv.lit(), e);
            self.constraint.push(c);
        }
    }

    pub fn map(&mut self, map: impl Fn(Var) -> Var + Copy, rst: &mut Restore) {
        let old_input = self.input.clone();
        let old_latch = self.latch.clone();
        let mut init = VarMap::new();
        let mut next = VarMap::new();
        for &v in old_input.iter().chain(old_latch.iter()) {
            if let Some(i) = self.init(v) {
                let mv = map(v);
                init.reserve(mv);
                init[mv] = OptionU32::some(i.map_var(map).into());
            }
        }
        for &l in old_latch.iter() {
            let ml = map(l);
            next.reserve(ml);
            next[ml] = OptionU32::some(self.var_next_lit(l).map_var(map).into());
        }
        self.input
            .iter_mut()
            .chain(self.latch.iter_mut())
            .for_each(|v| *v = map(*v));
        self.rel = self.rel.map(map);
        self.init = init;
        self.next = next;
        self.bad = self.bad.map_var(map);
        self.constraint = self.constraint.map_var(map);
        self.justice = self.justice.map_var(map);
        rst.map_var(&map);
    }

    pub fn replace(&mut self, map: &VarLMap, rst: &mut Restore) {
        for (&x, &y) in map.iter() {
            if self.is_latch(x)
                && let Some(x_init) = self.init(x)
            {
                let y_init = x_init.not_if(!y.polarity());
                if let Some(init) = self.init(y.var()) {
                    let c = self.rel.new_xnor(init, y_init);
                    if !c.is_constant(true) {
                        let iv = rst.get_init_var(self);
                        let c = self.rel.new_imply(iv.lit(), c);
                        self.constraint.push(c);
                    }
                } else {
                    self.add_init(y.var(), y_init);
                }
            }
        }
        for (&x, &y) in map.iter() {
            if self.is_latch(x) {
                rst.replace(x, y);
            } else {
                rst.remove(x);
            }
        }
        self.input.retain(|l| !map.contains_key(l));
        self.latch.retain(|l| !map.contains_key(l));
        self.rel.replace(map);
        let mut init = VarMap::new();
        let mut next = VarMap::new();
        for v in VarRange::new_inclusive(Var::CONST, self.max_var()) {
            if map.contains_key(&v) {
                continue;
            }
            if let Some(i) = self.init(v) {
                let i = map.map_lit(i).unwrap_or(i);
                init.reserve(v);
                init[v] = OptionU32::some(i.into());
            }
        }
        for &l in self.latch.iter() {
            let n = self.var_next_lit(l);
            let n = map.map_lit(n).unwrap_or(n);
            next.reserve(l);
            next[l] = OptionU32::some(n.into());
        }
        self.init = init;
        self.next = next;
        let map_fn = map.try_map_fn();
        self.bad = self.bad.map(|l| map_fn(l).unwrap_or(l));
        self.constraint = self.constraint.map(|l| map_fn(l).unwrap_or(l));
        self.justice = self.justice.map(|l| map_fn(l).unwrap_or(l));
    }

    pub fn topsort(&mut self, rst: &mut Restore) {
        let (_, m) = self.rel.topsort();
        let m = m.inverse();
        self.map(|v| m[v], rst);
    }
}
