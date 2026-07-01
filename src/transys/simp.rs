use super::Transys;
use crate::RseedSet as HashSet;
use crate::{
    config::PreprocConfig,
    transys::{certify::Restore, frts::FrTs, scorr::Scorr},
};
use log::{debug, info};
use logicrs::{Lit, OptionU32, Var, VarMap, VarRange};

impl Transys {
    pub fn coi_refine(&mut self, rst: &mut Restore) {
        let mut mark = HashSet::default();
        let mut queue = Vec::new();
        for v in self
            .constraint
            .iter()
            .chain(self.bad.iter())
            .chain(self.justice.iter())
            .map(|l| l.var())
        {
            if !mark.contains(&v) {
                mark.insert(v);
                queue.push(v);
            }
        }
        if !self.justice.is_empty() {
            for v in self.latch.iter() {
                if !mark.contains(v) {
                    mark.insert(*v);
                    queue.push(*v);
                }
            }
        }
        while let Some(v) = queue.pop() {
            if self.is_latch(v) {
                let n = self.var_next_lit(v);
                let nv = n.var();
                if !mark.contains(&nv) {
                    mark.insert(nv);
                    queue.push(nv);
                }
            }
            if let Some(i) = self.init(v) {
                let iv = i.var();
                if !mark.contains(&iv) {
                    mark.insert(iv);
                    queue.push(iv);
                }
            }
            for &d in self.rel.dep(v).iter() {
                if !mark.contains(&d) {
                    mark.insert(d);
                    queue.push(d);
                }
            }
        }
        for v in self.input.iter().chain(self.latch.iter()) {
            if !mark.contains(v) {
                let idx: usize = (*v).into();
                if idx < self.init.len() {
                    self.init[*v] = OptionU32::NONE;
                }
                if idx < self.next.len() {
                    self.next[*v] = OptionU32::NONE;
                }
            }
        }
        self.input.retain(|i| mark.contains(i));
        self.latch.retain(|i| mark.contains(i));
        let mut removed = 0;
        for v in VarRange::new_inclusive(Var::CONST + 1, self.max_var()) {
            if !mark.contains(&v) {
                removed += self.rel[v].len();
                self.rel_mut().del_rel(v);
                rst.remove(v);
            }
        }
        debug!("ts coi simplify: removed {removed} clauses");
    }

    pub fn rearrange(&mut self, rst: &mut Restore) {
        let mut additional = vec![Var::CONST];
        additional.extend(
            self.constraint
                .iter()
                .chain(self.bad.iter())
                .chain(self.justice.iter())
                .map(|l| l.var())
                .chain(self.input.iter().copied())
                .chain(self.latch.iter().copied()),
        );
        for l in self.latch.iter() {
            if let Some(i) = self.init(*l) {
                additional.push(i.var());
            }
            additional.push(self.var_next_lit(*l).var());
        }
        let domain_map = self.rel_mut().rearrange(additional);
        let map_lit = |l: Lit| Lit::new(domain_map[l.var()], l.polarity());
        let old_input = self.input.clone();
        let old_latch = self.latch.clone();
        let mut init = VarMap::new();
        let mut next = VarMap::new();
        for &v in old_input.iter().chain(old_latch.iter()) {
            if let Some(i) = self.init(v) {
                let mv = domain_map[v];
                init.reserve(mv);
                init[mv] = OptionU32::some(map_lit(i).into());
            }
        }
        for &l in old_latch.iter() {
            let ml = domain_map[l];
            next.reserve(ml);
            next[ml] = OptionU32::some(map_lit(self.var_next_lit(l)).into());
        }
        self.input = self.input.iter().map(|v| domain_map[*v]).collect();
        self.latch = self.latch.iter().map(|v| domain_map[*v]).collect();
        self.init = init;
        self.next = next;
        self.bad = self.bad.map(map_lit);
        self.constraint = self.constraint.map(map_lit);
        self.justice = self.justice.map(map_lit);
        rst.filter_map_var(&|v| domain_map.get(&v).copied());
    }

    pub fn simplify(&mut self, rst: &mut Restore) {
        self.coi_refine(rst);
        let frozens = self.frozens();
        self.rel = std::sync::Arc::new(self.rel.simplify(frozens.iter().copied()));
        self.coi_refine(rst);
        self.constraint.retain(|l| !l.is_constant(true));
        self.constraint.sort();
        self.constraint.dedup();
        self.rearrange(rst);
    }

    pub fn preproc(mut ts: Self, cfg: &PreprocConfig, mut rst: Restore) -> (Self, Restore) {
        if cfg.preproc {
            ts.simplify(&mut rst);
            info!("trivial simplified ts: {}", ts.statistic());
            if cfg.scorr {
                let scorr = Scorr::new(ts, cfg, rst);
                (ts, rst) = scorr.scorr();
            }
            if cfg.frts {
                let frts = FrTs::new(ts, cfg, rst);
                (ts, rst) = frts.fr();
            }
        }
        info!("preprocessed ts has {}", ts.statistic());
        (ts, rst)
    }
}
