use super::Transys;
use crate::RseedSet as HashSet;
use crate::{
    config::PreprocConfig,
    transys::{certify::Restore, frts::combsweep, scorr::Scorr},
};
use log::{debug, info};
use logicrs::{Lit, LitVec, OptionU32, Var, VarMap, VarRange};

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
                let idx: usize = v.0 as usize;
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
        for v in VarRange::new_inclusive(Var(1), self.max_var()) {
            if !mark.contains(&v) {
                removed += self.rel.clauses_of_var(v).len();
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
                init[mv] = OptionU32::some(map_lit(i).0);
            }
        }
        for &l in old_latch.iter() {
            let ml = domain_map[l];
            next.reserve(ml);
            next[ml] = OptionU32::some(map_lit(self.var_next_lit(l)).0);
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
        self.rel = std::sync::Arc::new(self.rel.simplify(frozens));
        self.coi_refine(rst);
        self.constraint.retain(|l| !l.is_constant(true));
        self.constraint.sort();
        self.constraint.dedup();
        self.rearrange(rst);
        self.rel_mut().compact();
    }

    /// Normalize frontend properties before simplifying: bad[0] is the target,
    /// bad[1..] are helper bads whose negations may be assumed on a proof prefix.
    /// Helpers remain roots, never ordinary constraints, throughout preprocessing.
    pub fn preproc(mut ts: Self, cfg: &PreprocConfig, mut rst: Restore) -> (Self, Restore) {
        let num_prop = ts.bad.len();
        rst.helper_props.clear();
        let finish = |mut ts: Transys, mut rst: Restore| {
            ts.simplify(&mut rst);
            info!("trivial simplified ts: {}", ts.statistic());
            if cfg.scorr {
                let scorr = Scorr::new(ts, cfg, rst);
                (ts, rst) = scorr.scorr();
            }
            if cfg.frts {
                (ts, rst) = combsweep(ts, cfg, rst);
            }
            info!("preprocessed ts has {}", ts.statistic());
            (ts, rst)
        };

        if cfg.prop >= num_prop {
            rst.prop = None;
            let bad = std::mem::take(&mut ts.bad);
            ts.bad = LitVec::from(ts.rel_mut().new_or(bad));
            return finish(ts, rst);
        }
        let prop = cfg.prop;
        rst.prop = Some(prop);
        if !cfg.local_proof || num_prop <= 1 {
            ts.bad = LitVec::from(ts.bad[prop]);
            return finish(ts, rst);
        }

        // Two roots are connected exactly when their sequential fanin cones overlap, transitively.
        // Each constraint is another root: it can bridge cones, but unrelated constraints do not
        // seed the target's component. All genuine constraints are kept below. Record the first
        // owner of each variable and union overlapping roots. Its fanin was already visited by that
        // owner, so each variable's dependencies need only be traversed once.
        let num_root = num_prop + ts.constraint.len();
        // set up DSU for transitive root identification
        let mut parent: Vec<usize> = (0..num_root).collect();
        let mut size = vec![1usize; num_root];
        let mut owner: VarMap<Option<usize>> = VarMap::new_with(ts.max_var());
        let mut queue = Vec::new();
        for (root, bad) in ts.bad.iter().chain(ts.constraint.iter()).enumerate() {
            queue.push(bad.var());
            while let Some(v) = queue.pop() {
                // Constant initializations must not connect every cone.
                if v.is_constant() {
                    continue;
                }
                if let Some(previous) = owner[v] {
                    let mut a = root;
                    while parent[a] != a {
                        parent[a] = parent[parent[a]];
                        a = parent[a];
                    }
                    let mut b = previous;
                    while parent[b] != b {
                        parent[b] = parent[parent[b]];
                        b = parent[b];
                    }
                    if a != b {
                        if size[a] < size[b] {
                            std::mem::swap(&mut a, &mut b);
                        }
                        parent[b] = a;
                        size[a] += size[b];
                    }
                    continue;
                }
                owner[v] = Some(root);

                if ts.is_latch(v) {
                    queue.push(ts.var_next_lit(v).var());
                }
                if let Some(init) = ts.init(v) {
                    queue.push(init.var());
                }
                queue.extend_from_slice(ts.rel.dep(v));
            }
        }

        // extract the particular set of selected property
        for root in 0..num_root {
            let mut component = root;
            while parent[component] != component {
                parent[component] = parent[parent[component]];
                component = parent[component];
            }
            parent[root] = component;
        }
        let mut bad = LitVec::from(ts.bad[prop]);
        for i in 0..num_prop {
            if i != prop && parent[i] == parent[prop] {
                bad.push(ts.bad[i]);
                rst.helper_props.push(i);
            }
        }
        info!(
            "property {prop}: retained {} of {} helper properties",
            rst.helper_props.len(),
            num_prop - 1,
        );
        ts.bad = bad;
        finish(ts, rst)
    }
}
