use super::{
    DagCnfSolver,
    cdb::{CREF_NONE, CRef},
};
use logicrs::{Lit, LitVec, Var, VarMap};
use std::ops::{Deref, DerefMut};

#[derive(Clone, Copy, Debug, Default)]
pub enum Mark {
    #[default]
    Unseen,
    Seen,
    Removable,
    Failed,
}

#[derive(Clone)]
pub struct Analyze {
    mark: VarMap<Mark>,
    clear: Vec<Var>,
}

impl Analyze {
    pub fn new_with(var: Var) -> Self {
        Self {
            mark: VarMap::new_with(var),
            clear: Vec::new(),
        }
    }

    #[inline]
    pub fn seen_var(&self, var: Var) -> bool {
        !matches!(self.mark[var], Mark::Unseen)
    }

    #[inline]
    pub fn see(&mut self, lit: Lit) {
        self.see_var(lit.var());
    }

    #[inline]
    pub fn see_var(&mut self, var: Var) {
        self.mark[var] = Mark::Seen;
        self.clear.push(var);
    }

    #[inline]
    fn mark_var(&mut self, var: Var, m: Mark) {
        self.mark[var] = m;
        self.clear.push(var);
    }

    fn clear(&mut self) {
        for c in self.clear.iter() {
            self.mark[*c] = Mark::Unseen;
        }
        self.clear.clear();
    }
}

impl Deref for Analyze {
    type Target = VarMap<Mark>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.mark
    }
}

impl DerefMut for Analyze {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.mark
    }
}

impl DagCnfSolver {
    fn lit_redundant(&mut self, lit: Lit) -> bool {
        let var = lit.var();
        debug_assert!(matches!(self.analyze[var], Mark::Unseen | Mark::Seen));
        if self.reason[var] == CREF_NONE {
            return false;
        }
        let mut stack: Vec<(Lit, usize)> = vec![(lit, 1)];
        'a: while let Some((p, b)) = stack.pop() {
            let c = self.cdb.get(self.reason[p.var()]);
            for i in b..c.len() {
                let l = c[i];
                let lvar = l.var();
                if self.level[lvar] == 0
                    || matches!(self.analyze[lvar], Mark::Seen | Mark::Removable)
                {
                    continue;
                }
                if self.reason[lvar] == CREF_NONE || matches!(self.analyze[lvar], Mark::Failed) {
                    stack.push((p, 0));
                    for (l, _) in stack {
                        let var = l.var();
                        if matches!(self.analyze[var], Mark::Unseen) {
                            self.analyze.mark_var(var, Mark::Failed);
                        }
                    }
                    return false;
                }
                stack.push((p, i + 1));
                stack.push((l, 1));
                continue 'a;
            }
            let var = p.var();
            if matches!(self.analyze[var], Mark::Unseen) {
                self.analyze.mark_var(var, Mark::Removable);
            }
        }
        true
    }

    fn minimal_learnt(&mut self, mut learnt: LitVec) -> LitVec {
        let mut now = 1;
        for i in 1..learnt.len() {
            if !self.lit_redundant(learnt[i]) {
                learnt[now] = learnt[i];
                now += 1
            }
        }
        learnt.truncate(now);
        learnt
    }

    pub(super) fn analyze(&mut self, mut conflict: CRef) -> (LitVec, usize) {
        let mut learnt = LitVec::from([Lit::default()]);
        let mut path = 0;
        let mut trail_idx = self.trail.len() - 1;
        let mut resolve_lit = None;
        loop {
            self.cdb.bump(conflict);
            let cref = self.cdb.get(conflict);
            let begin = usize::from(resolve_lit.is_some());
            for lit in begin..cref.len() {
                let lit = cref[lit];
                let var = lit.var();
                if !self.analyze.seen_var(var) && self.level[var] > 0 {
                    if var != self.constrain_act {
                        self.vsids.bump(var);
                    }
                    self.analyze[var] = Mark::Seen;
                    if self.level[var] >= self.highest_level() as u32 {
                        path += 1;
                    } else {
                        learnt.push(lit);
                    }
                }
            }
            let resolve = loop {
                let lit = self.trail[trail_idx];
                if self.analyze.seen_var(lit.var()) {
                    break lit;
                }
                trail_idx -= 1;
            };
            let resolve_var = resolve.var();
            self.analyze[resolve_var] = Mark::Unseen;
            resolve_lit = Some(resolve);
            path -= 1;
            if path == 0 {
                break;
            }
            conflict = self.reason[resolve_var];
        }
        learnt[0] = !resolve_lit.unwrap();
        self.analyze.clear.extend(learnt.iter().map(Lit::var));
        learnt = self.minimal_learnt(learnt);
        self.analyze.clear();
        let btl = if learnt.len() == 1 {
            0
        } else {
            let max_idx = (1..learnt.len())
                .max_by_key(|idx| self.level[learnt[*idx].var()])
                .unwrap();
            learnt.swap(1, max_idx);
            self.level[learnt[1].var()]
        };
        (learnt, btl as usize)
    }

    pub(super) fn analyze_unsat_core(&mut self, mut p: Lit) {
        self.unsat_core.clear();
        self.unsat_core.insert(p);
        if self.highest_level() == 0 {
            return;
        }
        self.analyze.see(p);
        for i in (self.pos_in_trail[0]..self.trail.len() as u32).rev() {
            p = self.trail[i];
            let var = p.var();
            if self.analyze.seen_var(var) {
                if self.reason[var] != CREF_NONE {
                    let c = self.cdb.get(self.reason[var]);
                    for l in 1..c.len() {
                        let l = c[l];
                        let var = l.var();
                        if self.level[var] > 0 {
                            self.analyze.see_var(var);
                        }
                    }
                } else {
                    self.unsat_core.insert(p);
                }
            }
        }
        self.analyze.clear();
    }
}
