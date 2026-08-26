use super::IC3;
use super::solver::inductive_core;
use crate::RseedSet as HashSet;
use logicrs::{Lit, LitOrdVec, LitVec};
use rand::{RngExt, seq::SliceRandom};

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct DropVarParameter {
    pub(super) limit: usize,
    max: usize,
    level: usize,
}

impl DropVarParameter {
    #[inline]
    pub fn new(limit: usize, max: usize, level: usize) -> Self {
        Self { limit, max, level }
    }

    fn sub_level(self) -> Self {
        Self {
            limit: self.limit,
            max: self.max,
            level: self.level - 1,
        }
    }
}

impl IC3 {
    fn down(
        &mut self,
        frame: usize,
        cube: &LitVec,
        keep: &HashSet<Lit>,
        full: &LitVec,
        constraint: &[Lit],
        cex: &mut Vec<(LitOrdVec, LitOrdVec)>,
    ) -> Option<LitVec> {
        let mut cube = cube.clone();
        let state_cst = !self.ts.lits_next(full);
        let mut cube_cst = LitVec::new_with_cap(cube.len());
        let mut ordcube = LitVec::new_with_cap(cube.len());
        let mut assump = LitVec::new_with_cap(cube.len());
        let ts = &self.ts;
        let activity = &mut self.activity;
        let slv = &mut self.solvers[frame - 1];

        loop {
            if ts.cube_subsume_init(&cube) {
                return None;
            }
            let lemma = LitOrdVec::new(cube.clone());
            if cex
                .iter()
                .any(|(s, t)| !lemma.subsume(s) && lemma.subsume(t))
            {
                return None;
            }

            ordcube.clear();
            ordcube.extend_from_slice(&cube);
            activity.sort_by_activity(&mut ordcube, false);
            assump.clear();
            assump.extend(ordcube.iter().map(|l| ts.next(*l)));
            cube_cst.clear();
            cube_cst.extend(ordcube.iter().map(|l| !*l));

            let allcst: &[&[Lit]] = if constraint.is_empty() {
                &[state_cst.as_slice(), &cube_cst]
            } else {
                &[constraint, &state_cst, &cube_cst]
            };
            if !slv.dcs_solve(&assump, allcst, &[], u32::MAX).unwrap() {
                return Some(inductive_core(slv, ts, &ordcube).unwrap());
            }
            let mut ret = false;
            let mut cube_new = LitVec::new();
            for lit in cube {
                if keep.contains(&lit) {
                    if let Some(true) = slv.dcs_satval(lit) {
                        cube_new.push(lit);
                    } else {
                        ret = true;
                        break;
                    }
                } else if let Some(true) = slv.dcs_satval(lit)
                    && !slv.flip_to_none(lit.var())
                {
                    cube_new.push(lit);
                }
            }
            cube = cube_new;
            let mut s = LitVec::new();
            let mut t = LitVec::new();
            for l in full.iter() {
                if let Some(v) = slv.dcs_satval(*l)
                    && slv.flip_to_none(l.var())
                {
                    s.push(l.not_if(!v));
                }
                if let Some(v) = slv.dcs_satval(ts.next(*l)) {
                    t.push(l.not_if(!v));
                }
            }
            cex.push((LitOrdVec::new(s), LitOrdVec::new(t)));
            if ret {
                return None;
            }
        }
    }

    fn ctg_down(
        &mut self,
        frame: usize,
        cube: &LitVec,
        keep: &HashSet<Lit>,
        full: &LitVec,
        parameter: DropVarParameter,
    ) -> Option<LitVec> {
        let mut cube = cube.clone();
        let full = !full;
        let state_cst = self.ts.lits_next(&full);
        let mut cube_cst = LitVec::new_with_cap(cube.len());
        let mut ordcube = LitVec::new_with_cap(cube.len());
        let mut assump = LitVec::new_with_cap(cube.len());
        let mut ctg = 0;

        loop {
            if self.ts.cube_subsume_init(&cube) {
                return None;
            }
            ordcube.clear();
            ordcube.extend_from_slice(&cube);
            self.activity.sort_by_activity(&mut ordcube, false);
            assump.clear();
            assump.extend(ordcube.iter().map(|l| self.ts.next(*l)));
            cube_cst.clear();
            cube_cst.extend(ordcube.iter().map(|l| !*l));

            let slv = &mut self.solvers[frame - 1];
            // Preserve the baseline D/D' cone while attaching !K' below.
            // The helper remains available to BCP but cannot seed the COI.
            slv.set_domain(
                assump.iter().copied().chain(ordcube.iter().copied()),
                &state_cst,
            );
            let blocked = !slv.dcs_solve(&assump, &[&state_cst, &cube_cst], &[], u32::MAX).unwrap();
            let core = blocked.then(|| inductive_core(slv, &self.ts, &ordcube).unwrap());
            let keep_in_model = !blocked
                && cube.iter().all(|lit| {
                    !keep.contains(lit) || slv.dcs_satval(*lit).is_some_and(|value| value)
                });
            // Nested CTG blocking can push through this solver, so do not
            // let the per-query temporary domain leak past this point.
            slv.unset_domain();
            if let Some(core) = core {
                return Some(core);
            }
            if !keep_in_model {
                return None;
            }

            let (model, _) = self.get_pred(frame, &assump, false);
            let cex_set: HashSet<Lit> = HashSet::from_iter(model.iter().cloned());
            if ctg < parameter.max
                && frame > 1
                && !self.ts.cube_subsume_init(&model)
                && self.trivial_block(frame - 1, model.clone(), &full, parameter.sub_level())
            {
                ctg += 1;
                continue;
            }
            ctg = 0;
            let mut cube_new = LitVec::new();
            for lit in cube {
                if cex_set.contains(&lit) {
                    cube_new.push(lit);
                } else if keep.contains(&lit) {
                    return None;
                }
            }
            cube = cube_new;
        }
    }

    pub(super) fn mic(
        &mut self,
        frame: usize,
        mut cube: LitVec,
        constraint: &[Lit],
        parameter: DropVarParameter,
    ) -> LitVec {
        if parameter.level == 0 {
            self.solvers[frame - 1].set_domain(
                self.ts
                    .lits_next(&cube)
                    .iter()
                    .copied()
                    .chain(cube.iter().copied()),
                &[],
            );
        }
        let mut cex = Vec::new();
        if self.rng.random_bool(0.2) {
            cube.shuffle(&mut self.rng);
        } else {
            self.activity.sort_by_activity(&mut cube, true);
        }
        if self.parent_lemma
            && let Some(parent) = self.frame.parent_lemma(&cube, frame)
        {
            let parent = HashSet::from_iter(parent.as_litvec());
            cube.sort_by_key(|x| parent.contains(x));
        }
        let mut keep = HashSet::default();
        let mut i = 0;
        while i < cube.len() {
            if keep.contains(&cube[i]) {
                i += 1;
                continue;
            }
            let mut removed_cube = cube.clone();
            removed_cube.remove(i);
            let mic = if parameter.level == 0 {
                self.down(frame, &removed_cube, &keep, &cube, constraint, &mut cex)
            } else {
                self.ctg_down(frame, &removed_cube, &keep, &cube, parameter)
            };
            if let Some(mut new_cube) = mic {
                new_cube = cube
                    .iter()
                    .filter(|lit| new_cube.contains(lit))
                    .copied()
                    .collect();
                let new_i = new_cube
                    .iter()
                    .position(|lit| !cube[..i].contains(lit))
                    .unwrap_or(new_cube.len());
                if new_i < new_cube.len() {
                    debug_assert!(!cube[..=i].contains(&new_cube[new_i]));
                }
                (cube, i) = (new_cube, new_i);
                if parameter.level == 0 {
                    self.solvers[frame - 1].unset_domain();
                    self.solvers[frame - 1].set_domain(
                        self.ts
                            .lits_next(&cube)
                            .iter()
                            .copied()
                            .chain(cube.iter().copied()),
                        &[],
                    );
                }
            } else {
                keep.insert(cube[i]);
                i += 1;
            }
        }
        if parameter.level == 0 {
            self.solvers[frame - 1].unset_domain();
        }
        self.activity.bump_cube_activity(&cube);
        cube
    }
}
