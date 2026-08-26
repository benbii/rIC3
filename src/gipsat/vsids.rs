use super::{DagCnfSolver, cdb::CREF_NONE, state::VarState};
use logicrs::{Lbool, Lit, Var, VarMap};
use logicrs::{OptionU32, nckvec::NckVec};
use rand::RngExt;
use std::ops::{Index, MulAssign};

#[derive(Default, Clone)]
pub struct BinaryHeap {
    heap: NckVec<Var>,
    pos: VarMap<OptionU32>,
}

impl BinaryHeap {
    #[inline]
    fn new_with(var: Var) -> Self {
        Self {
            heap: NckVec::new(),
            pos: VarMap::new_with(var),
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        for v in self.heap.iter() {
            self.pos[*v] = OptionU32::NONE;
        }
        self.heap.clear();
    }

    #[inline]
    fn up(&mut self, v: Var, activity: &Activity) {
        let mut idx = match self.pos[v] {
            OptionU32::NONE => return,
            idx => *idx,
        };
        while idx != 0 {
            let pidx = (idx - 1) >> 1;
            if activity[self.heap[pidx]] >= activity[v] {
                break;
            }
            self.heap[idx] = self.heap[pidx];
            *self.pos[self.heap[idx]] = idx;
            idx = pidx;
        }
        self.heap[idx] = v;
        *self.pos[v] = idx;
    }

    #[inline]
    fn down(&mut self, mut idx: u32, activity: &Activity) {
        let v = self.heap[idx];
        loop {
            let left = (idx << 1) + 1;
            if left >= self.heap.len() as u32 {
                break;
            }
            let right = left + 1;
            let child = if right < self.heap.len() as u32
                && activity[self.heap[right]] > activity[self.heap[left]]
            {
                right
            } else {
                left
            };
            if activity[v] >= activity[self.heap[child]] {
                break;
            }
            self.heap[idx] = self.heap[child];
            *self.pos[self.heap[idx]] = idx;
            idx = child;
        }
        self.heap[idx] = v;
        *self.pos[v] = idx;
    }

    #[inline]
    pub fn push(&mut self, var: Var, activity: &Activity) {
        if self.pos[var].is_some() {
            return;
        }
        let idx = self.heap.len() as u32;
        self.heap.push(var);
        *self.pos[var] = idx;
        self.up(var, activity);
    }

    #[inline]
    pub fn pop(&mut self, activity: &Activity) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let value = self.heap[0u32];
        self.heap[0u32] = self.heap[self.heap.len() - 1];
        *self.pos[self.heap[0u32]] = 0;
        self.pos[value] = OptionU32::NONE;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.down(0, activity);
        }
        Some(value)
    }
}

#[derive(Clone)]
pub struct Activity {
    activity: VarMap<f64>,
    act_inc: f64,
    bucket_heap: BinaryHeap,
}

impl Index<Var> for Activity {
    type Output = f64;

    #[inline]
    fn index(&self, index: Var) -> &Self::Output {
        &self.activity[index]
    }
}

impl Activity {
    #[inline]
    pub fn new_with(var: Var) -> Self {
        Self {
            activity: VarMap::new_with(var),
            act_inc: 1.0,
            bucket_heap: BinaryHeap::new_with(var),
        }
    }

    #[inline]
    fn check(&mut self, var: Var) {
        let act = unsafe { &mut *(self as *mut Activity) };
        if self.bucket_heap.pos[var].is_none() {
            self.bucket_heap.push(var, act);
        }
        assert!(self.bucket_heap.pos[var].is_some())
    }

    #[inline]
    fn unranked_bucket(&self) -> u32 {
        let len = self.bucket_heap.heap.len() as u32;
        if len == 0 {
            0
        } else {
            u32::BITS - (len - 1).leading_zeros() + 1
        }
    }

    #[inline]
    fn bucket(&self, var: Var) -> u32 {
        match self.bucket_heap.pos[var] {
            OptionU32::NONE => self.unranked_bucket(),
            pos => u32::BITS - pos.leading_zeros(),
        }
    }

    #[inline]
    pub fn bump(&mut self, var: Var) {
        self.activity[var] += self.act_inc;
        self.check(var);
        let act = unsafe { &mut *(self as *mut Activity) };
        self.bucket_heap.up(var, act);
        if self.activity[var] > 1e100 {
            self.activity.iter_mut().for_each(|a| a.mul_assign(1e-100));
            self.act_inc *= 1e-100;
        }
    }

    const DECAY: f64 = 0.95;

    #[inline]
    pub fn decay(&mut self) {
        self.act_inc *= 1.0 / Self::DECAY
    }
}

#[derive(Clone)]
pub struct Vsids {
    pub activity: Activity,
    pub heap: BinaryHeap,
    pub bucket: Bucket,
    pub enable_bucket: bool,
}

impl Vsids {
    pub fn new_with(var: Var) -> Self {
        Self {
            activity: Activity::new_with(var),
            heap: BinaryHeap::new_with(var),
            bucket: Bucket::new(),
            enable_bucket: true,
        }
    }

    #[inline]
    pub fn push(&mut self, var: Var, state: &mut VarState) {
        if self.enable_bucket {
            return self.bucket.push(var, &self.activity, state);
        }
        self.heap.push(var, &self.activity)
    }

    #[inline]
    pub fn pop(&mut self, state: &mut VarState) -> Option<Var> {
        if self.enable_bucket {
            return self.bucket.pop(state);
        }
        self.heap.pop(&self.activity)
    }

    #[inline]
    pub fn bump(&mut self, var: Var) {
        self.activity.bump(var);
        if !self.enable_bucket {
            self.heap.up(var, &self.activity);
        }
    }

    #[inline]
    pub fn decay(&mut self) {
        self.activity.decay();
    }
}

#[derive(Clone)]
pub struct Bucket {
    buckets: NckVec<NckVec<Var>>,
    head: u32,
}

impl Bucket {
    #[inline]
    fn new() -> Self {
        let mut buckets: NckVec<_> = NckVec::new();
        // A Lit can address fewer than 2^31 variables, so buckets 0..=32
        // cover every possible binary-heap rank plus the unranked bucket.
        buckets.reserve(u32::BITS as usize + 1);
        Self {
            buckets,
            head: Default::default(),
        }
    }

    #[inline]
    pub fn push(&mut self, var: Var, activity: &Activity, state: &mut VarState) {
        if !state.insert_bucket(var) {
            return;
        }
        let bucket = activity.bucket(var);
        if self.head > bucket {
            self.head = bucket;
        }
        self.buckets[bucket].push(var);
    }

    #[inline]
    pub fn pop(&mut self, state: &mut VarState) -> Option<Var> {
        while self.head < self.buckets.len() as u32 {
            if !self.buckets[self.head].is_empty() {
                let var = self.buckets[self.head].pop().unwrap();
                state.remove_bucket(var);
                return Some(var);
            }
            self.head += 1;
        }
        None
    }

    #[inline]
    pub fn clear(&mut self, state: &mut VarState) {
        while self.head < self.buckets.len() as u32 {
            while let Some(var) = self.buckets[self.head].pop() {
                state.remove_bucket(var);
            }
            self.head += 1;
        }
        for b in self.buckets.iter_mut() {
            b.clear();
        }
        self.head = 0;
    }
}

impl DagCnfSolver {
    #[inline]
    pub fn decide(&mut self) -> bool {
        while let Some(decide) = self.vsids.pop(&mut self.state) {
            let state = self.state.get(decide);
            if state.value().is_none() {
                let phase = state.phase();
                let decide = if !self.use_phase_saving || phase.is_none() {
                    Lit::new(decide, self.rng.random_bool(0.5))
                } else {
                    Lit::new(decide, phase != Lbool::FALSE)
                };
                self.pos_in_trail.push(self.trail.len() as u32);
                self.assign(decide, CREF_NONE);
                return true;
            }
        }
        false
    }
}
