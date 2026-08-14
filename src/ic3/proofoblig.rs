use log::trace;
use logicrs::{LitOrdVec, LitVec};
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

#[derive(Default)]
pub struct PoInner {
    pub frame: usize,
    pub input: Vec<LitVec>,
    pub state: LitOrdVec,
    pub depth: usize,
    pub next: Option<Po>,
    pub act: f64,
}

impl PartialEq for PoInner {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.state == other.state
    }
}

impl Eq for PoInner {}

impl PartialOrd for PoInner {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PoInner {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match other.frame.cmp(&self.frame) {
            Ordering::Equal => match self.depth.cmp(&other.depth) {
                Ordering::Equal => match other.state.len().cmp(&self.state.len()) {
                    Ordering::Equal => other.state.cmp(&self.state),
                    ord => ord,
                },
                ord => ord,
            },
            ord => ord,
        }
    }
}

impl Debug for PoInner {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProofObligation")
            .field("frame", &self.frame)
            .field("lemma", &self.state)
            .field("depth", &self.depth)
            .finish()
    }
}

#[derive(Clone, Default)]
pub struct Po {
    inner: Rc<PoInner>,
}

impl Po {
    pub fn new(
        frame: usize,
        lemma: LitOrdVec,
        input: Vec<LitVec>,
        depth: usize,
        next: Option<Self>,
    ) -> Self {
        Self {
            inner: Rc::new(PoInner {
                frame,
                input,
                state: lemma,
                depth,
                next,
                act: 0.0,
            }),
        }
    }

    pub fn push_to(&mut self, frame: usize) {
        for _ in self.frame..frame {
            self.act *= 0.6;
        }
        self.frame = frame;
    }
}

impl Deref for Po {
    type Target = PoInner;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for Po {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(Rc::as_ptr(&self.inner) as *mut PoInner) }
    }
}

impl PartialEq for Po {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Po {}

impl PartialOrd for Po {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Po {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl Debug for Po {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[derive(Default, Debug)]
pub struct Poq {
    obligations: BTreeSet<Po>,
    num: Vec<usize>,
}

impl Poq {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, po: Po) {
        if self.num.len() <= po.frame {
            self.num.resize(po.frame + 1, 0);
        }
        self.num[po.frame] += 1;
        trace!("add obligation: {}", po.state.as_litvec());
        assert!(self.obligations.insert(po));
    }

    pub fn pop(&mut self, depth: usize) -> Option<Po> {
        if let Some(po) = self.obligations.last().filter(|po| po.frame <= depth) {
            self.num[po.frame] -= 1;
            self.obligations.pop_last()
        } else {
            None
        }
    }

    pub fn peak(&mut self) -> Option<Po> {
        self.obligations.last().cloned()
    }

    pub fn remove(&mut self, po: &Po) -> bool {
        let ret = self.obligations.remove(po);
        if ret {
            self.num[po.frame] -= 1;
        }
        ret
    }

    pub fn clear(&mut self) {
        self.obligations.clear();
        for n in self.num.iter_mut() {
            *n = 0;
        }
    }

    pub fn statistic(&self) -> String {
        format!("{:?}", self.num)
    }
}
