use crate::nckvec::NckVec;
use crate::{Lit, LitMap, Var};

#[derive(Debug, Clone, Default)]
struct Occur {
    occur: NckVec<usize>,
    dirty: bool,
    size: usize,
}

impl Occur {
    #[inline]
    fn len(&self) -> usize {
        self.size
    }

    #[inline]
    fn clean<T>(&mut self, cdb: &NckVec<(T, bool)>) {
        if self.dirty {
            self.occur.retain(|&i| !cdb[i].1);
            self.dirty = false;
        }
    }

    #[inline]
    fn add(&mut self, c: usize) {
        self.occur.push(c);
        self.size += 1;
    }

    #[inline]
    fn lazy_remove(&mut self) {
        self.dirty = true;
        self.size -= 1;
    }
}

pub(crate) struct Occurs<T> {
    occurs: LitMap<Occur>,
    _t: std::marker::PhantomData<T>,
}

impl<T> Occurs<T> {
    #[inline]
    pub(crate) fn new_with(var: Var) -> Self {
        Self {
            occurs: LitMap::new_with(var),
            _t: std::marker::PhantomData,
        }
    }

    #[inline]
    pub(crate) fn num_occur(&self, l: Lit) -> usize {
        self.occurs[l].len()
    }

    #[inline]
    pub(crate) fn add(&mut self, lit: Lit, o: usize) {
        self.occurs[lit].add(o);
    }

    #[inline]
    pub(crate) fn del(&mut self, lit: Lit, _o: usize) {
        self.occurs[lit].lazy_remove();
    }

    #[inline]
    pub(crate) fn get(&mut self, lit: Lit, cdb: &NckVec<(T, bool)>) -> &[usize] {
        self.occurs[lit].clean(cdb);
        &self.occurs[lit].occur
    }
}
