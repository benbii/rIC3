use crate::{Lit, LitSet, LitVec};
use std::ops::Deref;

#[derive(Debug, Default, Clone)]
pub struct LitOrdVec {
    cube: LitVec,
    sign: u128,
}

impl Deref for LitOrdVec {
    type Target = LitVec;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.cube
    }
}

impl PartialEq for LitOrdVec {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.sign != other.sign || self.len() != other.len() {
            return false;
        }
        for i in 0..self.cube.len() {
            if self[i] != other[i] {
                return false;
            }
        }
        true
    }
}

impl LitOrdVec {
    #[inline]
    pub fn new(mut lv: LitVec) -> Self {
        lv.sort();
        Self::ordered_new(lv)
    }

    #[inline]
    pub fn ordered_new(lv: LitVec) -> Self {
        debug_assert!(lv.is_sorted());
        let mut sign = 0;
        for l in lv.iter() {
            sign |= 1 << (Into::<u32>::into(*l) % u128::BITS);
        }
        Self { cube: lv, sign }
    }

    #[inline]
    pub fn as_litvec(&self) -> &LitVec {
        &self.cube
    }

    #[inline]
    pub fn into_litvec(self) -> LitVec {
        self.cube
    }

    #[inline]
    fn var_sign(&self) -> u128 {
        ((self.sign >> 1) | self.sign) & 113427455640312821154458202477256070485_u128
    }

    #[inline]
    pub fn subsume(&self, other: &LitOrdVec) -> bool {
        if self.cube.len() > other.cube.len() {
            return false;
        }
        if self.sign & other.sign != self.sign {
            return false;
        }
        self.cube.ordered_subsume(&other.cube)
    }

    #[inline]
    pub fn subsume_except_one(&self, other: &LitOrdVec) -> (bool, Option<Lit>) {
        if self.cube.len() > other.cube.len() {
            return (false, None);
        }
        let ss = self.var_sign();
        if ss & other.var_sign() != ss {
            return (false, None);
        }
        self.cube.ordered_subsume_except_one(&other.cube)
    }

    #[inline]
    pub fn subsume_set(&self, other: &LitOrdVec, other_lits: &LitSet) -> bool {
        if self.cube.len() > other.cube.len() {
            return false;
        }
        if self.sign & other.sign != self.sign {
            return false;
        }
        for l in self.iter() {
            if !other_lits.has(*l) {
                return false;
            }
        }
        true
    }
}
