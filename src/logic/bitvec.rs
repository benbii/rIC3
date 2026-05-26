use crate::nckvec::NckVec;
use rand::rngs::StdRng;
use std::{
    fmt::{self, Debug, Display},
    hash::Hash,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

#[derive(Clone)]
pub struct BitVec {
    bits: NckVec<u64>,
    last_len: usize,
}

impl BitVec {
    pub const WORD_SIZE: usize = 64;
    pub const WORD_SIZE_MASK: usize = Self::WORD_SIZE - 1;

    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn new_rand(num_word: usize, rng: &mut StdRng) -> Self {
        if num_word == 0 {
            return Self::default();
        }
        let mut bits = NckVec::new_rand(num_word, rng);
        bits.push(0);
        bits[0] &= u64::MAX - 1;
        bits[0] |= 2u64;
        Self {
            bits,
            last_len: 0,
        }
    }

    pub fn from_elem(len: usize, val: bool) -> Self {
        if len == 0 {
            return Self::default();
        }
        let v = if val { u64::MAX } else { 0 };
        let mut bits = NckVec::from(vec![v; len / Self::WORD_SIZE]);
        let last_len = len & Self::WORD_SIZE_MASK;
        bits.push(if val { (1u64 << last_len) - 1 } else { 0 });
        Self { bits, last_len }
    }

    pub fn from_usize(len: usize, v: usize) -> Self {
        if len == 0 {
            return Self::default();
        }
        let mut res = Self::zero(len);
        res.bits[0] = v as u64;
        res.mask_last();
        res
    }

    #[inline]
    pub fn len(&self) -> usize {
        (self.bits.len() - 1) * 64 + self.last_len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        debug_assert!(self.bits.len() >= 1);
        self.bits.len() == 1 && self.last_len == 0
    }

    #[inline]
    pub fn clear(&mut self) {
        self.bits.clear();
        self.bits.push(0);
        self.last_len = 0;
    }

    #[inline]
    pub fn get(&self, index: usize) -> bool {
        debug_assert!(index < self.len());
        let word_index = index / 64;
        let bit_index = index % 64;
        let mask = 1 << bit_index;
        (self.bits[word_index] & mask) != 0
    }

    #[inline]
    pub fn set(&mut self, index: usize, val: bool) {
        debug_assert!(index < self.len());
        let word_index = index / 64;
        let bit_index = index % 64;
        let mask = 1 << bit_index;
        if val {
            self.bits[word_index] |= mask;
        } else {
            self.bits[word_index] &= !mask;
        }
    }

    fn mask_last(&mut self) {
        let last = unsafe { self.bits.last_mut().unwrap_unchecked() };
        let mask = (1u64 << self.last_len) - 1;
        *last &= mask;
    }

    // If the last 2 words tell lhs != rhs.not_if(inv) then true.
    // Should be useful in both updated `scorr` and `frts`
    pub fn ne_inv(&self, rhs: &Self, inv: bool) -> bool {
        debug_assert!(self.len() == rhs.len());
        if self.is_empty() {
            return false;
        }
        let at = self.bits.len() - 1;
        let mask = (1u64 << self.last_len) - 1;
        let xor = if inv { u64::MAX } else { 0u64 };
        if (self.bits[at] & mask) != ((rhs.bits[at] ^ xor) & mask) {
            return true;
        }
        for i in (0..at).rev() {
            if self.bits[i] != rhs.bits[i] ^ xor {
                return true;
            }
        }
        false
    }

    pub fn push(&mut self, bit: bool) {
        let mask = 1 << self.last_len;
        let x = unsafe { self.bits.last_mut().unwrap_unchecked() };
        if bit {
            *x |= mask;
        } else {
            *x &= !mask;
        }
        self.last_len += 1;
        if self.last_len == 64 {
            self.bits.push(0);
            self.last_len = 0;
        }
    }

    #[inline]
    pub fn zero(len: usize) -> Self {
        Self::from_elem(len, false)
    }

    #[inline]
    pub fn ones(len: usize) -> Self {
        debug_assert!(len > 0);
        Self::from_elem(len, true)
    }

    #[inline]
    pub fn one(len: usize) -> Self {
        debug_assert!(len > 0);
        let mut r = Self::from_elem(len, false);
        r.set(0, true);
        r
    }

    pub fn is_zero(&self) -> bool {
        self.bits.iter().all(|x| *x == 0)
    }

    pub fn is_one(&self) -> bool {
        if self.bits[0] != 1u64 {
            return false;
        }
        self.bits.iter().skip(1).all(|x| *x == 0)
    }

    pub fn is_ones(&self) -> bool {
        debug_assert!(!self.is_empty());
        let (last, full_words) = self.bits.split_last().unwrap();
        full_words.iter().all(|&word| word == u64::MAX) && *last == (1u64 << self.last_len) - 1
    }

    pub fn iter(&self) -> Iter<'_> {
        Iter {
            bv: self,
            start: 0,
            end: self.len(),
        }
    }

    #[inline]
    pub fn bool(&self) -> bool {
        self.get(0)
    }
}

impl AsRef<Self> for BitVec {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

pub struct Iter<'a> {
    bv: &'a BitVec,
    start: usize,
    end: usize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = bool;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let res = self.bv.get(self.start);
            self.start += 1;
            Some(res)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end - self.start;
        (len, Some(len))
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            self.end -= 1;
            Some(self.bv.get(self.end))
        } else {
            None
        }
    }
}

impl<'a> ExactSizeIterator for Iter<'a> {}

impl<'a> IntoIterator for &'a BitVec {
    type Item = bool;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl Default for BitVec {
    #[inline]
    fn default() -> Self {
        Self {
            bits: NckVec::from([0]),
            last_len: 0,
        }
    }
}

impl PartialEq for BitVec {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.last_len == other.last_len && self.bits.as_slice() == other.bits.as_slice()
    }
}

impl Eq for BitVec {}

impl Hash for BitVec {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for &bit in self.bits.iter() {
            bit.hash(state);
        }
        self.last_len.hash(state);
    }
}

impl Not for &BitVec {
    type Output = BitVec;

    #[inline]
    fn not(self) -> BitVec {
        let mut res = self.clone();
        for r in res.bits.iter_mut() {
            *r = !*r;
        }
        res.mask_last();
        res
    }
}

macro_rules! impl_bitop_owned_and_ref {
    (
        trait = $trait:ident,
        method = $method:ident,
        op = $op:tt,
    ) => {
        impl<R: AsRef<BitVec>> $trait<R> for BitVec {
            type Output = BitVec;

            #[inline]
            fn $method(self, rhs: R) -> Self::Output {
                assert!(self.len() == rhs.as_ref().len());
                let mut res = BitVec {
                    bits: self
                        .bits
                        .iter()
                        .zip(rhs.as_ref().bits.iter())
                        .map(|(s, r)| s $op r)
                        .collect(),
                    last_len: self.last_len,
                };
                res.mask_last();
                res
            }
        }

        impl<R: AsRef<BitVec>> $trait<R> for &BitVec {
            type Output = BitVec;

            #[inline]
            fn $method(self, rhs: R) -> Self::Output {
                assert!(self.len() == rhs.as_ref().len());
                let mut res = BitVec {
                    bits: self
                        .bits
                        .iter()
                        .zip(rhs.as_ref().bits.iter())
                        .map(|(s, r)| s $op r)
                        .collect(),
                    last_len: self.last_len,
                };
                res.mask_last();
                res
            }
        }
    };
}

macro_rules! impl_bitassign_ref {
    (
        trait = $trait:ident,
        method = $method:ident,
        op = $op:tt,
    ) => {
        impl $trait<&BitVec> for BitVec {
            #[inline]
            fn $method(&mut self, rhs: &BitVec) {
                assert!(self.len() == rhs.len());
                for (s, r) in self.bits.iter_mut().zip(rhs.bits.iter()) {
                    *s $op r;
                }
                self.mask_last();
            }
        }
    };
}

impl_bitop_owned_and_ref!(
    trait = BitAnd,
    method = bitand,
    op = &,
);

impl_bitop_owned_and_ref!(
    trait = BitOr,
    method = bitor,
    op = |,
);

impl_bitop_owned_and_ref!(
    trait = BitXor,
    method = bitxor,
    op = ^,
);

impl_bitassign_ref!(
    trait = BitAndAssign,
    method = bitand_assign,
    op = &=,
);

impl_bitassign_ref!(
    trait = BitOrAssign,
    method = bitor_assign,
    op = |=,
);

impl_bitassign_ref!(
    trait = BitXorAssign,
    method = bitxor_assign,
    op = ^=,
);

impl<const N: usize> From<[bool; N]> for BitVec {
    #[inline]
    fn from(s: [bool; N]) -> Self {
        let mut r = Self::new();
        for x in s.into_iter() {
            r.push(x);
        }
        r
    }
}

impl<const N: usize> From<&[bool; N]> for BitVec {
    #[inline]
    fn from(s: &[bool; N]) -> Self {
        let mut r = Self::new();
        for x in s {
            r.push(*x);
        }
        r
    }
}

impl From<&[bool]> for BitVec {
    #[inline]
    fn from(s: &[bool]) -> Self {
        let mut r = Self::new();
        for x in s.iter() {
            r.push(*x);
        }
        r
    }
}

impl FromIterator<bool> for BitVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut r = Self::new();
        for x in iter.into_iter() {
            r.push(x);
        }
        r
    }
}

impl Extend<bool> for BitVec {
    fn extend<T: IntoIterator<Item = bool>>(&mut self, iter: T) {
        for x in iter {
            self.push(x);
        }
    }
}

impl Debug for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "[]");
        }
        let mut s = String::new();
        for i in (0..self.len()).rev() {
            if self.get(i) {
                s.push('1');
            } else {
                s.push('0');
            }
        }
        write!(f, "{s}")
    }
}

impl Display for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl fmt::LowerHex for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "[]");
        }
        write!(f, "0x")?;
        if self.is_zero() {
            return write!(f, "0");
        }
        let mut last = self.bits.len() - 1;
        if self.last_len == 0 {
            last -= 1;
        }
        write!(f, "{:x}", self.bits[last])?;
        for i in (0..last).rev() {
            write!(f, "{:016x}", self.bits[i])?;
        }
        Ok(())
    }
}

impl fmt::UpperHex for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "[]");
        }
        write!(f, "0x")?;
        if self.is_zero() {
            return write!(f, "0");
        }
        let mut last = self.bits.len() - 1;
        if self.last_len == 0 {
            last -= 1;
        }
        write!(f, "{:X}", self.bits[last])?;
        for i in (0..last).rev() {
            write!(f, "{:016X}", self.bits[i])?;
        }
        Ok(())
    }
}

impl fmt::Binary for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RseedSet as HashSet;

    #[test]
    fn test0() {
        let v = [true, false, true, false, true];
        let bv = BitVec::from(v);
        for i in 0..bv.len() {
            assert_eq!(bv.get(i), v[i]);
        }
    }

    #[test]
    fn test1() {
        let bv = BitVec::from_elem(0, true);
        assert!(bv.is_empty());
        let mut bv = BitVec::default();
        assert!(bv.is_empty());
        bv.push(false);
        assert!(!bv.is_empty());
    }

    #[test]
    fn test2() {
        for w in 1..200 {
            let one = BitVec::one(w);
            assert!(one.is_one());
            let ones = BitVec::ones(w);
            assert!(ones.is_ones());
            let zero = BitVec::zero(w);
            assert!(zero.is_zero());
        }
    }

    #[test]
    fn test3() {
        let v = [true, false, true, true, false];
        let bv = BitVec::from(v);
        let mut iter = bv.iter();
        for &val in &v {
            assert_eq!(iter.next(), Some(val));
        }
        assert_eq!(iter.next(), None);
        for (i, val) in bv.iter().enumerate() {
            assert_eq!(val, v[i]);
        }
    }

    #[test]
    fn test_fmt() {
        let z = BitVec::new();
        assert_eq!(format!("{}", z), "[]");
        assert_eq!(format!("{:x}", z), "[]");
        assert_eq!(format!("{:X}", z), "[]");

        let v = 12345;
        let bv = BitVec::from_usize(64, v);
        let s = format!("{}", bv);
        assert_eq!(s.len(), 64);
        assert!(s.ends_with("11000000111001"));

        assert_eq!(format!("{:x}", bv), "0x3039");
        assert_eq!(format!("{:X}", bv), "0x3039");

        let mut bv_large = BitVec::zero(128);
        bv_large.bits[0] = u64::MAX;
        bv_large.bits[1] = 1_u64;

        assert_eq!(format!("{:x}", bv_large), "0x1ffffffffffffffff");
        assert_eq!(format!("{:X}", bv_large), "0x1FFFFFFFFFFFFFFFF");

        let s_large = format!("{}", bv_large);
        assert_eq!(s_large.len(), 128);
        let expected_suffix = "1".repeat(65);
        assert!(s_large.ends_with(&expected_suffix));
        assert!(s_large.starts_with('0'));
    }

    #[test]
    fn test_extend() {
        let mut bv = BitVec::new();
        bv.extend([true, false, true]);
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.get(0), true);
        assert_eq!(bv.get(1), false);
        assert_eq!(bv.get(2), true);

        bv.extend([false, true]);
        assert_eq!(bv.len(), 5);
        assert_eq!(bv.get(3), false);
        assert_eq!(bv.get(4), true);
    }

    #[test]
    fn test_double_ended_iter() {
        let v = [true, false, true, true, false, true, false, false];
        let bv = BitVec::from(v);

        let mut iter = bv.iter();
        let mut v_iter = v.iter().copied();
        while v_iter.len() > 0 {
            if v_iter.len() % 2 == 0 {
                assert_eq!(iter.next(), v_iter.next());
            } else {
                assert_eq!(iter.next_back(), v_iter.next_back());
            }
        }
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_hash_eq() {
        let a = BitVec::ones(64);
        let b = BitVec {
            bits: NckVec::from([u64::MAX, 0]),
            last_len: 0,
        };
        assert!(a == b);
        let mut s = HashSet::default();
        s.insert(a);
        s.insert(b);
        assert!(s.len() == 1);
    }

    #[test]
    fn test_push_word_boundary() {
        let mut bv = BitVec::new();
        for _ in 0..64 {
            bv.push(true);
        }
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.last_len, 0);
        assert_eq!(bv.bits.len(), 2);
        assert_eq!(bv.bits[0], u64::MAX);
        assert_eq!(bv.bits[1], 0u64);

        bv.push(true);
        assert_eq!(bv.len(), 65);
        assert_eq!(bv.last_len, 1);
        assert_eq!(bv.bits.len(), 2);
        assert_eq!(bv.bits[1], 1u64);
    }

    #[test]
    fn test_from_iter_str() {
        let bv0 = BitVec::from_usize(2, 2);
        let bv1 = BitVec::from_iter([false, true]);
        assert!(bv0 == bv1);
    }
}
