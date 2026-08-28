#![allow(non_snake_case)]
#![cfg_attr(test, allow(linker_messages))]

extern crate self as logicrs;

mod logic;
pub use logic::bitvec;
pub use logic::fol;
pub use logic::nckvec;
pub(crate) use logic::occur;

pub mod aig;
pub mod bitwuzla;
pub mod bmc;
pub mod btor;
pub mod cadical;
pub mod config;
pub mod frontend;
pub mod gipsat;
pub mod ic3;
pub mod kind;
pub mod kissat;
pub mod rlive;
pub mod transys;
pub mod wlbmc;
pub mod wlkind;
pub mod wltransys;
pub use logic::*;
use serde::{Deserialize, Serialize};

use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug, Display},
    hash::{BuildHasher, Hash},
    ops::Not,
};

#[derive(Clone)]
pub struct Ric3RandomState(ahash::RandomState);

impl Default for Ric3RandomState {
    #[inline]
    fn default() -> Self {
        Self(ahash::RandomState::with_seeds(0, 0, 0, 0))
    }
}

impl BuildHasher for Ric3RandomState {
    type Hasher = ahash::AHasher;

    #[inline]
    fn build_hasher(&self) -> Self::Hasher {
        self.0.build_hasher()
    }

    #[inline]
    fn hash_one<T: Hash>(&self, x: T) -> u64
    where
        Self: Sized,
    {
        self.0.hash_one(x)
    }
}

pub type RseedMap<K, V> = HashMap<K, V, Ric3RandomState>;
pub type RseedSet<T> = HashSet<T, Ric3RandomState>;

#[derive(
    Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default, Serialize, Deserialize, Debug,
)]
pub struct Var(pub u32);
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default, Serialize, Deserialize)]
pub struct Lit(pub u32);

impl Var {
    pub const CONST: Var = Var(0);

    #[inline]
    pub fn new(x: usize) -> Self {
        Self(x as _)
    }

    #[inline]
    pub fn lit(&self) -> Lit {
        Lit(self.0 << 1)
    }

    #[inline]
    pub fn is_constant(&self) -> bool {
        *self == Self::CONST
    }
}

impl AsRef<Var> for Var {
    #[inline]
    fn as_ref(&self) -> &Var {
        self
    }
}

impl Display for Var {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An iterator over a range of `Var` values (stable Rust compatible replacement for RangeInclusive<Var>)
#[derive(Clone, Debug)]
pub struct VarRange {
    inner: std::ops::RangeInclusive<u32>,
}

impl VarRange {
    #[inline]
    pub fn new_inclusive(start: Var, end: Var) -> Self {
        Self {
            inner: start.0..=end.0,
        }
    }
}

impl Iterator for VarRange {
    type Item = Var;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Var)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl DoubleEndedIterator for VarRange {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(Var)
    }
}

impl ExactSizeIterator for VarRange {}

impl Lit {
    #[inline]
    pub fn new(var: Var, polarity: bool) -> Self {
        Lit(var.0 + var.0 + !polarity as u32)
    }

    #[inline]
    pub fn var(&self) -> Var {
        Var(self.0 >> 1)
    }

    #[inline]
    pub fn polarity(&self) -> bool {
        self.0 & 1 == 0
    }

    #[inline]
    pub fn constant(polarity: bool) -> Self {
        Self::new(Var::CONST, !polarity)
    }

    #[inline]
    pub fn try_constant(&self) -> Option<bool> {
        self.var().is_constant().then_some(self.is_constant(true))
    }

    #[inline]
    pub fn is_constant(&self, polarity: bool) -> bool {
        *self == Self::constant(polarity)
    }

    #[inline]
    pub fn not_if(&self, c: bool) -> Self {
        if c { !*self } else { *self }
    }

    #[inline]
    pub fn map_var(&self, map: impl Fn(Var) -> Var) -> Self {
        Self::new(map(self.var()), self.polarity())
    }

    #[inline]
    pub fn filter_map_var(&self, map: impl Fn(Var) -> Option<Var>) -> Option<Self> {
        map(self.var()).map(|v| Self::new(v, self.polarity()))
    }
}

impl Not for Lit {
    type Output = Self;

    #[inline]
    fn not(mut self) -> Self::Output {
        self.0 ^= 1;
        self
    }
}

impl Not for &Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Self::Output {
        !*self
    }
}

impl AsRef<Lit> for Lit {
    #[inline]
    fn as_ref(&self) -> &Lit {
        self
    }
}

impl Debug for Lit {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.polarity() {
            write!(f, "{}", self.var())
        } else {
            write!(f, "-{}", self.var())
        }
    }
}

impl Display for Lit {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

pub use btor::Btor;

use crate::{
    transys::certify::{BlProof, BlWitness},
    wltransys::certify::{WlProof, WlWitness},
};
use enum_as_inner::EnumAsInner;

#[derive(Serialize, Deserialize, Clone, Copy, Debug, EnumAsInner)]
pub enum McResult {
    /// Safe
    Safe,
    /// Unsafe with Cex Depth
    Unsafe(usize),
    /// Proved in Some(exact depth)
    Unknown(usize),
}

#[derive(Clone, Debug, EnumAsInner)]
pub enum McProof {
    Bl(BlProof),
    Wl(WlProof),
}

#[derive(Clone, Debug, EnumAsInner)]
pub enum McWitness {
    Bl(BlWitness),
    Wl(WlWitness),
}

pub trait Engine {
    fn check(&mut self) -> McResult;
    fn statistic(&mut self) {}
    fn proof(&mut self) -> McProof {
        panic!("proof unsupported");
    }
    fn witness(&mut self) -> McWitness;
}
