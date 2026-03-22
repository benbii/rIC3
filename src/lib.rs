#![allow(non_snake_case)]

extern crate self as logicrs;

mod logic;
pub use logic::bitvec;
pub use logic::fol;
pub use logic::nckvec;
pub(crate) use logic::occur;
pub use logic::satif;
pub use logic::statistic;

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
    ops::{Add, AddAssign, Deref, Not, Sub},
};

pub const RIC3_HASH_SEED: [u64; 4] = [0, 0, 0, 0];

#[derive(Clone)]
pub struct Ric3RandomState(ahash::RandomState);

impl Default for Ric3RandomState {
    #[inline]
    fn default() -> Self {
        Self(ahash::RandomState::with_seeds(
            RIC3_HASH_SEED[0],
            RIC3_HASH_SEED[1],
            RIC3_HASH_SEED[2],
            RIC3_HASH_SEED[3],
        ))
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

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default, Serialize, Deserialize)]
pub struct Var(pub u32);

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

impl Add<Var> for Var {
    type Output = Var;

    #[inline]
    fn add(self, rhs: Var) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Sub<Var> for Var {
    type Output = Var;

    #[inline]
    fn sub(self, rhs: Var) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl AddAssign<Var> for Var {
    #[inline]
    fn add_assign(&mut self, rhs: Var) {
        self.0 += rhs.0;
    }
}

impl From<Lit> for Var {
    #[inline]
    fn from(value: Lit) -> Self {
        value.var()
    }
}

impl Deref for Var {
    type Target = u32;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<Var> for Var {
    #[inline]
    fn as_ref(&self) -> &Var {
        self
    }
}

impl AsMut<Var> for Var {
    #[inline]
    fn as_mut(&mut self) -> &mut Var {
        self
    }
}

impl Display for Var {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Debug for Var {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

macro_rules! impl_var_traits {
    ($T:ty) => {
        impl PartialEq<$T> for Var {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                self.0.eq(&(*other as u32))
            }
        }

        impl PartialOrd<$T> for Var {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&(*other as u32))
            }
        }

        impl From<Var> for $T {
            #[inline]
            fn from(value: Var) -> Self {
                value.0 as $T
            }
        }

        impl From<$T> for Var {
            #[inline]
            fn from(value: $T) -> Self {
                Self(value as u32)
            }
        }

        impl Add<$T> for Var {
            type Output = Var;

            #[inline]
            fn add(self, rhs: $T) -> Self::Output {
                Self(self.0 + rhs as u32)
            }
        }

        impl Sub<$T> for Var {
            type Output = Var;

            #[inline]
            fn sub(self, rhs: $T) -> Self::Output {
                Self(self.0 - rhs as u32)
            }
        }

        impl AddAssign<$T> for Var {
            #[inline]
            fn add_assign(&mut self, rhs: $T) {
                self.0 += rhs as u32;
            }
        }
    };
}

impl_var_traits!(u32);
impl_var_traits!(i32);
impl_var_traits!(usize);
impl_var_traits!(isize);

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

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default, Serialize, Deserialize)]
pub struct Lit(u32);

impl From<Var> for Lit {
    #[inline]
    fn from(value: Var) -> Self {
        Self(value.0 << 1)
    }
}

impl From<Lit> for u32 {
    #[inline]
    fn from(val: Lit) -> Self {
        val.0
    }
}

impl From<Lit> for i32 {
    #[inline]
    fn from(val: Lit) -> Self {
        let mut v: i32 = val.var().into();
        if !val.polarity() {
            v = -v;
        }
        v
    }
}

impl From<i32> for Lit {
    #[inline]
    fn from(value: i32) -> Self {
        Self::new(Var(value.unsigned_abs()), value > 0)
    }
}

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
    pub fn cube(&self) -> LitVec {
        LitVec::from([*self])
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

impl AsMut<Lit> for Lit {
    #[inline]
    fn as_mut(&mut self) -> &mut Lit {
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
    config::EngineConfig,
    transys::{
        Transys,
        certify::{BlProof, BlWitness},
    },
    wltransys::{
        WlTransys,
        certify::{WlProof, WlWitness},
    },
};
use enum_as_inner::EnumAsInner;
use std::ops::BitOr;

#[derive(Serialize, Deserialize, Clone, Copy, Debug, EnumAsInner)]
pub enum McResult {
    /// Safe
    Safe,
    /// Unsafe with Cex Depth
    Unsafe(usize),
    /// Proved in Some(exact depth)
    Unknown(Option<usize>),
}

impl Default for McResult {
    fn default() -> Self {
        McResult::Unknown(None)
    }
}

impl BitOr for McResult {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        use McResult::*;
        match (self, rhs) {
            (Safe, Unsafe(_)) | (Unsafe(_), Safe) => {
                panic!("conflicting results: safe and unsafe")
            }
            (Safe, _) | (_, Safe) => Safe,
            (Unsafe(a), Unsafe(b)) => Unsafe(a.max(b)),
            (Unsafe(a), Unknown(_)) | (Unknown(_), Unsafe(a)) => Unsafe(a),
            (Unknown(a), Unknown(b)) => Unknown(match (a, b) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            }),
        }
    }
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
        panic!("unsupport proof");
    }

    fn witness(&mut self) -> McWitness {
        panic!("unsupport witness");
    }
}

pub fn create_bl_engine(cfg: EngineConfig, ts: Transys) -> Box<dyn Engine> {
    match cfg {
        EngineConfig::IC3(cfg) => Box::new(ic3::IC3::new(cfg, ts)),
        EngineConfig::Kind(cfg) => Box::new(kind::Kind::new(cfg, ts)),
        EngineConfig::BMC(cfg) => Box::new(bmc::BMC::new(cfg, ts)),
        EngineConfig::Rlive(cfg) => Box::new(rlive::Rlive::new(cfg, ts)),
        _ => unreachable!(),
    }
}

pub fn create_wl_engine(cfg: EngineConfig, ts: WlTransys) -> Box<dyn Engine> {
    match cfg {
        EngineConfig::WlBMC(cfg) => Box::new(wlbmc::WlBMC::new(cfg, ts)),
        EngineConfig::WlKind(cfg) => Box::new(wlkind::WlKind::new(cfg, ts)),
        _ => unreachable!(),
    }
}
