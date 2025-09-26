//! this is like <https://github.com/paritytech/nohash-hasher>, but i have my opinions.

use std::any::type_name;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::marker::PhantomData;

pub trait NoHash: Hash {}

impl NoHash for u8 {}
impl NoHash for u16 {}
impl NoHash for u32 {}
impl NoHash for u64 {}
impl NoHash for usize {}
impl NoHash for i8 {}
impl NoHash for i16 {}
impl NoHash for i32 {}
impl NoHash for i64 {}
impl NoHash for isize {}

pub struct NoHasher<T>(u64, PhantomData<T>);

impl<T: NoHash> Hasher for NoHasher<T> {
    #[cold]
    #[inline(never)]
    fn write(&mut self, _bytes: &[u8]) {
        panic!("invalid use of nohash");
    }

    #[inline]
    fn write_u8(&mut self, n: u8) {
        self.0 = n as u64;
    }

    #[inline]
    fn write_u16(&mut self, n: u16) {
        self.0 = n as u64;
    }

    #[inline]
    fn write_u32(&mut self, n: u32) {
        self.0 = n as u64;
    }

    #[inline]
    fn write_u64(&mut self, n: u64) {
        self.0 = n;
    }

    #[inline]
    fn write_usize(&mut self, n: usize) {
        self.0 = n as u64;
    }

    #[inline]
    fn write_i8(&mut self, n: i8) {
        self.0 = n as u64;
    }

    #[inline]
    fn write_i16(&mut self, n: i16) {
        self.0 = n as u64;
    }

    #[inline]
    fn write_i32(&mut self, n: i32) {
        self.0 = n as u64;
    }

    #[inline]
    fn write_i64(&mut self, n: i64) {
        self.0 = n as u64;
    }

    #[inline]
    fn write_isize(&mut self, n: isize) {
        self.0 = n as u64;
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

impl<T> fmt::Debug for NoHasher<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple(type_name::<Self>()).field(&self.0).finish()
    }
}

// @BlindDerive
impl<T> Default for NoHasher<T> {
    #[inline]
    fn default() -> Self {
        Self(0, PhantomData)
    }
}

// @BlindDerive
impl<T> Clone for NoHasher<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

// @BlindDerive
impl<T> Copy for NoHasher<T> {}

pub type NoBuildHasher<T> = BuildHasherDefault<NoHasher<T>>;

pub type NoHashMap<K, V> = HashMap<K, V, NoBuildHasher<K>>;
pub type NoHashSet<T> = HashSet<T, NoBuildHasher<T>>;
