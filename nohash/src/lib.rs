//! this is like <https://github.com/paritytech/nohash-hasher>, but i have my opinions.
use std::{
    any::type_name,
    collections::{HashMap, HashSet},
    fmt,
    hash::{BuildHasherDefault, Hash, Hasher},
    marker::PhantomData,
};

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

pub struct NoHashHasher<T>(u64, PhantomData<T>);

impl<T: NoHash> Hasher for NoHashHasher<T> {
    fn write(&mut self, _bytes: &[u8]) {
        unreachable!();
    }

    fn write_u8(&mut self, n: u8) {
        self.0 = n as u64;
    }

    fn write_u16(&mut self, n: u16) {
        self.0 = n as u64;
    }

    fn write_u32(&mut self, n: u32) {
        self.0 = n as u64;
    }

    fn write_u64(&mut self, n: u64) {
        self.0 = n;
    }

    fn write_usize(&mut self, n: usize) {
        self.0 = n as u64;
    }

    fn write_i8(&mut self, n: i8) {
        self.0 = n as u64;
    }

    fn write_i16(&mut self, n: i16) {
        self.0 = n as u64;
    }

    fn write_i32(&mut self, n: i32) {
        self.0 = n as u64;
    }

    fn write_i64(&mut self, n: i64) {
        self.0 = n as u64;
    }

    fn write_isize(&mut self, n: isize) {
        self.0 = n as u64;
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

impl<T> fmt::Debug for NoHashHasher<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple(type_name::<Self>()).field(&self.0).finish()
    }
}

// @BlindDerive
impl<T> Default for NoHashHasher<T> {
    fn default() -> Self {
        Self(0, PhantomData)
    }
}

// @BlindDerive
impl<T> Clone for NoHashHasher<T> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

// @BlindDerive
impl<T> Copy for NoHashHasher<T> {}

pub type BuildNoHashHasher<T> = BuildHasherDefault<NoHashHasher<T>>;

pub type NoHashMap<K, V> = HashMap<K, V, BuildNoHashHasher<K>>;
pub type NoHashSet<T> = HashSet<T, BuildNoHashHasher<T>>;
