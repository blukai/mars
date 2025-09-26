//! this is const hash function based on what's used in firefox.
//!
//! custom implementation of hash functions? why? simply because i need them to be
//! const(/comptime); none of the crates that i went throuh had reasonable implementations.
//!
//! also note that fxhash was previosly used by rustc_hash crate that rust compiler uses for their
//! hashing needs, but not anymore.
//! see <https://github.com/rust-lang/rustc-hash/pull/37>.
//!
//! a little bit more info on fx hash is available on
//! <https://nnethercote.github.io/2021/12/08/a-brutally-effective-hash-function-in-rust.html>
//!
//! from firefox:
//! ```quote
//! This is the meat of all our hash routines.  This hash function is not
//! particularly sophisticated, but it seems to work well for our mostly
//! plain-text inputs.  Implementation notes follow.
//!
//! Our use of the golden ratio here is arbitrary; we could pick almost any
//! number which:
//!
//!  * is odd (because otherwise, all our hash values will be even)
//!
//!  * has a reasonably-even mix of 1's and 0's (consider the extreme case
//!    where we multiply by 0x3 or 0xeffffff -- this will not produce good
//!    mixing across all bits of the hash).
//!
//! The rotation length of 5 is also arbitrary, although an odd number is again
//! preferable so our hash explores the whole universe of possible rotations.
//!
//! Finally, we multiply by the golden ratio *after* xor'ing, not before.
//! Otherwise, if |aHash| is 0 (as it often is for the beginning of a
//! message), the expression
//!
//!   mozilla::WrappingMultiply(kGoldenRatioU32, RotateLeft5(aHash))
//!   |xor|
//!   aValue
//!
//! evaluates to |aValue|.
//!
//! (Number-theoretic aside: Because any odd number |m| is relatively prime to
//! our modulus (2**32), the list
//!
//!    [x * m (mod 2**32) for 0 <= x < 2**32]
//!
//! has no duplicate elements.  This means that multiplying by |m| does not
//! cause us to skip any possible hash values.
//!
//! It's also nice if |m| has large-ish order mod 2**32 -- that is, if the
//! smallest k such that m**k == 1 (mod 2**32) is large -- so we can safely
//! multiply our hash value by |m| a few times without negating the
//! multiplicative effect.  Our golden ratio constant has order 2**29, which is
//! more than enough for our purposes.)
//! ```
//!
//! see <https://searchfox.org/firefox-main/rev/57c85839a717f3a5e1c854150f1e5743133fbdda/mfbt/HashFunctions.h>
//! and <https://searchfox.org/firefox-main/rev/f32cfcbfa2ec5417780e0d8d7b16530523a009c2/mfbt/HashFunctions.cpp>

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

// NOTE: u64 golden ration is stolen from old version of rustc_hash
//   see <https://github.com/rust-lang/rustc-hash/blob/786ccda70fce97a3177d6088f21a22ac7f0f2f85/src/lib.rs#L67>
const GOLDEN_RATIO: u64 = 0x517cc1b727220a95;
const ROTATION_LENGTH: u32 = 5;

#[inline(always)]
pub const fn add_u64_to_hash(hash: u64, value: u64) -> u64 {
    (hash.rotate_left(ROTATION_LENGTH) ^ value).wrapping_mul(GOLDEN_RATIO)
}

#[inline]
pub const fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0;
    let mut i: usize = 0;

    // hash as u64s first
    let p = bytes.as_ptr();
    while i < bytes.len() - (bytes.len() % size_of::<u64>()) {
        let value = unsafe { std::ptr::read_unaligned(p.add(i) as *const u64) };
        hash = add_u64_to_hash(hash, value);
        i += size_of::<u64>();
    }

    // and now hash remaining bytes
    while i < bytes.len() {
        let value = bytes[i] as u64;
        hash = add_u64_to_hash(hash, value);
        i += 1;
    }

    // NOTE: you might want to xor by len (same as new rusrc-hash does)?
    hash
}

#[derive(Default, Clone, Copy)]
pub struct FxHasher(u64);

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        self.0 = add_u64_to_hash(self.0, hash_bytes(bytes));
    }

    #[inline]
    fn write_u8(&mut self, n: u8) {
        self.0 = add_u64_to_hash(self.0, n as u64);
    }

    #[inline]
    fn write_u16(&mut self, n: u16) {
        self.0 = add_u64_to_hash(self.0, n as u64);
    }

    #[inline]
    fn write_u32(&mut self, n: u32) {
        self.0 = add_u64_to_hash(self.0, n as u64);
    }

    #[inline]
    fn write_u64(&mut self, n: u64) {
        self.0 = add_u64_to_hash(self.0, n);
    }

    #[inline]
    fn write_usize(&mut self, n: usize) {
        self.0 = add_u64_to_hash(self.0, n as u64);
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

pub type FxBuildHasher = BuildHasherDefault<FxHasher>;

pub type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;
pub type FxHashSet<T> = HashSet<T, FxBuildHasher>;
