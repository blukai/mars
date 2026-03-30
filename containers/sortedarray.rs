use core::cmp::Ordering;
use core::fmt;

use alloc::{AllocError, Allocator};

use crate::array::{Array, InsertError, InsertErrorKind};
use crate::arraymemory::{
    ArrayMemory, FixedArrayMemory, GrowableArrayMemory, SpillableArrayMemory,
};

// NOTE: this can be used instead of hashmap.
//   good for small number of pairs.
//   better then the hashmap for <= 128 items for sure (see benchmark).
//   - `insert` is o(n);
//   - `get` performs binary search.

// NOTE: i am too lazy to duplicate majority of Array's methods in impls.
//   feel free to use any non-mutating method of the underlying array(.0);
//   but mutating it is illegal.

/// you may wish to implement SortedArrayCompare if comparison logic that your SortedArray* type
/// needs is incompatible with Ord that you may need for other purposes..
pub trait SortedArrayCompare {
    fn cmp(&self, other: &Self) -> Ordering;
}

impl<T: Ord> SortedArrayCompare for T {
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(self, other)
    }
}

// ----
// sorted array map

pub struct SortedArrayMap<K, V, M: ArrayMemory<(K, V)>>(pub Array<(K, V), M>);

impl<K, V, M: ArrayMemory<(K, V)>> SortedArrayMap<K, V, M> {
    #[inline]
    pub fn new_in<I: Into<M>>(mem: I) -> Self {
        Self(Array::new_in(mem))
    }
}

impl<K: SortedArrayCompare, V, M: ArrayMemory<(K, V)>> SortedArrayMap<K, V, M> {
    pub fn try_insert(&mut self, key: K, value: V) -> Result<Option<V>, InsertError<(K, V)>> {
        let index = self
            .0
            .partition_point(|(k, _)| SortedArrayCompare::cmp(k, &key) == Ordering::Less);
        match self.0.get(index) {
            // TODO: does it matter which value i return?
            Some((k, ..)) if SortedArrayCompare::cmp(k, &key) == Ordering::Equal => Ok(Some(value)),
            _ => self.0.try_insert(index, (key, value)).map(|_| None),
        }
    }

    // ----
    // extend from

    pub fn try_extend_from_iter<I: Iterator<Item = (K, V)>>(
        &mut self,
        iter: I,
    ) -> Result<(), AllocError> {
        self.0.try_extend_from_iter(iter)?;
        self.0.sort_by(|(a, _), (b, _)| a.cmp(b));
        Ok(())
    }

    // ----
    // array deviations

    pub fn contains(&self, key: &K) -> bool {
        self.0.binary_search_by(|(k, _)| k.cmp(key)).is_ok()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.0
            .binary_search_by(|(k, _)| k.cmp(key))
            .ok()
            .map(|found| unsafe { &self.0.get_unchecked(found).1 })
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self.0
            .binary_search_by(|(k, _)| k.cmp(key))
            .ok()
            .map(|found| unsafe { &mut self.0.get_unchecked_mut(found).1 })
    }
}

impl<K, V, M: ArrayMemory<(K, V)> + Default> Default for SortedArrayMap<K, V, M> {
    #[inline]
    fn default() -> Self {
        Self::new_in(M::default())
    }
}

impl<K: fmt::Debug, V: fmt::Debug, M: ArrayMemory<(K, V)>> fmt::Debug for SortedArrayMap<K, V, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0.as_slice(), f)
    }
}

// NOTE: this macro is similar what would be an equivalent in the underlying array.
//   i did a macro thing because i may want to impl partial eq not only for direct comparison, but
//   for other rhs variants (same as array has).
macro_rules! impl_partial_eq_for_map {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty $(where $ty:ty: $bound:ident)?) => {
        impl<K1, V1, K2, V2, $($vars)*> PartialEq<$rhs> for $lhs
        where
            (K1, V1): PartialEq<(K2, V2)>,
            $($ty: $bound)?
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { self.0[..] == other.0[..] }
        }
    }
}

impl_partial_eq_for_map! {
    [M1: ArrayMemory<(K1, V1)>, M2: ArrayMemory<(K2, V2)>] SortedArrayMap<K1, V1, M1>, SortedArrayMap<K2, V2, M2>
}

// ----
// aliases and their makers below

#[expect(type_alias_bounds)]
pub type GrowableSortedArrayMap<K, V, A: Allocator> =
    SortedArrayMap<K, V, GrowableArrayMemory<(K, V), A>>;

pub type FixedSortedArrayMap<K, V, const N: usize> =
    SortedArrayMap<K, V, FixedArrayMemory<(K, V), N>>;

impl<K: Clone, V: Clone, const N: usize> Clone for FixedSortedArrayMap<K, V, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[expect(type_alias_bounds)]
pub type SpillableSortedArrayMap<K, V, const N: usize, A: Allocator> =
    SortedArrayMap<K, V, SpillableArrayMemory<(K, V), N, A>>;

// ----
// sorted array set

pub struct SortedArraySet<T, M: ArrayMemory<T>>(pub Array<T, M>);

impl<T, M: ArrayMemory<T>> SortedArraySet<T, M> {
    #[inline]
    pub fn new_in<I: Into<M>>(mem: I) -> Self {
        Self(Array::new_in(mem))
    }
}

impl<T: SortedArrayCompare, M: ArrayMemory<T>> SortedArraySet<T, M> {
    pub fn try_insert(&mut self, value: T) -> Result<Option<T>, InsertError<T>> {
        let index = self
            .0
            .partition_point(|v| SortedArrayCompare::cmp(v, &value) == Ordering::Less);
        match self.0.get(index) {
            // TODO: does it matter which value i return?
            Some(v) if SortedArrayCompare::cmp(v, &value) == Ordering::Equal => Ok(Some(value)),
            _ => self.0.try_insert(index, value).map(|_| None),
        }
    }

    // ----
    // extend from

    pub fn try_extend_from_iter<I: Iterator<Item = T>>(
        &mut self,
        iter: I,
    ) -> Result<(), AllocError> {
        self.0.try_extend_from_iter(iter)?;
        self.0.sort_by(|a, b| a.cmp(b));
        Ok(())
    }

    // ----
    // array deviations

    pub fn contains(&self, value: &T) -> bool {
        self.0.binary_search_by(|v| v.cmp(value)).is_ok()
    }
}

impl<T, M: ArrayMemory<T> + Default> Default for SortedArraySet<T, M> {
    #[inline]
    fn default() -> Self {
        Self::new_in(M::default())
    }
}

impl<T: fmt::Debug, M: ArrayMemory<T>> fmt::Debug for SortedArraySet<T, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0.as_slice(), f)
    }
}

// ----
// aliases and their makers below

#[expect(type_alias_bounds)]
pub type GrowableSortedArraySet<T, A: Allocator> = SortedArraySet<T, GrowableArrayMemory<T, A>>;

pub type FixedSortedArraySet<T, const N: usize> = SortedArraySet<T, FixedArrayMemory<T, N>>;

impl<T: Clone, const N: usize> Clone for FixedSortedArraySet<T, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[expect(type_alias_bounds)]
pub type SpillableSortedArraySet<T, const N: usize, A: Allocator> =
    SortedArraySet<T, SpillableArrayMemory<T, N, A>>;

// NOTE: this macro is similar what would be an equivalent in the underlying array.
//   i did a macro thing because i may want to impl partial eq not only for direct comparison, but
//   for other rhs variants (same as array has).
macro_rules! impl_partial_eq_for_set {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty $(where $ty:ty: $bound:ident)?) => {
        impl<T1, T2, $($vars)*> PartialEq<$rhs> for $lhs
        where
            T1: PartialEq<T2>,
            $($ty: $bound)?
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { self.0[..] == other.0[..] }
        }
    }
}

impl_partial_eq_for_set! {
    [M1: ArrayMemory<T1>, M2: ArrayMemory<T2>] SortedArraySet<T1, M1>, SortedArraySet<T2, M2>
}

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use crate::{eek, this_is_fine};

    use super::*;

    impl<K: SortedArrayCompare, V, M: ArrayMemory<(K, V)>> SortedArrayMap<K, V, M> {
        pub fn insert(&mut self, key: K, value: V) {
            match self.try_insert(key, value) {
                Ok(..) => {}
                Err(InsertError {
                    kind: InsertErrorKind::OutOfMemory(alloc_error),
                    ..
                }) => eek(alloc_error),
                Err(InsertError {
                    kind: InsertErrorKind::OutOfBounds { index, len },
                    ..
                }) => panic!("out of bounds (index {index}, len {len})"),
            }
        }

        // ----
        // extend from

        #[inline]
        pub fn extend_from_iter<I: Iterator<Item = (K, V)>>(&mut self, iter: I) {
            this_is_fine(self.try_extend_from_iter(iter))
        }
    }

    // :TryCloneIn
    impl<K: Clone, V: Clone, A: Allocator + Clone> Clone for GrowableSortedArrayMap<K, V, A> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    // :TryCloneIn
    impl<K: Clone, V: Clone, const N: usize, A: Allocator + Clone> Clone
        for SpillableSortedArrayMap<K, V, N, A>
    {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: SortedArrayCompare, M: ArrayMemory<T>> SortedArraySet<T, M> {
        pub fn insert(&mut self, value: T) {
            match self.try_insert(value) {
                Ok(..) => {}
                Err(InsertError {
                    kind: InsertErrorKind::OutOfMemory(alloc_error),
                    ..
                }) => eek(alloc_error),
                Err(InsertError {
                    kind: InsertErrorKind::OutOfBounds { index, len },
                    ..
                }) => panic!("out of bounds (index {index}, len {len})"),
            }
        }

        // ----
        // extend from

        #[inline]
        pub fn extend_from_iter<I: Iterator<Item = T>>(&mut self, iter: I) {
            this_is_fine(self.try_extend_from_iter(iter))
        }
    }

    // :TryCloneIn
    impl<T: Clone, A: Allocator + Clone> Clone for GrowableSortedArraySet<T, A> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    // :TryCloneIn
    impl<T: Clone, const N: usize, A: Allocator + Clone> Clone for SpillableSortedArraySet<T, N, A> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }
}

// ----

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_insert() {
        let mut this = GrowableSortedArrayMap::<u32, (), _>::new_in(alloc::Global);
        this.insert(42, ());
        this.insert(64, ());
        this.insert(64, ());
        this.insert(27, ());
        assert_eq!(this.0.as_slice(), &[(27, ()), (42, ()), (64, ())]);
    }

    #[test]
    fn test_map_get() {
        let mut this = GrowableSortedArrayMap::<u32, &'static str, _>::new_in(alloc::Global);
        this.insert(0, "zero");
        this.insert(8, "hachi");
        this.insert(16, "juuroku");
        assert_eq!(this.get(&8), Some(&"hachi"));
    }

    #[test]
    fn test_set_insert() {
        let mut this = GrowableSortedArraySet::<u32, _>::new_in(alloc::Global);
        this.insert(64);
        this.insert(42);
        this.insert(27);
        this.insert(64);
        assert_eq!(this.0.as_slice(), &[27, 42, 64]);
    }

    #[test]
    fn test_set_contains() {
        let mut this = GrowableSortedArraySet::<&'static str, _>::new_in(alloc::Global);
        this.insert("zero");
        this.insert("hachi");
        this.insert("juuroku");
        assert!(this.contains(&"zero"));
        assert!(!this.contains(&"ichi"));
    }
}
