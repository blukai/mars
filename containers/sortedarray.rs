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
//   feel free to use any non-mutating method of the underlying vector (0);
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
// sorted vector map

pub struct SortedArrayMap<K, V, M: ArrayMemory<(K, V)>>(pub Array<(K, V), M>);

impl<K, V, M: ArrayMemory<(K, V)>> SortedArrayMap<K, V, M> {
    #[inline]
    pub fn new_in(mem: M) -> Self {
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
    // builder-lite with

    pub fn try_with_iter<I: Iterator<Item = (K, V)>>(
        mut self,
        iter: I,
    ) -> Result<Self, AllocError> {
        self.try_extend_from_iter(iter)?;
        Ok(self)
    }

    // ----
    // vector deviations

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

// ----
// aliases and their makers below

#[expect(type_alias_bounds)]
pub type GrowableSortedArrayMap<K, V, A: Allocator> =
    SortedArrayMap<K, V, GrowableArrayMemory<(K, V), A>>;

impl<K, V, A: Allocator> GrowableSortedArrayMap<K, V, A> {
    #[inline]
    pub fn new_growable_in(alloc: A) -> Self {
        Self::new_in(GrowableArrayMemory::new_in(alloc))
    }
}

pub type FixedSortedArrayMap<K, V, const N: usize> =
    SortedArrayMap<K, V, FixedArrayMemory<(K, V), N>>;

impl<K, V, const N: usize> FixedSortedArrayMap<K, V, N> {
    #[inline]
    pub fn new_fixed() -> Self {
        Self::new_in(FixedArrayMemory::default())
    }
}

impl<K: Clone, V: Clone, const N: usize> Clone for FixedSortedArrayMap<K, V, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[expect(type_alias_bounds)]
pub type SpillableSortedArrayMap<K, V, const N: usize, A: Allocator> =
    SortedArrayMap<K, V, SpillableArrayMemory<(K, V), N, A>>;

impl<K, V, const N: usize, A: Allocator> SpillableSortedArrayMap<K, V, N, A> {
    #[inline]
    pub fn new_spillable_in(alloc: A) -> Self {
        Self::new_in(SpillableArrayMemory::new_in(alloc))
    }
}

// ----
// sorted vector set

pub struct SortedArraySet<T, M: ArrayMemory<T>>(pub Array<T, M>);

impl<T, M: ArrayMemory<T>> SortedArraySet<T, M> {
    #[inline]
    pub fn new_in(mem: M) -> Self {
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
    // builder-lite with

    pub fn try_with_iter<I: Iterator<Item = T>>(mut self, iter: I) -> Result<Self, AllocError> {
        self.try_extend_from_iter(iter)?;
        Ok(self)
    }

    // ----
    // vector deviations

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

impl<T, A: Allocator> GrowableSortedArraySet<T, A> {
    #[inline]
    pub fn new_growable_in(alloc: A) -> Self {
        Self::new_in(GrowableArrayMemory::new_in(alloc))
    }
}

pub type FixedSortedArraySet<T, const N: usize> = SortedArraySet<T, FixedArrayMemory<T, N>>;

impl<T, const N: usize> FixedSortedArraySet<T, N> {
    #[inline]
    pub fn new_fixed() -> Self {
        Self::new_in(FixedArrayMemory::default())
    }
}

impl<T: Clone, const N: usize> Clone for FixedSortedArraySet<T, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[expect(type_alias_bounds)]
pub type SpillableSortedArraySet<T, const N: usize, A: Allocator> =
    SortedArraySet<T, SpillableArrayMemory<T, N, A>>;

impl<T, const N: usize, A: Allocator> SpillableSortedArraySet<T, N, A> {
    #[inline]
    pub fn new_spillable_in(alloc: A) -> Self {
        Self::new_in(SpillableArrayMemory::new_in(alloc))
    }
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

        // ----
        // builder-lite with

        #[inline]
        pub fn with_iter<I: Iterator<Item = (K, V)>>(self, iter: I) -> Self {
            this_is_fine(self.try_with_iter(iter))
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

        // ----
        // builder-lite with

        #[inline]
        pub fn with_iter<I: Iterator<Item = T>>(self, iter: I) -> Self {
            this_is_fine(self.try_with_iter(iter))
        }
    }
}

// ----

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_insert() {
        let mut this =
            SortedArrayMap::<u32, (), _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        this.insert(42, ());
        this.insert(64, ());
        this.insert(64, ());
        this.insert(27, ());
        assert_eq!(this.0.as_slice(), &[(27, ()), (42, ()), (64, ())]);
    }

    #[test]
    fn test_map_get() {
        let mut this = SortedArrayMap::<u32, &'static str, _>::new_in(GrowableArrayMemory::new_in(
            alloc::Global,
        ));
        this.insert(0, "zero");
        this.insert(8, "hachi");
        this.insert(16, "juuroku");
        assert_eq!(this.get(&8), Some(&"hachi"));
    }

    #[test]
    fn test_set_insert() {
        let mut this = SortedArraySet::<u32, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        this.insert(64);
        this.insert(42);
        this.insert(27);
        this.insert(64);
        assert_eq!(this.0.as_slice(), &[27, 42, 64]);
    }

    #[test]
    fn test_set_contains() {
        let mut this =
            SortedArraySet::<&'static str, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        this.insert("zero");
        this.insert("hachi");
        this.insert("juuroku");
        assert!(this.contains(&"zero"));
        assert!(!this.contains(&"ichi"));
    }
}
