use core::borrow::Borrow;
use core::cmp::Ordering;
use core::{fmt, mem};

use alloc::{AllocError, Allocator};

use crate::array::{
    Array, ArrayMemory, FixedArrayMemory, InsertError, ResizableArrayMemory, SpillableArrayMemory,
};

// NOTE: this can be used instead of hashmap.
//   good for small number of pairs.
//   better then the hashmap for <= 128 items for sure (see benchmark).
//   - `insert` is o(n);
//   - `find` performs binary search.

// NOTE: i am too lazy to duplicate majority of Array's methods in impls.
//   feel free to use any non-mutating method of the underlying array(.0);
//   but mutating it is illegal.

// MAYBE: warn on drop when len > threshold or something?
// #[cfg(debug_assertions)]
// const WARN_LEN_GREATER_THEN: usize = 64;

/// you may wish to implement SortedArrayCompare if comparison logic that your SortedArray* type
/// needs is incompatible with Ord that you may need for other purposes..
pub trait SortedArrayCompare<K: ?Sized = Self> {
    fn compare(&self, key: &K) -> Ordering;
}

impl<K, Q> SortedArrayCompare<Q> for K
where
    K: ?Sized + Borrow<Q>,
    Q: ?Sized + Ord,
{
    #[inline(always)]
    fn compare(&self, key: &Q) -> Ordering {
        Ord::cmp(self.borrow(), key)
    }
}

// ----
// sorted array map

#[inline(always)]
pub fn map_is_sorted<K, V>(entries: &[(K, V)]) -> bool
where
    K: SortedArrayCompare,
{
    entries.is_sorted_by(|(a, _), (b, _)| a.compare(b) != Ordering::Greater)
}

pub struct SortedArrayMap<K, V, M: ArrayMemory<(K, V)>>(pub Array<(K, V), M>);

impl<K, V, M: ArrayMemory<(K, V)>> SortedArrayMap<K, V, M> {
    #[inline]
    pub fn new_in<I: Into<M>>(mem: I) -> Self {
        Self(Array::new_in(mem))
    }
}

macro_rules! impl_map {
    ($($header:tt)*) => {
        $($header)* {
            /// returns ok if key is found; otherwise err will contain index where it could be inserted.
            #[inline]
            pub fn find_index<Q>(&self, key: &Q) -> Result<usize, usize>
            where
                K: SortedArrayCompare<Q>,
                Q: ?Sized,
            {
                self.0
                    .binary_search_by(|(k, _)| SortedArrayCompare::compare(k, key.borrow()))
            }

            #[inline]
            pub fn contains<Q>(&self, key: &Q) -> bool
            where
                K: SortedArrayCompare<Q>,
                Q: ?Sized,
            {
                self.find_index(key).is_ok()
            }

            #[inline]
            pub fn find<Q>(&self, key: &Q) -> Option<&V>
            where
                K: SortedArrayCompare<Q>,
                Q: ?Sized,
            {
                match self.find_index(key) {
                    Ok(i) => Some(unsafe { &self.0.get_unchecked(i).1 }),
                    Err(_) => None,
                }
            }

            #[inline]
            pub fn find_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
            where
                K: SortedArrayCompare<Q>,
                Q: ?Sized,
            {
                match self.find_index(key) {
                    Ok(i) => Some(unsafe { &mut self.0.get_unchecked_mut(i).1 }),
                    Err(_) => None,
                }
            }

            #[inline]
            pub fn remove<Q>(&mut self, key: &Q) -> Option<(K, V)>
            where
                K: SortedArrayCompare<Q>,
                Q: ?Sized,
            {
                match self.find_index(key) {
                    Ok(i) => self.0.remove_ordered(i),
                    Err(_) => None,
                }
            }
        }
    };
}

pub(crate) use impl_map;

impl_map!(impl<K, V, M: ArrayMemory<(K, V)>> SortedArrayMap<K, V, M>);

impl<K: SortedArrayCompare, V, M: ArrayMemory<(K, V)>> SortedArrayMap<K, V, M> {
    pub fn try_insert(
        &mut self,
        key: K,
        value: V,
    ) -> Result<(&mut V, Option<V>), InsertError<(K, V)>> {
        match self.find_index(&key) {
            Ok(i) => {
                let v = unsafe { &mut self.0.get_unchecked_mut(i).1 };
                let prev = mem::replace(v, value);
                Ok((v, Some(prev)))
            }
            Err(i) => {
                self.0.try_insert(i, (key, value))?;
                let v = unsafe { &mut self.0.get_unchecked_mut(i).1 };
                Ok((v, None))
            }
        }
    }

    pub fn try_extend_from_iter<I: Iterator<Item = (K, V)>>(
        &mut self,
        iter: I,
    ) -> Result<(), AllocError> {
        self.0.try_extend_from_iter(iter)?;
        self.0.sort_unstable_by(|(a, _), (b, _)| a.compare(b));
        Ok(())
    }

    pub fn find_or_try_insert_with<Q, F>(
        &mut self,
        key: Q,
        make_value: F,
    ) -> Result<&mut V, InsertError<(K, V)>>
    where
        K: SortedArrayCompare<Q>,
        Q: Into<K>,
        F: FnOnce() -> V,
    {
        let i = match self.find_index(key.borrow()) {
            Ok(i) => i,
            Err(i) => {
                self.0.try_insert(i, (key.into(), make_value()))?;
                i
            }
        };
        Ok(unsafe { &mut self.0.get_unchecked_mut(i).1 })
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
    ([$($vars:tt)*] $lhs:ty, $rhs:ty) => {
        impl<K1, V1, K2, V2, $($vars)*> PartialEq<$rhs> for $lhs
        where
            (K1, V1): PartialEq<(K2, V2)>,
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
pub type ResizableSortedArrayMap<K, V, A: Allocator> =
    SortedArrayMap<K, V, ResizableArrayMemory<(K, V), A>>;

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

#[inline(always)]
pub fn set_is_sorted<T>(entries: &[T]) -> bool
where
    T: SortedArrayCompare,
{
    entries.is_sorted_by(|a, b| a.compare(b) != Ordering::Greater)
}

pub struct SortedArraySet<T, M: ArrayMemory<T>>(pub Array<T, M>);

impl<T, M: ArrayMemory<T>> SortedArraySet<T, M> {
    #[inline]
    pub fn new_in<I: Into<M>>(mem: I) -> Self {
        Self(Array::new_in(mem))
    }
}

macro_rules! impl_set {
    ($($header:tt)*) => {
        $($header)* {
            /// returns ok if key is found; otherwise err will contain index where it could be inserted.
            #[inline]
            pub fn find_index<Q>(&self, value: &Q) -> Result<usize, usize>
            where
                T: SortedArrayCompare<Q>,
                Q: ?Sized,
            {
                self.0
                    .binary_search_by(|v| SortedArrayCompare::compare(v, value.borrow()))
            }

            #[inline]
            pub fn contains<Q>(&self, value: &Q) -> bool
            where
                T: SortedArrayCompare<Q>,
                Q: ?Sized,
            {
                self.find_index(value).is_ok()
            }

            #[inline]
            pub fn remove<Q>(&mut self, value: &Q) -> Option<T>
            where
                T: SortedArrayCompare<Q>,
                Q: ?Sized,
            {
                match self.find_index(value) {
                    Ok(i) => self.0.remove_ordered(i),
                    Err(_) => None,
                }
            }
        }
    };
}

pub(crate) use impl_set;

impl_set!(impl<T: SortedArrayCompare, M: ArrayMemory<T>> SortedArraySet<T, M>);

impl<T: SortedArrayCompare, M: ArrayMemory<T>> SortedArraySet<T, M> {
    /// returns true if the set did not have this value.
    pub fn try_insert(&mut self, value: T) -> Result<bool, InsertError<T>> {
        match self.find_index(&value) {
            Ok(_) => Ok(false),
            Err(i) => {
                self.0.try_insert(i, value)?;
                Ok(true)
            }
        }
    }

    pub fn try_extend_from_iter<I: Iterator<Item = T>>(
        &mut self,
        iter: I,
    ) -> Result<(), AllocError> {
        self.0.try_extend_from_iter(iter)?;
        self.0.sort_unstable_by(|a, b| a.compare(b));
        Ok(())
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
pub type ResizableSortedArraySet<T, A: Allocator> = SortedArraySet<T, ResizableArrayMemory<T, A>>;

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
    ([$($vars:tt)*] $lhs:ty, $rhs:ty) => {
        impl<T1, T2, $($vars)*> PartialEq<$rhs> for $lhs
        where
            T1: PartialEq<T2>,
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
    use alloc::this_is_fine;

    use super::*;

    impl<K: SortedArrayCompare, V, M: ArrayMemory<(K, V)>> SortedArrayMap<K, V, M> {
        #[track_caller]
        #[inline]
        pub fn insert(&mut self, key: K, value: V) -> (&mut V, Option<V>) {
            match self.try_insert(key, value) {
                Ok(ok) => ok,
                Err(err) => err.panic(),
            }
        }

        #[track_caller]
        #[inline]
        pub fn extend_from_iter<I: Iterator<Item = (K, V)>>(&mut self, iter: I) {
            this_is_fine(self.try_extend_from_iter(iter))
        }

        #[track_caller]
        #[inline]
        pub fn find_or_insert_with<Q, F>(&mut self, key: Q, make_value: F) -> &mut V
        where
            K: SortedArrayCompare<Q>,
            Q: Into<K>,
            F: FnOnce() -> V,
        {
            match self.find_or_try_insert_with(key, make_value) {
                Ok(ok) => ok,
                Err(err) => err.panic(),
            }
        }
    }

    // :TryCloneIn
    impl<K: Clone, V: Clone, A: Allocator + Clone> Clone for ResizableSortedArrayMap<K, V, A> {
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
        /// returns true if the set did not have this value.
        #[track_caller]
        #[inline]
        pub fn insert(&mut self, value: T) -> bool {
            match self.try_insert(value) {
                Ok(ok) => ok,
                Err(err) => err.panic(),
            }
        }

        #[track_caller]
        #[inline]
        pub fn extend_from_iter<I: Iterator<Item = T>>(&mut self, iter: I) {
            this_is_fine(self.try_extend_from_iter(iter))
        }
    }

    // :TryCloneIn
    impl<T: Clone, A: Allocator + Clone> Clone for ResizableSortedArraySet<T, A> {
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
    use crate::string::FixedString;

    use super::*;

    #[test]
    fn test_map_insert() {
        let mut this = ResizableSortedArrayMap::<u32, u32, _>::new_in(alloc::Global);
        this.insert(42, 0);
        this.insert(64, 1);
        core::assert_matches!(this.insert(64, 0), (.., Some(1)));
        this.insert(27, 0);
        assert_eq!(this.0.as_slice(), &[(27, 0), (42, 0), (64, 0)]);
    }

    #[test]
    fn test_map_get() {
        let mut this = ResizableSortedArrayMap::<u32, &'static str, _>::new_in(alloc::Global);
        this.insert(0, "zero");
        this.insert(8, "hachi");
        this.insert(16, "juuroku");
        assert_eq!(this.find(&8), Some(&"hachi"));
    }

    #[test]
    fn test_map_remove() {
        let mut this = ResizableSortedArrayMap::<u32, (), _>::new_in(alloc::Global);
        this.insert(42, ());
        this.insert(64, ());
        this.insert(27, ());
        assert_eq!(this.0.as_slice(), &[(27, ()), (42, ()), (64, ())]);
        this.remove(&27);
        assert_eq!(this.0.as_slice(), &[(42, ()), (64, ())]);
    }

    #[test]
    fn test_set_insert() {
        let mut this = ResizableSortedArraySet::<u32, _>::new_in(alloc::Global);
        this.insert(64);
        this.insert(42);
        this.insert(27);
        this.insert(64);
        assert_eq!(this.0.as_slice(), &[27, 42, 64]);
    }

    #[test]
    fn test_set_contains() {
        let mut this = ResizableSortedArraySet::<&'static str, _>::new_in(alloc::Global);
        this.insert("zero");
        this.insert("hachi");
        this.insert("juuroku");
        assert!(this.contains(&"zero"));
        assert!(!this.contains(&"ichi"));
    }

    #[test]
    fn test_set_remove() {
        let mut this = ResizableSortedArraySet::<u32, _>::new_in(alloc::Global);
        this.insert(42);
        this.insert(27);
        this.insert(64);
        assert_eq!(this.0.as_slice(), &[27, 42, 64]);
        this.remove(&27);
        assert_eq!(this.0.as_slice(), &[42, 64]);
    }

    #[test]
    fn test_map_get_by_str_when_key_is_a_fixed_string() {
        let mut this = FixedSortedArrayMap::<FixedString<16>, _, 2>::default();
        this.insert(FixedString::from_str("zero"), 0);
        assert_eq!(this.find("zero"), Some(&0));
    }
}
