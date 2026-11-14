use core::borrow::Borrow;
use core::{fmt, mem};

use alloc::{AllocError, Allocator};

use crate::array::InsertError;
use crate::sortedarray::{self, SortedArrayCompare};
use crate::unmanagedarray::UnmanagedArray;

// ----
// unmanaged sorted array map

pub struct UnmanagedSortedArrayMap<K, V>(pub UnmanagedArray<(K, V)>);

sortedarray::impl_map!(impl<K, V> UnmanagedSortedArrayMap<K, V>);

impl<K: SortedArrayCompare, V> UnmanagedSortedArrayMap<K, V> {
    pub fn try_insert(
        &mut self,
        alloc: impl Allocator,
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
                self.0.try_insert(alloc, i, (key, value))?;
                let v = unsafe { &mut self.0.get_unchecked_mut(i).1 };
                Ok((v, None))
            }
        }
    }

    pub fn try_extend_from_iter<I: Iterator<Item = (K, V)>>(
        &mut self,
        alloc: impl Allocator,
        iter: I,
    ) -> Result<(), AllocError> {
        self.0.try_extend_from_iter(alloc, iter)?;
        self.0.sort_unstable_by(|(a, _), (b, _)| a.compare(b));
        Ok(())
    }

    pub fn find_or_try_insert_with<Q, F>(
        &mut self,
        alloc: impl Allocator,
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
                self.0.try_insert(alloc, i, (key.into(), make_value()))?;
                i
            }
        };
        Ok(unsafe { &mut self.0.get_unchecked_mut(i).1 })
    }
}

impl<K, V> Default for UnmanagedSortedArrayMap<K, V> {
    #[inline]
    fn default() -> Self {
        Self(UnmanagedArray::default())
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for UnmanagedSortedArrayMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0.as_slice(), f)
    }
}

// ----
// unmanaged sorted array set

pub struct UnmanagedSortedArraySet<T>(pub UnmanagedArray<T>);

sortedarray::impl_set!(impl<T> UnmanagedSortedArraySet<T>);

impl<T: SortedArrayCompare> UnmanagedSortedArraySet<T> {
    /// returns true if the set did not have this value.
    pub fn try_insert(&mut self, alloc: impl Allocator, value: T) -> Result<bool, InsertError<T>> {
        match self.find_index(&value) {
            Ok(_) => Ok(false),
            Err(i) => {
                self.0.try_insert(alloc, i, value)?;
                Ok(true)
            }
        }
    }

    pub fn try_extend_from_iter<I: Iterator<Item = T>>(
        &mut self,
        alloc: impl Allocator,
        iter: I,
    ) -> Result<(), AllocError> {
        self.0.try_extend_from_iter(alloc, iter)?;
        self.0.sort_unstable_by(|a, b| a.compare(b));
        Ok(())
    }
}

impl<T> Default for UnmanagedSortedArraySet<T> {
    #[inline]
    fn default() -> Self {
        Self(UnmanagedArray::default())
    }
}

impl<T: fmt::Debug> fmt::Debug for UnmanagedSortedArraySet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0.as_slice(), f)
    }
}

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::this_is_fine;

    use super::*;

    impl<K: SortedArrayCompare, V> UnmanagedSortedArrayMap<K, V> {
        #[track_caller]
        #[inline]
        pub fn insert(&mut self, alloc: impl Allocator, key: K, value: V) -> (&mut V, Option<V>) {
            match self.try_insert(alloc, key, value) {
                Ok(ok) => ok,
                Err(err) => err.panic(),
            }
        }

        #[track_caller]
        #[inline]
        pub fn extend_from_iter<I: Iterator<Item = (K, V)>>(
            &mut self,
            alloc: impl Allocator,
            iter: I,
        ) {
            this_is_fine(self.try_extend_from_iter(alloc, iter))
        }

        #[track_caller]
        #[inline]
        pub fn find_or_insert_with<Q, F>(
            &mut self,
            alloc: impl Allocator,
            key: Q,
            make_value: F,
        ) -> &mut V
        where
            K: SortedArrayCompare<Q>,
            Q: Into<K>,
            F: FnOnce() -> V,
        {
            match self.find_or_try_insert_with(alloc, key, make_value) {
                Ok(ok) => ok,
                Err(err) => err.panic(),
            }
        }
    }

    impl<T: SortedArrayCompare> UnmanagedSortedArraySet<T> {
        /// returns true if the set did not have this value.
        #[track_caller]
        #[inline]
        pub fn insert(&mut self, alloc: impl Allocator, value: T) -> bool {
            match self.try_insert(alloc, value) {
                Ok(ok) => ok,
                Err(err) => err.panic(),
            }
        }

        #[track_caller]
        #[inline]
        pub fn extend_from_iter<I: Iterator<Item = T>>(&mut self, alloc: impl Allocator, iter: I) {
            this_is_fine(self.try_extend_from_iter(alloc, iter))
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::Global;

    use super::*;

    #[test]
    fn test_unmanaged_sorted_array_map() {
        let mut this = UnmanagedSortedArrayMap::default();

        this.try_insert(Global, 42, 0).unwrap();
        this.try_insert(Global, 64, 0).unwrap();
        this.try_insert(Global, 27, 0).unwrap();
        this.try_insert(Global, 27, 1).unwrap();
        assert_eq!(this.0.as_slice(), &[(27, 1), (42, 0), (64, 0)]);

        assert!(this.contains(&42));

        assert_eq!(this.find(&27), Some(&1));

        this.remove(&27);
        assert_eq!(this.0.as_slice(), &[(42, 0), (64, 0)]);
    }

    #[test]
    fn test_unmanaged_sorted_array_set() {
        let mut this = UnmanagedSortedArraySet::default();

        this.try_insert(Global, 42).unwrap();
        this.try_insert(Global, 64).unwrap();
        this.try_insert(Global, 27).unwrap();
        this.try_insert(Global, 27).unwrap();
        assert_eq!(this.0.as_slice(), &[27, 42, 64]);

        assert!(this.contains(&42));

        this.remove(&27);
        assert_eq!(this.0.as_slice(), &[42, 64]);
    }
}
