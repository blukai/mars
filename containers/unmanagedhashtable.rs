use core::alloc::Layout;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::ptr::{self, NonNull};
use core::{mem, slice};

use alloc::{AllocError, Allocator};

use crate::array::InsertError;

const DEFAULT_LOAD_FACTOR: usize = 70;
const MIN_CAP: usize = 16;
const _: () = assert!(MIN_CAP.is_power_of_two());

const TAG_SHIFT: u64 = 62;

const TAG_REMOVED: u64 = 0x2 << TAG_SHIFT; // 10
const TAG_VACANT: u64 = 0x3 << TAG_SHIFT; // 11

const TAG_MASK: u64 = 0x3 << TAG_SHIFT;
const HASH_MASK: u64 = !TAG_MASK;

struct Entry<T> {
    hash: u64,
    // TODO: MaybeUninit<T>
    value: T,
}

pub struct UnmanagedExponentialHashTable<T, const LOAD_FACTOR: usize = DEFAULT_LOAD_FACTOR> {
    ptr: *mut Entry<T>,
    cap: usize,
    len: usize,
    tombstones: usize,
}

impl<T, const LOAD_FACTOR: usize> UnmanagedExponentialHashTable<T, LOAD_FACTOR> {
    #[inline]
    pub fn cap(&self) -> usize {
        self.cap
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// reserve cap for at least `additional` more items; may reserve more.
    pub fn try_reserve(
        &mut self,
        alloc: impl Allocator,
        additional: usize,
    ) -> Result<(), AllocError> {
        let old_cap = self.cap();
        let len = self.len();

        let max_load = old_cap * LOAD_FACTOR;

        let occupied_and_removed_projected_load = (len + self.tombstones + additional) * 100;
        if occupied_and_removed_projected_load <= max_load {
            return Ok(());
        }

        let occupied_projected_load = (len + additional) * 100;
        // if occupied_projected_load * 2 <= max_load {
        //     // MAYBE: redistribute here? but don't need to grow?
        // }

        let new_cap = occupied_projected_load
            .div_ceil(LOAD_FACTOR)
            .next_power_of_two()
            .max(MIN_CAP);

        let new_layout = Layout::array::<Entry<T>>(new_cap).map_err(|_| AllocError)?;
        let new_ptr = alloc.allocate(new_layout)?.as_ptr() as *mut Entry<T>;

        let news = unsafe { slice::from_raw_parts_mut(new_ptr, new_cap) };
        for new in news {
            new.hash = TAG_VACANT;
        }

        let old_ptr = self.ptr;
        self.ptr = new_ptr;
        self.cap = new_cap;
        self.tombstones = 0;

        if let Some(old_ptrjke) = NonNull::new(old_ptr as *mut u8) {
            if len > 0 {
                let olds = unsafe { slice::from_raw_parts_mut(old_ptr, old_cap) };
                let idx_mask = new_cap as u64 - 1;
                for old in olds {
                    debug_assert!(TAG_REMOVED < TAG_VACANT);
                    if old.hash >= TAG_REMOVED {
                        continue;
                    }

                    let mut idx = old.hash & idx_mask;
                    let mut probe = 1;
                    loop {
                        let entry = unsafe { &mut *new_ptr.add(idx as usize) };
                        debug_assert!(TAG_REMOVED < TAG_VACANT);
                        if entry.hash >= TAG_VACANT {
                            entry.hash = old.hash;
                            unsafe {
                                ptr::copy_nonoverlapping(&old.value, &mut entry.value, 1);
                            }
                            break;
                        }
                        idx = (idx + probe) & idx_mask;
                        probe += 1;
                    }
                }
            }

            unsafe {
                let old_layout = Layout::array::<Entry<T>>(old_cap).expect("bad old layout, why");
                alloc.deallocate(old_ptrjke, old_layout);
            }
        }

        Ok(())
    }

    /// returns mutable reference to newly inserted value, maybe old value; or an error.
    pub fn try_insert(
        &mut self,
        alloc: impl Allocator,
        hash: u64,
        eq: impl Fn(&T, &T) -> bool,
        value: T,
    ) -> Result<(&mut T, Option<T>), InsertError<T>> {
        if let Err(err) = self.try_reserve(alloc, 1) {
            return Err(InsertError::new_oom(err, value));
        };

        let hash = hash & HASH_MASK;
        let idx_mask = self.cap() as u64 - 1;
        let mut idx = hash & idx_mask;
        let mut probe = 1;
        let mut maybe_first_tombstone = ptr::null_mut::<Entry<T>>();
        loop {
            let entry_ptr = unsafe { self.ptr.add(idx as usize) };
            let entry = unsafe { &mut *entry_ptr };

            if entry.hash == hash {
                if eq(&entry.value, &value) {
                    let old_value = mem::replace(&mut entry.value, value);
                    return Ok((&mut entry.value, Some(old_value)));
                }

                // MAYBE: count collissions
            }

            if entry.hash >= TAG_REMOVED {
                if entry.hash >= TAG_VACANT {
                    // NOTE: at this point you know that the given value isn't present.
                    self.len += 1;
                    let dst = if maybe_first_tombstone.is_null() {
                        entry
                    } else {
                        self.tombstones -= 1;
                        unsafe { &mut *maybe_first_tombstone }
                    };
                    dst.hash = hash;
                    unsafe {
                        ptr::write(&mut dst.value, value);
                    }
                    return Ok((&mut dst.value, None));
                }

                if maybe_first_tombstone.is_null() {
                    maybe_first_tombstone = entry_ptr;
                }
            }

            idx = (idx + probe) & idx_mask;
            probe += 1;
        }
    }

    // NOTE: `find` is more honest then `get`.

    fn find_occupied_entry_ptr(&self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<*mut Entry<T>> {
        debug_assert!(LOAD_FACTOR < 100);

        if self.len() == 0 {
            return None;
        }

        let hash = hash & HASH_MASK;
        let idx_mask = self.cap() as u64 - 1;
        let mut idx = hash & idx_mask;
        let mut probe = 1;
        loop {
            let entry_ptr = unsafe { self.ptr.add(idx as usize) };
            let entry = unsafe { &*entry_ptr };
            if entry.hash == hash {
                if eq(&entry.value) {
                    return Some(entry_ptr);
                }
                // MAYBE: count collissions
            }
            if entry.hash >= TAG_VACANT {
                return None;
            }
            idx = (idx + probe) & idx_mask;
            probe += 1;
        }
    }

    #[inline]
    pub fn find(&self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<&T> {
        let entry_ptr = self.find_occupied_entry_ptr(hash, eq)?;
        let entry = unsafe { &*entry_ptr };
        Some(&entry.value)
    }

    #[inline]
    pub fn find_mut(&mut self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<&mut T> {
        let entry_ptr = self.find_occupied_entry_ptr(hash, eq)?;
        let entry = unsafe { &mut *entry_ptr };
        Some(&mut entry.value)
    }

    pub fn remove(&mut self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<T> {
        let entry_ptr = self.find_occupied_entry_ptr(hash, eq)?;
        let entry = unsafe { &mut *entry_ptr };
        let value = unsafe { ptr::read(&entry.value) };
        entry.hash = TAG_REMOVED;
        self.len -= 1;
        self.tombstones += 1;
        Some(value)
    }

    pub fn clear(&mut self) {
        todo!()
    }

    pub fn deinit(&mut self, alloc: impl Allocator) {
        todo!()
    }
}

impl<T, const LOAD_FACTOR: usize> Default for UnmanagedExponentialHashTable<T, LOAD_FACTOR> {
    fn default() -> Self {
        Self {
            ptr: ptr::null_mut(),
            cap: 0,
            len: 0,
            tombstones: 0,
        }
    }
}

#[test]
fn test_hashtable() {
    let value: u64 = 0xb00b;
    let hash = |value: &u64| *value; // identity, don't care.
    let mut this = UnmanagedExponentialHashTable::<u64>::default();
    this.try_insert(alloc::Global, hash(&value), |a, b| a == b, value)
        .unwrap();
    assert_eq!(this.find(hash(&value), |x| x == &value), Some(&value));
    let entry_ptr_after_first_insertion = this
        .find_occupied_entry_ptr(hash(&value), |x| x == &value)
        .unwrap();
    assert_eq!(this.remove(hash(&value), |x| x == &value), Some(value));
    assert_eq!(this.find(hash(&value), |x| x == &value), None);
    this.try_insert(alloc::Global, hash(&value), |a, b| a == b, value)
        .unwrap();
    let entry_ptr_after_second_insertion = this
        .find_occupied_entry_ptr(hash(&value), |x| x == &value)
        .unwrap();
    assert_eq!(
        entry_ptr_after_first_insertion,
        entry_ptr_after_second_insertion
    );
}

pub struct UnmanagedExponentialHashMap<K, V, H, const LOAD_FACTOR: usize = DEFAULT_LOAD_FACTOR> {
    hash_builder: H,
    hash_table: UnmanagedExponentialHashTable<(K, V), LOAD_FACTOR>,
}

impl<K, V, H, const LOAD_FACTOR: usize> UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR> {
    pub fn cap(&self) -> usize {
        self.hash_table.cap()
    }

    pub fn len(&self) -> usize {
        self.hash_table.len()
    }

    /// reserve cap for at least `additional` more items; may reserve more.
    pub fn try_reserve(
        &mut self,
        alloc: impl Allocator,
        additional: usize,
    ) -> Result<(), AllocError> {
        self.hash_table.try_reserve(alloc, additional)
    }

    pub fn clear(&mut self) {
        self.hash_table.clear();
    }

    pub fn deinit(&mut self, alloc: impl Allocator) {
        self.hash_table.deinit(alloc);
    }
}

impl<K, V, H, const LOAD_FACTOR: usize> UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR>
where
    K: Eq + Hash,
    H: BuildHasher,
{
    /// returns mutable reference to newly inserted value, maybe old value; or an error.
    pub fn try_insert(
        &mut self,
        alloc: impl Allocator,
        key: K,
        value: V,
    ) -> Result<(&mut V, Option<V>), InsertError<(K, V)>> {
        let hash = self.hash_builder.hash_one(&key);
        match self
            .hash_table
            .try_insert(alloc, hash, |(a, _), (b, _)| a == b, (key, value))
        {
            Ok(((_, value), Some((_, prev_value)))) => Ok((value, Some(prev_value))),
            Ok(((_, value), None)) => Ok((value, None)),
            Err(err) => Err(err),
        }
    }

    pub fn find<Q>(&self, key: &Q) -> Option<&V>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        let hash = self.hash_builder.hash_one(key);
        match self.hash_table.find(hash, |(k, _)| key.eq(k.borrow())) {
            Some((_, value)) => Some(value),
            None => None,
        }
    }

    pub fn find_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        let hash = self.hash_builder.hash_one(key);
        match self.hash_table.find_mut(hash, |(k, _)| key.eq(k.borrow())) {
            Some((_, value)) => Some(value),
            None => None,
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        let hash = self.hash_builder.hash_one(key);
        match self.hash_table.remove(hash, |(k, _)| key.eq(k.borrow())) {
            Some((_, value)) => Some(value),
            None => None,
        }
    }
}

impl<K, V, H, const LOAD_FACTOR: usize> Default
    for UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR>
where
    H: Default,
{
    fn default() -> Self {
        Self {
            hash_builder: H::default(),
            hash_table: UnmanagedExponentialHashTable::default(),
        }
    }
}

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::this_is_fine;

    use super::*;

    impl<T, const LOAD_FACTOR: usize> UnmanagedExponentialHashTable<T, LOAD_FACTOR> {
        pub fn reserve(&mut self, alloc: impl Allocator, additional: usize) {
            this_is_fine(self.try_reserve(alloc, additional))
        }

        pub fn insert(
            &mut self,
            alloc: impl Allocator,
            hash: u64,
            eq: impl Fn(&T, &T) -> bool,
            value: T,
        ) -> (&mut T, Option<T>) {
            match self.try_insert(alloc, hash, eq, value) {
                Ok(ret) => ret,
                Err(err) => err.panic(),
            }
        }
    }

    impl<K, V, H, const LOAD_FACTOR: usize> UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR> {
        /// reserve cap for at least `additional` more items; may reserve more.
        pub fn reserve(&mut self, alloc: impl Allocator, additional: usize) {
            this_is_fine(self.try_reserve(alloc, additional))
        }
    }

    impl<K, V, H, const LOAD_FACTOR: usize> UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR>
    where
        K: Eq + Hash,
        H: BuildHasher,
    {
        /// returns mutable reference to newly inserted value, maybe old value; or an error.
        pub fn insert(&mut self, alloc: impl Allocator, key: K, value: V) -> (&mut V, Option<V>) {
            match self.try_insert(alloc, key, value) {
                Ok(ret) => ret,
                Err(err) => err.panic(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // NOTE: this one is stolen from hashbrown.
    #[test]
    fn test_lots_of_insertions() {
        let start = std::time::Instant::now();

        let mut m = UnmanagedExponentialHashMap::<i32, i32, hash::fxhash::FxBuildHasher>::default();

        // Try this a few times to make sure we never screw up the hashmap's
        // internal state.
        for _ in 0..10 {
            assert!(m.len() == 0);

            for i in 1..1001 {
                assert!(m.insert(alloc::Global, i, i).1.is_none());

                for j in 1..=i {
                    let r = m.find(&j);
                    assert_eq!(r, Some(&j));
                }

                for j in i + 1..1001 {
                    let r = m.find(&j);
                    assert_eq!(r, None);
                }
            }

            for i in 1001..2001 {
                assert!(m.find(&i).is_none());
            }

            // remove forwards
            for i in 1..1001 {
                assert!(m.remove(&i).is_some());

                for j in 1..=i {
                    assert!(m.find(&j).is_none());
                }

                for j in i + 1..1001 {
                    assert!(m.find(&j).is_some());
                }
            }

            for i in 1..1001 {
                assert!(m.find(&i).is_none());
            }

            for i in 1..1001 {
                assert!(m.insert(alloc::Global, i, i).1.is_none());
            }

            // remove backwards
            for i in (1..1001).rev() {
                assert!(m.remove(&i).is_some());

                for j in i..1001 {
                    assert!(m.find(&j).is_none());
                }

                for j in 1..i {
                    assert!(m.find(&j).is_some());
                }
            }
        }

        dbg!("my", start.elapsed());
    }

    #[test]
    fn test_lots_of_insertions_hashbrown() {
        let start = std::time::Instant::now();

        let mut m = hashbrown::HashMap::<i32, i32, hash::fxhash::FxBuildHasher>::default();

        // Try this a few times to make sure we never screw up the hashmap's
        // internal state.
        for _ in 0..10 {
            assert!(m.is_empty());

            for i in 1..1001 {
                assert!(m.insert(i, i).is_none());

                for j in 1..=i {
                    let r = m.get(&j);
                    assert_eq!(r, Some(&j));
                }

                for j in i + 1..1001 {
                    let r = m.get(&j);
                    assert_eq!(r, None);
                }
            }

            for i in 1001..2001 {
                assert!(!m.contains_key(&i));
            }

            // remove forwards
            for i in 1..1001 {
                assert!(m.remove(&i).is_some());

                for j in 1..=i {
                    assert!(!m.contains_key(&j));
                }

                for j in i + 1..1001 {
                    assert!(m.contains_key(&j));
                }
            }

            for i in 1..1001 {
                assert!(!m.contains_key(&i));
            }

            for i in 1..1001 {
                assert!(m.insert(i, i).is_none());
            }

            // remove backwards
            for i in (1..1001).rev() {
                assert!(m.remove(&i).is_some());

                for j in i..1001 {
                    assert!(!m.contains_key(&j));
                }

                for j in 1..i {
                    assert!(m.contains_key(&j));
                }
            }
        }

        dbg!("hashbrown", start.elapsed());
    }

    #[test]
    fn test_lots_of_insertions_sortedarraymap() {
        let start = std::time::Instant::now();

        let mut m =
            crate::sortedarray::ResizableSortedArrayMap::<i32, i32, alloc::Global>::default();

        // Try this a few times to make sure we never screw up the hashmap's
        // internal state.
        for _ in 0..10 {
            assert!(m.0.is_empty());

            for i in 1..1001 {
                assert!(m.insert(i, i).is_none());

                for j in 1..=i {
                    let r = m.get(&j);
                    assert_eq!(r, Some(&j));
                }

                for j in i + 1..1001 {
                    let r = m.get(&j);
                    assert_eq!(r, None);
                }
            }

            for i in 1001..2001 {
                assert!(!m.contains(&i));
            }

            // remove forwards
            for i in 1..1001 {
                assert!(m.remove(&i).is_some());

                for j in 1..=i {
                    assert!(!m.contains(&j));
                }

                for j in i + 1..1001 {
                    assert!(m.contains(&j));
                }
            }

            for i in 1..1001 {
                assert!(!m.contains(&i));
            }

            for i in 1..1001 {
                assert!(m.insert(i, i).is_none());
            }

            // remove backwards
            for i in (1..1001).rev() {
                assert!(m.remove(&i).is_some());

                for j in i..1001 {
                    assert!(!m.contains(&j));
                }

                for j in 1..i {
                    assert!(m.contains(&j));
                }
            }
        }

        dbg!("sortedarraymap", start.elapsed());
    }
}
