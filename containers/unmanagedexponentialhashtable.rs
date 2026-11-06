use core::alloc::Layout;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::mem;
use core::{ptr, slice};

use alloc::{AllocError, Allocator};

use crate::array::InsertError;
use crate::unmanagedexponentialarray::{chunk_cap, item_loc, max_chunks};

// NOTE: tag is stored within the hash, in higher bits.
//   that is okay because they pretty much never used.
//   how come?
//   that is because when we reduce hash to an index we do
//   hash & (cap - 1) and that uses log2 bits of hash ..
//     - cap being power of two
//     - in case of cap 1024 only 10 bits will be used.
//
//  this is what swiss table does, see https://abseil.io/about/design/swisstables
//  do i get this right? i sure hope so.
//
//  but the table is not swiss, it's open addressing.
//
// TODO: at ~500k items only 19-20 bits of hash will be used.
//   but i don't think that means that it would be worth using 32 bit hashes instead of 64 bit ones;
//   hashing algos can enjoy having more bits, right?

const DEFAULT_LOAD_FACTOR: usize = 70;
const DEFAULT_SHIFT: usize = 4;
const DEFAULT_MAX_CHUNKS: usize = max_chunks(4);

const TAG_SHIFT: u64 = 62;

const TAG_PENDING_REDISTRIBUTION: u64 = 0x1 << TAG_SHIFT; // 01
const TAG_REMOVED: u64 = 0x2 << TAG_SHIFT; // 10
const TAG_VACANT: u64 = 0x3 << TAG_SHIFT; // 11

const TAG_MASK: u64 = 0x3 << TAG_SHIFT;
const HASH_MASK: u64 = !TAG_MASK;

struct Entry<T> {
    hash: u64,
    // TODO: MaybeUninit<T>
    value: T,
}

pub struct UnmanagedExponentialHashTable<
    T,
    const LOAD_FACTOR: usize = DEFAULT_LOAD_FACTOR,
    const SHIFT: usize = DEFAULT_SHIFT,
    const MAX_CHUNKS: usize = DEFAULT_MAX_CHUNKS,
> {
    chunks: [*mut Entry<T>; MAX_CHUNKS],
    cap: usize,
    len: usize,
    tombstones: usize,
}

impl<T, const LOAD_FACTOR: usize, const SHIFT: usize, const MAX_CHUNKS: usize>
    UnmanagedExponentialHashTable<T, LOAD_FACTOR, SHIFT, MAX_CHUNKS>
{
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

        let used_load = (len + self.tombstones + additional) * 100;
        if used_load <= max_load {
            return Ok(());
        }

        let live_load = (len + additional) * 100;
        // if live_load * 2 <= max_load {
        //     // MAYBE: redistribute here? but don't need to grow?
        // }

        // NOTE: grow

        let min_cap = live_load.div_ceil(LOAD_FACTOR);
        let (_, _, last_to_allocate_chunk_idx) = item_loc(min_cap - 1, SHIFT);
        if last_to_allocate_chunk_idx >= MAX_CHUNKS {
            return Err(AllocError);
        }

        let (_, _, first_unallocated_chunk_idx) = item_loc(old_cap, SHIFT);
        debug_assert!(
            self.chunks[..first_unallocated_chunk_idx]
                .iter()
                .all(|it| !it.is_null())
        );

        for chunk_idx in first_unallocated_chunk_idx..=last_to_allocate_chunk_idx {
            debug_assert!(self.chunks[chunk_idx].is_null());

            let chunk_cap = chunk_cap(chunk_idx, SHIFT);
            let Ok(chunk_layout) = Layout::array::<Entry<T>>(chunk_cap) else {
                return Err(AllocError);
            };
            let chunk_ptr = alloc.allocate(chunk_layout)?.as_ptr() as *mut Entry<T>;
            let chunk = unsafe { slice::from_raw_parts_mut(chunk_ptr, chunk_cap) };
            for entry in chunk {
                entry.hash = TAG_VACANT;
            }
            self.chunks[chunk_idx] = chunk_ptr;
            self.cap += chunk_cap;
        }

        // NOTE: redistribute

        // :RedistributionPass1
        for chunk_idx in 0..first_unallocated_chunk_idx {
            let chunk_ptr = self.chunks[chunk_idx];
            let chunk_cap = chunk_cap(chunk_idx, SHIFT);
            let chunk = unsafe { slice::from_raw_parts_mut(chunk_ptr, chunk_cap) };
            for entry in chunk {
                entry.hash |= TAG_PENDING_REDISTRIBUTION;
            }
        }

        let idx_mask = self.cap() as u64 - 1;
        for chunk_idx in 0..first_unallocated_chunk_idx {
            let src_chunk_ptr = self.chunks[chunk_idx];
            let src_chunk_cap = chunk_cap(chunk_idx, SHIFT);
            let src_chunk = unsafe { slice::from_raw_parts_mut(src_chunk_ptr, src_chunk_cap) };
            for src_entry in src_chunk {
                while (src_entry.hash & TAG_MASK) == TAG_PENDING_REDISTRIBUTION {
                    let hash = src_entry.hash & HASH_MASK;

                    let dst_entry = {
                        let mut idx = hash & idx_mask;
                        let mut probe = 1;
                        loop {
                            let (item_idx, _, chunk_idx) = item_loc(idx as usize, SHIFT);
                            let entry_ptr = unsafe { self.chunks[chunk_idx].add(item_idx) };
                            let entry = unsafe { &mut *entry_ptr };

                            if entry.hash > HASH_MASK {
                                break entry;
                            }

                            idx = (idx + probe) & idx_mask;
                            probe += 1;
                        }
                    };

                    unsafe {
                        ptr::swap(src_entry, dst_entry);
                    }
                    dst_entry.hash = hash;
                }
            }
        }

        self.tombstones = 0;

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
            // TODO: can you not iterate like this? to avoid calling item_loc?
            let (item_idx, _, chunk_idx) = item_loc(idx as usize, SHIFT);
            let entry_ptr = unsafe { self.chunks[chunk_idx].add(item_idx) };
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

    fn find_occupied_entry_ptr(&self, hash: u64, eq: impl Fn(&T) -> bool) -> Option<*mut Entry<T>> {
        // NOTE: at 100 it'll infinite loop.
        debug_assert!(LOAD_FACTOR < 100);

        if self.len() == 0 {
            return None;
        }

        let hash = hash & HASH_MASK;
        let idx_mask = self.cap() as u64 - 1;
        let mut idx = hash & idx_mask;
        let mut probe = 1;
        loop {
            // TODO: can you not iterate like this? to avoid calling item_loc?
            let (item_idx, _, chunk_idx) = item_loc(idx as usize, SHIFT);
            let entry_ptr = unsafe { self.chunks[chunk_idx].add(item_idx) };
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

    // NOTE: `find` is more honest then `get`.

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

impl<T, const LOAD_FACTOR: usize, const SHIFT: usize, const MAX_CHUNKS: usize> Default
    for UnmanagedExponentialHashTable<T, LOAD_FACTOR, SHIFT, MAX_CHUNKS>
{
    fn default() -> Self {
        Self {
            chunks: [ptr::null_mut(); MAX_CHUNKS],
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

pub struct UnmanagedExponentialHashMap<
    K,
    V,
    H,
    const LOAD_FACTOR: usize = DEFAULT_LOAD_FACTOR,
    const SHIFT: usize = DEFAULT_SHIFT,
    const MAX_CHUNKS: usize = DEFAULT_MAX_CHUNKS,
> {
    hash_builder: H,
    hash_table: UnmanagedExponentialHashTable<(K, V), LOAD_FACTOR, SHIFT, MAX_CHUNKS>,
}

impl<K, V, H, const LOAD_FACTOR: usize, const SHIFT: usize, const MAX_CHUNKS: usize>
    UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR, SHIFT, MAX_CHUNKS>
{
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

impl<K, V, H, const LOAD_FACTOR: usize, const SHIFT: usize, const MAX_CHUNKS: usize>
    UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR, SHIFT, MAX_CHUNKS>
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

impl<K, V, H, const LOAD_FACTOR: usize, const SHIFT: usize, const MAX_CHUNKS: usize> Default
    for UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR, SHIFT, MAX_CHUNKS>
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

    impl<T, const LOAD_FACTOR: usize, const SHIFT: usize, const MAX_CHUNKS: usize>
        UnmanagedExponentialHashTable<T, LOAD_FACTOR, SHIFT, MAX_CHUNKS>
    {
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

    impl<K, V, H, const LOAD_FACTOR: usize, const SHIFT: usize, const MAX_CHUNKS: usize>
        UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR, SHIFT, MAX_CHUNKS>
    {
        /// reserve cap for at least `additional` more items; may reserve more.
        pub fn reserve(&mut self, alloc: impl Allocator, additional: usize) {
            this_is_fine(self.try_reserve(alloc, additional))
        }
    }

    impl<K, V, H, const LOAD_FACTOR: usize, const SHIFT: usize, const MAX_CHUNKS: usize>
        UnmanagedExponentialHashMap<K, V, H, LOAD_FACTOR, SHIFT, MAX_CHUNKS>
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
