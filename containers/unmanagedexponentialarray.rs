// NOTE: this is from andrew reece's bsc talk.
//   see
//     - https://azmr.uk/dyn/#exponential-arrayxar
//     - https://www.youtube.com/watch?v=i-h95QIGchY&t=3724
//
//   items are never moved once allocated.
//   items in this array are not stored linerarly, but in chunks.
//   chunks are exponentially sized.

// NOTE: can't do math with polymorphic params.
//   see https://github.com/rust-lang/rust/issues/76560
//   there's a niglty generic_const_exprs feature (maybe in 2036?)

use core::marker::PhantomData;
use core::ptr::{self, null_mut};
use core::{alloc::Layout, fmt, ops};

use alloc::{AllocError, Allocator};

use crate::array::PushError;
use crate::panic_bounds_check;

#[macro_export]
macro_rules! __max_chunks {
    ($shift:expr) => {{
        let shift: usize = $shift;

        debug_assert!(shift > 0);
        debug_assert!(shift <= usize::BITS as usize >> 1);

        1 << (usize::BITS.ilog2() - shift.ilog2())
    }};
}

pub use __max_chunks as max_chunks;

#[inline(always)]
pub const fn max_cap(shift: usize) -> usize {
    1 << (shift + max_chunks!(shift) - 1)
}

const fn msb64(n: u64) -> u32 {
    debug_assert!(n != 0);
    usize::BITS - 1 - n.leading_zeros()
}

#[inline(always)]
const fn item_loc(idx: usize, shift: usize) -> (usize, usize, usize) {
    // NOTE: see https://www.youtube.com/watch?v=i-h95QIGchY&t=3724 (with timecode).

    let mut item_idx = idx;
    let mut chunk_cap = 1 << shift;
    let mut chunk_idx = 0;

    let idx_shift = idx >> shift;
    if idx_shift > 0 {
        chunk_idx = msb64(idx_shift as u64) as usize;
        chunk_cap = 1 << (chunk_idx + shift);
        item_idx -= chunk_cap;
        chunk_idx += 1;
    }

    (item_idx, chunk_cap, chunk_idx)
}

#[inline(always)]
const fn chunk_cap(chunk_idx: usize, shift: usize) -> usize {
    1 << (chunk_idx.saturating_sub(1) + shift)
}

// NOTE: you probably want shift to be 4 or 8.
//   - with 4 you'll get 16 chunks and 524288 items
//   - with 8 - 8 chunks, 32768 items
pub struct UnmanagedExponentialArray<T, const SHIFT: usize, const MAX_CHUNKS: usize> {
    chunks: [*mut T; MAX_CHUNKS],
    len: usize,

    #[cfg(debug_assertions)]
    cap: usize,
}

impl<T, const SHIFT: usize, const MAX_CHUNKS: usize>
    UnmanagedExponentialArray<T, SHIFT, MAX_CHUNKS>
{
    pub fn cap(&self) -> usize {
        // NOTE: idk if this would actually inline it?
        #[inline(always)]
        fn not_null<T>(ptr: &*mut T) -> bool {
            !ptr.is_null()
        }
        let Some(i) = self.chunks.iter().rposition(not_null) else {
            return 0;
        };
        1 << (SHIFT + i)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn try_push(&mut self, alloc: impl Allocator, value: T) -> Result<(), PushError<T>> {
        let (item_idx, chunk_cap, chunk_idx) = item_loc(self.len(), SHIFT);

        if chunk_idx >= MAX_CHUNKS || item_idx >= chunk_cap {
            return Err(PushError::new_oom(AllocError, value));
        }

        if self.chunks[chunk_idx].is_null() {
            let Ok(layout) = Layout::array::<T>(chunk_cap) else {
                return Err(PushError::new_oom(AllocError, value));
            };
            let Ok(ptr) = alloc.allocate(layout) else {
                return Err(PushError::new_oom(AllocError, value));
            };
            self.chunks[chunk_idx] = ptr.as_ptr().cast();

            #[cfg(debug_assertions)]
            {
                self.cap += chunk_cap;
                assert_eq!(self.cap, self.cap());
            }
        }

        unsafe {
            self.chunks[chunk_idx].add(item_idx).write(value);
        }
        self.len += 1;

        Ok(())
    }

    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        let (item_idx, _, chunk_idx) = item_loc(index, SHIFT);
        unsafe { &*self.chunks.get_unchecked(chunk_idx).add(item_idx) }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len() {
            return None;
        }
        unsafe { Some(self.get_unchecked(index)) }
    }

    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        let (item_idx, _, chunk_idx) = item_loc(index, SHIFT);
        unsafe { &mut *self.chunks.get_unchecked_mut(chunk_idx).add(item_idx) }
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.len() {
            return None;
        }
        unsafe { Some(self.get_unchecked_mut(index)) }
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, T, SHIFT, MAX_CHUNKS> {
        Iter {
            arr: self,
            next_idx: 0,
            _marker: PhantomData,
        }
    }

    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, T, SHIFT, MAX_CHUNKS> {
        IterMut {
            arr: self,
            next_idx: 0,
            _marker: PhantomData,
        }
    }

    pub fn remove_unordered(&mut self, index: usize) -> Option<T> {
        let len = self.len();
        if index >= len {
            return None;
        }
        unsafe {
            let value_ptr = self.get_unchecked_mut(index) as *mut _;
            let value = ptr::read(value_ptr);
            ptr::copy(self.get_unchecked_mut(len - 1), value_ptr, 1);
            self.len -= 1;
            Some(value)
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len() == 0 {
            return None;
        }
        unsafe {
            self.len -= 1;
            Some(ptr::read(self.get_unchecked(self.len())))
        }
    }

    pub fn clear(&mut self) {
        let Some(last_item_idx) = self.len().checked_sub(1) else {
            return;
        };

        let (last_item_idx_within_chunk, _last_chunk_cap, last_chunk_idx) =
            item_loc(last_item_idx, SHIFT);

        for i in 0..last_chunk_idx {
            let chunk_cap = chunk_cap(i, SHIFT);
            unsafe {
                ptr::slice_from_raw_parts_mut(self.chunks[i], chunk_cap).drop_in_place();
            }
        }

        debug_assert!(last_item_idx_within_chunk > 0);
        unsafe {
            ptr::slice_from_raw_parts_mut(
                self.chunks[last_chunk_idx],
                last_item_idx_within_chunk + 1,
            )
            .drop_in_place();
        }
    }

    pub fn deinit(&mut self, alloc: impl Allocator) {
        self.clear();

        for (i, it) in self.chunks.iter_mut().enumerate() {
            if it.is_null() {
                break;
            }

            let chunk_cap = chunk_cap(i, SHIFT);
            unsafe {
                // NOTE: chunk with invalid layout could not have been allocated.
                let layout = Layout::array::<T>(chunk_cap).unwrap_unchecked();
                alloc.deallocate(ptr::NonNull::new_unchecked(*it as *mut u8), layout);
            }
            *it = null_mut();
        }

        debug_assert!(self.chunks.iter().all(|it| it.is_null()));
    }
}

impl<T, const SHIFT: usize, const MAX_CHUNKS: usize> Default
    for UnmanagedExponentialArray<T, SHIFT, MAX_CHUNKS>
{
    fn default() -> Self {
        Self {
            chunks: [null_mut(); MAX_CHUNKS],
            len: 0,

            #[cfg(debug_assertions)]
            cap: 0,
        }
    }
}

impl<T: fmt::Debug, const SHIFT: usize, const MAX_CHUNKS: usize> fmt::Debug
    for UnmanagedExponentialArray<T, SHIFT, MAX_CHUNKS>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut l = f.debug_list();
        for it in self.iter() {
            l.entry(it);
        }
        l.finish()
    }
}

impl<T, const SHIFT: usize, const MAX_CHUNKS: usize> ops::Index<usize>
    for UnmanagedExponentialArray<T, SHIFT, MAX_CHUNKS>
{
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        let Some(item) = self.get(index) else {
            panic_bounds_check(index, self.len())
        };
        item
    }
}

impl<T, const SHIFT: usize, const MAX_CHUNKS: usize> ops::IndexMut<usize>
    for UnmanagedExponentialArray<T, SHIFT, MAX_CHUNKS>
{
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let len = self.len();
        match self.get_mut(index) {
            Some(item) => item,
            None => panic_bounds_check(index, len),
        }
    }
}

pub struct Iter<'a, T: 'a, const SHIFT: usize, const MAX_CHUNKS: usize> {
    arr: *const UnmanagedExponentialArray<T, SHIFT, MAX_CHUNKS>,
    next_idx: usize,
    _marker: PhantomData<&'a ()>,
}

impl<'a, T, const SHIFT: usize, const CHUNKS: usize> Iterator for Iter<'a, T, SHIFT, CHUNKS> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let arr = unsafe { &*self.arr };
        let ret = arr.get(self.next_idx);
        self.next_idx += ret.is_some() as usize;
        ret
    }
}

pub struct IterMut<'a, T: 'a, const SHIFT: usize, const MAX_CHUNKS: usize> {
    arr: *mut UnmanagedExponentialArray<T, SHIFT, MAX_CHUNKS>,
    next_idx: usize,
    _marker: PhantomData<&'a ()>,
}

impl<'a, T, const SHIFT: usize, const CHUNKS: usize> Iterator for IterMut<'a, T, SHIFT, CHUNKS> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let arr = unsafe { &mut *self.arr };
        let ret = arr.get_mut(self.next_idx);
        self.next_idx += ret.is_some() as usize;
        ret
    }
}

// ----

#[macro_export]
macro_rules! __UnmanagedExponentialArray {
    ($t:ty, $shift:expr) => {
        $crate::unmanagedexponentialarray::UnmanagedExponentialArray<
            $t,
            $shift,
            { $crate::unmanagedexponentialarray::max_chunks!($shift) },
        >
    };
}

pub use __UnmanagedExponentialArray as UnmanagedExponentialArray;

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::eek;

    use crate::array::PushErrorKind;

    use super::*;

    impl<T, const SHIFT: usize, const CHUNKS: usize> UnmanagedExponentialArray<T, SHIFT, CHUNKS> {
        #[track_caller]
        #[inline]
        pub fn push(&mut self, alloc: impl Allocator, value: T) {
            match self.try_push(alloc, value) {
                Ok(..) => {}
                Err(PushError {
                    kind: PushErrorKind::OutOfMemory(alloc_error),
                    ..
                }) => eek(alloc_error),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use core::array;

    use alloc::Global;

    use crate::testutil::struct_with_counted_drop;

    use super::*;

    #[test]
    fn test_push() {
        let values = array::from_fn::<usize, 40, _>(|i| i);
        let mut this = <UnmanagedExponentialArray!(_, 8)>::default();
        for i in values {
            this.push(Global, i);
        }
        assert!(this.iter().eq(values.iter()));
    }

    #[test]
    fn test_respects_bounds() {
        const SHIFT: usize = 8;
        let mut this = <UnmanagedExponentialArray!(_, SHIFT)>::default();
        for i in 0..max_cap(SHIFT) {
            assert!(this.try_push(Global, i).is_ok());
        }
        assert!(this.try_push(Global, 0).is_err());
    }

    #[test]
    fn test_remove_unordered() {
        let mut this = <UnmanagedExponentialArray!(_, 8)>::default();
        assert!(this.remove_unordered(0).is_none());
        assert!(this.try_push(Global, 1).is_ok());
        assert!(this.try_push(Global, 2).is_ok());
        assert!(this.try_push(Global, 3).is_ok());
        assert_eq!(this.remove_unordered(0), Some(1));
        assert_eq!(this.len(), 2);
        assert!(this.iter().eq([3, 2].iter()));
    }

    #[test]
    fn test_pop() {
        let mut this = <UnmanagedExponentialArray!(_, 8)>::default();
        assert_eq!(this.pop(), None);
        assert!(this.try_push(Global, 1).is_ok());
        assert!(this.try_push(Global, 2).is_ok());
        assert_eq!(this.pop(), Some(2));
        assert_eq!(this.pop(), Some(1));
        assert_eq!(this.pop(), None);
    }

    #[test]
    fn item_locs_chunk_cap_matches_chunk_cap_xd() {
        const SHIFT: usize = 4;
        for i in 0..max_cap(SHIFT) {
            let (_, chunk_cap_, chunk_idx) = item_loc(i, SHIFT);
            assert_eq!(chunk_cap_, chunk_cap(chunk_idx, SHIFT));
        }
    }

    #[test]
    fn test_deinit() {
        struct_with_counted_drop!(Elem(u32), DROPS);

        let mut this = <UnmanagedExponentialArray!(_, 8)>::default();

        const N: u32 = 5;
        for i in 0..N {
            this.push(Global, Elem(i));
        }

        assert_eq!(DROPS.get(), 0);
        this.deinit(Global);
        assert_eq!(DROPS.get(), N);
    }
}
