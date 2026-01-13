use core::error::Error;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::ptr::{self, NonNull};
use core::slice;
use core::{fmt, ops};
use std::io;

use alloc::{AllocError, Allocator};
use scopeguard::ScopeGuard;

use crate::arraymemory::{
    ArrayMemory, FixedArrayMemory, GrowableArrayMemory, SpillableArrayMemory,
};

// TODO: think about how to do better job at growing.
//   maybe with some kind of GrowthStrategy?

// NOTE: this is copypasted from std.
//
// Tiny Vecs are dumb. Skip to:
// - 8 if the item size is 1, because any heap allocator is likely
//   to round up a request of less than 8 bytes to at least 8 bytes.
// - 4 if items are moderate-sized (<= 1 KiB).
// - 1 otherwise, to avoid wasting too much space for very short Vecs.
const fn min_non_zero_cap(size: usize) -> usize {
    if size == 1 {
        8
    } else if size <= 1024 {
        4
    } else {
        1
    }
}

// TODO: get rid of this when `slice_range` feature is stable.
fn try_range_from_bounds<R>(range: R, bounds: ops::RangeTo<usize>) -> Option<ops::Range<usize>>
where
    R: ops::RangeBounds<usize>,
{
    let len = bounds.end;

    let start = match range.start_bound() {
        ops::Bound::Included(&start) => start,
        ops::Bound::Excluded(start) => start.checked_add(1)?,
        ops::Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
        ops::Bound::Included(end) => end.checked_add(1)?,
        ops::Bound::Excluded(&end) => end,
        ops::Bound::Unbounded => len,
    };

    if start > end || end > len {
        None
    } else {
        Some(ops::Range { start, end })
    }
}

pub enum PushErrorKind {
    OutOfMemory(AllocError),
}

pub struct PushError<T> {
    pub kind: PushErrorKind,
    pub value: T,
}

impl<T> Error for PushError<T> {}

impl<T> fmt::Display for PushError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            PushErrorKind::OutOfMemory(ref alloc_error) => fmt::Display::fmt(alloc_error, f),
        }
    }
}

// @BlindDerive
impl<T> fmt::Debug for PushError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

pub enum InsertErrorKind {
    OutOfBounds { index: usize, len: usize },
    OutOfMemory(AllocError),
}

pub struct InsertError<T> {
    pub kind: InsertErrorKind,
    pub value: T,
}

impl<T> Error for InsertError<T> {}

impl<T> fmt::Display for InsertError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            InsertErrorKind::OutOfBounds { index, len } => {
                f.write_fmt(format_args!("out of bounds (index {index}, len {len})"))
            }
            InsertErrorKind::OutOfMemory(ref alloc_error) => fmt::Display::fmt(alloc_error, f),
        }
    }
}

// @BlindDerive
impl<T> fmt::Debug for InsertError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

pub struct Array<T, M: ArrayMemory<T>> {
    mem: M,
    len: usize,
    _ty: PhantomData<T>,
}

const _: () = {
    let this = size_of::<Array<u8, GrowableArrayMemory<u8, alloc::Global>>>();
    let std = size_of::<std::vec::Vec<u8>>();
    assert!(this <= std)
};

impl<T, M: ArrayMemory<T>> Array<T, M> {
    #[inline]
    const fn is_zst() -> bool {
        size_of::<T>() == 0
    }

    #[inline]
    pub fn new_in(mem: M) -> Self {
        Self {
            mem,
            len: 0,
            _ty: PhantomData,
        }
    }

    #[inline]
    pub fn memory(&self) -> &M {
        &self.mem
    }

    /// will always return `usize::MAX` if `T` is zero-sized.
    #[inline]
    pub fn cap(&self) -> usize {
        if Self::is_zst() {
            usize::MAX
        } else {
            self.mem.cap()
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// SAFETY: new_len must be less than or equal to capacity.
    /// the items at old_len..new_len must be initialized.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.cap());
        self.len = new_len;
    }

    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.mem.as_ptr(), self.len()) }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.mem.as_mut_ptr(), self.len()) }
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), AllocError> {
        let cap = self.cap();
        let len = self.len();

        if cap - len >= additional {
            return Ok(());
        }

        if Self::is_zst() {
            return Err(AllocError);
        }

        let required_cap = len.checked_add(additional).ok_or(AllocError)?;

        // SAFETY: we ensured above that new cap would be greater then current.
        unsafe { self.mem.grow(required_cap) }
    }

    pub fn try_reserve_amortized(&mut self, additional: usize) -> Result<(), AllocError> {
        let cap = self.cap();
        let len = self.len();

        if cap - len >= additional {
            return Ok(());
        }

        if Self::is_zst() {
            // NOTE: the capacity is already `usize::MAX` for zsts.
            return Err(AllocError);
        }

        let required_cap = len.checked_add(additional).ok_or(AllocError)?;
        let amortized_cap = required_cap
            // NOTE: the doubling cannot overflow because `cap <= isize::MAX`.
            //   `Layout::array` upholds this.
            .max(cap * 2)
            .max(min_non_zero_cap(size_of::<T>()));

        // SAFETY: we ensured above that new cap would be greater then current.
        unsafe { self.mem.grow(amortized_cap) }
    }

    #[inline]
    pub fn spare_cap_mut(&mut self) -> &mut [MaybeUninit<T>] {
        let len = self.len();
        // SAFETY: the memory between `self.len` and `self.cap` is guaranteed to be allocated
        // and valid, but uninitialized.
        unsafe {
            let ptr = self.as_mut_ptr().add(len).cast::<MaybeUninit<T>>();
            slice::from_raw_parts_mut(ptr, self.cap() - len)
        }
    }

    /// SAFETY: the length must be less than the capacity.
    #[inline]
    pub unsafe fn push_within_cap_unchecked(&mut self, value: T) {
        let spare = self.spare_cap_mut();
        // SAFETY: by the safety requirements, `spare` is non-empty.
        unsafe { spare.get_unchecked_mut(0).write(value) };
        self.len += 1;
    }

    #[inline]
    pub fn push_within_cap(&mut self, value: T) -> Option<T> {
        if self.cap() == self.len() {
            return Some(value);
        }
        unsafe { self.push_within_cap_unchecked(value) };
        None
    }

    // TODO: should there be a custom error for push?
    //   that will contain value so that the caller can get it back?
    #[inline]
    pub fn try_push(&mut self, value: T) -> Result<(), PushError<T>> {
        if let Err(alloc_error) = self.try_reserve_amortized(1) {
            return Err(PushError {
                kind: PushErrorKind::OutOfMemory(alloc_error),
                value,
            });
        }
        unsafe { self.push_within_cap_unchecked(value) };
        Ok(())
    }

    /// removes the last item and returns it, or `None` if it is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.len() == 0 {
            return None;
        }
        unsafe {
            self.len -= 1;
            Some(self.as_ptr().add(self.len()).read())
        }
    }

    pub fn remove(&mut self, index: usize) -> Option<T> {
        let len = self.len();
        // TODO: might want to introduce RemoveError (to be able to indicate oob).
        if index >= len {
            return None;
        }
        unsafe {
            let ptr = self.as_mut_ptr().add(index);
            // NOTE: now we'll have two values. one here, on the stack, and one in array.
            let value = ptr::read(ptr);
            // shift everything to fill in that spot.
            ptr::copy(ptr.add(1), ptr, len - index - 1);
            self.len -= 1;
            Some(value)
        }
    }

    /// shortens the array, setting the length to `len` and drops the removed values.
    /// this has no effect on the capacity and will not allocate.
    pub fn truncate(&mut self, len: usize) {
        let Some(count) = self.len().checked_sub(len) else {
            return;
        };
        unsafe {
            let to_drop = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), count);
            self.len = len;
            to_drop.drop_in_place();
        }
    }

    /// removes all items, has no effect on the allocated capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
        debug_assert!(self.len() == 0);
    }

    /// takes ownership of the subslice indicated by the given range without consuming the
    /// allocation.
    ///
    /// # panics
    ///
    /// if the range is invalid (`range.start > range.end`) or if end out of bounds
    /// `range.end > self.len()`.
    ///
    /// # leaks
    ///
    /// if [`Drain`] goes out of scope without being dropped (due to [`std::mem::forget`], for
    /// example), the array may have lost and leaked items arbitrarily, including items outside
    /// the range.
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, M>
    where
        R: ops::RangeBounds<usize>,
    {
        let len = self.len();
        // TODO(blukai): maybe non-paniching variant of drain (try_drain?).
        let ops::Range { start, end } = try_range_from_bounds(range, ..len).expect("invalid range");
        // NOTE: when Drain drops the remaining tail of the array is copied back to cover the hole.
        unsafe {
            // NOTE: set len to start, to be safe in case Drain's leakage.
            self.len = start;
            let iter =
                slice::from_raw_parts_mut(self.as_mut_ptr().add(start), end - start).iter_mut();
            Drain {
                iter,
                ptr: NonNull::from(self),
                tail_start: end,
                tail_len: len - end,
            }
        }
    }

    // TODO: might want to introduce push-like variants of insert
    //   (insert_within_cap_unchecked, insert_within_cap).
    #[inline]
    pub fn try_insert(&mut self, index: usize, value: T) -> Result<(), InsertError<T>> {
        let len = self.len();
        if index > self.len() {
            return Err(InsertError {
                kind: InsertErrorKind::OutOfBounds { index, len },
                value,
            });
        }

        if let Err(alloc_error) = self.try_reserve_amortized(1) {
            return Err(InsertError {
                kind: InsertErrorKind::OutOfMemory(alloc_error),
                value,
            });
        }

        unsafe {
            let ptr = self.as_mut_ptr().add(index);
            if index < len {
                // shift everything to make space
                // NOTE: this makes the indexth item exist in two places (temporarily).
                ptr.copy_to(ptr.add(1), len - index);
            }
            ptr.write(value);
            self.len += 1;
        }

        Ok(())
    }

    // ----
    // extend from

    pub fn try_extend_from_iter<I: Iterator<Item = T>>(
        &mut self,
        mut iter: I,
    ) -> Result<(), AllocError> {
        while let Some(it) = iter.next() {
            if self.cap() == self.len() {
                let (lower, _) = iter.size_hint();
                self.try_reserve_amortized(lower.saturating_add(1))?;
            }
            unsafe { self.push_within_cap_unchecked(it) };
        }
        Ok(())
    }

    /// use [`Self::try_extend_from_iter`] for items that cannot be copied.
    pub fn try_extend_from_slice_copy(&mut self, slice: &[T]) -> Result<(), AllocError>
    where
        T: Copy,
    {
        let count = slice.len();
        self.try_reserve_amortized(count)?;
        unsafe {
            self.as_mut_ptr()
                .add(self.len())
                .copy_from_nonoverlapping(slice.as_ptr(), count)
        };
        self.len += count;
        Ok(())
    }

    // ----
    // builder-lite

    #[inline]
    pub fn try_with_cap(mut self, cap: usize) -> Result<Self, AllocError> {
        // TODO: should with_cap resize (grow/shrink)?
        assert_eq!(self.cap(), 0);
        self.try_reserve_exact(cap)?;
        Ok(self)
    }

    // ----
    // builder-lite with

    pub fn try_with_iter<I: Iterator<Item = T>>(mut self, iter: I) -> Result<Self, AllocError> {
        self.try_extend_from_iter(iter)?;
        Ok(self)
    }

    /// use [`Self::try_with_iter`] for items that cannot be copied.
    pub fn try_with_slice_copy(mut self, slice: &[T]) -> Result<Self, AllocError>
    where
        T: Copy,
    {
        let count = slice.len();
        self.try_reserve_exact(count)?;
        unsafe {
            self.as_mut_ptr()
                .add(self.len())
                .copy_from_nonoverlapping(slice.as_ptr(), count)
        };
        self.len += count;
        Ok(self)
    }

    pub fn try_with_array<const C: usize>(mut self, array: [T; C]) -> Result<Self, AllocError> {
        // NOTE: this is somewhat of an untangled version of what std does
        //   but not quite; although technically mostly yes...
        //
        //   std puts array into Box first, deconstructs it into raw ptr and alloc, and then
        //   constructs Vec from raw parts.
        //
        //   std's Box::new method is relying on not-publicly-available lang exchange malloc
        //   intrinsic that supposedly can put array onto the heap right away omitting the stack
        //   (somehow? how?).
        //   we can't do exactly copy that.
        self.try_reserve_exact(array.len())?;
        unsafe { self.as_mut_ptr().cast::<[T; C]>().write(array) };
        self.len = C;
        Ok(self)
    }
}

impl<T, M: ArrayMemory<T>> ops::Deref for Array<T, M> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, M: ArrayMemory<T>> ops::DerefMut for Array<T, M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, M: ArrayMemory<T>> Drop for Array<T, M> {
    fn drop(&mut self) {
        unsafe { ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len()).drop_in_place() };
    }
}

impl<T, M: ArrayMemory<T> + Default> Default for Array<T, M> {
    #[inline]
    fn default() -> Self {
        Self::new_in(M::default())
    }
}

impl<T: fmt::Debug, M: ArrayMemory<T>> fmt::Debug for Array<T, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_slice(), f)
    }
}

macro_rules! impl_partial_eq {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty $(where $ty:ty: $bound:ident)?) => {
        impl<T, U, $($vars)*> PartialEq<$rhs> for $lhs
        where
            T: PartialEq<U>,
            $($ty: $bound)?
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { self[..] == other[..] }
        }
    }
}

impl_partial_eq! { [M1: ArrayMemory<T>, M2: ArrayMemory<U>] Array<T, M1>, Array<U, M2> }

impl_partial_eq! { [M: ArrayMemory<T>, const C: usize] Array<T, M>, [U; C] }
impl_partial_eq! { [M: ArrayMemory<T>] Array<T, M>, [U] }
impl_partial_eq! { [M: ArrayMemory<T>] Array<T, M>, std::vec::Vec<U> }

impl_partial_eq! { [M: ArrayMemory<U>, const C: usize] [T; C], Array<U, M> }
impl_partial_eq! { [M: ArrayMemory<U>] [T], Array<U, M> }
impl_partial_eq! { [M: ArrayMemory<U>] std::vec::Vec<T>, Array<U, M> }

impl<T: Hash, M: ArrayMemory<T>> Hash for Array<T, M> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(self.as_slice(), state)
    }
}

/// the array will grow as needed.
impl<M: ArrayMemory<u8>> io::Write for Array<u8, M> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.try_extend_from_slice_copy(buf)
            .map_err(io::Error::other)?;
        Ok(buf.len())
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[io::IoSlice<'_>]) -> io::Result<usize> {
        let len = bufs.iter().map(|b| b.len()).sum();
        self.try_reserve_amortized(len).map_err(io::Error::other)?;
        for buf in bufs {
            // NOTE: ok to ignore because reserve ^ above did succeed.
            _ = self.try_extend_from_slice_copy(buf);
        }
        Ok(len)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.try_extend_from_slice_copy(buf)
            .map_err(io::Error::other)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub struct Drain<'v, T: 'v, M: ArrayMemory<T> + 'v> {
    iter: slice::IterMut<'v, T>,
    ptr: NonNull<Array<T, M>>,
    tail_start: usize,
    tail_len: usize,
}

impl<T, M: ArrayMemory<T>> Drop for Drain<'_, T, M> {
    fn drop(&mut self) {
        // QUOTE:
        // > moves back the un-`Drain`ed items to restore the original `Vec`.
        // > ensure items are moved back into their appropriate places, even when drop_in_place panics
        let _guard = ScopeGuard::new(|| {
            if self.tail_len == 0 {
                return;
            }

            unsafe {
                let this = self.ptr.as_mut();
                let start = this.len();
                let tail = self.tail_start;
                if tail != start {
                    let src = this.as_ptr().add(tail);
                    let dst = this.as_mut_ptr().add(start);
                    ptr::copy(src, dst, self.tail_len);
                }
                this.len = start + self.tail_len;
            }
        });

        let iter = mem::take(&mut self.iter);
        // SAFETY: we own these values so we destroy them.
        unsafe { ptr::drop_in_place(iter.into_slice()) };
    }
}

impl<T, M: ArrayMemory<T>> Iterator for Drain<'_, T, M> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next().map(|it| unsafe { ptr::read(it) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, M: ArrayMemory<T>> DoubleEndedIterator for Drain<'_, T, M> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back().map(|it| unsafe { ptr::read(it) })
    }
}

impl<T, M: ArrayMemory<T>> ExactSizeIterator for Drain<'_, T, M> {}

// ----

#[inline]
fn try_array_clone_slow<T: Clone, M: ArrayMemory<T>>(
    src: &Array<T, M>,
    dst: &mut Array<T, M>,
) -> Result<(), AllocError> {
    assert!(dst.is_empty());
    // NOTE: researve enough space to avoid reallocations that can be caused by logic
    // that extends self from iter.
    dst.try_reserve_exact(src.len())?;
    // TODO: @Specialization don't iter cloned copyable items, copy all at once.
    dst.extend_from_iter(src.iter().cloned());
    Ok(())
}

// ----
// aliases and their makers below

#[expect(type_alias_bounds)]
pub type GrowableArray<T, A: Allocator> = Array<T, GrowableArrayMemory<T, A>>;

impl<T, A: Allocator> GrowableArray<T, A> {
    #[inline]
    pub fn new_growable_in(alloc: A) -> Self {
        Self::new_in(GrowableArrayMemory::new_in(alloc))
    }
}

pub type FixedArray<T, const N: usize> = Array<T, FixedArrayMemory<T, N>>;

const _: () = {
    // NOTE: max len of string + length
    assert!(size_of::<FixedArray<u8, 16>>() == 16 + size_of::<usize>());
};

impl<T, const N: usize> FixedArray<T, N> {
    #[inline]
    pub fn new_fixed() -> Self {
        Self::new_in(FixedArrayMemory::default())
    }
}

impl<T: Clone, const N: usize> Clone for FixedArray<T, N> {
    fn clone(&self) -> Self {
        let mut ret = Self::new_fixed();
        // NOTE: ok to unwrap. both array's capacities are equal.
        try_array_clone_slow(self, &mut ret).unwrap();
        ret
    }
}

#[expect(type_alias_bounds)]
pub type SpillableArray<T, const N: usize, A: Allocator> = Array<T, SpillableArrayMemory<T, N, A>>;

impl<T, const N: usize, A: Allocator> SpillableArray<T, N, A> {
    #[inline]
    pub fn new_spillable_in(alloc: A) -> Self {
        Self::new_in(SpillableArrayMemory::new_in(alloc))
    }

    #[inline]
    pub fn is_spilled(&self) -> bool {
        self.mem.is_spilled()
    }
}

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use crate::{eek, this_is_fine};

    use super::*;

    impl<T, M: ArrayMemory<T>> Array<T, M> {
        #[inline]
        pub fn reserve_exact(&mut self, additional: usize) {
            this_is_fine(self.try_reserve_exact(additional))
        }

        #[inline]
        pub fn reserve_amortized(&mut self, additional: usize) {
            this_is_fine(self.try_reserve_amortized(additional))
        }

        #[inline]
        pub fn push(&mut self, value: T) {
            match self.try_push(value) {
                Ok(..) => {}
                Err(PushError {
                    kind: PushErrorKind::OutOfMemory(alloc_error),
                    ..
                }) => eek(alloc_error),
            }
        }

        #[inline]
        pub fn insert(&mut self, index: usize, value: T) {
            match self.try_insert(index, value) {
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

        #[inline]
        pub fn extend_from_slice_copy(&mut self, other: &[T])
        where
            T: Copy,
        {
            this_is_fine(self.try_extend_from_slice_copy(other))
        }

        // ----
        // builder-lite

        #[inline]
        pub fn with_cap(self, cap: usize) -> Self {
            this_is_fine(self.try_with_cap(cap))
        }

        // ----
        // builder-lite with

        #[inline]
        pub fn with_iter<I: Iterator<Item = T>>(self, iter: I) -> Self {
            this_is_fine(self.try_with_iter(iter))
        }

        #[inline]
        pub fn with_slice_copy(self, slice: &[T]) -> Self
        where
            T: Copy,
        {
            this_is_fine(self.try_with_slice_copy(slice))
        }

        #[inline]
        pub fn with_array<const C: usize>(self, array: [T; C]) -> Self {
            this_is_fine(self.try_with_array(array))
        }
    }

    // @TryCloneIn
    impl<T: Clone, A: Allocator + Clone> Clone for GrowableArray<T, A> {
        fn clone(&self) -> Self {
            let mut ret = Self::new_growable_in(self.mem.allocator().clone());
            this_is_fine(try_array_clone_slow(self, &mut ret));
            ret
        }
    }

    // @TryCloneIn
    impl<T: Clone, const N: usize, A: Allocator + Clone> Clone for SpillableArray<T, N, A> {
        fn clone(&self) -> Self {
            let mut ret = Self::new_spillable_in(self.mem.allocator().clone());
            this_is_fine(try_array_clone_slow(self, &mut ret));
            ret
        }
    }
}

// ----

#[cfg(test)]
mod tests {
    use core::iter;

    use crate::testutil::struct_with_counted_drop;

    use super::*;

    #[test]
    fn test_push() {
        let mut this = Array::<u32, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        this.push(8);
        this.push(16);
        assert_eq!(this, [8, 16]);
    }

    #[test]
    fn test_pop() {
        let mut this =
            Array::<u32, _>::new_in(GrowableArrayMemory::new_in(alloc::Global)).with_array([8, 16]);
        assert_eq!(this.pop(), Some(16));
        assert_eq!(this.pop(), Some(8));
        assert_eq!(this.pop(), None);
        assert_eq!(this, []);
    }

    #[test]
    fn test_remove() {
        let mut this =
            Array::new_in(GrowableArrayMemory::new_in(alloc::Global)).with_array([1, 2, 3]);
        assert_eq!(this.remove(0), Some(1));
        assert_eq!(this.remove(2), None);

        let mut this = Array::<u32, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        assert!(this.remove(0).is_none());
    }

    #[test]
    fn test_index() {
        let this =
            Array::<u32, _>::new_in(GrowableArrayMemory::new_in(alloc::Global)).with_array([8, 16]);
        assert_eq!(this[0], 8);
        assert_eq!(this[1], 16);
    }

    #[test]
    fn test_drain() {
        let mut a = Array::new_in(GrowableArrayMemory::new_in(alloc::Global)).with_array([8, 16]);
        let b = Array::new_in(GrowableArrayMemory::new_in(alloc::Global)).with_iter(a.drain(..));
        assert_eq!(a, []);
        assert_eq!(b, [8, 16]);
    }

    #[test]
    fn test_insert() {
        let mut this = Array::new_in(GrowableArrayMemory::new_in(alloc::Global)).with_array([16]);
        this.insert(0, 8);
        assert_eq!(this, [8, 16]);
    }

    #[test]
    fn test_uses_provided_allocator() {
        let mut temp_data = [0; 1000];
        let temp = alloc::TempAllocator::new(&mut temp_data);

        let mut this: Array<u32, _> = Array::new_in(GrowableArrayMemory::new_in(&temp));

        this.reserve_amortized(42);
        assert_eq!(temp.get_checkpoint().occupied, 42 * size_of::<u32>());
    }

    #[test]
    fn test_matches_std_reserve_amortized_strategy() {
        {
            let mut this: Array<u32, _> = Array::new_in(GrowableArrayMemory::new_in(alloc::Global));
            let mut std: std::vec::Vec<u32> = std::vec::Vec::new();

            this.reserve_amortized(9);
            std.reserve(9);
            assert_eq!(this.cap(), std.capacity());
        }

        {
            let mut this: Array<u32, _> = Array::new_in(GrowableArrayMemory::new_in(alloc::Global));
            let mut std: std::vec::Vec<u32> = std::vec::Vec::new();

            this.reserve_amortized(8);
            std.reserve(8);
            assert_eq!(this.cap(), std.capacity());

            this.reserve_amortized(90);
            std.reserve(90);
            assert_eq!(this.cap(), std.capacity());
        }
    }

    #[test]
    fn test_matches_std_zst_allocation_strategy() {
        let mut temp_data = [0; 1000];
        let temp = alloc::TempAllocator::new(&mut temp_data);

        #[derive(Clone, Copy)]
        struct ZST;

        let mut this: Array<ZST, _> = Array::new_in(GrowableArrayMemory::new_in(&temp));
        let mut std: std::vec::Vec<ZST> = std::vec::Vec::new();

        this.extend_from_iter(iter::repeat_n(ZST, 101));
        assert!(matches!(
            this.try_reserve_amortized(usize::MAX - 100),
            Err(AllocError)
        ));

        std.extend(iter::repeat_n(ZST, 101));
        assert!(matches!(
            std.try_reserve(usize::MAX - 100),
            Err(std::collections::TryReserveError { .. })
        ));

        // NOTE: ensure that vec did attempt to allocate memory.
        assert_eq!(temp.get_high_water_mark(), 0);
    }

    // ----
    // fixed memory

    #[test]
    fn test_fixed_push() {
        let mut this = FixedArray::<u32, 2>::default();
        assert!(this.try_push(8).is_ok());
        assert!(this.try_push(16).is_ok());
        assert!(this.try_push(32).is_err());
        assert_eq!(this, [8, 16]);
    }

    // ----
    // fixed growable memory

    #[test]
    fn test_fixed_spill() {
        let mut temp_data = [0; 1000];
        let temp = alloc::TempAllocator::new(&mut temp_data);

        let mut this = SpillableArray::new_in(SpillableArrayMemory::<u32, 2, _>::new_in(&temp));
        assert!(this.try_push(8).is_ok());
        assert!(this.try_push(16).is_ok());
        assert!(!this.is_spilled());
        assert!(this.try_push(32).is_ok());
        assert!(this.is_spilled());
        assert_eq!(this, [8, 16, 32]);
    }

    // ----
    // NOTE: tests that start with test_std_ are stolen from std.

    #[test]
    fn test_std_double_drop() {
        struct DropCounter<'a> {
            count: &'a mut u32,
        }

        impl Drop for DropCounter<'_> {
            fn drop(&mut self) {
                *self.count += 1;
            }
        }

        struct TwoArrays<T, M: ArrayMemory<T>> {
            x: Array<T, M>,
            y: Array<T, M>,
        }

        let (mut count_x, mut count_y) = (0, 0);
        {
            let mut tv = TwoArrays {
                x: Array::new_in(GrowableArrayMemory::new_in(alloc::Global)),
                y: Array::new_in(GrowableArrayMemory::new_in(alloc::Global)),
            };
            tv.x.push(DropCounter {
                count: &mut count_x,
            });
            tv.y.push(DropCounter {
                count: &mut count_y,
            });

            // If Array had a drop flag, here is where it would be zeroed.
            // Instead, it should rely on its internal state to prevent
            // doing anything significant when dropped multiple times.
            drop(tv.x);

            // Here tv goes out of scope, tv.y should be dropped, but not tv.x.
        }
        assert_eq!(count_x, 1);
        assert_eq!(count_y, 1);
    }

    #[test]
    #[cfg_attr(not(panic = "unwind"), ignore = "test requires unwinding support")]
    fn test_std_drain_leak() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        struct_with_counted_drop!(D(u32, bool), DROPS => |this: &D| if this.1 { panic!("panic in `drop`"); });

        let mut v = Array::new_in(GrowableArrayMemory::new_in(alloc::Global)).with_array([
            D(0, false),
            D(1, false),
            D(2, false),
            D(3, false),
            D(4, true),
            D(5, false),
            D(6, false),
        ]);

        catch_unwind(AssertUnwindSafe(|| {
            v.drain(2..=5);
        }))
        .ok();

        assert_eq!(DROPS.get(), 4);
        assert_eq!(v, [D(0, false), D(1, false), D(6, false)]);
    }

    #[test]
    fn test_std_truncate_drop() {
        struct_with_counted_drop!(Elem(i32), DROPS);

        let mut v = Array::new_in(GrowableArrayMemory::new_in(alloc::Global)).with_array([
            Elem(1),
            Elem(2),
            Elem(3),
            Elem(4),
            Elem(5),
        ]);

        assert_eq!(DROPS.get(), 0);
        v.truncate(3);
        assert_eq!(DROPS.get(), 2);
        v.truncate(0);
        assert_eq!(DROPS.get(), 5);
    }

    #[test]
    fn test_std_clone() {
        let v = Array::<i32, _>::new_in(GrowableArrayMemory::new_in(alloc::Global));
        let w = Array::new_in(GrowableArrayMemory::<i32, _>::new_in(alloc::Global))
            .with_array([1, 2, 3]);

        assert_eq!(v, v.clone());

        let z = w.clone();
        assert_eq!(w, z);
        // they should be disjoint in memory.
        assert!(w.as_ptr() != z.as_ptr())
    }
}
