use core::alloc::Layout;
use core::mem::MaybeUninit;
use core::ptr::{self, NonNull};
use core::{borrow, fmt, ops, slice};

use alloc::{AllocError, Allocator};

use crate::array::{GrowthMode, InsertError, InsertErrorKind, PushError, PushErrorKind, grow_cap};

pub struct UnmanagedArray<T> {
    cap: usize,
    len: usize,
    ptr: NonNull<T>,
}

impl<T> UnmanagedArray<T> {
    // NOTE: all of the functions below were copypasted from Array's impl.
    //   only functions that allocate memory were modified to accept alloc param.

    /// will always return `usize::MAX` if `T` is zero-sized.
    #[inline]
    pub fn cap(&self) -> usize {
        if size_of::<T>() == 0 {
            usize::MAX
        } else {
            self.cap
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
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len()) }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len()) }
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

    fn try_reserve(
        &mut self,
        alloc: impl Allocator,
        additional: usize,
        mode: GrowthMode,
    ) -> Result<(), AllocError> {
        let old_cap = self.cap();

        let Some(new_cap) = grow_cap(old_cap, self.len(), additional, size_of::<T>(), mode)? else {
            return Ok(());
        };

        let new_layout = Layout::array::<T>(new_cap).map_err(|_| AllocError)?;
        let new_ptr = if new_cap > 0 {
            let old_layout = unsafe { Layout::array::<T>(old_cap).unwrap_unchecked() };
            debug_assert_eq!(old_layout.align(), new_layout.align());
            unsafe { alloc.grow(self.ptr.cast(), old_layout, new_layout) }
        } else {
            debug_assert!(new_layout.size() > 0);
            alloc.allocate(new_layout)
        }?
        .cast();

        self.ptr = new_ptr;
        self.cap = new_cap;

        Ok(())
    }

    pub fn try_reserve_exact(
        &mut self,
        alloc: impl Allocator,
        additional: usize,
    ) -> Result<(), AllocError> {
        self.try_reserve(alloc, additional, GrowthMode::Exact)
    }

    pub fn try_reserve_amortized(
        &mut self,
        alloc: impl Allocator,
        additional: usize,
    ) -> Result<(), AllocError> {
        self.try_reserve(alloc, additional, GrowthMode::Amortized)
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

    #[inline]
    pub fn try_push(&mut self, alloc: impl Allocator, value: T) -> Result<(), PushError<T>> {
        if let Err(alloc_error) = self.try_reserve_amortized(alloc, 1) {
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

    pub fn remove_ordered(&mut self, index: usize) -> Option<T> {
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

    // TODO: drain

    /// removes all items `it` for which `f(&it)` returns `false`.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let mut retained_count = 0;
        let mut next_index = 0;
        while let Some(it) = self.get(next_index) {
            if f(it) {
                self.swap(retained_count, next_index);
                retained_count += 1;
            }
            next_index += 1;
        }
        self.truncate(retained_count);
    }

    // TODO: might want to introduce push-like variants of insert
    //   (insert_within_cap_unchecked, insert_within_cap).
    #[inline]
    pub fn try_insert(
        &mut self,
        alloc: impl Allocator,
        index: usize,
        value: T,
    ) -> Result<(), InsertError<T>> {
        let len = self.len();
        if index > self.len() {
            return Err(InsertError {
                kind: InsertErrorKind::OutOfBounds { index, len },
                value,
            });
        }

        if let Err(alloc_error) = self.try_reserve_amortized(alloc, 1) {
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
        alloc: impl Allocator,
        mut iter: I,
    ) -> Result<(), AllocError> {
        while let Some(it) = iter.next() {
            if self.cap() == self.len() {
                let (lower, _) = iter.size_hint();
                self.try_reserve_amortized(&alloc, lower.saturating_add(1))?;
            }
            unsafe { self.push_within_cap_unchecked(it) };
        }
        Ok(())
    }

    /// use [`Self::try_extend_from_iter`] for items that cannot be copied.
    pub fn try_extend_from_slice_copy(
        &mut self,
        alloc: impl Allocator,
        slice: &[T],
    ) -> Result<(), AllocError>
    where
        T: Copy,
    {
        let count = slice.len();
        self.try_reserve_amortized(alloc, count)?;
        unsafe {
            self.as_mut_ptr()
                .add(self.len())
                .copy_from_nonoverlapping(slice.as_ptr(), count)
        };
        self.len += count;
        Ok(())
    }

    pub fn try_extend_from_array<const C: usize>(
        &mut self,
        alloc: impl Allocator,
        array: [T; C],
    ) -> Result<(), AllocError> {
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
        self.try_reserve_amortized(alloc, C)?;
        unsafe { self.as_mut_ptr().cast::<[T; C]>().write(array) };
        self.len += C;
        Ok(())
    }

    // ----
    // NOTE: all of the functions below are copypasted from ResizableArray's impl.

    /// SAFETY: if `T` is a ZST `ptr` must be dangling. otherwise:
    ///   - `ptr` must have been allocated with the allocator `A`.
    ///   - `ptr` must point to memory with a size of at least `size_of::<T>() * cap` bytes.
    ///   - `len` must be less than or equal to `cap`.
    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut T, len: usize, cap: usize) -> Self {
        Self {
            cap,
            len,
            // SAFETY: by the safety requirements, `ptr` is either dangling or pointing to a valid
            // memory allocation, allocated with `A`.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }

    // ----
    // NOTE: below are UnmanagedArray-specific functions

    pub fn deinit(&mut self, alloc: impl Allocator) {
        self.clear();
        let layout = unsafe { Layout::array::<T>(self.cap()).unwrap_unchecked() };
        // SAFETY: even if T is zst Allocator and ptr is dangling - alloc knows how to handle that.
        unsafe { alloc.deallocate(self.ptr.cast(), layout) }
    }
}

impl<T> ops::Deref for UnmanagedArray<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> ops::DerefMut for UnmanagedArray<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> borrow::Borrow<[T]> for UnmanagedArray<T> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> borrow::BorrowMut<[T]> for UnmanagedArray<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> Default for UnmanagedArray<T> {
    #[inline]
    fn default() -> Self {
        Self {
            cap: 0,
            len: 0,
            ptr: NonNull::dangling(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for UnmanagedArray<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_slice(), f)
    }
}

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::{eek, this_is_fine};

    use super::*;

    impl<T> UnmanagedArray<T> {
        #[track_caller]
        #[inline]
        pub fn reserve_exact(&mut self, alloc: impl Allocator, additional: usize) {
            this_is_fine(self.try_reserve_exact(alloc, additional))
        }

        #[track_caller]
        #[inline]
        pub fn reserve_amortized(&mut self, alloc: impl Allocator, additional: usize) {
            this_is_fine(self.try_reserve_amortized(alloc, additional))
        }

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

        #[track_caller]
        #[inline]
        pub fn insert(&mut self, alloc: impl Allocator, index: usize, value: T) {
            match self.try_insert(alloc, index, value) {
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

        #[track_caller]
        #[inline]
        pub fn extend_from_iter<I: Iterator<Item = T>>(&mut self, alloc: impl Allocator, iter: I) {
            this_is_fine(self.try_extend_from_iter(alloc, iter))
        }

        #[track_caller]
        #[inline]
        pub fn extend_from_slice_copy(&mut self, alloc: impl Allocator, other: &[T])
        where
            T: Copy,
        {
            this_is_fine(self.try_extend_from_slice_copy(alloc, other))
        }

        #[track_caller]
        #[inline]
        pub fn extend_from_array<const C: usize>(&mut self, alloc: impl Allocator, array: [T; C]) {
            this_is_fine(self.try_extend_from_array(alloc, array))
        }
    }
}
