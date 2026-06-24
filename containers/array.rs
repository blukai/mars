use core::alloc::Layout;
use core::error::Error;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ptr::{self, NonNull};
use core::{borrow, cmp, fmt, ops, slice};
use std::io;

use alloc::{AllocError, Allocator};
use dropguard::DropGuard;

use crate::boxed::Box;

pub unsafe trait ArrayMemory<T> {
    fn as_ptr(&self) -> *mut T;
    fn cap(&self) -> usize;
    /// `new_cap` must be greater then the current capacity.
    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), AllocError>;
    // TODO: Memory will also need srink method.
}

// TODO: think about how to do better job at growing.
//   maybe with some kind of GrowthStrategy?

// NOTE: this is copypasted from std.
//
// Tiny Vecs are dumb. Skip to:
// - 8 if the item size is 1, because any heap allocator is likely
//   to round up a request of less than 8 bytes to at least 8 bytes.
// - 4 if items are moderate-sized (<= 1 KiB).
// - 1 otherwise, to avoid wasting too much space for very short Vecs.
#[inline]
const fn min_non_zero_cap(item_size: usize) -> usize {
    if item_size == 1 {
        8
    } else if item_size <= 1024 {
        4
    } else {
        1
    }
}

pub enum GrowthMode {
    Exact,
    Amortized,
}

#[inline]
pub fn grow_cap(
    cap: usize,
    len: usize,
    additional: usize,
    item_size: usize,
    mode: GrowthMode,
) -> Result<Option<usize>, AllocError> {
    if cap - len >= additional {
        return Ok(None);
    }

    if item_size == 0 {
        // NOTE: the capacity is already `usize::MAX` for zsts.
        return Err(AllocError);
    }

    let new_cap = len.checked_add(additional).ok_or(AllocError)?;
    let new_cap = match mode {
        GrowthMode::Exact => new_cap,
        GrowthMode::Amortized => new_cap
            // NOTE: the doubling cannot overflow because `cap <= isize::MAX`. `Layout::array`
            // upholds this.
            .max(cap * 2)
            .max(min_non_zero_cap(item_size)),
    };
    Ok(Some(new_cap))
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

// :BlindDerive
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

// :BlindDerive
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

impl<T, M: ArrayMemory<T>> Array<T, M> {
    #[inline]
    pub fn new_in<I: Into<M>>(mem: I) -> Self {
        Self {
            mem: mem.into(),
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
        if size_of::<T>() == 0 {
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
        unsafe { slice::from_raw_parts_mut(self.mem.as_ptr(), self.len()) }
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

    fn try_reserve(&mut self, additional: usize, mode: GrowthMode) -> Result<(), AllocError> {
        let Some(new_cap) = grow_cap(self.cap(), self.len(), additional, size_of::<T>(), mode)?
        else {
            return Ok(());
        };
        // SAFETY: grow_cap returns Some(new_cap) iff new cap is greater then old.
        unsafe { self.mem.grow(new_cap) }
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), AllocError> {
        self.try_reserve(additional, GrowthMode::Exact)
    }

    pub fn try_reserve_amortized(&mut self, additional: usize) -> Result<(), AllocError> {
        self.try_reserve(additional, GrowthMode::Amortized)
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

    pub fn try_extend_from_array<const C: usize>(
        &mut self,
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
        self.try_reserve_amortized(C)?;
        unsafe {
            self.as_mut_ptr()
                .add(self.len())
                .cast::<[T; C]>()
                .write(array)
        };
        self.len += C;
        Ok(())
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

impl<T, M: ArrayMemory<T>> borrow::Borrow<[T]> for Array<T, M> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, M: ArrayMemory<T>> borrow::BorrowMut<[T]> for Array<T, M> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, M: ArrayMemory<T>> Drop for Array<T, M> {
    fn drop(&mut self) {
        self.clear();
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
        impl<T1, T2, $($vars)*> PartialEq<$rhs> for $lhs
        where
            T1: PartialEq<T2>,
            $($ty: $bound)?
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
        }
    }
}

impl_partial_eq! { [M1: ArrayMemory<T1>, M2: ArrayMemory<T2>] Array<T1, M1>, Array<T2, M2> }

impl_partial_eq! { [M: ArrayMemory<T1>, const C: usize] Array<T1, M>, [T2; C] }
impl_partial_eq! { [M: ArrayMemory<T1>] Array<T1, M>, [T2] }
impl_partial_eq! { [M: ArrayMemory<T1>] Array<T1, M>, std::vec::Vec<T2> }

impl_partial_eq! { [M: ArrayMemory<T2>, const C: usize] [T1; C], Array<T2, M> }
impl_partial_eq! { [M: ArrayMemory<T2>] [T1], Array<T2, M> }
impl_partial_eq! { [M: ArrayMemory<T2>] std::vec::Vec<T1>, Array<T2, M> }

impl<T: Eq, M: ArrayMemory<T>> Eq for Array<T, M> {}

impl<T: PartialOrd, M: ArrayMemory<T>> PartialOrd for Array<T, M> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(&self[..], &other[..])
    }
}

impl<T: Ord, M: ArrayMemory<T>> Ord for Array<T, M> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(&self[..], &other[..])
    }
}

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
        let _guard = DropGuard::new(|| {
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
fn try_array_clone_slow<T: Clone, M1: ArrayMemory<T>, M2: ArrayMemory<T>>(
    src: &Array<T, M1>,
    dst: &mut Array<T, M2>,
) -> Result<(), AllocError> {
    assert!(dst.is_empty());
    // NOTE: researve enough space to avoid reallocations that can be caused by logic
    // that extends self from iter.
    dst.try_reserve_exact(src.len())?;
    // TODO: :Specialization don't iter cloned copyable items, copy all at once.
    dst.extend_from_iter(src.iter().cloned());
    Ok(())
}

// ----
// resizable

pub struct ResizableArrayMemory<T, A: Allocator> {
    ptr: NonNull<T>,
    cap: usize,
    alloc: A,
}

impl<T, A: Allocator> ResizableArrayMemory<T, A> {
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        Self {
            ptr: NonNull::dangling(),
            cap: 0,
            alloc,
        }
    }

    /// SAFETY: if `T` is a ZST `ptr` must be dangling. otherwise:
    ///   - `ptr` must have been allocated with the allocator `A`.
    ///   - `ptr` must point to memory with a size of at least `size_of::<T>() * cap` bytes.
    #[inline]
    pub unsafe fn from_raw_parts_in(ptr: *mut T, cap: usize, alloc: A) -> Self {
        Self {
            // SAFETY: by the safety requirements, `ptr` is either dangling or pointing to a valid
            // memory allocation, allocated with `A`.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            cap,
            alloc,
        }
    }

    #[inline]
    pub fn allocator(&self) -> &A {
        &self.alloc
    }
}

unsafe impl<T, A: Allocator> ArrayMemory<T> for ResizableArrayMemory<T, A> {
    #[inline]
    fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    #[inline]
    fn cap(&self) -> usize {
        self.cap
    }

    /// SAFETY: `new_cap` must be greater then the current capacity.
    #[inline]
    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), AllocError> {
        let old_cap = self.cap();

        // NOTE: this must be ensured by the caller.
        debug_assert!(new_cap > old_cap);

        let new_layout = Layout::array::<T>(new_cap).map_err(|_| AllocError)?;
        let new_ptr = if new_cap > 0 {
            let old_layout = unsafe { Layout::array::<T>(old_cap).unwrap_unchecked() };
            debug_assert_eq!(old_layout.align(), new_layout.align());
            unsafe { self.alloc.grow(self.ptr.cast(), old_layout, new_layout) }
        } else {
            debug_assert!(new_layout.size() > 0);
            self.alloc.allocate(new_layout)
        }?
        .cast();

        self.ptr = new_ptr;
        self.cap = new_cap;

        Ok(())
    }
}

impl<T, A: Allocator> Drop for ResizableArrayMemory<T, A> {
    fn drop(&mut self) {
        let layout = unsafe { Layout::array::<T>(self.cap()).unwrap_unchecked() };
        // SAFETY: even if T is zst Allocator and ptr is dangling - alloc knows how to handle that.
        unsafe { self.alloc.deallocate(self.ptr.cast(), layout) }
    }
}

impl<T, A: Allocator + Default> Default for ResizableArrayMemory<T, A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(A::default())
    }
}

impl<T, A: Allocator> From<A> for ResizableArrayMemory<T, A> {
    #[inline(always)]
    fn from(value: A) -> Self {
        Self::new_in(value)
    }
}

// SAFETY: ResizableArrayMemory owns both T and A.
unsafe impl<T: Send, A: Allocator + Send> Send for ResizableArrayMemory<T, A> {}

// SAFETY: ResizableArrayMemory owns both T and A.
unsafe impl<T: Sync, A: Allocator + Sync> Sync for ResizableArrayMemory<T, A> {}

#[expect(type_alias_bounds)]
pub type ResizableArray<T, A: Allocator> = Array<T, ResizableArrayMemory<T, A>>;

const _: () = {
    let this = size_of::<ResizableArray<u8, alloc::Global>>();
    let std = size_of::<std::vec::Vec<u8>>();
    assert!(this <= std)
};

impl<T, A: Allocator> ResizableArray<T, A> {
    /// SAFETY: if `T` is a ZST `ptr` must be dangling. otherwise:
    ///   - `ptr` must have been allocated with the allocator `A`.
    ///   - `ptr` must point to memory with a size of at least `size_of::<T>() * cap` bytes.
    ///   - `len` must be less than or equal to `cap`.
    #[inline]
    pub unsafe fn from_raw_parts_in(ptr: *mut T, len: usize, cap: usize, alloc: A) -> Self {
        Self {
            // SAFETY: by the safety requirements, `ptr` is either dangling or pointing to a valid
            // memory allocation, allocated with `A`.
            mem: unsafe { ResizableArrayMemory::from_raw_parts_in(ptr, cap, alloc) },
            len,
            _ty: PhantomData,
        }
    }

    pub fn leak_with_alloc<'a>(self) -> (&'a mut [T], A) {
        let mut this = ManuallyDrop::new(self);
        unsafe {
            (
                mem::transmute(this.as_mut_slice()),
                ptr::read(this.mem.allocator()),
            )
        }
    }

    pub fn into_boxed_slice_assume_full(self) -> Box<[T], A> {
        assert_eq!(self.len(), self.cap());
        let mut this = ManuallyDrop::new(self);
        unsafe { Box::from_raw_in(this.as_mut_slice(), ptr::read(this.mem.allocator())) }
    }

    // pub fn into_boxed_slice_maybe_shrink(self) -> boxed::Box<[T], A> { todo!() }
}

// ----
// fixed

#[repr(transparent)]
pub struct FixedArrayMemory<T, const N: usize> {
    data: MaybeUninit<[T; N]>,
}

unsafe impl<T, const N: usize> ArrayMemory<T> for FixedArrayMemory<T, N> {
    #[inline]
    fn as_ptr(&self) -> *mut T {
        self.data.as_ptr() as *mut T
    }

    #[inline]
    fn cap(&self) -> usize {
        N
    }

    #[inline]
    unsafe fn grow(&mut self, _new_cap: usize) -> Result<(), AllocError> {
        Err(AllocError)
    }
}

impl<T, const N: usize> Default for FixedArrayMemory<T, N> {
    #[inline]
    fn default() -> Self {
        Self {
            data: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }
}

pub type FixedArray<T, const N: usize> = Array<T, FixedArrayMemory<T, N>>;

const _: () = {
    // NOTE: max len of string + length
    assert!(size_of::<FixedArray<u8, 16>>() == 16 + size_of::<usize>());
};

impl<T: Clone, const N: usize> Clone for FixedArray<T, N> {
    fn clone(&self) -> Self {
        let mut ret = Self::default();
        // NOTE: ok to unwrap. both array's capacities are equal.
        try_array_clone_slow(self, &mut ret).unwrap();
        ret
    }
}

// NOTE: you can't implement Copy for FixedArray
//   even though that should be legal for T: Copy, because Drop impls cannot be specialized (meaning
//   you can't impl drop for resizable and spillable array but not for fixed array).

// ----
// spillable
//   fixed on stack -> spill to resizable on heap

pub enum SpillableArrayMemory<T, const N: usize, A: Allocator> {
    // NOTE: Fixed variant holds onto A, it'll be passed to ResizableMemory on spill.
    Fixed((FixedArrayMemory<T, N>, A)),
    Resizable(ResizableArrayMemory<T, A>),
    // NOTE: Transitional variant is used as a temp value while transitioning between
    // fixed<->resizable state.
    //   maybe there's a better way?
    Transitional,
}

impl<T, const N: usize, A: Allocator> SpillableArrayMemory<T, N, A> {
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        Self::Fixed((FixedArrayMemory::default(), alloc))
    }

    #[inline]
    pub fn allocator(&self) -> &A {
        match self {
            Self::Fixed((_, alloc)) => alloc,
            Self::Resizable(resizable) => resizable.allocator(),
            Self::Transitional => unreachable!(),
        }
    }

    pub fn is_spilled(&self) -> bool {
        match self {
            Self::Fixed(..) => false,
            Self::Resizable(..) => true,
            Self::Transitional => unreachable!(),
        }
    }
}

unsafe impl<T, const N: usize, A: Allocator> ArrayMemory<T> for SpillableArrayMemory<T, N, A> {
    #[inline]
    fn as_ptr(&self) -> *mut T {
        match self {
            Self::Fixed((fixed, _)) => ArrayMemory::as_ptr(fixed),
            Self::Resizable(resizable) => ArrayMemory::as_ptr(resizable),
            Self::Transitional => unreachable!(),
        }
    }

    #[inline]
    fn cap(&self) -> usize {
        match self {
            Self::Fixed((fixed, _)) => ArrayMemory::cap(fixed),
            Self::Resizable(resizable) => ArrayMemory::cap(resizable),
            Self::Transitional => unreachable!(),
        }
    }

    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), AllocError> {
        // NOTE: this assert here just for documentation purposes.
        debug_assert!(new_cap > self.cap());

        match self {
            Self::Fixed(..) => {
                let Self::Fixed((fixed, alloc)) = mem::replace(self, Self::Transitional) else {
                    unreachable!();
                };
                let mut resizable = ResizableArrayMemory::<T, A>::new_in(alloc);
                unsafe {
                    resizable.grow(new_cap)?;
                    resizable
                        .as_ptr()
                        .copy_from_nonoverlapping(fixed.data.as_ptr().cast(), N)
                };
                *self = Self::Resizable(resizable);
                Ok(())
            }
            Self::Resizable(resizable) => unsafe { ArrayMemory::grow(resizable, new_cap) },
            Self::Transitional => unreachable!(),
        }
    }
}

impl<T, const N: usize, A: Allocator + Default> Default for SpillableArrayMemory<T, N, A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(A::default())
    }
}

impl<T, const N: usize, A: Allocator> From<A> for SpillableArrayMemory<T, N, A> {
    #[inline(always)]
    fn from(value: A) -> Self {
        Self::new_in(value)
    }
}

#[expect(type_alias_bounds)]
pub type SpillableArray<T, const N: usize, A: Allocator> = Array<T, SpillableArrayMemory<T, N, A>>;

impl<T, const N: usize, A: Allocator> SpillableArray<T, N, A> {
    pub fn is_spilled(&self) -> bool {
        self.mem.is_spilled()
    }
}

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::{eek, this_is_fine};

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

        #[track_caller]
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

        #[track_caller]
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

        #[inline]
        pub fn extend_from_array<const C: usize>(&mut self, array: [T; C]) {
            this_is_fine(self.try_extend_from_array(array))
        }
    }

    // :TryCloneIn
    impl<T: Clone, A: Allocator + Clone> Clone for ResizableArray<T, A> {
        fn clone(&self) -> Self {
            let mut ret = Self::new_in(self.mem.allocator().clone());
            this_is_fine(try_array_clone_slow(self, &mut ret));
            ret
        }
    }

    // :TryCloneIn
    impl<T: Clone, const N: usize, A: Allocator + Clone> Clone for SpillableArray<T, N, A> {
        fn clone(&self) -> Self {
            let mut ret = Self::new_in(self.mem.allocator().clone());
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
        let mut this = ResizableArray::new_in(alloc::Global);
        this.push(8);
        this.push(16);
        assert_eq!(this, [8, 16]);
    }

    #[test]
    fn test_extend_from_array() {
        let mut this = ResizableArray::new_in(alloc::Global);
        this.extend_from_array([8, 16]);
        this.extend_from_array([32]);
        assert_eq!(this, [8, 16, 32]);
    }

    #[test]
    fn test_pop() {
        let mut this = ResizableArray::new_in(alloc::Global);
        this.extend_from_array([8, 16]);
        assert_eq!(this.pop(), Some(16));
        assert_eq!(this.pop(), Some(8));
        assert_eq!(this.pop(), None);
        assert_eq!(this, []);
    }

    #[test]
    fn test_remove_ordered() {
        let mut this = ResizableArray::<i32, _>::new_in(alloc::Global);
        this.extend_from_array([1, 2, 3]);
        assert_eq!(this.remove_ordered(0), Some(1));
        assert_eq!(this.remove_ordered(2), None);

        let mut this = ResizableArray::<i32, _>::new_in(alloc::Global);
        assert!(this.remove_ordered(0).is_none());
    }

    #[test]
    fn test_index() {
        let mut this = ResizableArray::new_in(alloc::Global);
        this.extend_from_array([8, 16]);
        assert_eq!(this[0], 8);
        assert_eq!(this[1], 16);
    }

    #[test]
    fn test_drain() {
        let mut a = ResizableArray::new_in(alloc::Global);
        a.extend_from_array([8, 16]);
        let mut b = ResizableArray::new_in(alloc::Global);
        b.extend_from_iter(a.drain(..));
        assert_eq!(a, []);
        assert_eq!(b, [8, 16]);
    }

    #[test]
    fn test_retain() {
        let mut this = ResizableArray::new_in(alloc::Global);
        this.extend_from_array([1, 2, 3, 4]);
        this.retain(|&x| x % 2 == 0);
        assert_eq!(this, [2, 4]);
    }

    #[test]
    fn test_retain_predicate_order() {
        for to_keep in [true, false] {
            let mut number_of_executions = 0;
            let mut this = ResizableArray::new_in(alloc::Global);
            this.extend_from_array([1, 2, 3, 4]);
            let mut next_expected = 1;
            this.retain(|&x| {
                assert_eq!(next_expected, x);
                next_expected += 1;
                number_of_executions += 1;
                to_keep
            });
            assert_eq!(number_of_executions, 4);
        }
    }

    #[test]
    fn test_insert() {
        let mut this = ResizableArray::new_in(alloc::Global);
        this.extend_from_array([16]);
        this.insert(0, 8);
        assert_eq!(this, [8, 16]);
    }

    #[test]
    fn test_uses_provided_allocator() {
        let mut temp_data = [0; 1000];
        let temp = alloc::TempAllocator::new(&mut temp_data, &alloc::Global, None);

        let mut this = ResizableArray::<u32, _>::new_in(&temp);

        this.reserve_amortized(42);
        assert_eq!(temp.make_checkpoint().occupied, 42 * size_of::<u32>());
    }

    #[test]
    fn test_matches_std_reserve_amortized_strategy() {
        {
            let mut this = ResizableArray::<u32, _>::new_in(alloc::Global);
            let mut std: std::vec::Vec<u32> = std::vec::Vec::new();

            this.reserve_amortized(9);
            std.reserve(9);
            assert_eq!(this.cap(), std.capacity());
        }

        {
            let mut this = ResizableArray::<u32, _>::new_in(alloc::Global);
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
        let temp = alloc::TempAllocator::new(&mut temp_data, &alloc::Global, None);

        #[derive(Clone, Copy)]
        struct ZST;

        let mut this = ResizableArray::<ZST, _>::new_in(&temp);
        let mut std = std::vec::Vec::<ZST>::new();

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
    // fixed resizable memory

    #[test]
    fn test_fixed_spill() {
        let mut temp_data = [0; 1000];
        let temp = alloc::TempAllocator::new(&mut temp_data, &alloc::Global, None);

        let mut this = SpillableArray::<u32, 2, _>::new_in(&temp);
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
                x: ResizableArray::new_in(alloc::Global),
                y: ResizableArray::new_in(alloc::Global),
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

        let mut v = ResizableArray::new_in(alloc::Global);
        v.extend_from_array([
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

        let mut v = ResizableArray::new_in(alloc::Global);
        v.extend_from_array([Elem(1), Elem(2), Elem(3), Elem(4), Elem(5)]);

        assert_eq!(DROPS.get(), 0);
        v.truncate(3);
        assert_eq!(DROPS.get(), 2);
        v.truncate(0);
        assert_eq!(DROPS.get(), 5);
    }

    #[test]
    fn test_std_clone() {
        let v = ResizableArray::<i32, _>::new_in(alloc::Global);
        let mut w = ResizableArray::<i32, _>::new_in(alloc::Global);
        w.extend_from_array([1, 2, 3]);

        assert_eq!(v, v.clone());

        let z = w.clone();
        assert_eq!(w, z);
        // they should be disjoint in memory.
        assert!(w.as_ptr() != z.as_ptr())
    }

    #[test]
    fn test_into_boxed_slice_assume_full() {
        let mut xs = ResizableArray::new_in(alloc::Global);
        xs.reserve_exact(3);
        xs.extend_from_array([1, 2, 3]);
        let ys = xs.into_boxed_slice_assume_full();
        assert_eq!(&*ys, [1, 2, 3]);
    }
}
