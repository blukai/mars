use core::error::Error;
use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::ptr::{self, NonNull};
use core::slice::{self, SliceIndex};
use core::{fmt, ops};
use std::io;

use alloc::{AllocError, Allocator, Global, Layout};
use scopeguard::ScopeGuard;

use crate::try_range_from_bounds;

// NOTE(blukai): alloc::handle_alloc_error wants layout arg, but it doesn't really do anything
// useful with it and it's annoying to jiggle it around.
#[cfg(not(no_global_oom_handling))]
#[cold]
fn eek(_err: AllocError) -> ! {
    panic!("allocation failed");
}

#[cfg(not(no_global_oom_handling))]
#[inline]
fn this_is_fine<T>(result: Result<T, AllocError>) -> T {
    match result {
        Ok(ok) => ok,
        Err(err) => eek(err),
    }
}

pub unsafe trait Memory<T> {
    fn as_ptr(&self) -> *const T;
    fn as_mut_ptr(&mut self) -> *mut T;
    fn cap(&self) -> usize;
    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), AllocError>;
    // TODO: Memory will also need srink method.
}

pub struct GrowableMemory<T, A: Allocator> {
    ptr: NonNull<T>,
    cap: usize,
    alloc: A,
}

impl<T, A: Allocator> GrowableMemory<T, A> {
    #[inline]
    pub const fn new_in(alloc: A) -> Self {
        Self {
            ptr: NonNull::dangling(),
            cap: 0,
            alloc,
        }
    }

    #[inline]
    pub fn try_new_with_cap_in(cap: usize, alloc: A) -> Result<Self, AllocError> {
        let mut this = Self::new_in(alloc);
        if cap > 0 {
            unsafe { this.grow(cap)? };
        }
        Ok(this)
    }
}

impl<T, A: Allocator> Drop for GrowableMemory<T, A> {
    fn drop(&mut self) {
        let layout = unsafe { Layout::array::<T>(self.cap).unwrap_unchecked() };
        // SAFETY: even if T is zst Allocator and ptr is dangling - alloc knows how to handle that.
        unsafe { self.alloc.deallocate(self.ptr.cast(), layout) }
    }
}

unsafe impl<T, A: Allocator> Memory<T> for GrowableMemory<T, A> {
    #[inline]
    fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
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

impl<T, A: Allocator + Default> Default for GrowableMemory<T, A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(A::default())
    }
}

#[cfg(not(no_global_oom_handling))]
mod oom_growable_memory {
    use super::*;

    impl<T, A: Allocator> GrowableMemory<T, A> {
        #[inline]
        pub fn new_with_cap_in(cap: usize, alloc: A) -> Self {
            this_is_fine(Self::try_new_with_cap_in(cap, alloc))
        }
    }
}

#[repr(transparent)]
pub struct FixedMemory<T, const N: usize> {
    data: MaybeUninit<[T; N]>,
}

impl<T, const N: usize> FixedMemory<T, N> {
    #[inline]
    const fn empty() -> Self {
        Self {
            data: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }

    #[inline]
    pub const fn from_array(array: [T; N]) -> Self {
        Self {
            data: MaybeUninit::new(array),
        }
    }
}

unsafe impl<T, const N: usize> Memory<T> for FixedMemory<T, N> {
    #[inline]
    fn as_ptr(&self) -> *const T {
        self.data.as_ptr().cast()
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
        self.data.as_mut_ptr().cast()
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

impl<T, const N: usize> Default for FixedMemory<T, N> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

enum Either<L, R> {
    Left(L),
    Right(R),
}

pub struct FixedGrowableMemory<T, const N: usize, A: Allocator> {
    mem: Either<FixedMemory<T, N>, GrowableMemory<T, A>>,
    alloc: Option<A>,
}

impl<T, const N: usize, A: Allocator> FixedGrowableMemory<T, N, A> {
    #[inline]
    pub const fn from_array_in(array: [T; N], alloc: A) -> Self {
        Self {
            mem: Either::Left(FixedMemory::from_array(array)),
            alloc: Some(alloc),
        }
    }

    #[inline]
    pub const fn new_in(alloc: A) -> Self {
        Self {
            mem: Either::Left(FixedMemory::empty()),
            alloc: Some(alloc),
        }
    }
}

unsafe impl<T, const N: usize, A: Allocator> Memory<T> for FixedGrowableMemory<T, N, A> {
    #[inline]
    fn as_ptr(&self) -> *const T {
        match self.mem {
            Either::Left(ref fixed) => Memory::as_ptr(fixed),
            Either::Right(ref growable) => Memory::as_ptr(growable),
        }
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
        match self.mem {
            Either::Left(ref mut fixed) => Memory::as_mut_ptr(fixed),
            Either::Right(ref mut growable) => Memory::as_mut_ptr(growable),
        }
    }

    #[inline]
    fn cap(&self) -> usize {
        match self.mem {
            Either::Left(ref fixed) => Memory::cap(fixed),
            Either::Right(ref growable) => Memory::cap(growable),
        }
    }

    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), AllocError> {
        match self.mem {
            Either::Left(ref mut fixed) => {
                let alloc = self.alloc.take().expect("unyoinked alloc");
                let mut growable = GrowableMemory::<T, A>::try_new_with_cap_in(new_cap, alloc)?;
                unsafe {
                    growable
                        .as_mut_ptr()
                        .copy_from_nonoverlapping(fixed.data.as_ptr().cast(), N)
                };
                self.mem = Either::Right(growable);
                assert!(matches!(self.mem, Either::Right(GrowableMemory { .. })));
                Ok(())
            }
            Either::Right(ref mut growable) => unsafe { Memory::grow(growable, new_cap) },
        }
    }
}

pub struct PushError<T> {
    pub error: AllocError,
    pub value: T,
}

impl<T> Error for PushError<T> {}

impl<T> fmt::Debug for PushError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.error, f)
    }
}

impl<T> fmt::Display for PushError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

pub struct Vec<T, M: Memory<T>> {
    mem: M,
    len: usize,
    _ty: PhantomData<T>,
}

const _: () = {
    let this = size_of::<Vec<u8, GrowableMemory<u8, Global>>>();
    let std = size_of::<std::vec::Vec<u8>>();
    assert!(this <= std)
};

impl<T, M: Memory<T>> Vec<T, M> {
    #[inline]
    const fn is_zst() -> bool {
        size_of::<T>() == 0
    }

    #[inline]
    pub const fn new_in(mem: M) -> Self {
        Self {
            mem,
            len: 0,
            _ty: PhantomData,
        }
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
    pub fn as_ptr(&self) -> *const T {
        self.mem.as_ptr()
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.mem.as_mut_ptr()
    }

    /// SAFETY: `new_cap` must be greater then the current capacity.
    #[inline]
    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), AllocError> {
        unsafe { self.mem.grow(new_cap) }
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
        unsafe { self.grow(required_cap) }
    }

    pub fn try_reserve_amortized(&mut self, additional: usize) -> Result<(), AllocError> {
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
        unsafe { self.grow(amortized_cap) }
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
        if let Err(error) = self.try_reserve_amortized(1) {
            return Err(PushError { error, value });
        }
        unsafe { self.push_within_cap_unchecked(value) };
        Ok(())
    }

    /// removes the last item and returns it, or `None` if it is empty.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        unsafe {
            self.len -= 1;
            Some(self.as_ptr().add(self.len()).read())
        }
    }

    /// shortens the vector, setting the length to `len` and drops the removed values.
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

    /// removes all items, as no effect on the allocated capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
        debug_assert!(self.is_empty());
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
    /// example), the vector may have lost and leaked items arbitrarily, including items outside
    /// the range.
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, M>
    where
        R: ops::RangeBounds<usize>,
    {
        let len = self.len();
        // TODO(blukai): maybe non-paniching variant of drain (try_drain?).
        let ops::Range { start, end } = try_range_from_bounds(range, ..len).expect("invalid range");
        // NOTE: when Drain drops the remaining tail of the vec is copied back to cover the hole.
        unsafe {
            // NOTE: set len to start, to be safe in case Drain's leakage.
            self.len = start;
            let iter =
                slice::from_raw_parts_mut(self.as_mut_ptr().add(start), end - start).iter_mut();
            Drain {
                iter,
                vec: NonNull::from(self),
                tail_start: end,
                tail_len: len - end,
            }
        }
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
    pub fn try_extend_from_slice_copy(&mut self, other: &[T]) -> Result<(), AllocError>
    where
        T: Copy,
    {
        let count = other.len();
        self.try_reserve_amortized(count)?;
        unsafe {
            self.as_mut_ptr()
                .add(self.len())
                .copy_from_nonoverlapping(other.as_ptr(), count)
        };
        self.len += count;
        Ok(())
    }

    // ----
    // construct from

    pub fn try_from_iter_in<I: Iterator<Item = T>>(iter: I, mem: M) -> Result<Self, AllocError> {
        let mut this = Self::new_in(mem);
        this.try_extend_from_iter(iter)?;
        Ok(this)
    }

    /// use [`Self::try_from_iter_in`] for items that cannot be copied.
    pub fn try_from_slice_copy_in(slice: &[T], mem: M) -> Result<Self, AllocError>
    where
        T: Copy,
    {
        let mut this = Self::new_in(mem);
        this.try_extend_from_slice_copy(slice)?;
        Ok(this)
    }

    pub fn try_from_array_in<const N: usize>(array: [T; N], mem: M) -> Result<Self, AllocError> {
        // NOTE: this is somewhat of an untangled version of what std does
        //   but not quite; although technically mostly yes...
        //
        //   std puts array into Box first, deconstructs it into raw ptr and alloc, and then
        //   constructs Vec from raw parts.
        //
        //   std's Box::new method is relying on not-publicly-available lang exchange malloc
        //   intrinsic that supposedly can put array onto the heap right away omitting stack.
        //   we can't do exactly copy that.
        let mut this = Self::new_in(mem);
        this.try_reserve_exact(array.len())?;
        unsafe { this.as_mut_ptr().cast::<[T; N]>().write(array) };
        this.len = N;
        Ok(this)
    }
}

impl<T, M: Memory<T>> Drop for Vec<T, M> {
    fn drop(&mut self) {
        unsafe { ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len()).drop_in_place() };
        // NOTE: mem will drop itself.
    }
}

impl<T, M: Memory<T>> ops::Deref for Vec<T, M> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl<T, M: Memory<T>> ops::DerefMut for Vec<T, M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

impl<T, M: Memory<T>, I: SliceIndex<[T]>> ops::Index<I> for Vec<T, M> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        ops::Index::index(&**self, index)
    }
}

impl<T, M: Memory<T>, I: SliceIndex<[T]>> ops::IndexMut<I> for Vec<T, M> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        ops::IndexMut::index_mut(&mut **self, index)
    }
}

impl<T: fmt::Debug, M: Memory<T>> fmt::Debug for Vec<T, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T, M: Memory<T> + Default> Default for Vec<T, M> {
    #[inline]
    fn default() -> Self {
        Self::new_in(M::default())
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

            #[inline]
            fn ne(&self, other: &$rhs) -> bool { self[..] != other[..] }
        }
    }
}

impl_partial_eq! { [M1: Memory<T>, M2: Memory<U>] Vec<T, M1>, Vec<U, M2> }

impl_partial_eq! { [M: Memory<T>, const C: usize] Vec<T, M>, &[U; C] }
impl_partial_eq! { [M: Memory<T>, const C: usize] Vec<T, M>, [U; C] }
impl_partial_eq! { [M: Memory<T>] Vec<T, M>, &[U] }
impl_partial_eq! { [M: Memory<T>] Vec<T, M>, [U] }
impl_partial_eq! { [M: Memory<T>] Vec<T, M>, std::vec::Vec<U> }

impl_partial_eq! { [M: Memory<U>, const C: usize] &[T; C], Vec<U, M> }
impl_partial_eq! { [M: Memory<U>, const C: usize] [T; C], Vec<U, M> }
impl_partial_eq! { [M: Memory<U>] &[T], Vec<U, M> }
impl_partial_eq! { [M: Memory<U>] [T], Vec<U, M> }
impl_partial_eq! { [M: Memory<U>] std::vec::Vec<T>, Vec<U, M> }

/// Write is implemented for `Vec<u8>` by appending to the vector.
/// The vector will grow as needed.
impl<M: Memory<u8>> io::Write for Vec<u8, M> {
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

pub struct Drain<'v, T: 'v, M: Memory<T> + 'v> {
    iter: slice::IterMut<'v, T>,
    vec: NonNull<Vec<T, M>>,
    tail_start: usize,
    tail_len: usize,
}

impl<T, M: Memory<T>> Drop for Drain<'_, T, M> {
    fn drop(&mut self) {
        // QUOTE:
        // > moves back the un-`Drain`ed items to restore the original `Vec`.
        // > ensure items are moved back into their appropriate places, even when drop_in_place panics
        let _guard = ScopeGuard::new(|| {
            if self.tail_len == 0 {
                return;
            }

            unsafe {
                let vec = self.vec.as_mut();
                let start = vec.len();
                let tail = self.tail_start;
                if tail != start {
                    let src = vec.as_ptr().add(tail);
                    let dst = vec.as_mut_ptr().add(start);
                    ptr::copy(src, dst, self.tail_len);
                }
                vec.len = start + self.tail_len;
            }
        });

        let iter = mem::take(&mut self.iter);
        // SAFETY: we own these values so we destroy them.
        unsafe { ptr::drop_in_place(iter.into_slice()) };
    }
}

impl<T, M: Memory<T>> Iterator for Drain<'_, T, M> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next().map(|it| unsafe { ptr::read(it) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, M: Memory<T>> DoubleEndedIterator for Drain<'_, T, M> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back().map(|it| unsafe { ptr::read(it) })
    }
}

impl<T, M: Memory<T>> ExactSizeIterator for Drain<'_, T, M> {}

#[cfg(not(no_global_oom_handling))]
mod oom_vec {
    use super::*;

    impl<T, M: Memory<T>> Vec<T, M> {
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
            if let Err(PushError { error, .. }) = self.try_push(value) {
                eek(error)
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
        // construct from

        #[inline]
        pub fn from_iter_in<I: Iterator<Item = T>>(iter: I, mem: M) -> Self {
            this_is_fine(Self::try_from_iter_in(iter, mem))
        }

        #[inline]
        pub fn from_slice_copy_in(slice: &[T], mem: M) -> Self
        where
            T: Copy,
        {
            this_is_fine(Self::try_from_slice_copy_in(slice, mem))
        }

        #[inline]
        pub fn from_array_in<const N: usize>(array: [T; N], mem: M) -> Self {
            this_is_fine(Self::try_from_array_in(array, mem))
        }
    }
}

#[expect(type_alias_bounds)]
pub type GrowableVec<T, A: Allocator> = Vec<T, GrowableMemory<T, A>>;

pub type FixedVec<T, const N: usize> = Vec<T, FixedMemory<T, N>>;

#[expect(type_alias_bounds)]
pub type FixedGrowableVec<T, const N: usize, A: Allocator> = Vec<T, FixedGrowableMemory<T, N, A>>;

impl<T, const N: usize, A: Allocator> FixedGrowableVec<T, N, A> {
    #[inline]
    pub const fn is_spilled(&self) -> bool {
        match self.mem.mem {
            Either::Right(GrowableMemory { .. }) => true,
            Either::Left(FixedMemory { .. }) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use core::iter;

    use crate::{
        testing::{assert_matches, struct_with_counted_drop},
        vec::*,
    };

    #[test]
    fn test_push() {
        let mut this = Vec::<u32, _>::new_in(GrowableMemory::new_in(Global));
        this.push(8);
        this.push(16);
        assert_eq!(this, [8, 16]);
    }

    #[test]
    fn test_pop() {
        let mut this = Vec::<u32, _>::from_array_in([8, 16], GrowableMemory::new_in(Global));
        assert_eq!(this.pop(), Some(16));
        assert_eq!(this.pop(), Some(8));
        assert_eq!(this.pop(), None);
        assert_eq!(this, []);
    }

    #[test]
    fn test_index() {
        let this = Vec::<u32, _>::from_array_in([8, 16], GrowableMemory::new_in(Global));
        assert_eq!(this[0], 8);
        assert_eq!(this[1], 16);
    }

    #[test]
    fn test_drain() {
        let mut a = Vec::from_array_in([8, 16], GrowableMemory::new_in(Global));
        let b = Vec::from_iter_in(a.drain(..), GrowableMemory::new_in(Global));
        assert_eq!(a, []);
        assert_eq!(b, [8, 16]);
    }

    #[test]
    fn test_uses_provided_allocator() {
        let mut temp_data = [0; 1000];
        let temp = alloc::TempAllocator::new(&mut temp_data);

        let mut this: Vec<u32, _> = Vec::new_in(GrowableMemory::new_in(&temp));

        this.try_reserve_amortized(42).unwrap();
        assert_eq!(temp.get_checkpoint().occupied, 42 * size_of::<u32>());
    }

    #[test]
    fn test_matches_std_reserve_amortized_strategy() {
        {
            let mut this: Vec<u32, _> = Vec::new_in(GrowableMemory::new_in(Global));
            let mut std: std::vec::Vec<u32> = std::vec::Vec::new();

            this.try_reserve_amortized(9).unwrap();
            std.reserve(9);
            assert_eq!(this.cap(), std.capacity());
        }

        {
            let mut this: Vec<u32, _> = Vec::new_in(GrowableMemory::new_in(Global));
            let mut std: std::vec::Vec<u32> = std::vec::Vec::new();

            this.try_reserve_amortized(8).unwrap();
            std.reserve(8);
            assert_eq!(this.cap(), std.capacity());

            this.try_reserve_amortized(90).unwrap();
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

        let mut this: Vec<ZST, _> = Vec::new_in(GrowableMemory::new_in(&temp));
        let mut std: std::vec::Vec<ZST> = std::vec::Vec::new();

        this.extend_from_iter(iter::repeat_n(ZST, 101));
        assert_matches!(
            this.try_reserve_amortized(usize::MAX - 100),
            Err(AllocError)
        );

        std.extend(iter::repeat_n(ZST, 101));
        assert_matches!(
            std.try_reserve(usize::MAX - 100),
            Err(std::collections::TryReserveError { .. })
        );

        // NOTE: ensure that vec did attempt to allocate memory.
        assert_eq!(temp.get_high_water_mark(), 0);
    }

    // ----
    // NOTE: tests that start with std_test_ are stolen from std.

    #[test]
    fn std_test_double_drop() {
        struct DropCounter<'a> {
            count: &'a mut u32,
        }

        impl Drop for DropCounter<'_> {
            fn drop(&mut self) {
                *self.count += 1;
            }
        }

        struct TwoVec<T, M: Memory<T>> {
            x: Vec<T, M>,
            y: Vec<T, M>,
        }

        let (mut count_x, mut count_y) = (0, 0);
        {
            let mut tv = TwoVec {
                x: Vec::new_in(GrowableMemory::new_in(Global)),
                y: Vec::new_in(GrowableMemory::new_in(Global)),
            };
            tv.x.push(DropCounter {
                count: &mut count_x,
            });
            tv.y.push(DropCounter {
                count: &mut count_y,
            });

            // If Vec had a drop flag, here is where it would be zeroed.
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
    fn std_test_drain_leak() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        struct_with_counted_drop!(D(u32, bool), DROPS => |this: &D| if this.1 { panic!("panic in `drop`"); });

        let mut v = Vec::from_array_in(
            [
                D(0, false),
                D(1, false),
                D(2, false),
                D(3, false),
                D(4, true),
                D(5, false),
                D(6, false),
            ],
            GrowableMemory::new_in(Global),
        );

        catch_unwind(AssertUnwindSafe(|| {
            v.drain(2..=5);
        }))
        .ok();

        assert_eq!(DROPS.get(), 4);
        assert_eq!(v, [D(0, false), D(1, false), D(6, false)]);
    }

    #[test]
    fn std_test_vec_truncate_drop() {
        struct_with_counted_drop!(Elem(i32), DROPS);

        let mut v = Vec::from_array_in(
            [Elem(1), Elem(2), Elem(3), Elem(4), Elem(5)],
            GrowableMemory::new_in(Global),
        );

        assert_eq!(DROPS.get(), 0);
        v.truncate(3);
        assert_eq!(DROPS.get(), 2);
        v.truncate(0);
        assert_eq!(DROPS.get(), 5);
    }

    // ----
    // fixed memory

    #[test]
    fn test_fixed_push() {
        let mut this = FixedVec::<u32, 2>::default();
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

        let mut this = FixedGrowableVec::new_in(FixedGrowableMemory::<u32, 2, _>::new_in(&temp));
        assert!(this.try_push(8).is_ok());
        assert!(this.try_push(16).is_ok());
        assert!(!this.is_spilled());
        assert!(this.try_push(32).is_ok());
        assert!(this.is_spilled());
        assert_eq!(this, [8, 16, 32]);
    }
}
