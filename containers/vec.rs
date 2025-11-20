use core::error::Error;
use core::mem::{self, MaybeUninit};
use core::ptr::{self, NonNull};
use core::slice::{self, SliceIndex};
use core::{fmt, iter, ops};
use std::io;

use alloc::{Allocator, Global, Layout};
use scopeguard::ScopeGuard;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReserveError {
    /// capacity cannot exceed `isize::MAX`.
    CapacityOverflow,
    AllocError {
        // NOTE: layout is included because `std::alloc::handle_alloc_error` wants it.
        layout: Layout,
    },
}

impl Error for ReserveError {}

impl fmt::Display for ReserveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapacityOverflow => f.write_str("capacity exceeded `isize::MAX`"),
            Self::AllocError { .. } => f.write_str("memory allocation failed"),
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[cold]
pub fn handle_reserve_error(err: ReserveError) -> ! {
    match err {
        ReserveError::CapacityOverflow => panic!("capacity overflow"),
        ReserveError::AllocError { layout, .. } => alloc::handle_alloc_error(layout),
    }
}

/// a simpler version, a subset of [`std::vec::Vec`] that works with [`Allocator`] trait.
/// api attempts to be (but not always is) compatible with [`std::vec::Vec`].
pub struct Vec<T, A: Allocator = Global> {
    ptr: NonNull<T>,
    cap: usize,
    len: usize,
    alloc: A,
}

impl<T, A: Allocator> Vec<T, A> {
    #[inline]
    const fn is_zst() -> bool {
        size_of::<T>() == 0
    }

    #[inline]
    pub const fn new_in(alloc: A) -> Self {
        Self {
            ptr: NonNull::dangling(),
            cap: 0,
            len: 0,
            alloc,
        }
    }

    /// will always return `usize::MAX` if `T` is zero-sized.
    #[inline]
    pub const fn capacity(&self) -> usize {
        if Self::is_zst() { usize::MAX } else { self.cap }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }

    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr.as_ptr()
    }

    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// SAFETY: `new_cap` must be greater then the current capacity.
    #[inline]
    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), ReserveError> {
        let old_cap = self.capacity();

        // NOTE: this is ensured by the caller.
        debug_assert!(new_cap > old_cap);

        let new_layout = Layout::array::<T>(new_cap).map_err(|_| ReserveError::CapacityOverflow)?;
        let new_ptr = if new_cap > 0 {
            let old_layout = unsafe { Layout::array::<T>(old_cap).unwrap_unchecked() };
            debug_assert_eq!(old_layout.align(), new_layout.align());
            unsafe { self.alloc.grow(self.ptr.cast(), old_layout, new_layout) }
        } else {
            self.alloc.allocate(new_layout)
        }
        .map_err(|_| ReserveError::AllocError { layout: new_layout })?
        .cast();

        self.ptr = new_ptr;
        self.cap = new_cap;

        Ok(())
    }

    /// ensures that the capacity exceeds the length by at least `additional` items.
    ///
    /// # example
    ///
    /// ```
    /// use containers::vec::{Vec, ReserveError};
    ///
    /// let mut v = Vec::new();
    /// v.try_push(1)?;
    /// v.try_reserve(10)?;
    /// assert!(v.capacity() >= 11);
    ///
    /// # Ok::<(), ReserveError>(())
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), ReserveError> {
        let cap = self.capacity();
        let len = self.len();

        if cap - len >= additional {
            return Ok(());
        }

        if Self::is_zst() {
            // NOTE: the capacity is already `usize::MAX` for zsts.
            return Err(ReserveError::CapacityOverflow);
        }

        let required_cap = len
            .checked_add(additional)
            .ok_or(ReserveError::CapacityOverflow)?;

        let amortized_cap = required_cap
            // NOTE: the doubling cannot overflow because `cap <= isize::MAX`.
            //   `Layout::array` upholds this.
            .max(cap * 2)
            .max(min_non_zero_cap(size_of::<T>()));

        // SAFETY: we ensured aboce that `new_cap` must be greater then the current capacity.
        unsafe { self.grow(amortized_cap) }
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        if let Err(err) = self.try_reserve(additional) {
            handle_reserve_error(err);
        }
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), ReserveError> {
        let cap = self.capacity();
        let len = self.len();

        if cap - len >= additional {
            return Ok(());
        }

        if Self::is_zst() {
            return Err(ReserveError::CapacityOverflow);
        }

        let required_cap = len
            .checked_add(additional)
            .ok_or(ReserveError::CapacityOverflow)?;

        // SAFETY: we ensured aboce that `new_cap` must be greater then the current capacity.
        unsafe { self.grow(required_cap) }
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        if let Err(err) = self.try_reserve_exact(additional) {
            handle_reserve_error(err);
        }
    }

    #[inline]
    pub fn try_with_capacity_in(cap: usize, alloc: A) -> Result<Self, ReserveError> {
        let mut this = Self::new_in(alloc);
        this.try_reserve_exact(cap)?;
        Ok(this)
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn with_capacity_in(cap: usize, alloc: A) -> Self {
        match Self::try_with_capacity_in(cap, alloc) {
            Ok(this) => this,
            Err(err) => handle_reserve_error(err),
        }
    }

    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        // SAFETY: the memory between `self.len` and `self.capacity` is guaranteed to be allocated
        // and valid, but uninitialized.
        unsafe {
            let ptr = self.as_mut_ptr().add(self.len).cast::<MaybeUninit<T>>();
            slice::from_raw_parts_mut(ptr, self.capacity() - self.len)
        }
    }

    /// SAFETY: new_len must be less than or equal to capacity.
    /// the items at old_len..new_len must be initialized.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());
        self.len = new_len;
    }

    /// SAFETY: the length must be less than the capacity.
    #[inline]
    unsafe fn push_within_capacity_unchecked(&mut self, value: T) {
        let spare = self.spare_capacity_mut();
        // SAFETY: by the safety requirements, `spare` is non-empty.
        unsafe { spare.get_unchecked_mut(0) }.write(value);
        self.len += 1;
    }

    #[inline]
    pub fn push_within_capacity(&mut self, value: T) -> Result<(), T> {
        if self.len() < self.capacity() {
            unsafe { self.push_within_capacity_unchecked(value) };
            Ok(())
        } else {
            Err(value)
        }
    }

    // TODO: should there be a custom error for push?
    //   that will contain value so that the caller can get it back?
    #[inline]
    pub fn try_push(&mut self, value: T) -> Result<(), ReserveError> {
        self.try_reserve(1)?;
        unsafe { self.push_within_capacity_unchecked(value) };
        Ok(())
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn push(&mut self, value: T) {
        if let Err(err) = self.try_push(value) {
            handle_reserve_error(err);
        }
    }

    /// removes the last item and returns it, or `None` if it is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        unsafe {
            self.len -= 1;
            Some(ptr::read(self.as_ptr().add(self.len())))
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
            ptr::drop_in_place(to_drop);
        }
    }

    /// removes all items, as no effect on the allocated capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
        debug_assert!(self.is_empty());
    }

    // NOTE: this is failable equivalent of Extend::extend.
    pub fn try_extend_from_iter<I: Iterator<Item = T>>(
        &mut self,
        mut iter: I,
    ) -> Result<(), ReserveError> {
        while let Some(it) = iter.next() {
            let cap = self.capacity();
            let len = self.len();
            if cap == len {
                let (lower, _) = iter.size_hint();
                self.try_reserve(lower.saturating_add(1))?;
            }
            unsafe {
                ptr::write(self.as_mut_ptr().add(len), it);
                self.len += 1;
            }
        }
        Ok(())
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn extend_from_iter<I: Iterator<Item = T>>(&mut self, iter: I) {
        match self.try_extend_from_iter(iter) {
            Ok(this) => this,
            Err(err) => handle_reserve_error(err),
        }
    }

    // TODO: consider introducing a distinct method for T: Copy.
    //   can this be done? wouldn't specialization be required?
    //
    /// clones all items of slice into the [`Vec`] instance.
    pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), ReserveError>
    where
        T: Clone,
    {
        self.try_extend_from_iter(other.iter().cloned())
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        match self.try_extend_from_slice(other) {
            Ok(this) => this,
            Err(err) => handle_reserve_error(err),
        }
    }

    pub fn try_from_iter_in<I: Iterator<Item = T>>(
        iter: I,
        alloc: A,
    ) -> Result<Self, ReserveError> {
        let mut this = Self::new_in(alloc);
        this.try_extend_from_iter(iter)?;
        Ok(this)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_iter_in<I: Iterator<Item = T>>(iter: I, alloc: A) -> Self {
        match Self::try_from_iter_in(iter, alloc) {
            Ok(this) => this,
            Err(err) => handle_reserve_error(err),
        }
    }

    pub fn try_from_slice_in(slice: &[T], alloc: A) -> Result<Self, ReserveError>
    where
        T: Clone,
    {
        let mut this = Self::new_in(alloc);
        this.try_extend_from_slice(slice)?;
        Ok(this)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_slice_in(slice: &[T], alloc: A) -> Self
    where
        T: Clone,
    {
        match Self::try_from_slice_in(slice, alloc) {
            Ok(this) => this,
            Err(err) => handle_reserve_error(err),
        }
    }

    pub fn try_from_array_in<const N: usize>(
        array: [T; N],
        alloc: A,
    ) -> Result<Self, ReserveError> {
        // NOTE: this is somewhat of an untangled version of what std does
        //   but not quite; although technically mostly yes...
        //
        //   std puts array into Box first, deconstructs it into raw ptr and alloc, and then
        //   constructs Vec from raw parts.
        //
        //   std's Box::new method is relying on not-publicly-available lang exchange malloc
        //   intrinsic that supposedly can put array onto the heap right away omitting stack.
        //   we can't do exactly copy that.
        let mut this = Self::new_in(alloc);
        this.try_reserve_exact(array.len())?;
        unsafe { this.as_mut_ptr().cast::<[T; N]>().write(array) };
        this.len = N;
        Ok(this)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_array_in<const N: usize>(array: [T; N], alloc: A) -> Self {
        match Self::try_from_array_in(array, alloc) {
            Ok(this) => this,
            Err(err) => handle_reserve_error(err),
        }
    }

    /// create with `n` clones of `value`.
    pub fn try_from_item_in(value: T, n: usize, alloc: A) -> Result<Self, ReserveError>
    where
        T: Clone,
    {
        Self::try_from_iter_in(iter::repeat_n(value, n), alloc)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_item_in(value: T, n: usize, alloc: A) -> Self
    where
        T: Clone,
    {
        match Self::try_from_item_in(value, n, alloc) {
            Ok(this) => this,
            Err(err) => handle_reserve_error(err),
        }
    }

    /// resizes the [`Vec`] so that `len` is equal to `new_len`.
    ///
    /// if `new_len` is smaller than `len`, the `Vec` is [`Vec::truncate`]d.
    /// if `new_len` is larger, each new slot is filled with clones of `value`.
    pub fn try_resize(&mut self, new_len: usize, value: T) -> Result<(), ReserveError>
    where
        T: Clone,
    {
        let Some(n) = new_len.checked_sub(self.len()) else {
            self.truncate(new_len);
            return Ok(());
        };
        self.try_extend_from_iter(iter::repeat_n(value, n))
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        if let Err(err) = self.try_resize(new_len, value) {
            handle_reserve_error(err);
        }
    }

    /// resizes the [`Vec`] so that `len` is equal to `new_len`.
    ///
    /// if `new_len` is smaller than `len`, the `Vec` is [`Vec::truncate`]d.
    /// if `new_len` is larger, each new slot is filled with clones of `value`.
    ///
    /// if you'd rather [`Clone`] a given value, use [`Vec::try_resize`]/[`Vec::resize`]. if you want to use the
    /// [`Default`] trait to generate values, you can pass [`Default::default`].
    pub fn try_resize_with<F>(&mut self, new_len: usize, f: F) -> Result<(), ReserveError>
    where
        F: FnMut() -> T,
    {
        let Some(n) = new_len.checked_sub(self.len()) else {
            self.truncate(new_len);
            return Ok(());
        };
        self.try_extend_from_iter(iter::repeat_with(f).take(n))
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> T,
    {
        if let Err(err) = self.try_resize_with(new_len, f) {
            handle_reserve_error(err);
        }
    }

    /// takes ownership of the subslice indicated by the given range without consuming the allocation.
    ///
    /// # panics
    ///
    /// if the range is invalid (`range.start > range.end`) or if end out of bounds
    /// `range.end > self.len()`.
    ///
    /// # leaks
    ///
    /// if [`Drain`] goes out of scope without being dropped (due to [`std::mem::forget`], for example),
    /// the vector may have lost and leaked items arbitrarily, including items outside the
    /// range.
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A>
    where
        R: ops::RangeBounds<usize>,
    {
        let len = self.len();
        let start = match range.start_bound() {
            ops::Bound::Included(&n) => n,
            ops::Bound::Excluded(&n) => n + 1,
            ops::Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            ops::Bound::Included(&n) => n + 1,
            ops::Bound::Excluded(&n) => n,
            ops::Bound::Unbounded => len,
        };
        assert!(start <= end);
        assert!(end <= len);

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
}

impl<T> Vec<T> {
    #[inline]
    pub const fn new() -> Self {
        Self::new_in(Global)
    }

    #[inline]
    pub fn try_with_capacity(cap: usize) -> Result<Self, ReserveError> {
        Self::try_with_capacity_in(cap, Global)
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self::with_capacity_in(cap, Global)
    }

    // NOTE: faillable variant `from_iter` is implemented by `FromIterator` trait.
    #[inline]
    pub fn try_from_iter<I: Iterator<Item = T>>(iter: I) -> Result<Self, ReserveError> {
        Self::try_from_iter_in(iter, Global)
    }

    // NOTE: from_iter is implemented by the FromIterator trait.
    // pub fn from_iter<I: Iterator<Item = T>>(iter: I) -> Self { ... }

    /// creates a new with `n` clones of `value`.
    #[inline]
    pub fn try_from_item(value: T, n: usize) -> Result<Self, ReserveError>
    where
        T: Clone,
    {
        Self::try_from_item_in(value, n, Global)
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn from_item(value: T, n: usize) -> Self
    where
        T: Clone,
    {
        Self::from_item_in(value, n, Global)
    }

    #[inline]
    pub fn try_from_array<const N: usize>(array: [T; N]) -> Result<Self, ReserveError> {
        Self::try_from_array_in(array, Global)
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn from_array<const N: usize>(array: [T; N]) -> Self {
        Self::from_array_in(array, Global)
    }

    #[inline]
    pub fn try_from_slice(slice: &[T]) -> Result<Self, ReserveError>
    where
        T: Clone,
    {
        Self::try_from_slice_in(slice, Global)
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn from_slice(slice: &[T]) -> Self
    where
        T: Clone,
    {
        Self::from_slice_in(slice, Global)
    }
}

impl<T, A: Allocator> Drop for Vec<T, A> {
    fn drop(&mut self) {
        unsafe { ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len()).drop_in_place() };
        let layout = unsafe { Layout::array::<T>(self.capacity()).unwrap_unchecked() };
        // SAFETY: even if T is zst Allocator and ptr is dangling - alloc knows how to handle that.
        unsafe { self.alloc.deallocate(self.ptr.cast(), layout) }
    }
}

impl<T> Default for Vec<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, A: Allocator> ops::Deref for Vec<T, A> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, A: Allocator> ops::DerefMut for Vec<T, A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, I: SliceIndex<[T]>, A> ops::Index<I> for Vec<T, A>
where
    A: Allocator,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        ops::Index::index(&**self, index)
    }
}

impl<T, I: SliceIndex<[T]>, A> ops::IndexMut<I> for Vec<T, A>
where
    A: Allocator,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        ops::IndexMut::index_mut(&mut **self, index)
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

impl_partial_eq! { [A1: Allocator, A2: Allocator] Vec<T, A1>, Vec<U, A2> }
impl_partial_eq! { [A: Allocator] Vec<T, A>, &[U] }
impl_partial_eq! { [A: Allocator] Vec<T, A>, [U] }
impl_partial_eq! { [A: Allocator, const N: usize] Vec<T, A>, [U; N] }
impl_partial_eq! { [A: Allocator] &[T], Vec<U, A> }
impl_partial_eq! { [A: Allocator] [T], Vec<U, A> }
impl_partial_eq! { [A: Allocator, const N: usize] Vec<T, A>, &[U; N] }

impl<'a, T, A> IntoIterator for &'a Vec<T, A>
where
    A: Allocator,
{
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, A: Allocator> IntoIterator for &'a mut Vec<T, A>
where
    A: Allocator,
{
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// impl<T, A: Allocator> IntoIterator for Vec<T, A> {
//     type Item = T;
//     type IntoIter = IntoIter<T, A>;
//
//     fn into_iter(self) -> Self::IntoIter {
//         todo!()
//     }
// }

impl<T, A: Allocator> Extend<T> for Vec<T, A> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.extend_from_iter(iter.into_iter());
    }
}

impl<'a, T: Copy + 'a, A: Allocator> Extend<&'a T> for Vec<T, A> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend_from_iter(iter.into_iter().copied())
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T> FromIterator<T> for Vec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from_iter_in(iter.into_iter(), Global)
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T: Clone, A: Allocator + Clone> Clone for Vec<T, A> {
    #[inline(always)]
    fn clone(&self) -> Self {
        let alloc = self.alloc.clone();
        let mut vec = Vec::with_capacity_in(self.len(), alloc);
        vec.extend_from_slice(self);
        vec
    }

    #[inline(always)]
    fn clone_from(&mut self, other: &Self) {
        // drop anything that will not be overwritten
        self.truncate(other.len());

        // self.len <= other.len due to the truncate above, so the
        // slices here are always in-bounds.
        let (init, tail) = other.split_at(self.len());

        // reuse the contained values' allocations/resources.
        self.clone_from_slice(init);
        self.extend_from_slice(tail);
    }
}

impl<T: fmt::Debug, A: Allocator> fmt::Debug for Vec<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// Write is implemented for `Vec<u8>` by appending to the vector.
/// The vector will grow as needed.
impl<A: Allocator> io::Write for Vec<u8, A> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.try_extend_from_slice(buf).map_err(io::Error::other)?;
        Ok(buf.len())
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[io::IoSlice<'_>]) -> io::Result<usize> {
        let len = bufs.iter().map(|b| b.len()).sum();
        self.try_reserve(len).map_err(io::Error::other)?;
        for buf in bufs {
            // NOTE: ok to ignore because reserve ^ above did succeed.
            _ = self.try_extend_from_slice(buf);
        }
        Ok(len)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.try_extend_from_slice(buf).map_err(io::Error::other)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub struct Drain<'vec, T: 'vec, A: Allocator + 'vec = Global> {
    iter: slice::IterMut<'vec, T>,
    vec: NonNull<Vec<T, A>>,
    tail_start: usize,
    tail_len: usize,
}

impl<T, A: Allocator> Iterator for Drain<'_, T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next().map(|it| unsafe { ptr::read(it) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, A: Allocator> DoubleEndedIterator for Drain<'_, T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back().map(|it| unsafe { ptr::read(it) })
    }
}

impl<T, A: Allocator> ExactSizeIterator for Drain<'_, T, A> {}

impl<T, A: Allocator> Drop for Drain<'_, T, A> {
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

#[test]
fn test_uses_provided_allocator() {
    let mut temp_data = [0; 1000];
    let temp = alloc::TempAllocator::new(&mut temp_data);

    let mut this: Vec<u32, _> = Vec::new_in(&temp);

    this.try_reserve(42).unwrap();
    assert_eq!(temp.get_checkpoint().occupied, 42 * size_of::<u32>());
}

#[test]
fn test_reserve_does_not_overallocate() {
    {
        let mut this: Vec<u32> = Vec::new();
        let mut std: std::vec::Vec<u32> = std::vec::Vec::new();

        this.try_reserve(9).unwrap();
        std.reserve(9);
        assert_eq!(this.capacity(), std.capacity());
    }

    {
        let mut this: Vec<u32> = Vec::new();
        let mut std: std::vec::Vec<u32> = std::vec::Vec::new();

        this.try_reserve(8).unwrap();
        std.reserve(8);
        assert_eq!(this.capacity(), std.capacity());

        this.try_reserve(90).unwrap();
        std.reserve(90);
        assert_eq!(this.capacity(), std.capacity());
    }
}

#[test]
fn test_zst_reserve_errors() {
    #[derive(Clone, Copy)]
    struct ZST;

    let mut this: Vec<ZST> = Vec::new();
    let mut std: std::vec::Vec<ZST> = std::vec::Vec::new();

    this.resize(101, ZST);
    assert!(matches!(
        this.try_reserve(usize::MAX - 100),
        Err(ReserveError::CapacityOverflow)
    ));

    std.resize_with(101, || ZST);
    assert!(matches!(
        std.try_reserve(usize::MAX - 100),
        Err(std::collections::TryReserveError { .. })
    ));
}
