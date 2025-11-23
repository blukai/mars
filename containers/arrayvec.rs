use core::mem::{self, MaybeUninit};
use core::ptr::{self, NonNull};
use core::slice::{self, SliceIndex};
use core::{fmt, iter, ops};
use std::io;

use alloc::{AllocError, Allocator, Layout};
use scopeguard::ScopeGuard;

use crate::vec::Vec;
use crate::{
    CapacityError, ReserveError, try_range_from_bounds, unwrap_capacity_result,
    unwrap_reserve_result,
};

struct ArrayStorage<T, const N: usize>([MaybeUninit<T>; N], bool);

impl<T, const N: usize> ArrayStorage<T, N> {
    const fn new() -> Self {
        Self(unsafe { MaybeUninit::uninit().assume_init() }, false)
    }
}

unsafe impl<T, const N: usize> Allocator for ArrayStorage<T, N> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if self.1 || size_of_val(&self.0) < layout.size() {
            return Err(AllocError);
        }
        #[expect(invalid_reference_casting)]
        unsafe {
            (&mut *(self as *const _ as *mut Self)).1 = true
        };
        NonNull::new(ptr::slice_from_raw_parts_mut(
            self.0.as_ptr().cast::<u8>().cast_mut(),
            layout.size(),
        ))
        .ok_or(AllocError)
        // println!("{} / {}", layout.size(), N * size_of::<T>());
        // println!("{:?}", &self.0);
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: std::alloc::Layout) {
        // no.
    }
}

// TODO: rename to FixedVec.
pub struct ArrayVec<T, const N: usize>(Vec<T, ArrayStorage<T, N>>);

#[rustfmt::skip]
impl<T, const N: usize> ArrayVec<T, N> {
    pub const fn as_mut_ptr(&mut self) -> *mut T { self.0.as_mut_ptr() }
    pub const fn as_mut_slice(&mut self) -> &mut [T] { self.0.as_mut_slice() }
    pub const fn as_ptr(&self) -> *const T { self.0.as_ptr() }
    pub const fn as_slice(&self) -> &[T] { self.0.as_slice() }
    pub const fn capacity(&self) -> usize { self.0.capacity() }
    pub const fn is_empty(&self) -> bool { self.0.is_empty() }
    pub const fn len(&self) -> usize { self.0.len() }
    pub const fn new() -> Self { Self(Vec::new_in(ArrayStorage::new())) }
    // pub const fn new_in(alloc: A) -> Self { self.0.new_in() }
    pub fn clear(&mut self) { self.0.clear() }
    // pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A> { self.0.drain() }
    pub fn extend_from_iter<I: Iterator<Item = T>>(&mut self, iter: I) { self.0.extend_from_iter(iter) }
    pub fn extend_from_slice(&mut self, slice: &[T]) where T: Clone { self.0.extend_from_slice(slice) }
    pub fn from_array<const C: usize>(array: [T; C]) -> Self { Self(Vec::from_array_in(array, ArrayStorage::new())) }
    // pub fn from_array_in<const C: usize>(array: [T; C], alloc: A) -> Self { self.0.from_array_in() }
    pub fn from_item(value: T, n: usize) -> Self where T: Clone { Self(Vec::from_item_in(value, n, ArrayStorage::new())) }
    // pub fn from_item_in(value: T, n: usize, alloc: A) -> Self { self.0.from_item_in() }
    // pub fn from_iter_in<I: Iterator<Item = T>>(iter: I, alloc: A) -> Self { self.0.from_iter_in() }
    pub fn from_slice(slice: &[T]) -> Self where T: Clone { Self(Vec::from_slice_in(slice, ArrayStorage::new())) }
    // pub fn from_slice_in(slice: &[T], alloc: A) -> Self { self.0.from_slice_in() }
    pub fn pop(&mut self) -> Option<T> { self.0.pop() }
    pub fn push(&mut self, value: T) { self.0.push(value) }
    pub fn push_within_capacity(&mut self, value: T) -> Result<(), T> { self.0.push_within_capacity(value) }
    // pub fn reserve(&mut self, additional: usize) { self.0.reserve(additional) }
    // pub fn reserve_exact(&mut self, additional: usize) { self.0.reserve_exact(additional) }
    pub fn resize(&mut self, new_len: usize, value: T) where T: Clone { self.0.resize(new_len, value) }
    pub fn resize_with<F>(&mut self, new_len: usize, f: F) where F: FnMut() -> T { self.0.resize_with(new_len, f) }
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] { self.0.spare_capacity_mut() }
    pub fn truncate(&mut self, len: usize) { self.0.truncate(len) }
    pub fn try_extend_from_iter<I: Iterator<Item = T>>(&mut self, iter: I) -> Result<(), ReserveError> { self.0.try_extend_from_iter(iter) }
    pub fn try_extend_from_slice(&mut self, slice: &[T]) -> Result<(), ReserveError> where T: Clone { self.0.try_extend_from_slice(slice) }
    pub fn try_from_array<const C: usize>(array: [T; C]) -> Result<Self, ReserveError> { Vec::try_from_array_in(array, ArrayStorage::new()).map(Self) }
    // pub fn try_from_array_in<const C: usize>( { self.0.try_from_array_in() }
    pub fn try_from_item(value: T, n: usize) -> Result<Self, ReserveError> where T: Clone { Vec::try_from_item_in(value, n, ArrayStorage::new()).map(Self) }
    // pub fn try_from_item_in(value: T, n: usize, alloc: A) -> Result<Self, ReserveError> { self.0.try_from_item_in() }
    pub fn try_from_iter<I: Iterator<Item = T>>(iter: I) -> Result<Self, ReserveError> { Vec::try_from_iter_in(iter, ArrayStorage::new()).map(Self) }
    // pub fn try_from_iter_in<I: Iterator<Item = T>>( { self.0.try_from_iter_in() }
    pub fn try_from_slice(slice: &[T]) -> Result<Self, ReserveError> where T: Clone { Vec::try_from_slice_in(slice, ArrayStorage::new()).map(Self) }
    // pub fn try_from_slice_in(slice: &[T], alloc: A) -> Result<Self, ReserveError> { self.0.try_from_slice_in() }
    pub fn try_push(&mut self, value: T) -> Result<(), ReserveError> { self.0.try_push(value) }
    // pub fn try_reserve(&mut self, additional: usize) -> Result<(), ReserveError> { self.0.try_reserve(additional) }
    // pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), ReserveError> { self.0.try_reserve_exact(additional) }
    pub fn try_resize(&mut self, new_len: usize, value: T) -> Result<(), ReserveError> where T: Clone { self.0.try_resize(new_len, value) }
    pub fn try_resize_with<F>(&mut self, new_len: usize, f: F) -> Result<(), ReserveError> where F: FnMut() -> T { self.0.try_resize_with(new_len, f) }
    // pub fn try_with_capacity(cap: usize) -> Result<Self, ReserveError> { self.0.try_with_capacity() }
    // pub fn try_with_capacity_in(cap: usize, alloc: A) -> Result<Self, ReserveError> { self.0.try_with_capacity_in() }
    // pub fn with_capacity(cap: usize) -> Self { self.0.with_capacity() }
    // pub fn with_capacity_in(cap: usize, alloc: A) -> Self { self.0.with_capacity_in() }
    pub unsafe fn set_len(&mut self, new_len: usize) { unsafe { self.0.set_len(new_len) } }
}

// #[repr(C)]
// pub struct ArrayVec<T, const N: usize> {
//     len: usize,
//     data: [MaybeUninit<T>; N],
// }
//
// impl<T, const N: usize> ArrayVec<T, N> {
//     #[inline]
//     pub const fn new() -> Self {
//         Self {
//             len: 0,
//             data: unsafe { MaybeUninit::uninit().assume_init() },
//         }
//     }
//
//     #[inline]
//     pub const fn capacity(&self) -> usize {
//         N
//     }
//
//     #[inline]
//     pub const fn len(&self) -> usize {
//         self.len
//     }
//
//     #[inline]
//     pub const fn is_empty(&self) -> bool {
//         self.len() == 0
//     }
//
//     #[inline]
//     pub const fn is_full(&self) -> bool {
//         self.capacity() == self.len()
//     }
//
//     #[inline]
//     pub const fn remaining_capacity(&self) -> usize {
//         self.capacity() - self.len()
//     }
//
//     /// SAFETY: new_len must be less than or equal to capacity.
//     /// the items at old_len..new_len must be initialized.
//     #[inline]
//     pub unsafe fn set_len(&mut self, new_len: usize) {
//         debug_assert!(new_len <= self.capacity());
//         self.len = new_len;
//     }
//
//     #[inline]
//     pub const fn as_ptr(&self) -> *const T {
//         self.data.as_ptr().cast()
//     }
//
//     #[inline]
//     pub const fn as_mut_ptr(&mut self) -> *mut T {
//         self.data.as_mut_ptr().cast()
//     }
//
//     #[inline]
//     pub const fn as_slice(&self) -> &[T] {
//         unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
//     }
//
//     #[inline]
//     pub const fn as_mut_slice(&mut self) -> &mut [T] {
//         unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
//     }
//
//     #[inline]
//     pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
//         // SAFETY: the memory between `self.len` and `self.capacity` is guaranteed to be allocated
//         // and valid, but uninitialized.
//         unsafe {
//             let ptr = self.as_mut_ptr().add(self.len()).cast::<MaybeUninit<T>>();
//             slice::from_raw_parts_mut(ptr, self.remaining_capacity())
//         }
//     }
//
//     /// SAFETY: the length must be less than the capacity.
//     #[inline]
//     unsafe fn push_unchecked(&mut self, value: T) {
//         let spare = self.spare_capacity_mut();
//         // SAFETY: by the safety requirements, `spare` is non-empty.
//         unsafe { spare.get_unchecked_mut(0) }.write(value);
//         self.len += 1;
//     }
//
//     // TODO: should there be a custom error for push?
//     //   that will contain value so that the caller can get it back?
//     #[inline]
//     pub fn try_push(&mut self, value: T) -> Result<(), CapacityError> {
//         if self.is_full() {
//             return Err(CapacityError);
//         }
//         unsafe { self.push_unchecked(value) };
//         Ok(())
//     }
//
//     pub fn push(&mut self, value: T) {
//         unwrap_capacity_result(self.try_push(value))
//     }
//
//     /// removes the last item and returns it, or `None` if it is empty.
//     pub fn pop(&mut self) -> Option<T> {
//         if self.is_empty() {
//             return None;
//         }
//         unsafe {
//             self.len -= 1;
//             Some(self.as_ptr().add(self.len()).read())
//         }
//     }
//
//     /// shortens the vector, setting the length to `len` and drops the removed values.
//     pub fn truncate(&mut self, len: usize) {
//         let Some(count) = self.len().checked_sub(len) else {
//             return;
//         };
//         unsafe {
//             let to_drop = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), count);
//             self.len = len;
//             to_drop.drop_in_place();
//         }
//     }
//
//     #[inline]
//     pub fn clear(&mut self) {
//         self.truncate(0);
//         debug_assert!(self.is_empty());
//     }
//
//     // NOTE: this is failable equivalent of Extend::extend.
//     pub fn try_extend_from_iter<I: Iterator<Item = T>>(
//         &mut self,
//         mut iter: I,
//     ) -> Result<(), CapacityError> {
//         while let Some(it) = iter.next() {
//             if self.is_full() {
//                 return Err(CapacityError);
//             }
//             unsafe {
//                 self.push_unchecked(it);
//             }
//         }
//         Ok(())
//     }
//
//     pub fn extend_from_iter<I: Iterator<Item = T>>(&mut self, iter: I) {
//         unwrap_capacity_result(self.try_extend_from_iter(iter))
//     }
//
//     // TODO: consider introducing a distinct try_extend_from_slice for T: Copy.
//     //   need either specialization feature or split methods:
//     //   - try_extend_clone_from_slice
//     //   - try_extend_copy_from_slice
//     //   or something
//     pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), CapacityError>
//     where
//         T: Clone,
//     {
//         self.try_extend_from_iter(other.iter().cloned())
//     }
//
//     pub fn extend_from_slice(&mut self, other: &[T])
//     where
//         T: Clone,
//     {
//         unwrap_capacity_result(self.try_extend_from_slice(other))
//     }
//
//     pub fn try_from_iter<I: Iterator<Item = T>>(iter: I) -> Result<Self, CapacityError> {
//         let mut this = Self::new();
//         this.try_extend_from_iter(iter)?;
//         Ok(this)
//     }
//
//     // NOTE: from_iter is implemented by the FromIterator trait.
//     // pub fn from_iter<I: Iterator<Item = T>>(iter: I) -> Self { ... }
//
//     // TODO: consider introducing a distinct try_extend_from_slice for T: Copy.
//     //   need either specialization feature or split methods:
//     //   - try_from_slice_copy
//     //   - try_from_slice_clone
//     //   or something
//     pub fn try_from_slice(slice: &[T]) -> Result<Self, CapacityError>
//     where
//         T: Clone,
//     {
//         let mut this = Self::new();
//         this.try_extend_from_slice(slice)?;
//         Ok(this)
//     }
//
//     pub fn from_slice(slice: &[T]) -> Self
//     where
//         T: Clone,
//     {
//         unwrap_capacity_result(Self::try_from_slice(slice))
//     }
//
//     pub fn try_from_array<const C: usize>(array: [T; C]) -> Result<Self, CapacityError> {
//         if N < C {
//             return Err(CapacityError);
//         }
//         let mut this = Self::new();
//         unsafe { this.as_mut_ptr().cast::<[T; C]>().write(array) };
//         this.len = C;
//         Ok(this)
//     }
//
//     pub fn from_array<const C: usize>(array: [T; C]) -> Self {
//         unwrap_capacity_result(Self::try_from_array(array))
//     }
//
//     /// create with `n` clones of `value`.
//     pub fn try_from_item(value: T, n: usize) -> Result<Self, CapacityError>
//     where
//         T: Clone,
//     {
//         Self::try_from_iter(iter::repeat_n(value, n))
//     }
//
//     pub fn from_item(value: T, n: usize) -> Self
//     where
//         T: Clone,
//     {
//         unwrap_capacity_result(Self::try_from_item(value, n))
//     }
//
//     /// resizes the [`ArrayVec`] so that `len` is equal to `new_len`.
//     ///
//     /// if `new_len` is smaller than `len`, the `ArrayVec` is [`ArrayVec::truncate`]d.
//     /// if `new_len` is larger, each new slot is filled with clones of `value`.
//     pub fn try_resize(&mut self, new_len: usize, value: T) -> Result<(), CapacityError>
//     where
//         T: Clone,
//     {
//         let Some(n) = new_len.checked_sub(self.len()) else {
//             self.truncate(new_len);
//             return Ok(());
//         };
//         self.try_extend_from_iter(iter::repeat_n(value, n))
//     }
//
//     pub fn resize(&mut self, new_len: usize, value: T)
//     where
//         T: Clone,
//     {
//         unwrap_capacity_result(self.try_resize(new_len, value))
//     }
//
//     /// resizes the [`ArrayVec`] so that `len` is equal to `new_len`.
//     ///
//     /// if `new_len` is smaller than `len`, the `ArrayVec` is [`ArrayVec::truncate`]d.
//     /// if `new_len` is larger, each new slot is filled with clones of `value`.
//     ///
//     /// if you'd rather [`Clone`] a given value, use [`ArrayVec::try_resize`]/[`ArrayVec::resize`].
//     /// if you want to use the [`Default`] trait to generate values, you can pass
//     /// [`Default::default`].
//     pub fn try_resize_with<F>(&mut self, new_len: usize, f: F) -> Result<(), CapacityError>
//     where
//         F: FnMut() -> T,
//     {
//         let Some(n) = new_len.checked_sub(self.len()) else {
//             self.truncate(new_len);
//             return Ok(());
//         };
//         self.try_extend_from_iter(iter::repeat_with(f).take(n))
//     }
//
//     pub fn resize_with<F>(&mut self, new_len: usize, f: F)
//     where
//         F: FnMut() -> T,
//     {
//         unwrap_capacity_result(self.try_resize_with(new_len, f))
//     }
//
//     /// takes ownership of the subslice indicated by the given range.
//     ///
//     /// # panics
//     ///
//     /// if the range is invalid (`range.start > range.end`) or if end out of bounds
//     /// `range.end > self.len()`.
//     ///
//     /// # leaks
//     ///
//     /// if [`Drain`] goes out of scope without being dropped (due to [`std::mem::forget`], for
//     /// example), the vector may have lost and leaked items arbitrarily, including items outside
//     /// the range.
//     pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, N>
//     where
//         R: ops::RangeBounds<usize>,
//     {
//         let len = self.len();
//         // TODO(blukai): maybe non-paniching variant of drain (try_drain?).
//         let ops::Range { start, end } = try_range_from_bounds(range, ..len).expect("invalid range");
//
//         // NOTE: when Drain drops the remaining tail of the vec is copied back to cover the hole.
//         unsafe {
//             // NOTE: set len to start, to be safe in case Drain's leakage.
//             self.len = start;
//             let iter =
//                 slice::from_raw_parts_mut(self.as_mut_ptr().add(start), end - start).iter_mut();
//             Drain {
//                 iter,
//                 vec: NonNull::from(self),
//                 tail_start: end,
//                 tail_len: len - end,
//             }
//         }
//     }
// }

// impl<T, const N: usize> Drop for ArrayVec<T, N> {
//     fn drop(&mut self) {
//         unsafe { ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len()).drop_in_place() };
//     }
// }

impl<T, const N: usize> Default for ArrayVec<T, N> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> ops::Deref for ArrayVec<T, N> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> ops::DerefMut for ArrayVec<T, N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize, I: SliceIndex<[T]>> ops::Index<I> for ArrayVec<T, N> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        ops::Index::index(&**self, index)
    }
}

impl<T, const N: usize, I: SliceIndex<[T]>> ops::IndexMut<I> for ArrayVec<T, N> {
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

impl_partial_eq! { [const N1: usize, const N2: usize] ArrayVec<T, N1>, ArrayVec<U, N2> }
impl_partial_eq! { [const N: usize, const C: usize] ArrayVec<T, N>, &[U; C] }
impl_partial_eq! { [const N: usize, const C: usize] ArrayVec<T, N>, [U; C] }
impl_partial_eq! { [const N: usize] ArrayVec<T, N>, &[U] }
impl_partial_eq! { [const N: usize] ArrayVec<T, N>, [U] }
impl_partial_eq! { [const N: usize] &[T], ArrayVec<U, N> }
impl_partial_eq! { [const N: usize] [T], ArrayVec<U, N> }

impl<'a, T, const N: usize> IntoIterator for &'a ArrayVec<T, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut ArrayVec<T, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, const N: usize> Extend<T> for ArrayVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.extend_from_iter(iter.into_iter());
    }
}

impl<'a, T: Copy + 'a, const N: usize> Extend<&'a T> for ArrayVec<T, N> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend_from_iter(iter.into_iter().copied())
    }
}

impl<T, const N: usize> FromIterator<T> for ArrayVec<T, N> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        unwrap_reserve_result(Self::try_from_iter(iter.into_iter()))
    }
}

impl<T: Clone, const N: usize> Clone for ArrayVec<T, N> {
    #[inline(always)]
    fn clone(&self) -> Self {
        let mut this = ArrayVec::new();
        this.extend_from_slice(self);
        this
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

impl<T: fmt::Debug, const N: usize> fmt::Debug for ArrayVec<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// Write is implemented for `ArrayVec<u8>` by appending to the vector.
/// The vector will grow as needed.
impl<const N: usize> io::Write for ArrayVec<u8, N> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.try_extend_from_slice(buf).map_err(io::Error::other)?;
        Ok(buf.len())
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[io::IoSlice<'_>]) -> io::Result<usize> {
        let mut len = 0;
        for buf in bufs {
            self.try_extend_from_slice(buf).map_err(io::Error::other)?;
            len += buf.len();
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

// pub struct Drain<'v, T: 'v, const N: usize> {
//     iter: slice::IterMut<'v, T>,
//     vec: NonNull<ArrayVec<T, N>>,
//     tail_start: usize,
//     tail_len: usize,
// }
//
// impl<T, const N: usize> Iterator for Drain<'_, T, N> {
//     type Item = T;
//
//     #[inline]
//     fn next(&mut self) -> Option<T> {
//         self.iter.next().map(|it| unsafe { ptr::read(it) })
//     }
//
//     fn size_hint(&self) -> (usize, Option<usize>) {
//         self.iter.size_hint()
//     }
// }
//
// impl<T, const N: usize> DoubleEndedIterator for Drain<'_, T, N> {
//     #[inline]
//     fn next_back(&mut self) -> Option<T> {
//         self.iter.next_back().map(|it| unsafe { ptr::read(it) })
//     }
// }
//
// impl<T, const N: usize> ExactSizeIterator for Drain<'_, T, N> {}
//
// impl<T, const N: usize> Drop for Drain<'_, T, N> {
//     fn drop(&mut self) {
//         // QUOTE:
//         // > moves back the un-`Drain`ed items to restore the original `Vec`.
//         // > ensure items are moved back into their appropriate places, even when drop_in_place panics
//         let _guard = ScopeGuard::new(|| {
//             if self.tail_len == 0 {
//                 return;
//             }
//
//             unsafe {
//                 let vec = self.vec.as_mut();
//                 let start = vec.len();
//                 let tail = self.tail_start;
//                 if tail != start {
//                     let src = vec.as_ptr().add(tail);
//                     let dst = vec.as_mut_ptr().add(start);
//                     ptr::copy(src, dst, self.tail_len);
//                 }
//                 vec.len = start + self.tail_len;
//             }
//         });
//
//         let iter = mem::take(&mut self.iter);
//         // SAFETY: we own these values so we destroy them.
//         unsafe { ptr::drop_in_place(iter.into_slice()) };
//     }
// }

// #[test]
// fn test_push() {
//     let mut this = ArrayVec::<u32, 2>::new();
//     assert!(this.try_push(8).is_ok());
//     assert!(this.try_push(16).is_ok());
//     assert!(this.try_push(32).is_err());
//     assert_eq!(this, [8, 16]);
// }
//
// #[test]
// fn test_pop() {
//     let mut this = ArrayVec::<u32, 42>::from_array([8, 16]);
//     assert_eq!(this.pop(), Some(16));
//     assert_eq!(this.pop(), Some(8));
//     assert_eq!(this.pop(), None);
//     assert_eq!(this, []);
// }
//
// #[test]
// fn test_index() {
//     let this = ArrayVec::<u32, 42>::from_array([8, 16]);
//     assert_eq!(this[0], 8);
//     assert_eq!(this[1], 16);
// }
//
// // NOTE: test_double_drop is stolen from std tests.
// #[test]
// fn test_double_drop() {
//     struct TwoArrayVec<T> {
//         x: ArrayVec<T, 1>,
//         y: ArrayVec<T, 1>,
//     }
//
//     struct DropCounter<'a> {
//         count: &'a mut u32,
//     }
//
//     impl Drop for DropCounter<'_> {
//         fn drop(&mut self) {
//             *self.count += 1;
//         }
//     }
//
//     let (mut count_x, mut count_y) = (0, 0);
//     {
//         let mut tv = TwoArrayVec {
//             x: ArrayVec::new(),
//             y: ArrayVec::new(),
//         };
//         tv.x.push(DropCounter {
//             count: &mut count_x,
//         });
//         tv.y.push(DropCounter {
//             count: &mut count_y,
//         });
//
//         // If ArrayVec had a drop flag, here is where it would be zeroed.
//         // Instead, it should rely on its internal state to prevent
//         // doing anything significant when dropped multiple times.
//         drop(tv.x);
//
//         // Here tv goes out of scope, tv.y should be dropped, but not tv.x.
//     }
//
//     assert_eq!(count_x, 1);
//     assert_eq!(count_y, 1);
// }
//
// // NOTE: test_drain_leak is stolen from std tests.
// #[test]
// #[cfg_attr(not(panic = "unwind"), ignore = "test requires unwinding support")]
// fn test_drain_leak() {
//     use std::panic::{AssertUnwindSafe, catch_unwind};
//
//     use crate::testing::struct_with_counted_drop;
//
//     struct_with_counted_drop!(
//         D(u32, bool),
//         DROPS => |this: &D| if this.1 { panic!("panic in `drop`"); }
//     );
//
//     let mut v = vec![
//         D(0, false),
//         D(1, false),
//         D(2, false),
//         D(3, false),
//         D(4, true),
//         D(5, false),
//         D(6, false),
//     ];
//
//     catch_unwind(AssertUnwindSafe(|| {
//         v.drain(2..=5);
//     }))
//     .ok();
//
//     assert_eq!(DROPS.get(), 4);
//     assert_eq!(v, vec![D(0, false), D(1, false), D(6, false)]);
// }
//
// // NOTE: test_into_iter_leak is stolen from std tests.
// #[test]
// #[cfg_attr(not(panic = "unwind"), ignore = "test requires unwinding support")]
// fn test_into_iter_leak() {
//     use std::panic::catch_unwind;
//
//     use crate::testing::struct_with_counted_drop;
//
//     struct_with_counted_drop!(D(bool), DROPS => |this: &D| if this.0 { panic!("panic in `drop`"); });
//
//     let v = vec![D(false), D(true), D(false)];
//
//     catch_unwind(move || drop(v.into_iter())).ok();
//
//     assert_eq!(DROPS.get(), 3);
// }
