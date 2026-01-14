use core::mem::{self, MaybeUninit};
use core::ptr::NonNull;

use alloc::{AllocError, Allocator, Layout};

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

pub enum GrowMode {
    Exact,
    Amortized,
}

pub trait RelocateFn<T>: FnMut(/* old_ptr */ NonNull<[T]>, /* new_ptr */ NonNull<[T]>) {}
impl<T, U> RelocateFn<T> for U where U: FnMut(NonNull<[T]>, NonNull<[T]>) {}

#[inline]
pub fn default_relocate<T>(old_ptr: NonNull<[T]>, new_ptr: NonNull<[T]>) {
    debug_assert!(new_ptr.len() >= old_ptr.len());
    unsafe {
        new_ptr
            .cast::<T>()
            .copy_from_nonoverlapping(old_ptr.cast::<T>(), old_ptr.len())
    }
}

pub unsafe trait ArrayMemory<T> {
    fn ptr(&self) -> NonNull<[T]>;
    fn grow<R>(&mut self, new_cap: usize, mode: GrowMode, relocate: R) -> Result<(), AllocError>
    where
        R: RelocateFn<T>;
    // TODO: Memory will also need srink method.
}

// ----
// growable
//
// TODO: consider renaming GrowableMemory into ReallocableMemory or something in that direction?
//   but not HeapMemory because its Allocator may not necessarily be baked by heap.

pub struct GrowableArrayMemory<T, A: Allocator> {
    ptr: NonNull<[T]>,
    // TODO: is there a sane way to not store alloc?
    //
    //   i absolutely hate the idea of storing non-zero sized alloc at each container:
    //     - having anything in global scope (/static) is very-very awkward in rust;
    //       this seems to be the only way of making zero-sized allocators.
    //     - allocators cannot be clonable unless they bind to global state or rc/arc'ed.
    //     - the fact that each single tiny thing allocates needs to be generic over it's
    //       allocator. and these generic params need to propagate upwards .. is somewhat nightmarish.
    //       and there are different kinds of allocators.
    //       certain things would need multiple alloc params.
    //       you can solve propagation issue by just specifying concrete allocator though.
    //
    //   do it like zig does, accepting allocator as an arg in functions that may allocate?
    //   with that:
    //     - _assume_cap methods must not try to allocate (but can return capacity error).
    //     - _in methods may allocate, these will accept allocator arg.
    //   but then there would be no way to rely on Drop? instead things would need to be
    //   deinitialized explicitly:
    //     - panic on drop and require explicit deinitialization.
    //     - but then it'll become easy to be confused about which allocator the thing was
    //       allocated with without some kind of markers.
    //     - this would remove a feature or rust that i actually kind of enjoy.
    alloc: A,
}

impl<T, A: Allocator> GrowableArrayMemory<T, A> {
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        Self {
            ptr: NonNull::slice_from_raw_parts(NonNull::dangling(), 0),
            alloc,
        }
    }

    #[inline]
    pub fn allocator(&self) -> &A {
        &self.alloc
    }

    #[inline]
    pub fn try_with_cap(mut self, cap: usize) -> Result<Self, AllocError> {
        self.grow(cap, GrowMode::Exact, default_relocate)?;
        Ok(self)
    }
}

unsafe impl<T, A: Allocator> ArrayMemory<T> for GrowableArrayMemory<T, A> {
    #[inline]
    fn ptr(&self) -> NonNull<[T]> {
        self.ptr
    }

    #[inline]
    fn grow<R>(&mut self, new_cap: usize, mode: GrowMode, mut relocate: R) -> Result<(), AllocError>
    where
        R: RelocateFn<T>,
    {
        // NOTE: array's capacity is `usize::MAX` for zsts.
        if size_of::<T>() == 0 {
            return Err(AllocError);
        }

        let old_cap = self.ptr.len();
        if new_cap <= old_cap {
            return Ok(());
        }

        let new_cap = match mode {
            GrowMode::Exact => new_cap,
            GrowMode::Amortized => new_cap
                // NOTE: the doubling cannot overflow because `cap <= isize::MAX`.
                //   `Layout::array` upholds this.
                .max(old_cap * 2)
                .max(min_non_zero_cap(size_of::<T>())),
        };
        let new_layout = Layout::array::<T>(new_cap).map_err(|_| AllocError)?;
        let new_ptr = if old_cap > 0 {
            let new_ptr = self.alloc.allocate(new_layout)?;
            let new_ptr = NonNull::slice_from_raw_parts(new_ptr.cast::<T>(), new_cap);

            relocate(self.ptr, new_ptr);

            let old_layout = unsafe { Layout::array::<T>(old_cap).unwrap_unchecked() };
            debug_assert_eq!(old_layout.align(), new_layout.align());
            unsafe { self.alloc.deallocate(self.ptr.cast(), old_layout) };

            new_ptr
        } else {
            let new_ptr = self.alloc.allocate(new_layout)?;
            let new_ptr = NonNull::slice_from_raw_parts(new_ptr.cast::<T>(), new_cap);
            new_ptr
        };
        self.ptr = new_ptr;
        Ok(())
    }
}

impl<T, A: Allocator> Drop for GrowableArrayMemory<T, A> {
    fn drop(&mut self) {
        let layout = unsafe { Layout::array::<T>(self.ptr.len()).unwrap_unchecked() };
        // SAFETY: even if T is zst Allocator and ptr is dangling - alloc knows how to handle that.
        unsafe { self.alloc.deallocate(self.ptr.cast(), layout) }
    }
}

impl<T, A: Allocator + Default> Default for GrowableArrayMemory<T, A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(A::default())
    }
}

// ----
// fixed
//
// TODO: consider renaming FixedMemory to StackMemory or something alike.
//   that is because it is not unreasonable to think of fixed size heap allocations.
//   the word "fixed" doesn't fully correctly convey the meaning.
//
//   word "static" is also an option. not in terms of static location in memory, but
//   statically-known size.

#[repr(transparent)]
pub struct FixedArrayMemory<T, const N: usize> {
    data: MaybeUninit<[T; N]>,
}

unsafe impl<T, const N: usize> ArrayMemory<T> for FixedArrayMemory<T, N> {
    #[inline]
    fn ptr(&self) -> NonNull<[T]> {
        NonNull::slice_from_raw_parts(
            unsafe { NonNull::new_unchecked(self.data.as_ptr().cast::<T>().cast_mut()) },
            N,
        )
    }

    #[inline]
    fn grow<R>(&mut self, new_cap: usize, _mode: GrowMode, _relocate: R) -> Result<(), AllocError>
    where
        R: RelocateFn<T>,
    {
        if new_cap <= N {
            Ok(())
        } else {
            Err(AllocError)
        }
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

// ----
// spillable (fixed on stack -> spill to growable on heap)

pub enum SpillableArrayMemory<T, const N: usize, A: Allocator> {
    // NOTE: Fixed variant holds onto A, it'll be passed to GrowableMemory on spill.
    Fixed((FixedArrayMemory<T, N>, A)),
    Growable(GrowableArrayMemory<T, A>),
    // NOTE: Transitional variant is used as a temp value while transitioning between
    // fixed<->growable state.
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
            Self::Growable(growable) => growable.allocator(),
            Self::Transitional => unreachable!(),
        }
    }

    #[inline]
    pub fn is_spilled(&self) -> bool {
        match self {
            Self::Fixed(..) => false,
            Self::Growable(..) => true,
            Self::Transitional => unreachable!(),
        }
    }
}

unsafe impl<T, const N: usize, A: Allocator> ArrayMemory<T> for SpillableArrayMemory<T, N, A> {
    #[inline]
    fn ptr(&self) -> NonNull<[T]> {
        match self {
            Self::Fixed((fixed, _)) => ArrayMemory::ptr(fixed),
            Self::Growable(growable) => ArrayMemory::ptr(growable),
            Self::Transitional => unreachable!(),
        }
    }

    fn grow<R>(&mut self, new_cap: usize, mode: GrowMode, mut relocate: R) -> Result<(), AllocError>
    where
        R: RelocateFn<T>,
    {
        match self {
            Self::Fixed(..) => {
                // NOTE: we don't want to spill over if we don't need to regardless the mode.
                if new_cap <= N {
                    return Ok(());
                }
                let Self::Fixed((fixed, alloc)) = mem::replace(self, Self::Transitional) else {
                    unreachable!();
                };
                let growable = GrowableArrayMemory::<T, A>::new_in(alloc).try_with_cap(new_cap)?;
                relocate(fixed.ptr(), growable.ptr());
                *self = Self::Growable(growable);
                Ok(())
            }
            Self::Growable(growable) => ArrayMemory::grow(growable, new_cap, mode, relocate),
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

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use crate::this_is_fine;

    use super::*;

    impl<T, A: Allocator> GrowableArrayMemory<T, A> {
        #[inline]
        pub fn with_cap(self, cap: usize) -> Self {
            this_is_fine(self.try_with_cap(cap))
        }
    }
}
