use core::mem::{self, MaybeUninit};
use core::ptr::NonNull;

use alloc::{AllocError, Allocator, Layout};

pub unsafe trait ArrayMemory<T> {
    fn ptr(&self) -> NonNull<[T]>;
    unsafe fn grow(&mut self, new_len: usize) -> Result<(), AllocError>;
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
        // TODO: should with_cap resize (grow/shrink)?
        assert_eq!(self.ptr.len(), 0);
        if cap > 0 {
            unsafe { self.grow(cap)? };
        }
        Ok(self)
    }
}

unsafe impl<T, A: Allocator> ArrayMemory<T> for GrowableArrayMemory<T, A> {
    #[inline]
    fn ptr(&self) -> NonNull<[T]> {
        self.ptr
    }

    /// SAFETY: `new_cap` must be greater then the current capacity.
    #[inline]
    unsafe fn grow(&mut self, new_len: usize) -> Result<(), AllocError> {
        let old_len = self.ptr.len();

        // NOTE: this must be ensured by the caller.
        debug_assert!(new_len > old_len);
        // TODO: do i need to do anything special for zsts here? array handles them and they don't
        // propagate here.
        debug_assert!(size_of::<T>() > 0);

        let new_layout = Layout::array::<T>(new_len).map_err(|_| AllocError)?;
        let new_ptr = if old_len > 0 {
            let old_layout = unsafe { Layout::array::<T>(old_len).unwrap_unchecked() };
            debug_assert_eq!(old_layout.align(), new_layout.align());
            let new_ptr = unsafe { self.alloc.grow(self.ptr.cast(), old_layout, new_layout) }?;
            let new_ptr = NonNull::slice_from_raw_parts(new_ptr.cast::<T>(), new_len);
            new_ptr
        } else {
            let new_ptr = self.alloc.allocate(new_layout)?;
            let new_ptr = NonNull::slice_from_raw_parts(new_ptr.cast::<T>(), new_len);
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

    unsafe fn grow(&mut self, new_len: usize) -> Result<(), AllocError> {
        // NOTE: this assert here just for documentation purposes.
        debug_assert!(new_len > self.ptr().len());

        match self {
            Self::Fixed(..) => {
                let Self::Fixed((fixed, alloc)) = mem::replace(self, Self::Transitional) else {
                    unreachable!();
                };
                let growable = GrowableArrayMemory::<T, A>::new_in(alloc).try_with_cap(new_len)?;
                unsafe {
                    growable
                        .ptr()
                        .cast::<T>()
                        .copy_from_nonoverlapping(fixed.ptr().cast::<T>(), N)
                };
                *self = Self::Growable(growable);
                Ok(())
            }
            Self::Growable(growable) => unsafe { ArrayMemory::grow(growable, new_len) },
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
