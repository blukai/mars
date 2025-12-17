use core::mem::{self, MaybeUninit};
use core::ptr::NonNull;

use alloc::{AllocError, Allocator, Layout};

pub unsafe trait Memory<T> {
    fn as_ptr(&self) -> *const T;
    fn as_mut_ptr(&mut self) -> *mut T;
    fn cap(&self) -> usize;
    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), AllocError>;
    // TODO: Memory will also need srink method.
}

// ----
// growable
//
// TODO: consider renaming GrowableMemory into ReallocableMemory or something in that direction?

pub struct GrowableMemory<T, A: Allocator> {
    ptr: NonNull<T>,
    cap: usize,
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

impl<T, A: Allocator> GrowableMemory<T, A> {
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        Self {
            ptr: NonNull::dangling(),
            cap: 0,
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
        assert_eq!(self.cap, 0);
        if cap > 0 {
            unsafe { self.grow(cap)? };
        }
        Ok(self)
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

impl<T, A: Allocator> Drop for GrowableMemory<T, A> {
    fn drop(&mut self) {
        let layout = unsafe { Layout::array::<T>(self.cap).unwrap_unchecked() };
        // SAFETY: even if T is zst Allocator and ptr is dangling - alloc knows how to handle that.
        unsafe { self.alloc.deallocate(self.ptr.cast(), layout) }
    }
}

impl<T, A: Allocator + Default> Default for GrowableMemory<T, A> {
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

#[repr(transparent)]
pub struct FixedMemory<T, const N: usize> {
    data: MaybeUninit<[T; N]>,
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
        Self {
            data: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }
}

// ----
// spillable (fixed on stack -> spill to growable on heap)

pub enum SpillableMemory<T, const N: usize, A: Allocator> {
    // NOTE: Fixed variant holds onto A, it'll be passed to GrowableMemory on spill.
    Fixed((FixedMemory<T, N>, A)),
    Growable(GrowableMemory<T, A>),
    // NOTE: Transitional variant is used as a temp value while transitioning between
    // fixed<->growable state.
    //   maybe there's a better way?
    Transitional,
}

impl<T, const N: usize, A: Allocator> SpillableMemory<T, N, A> {
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        Self::Fixed((FixedMemory::default(), alloc))
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

unsafe impl<T, const N: usize, A: Allocator> Memory<T> for SpillableMemory<T, N, A> {
    #[inline]
    fn as_ptr(&self) -> *const T {
        match self {
            Self::Fixed((fixed, _)) => Memory::as_ptr(fixed),
            Self::Growable(growable) => Memory::as_ptr(growable),
            Self::Transitional => unreachable!(),
        }
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
        match self {
            Self::Fixed((fixed, _)) => Memory::as_mut_ptr(fixed),
            Self::Growable(growable) => Memory::as_mut_ptr(growable),
            Self::Transitional => unreachable!(),
        }
    }

    #[inline]
    fn cap(&self) -> usize {
        match self {
            Self::Fixed((fixed, _)) => Memory::cap(fixed),
            Self::Growable(growable) => Memory::cap(growable),
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
                let mut growable = GrowableMemory::<T, A>::new_in(alloc).try_with_cap(new_cap)?;
                unsafe {
                    growable
                        .as_mut_ptr()
                        .copy_from_nonoverlapping(fixed.data.as_ptr().cast(), N)
                };
                *self = Self::Growable(growable);
                Ok(())
            }
            Self::Growable(growable) => unsafe { Memory::grow(growable, new_cap) },
            Self::Transitional => unreachable!(),
        }
    }
}

impl<T, const N: usize, A: Allocator + Default> Default for SpillableMemory<T, N, A> {
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

    impl<T, A: Allocator> GrowableMemory<T, A> {
        #[inline]
        pub fn with_cap(self, cap: usize) -> Self {
            this_is_fine(self.try_with_cap(cap))
        }
    }
}
