use core::mem::MaybeUninit;
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

pub struct GrowableMemory<T, A: Allocator> {
    ptr: NonNull<T>,
    cap: usize,
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
    pub fn try_new_with_cap_in(cap: usize, alloc: A) -> Result<Self, AllocError> {
        let mut this = Self::new_in(alloc);
        if cap > 0 {
            unsafe { this.grow(cap)? };
        }
        Ok(this)
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

#[cfg(not(no_global_oom_handling))]
mod oom_growable_memory {
    use crate::this_is_fine;

    use super::*;

    impl<T, A: Allocator> GrowableMemory<T, A> {
        #[inline]
        pub fn new_with_cap_in(cap: usize, alloc: A) -> Self {
            this_is_fine(Self::try_new_with_cap_in(cap, alloc))
        }
    }
}

// ----
// fixed

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
// fixed+growable

pub enum FixedGrowableMemoryKind<T, const N: usize, A: Allocator> {
    Fixed(FixedMemory<T, N>),
    Growable(GrowableMemory<T, A>),
}

pub struct FixedGrowableMemory<T, const N: usize, A: Allocator> {
    pub kind: FixedGrowableMemoryKind<T, N, A>,
    alloc: Option<A>,
}

impl<T, const N: usize, A: Allocator> FixedGrowableMemory<T, N, A> {
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        Self {
            kind: FixedGrowableMemoryKind::Fixed(FixedMemory::default()),
            alloc: Some(alloc),
        }
    }
}

unsafe impl<T, const N: usize, A: Allocator> Memory<T> for FixedGrowableMemory<T, N, A> {
    #[inline]
    fn as_ptr(&self) -> *const T {
        use FixedGrowableMemoryKind::*;
        match self.kind {
            Fixed(ref fixed) => Memory::as_ptr(fixed),
            Growable(ref growable) => Memory::as_ptr(growable),
        }
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
        use FixedGrowableMemoryKind::*;
        match self.kind {
            Fixed(ref mut fixed) => Memory::as_mut_ptr(fixed),
            Growable(ref mut growable) => Memory::as_mut_ptr(growable),
        }
    }

    #[inline]
    fn cap(&self) -> usize {
        use FixedGrowableMemoryKind::*;
        match self.kind {
            Fixed(ref fixed) => Memory::cap(fixed),
            Growable(ref growable) => Memory::cap(growable),
        }
    }

    unsafe fn grow(&mut self, new_cap: usize) -> Result<(), AllocError> {
        use FixedGrowableMemoryKind::*;
        match self.kind {
            Fixed(ref mut fixed) => {
                let alloc = self.alloc.take().expect("unyoinked alloc");
                let mut growable = GrowableMemory::<T, A>::try_new_with_cap_in(new_cap, alloc)?;
                unsafe {
                    growable
                        .as_mut_ptr()
                        .copy_from_nonoverlapping(fixed.data.as_ptr().cast(), N)
                };
                self.kind = Growable(growable);
                Ok(())
            }
            Growable(ref mut growable) => unsafe { Memory::grow(growable, new_cap) },
        }
    }
}

impl<T, const N: usize, A: Allocator + Default> Default for FixedGrowableMemory<T, N, A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(A::default())
    }
}
