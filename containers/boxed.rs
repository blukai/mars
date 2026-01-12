use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::NonNull;
use core::{fmt, ops, slice};

use alloc::{AllocError, Allocator, Layout};

pub struct Box<T: ?Sized, A: Allocator = alloc::Global> {
    ptr: NonNull<T>,
    alloc: A,
}

impl<T: ?Sized, A: Allocator> Box<T, A> {
    /// # Safety
    ///
    /// For non-ZSTs, `raw` must point to memory allocated with `A` that holds a valid `T`. The
    /// caller passes ownership of the allocation to the `Box`.
    ///
    /// For ZSTs, `raw` must be a dangling, well aligned pointer.
    #[inline]
    pub const unsafe fn from_raw_in(ptr: *mut T, alloc: A) -> Self {
        Self {
            // SAFETY: by the safety preconditions of this function, `ptr` is not a null pointer.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            alloc,
        }
    }

    /// NOTE: this will not run the destructor of `T`.
    #[inline]
    pub fn into_raw_with_alloc(this: Self) -> (*mut T, A) {
        let mut this = ManuallyDrop::new(this);
        let ptr = this.ptr.as_ptr();
        let alloc = unsafe { (&raw mut this.alloc).read() };
        (ptr, alloc)
    }
}

impl<T, A: Allocator> Box<MaybeUninit<T>, A> {
    /// # Safety
    ///
    /// Callers must ensure that the value inside of `b` is in an initialized state.
    pub unsafe fn assume_init(self) -> Box<T, A> {
        let (ptr, alloc) = Box::into_raw_with_alloc(self);
        unsafe { Box::from_raw_in(ptr.cast(), alloc) }
    }

    pub fn write(self, value: T) -> Box<T, A> {
        unsafe {
            (self.ptr.cast()).write(value);
            self.assume_init()
        }
    }
}

impl<T, A: Allocator> Box<T, A> {
    #[inline]
    const fn is_zst() -> bool {
        size_of::<T>() == 0
    }

    pub fn try_new_uninit_in(alloc: A) -> Result<Box<MaybeUninit<T>, A>, AllocError> {
        let ptr = if Self::is_zst() {
            NonNull::dangling()
        } else {
            let layout = Layout::new::<MaybeUninit<T>>();
            alloc.allocate(layout)?.cast()
        };
        Ok(unsafe { Box::from_raw_in(ptr.as_ptr(), alloc) })
    }

    #[inline]
    pub fn try_new_in(value: T, alloc: A) -> Result<Self, AllocError> {
        let this = Self::try_new_uninit_in(alloc)?;
        Ok(this.write(value))
    }
}

impl<T, A: Allocator> Box<[MaybeUninit<T>], A> {
    pub unsafe fn assume_init(self) -> Box<[T], A> {
        unsafe {
            let len = self.len();
            let (ptr, alloc) = Box::into_raw_with_alloc(self);
            let slice = slice::from_raw_parts_mut(ptr.cast::<T>(), len);
            Box::from_raw_in(slice, alloc)
        }
    }
}

impl<T, A: Allocator> Box<[T], A> {
    pub fn try_new_uninit_in(len: usize, alloc: A) -> Result<Box<[MaybeUninit<T>], A>, AllocError> {
        unsafe {
            let layout = Layout::array::<MaybeUninit<T>>(len).map_err(|_| AllocError)?;
            let ptr = alloc.allocate(layout)?;
            let slice = slice::from_raw_parts_mut(ptr.cast::<MaybeUninit<T>>().as_ptr(), len);
            Ok(Box::from_raw_in(slice, alloc))
        }
    }
}

impl<T: ?Sized, A: Allocator> ops::Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T: ?Sized, A: Allocator> ops::DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T: ?Sized, A: Allocator> AsRef<T> for Box<T, A> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, A: Allocator> AsMut<T> for Box<T, A> {
    fn as_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<T: ?Sized + fmt::Display, A: Allocator> fmt::Display for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug, A: Allocator> fmt::Debug for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized, A: Allocator> Drop for Box<T, A> {
    fn drop(&mut self) {
        let layout = Layout::for_value::<T>(self);
        unsafe {
            self.ptr.drop_in_place();
            self.alloc.deallocate(self.ptr.cast(), layout)
        };
    }
}

unsafe impl<T: Send + ?Sized, A: Allocator> Send for Box<T, A> {}

unsafe impl<T: Sync + ?Sized, A: Allocator> Sync for Box<T, A> {}

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use crate::this_is_fine;

    use super::*;

    impl<T, A: Allocator> Box<T, A> {
        pub fn new_uninit_in(alloc: A) -> Box<MaybeUninit<T>, A> {
            this_is_fine(Self::try_new_uninit_in(alloc))
        }

        #[inline]
        pub fn new_in(value: T, alloc: A) -> Self {
            this_is_fine(Self::try_new_in(value, alloc))
        }
    }

    impl<T, A: Allocator> Box<[T], A> {
        pub fn new_uninit_in(len: usize, alloc: A) -> Box<[MaybeUninit<T>], A> {
            this_is_fine(Self::try_new_uninit_in(len, alloc))
        }
    }
}
