use core::alloc::Layout;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::NonNull;
use core::{fmt, ops, ptr, slice};

use alloc::{AllocError, Allocator};

pub struct Box<T: ?Sized, A: Allocator> {
    ptr: *mut T,
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
        Self { ptr, alloc }
    }

    #[inline]
    pub fn as_ptr(this: &Self) -> *const T {
        this.ptr
    }

    #[inline]
    pub fn as_mut_ptr(this: &Self) -> *mut T {
        this.ptr
    }

    /// NOTE: this will not run the destructor of `T`.
    #[inline]
    pub fn into_raw_with_alloc(this: Self) -> (*mut T, A) {
        let this = ManuallyDrop::new(this);
        unsafe { (this.ptr, ptr::read(&this.alloc)) }
    }

    pub fn leak_with_alloc<'a>(this: Self) -> (&'a mut T, A) {
        let mut this = ManuallyDrop::new(this);
        unsafe { (&mut *this.ptr, ptr::read(&this.alloc)) }
    }
}

impl<T, A: Allocator> Box<MaybeUninit<T>, A> {
    /// # Safety
    ///
    /// Callers must ensure that the value inside of `b` is in an initialized state.
    pub unsafe fn assume_init(self) -> Box<T, A> {
        let (ptr, alloc) = Box::into_raw_with_alloc(self);
        unsafe { Box::from_raw_in(ptr as *mut T, alloc) }
    }

    pub fn write(self, value: T) -> Box<T, A> {
        unsafe {
            (self.ptr as *mut T).write(value);
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
            ptr::dangling_mut()
        } else {
            let layout = Layout::new::<MaybeUninit<T>>();
            alloc.allocate(layout)?.as_ptr() as *mut MaybeUninit<T>
        };
        unsafe { Ok(Box::from_raw_in(ptr, alloc)) }
    }

    pub fn try_new_zeroed_in(alloc: A) -> Result<Box<MaybeUninit<T>, A>, AllocError> {
        let ptr = if Self::is_zst() {
            ptr::dangling_mut()
        } else {
            let layout = Layout::new::<MaybeUninit<T>>();
            alloc.allocate_zeroed(layout)?.as_ptr() as *mut MaybeUninit<T>
        };
        unsafe { Ok(Box::from_raw_in(ptr, alloc)) }
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
            let slice = slice::from_raw_parts_mut(ptr as *mut T, len);
            Box::from_raw_in(slice, alloc)
        }
    }
}

impl<T, A: Allocator> Box<[T], A> {
    pub fn try_new_uninit_slice_in(
        len: usize,
        alloc: A,
    ) -> Result<Box<[MaybeUninit<T>], A>, AllocError> {
        unsafe {
            let layout = Layout::array::<MaybeUninit<T>>(len).map_err(|_| AllocError)?;
            let ptr = alloc.allocate(layout)?;
            let slice = slice::from_raw_parts_mut(ptr.as_ptr() as *mut MaybeUninit<T>, len);
            Ok(Box::from_raw_in(slice, alloc))
        }
    }

    pub fn try_new_zeroed_slice_in(
        len: usize,
        alloc: A,
    ) -> Result<Box<[MaybeUninit<T>], A>, AllocError> {
        unsafe {
            let layout = Layout::array::<MaybeUninit<T>>(len).map_err(|_| AllocError)?;
            let ptr = alloc.allocate_zeroed(layout)?;
            let slice = slice::from_raw_parts_mut(ptr.as_ptr() as *mut MaybeUninit<T>, len);
            Ok(Box::from_raw_in(slice, alloc))
        }
    }

    pub fn try_from_slice_copy_in(slice: &[T], alloc: A) -> Result<Box<[T], A>, AllocError>
    where
        T: Copy,
    {
        unsafe {
            let mut this = Self::try_new_uninit_slice_in(slice.len(), alloc)?;
            ptr::copy_nonoverlapping(slice.as_ptr(), this.as_mut_ptr() as _, slice.len());
            Ok(this.assume_init())
        }
    }
}

impl<T: ?Sized, A: Allocator> ops::Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

impl<T: ?Sized, A: Allocator> ops::DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
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
            ptr::drop_in_place(self.ptr);
            self.alloc
                .deallocate(NonNull::new_unchecked(self.ptr as *mut u8), layout)
        };
    }
}

unsafe impl<T: Send + ?Sized, A: Allocator + Send> Send for Box<T, A> {}

unsafe impl<T: Sync + ?Sized, A: Allocator + Sync> Sync for Box<T, A> {}

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::this_is_fine;

    use super::*;

    impl<T, A: Allocator> Box<T, A> {
        #[track_caller]
        #[inline]
        pub fn new_uninit_in(alloc: A) -> Box<MaybeUninit<T>, A> {
            this_is_fine(Self::try_new_uninit_in(alloc))
        }

        #[track_caller]
        #[inline]
        pub fn new_zeroed_in(alloc: A) -> Box<MaybeUninit<T>, A> {
            this_is_fine(Self::try_new_zeroed_in(alloc))
        }

        #[track_caller]
        #[inline]
        pub fn new_in(value: T, alloc: A) -> Self {
            this_is_fine(Self::try_new_in(value, alloc))
        }
    }

    impl<T, A: Allocator> Box<[T], A> {
        #[track_caller]
        #[inline]
        pub fn new_uninit_slice_in(len: usize, alloc: A) -> Box<[MaybeUninit<T>], A> {
            this_is_fine(Self::try_new_uninit_slice_in(len, alloc))
        }

        #[track_caller]
        #[inline]
        pub fn new_zeroed_slice_in(len: usize, alloc: A) -> Box<[MaybeUninit<T>], A> {
            this_is_fine(Self::try_new_zeroed_slice_in(len, alloc))
        }

        #[track_caller]
        #[inline]
        pub fn from_slice_copy_in(slice: &[T], alloc: A) -> Box<[T], A>
        where
            T: Copy,
        {
            this_is_fine(Self::try_from_slice_copy_in(slice, alloc))
        }
    }
}

/// allows turning a `Box<T: Sized, A>` into a `Box<U: ?Sized, A>`.
/// std box can do this automatically using the unstable unsize traits.
///
/// NOTE: this is stolen from allocator-api2 crate. thanks.
#[macro_export]
macro_rules! __unsize_box {
    ($boxed:expr $(,)?) => {{
        let (ptr, allocator) = $crate::boxed::Box::into_raw_with_alloc($boxed);
        // NOTE: the compiler *will* allow an unsizing coercion to happen into the `ptr` place, if one is
        // available.
        let ptr: *mut _ = ptr;
        // SAFETY: see above for why ptr's type can only be something that can be safely coerced.
        unsafe { $crate::boxed::Box::from_raw_in(ptr, allocator) }
    }};
}

pub use __unsize_box as unsize_box;
