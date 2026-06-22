use core::ffi::CStr;
use core::{fmt, mem, ops};

use alloc::{AllocError, Allocator};

use crate::array::{
    Array, ArrayMemory, FixedArrayMemory, ResizableArrayMemory, SpillableArrayMemory,
};

// NOTE: for now CString is just a newtype on top of array.
//   possibly it'll grow into something similar to std::ffi::CString.

pub struct CString<M: ArrayMemory<u8>>(pub Array<u8, M>);

impl<M: ArrayMemory<u8>> CString<M> {
    #[inline]
    pub fn as_c_str(&self) -> &CStr {
        unsafe { CStr::from_bytes_with_nul_unchecked(self.0.as_slice()) }
    }

    // ----
    // construct-from

    pub fn try_from_str_in<I: Into<M>>(s: &str, mem: I) -> Result<Self, AllocError> {
        let len = s.len();
        let len_with_nul = len + 1;
        let mut arr = Array::<u8, M>::new_in(mem);
        arr.try_reserve_exact(len_with_nul)?;
        // SAFETY: just reserved needed capacity ^.
        unsafe {
            // TODO: maybe consider making something like Array::extend_from_slice_copy_unchecked?
            let ptr = arr.as_mut_ptr();
            ptr.copy_from_nonoverlapping(s.as_ptr(), len);
            ptr.add(len).write(b'\0');
            arr.set_len(len_with_nul);

            // TODO: do i want to keep all of these asserts here?
            debug_assert_eq!(arr.len(), len_with_nul);
            debug_assert_eq!(&arr[..len_with_nul - 1], s.as_bytes());
            debug_assert_eq!(arr[len_with_nul - 1], b'\0');
        }
        Ok(CString(arr))
    }

    pub fn try_from_c_str_in<I: Into<M>>(s: &CStr, mem: I) -> Result<Self, AllocError> {
        let mut arr = Array::new_in(mem);
        arr.try_reserve_exact(s.count_bytes() + 1)?;
        // TODO: it would be nice to have non-capacity checking array methods.
        arr.try_extend_from_slice_copy(s.to_bytes_with_nul())?;
        Ok(Self(arr))
    }
}

impl<M: ArrayMemory<u8>> ops::Deref for CString<M> {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        self.as_c_str()
    }
}

impl<M: ArrayMemory<u8>> fmt::Debug for CString<M> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_c_str(), f)
    }
}

// ----
// aliases

#[expect(type_alias_bounds)]
pub type ResizableCString<A: Allocator> = CString<ResizableArrayMemory<u8, A>>;

impl<A: Allocator> ResizableCString<A> {
    pub fn leak_with_alloc<'a>(self) -> (&'a mut CStr, A) {
        unsafe {
            let (slice, alloc) = self.0.leak_with_alloc();
            (mem::transmute::<&mut [u8], &mut CStr>(slice), alloc)
        }
    }
}

pub type FixedCString<const N: usize> = CString<FixedArrayMemory<u8, N>>;

impl<const N: usize> FixedCString<N> {
    // ----
    // construct-from

    #[inline]
    pub fn try_from_str(s: &str) -> Result<Self, AllocError> {
        Self::try_from_str_in(s, FixedArrayMemory::default())
    }

    #[inline]
    pub fn try_from_c_str(s: &CStr) -> Result<Self, AllocError> {
        Self::try_from_c_str_in(s, FixedArrayMemory::default())
    }
}

#[expect(type_alias_bounds)]
pub type SpillableCString<const N: usize, A: Allocator> = CString<SpillableArrayMemory<u8, N, A>>;

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::this_is_fine;

    use super::*;

    impl<M: ArrayMemory<u8>> CString<M> {
        // ----
        // construct-from

        #[inline]
        pub fn from_str_in<I: Into<M>>(s: &str, mem: I) -> Self {
            this_is_fine(Self::try_from_str_in(s, mem))
        }

        #[inline]
        pub fn from_c_str_in<I: Into<M>>(s: &CStr, mem: I) -> Self {
            this_is_fine(Self::try_from_c_str_in(s, mem))
        }
    }

    impl<const N: usize> FixedCString<N> {
        // ----
        // construct-from

        #[inline]
        pub fn from_str(s: &str) -> Self {
            Self::from_str_in(s, FixedArrayMemory::default())
        }

        #[inline]
        pub fn from_c_str(s: &CStr) -> Self {
            Self::from_c_str_in(s, FixedArrayMemory::default())
        }
    }
}

// ----

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_try_from_str() {
        let s = "udon";
        let c_string = ResizableCString::from_str_in(s, alloc::Global);
        assert_eq!(c_string.as_c_str(), c"udon");
        assert_eq!(c_string.to_bytes_with_nul().len(), s.len() + 1);
    }

    #[test]
    fn test_try_from_c_str() {
        let s = c"somen";
        let c_string = ResizableCString::from_c_str_in(s, alloc::Global);
        assert_eq!(c_string.as_c_str(), c"somen");
        assert_eq!(c_string.to_bytes_with_nul().len(), s.count_bytes() + 1);
    }
}
