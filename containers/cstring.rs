use core::ffi::CStr;
use core::ops;

use alloc::{AllocError, Allocator};

use crate::array::Array;
use crate::arraymemory::{
    ArrayMemory, FixedArrayMemory, GrowableArrayMemory, SpillableArrayMemory,
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
        let mut arr = Array::<u8, M>::new_in(mem.into());
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
}

impl<M: ArrayMemory<u8>> ops::Deref for CString<M> {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        self.as_c_str()
    }
}

// ----
// aliases

#[expect(type_alias_bounds)]
pub type GrowableCString<A: Allocator> = CString<GrowableArrayMemory<u8, A>>;

pub type FixedCString<const N: usize> = CString<FixedArrayMemory<u8, N>>;

impl<const N: usize> FixedCString<N> {
    // ----
    // construct-from

    #[inline]
    pub fn try_from_str(s: &str) -> Result<Self, AllocError> {
        Self::try_from_str_in(s, FixedArrayMemory::default())
    }
}

#[expect(type_alias_bounds)]
pub type SpillableCString<const N: usize, A: Allocator> = CString<SpillableArrayMemory<u8, N, A>>;

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use crate::this_is_fine;

    use super::*;

    impl<M: ArrayMemory<u8>> CString<M> {
        #[inline]
        pub fn from_str_in<I: Into<M>>(s: &str, mem: I) -> Self {
            this_is_fine(Self::try_from_str_in(s, mem))
        }
    }

    impl<const N: usize> FixedCString<N> {
        // ----
        // construct-from

        #[inline]
        pub fn from_str(s: &str) -> Self {
            Self::from_str_in(s, FixedArrayMemory::default())
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
        let c_string = GrowableCString::from_str_in(s, alloc::Global);
        assert_eq!(c_string.as_c_str(), c"udon");
        assert_eq!(c_string.to_bytes_with_nul().len(), s.len() + 1);
    }
}
