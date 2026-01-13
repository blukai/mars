use core::ffi::CStr;
use core::ops;

use crate::array::Array;
use crate::arraymemory::ArrayMemory;

// NOTE: for now CString is just a newtype on top of vector.
//   possibly it'll grow into something similar to std::ffi::CString.

pub struct CString<M: ArrayMemory<u8>>(pub Array<u8, M>);

impl<M: ArrayMemory<u8>> CString<M> {
    #[inline]
    pub fn as_c_str(&self) -> &CStr {
        unsafe { CStr::from_bytes_with_nul_unchecked(self.0.as_slice()) }
    }
}

impl<M: ArrayMemory<u8>> ops::Deref for CString<M> {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        self.as_c_str()
    }
}
