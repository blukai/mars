use core::error::Error;
use core::fmt;
pub use core::str::Utf8Error;

use allocator_api2::alloc::Global;
use allocator_api2::{alloc::Allocator, vec::Vec};

// TODO: do i really need this?
//   as of this moment this is fragment of an experiment.

#[derive(PartialEq, Eq)]
pub struct FromUtf8Error<A: Allocator> {
    bytes: Vec<u8, A>,
    error: Utf8Error,
}

impl<A: Allocator> Error for FromUtf8Error<A> {}

impl<A: Allocator> fmt::Display for FromUtf8Error<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl<A: Allocator> fmt::Debug for FromUtf8Error<A> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FromUtf8Error")
            .field("bytes", &self.bytes)
            .field("error", &self.error)
            .finish()
    }
}

#[derive(PartialEq, PartialOrd, Eq, Ord)]
pub struct String<A: Allocator = Global> {
    vec: Vec<u8, A>,
}

impl<A: Allocator> String<A> {
    #[inline]
    #[must_use]
    pub const fn new_in(alloc: A) -> Self {
        Self {
            vec: Vec::new_in(alloc),
        }
    }

    #[inline]
    #[must_use]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self {
            vec: Vec::with_capacity_in(capacity, alloc),
        }
    }

    #[inline]
    pub fn from_utf8_in(bytes: Vec<u8, A>) -> Result<Self, FromUtf8Error<A>> {
        match core::str::from_utf8(&bytes) {
            Ok(_) => Ok(String { vec: bytes }),
            Err(error) => Err(FromUtf8Error { bytes, error }),
        }
    }

    #[inline]
    #[must_use]
    pub const unsafe fn from_utf8_unchecked_in(bytes: Vec<u8, A>) -> Self {
        Self { vec: bytes }
    }
}

impl String {
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::new_in(Global)
    }

    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_in(capacity, Global)
    }
}
