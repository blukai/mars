use core::error::Error;
use core::fmt;
use core::marker::PhantomData;
use core::ops;

use allocator_api2::collections::TryReserveError;

/// allows to compute the size and write [`fmt::Arguments`] into a raw buffer.
///
/// writes will not fail if callers write past the capacity of the buffer so that they can compute
/// the size required to fit everything.
///
/// [`fmt::Arguments::estimated_capacity`] is not exposed; nor it or anything else is capable of
/// telling the exact size needed to write [`fmt::Arguments`].
pub struct OverflowingFormatter {
    ptr: *mut u8,
    cap: usize,
    len: usize,
}

impl OverflowingFormatter {
    pub fn empty() -> Self {
        Self {
            ptr: 0 as *mut u8,
            cap: 0,
            len: 0,
        }
    }

    /// SAFETY: memory starting at `buf` and extending for `cap` bytes must be valid for writes.
    pub unsafe fn new(ptr: *mut u8, cap: usize) -> Self {
        Self { ptr, len: 0, cap }
    }

    /// returns the number of bytes written to the buffer this formatter was created from.
    pub fn written(&self) -> usize {
        self.len
    }
}

impl fmt::Write for OverflowingFormatter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // NOTE: this is not bounded by `cap`.
        let len_new = self.len + s.len();
        // NOTE: this ensures we get 0 if we're about to overflow.
        let len_to_copy = core::cmp::min(len_new, self.cap).saturating_sub(self.len);
        if len_to_copy > 0 {
            // SAFETY: `len_to_copy` is non-zero; `pos` has not gone past `end`.
            unsafe {
                core::ptr::copy_nonoverlapping(
                    s.as_bytes().as_ptr(),
                    self.ptr.add(self.len),
                    len_to_copy,
                )
            };
        }
        self.len = len_new;
        Ok(())
    }
}

pub struct Formatter<'a>(OverflowingFormatter, PhantomData<&'a mut ()>);

impl<'a> Formatter<'a> {
    pub fn new(buf: &'a mut [u8]) -> Self {
        Self(
            unsafe { OverflowingFormatter::new(buf.as_mut_ptr(), buf.len()) },
            PhantomData,
        )
    }
}

impl ops::Deref for Formatter<'_> {
    type Target = OverflowingFormatter;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Write for Formatter<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.write_str(s)?;

        // NOTE: here we want to error out if we'll go past the end of the buffer.
        if self.0.len > self.0.cap {
            Err(fmt::Error)
        } else {
            Ok(())
        }
    }
}

#[derive(Debug)]
pub enum FormatError {
    TryReserve(TryReserveError),
    Fmt(fmt::Error),
}

impl Error for FormatError {}

impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TryReserve(e) => fmt::Display::fmt(e, f),
            Self::Fmt(e) => fmt::Display::fmt(e, f),
        }
    }
}
