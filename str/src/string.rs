use core::error::Error;
use core::fmt::{self, Write as _};
use core::marker::PhantomData;
pub use core::str::Utf8Error;
use core::{mem, ops};

use alloc::{Allocator, Global};
use vec::{ReserveError, Vec};

/// allows to compute the size and write [`fmt::Arguments`] into a raw buffer.
///
/// writes will not fail if callers write past the capacity of the buffer so that they can compute
/// the size required to fit everything.
///
/// [`fmt::Arguments::estimated_capacity`] is not exposed; nor it or anything else is capable of
/// telling the exact size needed to write [`fmt::Arguments`].
pub struct RawFormatter {
    ptr: *mut u8,
    cap: usize,
    len: usize,
}

impl RawFormatter {
    pub const fn empty() -> Self {
        Self {
            ptr: 0 as *mut u8,
            cap: 0,
            len: 0,
        }
    }

    /// SAFETY: memory starting at `buf` and extending for `cap` bytes must be valid for writes.
    pub const unsafe fn from_raw_parts(ptr: *mut u8, cap: usize) -> Self {
        Self { ptr, len: 0, cap }
    }

    /// returns the number of bytes written to the buffer this formatter was created from.
    pub const fn written(&self) -> usize {
        self.len
    }
}

impl fmt::Write for RawFormatter {
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

/// allows formatting of [`fmt::Arguments`] into a raw buffer.
pub struct Formatter<'a>(RawFormatter, PhantomData<&'a mut ()>);

impl<'a> Formatter<'a> {
    pub const fn from_raw_parts(ptr: *mut u8, cap: usize) -> Self {
        Self(
            unsafe { RawFormatter::from_raw_parts(ptr, cap) },
            PhantomData,
        )
    }
}

impl ops::Deref for Formatter<'_> {
    type Target = RawFormatter;

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
pub enum FromFmtError {
    Reserve(ReserveError),
    Fmt(fmt::Error),
}

impl Error for FromFmtError {}

impl fmt::Display for FromFmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reserve(e) => fmt::Display::fmt(e, f),
            Self::Fmt(e) => fmt::Display::fmt(e, f),
        }
    }
}

#[cfg_attr(not(no_global_oom_handling), derive(Clone))]
pub struct FromUtf8Error<A: Allocator> {
    bytes: Vec<u8, A>,
    error: Utf8Error,
}

impl<A: Allocator> FromUtf8Error<A> {
    /// returns a slice of [`u8`]s bytes that were attempted to convert to a `String`.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// returns the bytes that were attempted to convert to a `String`.
    pub fn into_bytes(self) -> Vec<u8, A> {
        self.bytes
    }

    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
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

impl<A: Allocator> PartialEq for FromUtf8Error<A> {
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&self.bytes, &other.bytes) && PartialEq::eq(&self.error, &other.error)
    }
}

impl<A: Allocator> Eq for FromUtf8Error<A> {}

/// a utf-8–encoded, growable string.
///
/// a simpler version, a subset of [`std::string::String`] that works with [`Allocator`] trait.
/// api attempts to be (but not always is) compatible with [`std::string::String`].
pub struct String<A: Allocator = Global> {
    vec: Vec<u8, A>,
}

impl<A: Allocator> String<A> {
    #[inline]
    pub const fn new_in(alloc: A) -> Self {
        Self {
            vec: Vec::new_in(alloc),
        }
    }

    #[inline]
    pub const fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.vec.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    #[inline]
    pub const fn as_str(&self) -> &str {
        // SAFETY: String contents are stipulated to be valid utf-8, invalid contents are an error
        // at construction.
        unsafe { str::from_utf8_unchecked(self.vec.as_slice()) }
    }

    #[inline]
    pub const fn as_mut_str(&mut self) -> &mut str {
        // SAFETY: String contents are stipulated to be valid UTF-8, invalid contents are an error
        // at construction.
        unsafe { str::from_utf8_unchecked_mut(self.vec.as_mut_slice()) }
    }

    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        self.vec.as_slice()
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), ReserveError> {
        self.vec.try_reserve(additional)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional)
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), ReserveError> {
        self.vec.try_reserve_exact(additional)
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        self.vec.reserve_exact(additional)
    }

    #[inline]
    pub fn try_with_capacity_in(capacity: usize, alloc: A) -> Result<Self, ReserveError> {
        let vec = Vec::try_with_capacity_in(capacity, alloc)?;
        Ok(Self { vec })
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        match Self::try_with_capacity_in(capacity, alloc) {
            Ok(this) => this,
            Err(err) => vec::handle_reserve_error(err),
        }
    }

    #[inline]
    pub fn from_utf8(vec: Vec<u8, A>) -> Result<Self, FromUtf8Error<A>> {
        match core::str::from_utf8(&vec) {
            Ok(_) => Ok(String { vec }),
            Err(error) => Err(FromUtf8Error { bytes: vec, error }),
        }
    }

    #[inline]
    pub const unsafe fn from_utf8_unchecked(vec: Vec<u8, A>) -> Self {
        Self { vec }
    }

    /// format in two passes; no overallocation.
    ///
    ///   - first pass will write into "void" formatter to compute size;
    ///   - second pass will reserve exact amount of memory and perform the actual write.
    ///
    ///   [`fmt::Arguments`] has no facilities for determining size needed to fit everything.
    pub fn try_from_format_args_in(
        args: fmt::Arguments<'_>,
        alloc: A,
    ) -> Result<Self, FromFmtError> {
        // NOTE: first we'll compute size of the buffer.
        let size = {
            let mut f = RawFormatter::empty();
            f.write_fmt(args).map_err(FromFmtError::Fmt)?;
            f.written()
        };
        let mut buf = Vec::new_in(alloc);
        buf.try_reserve_exact(size).map_err(FromFmtError::Reserve)?;

        let mut f = Formatter::from_raw_parts(buf.as_mut_ptr(), size);
        f.write_fmt(args).map_err(FromFmtError::Fmt)?;

        assert_eq!(size, f.written());
        // SAFETY: `size` number of bytes have been written buf by Formatter.
        unsafe { buf.set_len(size) };

        // SAFETY: formatter replaced everything that is non valid utf8 with replacement char.
        Ok(unsafe { Self::from_utf8_unchecked(buf) })
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_format_args_in(args: fmt::Arguments<'_>, alloc: A) -> Self {
        match Self::try_from_format_args_in(args, alloc) {
            Ok(this) => this,
            Err(FromFmtError::Reserve(err)) => vec::handle_reserve_error(err),
            Err(FromFmtError::Fmt(err)) => panic!("could not format: {err}"),
        }
    }

    pub fn try_from_str_in(s: &str, alloc: A) -> Result<Self, ReserveError> {
        let v = Vec::try_from_slice_in(s.as_bytes(), alloc)?;
        Ok(unsafe { Self::from_utf8_unchecked(v) })
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_str_in(s: &str, alloc: A) -> Self {
        match Self::try_from_str_in(s, alloc) {
            Ok(this) => this,
            Err(err) => vec::handle_reserve_error(err),
        }
    }

    pub fn try_from_char_in(ch: char, alloc: A) -> Result<Self, ReserveError> {
        let mut this = Self::new_in(alloc);
        this.try_push(ch)?;
        Ok(this)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_char_in(ch: char, alloc: A) -> Self {
        match Self::try_from_char_in(ch, alloc) {
            Ok(this) => this,
            Err(err) => vec::handle_reserve_error(err),
        }
    }

    #[inline]
    pub fn try_push_str(&mut self, s: &str) -> Result<(), ReserveError> {
        self.vec.try_extend_from_slice(s.as_bytes())
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn push_str(&mut self, s: &str) {
        if let Err(err) = self.try_push_str(s) {
            vec::handle_reserve_error(err)
        }
    }

    #[inline]
    pub fn try_push(&mut self, ch: char) -> Result<(), ReserveError> {
        let len = self.len();
        let ch_len = ch.len_utf8();
        // TODO(blukai): would it make more sense to reserve_exact?
        self.try_reserve(ch_len)?;
        // SAFETY: just reserved capacity for at least the length needed to encode `ch`.
        unsafe {
            ch.encode_utf8(mem::transmute(self.vec.spare_capacity_mut()));
            self.vec.set_len(len + ch_len);
        }
        Ok(())
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn push(&mut self, ch: char) {
        if let Err(err) = self.try_push(ch) {
            vec::handle_reserve_error(err)
        }
    }

    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe { self.vec.set_len(newlen) };
        Some(ch)
    }

    /// Shortens this `String` to the specified length.
    ///
    /// If `new_len` is greater than or equal to the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    #[inline]
    #[track_caller]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    /// Truncates this `String`, removing all contents.
    ///
    /// While this means the `String` will have a length of zero, it does not
    /// touch its capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear()
    }
}

// global alloc
impl String<Global> {
    #[inline]
    pub const fn new() -> Self {
        Self::new_in(Global)
    }

    #[inline]
    pub fn try_with_capacity(capacity: usize) -> Result<Self, ReserveError> {
        Self::try_with_capacity_in(capacity, Global)
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_in(capacity, Global)
    }

    pub fn try_from_format_args(args: fmt::Arguments) -> Result<Self, FromFmtError> {
        Self::try_from_format_args_in(args, Global)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_format_args(args: fmt::Arguments<'_>) -> Self {
        Self::from_format_args_in(args, Global)
    }

    pub fn try_from_str(s: &str) -> Result<Self, ReserveError> {
        Self::try_from_str_in(s, Global)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_str(s: &str) -> Self {
        Self::from_str_in(s, Global)
    }

    pub fn try_from_char(ch: char) -> Result<Self, ReserveError> {
        Self::try_from_char_in(ch, Global)
    }

    #[cfg(not(no_global_oom_handling))]
    pub fn from_char(ch: char) -> Self {
        Self::from_char_in(ch, Global)
    }
}

impl Default for String<Global> {
    fn default() -> Self {
        String::new()
    }
}

impl<A: Allocator> ops::Deref for String<A> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<A: Allocator> ops::DerefMut for String<A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<A: Allocator> AsRef<str> for String<A> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<A: Allocator> AsRef<[u8]> for String<A> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<A: Allocator> AsRef<std::ffi::OsStr> for String<A> {
    #[inline]
    fn as_ref(&self) -> &std::ffi::OsStr {
        (&**self).as_ref()
    }
}

impl<A: Allocator> AsRef<std::path::Path> for String<A> {
    #[inline]
    fn as_ref(&self) -> &std::path::Path {
        std::path::Path::new(self)
    }
}

macro_rules! impl_partial_eq {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty $(where $ty:ty: $bound:ident)?) => {
        impl<$($vars)*> PartialEq<$rhs> for $lhs
        where
            $($ty: $bound)?
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { self[..] == other[..] }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool { self[..] != other[..] }
        }
    }
}

impl_partial_eq! { [A1: Allocator, A2: Allocator] String<A1>, String<A2> }
impl_partial_eq! { [A: Allocator] String<A>, &str }
impl_partial_eq! { [A: Allocator] String<A>, std::string::String }
impl_partial_eq! { [A: Allocator] &str, String<A> }
impl_partial_eq! { [A: Allocator] std::string::String, String<A> }

impl<A: Allocator> fmt::Debug for String<A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<A: Allocator> fmt::Display for String<A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<A: Allocator> fmt::Write for String<A> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).map_err(|_| fmt::Error)
    }

    #[inline]
    fn write_char(&mut self, c: char) -> std::fmt::Result {
        self.try_push(c).map_err(|_| fmt::Error)
    }
}

#[macro_export]
macro_rules! format {
    (try in $alloc:expr, $($arg:tt)*) => {
        $crate::String::try_from_format_args_in(format_args!($($arg)*), $alloc)
    };
    (try, $($arg:tt)*) => {
        $crate::String::try_from_format_args(format_args!($($arg)*))
    };
    (in $alloc:expr, $($arg:tt)*) => {
        $crate::String::from_format_args_in(format_args!($($arg)*), $alloc)
    };
    ($($arg:tt)*) => {
        $crate::String::from_format_args(format_args!($($arg)*))
    };
}

#[test]
fn test_format_macro() {
    let mut talloc_data = [core::mem::MaybeUninit::<u8>::uninit(); 1000];
    let talloc = alloc::TempAllocator::new(&mut talloc_data);

    let expected = std::format!("hello, {who}! {:.4}", 42.69, who = "sailor");
    let actual = format!(try in &talloc, "hello, {who}! {:.4}", 42.69, who = "sailor").unwrap();
    assert_eq!(expected, actual);
}
