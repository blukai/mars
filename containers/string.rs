use core::error::Error;
use core::ffi::CStr;
use core::fmt::{self, Write as _};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
pub use core::str::Utf8Error;
use core::{mem, ops, ptr, slice};

use alloc::{AllocError, Allocator};

use crate::cstring::CString;
use crate::memory::{FixedMemory, GrowableMemory, Memory, SpillableMemory};
use crate::vector::Vector;

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
    Alloc(AllocError),
    Fmt(fmt::Error),
}

impl Error for FromFmtError {}

impl fmt::Display for FromFmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Alloc(e) => fmt::Display::fmt(e, f),
            Self::Fmt(e) => fmt::Display::fmt(e, f),
        }
    }
}

pub struct FromUtf8Error<M: Memory<u8>> {
    bytes: Vector<u8, M>,
    error: Utf8Error,
}

impl<M: Memory<u8>> FromUtf8Error<M> {
    /// returns a slice of [`u8`]s bytes that were attempted to convert to a `String`.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// returns the bytes that were attempted to convert to a `String`.
    pub fn into_bytes(self) -> Vector<u8, M> {
        self.bytes
    }

    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl<M: Memory<u8>> Error for FromUtf8Error<M> {}

impl<M: Memory<u8>> fmt::Display for FromUtf8Error<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl<M: Memory<u8>> fmt::Debug for FromUtf8Error<M> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FromUtf8Error")
            .field("bytes", &self.bytes)
            .field("error", &self.error)
            .finish()
    }
}

impl<M: Memory<u8>> PartialEq for FromUtf8Error<M> {
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&self.bytes, &other.bytes) && PartialEq::eq(&self.error, &other.error)
    }
}

impl<M: Memory<u8>> Eq for FromUtf8Error<M> {}

pub struct String<M: Memory<u8>> {
    vec: Vector<u8, M>,
}

const _: () = {
    let this = size_of::<String<GrowableMemory<u8, alloc::Global>>>();
    let std = size_of::<std::string::String>();
    assert!(this <= std)
};

impl<M: Memory<u8>> String<M> {
    #[inline]
    pub fn new_in(mem: M) -> Self {
        Self {
            vec: Vector::new_in(mem),
        }
    }

    #[inline]
    pub fn memory(&self) -> &M {
        &self.vec.memory()
    }

    #[inline]
    pub fn cap(&self) -> usize {
        self.vec.cap()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// SAFETY: new_len must be less than or equal to capacity.
    /// the items at old_len..new_len must be initialized.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.cap());
        unsafe { self.vec.set_len(new_len) };
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: contents are stipulated to be valid utf-8, invalid contents are an error at
        // construction.
        unsafe { str::from_utf8_unchecked(self.vec.as_slice()) }
    }

    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        // SAFETY: contents are stipulated to be valid UTF-8, invalid contents are an error at
        // construction.
        unsafe { str::from_utf8_unchecked_mut(self.vec.as_mut_slice()) }
    }

    #[inline]
    pub fn try_reserve_amortized(&mut self, additional: usize) -> Result<(), AllocError> {
        self.vec.try_reserve_amortized(additional)
    }

    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), AllocError> {
        self.vec.try_reserve_exact(additional)
    }

    #[inline]
    pub fn try_push_str(&mut self, s: &str) -> Result<(), AllocError> {
        self.vec.try_extend_from_slice_copy(s.as_bytes())
    }

    #[inline]
    pub fn try_push_char(&mut self, c: char) -> Result<(), AllocError> {
        let len = self.len();
        let char_len = c.len_utf8();
        // TODO(blukai): would it make more sense to reserve_exact?
        self.try_reserve_amortized(char_len)?;
        // SAFETY: just reserved capacity for at least the length needed to encode `ch`.
        unsafe {
            c.encode_utf8(mem::transmute(self.vec.spare_cap_mut()));
            self.vec.set_len(len + char_len);
        }
        Ok(())
    }

    pub fn pop(&mut self) -> Option<char> {
        let c = self.chars().rev().next()?;
        let new_len = self.len() - c.len_utf8();
        unsafe { self.vec.set_len(new_len) };
        Some(c)
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

    // ----
    // cstr+cstring

    /// SAFETY: the length must be less than the capacity.
    ///
    /// Note that mutable borrow is needed because terminating nul byte `\0` needs to be written
    /// into spare capacity; with that said - length will not be increased, CStr will be
    /// constructed with bytes 0..len + 1.
    #[inline]
    pub unsafe fn as_c_str_within_cap_unchecked(&mut self) -> &CStr {
        // SAFETY: by the safety requirements len < cap.
        //
        // NOTE: can't rely on Vector::push_within_cap* because that increases length - we don't
        // what that.
        unsafe {
            let ptr = self.vec.as_mut_ptr();
            let len = self.vec.len();
            ptr.add(len).write(b'\0');
            let bytes = slice::from_raw_parts(ptr, len + 1);
            CStr::from_bytes_with_nul_unchecked(bytes)
        }
    }

    #[inline]
    pub fn as_c_str_within_cap(&mut self) -> Option<&CStr> {
        if self.len() == self.cap() {
            return None;
        }
        Some(unsafe { self.as_c_str_within_cap_unchecked() })
    }

    // NOTE: my current use case for this is to use this with temporary allocator as a fallback
    // when within cap method fails.
    #[inline]
    pub fn try_to_c_string_in<W: Memory<u8>>(&self, mem: W) -> Result<CString<W>, AllocError> {
        let len = self.len();
        let len_with_nul = len + 1;
        let mut vec = Vector::new_in(mem).try_with_cap(len_with_nul)?;
        // SAFETY: just reserved needed capacity ^.
        unsafe {
            // TODO: maybe consider making something like Vector::extend_from_slice_copy_unchecked?
            let ptr = vec.as_mut_ptr();
            ptr.copy_from_nonoverlapping(self.as_ptr(), len);
            ptr.add(len).write(b'\0');
            vec.set_len(len_with_nul);

            // TODO: do i want to keep all of these asserts here?
            debug_assert_eq!(vec.len(), len_with_nul);
            debug_assert_eq!(&vec[..len_with_nul - 1], self.as_bytes());
            debug_assert_eq!(vec[len_with_nul - 1], b'\0');
        }
        Ok(CString(vec))
    }

    // ----
    // construct-from

    #[inline]
    pub const unsafe fn from_utf8_unchecked(vec: Vector<u8, M>) -> Self {
        Self { vec }
    }

    #[inline]
    pub fn try_from_utf8(vec: Vector<u8, M>) -> Result<Self, FromUtf8Error<M>> {
        match core::str::from_utf8(vec.as_slice()) {
            Ok(_) => Ok(unsafe { Self::from_utf8_unchecked(vec) }),
            Err(error) => Err(FromUtf8Error { bytes: vec, error }),
        }
    }

    // ----
    // builder-lite

    #[inline]
    pub fn try_with_cap(mut self, cap: usize) -> Result<Self, AllocError> {
        // TODO: should with_cap resize (grow/shrink)?
        assert_eq!(self.cap(), 0);
        self.try_reserve_exact(cap)?;
        Ok(self)
    }

    // ----
    // builder-lite with

    #[inline]
    pub fn try_with_str(mut self, s: &str) -> Result<Self, AllocError> {
        self.try_push_str(s)?;
        Ok(self)
    }

    #[inline]
    pub fn try_with_char(mut self, c: char) -> Result<Self, AllocError> {
        self.try_push_char(c)?;
        Ok(self)
    }

    /// format in two passes; no overallocation.
    ///
    ///   - first pass will write into "void" formatter to compute size;
    ///   - second pass will reserve exact amount of memory and perform the actual write.
    ///
    ///   [`fmt::Arguments`] has no facilities for determining size needed to fit everything.
    pub fn try_with_format_args(mut self, args: fmt::Arguments<'_>) -> Result<Self, FromFmtError> {
        // NOTE: first we'll compute size of the buffer.
        let size = {
            let mut f = RawFormatter::empty();
            f.write_fmt(args).map_err(FromFmtError::Fmt)?;
            f.written()
        };
        self.try_reserve_exact(size).map_err(FromFmtError::Alloc)?;

        let mut f = Formatter::from_raw_parts(self.as_mut_ptr(), size);
        f.write_fmt(args).map_err(FromFmtError::Fmt)?;

        assert_eq!(size, f.written());
        // SAFETY: `size` number of bytes have been written buf by Formatter.
        unsafe { self.set_len(size) };

        Ok(self)
    }
}

impl<M: Memory<u8>> ops::Deref for String<M> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<M: Memory<u8>> ops::DerefMut for String<M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<M: Memory<u8>> AsRef<str> for String<M> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<M: Memory<u8>> AsRef<std::ffi::OsStr> for String<M> {
    #[inline]
    fn as_ref(&self) -> &std::ffi::OsStr {
        self.as_str().as_ref()
    }
}

impl<M: Memory<u8>> AsRef<std::path::Path> for String<M> {
    #[inline]
    fn as_ref(&self) -> &std::path::Path {
        std::path::Path::new(self)
    }
}

impl<M: Memory<u8> + Default> Default for String<M> {
    fn default() -> Self {
        Self::new_in(M::default())
    }
}

impl<M: Memory<u8>> fmt::Debug for String<M> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<M: Memory<u8>> fmt::Display for String<M> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<M: Memory<u8>> fmt::Write for String<M> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).map_err(|_| fmt::Error)
    }

    #[inline]
    fn write_char(&mut self, c: char) -> std::fmt::Result {
        self.try_push_char(c).map_err(|_| fmt::Error)
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

impl_partial_eq! { [M1: Memory<u8>, M2: Memory<u8>] String<M1>, String<M2> }

impl_partial_eq! { [M: Memory<u8>] String<M>, str }
impl_partial_eq! { [M: Memory<u8>] String<M>, &str }
impl_partial_eq! { [M: Memory<u8>] String<M>, std::string::String }

impl_partial_eq! { [M: Memory<u8>] str, String<M> }
impl_partial_eq! { [M: Memory<u8>] &str, String<M> }
impl_partial_eq! { [M: Memory<u8>] std::string::String, String<M> }

impl<M: Memory<u8>> Hash for String<M> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(self.as_str(), state)
    }
}

// ----
// aliases and their makers below

#[expect(type_alias_bounds)]
pub type GrowableString<A: Allocator> = String<GrowableMemory<u8, A>>;

impl<A: Allocator> GrowableString<A> {
    #[inline]
    pub fn new_growable_in(alloc: A) -> Self {
        Self::new_in(GrowableMemory::new_in(alloc))
    }
}

pub type FixedString<const N: usize> = String<FixedMemory<u8, N>>;

const _: () = {
    // NOTE: max len of string + length
    assert!(size_of::<FixedString<16>>() == 16 + size_of::<usize>());
};

impl<const N: usize> FixedString<N> {
    #[inline]
    pub fn new_fixed() -> Self {
        Self::new_in(FixedMemory::default())
    }
}

// @TryCloneIn
impl<const N: usize> Clone for FixedString<N> {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY: self is a bunch of u8 and a usize. ok to copy these.
        unsafe { ptr::read(self) }
    }
}

#[expect(type_alias_bounds)]
pub type SpillableString<const N: usize, A: Allocator> = String<SpillableMemory<u8, N, A>>;

impl<const N: usize, A: Allocator> SpillableString<N, A> {
    #[inline]
    pub fn new_spillable_in(alloc: A) -> Self {
        Self::new_in(SpillableMemory::new_in(alloc))
    }

    #[inline]
    pub fn is_spilled(&self) -> bool {
        self.vec.is_spilled()
    }
}

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use crate::{eek, this_is_fine};

    use super::*;

    impl<M: Memory<u8>> String<M> {
        #[inline]
        pub fn reserve_exact(&mut self, additional: usize) {
            this_is_fine(self.try_reserve_exact(additional))
        }

        #[inline]
        pub fn reserve_amortized(&mut self, additional: usize) {
            this_is_fine(self.try_reserve_amortized(additional))
        }

        #[inline]
        pub fn push_str(&mut self, s: &str) {
            this_is_fine(self.try_push_str(s))
        }

        #[inline]
        pub fn push_char(&mut self, c: char) {
            this_is_fine(self.try_push_char(c))
        }

        // ----
        // cstr+cstring

        #[inline]
        pub fn to_c_string_in<W: Memory<u8>>(&self, mem: W) -> CString<W> {
            this_is_fine(self.try_to_c_string_in(mem))
        }

        // ----
        // builder-lite

        #[inline]
        pub fn with_cap(self, cap: usize) -> Self {
            this_is_fine(self.try_with_cap(cap))
        }

        // ----
        // builder-lite with

        #[inline]
        pub fn with_str(self, s: &str) -> Self {
            this_is_fine(self.try_with_str(s))
        }

        #[inline]
        pub fn with_char(self, c: char) -> Self {
            this_is_fine(self.try_with_char(c))
        }

        #[inline]
        pub fn with_format_args(self, args: fmt::Arguments<'_>) -> Self {
            match self.try_with_format_args(args) {
                Ok(ok) => ok,
                Err(FromFmtError::Alloc(err)) => eek(err),
                Err(FromFmtError::Fmt(err)) => panic!("could not format: {err}"),
            }
        }
    }

    impl<A: Allocator + Clone> Clone for GrowableString<A> {
        fn clone(&self) -> Self {
            Self::new_growable_in(self.vec.memory().allocator().clone()).with_str(self)
        }
    }

    impl<const N: usize, A: Allocator + Clone> Clone for SpillableString<N, A> {
        fn clone(&self) -> Self {
            Self::new_spillable_in(self.vec.memory().allocator().clone()).with_str(self)
        }
    }
}

// ----

#[macro_export]
macro_rules! format {
    (try in $alloc:expr, $($arg:tt)*) => {
        $crate::string::String::try_from_format_args_in(
            format_args!($($arg)*),
            $crate::memory::GrowableMemory::new_in($alloc),
        )
    };
    (in $alloc:expr, $($arg:tt)*) => {
        $crate::string::String::new_in($crate::memory::GrowableMemory::new_in($alloc))
            .with_format_args(format_args!($($arg)*))
    };
}

// ----

#[cfg(test)]
mod tests {
    use crate::memory::GrowableMemory;

    use super::*;

    #[test]
    fn test_format_macro() {
        let mut temp_data = [0; 1000];
        let temp = alloc::TempAllocator::new(&mut temp_data);

        let expected = std::format!("hello, {who}! {:.4}", 42.69, who = "sailor");
        let actual = format!(in &temp, "hello, {who}! {:.4}", 42.69, who = "sailor");
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_as_c_str_within_cap() {
        {
            let mut string = String::new_growable_in(alloc::Global).with_str("somen");
            assert_eq!(string.as_c_str_within_cap(), None);
        }

        {
            let mut string = String::new_growable_in(alloc::Global)
                .with_cap(1000)
                .with_str("soba");
            let c_str = string.as_c_str_within_cap().unwrap();
            assert_eq!(c_str, c"soba");
            assert_eq!(c_str.to_bytes_with_nul().len(), string.len() + 1);
        }
    }

    #[test]
    fn test_try_to_c_string() {
        let string = String::new_growable_in(alloc::Global).with_str("udon");
        let c_string = string
            .try_to_c_string_in(GrowableMemory::new_in(alloc::Global))
            .unwrap();
        assert_eq!(c_string.as_c_str(), c"udon");
        assert_eq!(c_string.to_bytes_with_nul().len(), string.len() + 1);
    }

    // ----
    // NOTE: tests that start with test_std_ are stolen from std.

    #[test]
    fn test_std_push_str() {
        let mut s = String::new_in(GrowableMemory::new_in(alloc::Global));
        s.push_str("");
        assert_eq!(&s[0..], "");
        s.push_str("abc");
        assert_eq!(&s[0..], "abc");
        s.push_str("ประเทศไทย中华Việt Nam");
        assert_eq!(&s[0..], "abcประเทศไทย中华Việt Nam");
    }

    #[test]
    fn test_std_push() {
        let mut data =
            String::new_in(GrowableMemory::new_in(alloc::Global)).with_str("ประเทศไทย中");
        data.push_char('华');
        data.push_char('b'); // 1 byte
        data.push_char('¢'); // 2 byte
        data.push_char('€'); // 3 byte
        data.push_char('𤭢'); // 4 byte
        assert_eq!(data, "ประเทศไทย中华b¢€𤭢");
    }

    #[test]
    fn test_std_pop() {
        let mut data =
            String::new_in(GrowableMemory::new_in(alloc::Global)).with_str("ประเทศไทย中华b¢€𤭢");
        assert_eq!(data.pop(), Some('𤭢')); // 4 bytes
        assert_eq!(data.pop(), Some('€')); // 3 bytes
        assert_eq!(data.pop(), Some('¢')); // 2 bytes
        assert_eq!(data.pop(), Some('b')); // 1 bytes
        assert_eq!(data.pop(), Some('华'));
        assert_eq!(data, "ประเทศไทย中");
    }

    #[test]
    fn test_std_clear() {
        let mut s = String::new_in(GrowableMemory::new_in(alloc::Global)).with_str("12345");
        s.clear();
        assert_eq!(s.len(), 0);
        assert_eq!(s, "");
    }

    #[test]
    fn test_std_slicing() {
        let s = String::new_in(GrowableMemory::new_in(alloc::Global)).with_str("foobar");
        assert_eq!("foobar", &s[..]);
        assert_eq!("foo", &s[..3]);
        assert_eq!("bar", &s[3..]);
        assert_eq!("oob", &s[1..4]);
    }
}
