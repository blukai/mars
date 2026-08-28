use core::error::Error;
use core::ffi::CStr;
use core::fmt::{self, Write as _};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
pub use core::str::Utf8Error;
use core::{borrow, cmp, mem, ops, ptr, slice};
use std::mem::MaybeUninit;

use alloc::{AllocError, Allocator};

use crate::array::{
    Array, ArrayMemory, FixedArrayMemory, InsertError, ResizableArrayMemory, SpillableArrayMemory,
    try_range_from_bounds,
};
use crate::boxed::Box;

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
    pub const unsafe fn from_raw_parts(ptr: *mut u8, cap: usize) -> Self {
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
    // MAYBE: rename Alloc to OutOfMemory?
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

pub struct FromUtf8Error<M: ArrayMemory<u8>> {
    bytes: Array<u8, M>,
    error: Utf8Error,
}

impl<M: ArrayMemory<u8>> FromUtf8Error<M> {
    /// returns a slice of [`u8`]s bytes that were attempted to convert to a `String`.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// returns the bytes that were attempted to convert to a `String`.
    pub fn into_bytes(self) -> Array<u8, M> {
        self.bytes
    }

    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl<M: ArrayMemory<u8>> Error for FromUtf8Error<M> {}

impl<M: ArrayMemory<u8>> fmt::Display for FromUtf8Error<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl<M: ArrayMemory<u8>> fmt::Debug for FromUtf8Error<M> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FromUtf8Error")
            .field("bytes", &self.bytes)
            .field("error", &self.error)
            .finish()
    }
}

impl<M: ArrayMemory<u8>> PartialEq for FromUtf8Error<M> {
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&self.bytes, &other.bytes) && PartialEq::eq(&self.error, &other.error)
    }
}

impl<M: ArrayMemory<u8>> Eq for FromUtf8Error<M> {}

pub struct String<M: ArrayMemory<u8>>(Array<u8, M>);

const _: () = {
    let this = size_of::<String<ResizableArrayMemory<u8, alloc::Global>>>();
    let std = size_of::<std::string::String>();
    assert!(this <= std)
};

impl<M: ArrayMemory<u8>> String<M> {
    #[inline]
    pub fn new_in<I: Into<M>>(mem: I) -> Self {
        Self(Array::new_in(mem))
    }

    #[inline]
    pub fn memory(&self) -> &M {
        self.0.memory()
    }

    #[inline]
    pub fn cap(&self) -> usize {
        self.0.cap()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// SAFETY: new_len must be less than or equal to capacity.
    /// the items at old_len..new_len must be initialized.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.cap());
        unsafe { self.0.set_len(new_len) };
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: contents are stipulated to be valid utf-8, invalid contents are an error at
        // construction.
        unsafe { str::from_utf8_unchecked(self.0.as_slice()) }
    }

    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        // SAFETY: contents are stipulated to be valid UTF-8, invalid contents are an error at
        // construction.
        unsafe { str::from_utf8_unchecked_mut(self.0.as_mut_slice()) }
    }

    #[inline]
    pub fn try_reserve_amortized(&mut self, additional: usize) -> Result<(), AllocError> {
        self.0.try_reserve_amortized(additional)
    }

    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), AllocError> {
        self.0.try_reserve_exact(additional)
    }

    #[inline]
    pub fn try_push_str(&mut self, s: &str) -> Result<(), AllocError> {
        self.0.try_extend_from_slice_copy(s.as_bytes())
    }

    #[inline]
    pub fn try_push_char(&mut self, c: char) -> Result<(), AllocError> {
        let len = self.len();
        let char_len = c.len_utf8();
        self.try_reserve_amortized(char_len)?;
        // SAFETY: just reserved capacity for at least the length needed to encode `ch`.
        unsafe {
            c.encode_utf8(mem::transmute(self.0.spare_cap_mut()));
            self.0.set_len(len + char_len);
        }
        Ok(())
    }

    pub fn pop(&mut self) -> Option<char> {
        let c = self.chars().next_back()?;
        let new_len = self.len() - c.len_utf8();
        unsafe { self.0.set_len(new_len) };
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
            self.0.truncate(new_len)
        }
    }

    /// Truncates this `String`, removing all contents.
    ///
    /// While this means the `String` will have a length of zero, it does not
    /// touch its capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.0.clear()
    }

    #[inline]
    pub fn try_insert_str<'a>(
        &mut self,
        index: usize,
        s: &'a str,
    ) -> Result<(), InsertError<&'a str>> {
        assert!(self.is_char_boundary(index));

        let len = self.len();
        if index > self.len() {
            return Err(InsertError::new_oob(index, len, s));
        }

        let s_len = s.len();
        if let Err(alloc_error) = self.try_reserve_amortized(s_len) {
            return Err(InsertError::new_oom(alloc_error, s));
        }

        unsafe {
            ptr::copy(
                self.as_ptr().add(index),
                self.as_mut_ptr().add(index + s_len),
                len - index,
            );
            ptr::copy_nonoverlapping(s.as_ptr(), self.as_mut_ptr().add(index), s_len);
            self.set_len(len + s_len);
        }

        Ok(())
    }

    #[inline]
    pub fn try_insert_char(&mut self, index: usize, c: char) -> Result<(), InsertError<char>> {
        let mut buf = const { MaybeUninit::<[u8; size_of::<char>()]>::uninit() };
        let s = unsafe { c.encode_utf8(buf.assume_init_mut()) };
        match self.try_insert_str(index, s) {
            Ok(()) => Ok(()),
            Err(InsertError { kind, .. }) => Err(InsertError { kind, value: c }),
        }
    }

    /// Removes the specified range in the string, and replaces it with the given string. The given
    /// string doesn't need to be the same length as the range.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is bounded on either end
    /// and does not lie on a [`char`] boundary.
    pub fn try_replace_range<R>(&mut self, range: R, replacement: &str) -> Result<(), AllocError>
    where
        R: ops::RangeBounds<usize>,
    {
        let len = self.len();
        let ops::Range { start, end } = try_range_from_bounds(range, ..len).expect("invalid range");

        assert!(
            self.is_char_boundary(start),
            "start of range should be a character boundary"
        );
        assert!(
            self.is_char_boundary(end),
            "end of range should be a character boundary"
        );

        let range_len = end - start;
        let replacement_len = replacement.len();
        let tail_len = len - end;
        if replacement_len > range_len {
            self.try_reserve_amortized(replacement_len - range_len)?;
        }

        unsafe {
            if range_len != replacement_len {
                ptr::copy(
                    self.as_ptr().add(end),
                    self.as_mut_ptr().add(start + replacement_len),
                    tail_len,
                );
            }
            ptr::copy_nonoverlapping(
                replacement.as_ptr(),
                self.as_mut_ptr().add(start),
                replacement_len,
            );
            self.set_len(start + replacement_len + tail_len);
        }

        Ok(())
    }

    // ----
    // cstr

    /// SAFETY: the length must be less than the capacity.
    ///
    /// Note that mutable borrow is needed because terminating nul byte `\0` needs to be written
    /// into spare capacity; with that said - length will not be increased, CStr will be
    /// constructed with bytes 0..len + 1.
    #[inline]
    pub unsafe fn as_c_str_within_cap_unchecked(&mut self) -> &CStr {
        // SAFETY: by the safety requirements len < cap.
        //
        // NOTE: can't rely on Array::push_within_cap* because that increases length - we don't
        // what that.
        unsafe {
            let ptr = self.0.as_mut_ptr();
            let len = self.0.len();
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

    // ----
    // construct-from

    #[inline]
    pub const unsafe fn from_utf8_unchecked(data: Array<u8, M>) -> Self {
        Self(data)
    }

    #[inline]
    pub fn try_from_utf8(data: Array<u8, M>) -> Result<Self, FromUtf8Error<M>> {
        match core::str::from_utf8(data.as_slice()) {
            Ok(_) => Ok(unsafe { Self::from_utf8_unchecked(data) }),
            Err(error) => Err(FromUtf8Error { bytes: data, error }),
        }
    }

    #[inline]
    pub fn try_from_str_in<I: Into<M>>(s: &str, mem: I) -> Result<Self, AllocError> {
        let mut arr = Array::new_in(mem);
        arr.try_reserve_exact(s.len())?;
        arr.try_extend_from_slice_copy(s.as_bytes())?;
        Ok(Self(arr))
    }

    /// format in two passes; no overallocation.
    ///
    ///   - first pass will write into "void" formatter to compute size;
    ///   - second pass will reserve exact amount of memory and perform the actual write.
    ///
    ///   [`fmt::Arguments`] has no facilities for determining size needed to fit everything.
    pub fn try_from_format_args_in<I: Into<M>>(
        args: fmt::Arguments<'_>,
        mem: I,
    ) -> Result<Self, FromFmtError> {
        // NOTE: first we'll compute size of the buffer.
        let size = {
            let mut f = RawFormatter::empty();
            f.write_fmt(args).map_err(FromFmtError::Fmt)?;
            f.written()
        };

        let mut arr = Array::new_in(mem);
        arr.try_reserve_exact(size).map_err(FromFmtError::Alloc)?;
        {
            let mut f = unsafe { Formatter::from_raw_parts(arr.as_mut_ptr(), size) };
            f.write_fmt(args).map_err(FromFmtError::Fmt)?;
            assert_eq!(size, f.written());
        }
        // SAFETY: `size` number of bytes have been written buf by Formatter.
        unsafe { arr.set_len(size) };
        Ok(Self(arr))
    }
}

impl<M: ArrayMemory<u8>> ops::Deref for String<M> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<M: ArrayMemory<u8>> ops::DerefMut for String<M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

// NOTE: borrow is needed for SortedArraySet/Map, and for HashMap
//   this allows you to get by &str with keys being FixedString or whatever.

impl<M: ArrayMemory<u8>> borrow::Borrow<str> for String<M> {
    #[inline]
    fn borrow(&self) -> &str {
        &self[..]
    }
}

impl<M: ArrayMemory<u8>> borrow::BorrowMut<str> for String<M> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        &mut self[..]
    }
}

// NOTE: i removed couple of AsRef (for str, path, osstr and whatnot)
//   i don't remember why i added those, i clearly don't need them.

impl<M: ArrayMemory<u8> + Default> Default for String<M> {
    #[inline]
    fn default() -> Self {
        Self::new_in(M::default())
    }
}

impl<M: ArrayMemory<u8>> fmt::Debug for String<M> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<M: ArrayMemory<u8>> fmt::Display for String<M> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<M: ArrayMemory<u8>> fmt::Write for String<M> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).map_err(|_| fmt::Error)
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
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
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
        }
    }
}

impl_partial_eq! { [M1: ArrayMemory<u8>, M2: ArrayMemory<u8>] String<M1>, String<M2> }

impl_partial_eq! { [M: ArrayMemory<u8>] String<M>, str }
impl_partial_eq! { [M: ArrayMemory<u8>] String<M>, &str }
impl_partial_eq! { [M: ArrayMemory<u8>] String<M>, std::string::String }

impl_partial_eq! { [M: ArrayMemory<u8>] str, String<M> }
impl_partial_eq! { [M: ArrayMemory<u8>] &str, String<M> }
impl_partial_eq! { [M: ArrayMemory<u8>] std::string::String, String<M> }

impl<M: ArrayMemory<u8>> Eq for String<M> {}

impl<M: ArrayMemory<u8>> PartialOrd for String<M> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_str(), other.as_str())
    }
}

impl<M: ArrayMemory<u8>> Ord for String<M> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.as_str(), other.as_str())
    }
}

impl<M: ArrayMemory<u8>> Hash for String<M> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(self.as_str(), state)
    }
}

// ----
// aliases and their makers below

#[expect(type_alias_bounds)]
pub type ResizableString<A: Allocator> = String<ResizableArrayMemory<u8, A>>;

impl<A: Allocator> ResizableString<A> {
    pub fn leak_with_alloc<'a>(self) -> (&'a mut str, A) {
        unsafe {
            let (slice, alloc) = self.0.leak_with_alloc();
            (str::from_utf8_unchecked_mut(slice), alloc)
        }
    }

    pub fn into_boxed_str_assume_full(self) -> Box<str, A> {
        debug_assert_eq!(self.len(), self.cap());
        let boxed_slice = self.0.into_boxed_slice_assume_full();
        let (ptr, alloc) = Box::into_raw_with_alloc(boxed_slice);
        unsafe { Box::from_raw_in(ptr as *mut str, alloc) }
    }

    // pub fn into_boxed_slice_maybe_shrink(self) -> boxed::Box<[T], A> { todo!() }
}

pub type FixedString<const N: usize> = String<FixedArrayMemory<u8, N>>;

const _: () = {
    // NOTE: max len of string + length
    assert!(size_of::<FixedString<16>>() == 16 + size_of::<usize>());
};

impl<const N: usize> FixedString<N> {
    #[inline]
    pub fn new_fixed() -> Self {
        Self::new_in(FixedArrayMemory::default())
    }

    // ----
    // construct-from

    #[inline]
    pub fn try_from_str(s: &str) -> Result<Self, AllocError> {
        Self::try_from_str_in(s, FixedArrayMemory::default())
    }

    #[inline]
    pub fn try_from_format_args(args: fmt::Arguments<'_>) -> Result<Self, FromFmtError> {
        Self::try_from_format_args_in(args, FixedArrayMemory::default())
    }
}

// :TryCloneIn
impl<const N: usize> Clone for FixedString<N> {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY: self is a bunch of u8 and a usize. ok to copy these.
        unsafe { ptr::read(self) }
    }
}

#[expect(type_alias_bounds)]
pub type SpillableString<const N: usize, A: Allocator> = String<SpillableArrayMemory<u8, N, A>>;

impl<const N: usize, A: Allocator> SpillableString<N, A> {
    pub fn is_spilled(&self) -> bool {
        self.0.is_spilled()
    }
}

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::{eek, this_is_fine};

    use super::*;

    impl<M: ArrayMemory<u8>> String<M> {
        #[track_caller]
        #[inline]
        pub fn reserve_exact(&mut self, additional: usize) {
            this_is_fine(self.try_reserve_exact(additional))
        }

        #[track_caller]
        #[inline]
        pub fn reserve_amortized(&mut self, additional: usize) {
            this_is_fine(self.try_reserve_amortized(additional))
        }

        #[track_caller]
        #[inline]
        pub fn push_str(&mut self, s: &str) {
            this_is_fine(self.try_push_str(s))
        }

        #[track_caller]
        #[inline]
        pub fn push_char(&mut self, c: char) {
            this_is_fine(self.try_push_char(c))
        }

        #[track_caller]
        #[inline]
        pub fn insert_str(&mut self, index: usize, s: &str) {
            match self.try_insert_str(index, s) {
                Ok(..) => {}
                Err(err) => err.panic(),
            }
        }

        #[track_caller]
        #[inline]
        pub fn insert_char(&mut self, index: usize, c: char) {
            match self.try_insert_char(index, c) {
                Ok(..) => {}
                Err(err) => err.panic(),
            }
        }

        #[track_caller]
        #[inline]
        pub fn replace_range<R>(&mut self, range: R, replace_with: &str)
        where
            R: ops::RangeBounds<usize>,
        {
            this_is_fine(self.try_replace_range(range, replace_with))
        }

        // ----
        // construct-from

        #[track_caller]
        #[inline]
        pub fn from_str_in<I: Into<M>>(s: &str, mem: I) -> Self {
            this_is_fine(Self::try_from_str_in(s, mem))
        }

        #[track_caller]
        #[inline]
        pub fn from_format_args_in<I: Into<M>>(args: fmt::Arguments<'_>, mem: I) -> Self {
            match Self::try_from_format_args_in(args, mem) {
                Ok(ok) => ok,
                Err(FromFmtError::Alloc(err)) => eek(err),
                Err(FromFmtError::Fmt(err)) => panic!("could not format: {err}"),
            }
        }
    }

    impl<A: Allocator + Clone> Clone for ResizableString<A> {
        fn clone(&self) -> Self {
            Self::from_str_in(self.as_str(), self.0.memory().allocator().clone())
        }
    }

    impl<const N: usize> FixedString<N> {
        // ----
        // construct-from

        #[inline]
        pub fn from_str(s: &str) -> Self {
            Self::from_str_in(s, FixedArrayMemory::default())
        }

        #[inline]
        pub fn from_format_args(args: fmt::Arguments<'_>) -> Self {
            Self::from_format_args_in(args, FixedArrayMemory::default())
        }
    }

    impl<const N: usize, A: Allocator + Clone> Clone for SpillableString<N, A> {
        fn clone(&self) -> Self {
            Self::from_str_in(self.as_str(), self.0.memory().allocator().clone())
        }
    }
}

// ----

// NOTE: i was thinking that i can do the same stupid workaround as in bitarray with macro. but no!
// rust is not happy because there's already a format thing in global scope.
#[macro_export]
macro_rules! format {
    (try in $alloc:expr, $($arg:tt)*) => {
        $crate::string::ResizableString::try_from_format_args_in(format_args!($($arg)*), $alloc)
    };
    (in $alloc:expr, $($arg:tt)*) => {
        $crate::string::ResizableString::from_format_args_in(format_args!($($arg)*), $alloc)
    };
}

// ----

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_macro() {
        let mut temp_data = [0; 1000];
        let temp = alloc::TempAllocator::new(&mut temp_data, &alloc::Global, None);

        let expected = std::format!("hello, {who}! {:.4}", 42.69, who = "sailor");
        let actual = format!(in &temp, "hello, {who}! {:.4}", 42.69, who = "sailor");
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_as_c_str_within_cap() {
        {
            let mut string = ResizableString::from_str_in("somen", alloc::Global);
            assert_eq!(string.as_c_str_within_cap(), None);
        }

        {
            let mut string = ResizableString::new_in(alloc::Global);
            string.reserve_exact(1000);
            string.push_str("soba");
            let c_str = string.as_c_str_within_cap().unwrap();
            assert_eq!(c_str, c"soba");
            assert_eq!(c_str.to_bytes_with_nul().len(), string.len() + 1);
        }
    }

    #[test]
    fn test_into_boxed_str() {
        let xs = ResizableString::from_str_in("hello my name is bob", alloc::Global);
        let ys = xs.into_boxed_str_assume_full();
        assert_eq!(&*ys, "hello my name is bob");
    }

    // ----
    // NOTE: tests that start with test_std_ are stolen from std.

    #[test]
    fn test_std_push_str() {
        let mut s = ResizableString::new_in(alloc::Global);
        s.push_str("");
        assert_eq!(&s[0..], "");
        s.push_str("abc");
        assert_eq!(&s[0..], "abc");
        s.push_str("ประเทศไทย中华Việt Nam");
        assert_eq!(&s[0..], "abcประเทศไทย中华Việt Nam");
    }

    #[test]
    fn test_std_push() {
        let mut data = ResizableString::from_str_in("ประเทศไทย中", alloc::Global);
        data.push_char('华');
        data.push_char('b'); // 1 byte
        data.push_char('¢'); // 2 byte
        data.push_char('€'); // 3 byte
        data.push_char('𤭢'); // 4 byte
        assert_eq!(data, "ประเทศไทย中华b¢€𤭢");
    }

    #[test]
    fn test_std_pop() {
        let mut data = ResizableString::from_str_in("ประเทศไทย中华b¢€𤭢", alloc::Global);
        assert_eq!(data.pop(), Some('𤭢')); // 4 bytes
        assert_eq!(data.pop(), Some('€')); // 3 bytes
        assert_eq!(data.pop(), Some('¢')); // 2 bytes
        assert_eq!(data.pop(), Some('b')); // 1 bytes
        assert_eq!(data.pop(), Some('华'));
        assert_eq!(data, "ประเทศไทย中");
    }

    #[test]
    fn test_std_clear() {
        let mut s = ResizableString::from_str_in("12345", alloc::Global);
        s.clear();
        assert_eq!(s.len(), 0);
        assert_eq!(s, "");
    }

    #[test]
    fn insert() {
        let mut s = ResizableString::from_str_in("foobar", alloc::Global);
        s.insert_char(0, 'ệ');
        assert_eq!(s, "ệfoobar");
        s.insert_char(6, 'ย');
        assert_eq!(s, "ệfooยbar");
    }

    #[test]
    #[should_panic]
    fn insert_bad1() {
        ResizableString::from_str_in("", alloc::Global).insert_char(1, 't');
    }
    #[test]
    #[should_panic]
    fn insert_bad2() {
        ResizableString::from_str_in("ệ", alloc::Global).insert_char(1, 't');
    }

    #[test]
    fn test_std_slicing() {
        let s = ResizableString::from_str_in("foobar", alloc::Global);
        assert_eq!("foobar", &s[..]);
        assert_eq!("foo", &s[..3]);
        assert_eq!("bar", &s[3..]);
        assert_eq!("oob", &s[1..4]);
    }

    #[test]
    fn test_std_replace_range() {
        let mut s = ResizableString::from_str_in("Hello, world!", alloc::Global);
        s.replace_range(7..12, "世界");
        assert_eq!(s, "Hello, 世界!");
    }

    #[test]
    #[should_panic = "start of range should be a character boundary"]
    fn test_std_replace_range_start_char_boundary() {
        let mut s = ResizableString::from_str_in("Hello, 世界!", alloc::Global);
        s.replace_range(8.., "");
    }

    #[test]
    #[should_panic = "end of range should be a character boundary"]
    fn test_std_replace_range_end_char_boundary() {
        let mut s = ResizableString::from_str_in("Hello, 世界!", alloc::Global);
        s.replace_range(..8, "");
    }

    #[test]
    fn test_std_replace_range_inclusive_range() {
        let mut v = ResizableString::from_str_in("12345", alloc::Global);
        v.replace_range(2..=3, "789");
        assert_eq!(v, "127895");
        v.replace_range(1..=2, "A");
        assert_eq!(v, "1A895");
    }

    #[test]
    #[should_panic = "invalid range"]
    // #[should_panic = "range end index 6 out of range for slice of length 5"]
    fn test_std_replace_range_out_of_bounds() {
        let mut s = ResizableString::from_str_in("12345", alloc::Global);
        s.replace_range(5..6, "789");
    }

    #[test]
    #[should_panic = "invalid range"]
    // #[should_panic = "range end index 5 out of range for slice of length 5"]
    fn test_std_replace_range_inclusive_out_of_bounds() {
        let mut s = ResizableString::from_str_in("12345", alloc::Global);
        s.replace_range(5..=5, "789");
    }

    // The overflowed index value is target-dependent,
    // so we don't check for its exact value in the panic message
    #[test]
    #[should_panic = "invalid range"]
    // #[should_panic = "out of range for slice of length 3"]
    fn test_std_replace_range_start_overflow() {
        use std::ops::Bound::*;

        let mut s = ResizableString::from_str_in("123", alloc::Global);
        s.replace_range((Excluded(usize::MAX), Included(0)), "");
    }

    // The overflowed index value is target-dependent,
    // so we don't check for its exact value in the panic message
    #[test]
    #[should_panic = "invalid range"]
    // #[should_panic = "out of range for slice of length 3"]
    fn test_std_replace_range_end_overflow() {
        use std::ops::Bound::*;

        let mut s = ResizableString::from_str_in("456", alloc::Global);
        s.replace_range((Included(0), Included(usize::MAX)), "");
    }

    #[test]
    fn test_std_replace_range_empty() {
        let mut s = ResizableString::from_str_in("12345", alloc::Global);
        s.replace_range(1..2, "");
        assert_eq!(s, "1345");
    }

    #[test]
    fn test_std_replace_range_unbounded() {
        let mut s = ResizableString::from_str_in("12345", alloc::Global);
        s.replace_range(.., "");
        assert_eq!(s, "");
    }

    #[test]
    fn test_std_replace_range_evil_start_bound() {
        use std::cell::Cell;
        use std::ops::{Bound, RangeBounds};

        struct EvilRange(Cell<bool>);

        impl RangeBounds<usize> for EvilRange {
            fn start_bound(&self) -> Bound<&usize> {
                Bound::Included(if self.0.get() {
                    &1
                } else {
                    self.0.set(true);
                    &0
                })
            }
            fn end_bound(&self) -> Bound<&usize> {
                Bound::Unbounded
            }
        }

        let mut s = ResizableString::from_str_in("🦀", alloc::Global);
        s.replace_range(EvilRange(Cell::new(false)), "");
        assert_eq!(Ok(""), str::from_utf8(s.as_bytes()));
    }

    #[test]
    fn test_std_replace_range_evil_end_bound() {
        use std::cell::Cell;
        use std::ops::{Bound, RangeBounds};

        struct EvilRange(Cell<bool>);

        impl RangeBounds<usize> for EvilRange {
            fn start_bound(&self) -> Bound<&usize> {
                Bound::Included(&0)
            }
            fn end_bound(&self) -> Bound<&usize> {
                Bound::Excluded(if self.0.get() {
                    &3
                } else {
                    self.0.set(true);
                    &4
                })
            }
        }

        let mut s = ResizableString::from_str_in("🦀", alloc::Global);
        s.replace_range(EvilRange(Cell::new(false)), "");
        assert_eq!(Ok(""), str::from_utf8(s.as_bytes()));
    }
}
