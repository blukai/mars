//! NOTE: this is a partial copy of unstable std bstr.

// $ find ./library -name "bstr*"
// ./library/alloc/src/bstr.rs
// ./library/core/src/bstr
// ./library/coretests/tests/bstr.rs
// ./library/std/src/bstr.rs

use core::error::Error;
use core::fmt::{self, Write as _};
use core::hash;
use core::marker::PhantomData;
use core::ops;

use allocator_api2::collections::TryReserveError;
use allocator_api2::{
    alloc::{Allocator, Global},
    vec::Vec,
};

// ----
// impl macros for ByteStr and ByteString.

macro_rules! impl_partial_eq {
    ([$($vars:tt)*], $lhs:ty, $rhs:ty) => {
        impl<$($vars)*> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(<$lhs as AsRef<[u8]>>::as_ref(self), <$rhs as AsRef<[u8]>>::as_ref(other))
            }
        }
    };
}

macro_rules! impl_partial_ord {
    ([$($vars:tt)*], $lhs:ty, $rhs:ty) => {
        impl<'a, $($vars)*> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<core::cmp::Ordering> {
                PartialOrd::partial_cmp(<$lhs as AsRef<[u8]>>::as_ref(self), <$rhs as AsRef<[u8]>>::as_ref(other))
            }
        }
    };
}

macro_rules! impl_index {
    ([$($vars:tt)*], $this:ty,  $idx:ty) => {
        impl<$($vars)*> ops::Index<$idx> for $this {
            type Output = [u8];

            #[inline]
            fn index(&self, index: $idx) -> &Self::Output {
                ops::Index::<$idx>::index(&self.0, index)
            }
        }

        impl<$($vars)*> ops::IndexMut<$idx> for $this {
            #[inline]
            fn index_mut(&mut self, index: $idx) -> &mut Self::Output {
                ops::IndexMut::<$idx>::index_mut(&mut self.0, index)
            }
        }
    };
}

/// A wrapper for `&[u8]` representing a human-readable string that's conventionally, but not
/// always, UTF-8.
///
/// Unlike `&str`, this type permits non-UTF-8 contents, making it suitable for user input,
/// non-native filenames (as `Path` only supports native filenames), and other applications that
/// need to round-trip whatever data the user provides.
///
/// For an owned, growable byte string buffer, use
/// [`crate::ByteString`].
///
/// `ByteStr` implements `Deref` to `[u8]`, so all methods available on `[u8]` are available on
/// `ByteStr`.
///
/// # Representation
///
/// A `&ByteStr` has the same representation as a `&str`. That is, a `&ByteStr` is a wide pointer
/// which includes a pointer to some bytes and a length.
///
/// # Trait implementations
///
/// The `ByteStr` type has a number of trait implementations, and in particular, defines equality
/// and comparisons between `&ByteStr`, `&str`, and `&[u8]`, for convenience.
///
/// The `Debug` implementation for `ByteStr` shows its bytes as a normal string, with invalid UTF-8
/// presented as hex escape sequences.
///
/// The `Display` implementation behaves as if the `ByteStr` were first lossily converted to a
/// `str`, with invalid UTF-8 presented as the Unicode replacement character (�).
#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct ByteStr(pub [u8]);

impl ByteStr {
    #[inline]
    pub const fn from_bytes(slice: &[u8]) -> &Self {
        // SAFETY: `ByteStr` is a transparent wrapper around `[u8]`, so we can turn a reference to
        // the wrapped type into a reference to the wrapper type.
        unsafe { &*(slice as *const [u8] as *const Self) }
    }

    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl ops::Deref for ByteStr {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        &self.0
    }
}

impl ops::DerefMut for ByteStr {
    #[inline]
    fn deref_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl AsRef<[u8]> for ByteStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsRef<ByteStr> for ByteStr {
    #[inline]
    fn as_ref(&self) -> &ByteStr {
        self
    }
}

impl fmt::Debug for ByteStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"")?;
        for chunk in self.utf8_chunks() {
            for c in chunk.valid().chars() {
                match c {
                    '\0' => write!(f, "\\0")?,
                    '\x01'..='\x7f' => write!(f, "{}", (c as u8).escape_ascii())?,
                    _ => write!(f, "{}", c.escape_debug())?,
                }
            }
            write!(f, "{}", chunk.invalid().escape_ascii())?;
        }
        write!(f, "\"")?;
        Ok(())
    }
}

impl fmt::Display for ByteStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_nopad(this: &ByteStr, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            for chunk in this.utf8_chunks() {
                f.write_str(chunk.valid())?;
                if !chunk.invalid().is_empty() {
                    f.write_str("\u{FFFD}")?;
                }
            }
            Ok(())
        }

        let Some(align) = f.align() else {
            return fmt_nopad(self, f);
        };
        let nchars: usize = self
            .utf8_chunks()
            .map(|chunk| {
                chunk.valid().chars().count() + if chunk.invalid().is_empty() { 0 } else { 1 }
            })
            .sum();
        let padding = f.width().unwrap_or(0).saturating_sub(nchars);
        let fill = f.fill();
        let (lpad, rpad) = match align {
            fmt::Alignment::Left => (0, padding),
            fmt::Alignment::Right => (padding, 0),
            fmt::Alignment::Center => {
                let half = padding / 2;
                (half, half + padding % 2)
            }
        };
        for _ in 0..lpad {
            write!(f, "{fill}")?;
        }
        fmt_nopad(self, f)?;
        for _ in 0..rpad {
            write!(f, "{fill}")?;
        }

        Ok(())
    }
}

impl<'a> Default for &'a ByteStr {
    fn default() -> Self {
        ByteStr::from_bytes(b"")
    }
}

impl_partial_eq!([], ByteStr, &[u8]);
impl_partial_eq!([], ByteStr, &str);
impl_partial_eq!([], &[u8], ByteStr);
impl_partial_eq!([], &str, ByteStr);

impl ops::Index<usize> for ByteStr {
    type Output = u8;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        ops::Index::<usize>::index(&self.0, index)
    }
}

impl ops::IndexMut<usize> for ByteStr {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        ops::IndexMut::<usize>::index_mut(&mut self.0, index)
    }
}

impl_index!([], ByteStr, ops::Range<usize>);
impl_index!([], ByteStr, ops::RangeFrom<usize>);
impl_index!([], ByteStr, ops::RangeFull);
impl_index!([], ByteStr, ops::RangeInclusive<usize>);
impl_index!([], ByteStr, ops::RangeTo<usize>);
impl_index!([], ByteStr, ops::RangeToInclusive<usize>);

impl hash::Hash for ByteStr {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<'a> TryFrom<&'a ByteStr> for &'a str {
    type Error = core::str::Utf8Error;

    #[inline]
    fn try_from(s: &'a ByteStr) -> Result<Self, Self::Error> {
        core::str::from_utf8(&s.0)
    }
}

#[test]
fn test_debug() {
    assert_eq!(
        r#""\0\x01\x02\x03\x04\x05\x06\x07\x08\t\n\x11\x12\r\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f \x7f\x80\x81\xfe\xff""#,
        format!("{:?}", ByteStr::from_bytes(b"\0\x01\x02\x03\x04\x05\x06\x07\x08\t\n\x11\x12\r\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f \x7f\x80\x81\xfe\xff")),
    );
}

#[test]
fn test_display() {
    let b1 = ByteStr::from_bytes(b"abc");
    let b2 = ByteStr::from_bytes(b"\xf0\x28\x8c\xbc");

    assert_eq!(&format!("{b1}"), "abc");
    assert_eq!(&format!("{b2}"), "�(��");

    assert_eq!(&format!("{b1:<7}!"), "abc    !");
    assert_eq!(&format!("{b1:>7}!"), "    abc!");
    assert_eq!(&format!("{b1:^7}!"), "  abc  !");
    assert_eq!(&format!("{b1:^6}!"), " abc  !");
    assert_eq!(&format!("{b1:-<7}!"), "abc----!");
    assert_eq!(&format!("{b1:->7}!"), "----abc!");
    assert_eq!(&format!("{b1:-^7}!"), "--abc--!");
    assert_eq!(&format!("{b1:-^6}!"), "-abc--!");

    assert_eq!(&format!("{b2:<7}!"), "�(��   !");
    assert_eq!(&format!("{b2:>7}!"), "   �(��!");
    assert_eq!(&format!("{b2:^7}!"), " �(��  !");
    assert_eq!(&format!("{b2:^6}!"), " �(�� !");
    assert_eq!(&format!("{b2:-<7}!"), "�(��---!");
    assert_eq!(&format!("{b2:->7}!"), "---�(��!");
    assert_eq!(&format!("{b2:-^7}!"), "-�(��--!");
    assert_eq!(&format!("{b2:-^6}!"), "-�(��-!");

    assert_eq!(&format!("{b1:<2}!"), "abc!");
    assert_eq!(&format!("{b1:>2}!"), "abc!");
    assert_eq!(&format!("{b1:^2}!"), "abc!");
    assert_eq!(&format!("{b1:-<2}!"), "abc!");
    assert_eq!(&format!("{b1:->2}!"), "abc!");
    assert_eq!(&format!("{b1:-^2}!"), "abc!");

    assert_eq!(&format!("{b2:<3}!"), "�(��!");
    assert_eq!(&format!("{b2:>3}!"), "�(��!");
    assert_eq!(&format!("{b2:^3}!"), "�(��!");
    assert_eq!(&format!("{b2:^2}!"), "�(��!");
    assert_eq!(&format!("{b2:-<3}!"), "�(��!");
    assert_eq!(&format!("{b2:->3}!"), "�(��!");
    assert_eq!(&format!("{b2:-^3}!"), "�(��!");
    assert_eq!(&format!("{b2:-^2}!"), "�(��!");
}

/// A wrapper for `Vec<u8>` representing a human-readable string that's conventionally, but not
/// always, UTF-8.
///
/// Unlike `String`, this type permits non-UTF-8 contents, making it suitable for user input,
/// non-native filenames (as `Path` only supports native filenames), and other applications that
/// need to round-trip whatever data the user provides.
///
/// A `ByteString` owns its contents and can grow and shrink, like a `Vec` or `String`. For a
/// borrowed byte string, see [`crate::ByteStr`].
///
/// `ByteString` implements `Deref` to `&Vec<u8>`, so all methods available on `&Vec<u8>` are
/// available on `ByteString`. Similarly, `ByteString` implements `DerefMut` to `&mut Vec<u8>`,
/// so you can modify a `ByteString` using any method available on `&mut Vec<u8>`.
///
/// The `Debug` and `Display` implementations for `ByteString` are the same as those for `ByteStr`,
/// showing invalid UTF-8 as hex escapes or the Unicode replacement character, respectively.
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ByteString<A: Allocator = Global>(pub Vec<u8, A>);

impl<A: Allocator> ops::Deref for ByteString<A> {
    type Target = Vec<u8, A>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<A: Allocator> ops::DerefMut for ByteString<A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<A: Allocator> AsRef<[u8]> for ByteString<A> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<A: Allocator> AsRef<ByteStr> for ByteString<A> {
    #[inline]
    fn as_ref(&self) -> &ByteStr {
        ByteStr::from_bytes(self.0.as_slice())
    }
}

impl<A: Allocator> fmt::Debug for ByteString<A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(ByteStr::from_bytes(self.0.as_slice()), f)
    }
}

impl<A: Allocator> fmt::Display for ByteString<A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(ByteStr::from_bytes(self.0.as_slice()), f)
    }
}

impl Default for ByteString {
    fn default() -> Self {
        ByteString(Vec::new())
    }
}

impl_partial_eq!([A: Allocator], ByteString<A>, &[u8]);
impl_partial_eq!([A: Allocator], ByteString<A>, &str);
impl_partial_eq!([A: Allocator], ByteString<A>, &ByteStr);
impl_partial_eq!([A: Allocator], &[u8], ByteString<A>);
impl_partial_eq!([A: Allocator], &str, ByteString<A>);
impl_partial_eq!([A: Allocator], &ByteStr, ByteString<A>);

impl_partial_ord!([A: Allocator], ByteString<A>, &ByteStr);
impl_partial_ord!([A: Allocator], &ByteStr, ByteString<A>);

impl<A: Allocator> ops::Index<usize> for ByteString<A> {
    type Output = u8;

    #[inline]
    fn index(&self, idx: usize) -> &u8 {
        &self.0[idx]
    }
}

impl<A: Allocator> ops::IndexMut<usize> for ByteString<A> {
    #[inline]
    fn index_mut(&mut self, idx: usize) -> &mut u8 {
        &mut self.0[idx]
    }
}

impl_index!([A: Allocator], ByteString<A>, ops::Range<usize>);
impl_index!([A: Allocator], ByteString<A>, ops::RangeFrom<usize>);
impl_index!([A: Allocator], ByteString<A>, ops::RangeFull);
impl_index!([A: Allocator], ByteString<A>, ops::RangeInclusive<usize>);
impl_index!([A: Allocator], ByteString<A>, ops::RangeTo<usize>);
impl_index!([A: Allocator], ByteString<A>, ops::RangeToInclusive<usize>);

impl<A: Allocator> hash::Hash for ByteString<A> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

/// allows to compute the size and write [`fmt::Arguments`] into a raw buffer.
///
/// writes will not fail if callers write past the capacity of the buffer so that they can compute
/// the size required to fit everything.
///
/// [`fmt::Arguments::estimated_capacity`] is not exposed; nor it or anything else is capable of
/// telling the exact size needed to write [`fmt::Arguments`].
struct OverflowingFormatter {
    ptr: *mut u8,
    cap: usize,
    len: usize,
}

impl OverflowingFormatter {
    fn empty() -> Self {
        Self {
            ptr: 0 as *mut u8,
            cap: 0,
            len: 0,
        }
    }

    /// SAFETY: memory starting at `buf` and extending for `cap` bytes must be valid for writes.
    unsafe fn new(ptr: *mut u8, cap: usize) -> Self {
        Self { ptr, len: 0, cap }
    }

    /// returns the number of bytes written to the buffer this formatter was created from.
    fn written(&self) -> usize {
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

struct Formatter<'a>(OverflowingFormatter, PhantomData<&'a mut ()>);

impl<'a> Formatter<'a> {
    fn new(buf: &'a mut [u8]) -> Self {
        Self(
            unsafe { OverflowingFormatter::new(buf.as_mut_ptr(), buf.len()) },
            PhantomData,
        )
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
            Self::TryReserve(e) => e.fmt(f),
            Self::Fmt(e) => e.fmt(f),
        }
    }
}

pub fn try_format_in<A: Allocator>(
    args: fmt::Arguments<'_>,
    alloc: A,
) -> Result<ByteString<A>, FormatError> {
    // NOTE: first we'll compute size of the buffer.
    let mut f = OverflowingFormatter::empty();
    // NOTE: OverflowingFormatter does not error out.
    f.write_fmt(args).map_err(FormatError::Fmt)?;
    let size = f.written();

    let mut buf = Vec::new_in(alloc);
    buf.try_reserve_exact(size)
        .map_err(FormatError::TryReserve)?;
    // SAFETY: we already know how many bytes will be written.
    unsafe { buf.set_len(size) };
    let mut f = Formatter::new(&mut buf);
    f.write_fmt(args).map_err(FormatError::Fmt)?;

    Ok(ByteString(buf))
}

#[macro_export]
macro_rules! try_format_in {
    ($alloc:expr; $($arg:tt)*) => {
        try_format_in(format_args!($($arg)*), $alloc)
    };
}

#[test]
fn test_try_format_in() {
    use tempalloc::TempAlloc;

    let temp = TempAlloc::<1000, 1>::new();

    assert_eq!(
        try_format_in!(&temp; "hello, {who}! {:.4}", 42.69, who = "sailor").unwrap(),
        ByteStr::from_bytes(b"hello, sailor! 42.6900"),
    );
}
