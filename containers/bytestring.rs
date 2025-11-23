// NOTE: this is a partial copy of unstable std bstr.
//
// $ find ./library -name "bstr*"
// ./library/alloc/src/bstr.rs
// ./library/core/src/bstr
// ./library/coretests/tests/bstr.rs
// ./library/std/src/bstr.rs

use alloc::{Allocator, Global};
use core::fmt::{self, Write as _};
use core::{hash, ops};

use crate::vec::Vec;

// ----
// impl macros

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
/// For an owned, growable byte string buffer, use [`ByteString`].
///
/// # Representation
///
/// A `&ByteStr` has the same representation as a `&str`.
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
impl<'a> Default for &'a ByteStr {
    #[inline]
    fn default() -> Self {
        ByteStr::from_bytes(b"")
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
        fn write_utf8_chunks(this: &ByteStr, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            for chunk in this.utf8_chunks() {
                f.write_str(chunk.valid())?;
                if !chunk.invalid().is_empty() {
                    f.write_char(char::REPLACEMENT_CHARACTER)?;
                }
            }
            Ok(())
        }

        let Some(align) = f.align() else {
            return write_utf8_chunks(self, f);
        };

        let (left_pad_width, right_pad_width) = {
            let char_count: usize = self
                .utf8_chunks()
                .map(|chunk| chunk.valid().chars().count() + !chunk.invalid().is_empty() as usize)
                .sum();
            let pad_width = f.width().unwrap_or(0).saturating_sub(char_count);
            match align {
                fmt::Alignment::Left => (0, pad_width),
                fmt::Alignment::Right => (pad_width, 0),
                fmt::Alignment::Center => {
                    let left = pad_width / 2;
                    let right = left + pad_width % 2;
                    (left, right)
                }
            }
        };

        let fill_char = f.fill();
        for _ in 0..left_pad_width {
            f.write_char(fill_char)?;
        }
        write_utf8_chunks(self, f)?;
        for _ in 0..right_pad_width {
            f.write_char(fill_char)?;
        }

        Ok(())
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
/// For a borrowed byte string see [`ByteStr`].
///
/// `ByteString` implements `Deref` to `&Vec<u8>`, so all methods available on `&Vec<u8>` are
/// available on `ByteString`. Similarly, `ByteString` implements `DerefMut` to `&mut Vec<u8>`,
/// so you can modify a `ByteString` using any method available on `&mut Vec<u8>`.
///
/// The `Debug` and `Display` implementations for `ByteString` are the same as those for `ByteStr`,
/// showing invalid UTF-8 as hex escapes or the Unicode replacement character, respectively.
#[repr(transparent)]
pub struct ByteString<A: Allocator = Global>(pub Vec<u8, A>);

impl Default for ByteString {
    fn default() -> Self {
        ByteString(Vec::empty())
    }
}

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

impl_partial_eq!([A1: Allocator, A2: Allocator], ByteString<A1>, ByteString<A2>);
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
