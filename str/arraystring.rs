use core::error::Error;
use core::mem::{self, MaybeUninit};
use core::{fmt, ops, slice};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapacityError;

impl Error for CapacityError {}

impl fmt::Display for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("capacity overflow")
    }
}

#[cold]
pub fn handle_capacity_error(_err: CapacityError) -> ! {
    panic!("capacity overflow")
}

#[repr(C)]
pub struct ArrayString<const N: usize> {
    len: usize,
    data: [MaybeUninit<u8>; N],
}

impl<const N: usize> ArrayString<N> {
    #[inline]
    pub const fn new() -> Self {
        Self {
            len: 0,
            data: [MaybeUninit::uninit(); N],
        }
    }

    #[inline]
    pub const fn capacity(&self) -> usize {
        N
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub const fn remaining_capacity(&self) -> usize {
        self.capacity() - self.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub const fn is_full(&self) -> bool {
        self.capacity() == self.len()
    }

    #[inline]
    pub const fn as_str(&self) -> &str {
        // SAFETY: contents are stipulated to be valid utf-8, invalid contents are an error
        // at construction.
        unsafe {
            let s = slice::from_raw_parts(self.data.as_ptr().cast(), self.len());
            str::from_utf8_unchecked(s)
        }
    }

    #[inline]
    pub const fn as_mut_str(&mut self) -> &mut str {
        // SAFETY: contents are stipulated to be valid UTF-8, invalid contents are an error
        // at construction.
        unsafe {
            let s = slice::from_raw_parts_mut(self.data.as_mut_ptr().cast(), self.len());
            str::from_utf8_unchecked_mut(s)
        }
    }

    #[inline]
    pub fn try_push_str(&mut self, s: &str) -> Result<(), CapacityError> {
        let len = self.len();
        let s_len = s.len();
        if self.remaining_capacity() < s_len {
            return Err(CapacityError);
        }
        // SAFETY: just ensured that we have enough capacity ^
        unsafe {
            let dst = mem::transmute::<_, &mut [u8]>(&mut self.data[len..len + s_len]);
            dst.copy_from_slice(s.as_bytes());
        }
        self.len += s_len;
        Ok(())
    }

    #[inline]
    pub fn push_str(&mut self, s: &str) {
        if let Err(err) = self.try_push_str(s) {
            handle_capacity_error(err)
        }
    }

    #[inline]
    pub fn try_push(&mut self, ch: char) -> Result<(), CapacityError> {
        let len = self.len();
        let ch_len = ch.len_utf8();
        if self.remaining_capacity() < ch_len {
            return Err(CapacityError);
        }
        // SAFETY: just ensured that we have enough capacity ^
        unsafe {
            let dst = mem::transmute::<_, &mut [u8]>(&mut self.data[len..]);
            ch.encode_utf8(dst);
        }
        self.len += ch_len;
        Ok(())
    }

    #[inline]
    pub fn push(&mut self, ch: char) {
        if let Err(err) = self.try_push(ch) {
            handle_capacity_error(err)
        }
    }

    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        self.len = self.len() - ch.len_utf8();
        Some(ch)
    }

    /// Shortens this `ArrayString` to the specified length.
    ///
    /// If `new_len` is greater than or equal to the string's current length, this has no
    /// effect.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    #[inline]
    #[track_caller]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.len = new_len;
        }
    }

    /// Truncates this `ArrayString`, removing all contents.
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
        debug_assert!(self.is_empty());
    }

    pub fn try_from_str(s: &str) -> Result<Self, CapacityError> {
        let mut this = Self::new();
        this.try_push_str(s)?;
        Ok(this)
    }

    pub fn from_str(s: &str) -> Self {
        match Self::try_from_str(s) {
            Ok(this) => this,
            Err(err) => handle_capacity_error(err),
        }
    }

    #[inline]
    pub fn try_from_char(ch: char) -> Result<Self, CapacityError> {
        let mut this = Self::new();
        this.try_push(ch)?;
        Ok(this)
    }

    #[inline]
    pub fn from_char_in(ch: char) -> Self {
        match Self::try_from_char(ch) {
            Ok(this) => this,
            Err(err) => handle_capacity_error(err),
        }
    }
}

impl<const N: usize> Default for ArrayString<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> ops::Deref for ArrayString<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> ops::DerefMut for ArrayString<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> AsRef<str> for ArrayString<N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> AsRef<[u8]> for ArrayString<N> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> AsRef<std::ffi::OsStr> for ArrayString<N> {
    #[inline]
    fn as_ref(&self) -> &std::ffi::OsStr {
        (&**self).as_ref()
    }
}

impl<const N: usize> AsRef<std::path::Path> for ArrayString<N> {
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

impl_partial_eq! { [const N1: usize, const N2: usize] ArrayString<N1>, ArrayString<N2> }
impl_partial_eq! { [const N: usize] ArrayString<N>, &str }
impl_partial_eq! { [const N: usize] ArrayString<N>, std::string::String }
impl_partial_eq! { [const N: usize, A: alloc::Allocator] ArrayString<N>, crate::string::String<A> }
impl_partial_eq! { [const N: usize] &str, ArrayString<N> }
impl_partial_eq! { [const N: usize] std::string::String, ArrayString<N> }
impl_partial_eq! { [const N: usize, A: alloc::Allocator] crate::string::String<A>, ArrayString<N> }

impl<const N: usize> fmt::Debug for ArrayString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Display for ArrayString<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<const N: usize> fmt::Write for ArrayString<N> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).map_err(|_| fmt::Error)
    }

    #[inline]
    fn write_char(&mut self, c: char) -> std::fmt::Result {
        self.try_push(c).map_err(|_| fmt::Error)
    }
}

#[test]
fn test_array_string() {
    let mut s = ArrayString::<5>::from_str("AYAYA");
    assert_eq!(s.try_push_str("Aya"), Err(CapacityError));
    assert_eq!(s, "AYAYA");
    assert_eq!(ArrayString::<42>::from_str("AYAYA"), s);
    assert_ne!(ArrayString::<42>::from_str("hello, sailor"), s);
    assert_eq!(crate::string::String::from_str("AYAYA"), s);
}
