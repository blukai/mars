use std::{
    alloc::Layout,
    error::Error,
    fmt,
    num::NonZero,
    ptr::{self, NonNull},
};

pub use global::*;
pub use temporary::*;

pub mod boxed;
mod global;
mod temporary;
pub mod vec;

#[cfg(test)]
mod vec_std_tests;

// NOTE: this is like std::alloc::Layout::dangling.
#[must_use]
#[inline]
pub(crate) const fn layout_dangling(this: &Layout) -> NonNull<u8> {
    NonNull::without_provenance(
        // SAFETY: Alignment::as_nonzero does not check zeroes, it just transmutes self.
        unsafe { NonZero::new_unchecked(this.align()) },
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllocError;

impl Error for AllocError {}

impl fmt::Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("memory allocation failed")
    }
}

// NOTE: rust is uncapable of deciding how to do memory allocation.
//   there's allocator_api nightly feature that provides Allocator trait.
//   this is similar to that.
//
//   i've been ocasionally taking a peek at it since 2022 (it's 2025 now), the original issue was
//   created in 2016, see https://github.com/rust-lang/rust/issues/32838.
//
//   this is copypasta from /rust/library/core/src/alloc/mod.rs,
//   this trait does not contain by_ref, grow_zeroed, allocate_zeroed methods.
//
// NOTE: i want that this trait to be dyn-compatible.
//   unfortunately it limits the specificity of errors. there's no way for each implementation to
//   include additional error information. see
//   - https://github.com/rust-lang/wg-allocators/issues/23
//   - https://github.com/rust-lang/wg-allocators/issues/106
pub unsafe trait Allocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() >= old_layout.size(),
            "`new_layout.size()` must be greater than or equal to `old_layout.size()`"
        );

        let new_ptr = self.allocate(new_layout)?;

        // SAFETY: because `new_layout.size()` must be greater than or equal to
        // `old_layout.size()`, both the old and new memory allocation are valid for reads and
        // writes for `old_layout.size()` bytes. Also, because the old allocation wasn't yet
        // deallocated, it cannot overlap `new_ptr`. Thus, the call to `copy_nonoverlapping` is
        // safe. The safety contract for `dealloc` must be upheld by the caller.
        unsafe {
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr().cast(), old_layout.size());
            self.deallocate(ptr, old_layout);
        }

        Ok(new_ptr)
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() <= old_layout.size(),
            "`new_layout.size()` must be smaller than or equal to `old_layout.size()`"
        );

        let new_ptr = self.allocate(new_layout)?;

        // SAFETY: same as in `grow`.
        unsafe {
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr().cast(), new_layout.size());
            self.deallocate(ptr, old_layout);
        }

        Ok(new_ptr)
    }
}

unsafe impl<A> Allocator for &A
where
    A: Allocator + ?Sized,
{
    #[inline]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        (**self).allocate(layout)
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe { (**self).deallocate(ptr, layout) }
    }

    #[inline]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        unsafe { (**self).grow(ptr, old_layout, new_layout) }
    }

    #[inline]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        unsafe { (**self).shrink(ptr, old_layout, new_layout) }
    }
}

// fn format_in<A: Allocator>(args: fmt::Arguments<'_>, alloc: A) -> Vec<u8, A> {
//     use std::io::Write as _;
//
//     // NOTE: std has estimated_capacity method on Arguments, but it's internal and not exposed and
//     // it does not seem like there's a way of getting it.
//     let mut output = AVec::new_in(alloc);
//     output.write_fmt(args).expect(
//         "a formatting trait implementation returned an error when the underlying stream did not",
//     );
//     output
// }

// #[macro_export]
// macro_rules! format_in {
//     ($alloc:expr, $($args:tt)*) => {
//
//         use allocator_api2::vec::Vec;
//
//         let args = format_args!($($args)*);
//
//         let capacity = args.estimated_capacity();
//         let mut output = Vec::<u8, _>::with_capacity_in(&temp);
//         output.write_fmt()
//             .expect("a formatting trait implementation returned an error when the underlying stream did not");
//
//         args.as_str().map_or_else(|| format_inner(args), crate::borrow::ToOwned::to_owned)
//     };
// }
//
// #[test]
// fn test_aformat() {
//     use std::io::Write as _;
//
//     use allocator_api2::vec::Vec;
//
//     let temp = TemporaryAllocator::<1024>::new();
//
//     let mut buf = Vec::<u8, _>::new_in(&temp);
//     buf.write_fmt(format_args!("hello, {who}", who = "sailor"))
//         .unwrap();
//     assert_eq!(str::from_utf8(&buf).unwrap(), "hello, sailor");
//     assert_eq!(temp.get_mark(), temp.get_high_water_mark());
//     assert_eq!(temp.get_mark(), "hello, sailor".len());
//
//     // format!();
//     // string
//     //     .write_fmt(format_args!($($args)*))
//     //     .expect("oom, or something else went terribly wrong");
//     // unsafe { std::mem::transmute::<_, &'static str>(string.as_str()) }
// }
//
//     #[test]
//     fn test_string_write() {
//         use std::fmt::Write as _;
//
//         let mut s = String::new();
//         let _ = write!(&mut s, "hello, {who}", who = "sailor");
//         assert_eq!(&s, "hello, sailor");
//     }
//
//     // impl<A: Allocator, B: Allocator> PartialOrd<String<B>> for String<A> {
//     //     #[inline]
//     //     fn partial_cmp(&self, other: &String<B>) -> Option<std::cmp::Ordering> {
//     //         todo!()
//     //         // PartialOrd::partial_cmp(&self[..], &other[..])
//     //     }
//     // }
//     //
//     // impl<A: Allocator> Ord for String<A> {
//     //     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//     //         todo!()
//     //         // Ord::cmp(&self[..], &other[..])
//     //     }
//     // }
// }
