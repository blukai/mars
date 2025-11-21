use core::error::Error;
use core::fmt;
use core::ops;

use alloc::Layout;

pub mod arraystring;
pub mod arrayvec;
pub mod bytestring;
pub mod string;
pub mod vec;

// TODO: get rid of this when `slice_range` feature is stable.
fn try_range_from_bounds<R>(range: R, bounds: ops::RangeTo<usize>) -> Option<ops::Range<usize>>
where
    R: ops::RangeBounds<usize>,
{
    let len = bounds.end;

    let start = match range.start_bound() {
        ops::Bound::Included(&start) => start,
        ops::Bound::Excluded(start) => start.checked_add(1)?,
        ops::Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
        ops::Bound::Included(end) => end.checked_add(1)?,
        ops::Bound::Excluded(&end) => end,
        ops::Bound::Unbounded => len,
    };

    if start > end || end > len {
        None
    } else {
        Some(ops::Range { start, end })
    }
}

// ----
// heap-collection err

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReserveError {
    /// capacity cannot exceed `isize::MAX`.
    CapacityOverflow,
    AllocError {
        // NOTE: layout is included because `std::alloc::handle_alloc_error` wants it.
        layout: Layout,
    },
}

impl Error for ReserveError {}

impl fmt::Display for ReserveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapacityOverflow => f.write_str("capacity exceeded `isize::MAX`"),
            Self::AllocError { .. } => f.write_str("memory allocation failed"),
        }
    }
}

#[cfg(not(no_global_oom_handling))]
#[cold]
fn handle_reserve_error(err: ReserveError) -> ! {
    match err {
        ReserveError::CapacityOverflow => panic!("capacity overflow"),
        ReserveError::AllocError { layout, .. } => alloc::handle_alloc_error(layout),
    }
}

#[cfg(not(no_global_oom_handling))]
#[inline]
fn unwrap_reserve_result<T>(result: Result<T, ReserveError>) -> T {
    match result {
        Ok(ok) => ok,
        Err(err) => handle_reserve_error(err),
    }
}

// ----
// stack-collection err

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapacityError;

impl Error for CapacityError {}

impl fmt::Display for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("capacity overflow")
    }
}

#[cold]
fn handle_capacity_error(_err: CapacityError) -> ! {
    panic!("capacity overflow")
}

#[inline]
fn unwrap_capacity_result<T>(result: Result<T, CapacityError>) -> T {
    match result {
        Ok(ok) => ok,
        Err(err) => handle_capacity_error(err),
    }
}

// ----
// test

#[cfg(test)]
mod vec_stdtests;

#[cfg(test)]
mod string_stdtests;

#[cfg(test)]
mod testing {
    // NOTE(blukai): this is a simplified version of what can be found in
    // /rust/library/core/src/macros/mod.rs
    macro_rules! assert_matches {
        ($left:expr, $(|)? $( $pattern:pat_param )|+ $( if $guard: expr )? $(,)?) => {
            match $left {
                $( $pattern )|+ $( if $guard )? => {}
                ref left_val => {
                    panic!(
                        r#"assertion failed
   left: {left_val:?}
  right: {right}"#,
                        right = stringify!($($pattern)|+ $(if $guard)?),
                    );
                }
            }
        };
        ($left:expr, $(|)? $( $pattern:pat_param )|+ $( if $guard: expr )?, $($arg:tt)+) => {
            match $left {
                $( $pattern )|+ $( if $guard )? => {}
                ref left_val => {
                    panic!(
                        r#"assertion failed: {args}
   left: {left_val:?}
  right: {right}"#,
                        right = stringify!($($pattern)|+ $(if $guard)?),
                        args = format_args!($($arg)+)
                    );
                }
            }
        };
    }

    pub(crate) use assert_matches;

    // NOTE(blukai): this is from /rust/library/alloctests/testing/macros.rs
    macro_rules! struct_with_counted_drop {
        ($struct_name:ident $(( $( $elt_ty:ty ),+ ))?, $drop_counter:ident $( => $drop_stmt:expr )? ) => {
            thread_local! {static $drop_counter: ::core::cell::Cell<u32> = ::core::cell::Cell::new(0);}

            #[derive(Clone, Debug, PartialEq)]
            struct $struct_name $(( $( $elt_ty ),+ ))?;

            impl ::std::ops::Drop for $struct_name {
                fn drop(&mut self) {
                    $drop_counter.set($drop_counter.get() + 1);

                    $($drop_stmt(self))?
                }
            }
        };
        ($struct_name:ident $(( $( $elt_ty:ty ),+ ))?, $drop_counter:ident[ $drop_key:expr,$key_ty:ty ] $( => $drop_stmt:expr )? ) => {
            thread_local! {
                static $drop_counter: ::core::cell::RefCell<::std::collections::HashMap<$key_ty, u32>> =
                    ::core::cell::RefCell::new(::std::collections::HashMap::new());
            }

            #[derive(Clone, Debug, PartialEq)]
            struct $struct_name $(( $( $elt_ty ),+ ))?;

            impl ::std::ops::Drop for $struct_name {
                fn drop(&mut self) {
                    $drop_counter.with_borrow_mut(|counter| {
                        *counter.entry($drop_key(self)).or_default() += 1;
                    });

                    $($drop_stmt(self))?
                }
            }
        };
    }

    pub(crate) use struct_with_counted_drop;
}
