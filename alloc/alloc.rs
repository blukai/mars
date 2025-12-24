// NOTE: re-export alloc from allocator-api2.
//   i don't really want to copypaste it in because there are some nice crates, like hashbrown,
//   that support allocator-api2.
pub use allocator_api2::alloc::*;
pub use temp::*;

mod temp;

#[inline]
pub(crate) const fn align_up(size: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (size + align - 1) & !(align - 1)
}

// TODO: remove once `core::ptr::is_aligned_to` (`pointer_is_aligned_to` feature flag) is stable.
#[inline]
pub(crate) fn ptr_is_aligned_to<T>(ptr: *const T, align: usize) -> bool {
    debug_assert!(align.is_power_of_two());
    ptr.addr() & (align - 1) == 0
}
