// NOTE: re-exports alloc from allocator-api2.
//   i don't really want to copypaste it in because there are some nice crates, like hashbrown,
//   that support allocator-api2.
pub use allocator_api2::alloc::*;

pub use tempallocator::TempAllocator;

mod tempallocator;

// TODO: consider moving temp alloc and range alloc into alloc crate.
