use core::alloc::Layout;
use core::ptr::NonNull;

use crate::{AllocError, Allocator};

pub struct NoopAlloc;

unsafe impl Allocator for NoopAlloc {
    fn allocate(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Err(AllocError)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}
