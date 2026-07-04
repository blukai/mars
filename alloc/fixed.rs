use core::alloc::Layout;
use core::cell::Cell;
use core::fmt;
use core::marker::PhantomData;
use core::ptr::{self, NonNull, null_mut};

use crate::{AllocError, Allocator, align_up};

// NOTE: whenever you add/remove fields - don't forget to update debug impl. :FixedDebug
pub struct FixedAllocator<'data> {
    data: *mut u8,
    size: usize,
    occupied: Cell<usize>,
    _lifetime: PhantomData<&'data mut ()>,
}

impl<'data> FixedAllocator<'data> {
    pub const fn new(data: &'data mut [u8]) -> Self {
        Self {
            data: data.as_mut_ptr(),
            size: data.len(),
            occupied: Cell::new(0),
            _lifetime: PhantomData,
        }
    }

    /// may return null.
    /// memory is non-zeroed.
    pub fn allocate(&self, layout: Layout) -> *mut u8 {
        // TODO: do i need some kind of zst check?
        // if layout.size() == 0 { return layout_dangling(&layout).as_ptr() }

        let curr_occupied = self.occupied.get();
        let addr_maybe_unaligned = self.data.addr() + curr_occupied;
        let addr_aligned_up = align_up(addr_maybe_unaligned, layout.align());
        let padding = addr_aligned_up - addr_maybe_unaligned;
        let size_including_padding = layout.size() + padding;
        let next_occupied = curr_occupied + size_including_padding;
        if next_occupied > self.size {
            return null_mut();
        }
        self.occupied.replace(next_occupied);
        return addr_aligned_up as *mut u8;
    }

    pub fn occupied(&self) -> usize {
        self.occupied.get()
    }
}

unsafe impl<'data> Allocator for FixedAllocator<'data> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let data = self.allocate(layout);
        NonNull::new(ptr::slice_from_raw_parts_mut(data, layout.size())).ok_or(AllocError)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // NOTE: no individual deallocations. use checkpoints or reset.
    }
}

// :FixedDebug
impl<'data> fmt::Debug for FixedAllocator<'data> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(core::any::type_name_of_val(self))
            .field("data", &self.data)
            .field("size", &self.size)
            .field("occupied", &self.occupied)
            .field("_lifetime", &self._lifetime)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use core::mem::MaybeUninit;

    use super::*;

    #[test]
    fn test_fixed() {
        let mut fixed_data = MaybeUninit::<[u8; 1000]>::uninit();
        let fixed = FixedAllocator::new(unsafe { fixed_data.assume_init_mut() });
        fixed.allocate(Layout::new::<u64>());
        assert_eq!(fixed.occupied(), size_of::<u64>());
    }

    #[test]
    fn test_alignment() {
        for align in [2, 4, 8, 16, 32, 64] {
            let fixed_layout = Layout::array::<u8>(1 << 20).unwrap();
            let mut fixed_memory = crate::Global.allocate(fixed_layout).unwrap();
            let fixed = FixedAllocator::new(unsafe { fixed_memory.as_mut() });
            let layout = Layout::from_size_align(align, align).unwrap();
            for _ in 0..1024 {
                let ptr = fixed.allocate(layout);
                assert!(!ptr.is_null());
                assert_eq!(ptr.align_offset(align), 0);
            }
            unsafe { crate::Global.deallocate(fixed_memory.cast(), fixed_layout) };
        }
    }
}
