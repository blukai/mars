use core::cell::Cell;
use core::marker::PhantomData;
use core::ptr::{self, NonNull, null_mut};

use scopeguard::ScopeGuard;

use crate::{AllocError, Allocator, Layout, align_up, ptr_is_aligned_to};

#[non_exhaustive]
pub struct TempCheckpoint {
    pub occupied: usize,
}

// NOTE: this is a copy of Jonathan Blow's Temporary_Stroage thing from
// https://www.youtube.com/watch?v=SSVHWrYG974.
//
//   newer version in current jai (year 2025) has overflow pages that allow to allocate more then
//   the initial size. overflow pages are link-listed.
//   i currently don't have a need for that.
//
//   jai's Temporary_Storage gets initialized with size and pointer to data.
//   but i don't have nor can foresee really a need for being able to provide initial data thus
//   it's generic over const SIZE. data is on the stack.
//
// TODO: add overflow pages if stack allocation can't afford to fit everythung you want.
//   can use ArenaAllocator (from arena.rs) for that, right?
//
// TODO: should MIN_ALIGN be size_of::<usize>()?
//   size of usize when compiled to wasm is 4 because wasm is 32 bit.
//   but wasm is capable of 8-byte loads.
//   is there any con to doing 8 instead of 4 (beside the obvious one which is slight memory
//   overhead)?
//   note that my rust->wasm <-> js glue code uses handles that are u64.
//   and also note that all the handles in javascript engines are also 64-bits because they do
//   nan-boxing/nan-taging.
//
// NOTE: each platform (and runtime , etc..) have different default stack sizes
//   - glic = 2-10mb
//   - musl = 128k (or 80k in old versions)
//   see https://wiki.musl-libc.org/functional-differences-from-glibc.html#Thread-stack-size
//   - windows = 1mb
//   see https://learn.microsoft.com/en-us/windows/win32/procthread/thread-stack-size
//   - apple = 512k for secondary threads
//   see https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/Multithreading/CreatingThreads/CreatingThreads.html
//
// TODO: figure out how to properly make this into thread-local static
//   with configurable size.
//   and maybe do the thing that Global does - impl Allocator for Temporary that is zero-sized that
//   just knows where to go.
//   look into:
//     - https://internals.rust-lang.org/t/idea-global-static-variables-extendable-at-compile-time/9879
//     - https://github.com/mmastrac/rust-ctor
//     - https://github.com/dtolnay/linkme
//     - https://users.rust-lang.org/t/use-compile-time-parameter-inside-program/110265
//   also look into how std::alloc::set_alloc_error_hook and std::panic::set_hook work.
#[repr(C, align(64))]
pub struct TempAllocator<'data> {
    // NOTE: constructor wants a slice, but we deconstruct it into ptr and cap because:
    //   - it's easier to operate on;
    //   - at least for now i want to be strict and ensure that temp alloc stuff can't be normally
    //   passed through thread boundary .. rust does not support negative traits (`impl !Send for
    //   TempAllocator<'_> {}`), but if a struct has raw mut pointer rust will decide to make it
    //   !Send according to https://github.com/rust-lang/rust/issues/68318
    data: *mut u8,
    size: usize,
    _marker: PhantomData<&'data mut ()>,

    occupied: Cell<usize>,
    high_water_mark: Cell<usize>,
}

impl<'data> TempAllocator<'data> {
    pub const fn new(data: &'data mut [u8]) -> Self {
        Self {
            data: data.as_mut_ptr(),
            size: data.len(),
            _marker: PhantomData,

            occupied: Cell::new(0),
            high_water_mark: Cell::new(0),
        }
    }

    /// may return null.
    /// memory is non-zeroed.
    pub fn allocate(&self, layout: Layout) -> *mut u8 {
        let curr_occupied = self.occupied.get();
        let addr_maybe_unaligned = self.data.addr() + curr_occupied;
        let addr_aligned_up = align_up(addr_maybe_unaligned, layout.align());
        let padding = addr_aligned_up - addr_maybe_unaligned;
        let next_occupied = curr_occupied + layout.size() + padding;
        if next_occupied > self.size {
            return null_mut();
        }
        self.occupied.replace(next_occupied);
        self.high_water_mark
            .replace(self.high_water_mark.get().max(next_occupied));
        let ret = addr_aligned_up as *mut u8;
        debug_assert!(ptr_is_aligned_to(ret, layout.align()));
        ret
    }

    pub fn get_checkpoint(&self) -> TempCheckpoint {
        TempCheckpoint {
            occupied: self.occupied.get(),
        }
    }

    pub fn reset_to_checkpoint(&self, checkpoint: TempCheckpoint) {
        assert!(checkpoint.occupied <= self.size);
        self.occupied.replace(checkpoint.occupied);
    }

    // TODO: consider renaming this to auto_checkpoint or scope_checkpoint or something.
    pub fn scope_guard(&self) -> ScopeGuard<(), impl FnOnce(())> {
        let checkpoint = self.get_checkpoint();
        ScopeGuard::new(move || self.reset_to_checkpoint(checkpoint))
    }

    pub fn get_high_water_mark(&self) -> usize {
        self.high_water_mark.get()
    }

    pub fn reset(&self) {
        self.occupied.replace(0);
        self.high_water_mark.replace(0);
    }
}

unsafe impl<'data> Allocator for TempAllocator<'data> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let data = self.allocate(layout);
        NonNull::new(ptr::slice_from_raw_parts_mut(data, layout.size())).ok_or(AllocError)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // NOTE: no individual deallocations. use checkpoints or reset.
    }
}

#[cfg(test)]
mod tests {
    use core::mem::MaybeUninit;

    use super::*;

    #[test]
    fn test_temp() {
        let mut temp_data = MaybeUninit::<[u8; 1000]>::uninit();
        let temp = TempAllocator::new(unsafe { temp_data.assume_init_mut() });

        // normal type
        {
            temp.allocate(Layout::new::<u64>());
            assert_eq!(temp.get_checkpoint().occupied, size_of::<u64>());
            temp.reset();
        }

        // zero-sized type
        {
            temp.allocate(Layout::new::<()>());
            assert_eq!(temp.get_checkpoint().occupied, size_of::<()>());
            temp.reset();
        }
    }

    #[test]
    fn test_alignment() {
        for align in [2, 4, 8, 16, 32, 64] {
            let mut temp_memory = {
                let temp_layout = Layout::array::<u8>(1 << 20).unwrap();
                scopeguard::ScopeGuard::new_with_data(
                    crate::Global.allocate(temp_layout).unwrap(),
                    move |temp_memory| unsafe {
                        crate::Global.deallocate(temp_memory.cast(), temp_layout)
                    },
                )
            };
            let temp = TempAllocator::new(unsafe { (*temp_memory).as_mut() });
            let layout = Layout::from_size_align(align, align).unwrap();
            for _ in 0..1024 {
                let ptr = temp.allocate(layout);
                assert!(!ptr.is_null());
                assert_eq!(ptr.align_offset(align), 0);
            }
        }
    }
}
