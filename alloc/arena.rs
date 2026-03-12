use core::alloc::Layout;
use core::cell::Cell;
use core::ptr::{self, NonNull, null_mut};

use scopeguard::ScopeGuard;

use crate::{AllocError, Allocator, align_up, ptr_is_aligned_to};

pub const ARENA_DEFAULT_MIN_REGION_SIZE: usize = 8 << 20;

const HEADER_SIZE: usize = size_of::<Region>();
const HEADER_ALIGN: usize = align_of::<Region>();

#[non_exhaustive]
pub struct ArenaCheckpoint(
    // NOTE: (null_mut(), 0) if arena was empty.
    (*mut Region, usize),
);

struct Region {
    cap: usize,
    next: *mut Region,
}

// TODO: ArenaAllocator doesn't handle (/care about) potential int overflows.
//
// TODO: should ArenaAllocator's alignment be configurable (MIN_ALIGN generic param)?
pub struct ArenaAllocator<A: Allocator> {
    region_alloc: A,
    min_region_size: usize,
    head: Cell<*mut Region>,
    curr: Cell<*mut Region>,
    curr_occupied: Cell<usize>,
}

impl<A: Allocator> ArenaAllocator<A> {
    pub const fn new_in(region_alloc: A) -> Self {
        Self {
            region_alloc,
            min_region_size: ARENA_DEFAULT_MIN_REGION_SIZE,
            head: Cell::new(null_mut()),
            curr: Cell::new(null_mut()),
            curr_occupied: Cell::new(0),
        }
    }

    pub const fn with_min_region_size(mut self, min_region_size: usize) -> Self {
        self.min_region_size = min_region_size;
        self
    }

    fn allocate_region(&self, min_size: usize) -> Result<*mut Region, AllocError> {
        unsafe {
            let cap = min_size.max(self.min_region_size);
            let size_including_header = cap + HEADER_SIZE;
            // NOTE: Layout must be synced with what's in drop().
            let layout = Layout::from_size_align_unchecked(size_including_header, HEADER_ALIGN);
            let memory = self.region_alloc.allocate(layout)?;

            let region = memory.cast::<Region>().as_mut();
            region.cap = cap;
            region.next = null_mut();

            Ok(region)
        }
    }

    // TODO: maybe put ArenaAllocator::allocate method into Allocator trait?
    pub fn allocate(&self, layout: Layout) -> *mut u8 {
        unsafe {
            // TODO: do i need to do anything special for zsts?

            // NOTE: first allocation.
            if self.curr.get().is_null() {
                assert!(self.head.get().is_null());
                assert!(self.curr_occupied.get() == 0);
                let Ok(head) = self.allocate_region(layout.size()) else {
                    return null_mut();
                };
                self.head.set(head);
                self.curr.set(head);
                self.curr_occupied.set(0);
            }

            loop {
                let curr_ptr = self.curr.get();
                let curr_occupied = self.curr_occupied.get();
                let addr_base = curr_ptr.addr() + HEADER_SIZE;
                let addr_maybe_unaligned = addr_base + curr_occupied;
                let addr_aligned_up = align_up(addr_maybe_unaligned, layout.align());
                let padding = addr_aligned_up - addr_maybe_unaligned;
                let next_occupied = curr_occupied + layout.size() + padding;
                if next_occupied <= (*curr_ptr).cap {
                    self.curr_occupied.set(next_occupied);
                    let ret = addr_aligned_up as *mut u8;
                    debug_assert!(ptr_is_aligned_to(ret, layout.align()));
                    return ret;
                }

                // NOTE: maybe we did a reset/reset_to_checkpoint.
                //   try to to find fitting existing region ahead.
                //   ----
                //   existing regions may be skipped if they are too small.
                //
                // TODO: would it make sense to deallocate skipped regions immedaitely?
                let curr = &mut *curr_ptr;
                let next = if !curr.next.is_null() {
                    curr.next
                } else {
                    let Ok(next) = self.allocate_region(layout.size()) else {
                        return null_mut();
                    };
                    curr.next = next;
                    curr.next
                };
                self.curr.set(next);
                self.curr_occupied.set(0);
            }
        }
    }

    pub fn reset(&self) {
        self.curr.set(self.head.get());
        self.curr_occupied.set(0);
    }

    pub fn is_this_your_memory<T>(&self, memory: *const T) -> bool {
        unsafe {
            let addr = memory.addr();
            let mut cursor = self.head.get();
            while let Some(region) = cursor.as_mut() {
                let start = (region as *const _ as *const u8).addr() + HEADER_SIZE;
                let end = start + region.cap;
                if addr >= start && addr < end {
                    return true;
                }

                cursor = region.next;
            }
            false
        }
    }

    fn is_this_your_checkoint(&self, checkpoint: &ArenaCheckpoint) -> bool {
        unsafe {
            let ArenaCheckpoint((ptr, _)) = *checkpoint;
            let mut cursor = self.head.get();
            while let Some(region) = cursor.as_mut() {
                if ptr::eq(region, ptr) {
                    return true;
                }

                cursor = region.next;
            }
            false
        }
    }

    pub fn make_checkpoint(&self) -> ArenaCheckpoint {
        ArenaCheckpoint((self.curr.get(), self.curr_occupied.get()))
    }

    pub fn reset_to_checkpoint(&self, checkpoint: ArenaCheckpoint) {
        let ArenaCheckpoint((ptr, occupied)) = checkpoint;
        if ptr.is_null() {
            return self.reset();
        }
        assert!(self.is_this_your_checkoint(&checkpoint));
        self.curr.set(ptr);
        self.curr_occupied.set(occupied);
    }

    pub fn checkpoint(&self) -> ScopeGuard<(), impl FnOnce(())> {
        let checkpoint = self.make_checkpoint();
        ScopeGuard::new(move || self.reset_to_checkpoint(checkpoint))
    }
}

impl<A: Allocator> Drop for ArenaAllocator<A> {
    fn drop(&mut self) {
        unsafe {
            let mut cursor = self.head.get();
            while let Some(region) = cursor.as_mut() {
                cursor = region.next;

                let size_including_header = region.cap + HEADER_SIZE;
                // NOTE: Layout must be synced with what's in allocate_region().
                let layout = Layout::from_size_align_unchecked(size_including_header, HEADER_ALIGN);
                self.region_alloc
                    .deallocate(NonNull::from_mut(region).cast(), layout);
            }
        }
    }
}

impl<A: Allocator + Default> Default for ArenaAllocator<A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(A::default())
    }
}

unsafe impl<A: Allocator> Allocator for ArenaAllocator<A> {
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
    use super::*;

    #[test]
    fn test_arena() {
        let arena = ArenaAllocator::<crate::Global>::default();
        let layout = Layout::from_size_align(100, 8).unwrap();
        let p1 = arena.allocate(layout);
        let p2 = arena.allocate(layout);
        assert!(!p1.is_null());
        assert!(!p2.is_null());
        assert!(p1 < p2);
    }

    #[test]
    fn test_drop_deallocates_regions() {
        struct CountingAllocator {
            allocs: Cell<usize>,
            deallocs: Cell<usize>,
        }

        impl CountingAllocator {
            fn new() -> Self {
                Self {
                    allocs: Cell::new(0),
                    deallocs: Cell::new(0),
                }
            }
        }

        unsafe impl Allocator for CountingAllocator {
            fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
                self.allocs.set(self.allocs.get() + 1);
                crate::Global.allocate(layout)
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                self.deallocs.set(self.deallocs.get() + 1);
                unsafe { crate::Global.deallocate(ptr, layout) };
            }
        }

        let ca = CountingAllocator::new();
        {
            const MIN_REGION_SIZE: usize = 1000;
            let arena = ArenaAllocator::new_in(&ca).with_min_region_size(MIN_REGION_SIZE);
            let layout = Layout::from_size_align(MIN_REGION_SIZE / 2 + 2, 8).unwrap();
            let _p1 = arena.allocate(layout);
            let _p2 = arena.allocate(layout);
        }
        assert_eq!(ca.allocs.get(), 2);
        assert_eq!(ca.deallocs.get(), 2);
    }

    #[test]
    fn test_post_reset_region_reuse() {
        let arena = ArenaAllocator::<crate::Global>::default();
        let layout = Layout::from_size_align(900, 8).unwrap();
        let p1 = arena.allocate(layout);
        let p2 = arena.allocate(layout);
        assert!(!p1.is_null());
        assert!(!p2.is_null());
        arena.reset();
        let p3 = arena.allocate(layout);
        let p4 = arena.allocate(layout);
        assert_eq!((p1, p2), (p3, p4));
    }

    #[test]
    fn test_checkpoint_same_region_reset() {
        let arena = ArenaAllocator::<crate::Global>::default();
        let layout = Layout::from_size_align(64, 8).unwrap();
        let _p1 = arena.allocate(layout);
        let checkpoint = arena.make_checkpoint();
        let p2 = arena.allocate(layout);
        arena.reset_to_checkpoint(checkpoint);
        let p3 = arena.allocate(layout);
        assert_eq!(p2, p3);
    }

    #[test]
    fn test_checkpoint_multi_region_reset() {
        let arena = ArenaAllocator::<crate::Global>::default();
        let layout = Layout::from_size_align(900, 8).unwrap();
        let _p1 = arena.allocate(layout);
        let checkpoint = arena.make_checkpoint();
        let p2 = arena.allocate(layout);
        arena.reset_to_checkpoint(checkpoint);
        let p3 = arena.allocate(layout);
        assert_eq!(p2, p3);
    }

    #[test]
    fn test_alignment() {
        for align in [2, 4, 8, 16, 32, 64] {
            let arena = ArenaAllocator::<crate::Global>::default();
            let layout = Layout::from_size_align(align, align).unwrap();
            for _ in 0..1024 {
                let ptr = arena.allocate(layout);
                assert!(!ptr.is_null());
                assert_eq!(ptr.align_offset(align), 0);
            }
        }
    }
}
