use core::alloc::Layout;
use core::cell::Cell;
use core::fmt;
use core::marker::PhantomData;
use core::ptr::{self, NonNull, null_mut};

use dropguard::DropGuard;

use crate::{AllocError, Allocator, align_up};

// NOTE: this is a copy of Jonathan Blow's Temporary_Stroage thing from
// https://www.youtube.com/watch?v=SSVHWrYG974.
//
//   newer version in current jai (year 2025) has overflow pages that allow to allocate more then
//   the initial size. overflow pages are link-listed.
//
//   it's nice to be able to overflow from time to time on some kind of ocasional rare burst.
//   for example you need to rasterize a buch of font glyphs and upload them to the gpu.

// NOTE: each platform (and runtime , etc..) have different default stack sizes
//   - glib = 2-10mb
//   - musl = 128k (or 80k in old versions)
//     see https://wiki.musl-libc.org/functional-differences-from-glibc.html#Thread-stack-size
//   - windows = 1mb
//     see https://learn.microsoft.com/en-us/windows/win32/procthread/thread-stack-size
//   - apple = 512k for secondary threads
//     see https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/Multithreading/CreatingThreads/CreatingThreads.html
pub const DEFAULT_TEMP_DATA_SIZE: usize = 40 << 10;

#[derive(Debug)]
struct OverflowRegion {
    cap: usize,
    prev: *mut Self,
}

fn make_overflow_region_layout_from_cap(cap: usize) -> Layout {
    unsafe {
        let size_including_header = cap + size_of::<OverflowRegion>();
        Layout::from_size_align_unchecked(size_including_header, align_of::<OverflowRegion>())
    }
}

#[non_exhaustive]
pub struct TempCheckpoint {
    pub occupied: usize,
    pub total_occupied: usize,
    overflow_region: *mut OverflowRegion,
}

// NOTE: whenever you add/remove fields - don't forget to update debug impl. :TempDebug
pub struct TempAllocator<'data> {
    // NOTE: constructor wants a slice, but we deconstruct it into ptr and cap because:
    //   - it's easier to operate on;
    //   - at least for now i want to be strict and ensure that temp alloc stuff can't be normally
    //   passed through thread boundary .. rust does not support negative traits (`impl !Send for
    //   TempAllocator<'_> {}`), but if a struct has raw mut pointer rust will decide to make it
    //   !Send according to https://github.com/rust-lang/rust/issues/68318
    data: Cell<*mut u8>,
    size: Cell<usize>,
    _lifetime: PhantomData<&'data mut ()>,

    occupied: Cell<usize>,
    total_occupied: Cell<usize>,
    high_water_mark: Cell<usize>,

    overflow_alloc: &'data dyn Allocator,
    min_overflow_region_size: usize,
    overflow_regions: Cell<*mut OverflowRegion>,
    initial_data: *mut u8,
    initial_size: usize,
}

impl<'data> TempAllocator<'data> {
    pub const fn new(
        data: &'data mut [u8],
        overflow_alloc: &'data dyn Allocator,
        preferred_min_overflow_region_size: Option<usize>,
    ) -> Self {
        let min_overflow_region_size = match preferred_min_overflow_region_size {
            Some(preferred) => preferred,
            None => data.len(),
        };
        Self {
            data: Cell::new(data.as_mut_ptr()),
            size: Cell::new(data.len()),
            _lifetime: PhantomData,

            occupied: Cell::new(0),
            total_occupied: Cell::new(0),
            high_water_mark: Cell::new(0),

            overflow_alloc,
            min_overflow_region_size,
            overflow_regions: Cell::new(null_mut()),
            initial_data: data.as_mut_ptr(),
            initial_size: data.len(),
        }
    }

    // TODO: (for allocate and add_overflow_region?) don't you need to be taking into account
    // alignment of the requested allocation?
    //
    //   wouldn't allocation fail if alignment of OverflowRegion (header) is 16 and size of the
    //   requested allocation is greater then min_region_size and alignment is greater then the
    //   alignment of OverflowRegion (header)? this is easy enough to test - do it.
    //
    //   :AllocRegionSizeAlign

    fn add_overflow_region(&self, min_size: usize) -> Result<(), AllocError> {
        unsafe {
            let cap = min_size.max(self.min_overflow_region_size);
            let layout = make_overflow_region_layout_from_cap(cap);
            let memory = self.overflow_alloc.allocate(layout)?.cast::<u8>();

            let overflow_region = memory.cast::<OverflowRegion>().as_mut();
            overflow_region.cap = cap;
            overflow_region.prev = self.overflow_regions.get();

            self.overflow_regions.set(overflow_region);

            self.data
                .set(memory.add(size_of::<OverflowRegion>()).as_ptr());
            self.size.set(cap);
            self.occupied.set(0);

            Ok(())
        }
    }

    fn remove_overflow_regions_down_to(&self, target: *mut OverflowRegion) {
        unsafe {
            let mut cursor = self.overflow_regions.get();
            while cursor != target {
                assert!(!cursor.is_null(), "attempt to free not my memory");

                let overflow_region = &mut *cursor;
                cursor = overflow_region.prev;

                let layout = make_overflow_region_layout_from_cap(overflow_region.cap);
                self.overflow_alloc
                    .deallocate(NonNull::from_mut(overflow_region).cast(), layout);
            }

            self.overflow_regions.set(target);
        }
    }

    /// may return null.
    /// memory is non-zeroed.
    pub fn allocate(&self, layout: Layout) -> *mut u8 {
        // TODO: do i need some kind of zst check?
        // if layout.size() == 0 { return layout_dangling(&layout).as_ptr() }

        loop {
            let curr_occupied = self.occupied.get();
            let addr_maybe_unaligned = self.data.get().addr() + curr_occupied;
            let addr_aligned_up = align_up(addr_maybe_unaligned, layout.align());
            let padding = addr_aligned_up - addr_maybe_unaligned;
            let size_including_padding = layout.size() + padding;
            let next_occupied = curr_occupied + size_including_padding;
            if next_occupied <= self.size.get() {
                self.occupied.replace(next_occupied);
                self.total_occupied
                    .replace(self.total_occupied.get() + size_including_padding);
                self.high_water_mark
                    .replace(self.high_water_mark.get().max(next_occupied));
                return addr_aligned_up as *mut u8;
            }

            if self.add_overflow_region(layout.size()).is_err() {
                return null_mut();
            };
        }
    }

    pub fn make_checkpoint(&self) -> TempCheckpoint {
        TempCheckpoint {
            occupied: self.occupied.get(),
            total_occupied: self.total_occupied.get(),
            overflow_region: self.overflow_regions.get(),
        }
    }

    pub fn reset_to_checkpoint(&self, checkpoint: TempCheckpoint) {
        unsafe {
            assert!(checkpoint.occupied <= self.size.get());

            self.remove_overflow_regions_down_to(checkpoint.overflow_region);

            if let Some(overflow_region) = checkpoint.overflow_region.as_mut() {
                self.data
                    .set((overflow_region as *mut _ as *mut u8).add(size_of::<OverflowRegion>()));
                self.size.set(overflow_region.cap);
            } else {
                self.data.set(self.initial_data);
                self.size.set(self.initial_size);
                assert!(self.overflow_regions.get().is_null());
            }

            self.occupied.replace(checkpoint.occupied);
            self.total_occupied.replace(checkpoint.total_occupied);
        }
    }

    pub fn checkpoint(&self) -> DropGuard<(), impl FnOnce(())> {
        let checkpoint = self.make_checkpoint();
        DropGuard::new(move || self.reset_to_checkpoint(checkpoint))
    }

    pub fn get_total_occupied(&self) -> usize {
        self.total_occupied.get()
    }

    pub fn get_high_water_mark(&self) -> usize {
        self.high_water_mark.get()
    }

    pub fn reset(&self) {
        self.data.set(self.initial_data);
        self.size.set(self.initial_size);

        self.occupied.set(0);
        self.total_occupied.set(0);
        self.high_water_mark.set(0);

        // NOTE: deallocate all overflow regions.
        //   the idea is that they would support rare occasional bursts.
        self.remove_overflow_regions_down_to(null_mut());
    }
}

impl<'data> Drop for TempAllocator<'data> {
    fn drop(&mut self) {
        self.remove_overflow_regions_down_to(null_mut());
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

// :TempDebug
impl<'data> fmt::Debug for TempAllocator<'data> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(core::any::type_name_of_val(self))
            .field("data", &self.data)
            .field("size", &self.size)
            .field("_lifetime", &self._lifetime)
            .field("occupied", &self.occupied)
            .field("total_occupied", &self.total_occupied)
            .field("high_water_mark", &self.high_water_mark)
            .field("overflow_alloc", &"<omitted>")
            .field("min_overflow_region_size", &self.min_overflow_region_size)
            .field("overflow_regions", &self.overflow_regions)
            .field("initial_data", &self.initial_data)
            .field("initial_size", &self.initial_size)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use core::mem::MaybeUninit;

    use super::*;

    #[test]
    fn test_temp() {
        let mut temp_data = MaybeUninit::<[u8; 1000]>::uninit();
        let temp = TempAllocator::new(unsafe { temp_data.assume_init_mut() }, &crate::Global, None);

        // normal type
        {
            temp.allocate(Layout::new::<u64>());
            assert_eq!(temp.make_checkpoint().occupied, size_of::<u64>());
            assert_eq!(temp.get_total_occupied(), size_of::<u64>());
            temp.reset();
        }

        // zero-sized type
        {
            temp.allocate(Layout::new::<()>());
            assert_eq!(temp.make_checkpoint().occupied, size_of::<()>());
            assert_eq!(temp.get_total_occupied(), size_of::<()>());
            temp.reset();
        }
    }

    #[test]
    fn test_alignment() {
        for align in [2, 4, 8, 16, 32, 64] {
            let temp_layout = Layout::array::<u8>(1 << 20).unwrap();
            let mut temp_memory = crate::Global.allocate(temp_layout).unwrap();
            let temp = TempAllocator::new(unsafe { temp_memory.as_mut() }, &crate::Global, None);
            let layout = Layout::from_size_align(align, align).unwrap();
            for _ in 0..1024 {
                let ptr = temp.allocate(layout);
                assert!(!ptr.is_null());
                assert_eq!(ptr.align_offset(align), 0);
            }
            unsafe { crate::Global.deallocate(temp_memory.cast(), temp_layout) };
        }
    }

    struct TrackingAllocator {
        allocs: Cell<usize>,
        deallocs: Cell<usize>,
    }

    impl TrackingAllocator {
        fn new() -> Self {
            Self {
                allocs: Cell::new(0),
                deallocs: Cell::new(0),
            }
        }

        fn live(&self) -> isize {
            self.allocs.get() as isize - self.deallocs.get() as isize
        }
    }

    unsafe impl Allocator for TrackingAllocator {
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            self.allocs.set(self.allocs.get() + 1);
            crate::Global.allocate(layout)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            self.deallocs.set(self.deallocs.get() + 1);
            unsafe { crate::Global.deallocate(ptr, layout) }
        }
    }

    #[test]
    fn test_add_overflow_regions() {
        let tracker = TrackingAllocator::new();
        let mut buf = [0u8; 64];
        let temp = TempAllocator::new(&mut buf, &tracker, None);

        let p1 = temp.allocate(Layout::from_size_align(64, 1).unwrap());
        assert!(!p1.is_null());
        assert_eq!(tracker.live(), 0);

        // NOTE: must spill.
        let p2 = temp.allocate(Layout::from_size_align(1, 1).unwrap());
        assert!(!p2.is_null());
        assert_eq!(tracker.live(), 1);
        assert!(unsafe { p2.offset_from(p1) }.abs() >= 64);
    }

    #[test]
    fn test_must_not_add_overflow_regions() {
        let tracker = TrackingAllocator::new();
        let mut buf = [0u8; 64];
        let temp = TempAllocator::new(&mut buf, &tracker, None);

        temp.allocate(Layout::from_size_align(64, 1).unwrap());
        assert_eq!(tracker.live(), 0);
    }

    #[test]
    fn test_remove_overflow_regions() {
        let tracker = TrackingAllocator::new();

        // reset to checkpoint
        {
            let mut buf = [0u8; 64];
            let temp = TempAllocator::new(&mut buf, &tracker, None);

            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            let checkpoint = temp.make_checkpoint();
            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            assert_eq!(tracker.live(), 2);
            temp.reset_to_checkpoint(checkpoint);
            assert_eq!(tracker.live(), 0);
        }

        // reset
        {
            let mut buf = [0u8; 64];
            let temp = TempAllocator::new(&mut buf, &tracker, None);

            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            assert_eq!(tracker.live(), 2);
            temp.reset();
            assert_eq!(tracker.live(), 0);
        }

        // drop
        {
            let mut buf = [0u8; 64];
            let temp = TempAllocator::new(&mut buf, &tracker, None);

            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            temp.allocate(Layout::from_size_align(64, 1).unwrap());
            assert_eq!(tracker.live(), 2);
            drop(temp);
            assert_eq!(tracker.live(), 0);
        }

        assert_eq!(tracker.live(), 0);
    }
}
