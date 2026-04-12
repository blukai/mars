//! inspired by <https://github.com/gfx-rs/range-alloc>.

// NOTE: the initial difference was that it was able to find (and hand-out) best fit, and then then
// there's a next stage where you could have choosen best fit out of pool.
//   i tend to overcomplicate things. that didn't turn out as something i would like to do again.

use core::fmt;
use core::ops::{Add, BitAnd, Not, Range, Rem, Sub};

use alloc::{AllocError, Allocator};
use containers::array::GrowableArray;

// TODO: try to avoid heap allocations in range alloc.
//   consider doing a generous fixed-size array or something?
//   size might be configurable via const generic param.
#[derive(Debug, Default)]
pub struct RangeAllocator<T, A: Allocator> {
    full_range: Range<T>,
    free_ranges: GrowableArray<Range<T>, A>,
}

impl<T, A: Allocator> RangeAllocator<T, A>
where
    T: fmt::Debug
        + Copy
        + Eq
        + Ord
        + Sub<Output = T>
        + Add<Output = T>
        + Rem<Output = T>
        + Not<Output = T>
        + BitAnd<Output = T>
        + From<u8>,
{
    fn is_power_of_two(value: T) -> bool {
        // https://graphics.stanford.edu/~seander/bithacks.html#DetermineIfPowerOf2
        let zero = T::from(0);
        let one = T::from(1);
        (value != zero) && ((value & (value - one)) == zero)
    }

    fn align_up(value: T, align: T) -> T {
        debug_assert!(Self::is_power_of_two(align));
        let one = T::from(1);
        (value + align - one) & !(align - one)
    }

    pub fn new_in(full_range: Range<T>, alloc: A) -> Self {
        // NOTE: <= because it's not invalid to initialize with 0..0.
        assert!(full_range.start <= full_range.end);
        Self {
            full_range: full_range.clone(),
            free_ranges: {
                let mut ret = GrowableArray::new_in(alloc);
                ret.push(full_range);
                ret
            },
        }
    }

    #[inline]
    pub fn allocate(&mut self, len: T, align: T) -> Result<Range<T>, AllocError> {
        assert_ne!(len, T::from(0));
        assert!(Self::is_power_of_two(align));

        let mut best_idx = None;
        let mut min_eff_len = None;

        for (idx, range_range) in self.free_ranges.iter().enumerate() {
            let aligned_start = Self::align_up(range_range.start, align);
            // TODO: this may panic; you may want to hand-roll checked_add.
            if aligned_start + len > range_range.end {
                continue;
            }
            let eff_len = range_range.end - aligned_start;
            match min_eff_len {
                None => {
                    min_eff_len = Some(eff_len);
                    best_idx = Some(idx);
                }
                Some(prev_min_eff_len) => {
                    if eff_len < prev_min_eff_len {
                        min_eff_len = Some(eff_len);
                        best_idx = Some(idx);
                    }
                }
            }
        }

        let idx = best_idx.ok_or(AllocError)?;
        let free_range = self.free_ranges.remove_ordered(idx).unwrap();
        let allocated_range = {
            let aligned_start = Self::align_up(free_range.start, align);
            aligned_start..aligned_start + len
        };

        let has_left_fragment = free_range.start < allocated_range.start;
        if has_left_fragment {
            self.free_ranges
                .insert(idx, free_range.start..allocated_range.start);
        }
        let has_right_fragment = allocated_range.end < free_range.end;
        if has_right_fragment {
            let idx = idx + has_left_fragment as usize;
            self.free_ranges
                .insert(idx, allocated_range.end..free_range.end);
        }

        Ok(allocated_range)
    }

    #[inline(always)]
    fn defragment_free_ranges(&mut self) {
        // merge ranges (with range 10..20)
        // free ranges = [5..10, 20..96]
        // after grow right = [5..20, 20..96]

        debug_assert!(
            self.free_ranges
                .is_sorted_by_key(|free_range| free_range.start)
        );

        let mut i = 0;
        while i + 1 < self.free_ranges.len() {
            if self.free_ranges[i].end == self.free_ranges[i + 1].start {
                let next = self.free_ranges.remove_ordered(i + 1).unwrap();
                self.free_ranges[i].end = next.end;
            } else {
                i += 1;
            }
        }
    }

    pub fn deallocate(&mut self, range: Range<T>) {
        assert!(range.start < range.end);
        assert!(range.start >= self.full_range.start && range.end <= self.full_range.end);

        let idx = self
            .free_ranges
            .binary_search_by(|probe| probe.start.cmp(&range.start))
            .unwrap_or_else(|idx| idx);
        self.free_ranges.insert(idx, range);

        self.defragment_free_ranges();
    }

    pub fn full_range(&self) -> &Range<T> {
        &self.full_range
    }

    pub fn grow(&mut self, new_end: T) {
        let old_end = self.full_range.end;

        assert!(new_end > old_end);

        if let Some(last_range) = self
            .free_ranges
            .last_mut()
            .filter(|last_range| last_range.end == old_end)
        {
            last_range.end = new_end;
        } else {
            self.free_ranges.push(old_end..new_end);
        }

        self.full_range.end = new_end;
    }

    pub fn reset(&mut self) {
        self.free_ranges.clear();
        self.free_ranges.push(self.full_range.clone());
    }

    pub fn has_allocations(&self) -> bool {
        self.free_ranges.len() == 1 && self.free_ranges[0] == self.full_range
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // NOTE: some tests use 1 as alignment; 1 is something like "don't care".

    #[test]
    fn allocate() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);
        let _ = ra.allocate(10, 1);
        assert_eq!(&ra.free_ranges, &[10..100]);
    }

    #[test]
    fn deallocate_right() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);

        // right
        ra.free_ranges.clear();
        ra.free_ranges.extend_from_array([5..10]);
        ra.deallocate(10..20);
        assert_eq!(&ra.free_ranges, &[5..20]);
    }

    #[test]
    fn deallocate_left() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);

        // left
        ra.free_ranges.clear();
        ra.free_ranges.extend_from_array([20..96]);
        ra.deallocate(10..20);
        assert_eq!(&ra.free_ranges, &[10..96]);
    }

    #[test]
    fn deallocate_defragment() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);

        let _ = ra.allocate(10, 1).unwrap();
        let r1 = ra.allocate(20, 1).unwrap();
        let r2 = ra.allocate(30, 1).unwrap();

        ra.deallocate(r1);
        ra.deallocate(r2);

        assert_eq!(&ra.free_ranges, &[10..100]);
    }

    #[test]
    fn allocate_full_range() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);
        assert_eq!(ra.allocate(100, 1), Ok(0..100));
        assert!(ra.free_ranges.is_empty());
    }

    #[test]
    #[should_panic]
    fn allocate_zero() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);
        let _ = ra.allocate(0, 1);
    }

    #[test]
    fn allocate_out_of_bounds() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);
        assert!(ra.allocate(101, 1).is_err());
    }

    #[test]
    #[should_panic]
    fn deallocate_out_of_bounds() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);
        ra.deallocate(101..200);
    }

    #[test]
    fn allocate_exhausted() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);
        assert_eq!(ra.allocate(100, 1), Ok(0..100));
        assert_eq!(ra.allocate(1, 1), Err(AllocError));
    }

    #[test]
    fn grow_extends_last_free_range() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);

        let _ = ra.allocate(50, 1).unwrap();
        assert_eq!(&ra.free_ranges, &[50..100]);

        ra.grow(150);
        assert_eq!(&ra.free_ranges, &[50..150]);
        assert_eq!(ra.full_range, 0..150);
    }

    #[test]
    fn grow_adds_new_free_range() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);

        let _ = ra.allocate(100, 1).unwrap();
        assert!(ra.free_ranges.is_empty());

        ra.grow(200);
        assert_eq!(&ra.free_ranges, &[100..200]);
        assert_eq!(ra.full_range, 0..200);
    }

    #[test]
    #[should_panic]
    fn grow_panics_on_invalid_new_end() {
        let mut ra = RangeAllocator::new_in(0..100 as u32, alloc::Global);
        ra.grow(50);
    }

    #[test]
    fn test_alignment() {
        let mut ra = RangeAllocator::new_in(0..64 as u32, alloc::Global);

        let r1 = ra.allocate(10, 32).unwrap();
        assert_eq!(r1, 0..10);

        let r2 = ra.allocate(10, 32).unwrap();
        assert_eq!(r2, 32..42);
        assert_eq!(r2.start % 32, 0);

        // NOTE: prove that we can allocate into gap (left fragment of the prev allocation).
        assert_eq!(&ra.free_ranges, &[10..32, 42..64]);
        let r3 = ra.allocate(20, 1).unwrap();
        assert_eq!(r3, 10..30);
    }
}
