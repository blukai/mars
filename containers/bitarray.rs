use core::slice;

use alloc::{AllocError, Allocator};

use crate::array::{
    ArrayMemory, FixedArrayMemory, GrowthMode, ResizableArrayMemory, SpillableArrayMemory, grow_cap,
};

pub const SLOT_BITS: usize = usize::BITS as usize;
pub const INDEX_MASK: usize = SLOT_BITS - 1;
pub const INDEX_SHIFT: usize = SLOT_BITS.ilog2() as usize;

pub struct BitArray<M: ArrayMemory<usize>> {
    mem: M,
    // NOTE: cap in bits.
    //   when converted to cap in slots be different then mem's cap.
    cap: usize,
}

impl<M: ArrayMemory<usize>> BitArray<M> {
    #[inline]
    pub fn new_in<I: Into<M>>(mem: I) -> Self {
        Self {
            mem: mem.into(),
            cap: 0,
        }
    }

    #[inline]
    pub fn cap(&self) -> usize {
        self.cap
    }

    pub fn count(&self) -> usize {
        let mut count = 0;
        for slot in self.slots() {
            count += slot.count_ones() as usize;
        }
        count
    }

    #[inline]
    fn slots(&self) -> &[usize] {
        let len = (self.cap + INDEX_MASK) / SLOT_BITS;
        unsafe { slice::from_raw_parts(self.mem.as_ptr(), len) }
    }

    #[inline]
    fn slots_mut(&mut self) -> &mut [usize] {
        let len = (self.cap + INDEX_MASK) / SLOT_BITS;
        unsafe { slice::from_raw_parts_mut(self.mem.as_ptr(), len) }
    }

    fn try_grow_to(&mut self, new_cap: usize) -> Result<(), AllocError> {
        let old_cap_in_bits = self.cap;
        let new_cap_in_bits = new_cap;

        let old_cap = (old_cap_in_bits + INDEX_MASK) / SLOT_BITS;
        let new_cap = (new_cap_in_bits + INDEX_MASK) / SLOT_BITS;

        let cap = self.mem.cap();
        let len = cap;
        let additional = new_cap - cap;

        if let Some(new_cap) =
            grow_cap(cap, len, additional, size_of::<usize>(), GrowthMode::Exact)?
        {
            // SAFETY: grow_cap returns Some(new_cap) if new cap is greater then old.
            unsafe {
                self.mem.grow(new_cap)?;
            }
        };

        self.cap = new_cap_in_bits;
        // NOTE: we did actually grow, need to zero-out new slots.
        self.slots_mut()[old_cap..].fill(0);

        Ok(())
    }

    // NOTE: don't bother thinking about implementing ops::Index, you can't overload assignment in
    // rust; some other languages can do that, but rust cant.
    //   and impementing only reading (Index) without assingment (IndexMut or what could have been
    //   of it) - no; it'a asymmetric.

    #[inline]
    pub fn get(&self, index: usize) -> bool {
        debug_assert!(index < self.cap());
        let slots = self.slots();
        let slot_index = index >> INDEX_SHIFT;
        (slots[slot_index] & (1 << (index & INDEX_MASK))) != 0
    }

    #[inline]
    pub fn set(&mut self, index: usize, value: bool) {
        debug_assert!(index < self.cap());
        let slots = self.slots_mut();
        let slot_index = index >> INDEX_SHIFT;
        // NOTE: see https://graphics.stanford.edu/~seander/bithacks.html#ConditionalSetOrClearBitsWithoutBranching
        let w = &mut slots[slot_index];
        let m = 1 << (index & INDEX_MASK);
        *w = (*w & !m) | ((value as usize).wrapping_neg() & m);
    }

    #[inline]
    pub fn clear(&mut self) {
        self.slots_mut().fill(0);
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_> {
        Iter::new(self)
    }
}

impl<M: ArrayMemory<usize> + Default> Default for BitArray<M> {
    #[inline]
    fn default() -> Self {
        Self::new_in(M::default())
    }
}

pub struct Iter<'a> {
    slots: &'a [usize],
    total_bits_remaining: usize,
    slot_index: usize,
    value: usize,
    bit: usize,
}

impl<'a> Iter<'a> {
    #[inline]
    fn new<M: ArrayMemory<usize>>(bit_array: &'a BitArray<M>) -> Self {
        let slots = bit_array.slots();
        Self {
            slots,
            total_bits_remaining: bit_array.cap(),
            slot_index: 0,
            value: slots[0],
            bit: 0,
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = bool;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.total_bits_remaining <= 0 {
            debug_assert!(self.total_bits_remaining == 0);
            return None;
        }

        let value = (self.value & 1) != 0;
        self.value >>= 1;

        self.bit += 1;
        self.total_bits_remaining -= 1;

        if self.bit >= SLOT_BITS {
            debug_assert!(self.bit == SLOT_BITS);
            self.slot_index += 1;
            self.value = *self.slots.get(self.slot_index).unwrap_or(&0);
            self.bit = 0;
        }

        Some(value)
    }
}

// ----
// aliases and their makers below

#[expect(type_alias_bounds)]
pub type ResizableBitArray<A: Allocator> = BitArray<ResizableArrayMemory<usize, A>>;

// NOTE: see https://github.com/rust-lang/rust/issues/76560
//   once generic_const_exprs feature is stable (maybe in 2036?) get rid of this macro?

pub type FixedBitArray<const N: usize> = BitArray<FixedArrayMemory<usize, N>>;

#[expect(type_alias_bounds)]
pub type SpillableBitArray<const N: usize, A: Allocator> =
    BitArray<SpillableArrayMemory<usize, N, A>>;

// NOTE: another thing i am not happy about is how macro exports work xd.
//   i hate the idea of these not being scoped to bitarray module.
//
//   an ugly workaround, yay.
//   thanks to
//   https://users.rust-lang.org/t/how-to-namespace-a-macro-rules-macro-within-a-module-or-macro-export-it-without-polluting-the-top-level-namespace/63779/5

#[macro_export]
macro_rules! __FixedBitArray {
    ($bits:expr) => {
        FixedBitArray<{ ($bits + $crate::bitarray::INDEX_MASK) / $crate::bitarray::SLOT_BITS }>
    };
}

#[macro_export]
macro_rules! __SpillableBitArray {
    ($bits:expr, $alloc:ty) => {
        SpillableBitArray<{ ($bits + $crate::bitarray::INDEX_MASK) / $crate::bitarray::SLOT_BITS }, $alloc>
    };
}

pub use __FixedBitArray as FixedBitArray;
pub use __SpillableBitArray as SpillableBitArray;

// ----

#[cfg(not(no_global_oom_handling))]
mod oom {
    use alloc::this_is_fine;

    use super::*;

    impl<M: ArrayMemory<usize>> BitArray<M> {
        #[inline]
        pub fn grow_to(&mut self, new_cap: usize) {
            this_is_fine(self.try_grow_to(new_cap))
        }
    }
}

// ----

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_array() {
        fn check<M: ArrayMemory<usize>>(
            bit_array: &mut BitArray<M>,
            cap_to_grow: usize,
            bit_to_set: usize,
        ) {
            bit_array.try_grow_to(cap_to_grow).unwrap();
            bit_array.set(bit_to_set, true);

            for (i, value) in bit_array.iter().enumerate() {
                assert!(value == (i == bit_to_set));
            }
        }

        check(&mut ResizableBitArray::new_in(alloc::Global), 10, 5);
        check(&mut <FixedBitArray!(1000)>::default(), 1000, 900);
        check(
            &mut <SpillableBitArray!(255, _)>::new_in(alloc::Global),
            255,
            120,
        );
    }

    #[test]
    fn test_count() {
        let mut bit_array = <FixedBitArray!(10)>::default();
        bit_array.try_grow_to(10).unwrap();
        assert!(bit_array.count() == 0);
        bit_array.set(2, true);
        bit_array.set(8, true);
        assert!(bit_array.count() == 2);
    }

    #[test]
    fn test_reserve() {
        fn check<M: ArrayMemory<usize>>(bit_array: &mut BitArray<M>) {
            assert!(bit_array.cap() == 0);
            bit_array.try_grow_to(65).unwrap();
            assert!(bit_array.cap() == 65);
        }

        check(&mut ResizableBitArray::new_in(alloc::Global));
        check(&mut <FixedBitArray!(65)>::default());
        check(&mut <SpillableBitArray!(65, alloc::Global)>::default());
    }
}
