use core::slice;

use alloc::{Allocator, this_is_fine};

use crate::array::{ArrayMemory, FixedArrayMemory, ResizableArrayMemory, SpillableArrayMemory};

pub const SLOT_BITS: usize = usize::BITS as usize;
pub const INDEX_MASK: usize = SLOT_BITS - 1;
pub const INDEX_SHIFT: usize = SLOT_BITS.ilog2() as usize;

pub struct BitArray<M: ArrayMemory<usize>> {
    mem: M,
    // NOTE: cap in bits.
    cap: usize,
}

impl<M: ArrayMemory<usize>> BitArray<M> {
    #[inline]
    pub fn new_in<I: Into<M>>(initial_bit_cap: usize, mem: I) -> Self {
        let mut mem = mem.into();

        let initial_slot_cap = (initial_bit_cap + INDEX_MASK) / SLOT_BITS;

        // TODO: don't init memory in new/constructor, instead provide resize method. :Hack
        debug_assert!(mem.cap() == 0 || mem.cap() == initial_slot_cap);
        if mem.cap() < initial_slot_cap {
            let result = unsafe { mem.grow(initial_slot_cap) };
            this_is_fine(result);
        }

        let spare = unsafe { slice::from_raw_parts_mut(mem.as_ptr(), initial_slot_cap) };
        spare.fill(0);

        Self {
            mem,
            cap: initial_bit_cap,
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
        unsafe { slice::from_raw_parts(self.mem.as_ptr(), self.mem.cap()) }
    }

    #[inline]
    fn slots_mut(&mut self) -> &mut [usize] {
        unsafe { slice::from_raw_parts_mut(self.mem.as_ptr(), self.mem.cap()) }
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
    ($len:expr) => {
        FixedBitArray<{ ($len + $crate::bitarray::INDEX_MASK) / $crate::bitarray::SLOT_BITS }>
    };
}

#[macro_export]
macro_rules! __SpillableBitArray {
    ($len:expr, $alloc:ty) => {
        SpillableBitArray<{ ($len + $crate::bitarray::INDEX_MASK) / $crate::bitarray::SLOT_BITS }, $alloc>
    };
}

#[macro_export]
macro_rules! __make_fixed_bit_array {
    ($len:expr) => {
        <$crate::bitarray::FixedBitArray!($len)>::new_in(
            $len,
            $crate::array::FixedArrayMemory::default(),
        )
    };
}

#[macro_export]
macro_rules! __make_spillable_bit_array_in {
    ($len:expr, $alloc:expr) => {
        <$crate::bitarray::SpillableBitArray!($len, _)>::new_in($len, $alloc)
    };
}

pub use __FixedBitArray as FixedBitArray;
pub use __SpillableBitArray as SpillableBitArray;
pub use __make_fixed_bit_array as make_fixed_bit_array;
pub use __make_spillable_bit_array_in as make_spillable_bit_array_in;

// ----

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_array() {
        fn all_bits_are_unset_but_one<M: ArrayMemory<usize>>(
            bit_array: &BitArray<M>,
            one_index: usize,
        ) {
            for (i, value) in bit_array.iter().enumerate() {
                assert!(value == (i == one_index));
            }
        }

        {
            let mut bit_array = ResizableBitArray::new_in(10, alloc::Global);
            bit_array.set(5, true);
            all_bits_are_unset_but_one(&bit_array, 5);
        }

        {
            let mut bit_array = make_fixed_bit_array!(1000);
            bit_array.set(900, true);
            all_bits_are_unset_but_one(&bit_array, 900);
        }

        {
            let mut bit_array = make_spillable_bit_array_in!(255, alloc::Global);
            bit_array.set(120, true);
            all_bits_are_unset_but_one(&bit_array, 120);
        }
    }

    #[test]
    fn test_count() {
        let mut bit_array = make_fixed_bit_array!(10);
        assert!(bit_array.count() == 0);
        bit_array.set(2, true);
        bit_array.set(8, true);
        assert!(bit_array.count() == 2);
    }
}
