use std::mem::MaybeUninit;

use alloc::Allocator;

use crate::array::Array;
use crate::arraymemory::{
    ArrayMemory, FixedArrayMemory, GrowableArrayMemory, SpillableArrayMemory,
};

pub const SLOT_BITS: usize = usize::BITS as usize;
pub const INDEX_MASK: usize = SLOT_BITS - 1;
pub const INDEX_SHIFT: usize = SLOT_BITS.ilog2() as usize;

pub struct BitArray<M: ArrayMemory<usize>> {
    slots: Array<usize, M>,
    len: usize,
}

impl<M: ArrayMemory<usize>> BitArray<M> {
    #[inline]
    pub fn new_in<I: Into<M>>(initial_bit_count: usize, mem: I) -> Self {
        let mut slots = Array::new_in(mem);

        let slots_len = (initial_bit_count + INDEX_MASK) / SLOT_BITS;
        slots.reserve_exact(slots_len);
        let spare = slots.spare_cap_mut();
        // NOTE: zero-out memory. ArrayMemory thing does not do allocate_zeroed.
        spare.fill(MaybeUninit::new(0));
        unsafe { slots.set_len(slots_len) };

        Self {
            slots,
            len: initial_bit_count,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn slots(&self) -> &[usize] {
        self.slots.as_slice()
    }

    // NOTE: don't bother thinking about implementing ops::Index, you can't overload assignment in
    // rust; some other languages can do that, but rust cant.
    //   and impementing only reading (Index) without assingment (IndexMut or what could have been
    //   of it) - no; it'a asymmetric.

    #[inline]
    pub fn get(&self, index: usize) -> bool {
        debug_assert!(index < self.len);
        (self.slots[index >> INDEX_SHIFT] & (1 << (index & INDEX_MASK))) != 0
    }

    #[inline]
    pub fn set(&mut self, index: usize, value: bool) {
        debug_assert!(index < self.len);
        // NOTE: see https://graphics.stanford.edu/~seander/bithacks.html#ConditionalSetOrClearBitsWithoutBranching
        let w = &mut self.slots[index >> INDEX_SHIFT];
        let m = 1 << (index & INDEX_MASK);
        *w = (*w & !m) | ((value as usize).wrapping_neg() & m);
    }

    #[inline]
    pub fn clear(&mut self) {
        self.slots.clear()
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
        Self {
            slots: &bit_array.slots,
            total_bits_remaining: bit_array.len,
            slot_index: 0,
            value: bit_array.slots[0],
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
pub type GrowableBitArray<A: Allocator> = BitArray<GrowableArrayMemory<usize, A>>;

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
            $crate::arraymemory::FixedArrayMemory::default(),
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
            let mut bit_array = GrowableBitArray::new_in(10, alloc::Global);
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
}
