#[cfg(feature = "varint")]
use dungers_varint::{zigzag_encode64, CONTINUE_BIT, PAYLOAD_BITS};

use crate::{OverflowError, BIT_WRITE_MASKS, EXTRA_MASKS};

pub struct BitWriter<'a> {
    data_bits: usize,
    data: &'a mut [u64],
    cur_bit: usize,
}

impl<'a> BitWriter<'a> {
    #[inline]
    pub fn new(buf: &'a mut [u8]) -> Self {
        Self {
            data_bits: buf.len() << 3,
            // SAFETY: transmuting data into a slice of u64s is safe here because BitWriter
            // requires the input data to be 8-byte aligned, which is enforced by the debug_assert
            // above.
            data: unsafe { std::mem::transmute(&mut *buf) },
            cur_bit: 0,
        }
    }

    #[inline(always)]
    pub fn num_bits_left(&self) -> usize {
        self.data_bits - self.cur_bit
    }

    #[inline(always)]
    pub fn num_bytes_left(&self) -> usize {
        self.num_bits_left() >> 3
    }

    #[inline(always)]
    pub fn num_bits_written(&self) -> usize {
        self.cur_bit
    }

    #[inline(always)]
    pub fn num_bytes_written(&self) -> usize {
        (self.cur_bit + 7) >> 3
    }

    /// returns a reference to the underlying buffer.
    pub fn get_data(&self) -> &[u8] {
        unsafe { std::mem::transmute(&*self.data) }
    }

    /// seek to a specific bit.
    pub fn seek(&mut self, bit: usize) -> Result<(), OverflowError> {
        if bit > self.data_bits {
            return Err(OverflowError);
        }
        self.cur_bit = bit;
        Ok(())
    }

    /// seek to an offset from the current position.
    pub fn seek_relative(&mut self, bit_delta: isize) -> Result<usize, OverflowError> {
        let bit = self.cur_bit as isize + bit_delta;
        if bit < 0 {
            return Err(OverflowError);
        }
        self.seek(bit as usize)?;
        Ok(self.cur_bit)
    }

    #[inline]
    pub unsafe fn write_ubit64_unchecked(&mut self, data: u64, num_bits: usize) {
        debug_assert!(num_bits <= 64);

        // erase bits at n and higher positions
        let data = data & EXTRA_MASKS[num_bits];

        let block1_idx = self.cur_bit >> 6;
        let bit_offset = self.cur_bit & 63;

        // SAFETY: assert and check above ensure that we'll not go out of bounds.

        let mut block1 = unsafe { *self.data.get_unchecked(block1_idx) };
        block1 &= BIT_WRITE_MASKS[bit_offset][num_bits];
        block1 |= data << bit_offset;
        unsafe { *self.data.get_unchecked_mut(block1_idx) = block1 };

        // did it span a block?
        let bits_written = 64 - bit_offset;
        if bits_written < num_bits {
            let data = data >> bits_written;
            let n = num_bits - bits_written;

            let block2_idx = block1_idx + 1;

            let mut block2 = unsafe { *self.data.get_unchecked(block2_idx) };
            block2 &= BIT_WRITE_MASKS[0][n];
            block2 |= data;
            unsafe { *self.data.get_unchecked_mut(block2_idx) = block2 };
        }

        self.cur_bit += num_bits;
    }

    #[inline]
    pub fn write_ubit64(&mut self, data: u64, num_bits: usize) -> Result<(), OverflowError> {
        debug_assert!(num_bits <= 64);

        if self.cur_bit + num_bits > self.data_bits {
            return Err(OverflowError);
        }

        // SAFETY: assert and check above ensure that we'll not go out of bounds.
        unsafe { self.write_ubit64_unchecked(data, num_bits) };

        Ok(())
    }

    pub fn write_byte(&mut self, data: u8) -> Result<(), OverflowError> {
        self.write_ubit64(data as u64, 8)
    }

    pub fn write_bits(&mut self, data: &[u8], num_bits: usize) -> Result<(), OverflowError> {
        if self.cur_bit + num_bits > self.data_bits {
            return Err(OverflowError);
        }

        let mut pos = 0;
        let mut bits_left = num_bits;

        // align to u64 boundary
        while (data.as_ptr() as usize & 7) != 0 && bits_left >= 8 {
            unsafe { self.write_ubit64_unchecked(*data.get_unchecked(pos) as u64, 8) };
            pos += 1;
            bits_left -= 8;
        }

        // if bits_left >= 64 {
        //     todo!()
        // }

        // write remaining bytes
        while bits_left >= 8 {
            unsafe { self.write_ubit64_unchecked(*data.get_unchecked(pos) as u64, 8) };
            pos += 1;
            bits_left -= 8;
        }

        // write remaining bits
        if bits_left > 0 {
            unsafe { self.write_ubit64_unchecked(*data.get_unchecked(pos) as u64, bits_left) };
        }

        Ok(())
    }

    // NOTE: ref impl for varints:
    // https://github.com/rust-lang/rust/blob/e5b3e68abf170556b9d56c6f9028318e53c9f06b/compiler/rustc_serialize/src/leb128.rs

    // TODO: varint funcs can be faster

    #[cfg(feature = "varint")]
    pub fn write_uvarint64(&mut self, mut value: u64) -> Result<(), OverflowError> {
        loop {
            if value < CONTINUE_BIT as u64 {
                self.write_byte(value as u8)?;
                break;
            }

            self.write_byte(((value & PAYLOAD_BITS as u64) | CONTINUE_BIT as u64) as u8)?;
            value >>= 7;
        }

        Ok(())
    }

    #[cfg(feature = "varint")]
    pub fn write_varint64(&mut self, data: i64) -> Result<(), OverflowError> {
        self.write_uvarint64(zigzag_encode64(data))
    }
}
