#[cfg(feature = "varint")]
use varint::{max_varint_size, zigzag_decode32, zigzag_decode64, CONTINUE_BIT, PAYLOAD_BITS};

#[cfg(feature = "varint")]
use crate::ReadVarintError;
use crate::{OverflowError, ReadIntoBufferError, EXTRA_MASKS};

// NOTE(blukai): introduction of "caching" didn't yeild any performance inprovements, in fact quite
// the opposite happened. numbers were degraded.

pub struct BitReader<'a> {
    num_bits: usize,
    data: &'a [u64],
    cur_bit: usize,
}

impl<'a> BitReader<'a> {
    #[inline]
    pub fn new(data: &'a [u8]) -> Self {
        Self {
            num_bits: data.len() << 3,
            data: unsafe {
                // SAFETY: it is okay to transmute u8s into u64s here, even if slice of slice does
                // not contain enough (8 / size_of::<u64>()).
                //
                // that is because all "safe" methods carefully keep track of where the reading is
                // taking place and any out of bound read will result in an error.
                //
                // BUT! "unsafe" `unchecked` methods may allow out of bounds reads - that is ub. in
                // debug builds assertions will yell at you loudly if something is not right, but
                // those assertions will not be present in release builds.
                std::mem::transmute::<&[u8], &[u64]>(data)
            },
            cur_bit: 0,
        }
    }

    #[inline(always)]
    pub fn num_bits_left(&self) -> usize {
        self.num_bits - self.cur_bit
    }

    #[inline(always)]
    pub fn num_bytes_left(&self) -> usize {
        self.num_bits_left() >> 3
    }

    #[inline(always)]
    pub fn num_bits_read(&self) -> usize {
        self.cur_bit
    }

    #[inline(always)]
    pub fn num_bytes_read(&self) -> usize {
        (self.cur_bit + 7) >> 3
    }

    /// seek to a specific bit.
    pub fn seek(&mut self, bit: usize) -> Result<(), OverflowError> {
        if bit > self.num_bits {
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

    #[inline(always)]
    pub unsafe fn read_ubit64_unchecked(&mut self, num_bits: usize) -> u64 {
        debug_assert!(num_bits <= 64);
        debug_assert!(self.num_bits_left() >= num_bits);

        let block1_idx = self.cur_bit >> 6;

        let mut block1 = unsafe { *self.data.get_unchecked(block1_idx) };
        // get the bits we're interested in
        block1 >>= self.cur_bit & 63;

        self.cur_bit += num_bits;
        let mut ret = block1;

        // does it span this block?
        if (self.cur_bit - 1) >> 6 == block1_idx {
            ret &= EXTRA_MASKS[num_bits];
        } else {
            let extra_bits = self.cur_bit & 63;

            let mut block2 = unsafe { *self.data.get_unchecked(block1_idx + 1) };
            block2 &= EXTRA_MASKS[extra_bits];

            // no need to mask since we hit the end of the block. shift the second block's part
            // into the high bits.
            ret |= block2 << (num_bits - extra_bits);
        }

        ret
    }

    /// read_ubit64 reads the specified number of bits into a `u64`. the function can read up to a
    /// maximum of 64 bits at a time. if the `num_bits` exceeds the number of remaining bits, the
    /// function returns an [`Error::Overflow`] error.
    #[inline]
    pub fn read_ubit64(&mut self, num_bits: usize) -> Result<u64, OverflowError> {
        debug_assert!(num_bits <= 64);

        if self.num_bits_left() < num_bits {
            return Err(OverflowError);
        }

        // SAFETY: assert and check above ensure that we'll not go out of bounds.
        Ok(unsafe { self.read_ubit64_unchecked(num_bits) })
    }

    #[inline(always)]
    pub unsafe fn read_bool_unchecked(&mut self) -> bool {
        debug_assert!(self.num_bits_left() >= 1);

        let one_bit =
            unsafe { self.data.get_unchecked(self.cur_bit >> 6) } >> (self.cur_bit & 63) & 1;
        self.cur_bit += 1;
        one_bit == 1
    }

    #[inline]
    pub fn read_bool(&mut self) -> Result<bool, OverflowError> {
        if self.num_bits_left() < 1 {
            return Err(OverflowError);
        }

        // SAFETY: check above ensures that we'll not go out of bounds.
        Ok(unsafe { self.read_bool_unchecked() })
    }

    #[inline(always)]
    pub unsafe fn read_byte_unchecked(&mut self) -> u8 {
        // NOTE: there's no point in asserting anything here because read_ubit64_unchecked contains
        // all the necessary debug assertions.
        unsafe { self.read_ubit64_unchecked(8) as u8 }
    }

    #[inline]
    pub fn read_byte(&mut self) -> Result<u8, OverflowError> {
        self.read_ubit64(8).map(|byte| byte as u8)
    }

    pub unsafe fn read_bits_unchecked(&mut self, buf: &mut [u8], num_bits: usize) {
        debug_assert!(buf.len() << 3 >= num_bits);
        debug_assert!(self.num_bits_left() >= num_bits);

        let mut out = buf.as_mut_ptr();
        let mut bits_left = num_bits;

        // align to u64 boundary
        while (out as usize & 7) != 0 && bits_left >= 8 {
            unsafe { *out = self.read_ubit64_unchecked(8) as u8 };
            out = unsafe { out.add(1) };
            bits_left -= 8;
        }

        // read large "blocks"/chunks first
        while bits_left >= 64 {
            // TODO: can copy if aligned
            unsafe { *(out as *mut u64) = self.read_ubit64_unchecked(64) };
            out = unsafe { out.add(8) };
            bits_left -= 64;
        }

        // read remaining bytes
        while bits_left >= 8 {
            unsafe { *out = self.read_ubit64_unchecked(8) as u8 };
            out = unsafe { out.add(1) };
            bits_left -= 8;
        }

        // read remaining bits
        if bits_left > 0 {
            unsafe { *out = self.read_ubit64_unchecked(bits_left) as u8 };
        }
    }

    pub fn read_bits(
        &mut self,
        buf: &mut [u8],
        num_bits: usize,
    ) -> Result<(), ReadIntoBufferError> {
        if buf.len() << 3 < num_bits {
            return Err(ReadIntoBufferError::BufferTooSmall);
        }

        if self.num_bits_left() < num_bits {
            return Err(ReadIntoBufferError::Overflow(OverflowError));
        }

        // SAFETY: check above ensures that we'll not go out of bounds.
        unsafe { self.read_bits_unchecked(buf, num_bits) };
        Ok(())
    }

    pub unsafe fn read_bytes_unchecked(&mut self, buf: &mut [u8]) {
        unsafe { self.read_bits_unchecked(buf, buf.len() << 3) };
    }

    pub fn read_bytes(&mut self, buf: &mut [u8]) -> Result<(), ReadIntoBufferError> {
        self.read_bits(buf, buf.len() << 3)
    }

    /// this can save your ass when you're using `_unchecked` methods. once you're done reading
    /// from buf call this to see if any bits were read from kyokai no kanata.
    ///
    /// returns [Error::Overflow] if overflowed (which means you are skrewed).
    ///
    /// i figured that returning result would be more convenient than a bool because it can be
    /// questionmarked; plus, in some cases, this would eliminate a need of coming up with a custom
    /// error.
    pub fn is_overflowed(&self) -> Result<(), OverflowError> {
        if self.cur_bit > self.num_bits {
            Err(OverflowError)
        } else {
            Ok(())
        }
    }

    // NOTE: ref impl for varints:
    // https://github.com/rust-lang/rust/blob/e5b3e68abf170556b9d56c6f9028318e53c9f06b/compiler/rustc_serialize/src/leb128.rs

    // TODO: varint funcs can be faster

    #[cfg(feature = "varint")]
    #[inline(always)]
    unsafe fn read_uvarint_unchecked<T>(&mut self) -> T
    where
        T: From<u8> + std::ops::BitOrAssign + std::ops::Shl<usize, Output = T>,
    {
        let byte = unsafe { self.read_byte_unchecked() };
        if (byte & CONTINUE_BIT) == 0 {
            return T::from(byte);
        }

        let mut value = T::from(byte & 0x7f);
        for count in 1..=max_varint_size::<T>() {
            let byte = unsafe { self.read_byte_unchecked() };
            value |= (T::from(byte & PAYLOAD_BITS)) << (count * 7);
            if (byte & CONTINUE_BIT) == 0 {
                return value;
            }
        }

        unreachable!("{}", ReadVarintError::MalformedVarint)
    }

    #[cfg(feature = "varint")]
    #[inline(always)]
    fn read_uvarint<T>(&mut self) -> Result<T, ReadVarintError>
    where
        T: From<u8> + std::ops::BitOrAssign + std::ops::Shl<usize, Output = T>,
    {
        let byte = self.read_byte().map_err(ReadVarintError::Overflow)?;
        if (byte & CONTINUE_BIT) == 0 {
            return Ok(T::from(byte));
        }

        let mut value = T::from(byte & 0x7f);
        for count in 1..=max_varint_size::<T>() {
            let byte = self.read_byte().map_err(ReadVarintError::Overflow)?;
            value |= (T::from(byte & PAYLOAD_BITS)) << (count * 7);
            if (byte & CONTINUE_BIT) == 0 {
                return Ok(value);
            }
        }

        Err(ReadVarintError::MalformedVarint)
    }

    #[cfg(feature = "varint")]
    pub unsafe fn read_uvarint64_unchecked(&mut self) -> u64 {
        unsafe { self.read_uvarint_unchecked() }
    }

    #[cfg(feature = "varint")]
    pub fn read_uvarint64(&mut self) -> Result<u64, ReadVarintError> {
        self.read_uvarint()
    }

    #[cfg(feature = "varint")]
    pub unsafe fn read_varint64_unchecked(&mut self) -> i64 {
        zigzag_decode64(unsafe { self.read_uvarint64_unchecked() })
    }

    #[cfg(feature = "varint")]
    pub fn read_varint64(&mut self) -> Result<i64, ReadVarintError> {
        self.read_uvarint64().map(zigzag_decode64)
    }

    #[cfg(feature = "varint")]
    pub unsafe fn read_uvarint32_unchecked(&mut self) -> u32 {
        unsafe { self.read_uvarint_unchecked() }
    }

    #[cfg(feature = "varint")]
    pub fn read_uvarint32(&mut self) -> Result<u32, ReadVarintError> {
        self.read_uvarint()
    }

    #[cfg(feature = "varint")]
    pub unsafe fn read_varint32_unchecked(&mut self) -> i32 {
        zigzag_decode32(unsafe { self.read_uvarint32_unchecked() })
    }

    #[cfg(feature = "varint")]
    pub fn read_varint32(&mut self) -> Result<i32, ReadVarintError> {
        self.read_uvarint32().map(zigzag_decode32)
    }
}
