use crate::{BitReader, BitWriter};

// ----
// bitwriter

#[test]
fn test_write_ubit64_extra_bits_erasure() {
    let mut buf = [0u8; 8];
    let mut bw = BitWriter::new(&mut buf);

    // write 4 bits, but provide a value with more than 4 bits set
    bw.write_ubit64(0b11111111, 4).unwrap();
    assert_eq!(buf[0], 0b1111);
}

#[test]
fn test_write_ubit64_overflow() {
    let mut buf = [0u8; 8];
    let mut bw = BitWriter::new(&mut buf);

    assert!(bw.write_ubit64(u64::MAX, u64::BITS as usize).is_ok());
    assert!(bw.write_ubit64(0b1, 1).is_err());
}

#[test]
fn test_write_ubit64_multiple_writes() {
    let mut buf = [0u8; 8];
    let mut bw = BitWriter::new(&mut buf);

    bw.write_ubit64(0b101, 3).unwrap();
    bw.write_ubit64(0b1100, 4).unwrap();
    assert_eq!(buf[0], 0b1100_101);
}

#[test]
fn test_write_ubit64_spanning_blocks() {
    let mut buf = [0u8; 16];
    let mut bw = BitWriter::new(&mut buf);

    // write 60 bits to nearly fill the first block
    bw.write_ubit64(0xfffffffffffffff, 60).unwrap();

    // write 8 more bits that will span across the first and second block
    bw.write_ubit64(0xaa, 8).unwrap();

    // check the first block (64 bits)
    let block1 = u64::from_le_bytes(buf[0..8].try_into().unwrap());
    assert_eq!(block1, 0xafffffffffffffff);

    // check the second block (should have 0xa in the lowest 2 bits)
    let block2 = u64::from_le_bytes(buf[8..16].try_into().unwrap());
    assert_eq!(block2, 0xa);
}

#[test]
fn test_write_bits() {
    let mut buf = [0u8; 4];
    let mut bw = BitWriter::new(&mut buf);

    // read 3 bits
    bw.write_bits(&[0b011], 3).unwrap();
    assert_eq!(bw.get_data()[0], 0b011);

    // write 5 bits
    bw.write_bits(&[0b10110], 5).unwrap();
    assert_eq!(bw.get_data()[0], 0b10110011);

    // write 8 bits
    bw.write_bits(&[0b01011100], 8).unwrap();
    assert_eq!(bw.get_data()[1], 0b01011100);

    // write 16 bits
    bw.write_bits(&[0b11001010, 0b00110101], 16).unwrap();
    assert_eq!(bw.get_data()[2], 0b11001010);
    assert_eq!(bw.get_data()[3], 0b00110101);

    // test writing more bits than available space
    assert!(bw.write_bits(&[u8::MAX; 5], 33).is_err());
}

// ----
// bitreader

#[test]
fn test_read_ubit64_overflow() {
    let buf = [0xffu8; 8];
    let mut br = BitReader::new(&buf);

    assert!(br.read_ubit64(u64::BITS as usize).is_ok());
    assert!(br.read_ubit64(1).is_err());
}

#[test]
fn test_read_ubit64_multiple_reads() {
    let mut buf = [0u8; 8];
    buf[0] = 0b1100_101;
    let mut br = BitReader::new(&buf);

    assert_eq!(br.read_ubit64(3).unwrap(), 0b101);
    assert_eq!(br.read_ubit64(4).unwrap(), 0b1100);
}

#[test]
fn test_read_ubit64_spanning_blocks() {
    let mut buf = [0xff; 16];
    buf[8] = 0xaa;
    let mut br = BitReader::new(&buf);

    br.read_ubit64(60).unwrap();

    // read 8 bits that span across the first and second block
    let result = br.read_ubit64(8).unwrap();
    // the result should be 4 bits from the end of the first block and 4 bits from the
    // start of the second block
    assert_eq!(result, 0xaf);
}

#[test]
fn test_read_bits() {
    let buf = [
        0b10110011, 0b01011100, 0b11001010, 0b00110101, 0xff, 0xff, 0xff, 0xff,
    ];
    let mut br = BitReader::new(&buf);

    let mut out = [0u8; 4];

    // read 3 bits
    br.read_bits(&mut out[0..1], 3).unwrap();
    assert_eq!(out[0], 0b011);

    // read 5 bits
    br.read_bits(&mut out[0..1], 5).unwrap();
    assert_eq!(out[0], 0b10110);

    // read 8 bits
    br.read_bits(&mut out[0..1], 8).unwrap();
    assert_eq!(out[0], 0b01011100);

    // read 16 bits
    br.read_bits(&mut out[0..2], 16).unwrap();
    assert_eq!(out[0], 0b11001010);
    assert_eq!(out[1], 0b00110101);

    // test reading more bits than available
    assert!(br.read_bits(&mut out, 33).is_err());
}

#[test]
fn test_read_bytes() {
    let buf = [0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x11, 0x22];
    let mut br = BitReader::new(&buf);

    let mut out = [0u8; 8];

    // read 4 bytes
    br.read_bytes(&mut out[0..4]).unwrap();
    assert_eq!(out[0..4], [0xaa, 0xbb, 0xcc, 0xdd]);

    // read 2 more bytes
    br.read_bytes(&mut out[0..2]).unwrap();
    assert_eq!(out[0..2], [0xee, 0xff]);

    // try to read more bytes than available
    assert!(br.read_bytes(&mut out).is_err());

    // read remaining bytes
    br.read_bytes(&mut out[0..2]).unwrap();
    assert_eq!(out[0..2], [0x11, 0x22]);

    // try to read when no more bytes are available
    assert!(br.read_bytes(&mut out[0..1]).is_err());
}

// ----
// varint

// NOTE: tests are stolen from
// https://github.com/rust-lang/rust/blob/e5b3e68abf170556b9d56c6f9028318e53c9f06b/compiler/rustc_serialize/tests/leb128.rs

#[cfg(feature = "varint")]
#[test]
fn test_varuint64() {
    // test 256 evenly spaced values of integer range, integer max value, and some
    // "random" numbers.
    let mut values = Vec::new();

    let increment = (1 as u64) << (u64::BITS - 8);
    values.extend((0..256).map(|i| u64::MIN + i * increment));

    values.push(u64::MAX);

    values.extend((-500..500).map(|i| (i as u64).wrapping_mul(0x12345789abcdefu64 as u64)));

    let mut buf = [0u8; 1 << 20];

    let mut bw = BitWriter::new(&mut buf);
    for x in &values {
        bw.write_uvarint64(*x).unwrap();
    }

    let mut br = BitReader::new(&buf);
    for want in &values {
        let got = br.read_uvarint64().unwrap();
        assert_eq!(got, *want);
    }
}

#[cfg(feature = "varint")]
#[test]
fn test_varint64() {
    // test 256 evenly spaced values of integer range, integer max value, and some
    // "random" numbers.
    let mut values = Vec::new();

    let mut value = i64::MIN;
    let increment = (1 as i64) << (i64::BITS - 8);

    for _ in 0..256 {
        values.push(value);
        // the addition in the last loop iteration overflows.
        value = value.wrapping_add(increment);
    }

    values.push(i64::MAX);

    values.extend((-500..500).map(|i| (i as i64).wrapping_mul(0x12345789abcdefi64 as i64)));

    let mut buf = [0u8; 1 << 20];

    let mut bw = BitWriter::new(&mut buf);
    for x in &values {
        bw.write_varint64(*x).unwrap();
    }

    let mut br = BitReader::new(&buf);
    for want in &values {
        let got = br.read_varint64().unwrap();
        assert_eq!(got, *want);
    }
}
