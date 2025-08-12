use std::hint::black_box;
use std::io::Cursor;

use criterion::{BenchmarkId, Criterion};
use criterion_cycles_per_byte::CyclesPerByte;
use varint::{max_varint_size, read_uvarint64, write_uvarint64};

const U64_VALUES: &[u64] = &[42, 255, u64::MAX / 2, u64::MAX];

fn bench_write_uvarint64(c: &mut Criterion<CyclesPerByte>) {
    let mut g = c.benchmark_group("varint");

    let mut buf = vec![0u8; max_varint_size::<u64>()];

    for &value in U64_VALUES {
        g.bench_function(BenchmarkId::new("write_uvarint64", value), |b| {
            b.iter(|| {
                let mut cursor = Cursor::new(&mut buf);
                black_box(write_uvarint64(&mut cursor, value).unwrap());
            })
        });
    }

    g.finish();
}

fn bench_read_uvarint64(c: &mut Criterion<CyclesPerByte>) {
    let mut g = c.benchmark_group("varint");

    let mut buf = vec![0u8; max_varint_size::<u64>()];

    for &value in U64_VALUES {
        let mut cursor = Cursor::new(&mut buf);
        write_uvarint64(&mut cursor, value).unwrap();

        g.bench_function(BenchmarkId::new("read_uvarint64", value), |b| {
            b.iter(|| {
                let mut cursor = Cursor::new(&buf);
                black_box(read_uvarint64(&mut cursor).unwrap());
            })
        });
    }

    g.finish();
}

fn main() {
    let mut c = Criterion::default()
        // NOTE: due to CyclesPerByte's requirements this benchmark should be started with certain
        // flags:
        // $ RUSTFLAGS="--cfg rdpru" taskset --cpu-list 0 cargo bench
        .with_measurement(CyclesPerByte)
        .configure_from_args();

    bench_write_uvarint64(&mut c);
    bench_read_uvarint64(&mut c);

    c.final_summary();
}
