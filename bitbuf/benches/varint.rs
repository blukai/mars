use std::hint::black_box;

use bitbuf::{BitReader, BitWriter};
use criterion::{BenchmarkId, Criterion};
use criterion_cycles_per_byte::CyclesPerByte;
use varint::max_varint_size;

const U64_VALUES: &[u64] = &[42, 255, u64::MAX / 2, u64::MAX];

fn bench_write_uvarint64(c: &mut Criterion<CyclesPerByte>) {
    let mut group = c.benchmark_group("bitbuf/varint");

    let mut buf = vec![0u8; max_varint_size::<u64>()];

    for &value in U64_VALUES {
        group.bench_function(BenchmarkId::new("write_uvarint64", value), |b| {
            b.iter(|| {
                let mut bw = BitWriter::new(&mut buf);
                black_box(bw.write_uvarint64(value).unwrap());
            })
        });
    }

    group.finish();
}

fn bench_read_uvarint64(c: &mut Criterion<CyclesPerByte>) {
    let mut group = c.benchmark_group("bitbuf/varint");

    let mut buf = vec![0u8; max_varint_size::<u64>()];

    for &value in U64_VALUES {
        let mut bw = BitWriter::new(&mut buf);
        bw.write_uvarint64(value).unwrap();

        group.bench_function(BenchmarkId::new("read_uvarint64_unchecked", value), |b| {
            b.iter(|| unsafe {
                let mut br = BitReader::new(&buf);
                black_box(br.read_uvarint64_unchecked());
            })
        });
    }

    for &value in U64_VALUES {
        let mut bw = BitWriter::new(&mut buf);
        bw.write_uvarint64(value).unwrap();

        group.bench_function(BenchmarkId::new("read_uvarint64", value), |b| {
            b.iter(|| {
                let mut br = BitReader::new(&buf);
                black_box(br.read_uvarint64().unwrap());
            })
        });
    }

    group.finish()
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
