use std::hint::black_box;

use bitbuf::{BitReader, BitWriter};
use criterion::{BenchmarkId, Criterion};
use criterion_cycles_per_byte::CyclesPerByte;

const U64_INPUTS: &[&(u64, usize)] = &[&(0xdeadbeefcafebabe, 64), &(0xdeadbeef, 32), &(0xaa, 8)];

fn bench_write_ubit64(c: &mut Criterion<CyclesPerByte>) {
    let mut group = c.benchmark_group("bitbuf/ubit64");

    let mut buf = [0u8; 100];

    for &input in U64_INPUTS {
        group.bench_function(
            BenchmarkId::new("write_ubit64", format!("{:?}", input)),
            |b| {
                b.iter(|| {
                    let mut bw = BitWriter::new(&mut buf);
                    black_box(bw.write_ubit64(input.0, input.1).unwrap());
                })
            },
        );
    }

    group.bench_function("write_ubit64", |b| {
        b.iter(|| {
            let mut bw = BitWriter::new(&mut buf);
            black_box(bw.write_ubit64(0xfffffffffffffff, 60).unwrap());
            black_box(bw.write_ubit64(0xaa, 8).unwrap());
        })
    });

    group.finish();
}

fn bench_read_ubit64(c: &mut Criterion<CyclesPerByte>) {
    let mut group = c.benchmark_group("bitbuf/ubit64");

    let mut buf = [0xFFu8; 100];

    for &input in U64_INPUTS {
        group.bench_function(
            BenchmarkId::new("read_ubit64_unchecked", format!("{:?}", input)),
            |b| {
                b.iter(|| unsafe {
                    let mut br = BitReader::new(&mut buf);
                    black_box(br.read_ubit64_unchecked(input.1));
                })
            },
        );
    }
    for &input in U64_INPUTS {
        group.bench_function(
            BenchmarkId::new("read_ubit64", format!("{:?}", input)),
            |b| {
                b.iter(|| {
                    let mut br = BitReader::new(&mut buf);
                    black_box(br.read_ubit64(input.1).unwrap());
                })
            },
        );
    }

    group.bench_function("read_ubit64_unchecked/<spanning_blocks>", |b| {
        b.iter(|| unsafe {
            let mut br = BitReader::new(&mut buf);
            black_box(br.read_ubit64_unchecked(60));
            black_box(br.read_ubit64_unchecked(8));
        })
    });
    group.bench_function("read_ubit64/<spanning_blocks>", |b| {
        b.iter(|| {
            let mut br = BitReader::new(&mut buf);
            black_box(br.read_ubit64(60).unwrap());
            black_box(br.read_ubit64(8).unwrap());
        })
    });

    group.finish();
}

fn main() {
    let mut c = Criterion::default()
        // NOTE: due to CyclesPerByte's requirements this benchmark should be started with certain
        // flags:
        // $ RUSTFLAGS="--cfg rdpru" taskset --cpu-list 0 cargo bench
        .with_measurement(CyclesPerByte)
        .configure_from_args();

    bench_write_ubit64(&mut c);
    bench_read_ubit64(&mut c);

    c.final_summary();
}
