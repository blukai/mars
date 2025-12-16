use std::collections::HashMap;
use std::hint::black_box;
use std::iter;

use containers::sortedarray::GrowableSortedArrayMap;
use criterion::Criterion;

fn bench_sortedvectormap(c: &mut Criterion) {
    let mut g = c.benchmark_group("sortedvectormap");

    g.bench_function("insert", |b| {
        b.iter(|| {
            let mut svm = GrowableSortedArrayMap::new_growable_in(alloc::Global);
            for (i, _) in black_box(iter::repeat_n((), 128)).enumerate() {
                black_box(svm.insert(i, ()));
            }
        })
    });

    g.bench_function("get", |b| {
        let mut svm = GrowableSortedArrayMap::new_growable_in(alloc::Global);
        iter::repeat_n((), 128)
            .enumerate()
            .for_each(|(i, _)| svm.insert(i, ()));
        b.iter(|| {
            for (i, _) in black_box(iter::repeat_n((), 128)).enumerate() {
                black_box({
                    _ = svm.get(&i);
                });
            }
        })
    });

    g.finish();
}

fn bench_std(c: &mut Criterion) {
    let mut g = c.benchmark_group("std");

    g.bench_function("insert", |b| {
        b.iter(|| {
            let mut hm = HashMap::new();
            for (i, _) in black_box(iter::repeat_n((), 128)).enumerate() {
                black_box({
                    _ = hm.insert(i, ());
                });
            }
        })
    });

    g.bench_function("get", |b| {
        let mut hm = HashMap::new();
        for (i, _) in iter::repeat_n((), 128).enumerate() {
            _ = hm.insert(i, ());
        }
        b.iter(|| {
            for (i, _) in black_box(iter::repeat_n((), 128)).enumerate() {
                black_box({
                    _ = hm.get(&i);
                });
            }
        })
    });

    g.finish();
}

fn main() {
    let mut c = Criterion::default().configure_from_args();
    bench_sortedvectormap(&mut c);
    bench_std(&mut c);
    c.final_summary();
}
