use std::collections::HashMap;
use std::hint::black_box;
use std::iter;

use containers::sortedarray::GrowableSortedArrayMap;
use criterion::Criterion;

const N: usize = 64;

const LIPSUM: &str = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nullam sit amet lorem eros. Phasellus quis metus ac mi elementum fringilla. Pellentesque arcu magna, suscipit et finibus vel, facilisis in est. Orci varius natoque penatibus et magnis dis parturient montes, nascetur ridiculus mus. Nulla condimentum est et lacus lacinia, non ultricies erat pretium. Class aptent taciti sociosqu ad litora torquent per conubia nostra, per inceptos.";

fn lipsum() -> [&'static str; N] {
    let mut acc = std::mem::MaybeUninit::<[&'static str; N]>::uninit();
    let ptr = acc.as_mut_ptr().cast::<&'static str>();
    for (i, part) in LIPSUM.split(" ").enumerate() {
        unsafe { ptr.add(i).write(part) };
    }
    unsafe { acc.assume_init() }
}

fn bench_sortedarraymap(c: &mut Criterion) {
    let lipsum = lipsum();
    let mut g = c.benchmark_group("sortedarraymap");

    g.bench_function("insert number", |b| {
        b.iter(|| {
            let mut thing = GrowableSortedArrayMap::new_growable_in(alloc::Global);
            for (i, _) in black_box(iter::repeat_n((), N)).enumerate() {
                black_box(thing.insert(i, ()));
            }
        })
    });
    g.bench_function("get number", |b| {
        let mut thing = GrowableSortedArrayMap::new_growable_in(alloc::Global);
        iter::repeat_n((), N)
            .enumerate()
            .for_each(|(i, _)| thing.insert(i, ()));
        b.iter(|| {
            for (i, _) in black_box(iter::repeat_n((), N)).enumerate() {
                black_box(_ = thing.get(&i));
            }
        })
    });

    g.bench_function("insert string", |b| {
        b.iter(|| {
            let mut thing = GrowableSortedArrayMap::new_growable_in(alloc::Global);
            for (i, _) in black_box(iter::repeat_n((), N)).enumerate() {
                black_box(thing.insert(lipsum[i], ()));
            }
        })
    });
    g.bench_function("get string", |b| {
        let mut thing = GrowableSortedArrayMap::new_growable_in(alloc::Global);
        iter::repeat_n((), N)
            .enumerate()
            .for_each(|(i, _)| thing.insert(lipsum[i], ()));
        b.iter(|| {
            for (i, _) in black_box(iter::repeat_n((), N)).enumerate() {
                black_box(_ = thing.get(&lipsum[i]));
            }
        })
    });

    g.finish();
}

fn bench_std(c: &mut Criterion) {
    let lipsum = lipsum();
    let mut g = c.benchmark_group("std");

    g.bench_function("insert number", |b| {
        b.iter(|| {
            let mut hm = HashMap::new();
            for (i, _) in black_box(iter::repeat_n((), N)).enumerate() {
                black_box(_ = hm.insert(i, ()));
            }
        })
    });
    g.bench_function("get number", |b| {
        let mut hm = HashMap::new();
        for (i, _) in iter::repeat_n((), N).enumerate() {
            _ = hm.insert(i, ());
        }
        b.iter(|| {
            for (i, _) in black_box(iter::repeat_n((), N)).enumerate() {
                black_box(_ = hm.get(&i));
            }
        })
    });

    g.bench_function("insert string", |b| {
        b.iter(|| {
            let mut hm = HashMap::new();
            for (i, _) in black_box(iter::repeat_n((), N)).enumerate() {
                black_box(_ = hm.insert(lipsum[i], ()));
            }
        })
    });
    g.bench_function("get string", |b| {
        let mut hm = HashMap::new();
        for (i, _) in iter::repeat_n((), N).enumerate() {
            _ = hm.insert(lipsum[i], ());
        }
        b.iter(|| {
            for (i, _) in black_box(iter::repeat_n((), N)).enumerate() {
                black_box(_ = hm.get(&lipsum[i]));
            }
        })
    });

    g.finish();
}

fn main() {
    let mut c = Criterion::default().configure_from_args();
    bench_sortedarraymap(&mut c);
    bench_std(&mut c);
    c.final_summary();
}
