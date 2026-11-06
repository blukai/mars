use containers::unmanagedexponentialhashtable::UnmanagedExponentialHashMap;

fn main() {
    // let start = std::time::Instant::now();

    let mut m = UnmanagedExponentialHashMap::<i32, i32, hash::fxhash::FxBuildHasher>::default();

    // Try this a few times to make sure we never screw up the hashmap's
    // internal state.
    for _ in 0..10 {
        assert!(m.len() == 0);

        for i in 1..1001 {
            assert!(m.insert(alloc::Global, i, i).1.is_none());

            for j in 1..=i {
                let r = m.find(&j);
                assert_eq!(r, Some(&j));
            }

            for j in i + 1..1001 {
                let r = m.find(&j);
                assert_eq!(r, None);
            }
        }

        for i in 1001..2001 {
            assert!(m.find(&i).is_none());
        }

        // remove forwards
        for i in 1..1001 {
            assert!(m.remove(&i).is_some());

            for j in 1..=i {
                assert!(m.find(&j).is_none());
            }

            for j in i + 1..1001 {
                assert!(m.find(&j).is_some());
            }
        }

        for i in 1..1001 {
            assert!(m.find(&i).is_none());
        }

        for i in 1..1001 {
            assert!(m.insert(alloc::Global, i, i).1.is_none());
        }

        // remove backwards
        for i in (1..1001).rev() {
            assert!(m.remove(&i).is_some());

            for j in i..1001 {
                assert!(m.find(&j).is_none());
            }

            for j in 1..i {
                assert!(m.find(&j).is_some());
            }
        }
    }

    // dbg!("my", start.elapsed());
}
