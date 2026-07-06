pub mod array;
pub mod bitarray;
pub mod boxed;
pub mod cstring;
pub mod handlearray;
pub mod sortedarray;
pub mod string;
pub mod unmanagedarray;
pub mod unmanagedexponentialarray;

#[cfg(test)]
pub(crate) mod testutil;

#[cold]
#[track_caller]
pub fn panic_bounds_check(index: usize, len: usize) -> ! {
    panic!("index out of bounds: the len is {len} but the index is {index}")
}
