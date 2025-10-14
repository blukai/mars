#![no_main]

use std::ffi::{c_char, c_int};

#[unsafe(no_mangle)]
pub fn main(argc: c_int, argv: *mut *mut c_char) {
    let mut args = arg::ArgIterator::new(argc, argv);
    while let Some(arg) = args.next() {
        println!("{arg:?}");
    }
}
