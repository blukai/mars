use alloc::Global;
use std::time::Duration;
use std::{env, process, thread};

fn main() {
    let mut fswatch = fswatch::FsWatch::init(Global).expect("could not make fswatch");

    let mut args = env::args();
    let program_name = args.next().expect("program name");
    let mut directories_added = 0;
    while let Some(arg) = args.next() {
        fswatch
            .add_directory(&arg, fswatch::EventFlags::all(), false)
            .expect("could not add directory");
        println!("watching {arg}");
        directories_added += 1;
    }
    if directories_added == 0 {
        println!("usage: {program_name} <directory-to-watch>...");
        process::exit(1);
    }

    loop {
        while let Some(ev) = fswatch.next_event().expect("could not get next event") {
            println!("{ev:?}");
        }

        thread::sleep(Duration::from_millis(333));
    }
}
