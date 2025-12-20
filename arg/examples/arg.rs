use std::process;

fn main() {
    let Some((argc, argv)) = arg::argc_argv() else {
        eprintln!("argc_argv is not available on this target");
        process::exit(1);
    };

    let mut args = arg::ArgIter::new(argc, argv);
    while let Some(arg) = args.next() {
        println!("{arg:?}");
    }
}
