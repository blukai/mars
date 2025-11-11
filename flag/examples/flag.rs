use std::borrow::Cow;
use std::ffi::OsString;
use std::path::PathBuf;

#[derive(Debug)]
enum Custom {
    Dark,
    Light,
}

impl<'a> flag::Value<'a> for Custom {
    fn parse(s: Cow<'a, str>) -> Result<Self, flag::ValueError>
    where
        Self: Sized,
    {
        match s.as_ref() {
            "dark" => Ok(Self::Dark),
            "light" => Ok(Self::Light),
            _ => Err(format!("invalid custom: {s}").into()),
        }
    }

    fn assign(&mut self, s: Cow<'a, str>) -> Result<(), flag::ValueError> {
        Self::parse(s).map(|v| *self = v)
    }
}

fn main() {
    const DEFAULT_COW_STR: &'static str = "MOO!";

    let mut cow_str_flag = Cow::<'_, str>::from(DEFAULT_COW_STR);
    let mut os_string_flag = None::<OsString>;
    let mut path_buf_flag = None::<PathBuf>;
    let mut string_flag = None::<String>;
    let mut bool_flag = false;
    let mut f64_flag = None::<f64>;
    let mut i8_flag = -42_i8;
    let mut custom_flag = None::<Custom>;

    let flag_set = flag::FlagSet::default()
        .add("cow-str", &mut cow_str_flag, "Cow<'_, str> flag")
        .add("os-string", &mut os_string_flag, "OsString flag")
        .add("path-buf", &mut path_buf_flag, "PathBuf flag")
        .add("string", &mut string_flag, "String flag")
        .add("bool", &mut bool_flag, "bool flag")
        .add("f64", &mut f64_flag, "f64 flag")
        .add("i8", &mut i8_flag, "i8 flag")
        .add("custom", &mut custom_flag, "custom flag");

    if let Some((argc, argv)) = arg::argc_argv() {
        // TODO: on windows (probably) (well, i don't do argc_argv on windows, nor ever touch
        // windows, BUT) first argument is not guaranteed to be the name of the program.
        flag_set
            .parse_os_str_args(arg::ArgIterator::new(argc, argv).skip(1))
            .expect("invalid args");

        assert!(matches!(cow_str_flag, Cow::Borrowed(_)));
    } else {
        flag_set
            .parse_os_string_args(std::env::args_os().skip(1))
            .expect("invalid args");
    }

    #[rustfmt::skip]
    println!("cow-str={cow_str_flag} (is_borrowed: {})", matches!(cow_str_flag, Cow::Borrowed(_)));
    println!("os-string={os_string_flag:?}");
    println!("string={string_flag:?}");
    println!("path-buf={path_buf_flag:?}");
    println!("bool={bool_flag}");
    println!("f64={f64_flag:?}");
    println!("i8={i8_flag}");
    println!("custom={custom_flag:?}");
}
