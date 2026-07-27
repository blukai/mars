use std::io;

#[derive(Debug)]
enum Custom {
    Dark,
    Light,
}

impl flag::Value for Custom {
    fn parse(s: String) -> Result<Self, flag::ValueError>
    where
        Self: Sized,
    {
        match s.as_ref() {
            "dark" => Ok(Self::Dark),
            "light" => Ok(Self::Light),
            _ => Err(format!("invalid custom: {s}").into()),
        }
    }

    fn assign(&mut self, s: String) -> Result<(), flag::ValueError> {
        Self::parse(s).map(|v| *self = v)
    }
}

fn main() {
    let mut string_flag = None::<String>;
    let mut bool_flag = false;
    let mut f64_flag = None::<f64>;
    let mut i8_flag = -42_i8;
    let mut custom_flag = None::<Custom>;
    let mut multi_flag = containers::sortedarray::FixedSortedArraySet::<String, 8>::default();

    {
        let mut flag_set = flag::FlagSet::default()
            .add("string", &mut string_flag, "String flag")
            .add("bool", &mut bool_flag, "bool flag")
            .add("f64", &mut f64_flag, "f64 flag")
            .add("i8", &mut i8_flag, "i8 flag")
            .add("custom", &mut custom_flag, "custom flag")
            .add("multi", &mut multi_flag, "multi flag");
        match flag_set.parse(std::env::args().skip(1)) {
            flag::ParseOutcome::Ok => {}
            flag::ParseOutcome::Break(flag::ParseBreak::Help) => {
                flag_set
                    .print(&mut io::stdout())
                    .expect("could not print flags");
                return;
            }
            flag::ParseOutcome::Break(flag::ParseBreak::NonFlag(arg_kind)) => {
                eprintln!("break at non-flag: {arg_kind:?}");
            }
            flag::ParseOutcome::Break(flag::ParseBreak::Terminator) => {
                eprintln!("break at terminator");
            }
            flag::ParseOutcome::Error(err) => panic!("could not parse flags: {err}"),
        }
    }

    println!("string={string_flag:?}");
    println!("bool={bool_flag}");
    println!("f64={f64_flag:?}");
    println!("i8={i8_flag}");
    println!("custom={custom_flag:?}");
    println!("multi={multi_flag:?}");
}
