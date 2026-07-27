//! based on go's flag package: <https://pkg.go.dev/flag>.
//!
//! incorporates tsoding's idea for ignoring flags: <https://github.com/tsoding/flag.h>.

use core::ops::{ControlFlow, Range};
use core::{any, cmp, error, fmt, str};
use std::io;

use alloc::Allocator;
use containers::array::ArrayMemory;
use containers::sortedarray::{SortedArrayCompare, SortedArraySet, SpillableSortedArraySet};

// NOTE: everything operates on std String here; no CStr, no OsStr, etc.
//   it's just easier and simpler and cleaner this way.

pub type ValueError = Box<dyn error::Error>;

pub trait Value: fmt::Debug {
    fn parse(s: String) -> Result<Self, ValueError>
    where
        Self: Sized;

    fn assign(&mut self, s: String) -> Result<(), ValueError>;

    fn assign_implicit_true(&mut self) {
        unreachable!();
    }

    fn type_is_bool() -> bool
    where
        Self: Sized,
    {
        false
    }

    fn option_is_none(&self) -> bool {
        false
    }
}

impl Value for bool {
    fn parse(s: String) -> Result<Self, ValueError>
    where
        Self: Sized,
    {
        // NOTE: all of these variations of true/false are same as in go's flag, see
        // https://pkg.go.dev/flag#hdr-Command_line_flag_syntax
        match s.as_ref() {
            "1" | "t" | "T" | "true" | "TRUE" | "True" => Ok(true),
            "0" | "f" | "F" | "false" | "FALSE" | "False" => Ok(false),
            _ => Err(format!("'{s}' could not be parsed as bool").into()),
        }
    }

    fn assign(&mut self, s: String) -> Result<(), ValueError> {
        Self::parse(s).map(|v| *self = v)
    }

    fn assign_implicit_true(&mut self) {
        *self = true;
    }

    fn type_is_bool() -> bool
    where
        Self: Sized,
    {
        true
    }
}

impl<T: Value> Value for Option<T> {
    fn parse(s: String) -> Result<Self, ValueError>
    where
        Self: Sized,
    {
        T::parse(s).map(Some)
    }

    fn assign(&mut self, s: String) -> Result<(), ValueError> {
        if let Some(inner) = self {
            inner.assign(s)
        } else {
            Self::parse(s).map(|v| *self = v)
        }
    }

    fn type_is_bool() -> bool
    where
        Self: Sized,
    {
        T::type_is_bool()
    }

    fn option_is_none(&self) -> bool {
        Option::is_none(self)
    }
}

// NOTE: i give up on trying to do auto impls purely with trait system.
//   maybe try again when trait specialization is out.

// NOTE: impl_value_from_borrowed is for types that result in parsing types discard the source &str/String.
macro_rules! impl_value_for_from_borrowed {
    ($t:ty) => {
        impl Value for $t {
            fn parse(s: String) -> Result<Self, ValueError> {
                str::FromStr::from_str(s.as_ref()).map_err(ValueError::from)
            }

            fn assign(&mut self, s: String) -> Result<(), ValueError> {
                Self::parse(s).map(|v| *self = v)
            }
        }
    };
}

impl_value_for_from_borrowed!(f32);
impl_value_for_from_borrowed!(f64);
impl_value_for_from_borrowed!(i128);
impl_value_for_from_borrowed!(i16);
impl_value_for_from_borrowed!(i32);
impl_value_for_from_borrowed!(i64);
impl_value_for_from_borrowed!(i8);
impl_value_for_from_borrowed!(isize);
impl_value_for_from_borrowed!(u128);
impl_value_for_from_borrowed!(u16);
impl_value_for_from_borrowed!(u32);
impl_value_for_from_borrowed!(u64);
impl_value_for_from_borrowed!(u8);
impl_value_for_from_borrowed!(usize);

// NOTE: impl_value_for_from_owned is for types that want to own String.
macro_rules! impl_value_for_from_owned {
    ($t:ty) => {
        impl Value for $t {
            fn parse(s: String) -> Result<Self, ValueError> {
                Ok(<$t>::from(s))
            }

            fn assign(&mut self, s: String) -> Result<(), ValueError> {
                Self::parse(s).map(|v| *self = v)
            }
        }
    };
}

impl_value_for_from_owned!(String);

impl<T: Value + Ord, M: ArrayMemory<T>> Value for SortedArraySet<T, M> {
    fn parse(s: String) -> Result<Self, ValueError>
    where
        Self: Sized,
    {
        _ = s;
        // NOTE: this is a developer error.
        //
        // MAYBE: can type system can protect from this?
        unreachable!("{} must be initialized", any::type_name::<Self>());
    }

    fn assign(&mut self, s: String) -> Result<(), ValueError> {
        T::parse(s).map(|v| self.insert(v))
    }
}

#[test]
fn test_type_is_bool() {
    assert!(<bool as Value>::type_is_bool());
    assert!(<Option<bool> as Value>::type_is_bool());
}

#[test]
fn test_option_is_none() {
    assert!((&None::<u8> as &dyn Value).option_is_none());
    assert!(!(&Some(0) as &dyn Value).option_is_none());
}

#[derive(Debug)]
pub enum ParseBreak {
    Help,
    NonFlag(String),
    // the "--" terminator. see guideline 10 of
    // https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap12.html
    Terminator,
}

#[derive(Debug)]
pub enum ParseError<'a> {
    InvalidArg(String),
    InvalidSyntax { arg: String },
    UnknownFlag { flag_name: String },
    MissingValue { flag_name: &'a str },
    CouldNotAssignValue { flag_name: &'a str, err: ValueError },
}

impl<'a> error::Error for ParseError<'a> {}

// NOTE: anyhow is whining about ParseError not being Send+Sync.
unsafe impl<'a> Send for ParseError<'a> {}
unsafe impl<'a> Sync for ParseError<'a> {}

impl<'a> fmt::Display for ParseError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidArg(arg) => write!(f, "invalid arg: {arg:?}"),
            Self::InvalidSyntax { arg } => write!(f, "invalid syntax: {arg}"),
            Self::UnknownFlag { flag_name } => {
                write!(f, "flag provided but not defined: {flag_name}")
            }
            Self::MissingValue { flag_name } => write!(f, "flag needs an argument: {flag_name}"),
            Self::CouldNotAssignValue { flag_name, err } => {
                write!(f, "could not assign value to -{flag_name}: {err}")
            }
        }
    }
}

#[derive(Debug)]
pub enum ParseOutcome<'a> {
    Ok,
    Break(ParseBreak),
    Error(ParseError<'a>),
}

struct Flag<'a> {
    name: &'a str,
    value: &'a mut dyn Value,
    usage: &'a str,
    dirty: bool,
    value_type_is_bool: bool,
}

impl<'a> SortedArrayCompare for Flag<'a> {
    fn compare(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.name, other.name)
    }
}

fn parse_one<'a, I>(
    args: &mut I,
    flags: &mut [Flag<'a>],
) -> Result<ControlFlow<Option<ParseBreak>>, ParseError<'a>>
where
    I: Iterator<Item = String>,
{
    let Some(mut arg) = args.next() else {
        return Ok(ControlFlow::Break(None));
    };

    if !arg.starts_with("-") {
        // NOTE: non-flag arg, terminate.
        return Ok(ControlFlow::Break(Some(ParseBreak::NonFlag(arg))));
    }
    let mut num_minuses = 1;
    if arg[num_minuses..].starts_with("-") {
        num_minuses += 1;
        // NOTE: `--` terminates flags.
        if arg == "--" {
            return Ok(ControlFlow::Break(Some(ParseBreak::Terminator)));
        }
    }

    // NOTE: this is tsoding's idea, see https://github.com/tsoding/flag.h.
    let mut ignore = false;
    if arg[num_minuses..].starts_with('/') {
        num_minuses += 1;
        ignore = true;
    }

    let mut name = &arg[num_minuses..];
    if name.is_empty() || name.starts_with(&['-', '=']) {
        return Err(ParseError::InvalidSyntax { arg });
    }

    let mut maybe_value_range = None::<Range<usize>>;
    if let Some(i) = name.find('=') {
        let start = num_minuses + i + 1;
        let end = num_minuses + name.len();
        maybe_value_range = Some(start..end);
        name = &name[..i];
    }

    let Some(flag) = flags.iter_mut().find(|f| f.name == name) else {
        return match name {
            "help" | "h" => Ok(ControlFlow::Break(Some(ParseBreak::Help))),
            _ => Err(ParseError::UnknownFlag { flag_name: arg }),
        };
    };

    macro_rules! assign {
        ($value:expr) => {
            flag.value
                .assign($value)
                .map_err(|err| ParseError::CouldNotAssignValue {
                    flag_name: flag.name,
                    err,
                })
        };
    }

    match maybe_value_range {
        Some(value_range) => {
            if !ignore {
                arg.replace_range(0..value_range.start, "");
                assign!(arg)?;
            }
        }
        // NOTE: bool is a special case.
        //   it doesn't require an arg, but is allowed to have it.
        //   unlike with any other kind of flag space is not allowed between flag name and its
        //   value because of * wildcard.
        None if flag.value_type_is_bool => {
            if !ignore {
                flag.value.assign_implicit_true();
            }
        }
        None => {
            let value = args.next().ok_or(ParseError::MissingValue {
                flag_name: flag.name,
            })?;
            if !ignore {
                assign!(value)?;
            }
        }
    };

    flag.dirty = !ignore;

    Ok(ControlFlow::Continue(()))
}

#[derive(Default)]
pub struct FlagSet<'a, const N: usize = 32, A: Allocator = alloc::Global> {
    flags: SpillableSortedArraySet<Flag<'a>, N, A>,
}

impl<'a> FlagSet<'a> {
    pub fn add<T: Value>(mut self, name: &'a str, value: &'a mut T, usage: &'a str) -> Self {
        assert!(!name.is_empty(), "empty flag name");
        assert!(!name.starts_with('-'), "flag {name} starts with -");
        assert!(!name.contains('='), "flag {name} contains =");

        let exists = self.flags.0.iter().any(|f| f.name == name);
        assert!(!exists, "flag redefined: {name}");

        self.flags.insert(Flag {
            name,
            value,
            usage,
            dirty: false,
            value_type_is_bool: T::type_is_bool(),
        });
        self
    }

    pub fn print<W: io::Write>(&self, w: &mut W) -> io::Result<()> {
        let mut width = 0;
        for Flag { name, .. } in self.flags.0.iter() {
            width = width.max(name.len());
        }

        for Flag {
            name,
            usage,
            value,
            dirty,
            ..
        } in self.flags.0.iter()
        {
            write!(w, "  -{name:<width$}  ")?;
            if !usage.trim().is_empty() {
                write!(w, "{usage}")?;
            }
            match (value.option_is_none(), dirty) {
                (false, false) => write!(w, " (default: {value:?})")?,
                (false, true) => write!(w, " (dirty: {value:?})")?,
                _ => {}
            }
            write!(w, "\n")?;
        }

        Ok(())
    }

    // NOTE: program name must not be included.
    pub fn parse<I>(&mut self, mut args: I) -> ParseOutcome<'a>
    where
        I: Iterator<Item = String>,
    {
        loop {
            match parse_one(&mut args, &mut self.flags.0) {
                Ok(ControlFlow::Continue(..)) => {}
                Ok(ControlFlow::Break(None)) => break,
                Ok(ControlFlow::Break(Some(b))) => return ParseOutcome::Break(b),
                Err(e) => return ParseOutcome::Error(e),
            }
        }
        ParseOutcome::Ok
    }
}
