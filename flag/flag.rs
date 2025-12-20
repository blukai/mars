//! based on go's flag package: <https://pkg.go.dev/flag>.
//!
//! incorporates tsoding's idea for ignoring flags: <https://github.com/tsoding/flag.h>.

use std::borrow::Cow;
use std::ffi::{OsStr, OsString};
use std::ops::{ControlFlow, Range};
use std::path::PathBuf;
use std::{cmp, error, fmt, io, str};

use alloc::Allocator;
use containers::sortedarray::{SortedArrayCompare, SpillableSortedArraySet};

// NOTE: this is tsoding's idea, see https://github.com/tsoding/flag.h.
pub const IGNORE_MARKER: char = '/';

pub type ValueError = Box<dyn std::error::Error>;

pub trait Value<'s>: fmt::Debug {
    fn parse(s: Cow<'s, str>) -> Result<Self, ValueError>
    where
        Self: Sized;

    fn assign(&mut self, s: Cow<'s, str>) -> Result<(), ValueError>;

    fn type_name(&self) -> &'static str {
        std::any::type_name::<Self>()
    }

    fn type_is_bool() -> bool
    where
        Self: Sized,
    {
        false
    }

    fn is_bool(&self) -> bool {
        false
    }

    fn is_none(&self) -> bool {
        false
    }
}

impl<'s> Value<'s> for bool {
    fn parse(s: Cow<'s, str>) -> Result<Self, ValueError>
    where
        Self: Sized,
    {
        // NOTE: all of these variations of true/false are same as in go's flag, see
        // https://pkg.go.dev/flag#hdr-Command_line_flag_syntax
        match s.as_ref() {
            "1" | "t" | "T" | "true" | "TRUE" | "True" => Ok(true),
            "0" | "f" | "F" | "false" | "FALSE" | "False" => Ok(false),
            _ => Err(format!("{s} could not be parsed as bool").into()),
        }
    }

    fn assign(&mut self, s: Cow<'s, str>) -> Result<(), ValueError> {
        Self::parse(s).map(|v| *self = v)
    }

    fn type_is_bool() -> bool
    where
        Self: Sized,
    {
        true
    }

    fn is_bool(&self) -> bool {
        Self::type_is_bool()
    }
}

impl<'s> Value<'s> for Cow<'s, str> {
    fn parse(s: Cow<'s, str>) -> Result<Self, ValueError>
    where
        Self: Sized,
    {
        Ok(s)
    }

    fn assign(&mut self, s: Cow<'s, str>) -> Result<(), ValueError> {
        Self::parse(s).map(|v| *self = v)
    }
}

impl<'s, T> Value<'s> for Option<T>
where
    T: Value<'s>,
{
    fn parse(s: Cow<'s, str>) -> Result<Self, ValueError>
    where
        Self: Sized,
    {
        T::parse(s).map(Some)
    }

    fn assign(&mut self, s: Cow<'s, str>) -> Result<(), ValueError> {
        Self::parse(s).map(|v| *self = v)
    }

    fn type_is_bool() -> bool
    where
        Self: Sized,
    {
        T::type_is_bool()
    }

    fn is_bool(&self) -> bool {
        Self::type_is_bool()
    }

    fn is_none(&self) -> bool {
        self.is_none()
    }
}

// NOTE: i give up on trying to do auto impls purely with trait system.
//   maybe try again when trait specialization is out.

// NOTE: impl_value_from_borrowed is for types that result in parsing types discard the source &str/String.
macro_rules! impl_value_for_from_borrowed {
    ($t:ty) => {
        impl<'s> Value<'s> for $t {
            fn parse(s: Cow<'s, str>) -> Result<Self, ValueError> {
                std::str::FromStr::from_str(s.as_ref()).map_err(ValueError::from)
            }

            fn assign(&mut self, s: Cow<'s, str>) -> Result<(), ValueError> {
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
        impl<'s> Value<'s> for $t {
            fn parse(s: Cow<'s, str>) -> Result<Self, ValueError> {
                Ok(<$t>::from(s.into_owned()))
            }

            fn assign(&mut self, s: Cow<'s, str>) -> Result<(), ValueError> {
                Self::parse(s).map(|v| *self = v)
            }
        }
    };
}

impl_value_for_from_owned!(OsString);
impl_value_for_from_owned!(PathBuf);
impl_value_for_from_owned!(String);

#[test]
fn test_is_bool() {
    assert!(true.is_bool());
    assert!(false.is_bool());
    assert!(None::<bool>.is_bool());
    assert!(bool::type_is_bool());

    assert!(!42u8.is_bool());
    assert!(!None::<u8>.is_bool());
    assert!(!u8::type_is_bool());
}

#[test]
fn test_is_none() {
    assert!((&None::<bool> as &dyn Value).is_none());
    assert!(!(&Some(true) as &dyn Value).is_none());
}

#[derive(Debug)]
pub enum ArgKind<'s> {
    OsStr(&'s OsStr),
    OsString(OsString),
}

impl<'s> ArgKind<'s> {
    pub fn as_os_str(&self) -> &OsStr {
        match self {
            Self::OsStr(os_str) => os_str,
            Self::OsString(os_string) => os_string.as_os_str(),
        }
    }

    pub fn into_cow_str(self) -> Result<Cow<'s, str>, Self> {
        match self {
            Self::OsStr(os_str) => <&'s str>::try_from(os_str)
                .map(Cow::Borrowed)
                .map_err(|_| self),
            Self::OsString(os_string) => os_string
                .into_string()
                .map(Cow::Owned)
                .map_err(Self::OsString),
        }
    }
}

#[derive(Debug)]
pub enum ParseBreak<'s> {
    Help,
    NonFlag(ArgKind<'s>),
    // the "--" terminator. see guideline 10 of
    // https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap12.html
    Terminator,
}

#[derive(Debug)]
pub enum ParseError<'a, 's> {
    InvalidArg(ArgKind<'s>),
    InvalidSyntax { arg: Cow<'s, str> },
    UnknownFlag { flag_name: Cow<'s, str> },
    MissingValue { flag_name: &'a str },
    CouldNotAssignValue { flag_name: &'a str, err: ValueError },
}

impl<'a, 's> error::Error for ParseError<'a, 's> {}

// NOTE: anyhow is whining about ParseError not being Send+Sync.
unsafe impl<'a, 's> Send for ParseError<'a, 's> {}
unsafe impl<'a, 's> Sync for ParseError<'a, 's> {}

impl<'a, 's> fmt::Display for ParseError<'a, 's> {
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
pub enum ParseOutcome<'a, 's> {
    Ok,
    Break(ParseBreak<'s>),
    Error(ParseError<'a, 's>),
}

struct Flag<'a, 's> {
    name: &'a str,
    value: &'a mut dyn Value<'s>,
    usage: &'a str,
    dirty: bool,
}

impl<'a, 's> SortedArrayCompare for Flag<'a, 's> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.name, other.name)
    }
}

fn parse_one<'a, 's, I>(
    args: &mut I,
    flags: &mut [Flag<'a, 's>],
) -> Result<ControlFlow<Option<ParseBreak<'s>>>, ParseError<'a, 's>>
where
    I: Iterator<Item = ArgKind<'s>>,
{
    let Some(arg_kind) = args.next() else {
        return Ok(ControlFlow::Break(None));
    };

    // NOTE: don't convert into cow str, just yet. maybe we'll need to return it to the caller.
    let arg_bytes = arg_kind.as_os_str().as_encoded_bytes();
    if !arg_bytes.starts_with(b"-") {
        // NOTE: non-flag arg, terminate.
        return Ok(ControlFlow::Break(Some(ParseBreak::NonFlag(arg_kind))));
    }
    let mut num_minuses = 1;
    if arg_bytes[num_minuses..].starts_with(b"-") {
        num_minuses += 1;
        // NOTE: `--` terminates flags.
        if arg_bytes == b"--" {
            return Ok(ControlFlow::Break(Some(ParseBreak::Terminator)));
        }
    }

    let arg = arg_kind.into_cow_str().map_err(ParseError::InvalidArg)?;

    let mut ignore = false;
    if arg[num_minuses..].starts_with(IGNORE_MARKER) {
        num_minuses += 1;
        ignore = true;
    }

    let mut name = &arg[num_minuses..];
    if name.is_empty() || name.starts_with(&['-', '=']) {
        return Err(ParseError::InvalidSyntax { arg });
    }

    let mut maybe_value_range = None::<Range<usize>>;
    for (i, c) in name.char_indices() {
        if c == '=' {
            maybe_value_range = {
                let start = num_minuses + i + 1;
                let end = num_minuses + name.len();
                Some(start..end)
            };
            name = &name[..i];
            break;
        }
    }

    let Some(flag) = flags.iter_mut().find(|f| f.name == name) else {
        return match name {
            "help" | "h" => Ok(ControlFlow::Break(Some(ParseBreak::Help))),
            _ => Err(ParseError::UnknownFlag { flag_name: arg }),
        };
    };

    let value: Cow<'s, str> = match maybe_value_range {
        Some(value_range) => match arg {
            Cow::Borrowed(str) => Cow::Borrowed(&str[value_range]),
            Cow::Owned(mut string) => {
                string.replace_range(0..value_range.start, "");
                Cow::Owned(string)
            }
        },
        // NOTE: bool is a special case.
        //   it doesn't require an arg, but is allowed to have it.
        //   unlike with any other kind of flag space is not allowed between flag name and its
        //   value because of * wildcard.
        None if flag.value.is_bool() => Cow::Borrowed("true"),
        _ => args
            .next()
            .ok_or(ParseError::MissingValue {
                flag_name: flag.name,
            })?
            .into_cow_str()
            .map_err(ParseError::InvalidArg)?,
    };

    // TODO: should value be validated regardless of whether it's ignored or not?
    if !ignore {
        flag.value
            .assign(value)
            .map_err(|err| ParseError::CouldNotAssignValue {
                flag_name: flag.name,
                err,
            })?;
        flag.dirty = true;
    }

    Ok(ControlFlow::Continue(()))
}

#[derive(Default)]
pub struct FlagSet<'a, 's, const N: usize = 32, A: Allocator = alloc::Global> {
    flags: SpillableSortedArraySet<Flag<'a, 's>, N, A>,
}

impl<'a, 's> FlagSet<'a, 's> {
    pub fn add(mut self, name: &'a str, value: &'a mut dyn Value<'s>, usage: &'a str) -> Self {
        assert!(!name.is_empty(), "empty flag name");
        assert!(!name.starts_with('-'), "flag {name} starts with -");
        assert!(!name.contains('='), "flag {name} contains =");

        let exists = self.flags.0.iter().find(|f| f.name == name).is_some();
        assert!(!exists, "flag redefined: {name}");

        self.flags.insert(Flag {
            name,
            value,
            usage,
            dirty: false,
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
        } in self.flags.0.iter()
        {
            write!(w, "  -{name:<width$}  ")?;
            if !usage.trim().is_empty() {
                write!(w, "{usage}")?;
            }
            match (value.is_none(), dirty) {
                (false, false) => write!(w, " (default: {value:?})")?,
                (false, true) => write!(w, " (dirty: {value:?})")?,
                _ => {}
            }
            write!(w, "\n")?;
        }

        Ok(())
    }

    // NOTE: program name must not be included.
    pub fn parse<I>(&mut self, mut args: I) -> ParseOutcome<'a, 's>
    where
        I: Iterator<Item = ArgKind<'s>>,
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
