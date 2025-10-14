//! based on go's flag package: <https://pkg.go.dev/flag>.
//!
//! incorporates tsoding's idea for ignoring flags: <https://github.com/tsoding/flag.h>.

use std::{
    array,
    borrow::Cow,
    error,
    ffi::{OsStr, OsString},
    fmt,
    io::{self, Write as _},
    mem,
    ops::{ControlFlow, Range},
    process, str,
};

// NOTE: who would want more?
const FLAGS_CAP: usize = 1 << 10;
#[cfg(target_pointer_width = "64")]
const _: () = assert!(size_of::<Flag<'_, '_>>() == 48);

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

trait ValueFromStr<'s>: Value<'s> + str::FromStr<Err: Into<ValueError>> {}

impl ValueFromStr<'_> for String {}
impl ValueFromStr<'_> for f32 {}
impl ValueFromStr<'_> for f64 {}
impl ValueFromStr<'_> for i128 {}
impl ValueFromStr<'_> for i16 {}
impl ValueFromStr<'_> for i32 {}
impl ValueFromStr<'_> for i64 {}
impl ValueFromStr<'_> for i8 {}
impl ValueFromStr<'_> for isize {}
impl ValueFromStr<'_> for u128 {}
impl ValueFromStr<'_> for u16 {}
impl ValueFromStr<'_> for u32 {}
impl ValueFromStr<'_> for u64 {}
impl ValueFromStr<'_> for u8 {}
impl ValueFromStr<'_> for usize {}

impl<'s, T: ValueFromStr<'s>> Value<'s> for T {
    fn parse(s: Cow<'s, str>) -> Result<Self, ValueError>
    where
        Self: Sized,
    {
        T::from_str(&s).map_err(|e| e.into())
    }

    fn assign(&mut self, s: Cow<'s, str>) -> Result<(), ValueError> {
        Self::parse(s).map(|v| *self = v)
    }
}

#[derive(Debug)]
pub enum ParseError {
    InvalidArg(OsString),
    InvalidSyntax { arg: String },
    UnknownFlag { name: String },
    MissingValue { flag_name: String },
    CouldNotAssignValue { flag_name: String, err: ValueError },
    HelpNotFirst,
    CouldNotPrintHelp(io::Error),
}

impl error::Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            _ => todo!("ArgError::fmt"),
        }
    }
}

struct Flag<'a, 's> {
    name: &'a str,
    value: &'a mut dyn Value<'s>,
    usage: &'a str,
}

fn print_flags<'a, 's, W: io::Write>(w: &mut W, flags: &[Flag<'a, 's>]) -> io::Result<()> {
    let mut width = 0;
    for Flag { name, .. } in flags {
        width = width.max(name.len());
    }

    for Flag { name, usage, value } in flags {
        write!(w, "  -{name:<width$}  ")?;
        if !usage.trim().is_empty() {
            write!(w, "{usage}")?;
        }
        if !value.is_none() {
            write!(w, " (default: {value:?})")?;
        }
        writeln!(w)?;
    }
    Ok(())
}

fn parse_arg<'a, 's, I>(
    args: &mut I,
    flags: &mut [Flag<'a, 's>],
) -> Result<ControlFlow<()>, ParseError>
where
    I: Iterator<Item = Result<Cow<'s, str>, ParseError>>,
{
    let Some(arg) = args.next().transpose()? else {
        return Ok(ControlFlow::Break(()));
    };

    // NOTE: non-flag arg, terminate.
    if !arg.starts_with('-') {
        return Ok(ControlFlow::Break(()));
    }
    let mut num_minuses = 1;
    if arg[num_minuses..].starts_with('-') {
        num_minuses += 1;
        // NOTE: `--` terminates flags.
        if arg == "--" {
            return Ok(ControlFlow::Break(()));
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
        return Err(ParseError::InvalidSyntax {
            arg: arg.to_string(),
        });
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
        return Err(match name {
            "help" | "h" => ParseError::HelpNotFirst,
            _ => ParseError::UnknownFlag {
                name: name.to_string(),
            },
        });
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
            .ok_or_else(|| ParseError::MissingValue {
                flag_name: name.to_string(),
            })
            .flatten()?,
    };

    // TODO: should value be validated regardless of whether it's ignored or not?
    if !ignore {
        flag.value
            .assign(value)
            .map_err(|err| ParseError::CouldNotAssignValue {
                flag_name: flag.name.to_string(),
                err,
            })?;
    }

    Ok(ControlFlow::Continue(()))
}

pub struct FlagSet<'a, 's> {
    flags: [Option<Flag<'a, 's>>; FLAGS_CAP],
    flags_len: usize,
    help: Option<&'a str>,
}

impl<'a, 's> Default for FlagSet<'a, 's> {
    fn default() -> Self {
        Self {
            flags: array::from_fn(|_| None),
            flags_len: 0,
            help: None,
        }
    }
}

impl<'a, 's> FlagSet<'a, 's> {
    pub fn add(mut self, name: &'a str, value: &'a mut dyn Value<'s>, usage: &'a str) -> Self {
        assert!(!name.is_empty(), "empty flag name");
        assert!(!name.starts_with('-'), "flag {name} starts with -");
        assert!(!name.contains('='), "flag {name} contains =");

        let exists = self
            .flags
            .iter()
            .map_while(Option::as_ref)
            .find(|f| f.name == name)
            .is_some();
        assert!(!exists, "flag redefined: {name}");

        self.flags[self.flags_len] = Some(Flag { name, value, usage });
        self.flags_len += 1;
        self
    }

    pub fn with_help(mut self, help: &'a str) -> Self {
        self.help = Some(help);
        self
    }

    fn parse_args<I>(mut self, args: I) -> Result<(), ParseError>
    where
        I: Iterator<Item = Result<Cow<'s, str>, ParseError>>,
    {
        let flags = {
            // NOTE: rust does niche optimization for Option enum.
            //   it is safe to transmute Option<T> as long as size of Option<T> == size of T
            //   (considering that you are sure that options are Some, and here we are sure of that!).
            const _: () = assert!(size_of::<Option<Flag<'_, '_>>>() == size_of::<Flag<'_, '_>>());
            unsafe { mem::transmute::<_, &mut [Flag<'a, 's>]>(&mut self.flags[..self.flags_len]) }
        };

        // NOTE: unlike go i allow help to be requested only via first argument.
        //
        //   that is because i want to be able to print default values for flags in the help
        //   message; parse_arg function immediately assigns values to registered flags meaning
        //   that if help flag is not first in the list - values for preceeding flags are not
        //   guarnateed to be default anymore.
        //
        //   i don't believe this worse then go. if you want to to request help you usually
        //   wouldn't expect that flag at theoretical position 42 in the list do it, would you?
        //   go's decision to handle it like that seems rather stange to me.
        let mut args = args.peekable();
        match args
            .peek()
            .map(|result| result.as_ref().map(|ok| ok.as_ref()))
        {
            Some(Ok("help" | "-h" | "-help" | "--h" | "--help")) => {
                // NOTE: if help message was requested it seems logical to write it to stdout
                // and not stderr.
                let mut stdout = io::stdout();
                // TODO: print provided help message
                if let Some(help) = self.help {
                    stdout.write(help.as_bytes()).unwrap();
                } else {
                    writeln!(&mut stdout as &mut dyn io::Write, "flags:").unwrap();
                    print_flags(&mut io::stdout(), flags).unwrap();
                }
                process::exit(1);
            }
            Some(Ok("/help" | "-/h" | "-/help" | "--/h" | "--/help")) => {
                // NOTE: respect ignore-syntax!
                _ = args.next();
            }
            _ => {}
        }

        loop {
            match parse_arg(&mut args, flags)? {
                ControlFlow::Continue(_) => {}
                ControlFlow::Break(_) => break,
            }
        }

        Ok(())
    }

    pub fn parse_os_str_args<I>(self, args: I) -> Result<(), ParseError>
    where
        I: Iterator<Item = &'s OsStr>,
    {
        let args = args.map(|os_str| {
            <&'s str>::try_from(os_str)
                .map(Cow::Borrowed)
                .map_err(|_| ParseError::InvalidArg(os_str.to_os_string()))
        });
        self.parse_args(args)
    }

    pub fn parse_os_string_args<I>(self, args: I) -> Result<(), ParseError>
    where
        I: Iterator<Item = OsString>,
    {
        let args = args.map(|os_string| {
            os_string
                .into_string()
                .map(Cow::Owned)
                .map_err(|os_string| ParseError::InvalidArg(os_string))
        });
        self.parse_args(args)
    }
}
