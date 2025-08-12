use std::{error, fmt};

#[derive(Debug)]
pub struct OverflowError;

impl fmt::Display for OverflowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "was about to overrun a buffer")
    }
}

impl error::Error for OverflowError {}

#[derive(Debug)]
pub enum ReadIntoBufferError {
    Overflow(OverflowError),
    BufferTooSmall,
}

impl fmt::Display for ReadIntoBufferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow(err) => err.fmt(f),
            Self::BufferTooSmall => write!(f, "buffer too small"),
        }
    }
}

impl error::Error for ReadIntoBufferError {}

#[cfg(feature = "varint")]
#[derive(Debug)]
pub enum ReadVarintError {
    Overflow(OverflowError),
    MalformedVarint,
}

#[cfg(feature = "varint")]
impl fmt::Display for ReadVarintError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow(err) => err.fmt(f),
            Self::MalformedVarint => write!(f, "malformed varint"),
        }
    }
}

#[cfg(feature = "varint")]
impl error::Error for ReadVarintError {}
