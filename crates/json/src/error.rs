//! Why a parse failed, for error messages.
//!
//! The reason and offset are `diag::doc_fail`'s, computed by the verified
//! `diag::explain`, and the line and column are `diag::line_col`'s. This
//! module only turns them into the public types.
use std::fmt;

/// What was wrong with the input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ErrorKind {
    /// The input ended inside a value.
    UnexpectedEnd,
    /// A string was not closed before the end of the input.
    UnterminatedString,
    /// A byte that cannot appear here (the byte is given).
    UnexpectedByte(u8),
    /// A raw control character (below 0x20) inside a string.
    ControlCharacter(u8),
    /// A backslash escape other than `\" \\ \/ \b \f \n \r \t \uXXXX`, or a
    /// `\u` escape with a lone or reversed surrogate.
    InvalidEscape,
    /// A number that does not follow the JSON grammar, such as `01`, `1.`
    /// or `.5`.
    InvalidNumber,
    /// Something other than `true`, `false` or `null` where one began.
    InvalidLiteral,
    /// Arrays and objects nested deeper than 1000 levels.
    TooDeep,
    /// Bytes other than whitespace after the value.
    TrailingData,
    /// The input is not well-formed UTF-8.
    InvalidUtf8,
    /// The input is over 2^48 - 1 bytes (256 TiB), more than a 64-bit
    /// address space holds today.
    TooLarge,
}

/// A parse failure: what went wrong and where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error {
    /// The byte offset of the problem.
    pub offset: usize,
    /// The 1-based line of `offset` (lines end at `\n`).
    pub line: usize,
    /// The 1-based column of `offset`, in bytes.
    pub column: usize,
    pub kind: ErrorKind,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            ErrorKind::UnexpectedEnd => write!(f, "unexpected end of input"),
            ErrorKind::UnterminatedString => write!(f, "unterminated string"),
            ErrorKind::UnexpectedByte(c) if c.is_ascii_graphic() => write!(f, "unexpected '{}'", c as char),
            ErrorKind::UnexpectedByte(c) => write!(f, "unexpected byte 0x{c:02x}"),
            ErrorKind::ControlCharacter(c) => write!(f, "control character 0x{c:02x} in string"),
            ErrorKind::InvalidEscape => write!(f, "invalid escape in string"),
            ErrorKind::InvalidNumber => write!(f, "invalid number"),
            ErrorKind::InvalidLiteral => write!(f, "invalid literal (expected true, false or null)"),
            ErrorKind::TooDeep => write!(f, "nesting deeper than {}", crate::spec::MAX_DEPTH),
            ErrorKind::TrailingData => write!(f, "data after the JSON value"),
            ErrorKind::InvalidUtf8 => write!(f, "invalid UTF-8"),
            ErrorKind::TooLarge => write!(f, "input of 256 TiB or more"),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at line {} column {} (byte {})", self.kind, self.line, self.column, self.offset)
    }
}

impl std::error::Error for Error {}

impl From<crate::diag::Why> for ErrorKind {
    fn from(w: crate::diag::Why) -> ErrorKind {
        use crate::diag::Why;
        match w {
            Why::UnexpectedEnd => ErrorKind::UnexpectedEnd,
            Why::UnterminatedString => ErrorKind::UnterminatedString,
            Why::UnexpectedByte(c) => ErrorKind::UnexpectedByte(c),
            Why::ControlCharacter(c) => ErrorKind::ControlCharacter(c),
            Why::InvalidEscape => ErrorKind::InvalidEscape,
            Why::InvalidNumber => ErrorKind::InvalidNumber,
            Why::InvalidLiteral => ErrorKind::InvalidLiteral,
            Why::TooDeep => ErrorKind::TooDeep,
            Why::TrailingData => ErrorKind::TrailingData,
            Why::InvalidUtf8 => ErrorKind::InvalidUtf8,
            Why::TooLarge => ErrorKind::TooLarge,
        }
    }
}

/// The error for a text that the parser rejected, in the mode
/// `require_end` it ran in. (`explain` requires that `document` rejects
/// the text, which is what every parser's `Err` means.)
pub(crate) fn diagnose(s: &[u8], require_end: bool) -> Error {
    let (offset, why) = crate::diag::explain(s, require_end);
    let (line, column) = crate::diag::line_col(s, offset);
    Error { offset, line, column, kind: why.into() }
}
