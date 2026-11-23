//! Why a parse failed, for error messages.
//!
//! The verified parser decides *whether* a text is JSON; where and why it
//! failed are diagnostics outside its spec. This module works them out
//! after the fact from the failure position the parser reports, by
//! rescanning the input up to that point. It is ordinary safe Rust and is
//! not verified.
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

fn is_ws(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\r')
}

type Fail = (usize, ErrorKind);

fn hex4(s: &[u8], i: usize) -> Option<u32> {
    let h = s.get(i..i + 4)?;
    let mut v = 0;
    for &c in h {
        v = v * 16 + (c as char).to_digit(16)?;
    }
    Some(v)
}

/// Lexes the string starting at the quote `s[i]`; returns its end.
fn lex_string(s: &[u8], i: usize) -> Result<usize, Fail> {
    let mut j = i + 1;
    loop {
        let Some(&c) = s.get(j) else { return Err((s.len(), ErrorKind::UnterminatedString)) };
        match c {
            b'"' => return Ok(j + 1),
            0..=0x1F => return Err((j, ErrorKind::ControlCharacter(c))),
            b'\\' => {
                let Some(&e) = s.get(j + 1) else { return Err((s.len(), ErrorKind::UnterminatedString)) };
                match e {
                    b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => j += 2,
                    b'u' => {
                        let Some(u) = hex4(s, j + 2) else { return Err((j, ErrorKind::InvalidEscape)) };
                        if (0xD800..0xDC00).contains(&u) {
                            // A high surrogate needs a low one right after.
                            let low = if s.get(j + 6..j + 8) == Some(b"\\u") { hex4(s, j + 8) } else { None };
                            match low {
                                Some(l) if (0xDC00..0xE000).contains(&l) => j += 12,
                                _ => return Err((j, ErrorKind::InvalidEscape)),
                            }
                        } else if (0xDC00..0xE000).contains(&u) {
                            return Err((j, ErrorKind::InvalidEscape));
                        } else {
                            j += 6;
                        }
                    }
                    _ => return Err((j, ErrorKind::InvalidEscape)),
                }
            }
            _ => j += 1,
        }
    }
}

/// Lexes the number starting at `s[i]`; returns its end.
fn lex_number(s: &[u8], i: usize) -> Result<usize, Fail> {
    let digit = |j: usize| s.get(j).is_some_and(u8::is_ascii_digit);
    let digits = |mut j: usize| -> Result<usize, Fail> {
        if !digit(j) {
            return Err((i, ErrorKind::InvalidNumber));
        }
        while digit(j) {
            j += 1;
        }
        Ok(j)
    };
    let mut j = i;
    if s.get(j) == Some(&b'-') {
        j += 1;
    }
    if s.get(j) == Some(&b'0') {
        j += 1;
        if digit(j) {
            return Err((i, ErrorKind::InvalidNumber));
        }
    } else {
        j = digits(j)?;
    }
    if s.get(j) == Some(&b'.') {
        j = digits(j + 1)?;
    }
    if matches!(s.get(j), Some(b'e' | b'E')) {
        j += 1;
        if matches!(s.get(j), Some(b'+' | b'-')) {
            j += 1;
        }
        j = digits(j)?;
    }
    Ok(j)
}

/// Lexes the literal starting at `s[i]` (`t`, `f` or `n`); returns its end.
fn lex_literal(s: &[u8], i: usize) -> Result<usize, Fail> {
    let lit: &[u8] = match s[i] {
        b't' => b"true",
        b'f' => b"false",
        _ => b"null",
    };
    for (k, &c) in lit.iter().enumerate() {
        match s.get(i + k) {
            None => return Err((s.len(), ErrorKind::UnexpectedEnd)),
            Some(&d) if d != c => return Err((i, ErrorKind::InvalidLiteral)),
            _ => {}
        }
    }
    Ok(i + lit.len())
}

/// Lexes the token starting at `s[i]`, if it starts one.
fn lex_token(s: &[u8], i: usize) -> Option<Result<usize, Fail>> {
    match s[i] {
        b'"' => Some(lex_string(s, i)),
        b'-' | b'0'..=b'9' => Some(lex_number(s, i)),
        b't' | b'f' | b'n' => Some(lex_literal(s, i)),
        _ => None,
    }
}

/// The parser's state at a position, as far as a plain scan can tell.
struct Scan {
    /// Open brackets and braces.
    stack: Vec<u8>,
    /// The last byte outside strings that was not whitespace, with a string
    /// counting as `"`.
    prev: Option<u8>,
    /// Start of the string, number or literal that the position is inside.
    token: Option<usize>,
}

/// Scans `s[start..p]` without checking it.
fn scan(s: &[u8], start: usize, p: usize) -> Scan {
    let mut sc = Scan { stack: Vec::new(), prev: None, token: None };
    let mut i = start;
    while i < p {
        let c = s[i];
        if c == b'"' {
            // Find the closing quote.
            let mut j = i + 1;
            while j < s.len() && s[j] != b'"' {
                j += if s[j] == b'\\' { 2 } else { 1 };
            }
            if j >= p {
                sc.token = Some(i);
                return sc;
            }
            sc.prev = Some(b'"');
            i = j + 1;
            continue;
        }
        match c {
            b'[' | b'{' => sc.stack.push(c),
            b']' | b'}' => {
                sc.stack.pop();
            }
            _ => {}
        }
        if is_ws(c) || matches!(c, b'[' | b'{' | b']' | b'}' | b',' | b':') {
            sc.token = None;
        } else if sc.token.is_none() {
            sc.token = Some(i);
        }
        if !is_ws(c) {
            sc.prev = Some(c);
        }
        i += 1;
    }
    sc
}

fn line_col(s: &[u8], p: usize) -> (usize, usize) {
    let p = p.min(s.len());
    let line = 1 + s[..p].iter().filter(|&&c| c == b'\n').count();
    let col = 1 + p - s[..p].iter().rposition(|&c| c == b'\n').map_or(0, |i| i + 1);
    (line, col)
}

fn at(s: &[u8], (offset, kind): Fail) -> Error {
    let (line, column) = line_col(s, offset);
    Error { offset, line, column, kind }
}

/// What is wrong at `p`, which the parser reached in state `sc`.
fn explain(s: &[u8], sc: &Scan, p: usize) -> Fail {
    // Inside a token: relex it from its start.
    if let Some(t) = sc.token {
        if let Some(Err(f)) = lex_token(s, t) {
            return f;
        }
    }
    if p >= s.len() {
        return (s.len(), ErrorKind::UnexpectedEnd);
    }
    let c = s[p];
    let in_object = sc.stack.last() == Some(&b'{');
    let want_value = match sc.prev {
        None | Some(b'[') | Some(b':') => true,
        Some(b',') => !in_object,
        _ => false,
    };
    let want_key = in_object && matches!(sc.prev, Some(b'{') | Some(b','));
    if want_value || (want_key && c == b'"') {
        if (c == b'[' || c == b'{') && sc.stack.len() >= crate::spec::MAX_DEPTH as usize {
            return (p, ErrorKind::TooDeep);
        }
        match lex_token(s, p) {
            Some(Err(f)) => return f,
            Some(Ok(end)) => {
                // The token is fine; the problem is what follows it.
                let mut q = end;
                while q < s.len() && is_ws(s[q]) {
                    q += 1;
                }
                return if q >= s.len() { (q, ErrorKind::UnexpectedEnd) } else { (q, ErrorKind::UnexpectedByte(s[q])) };
            }
            None => {}
        }
    }
    (p, ErrorKind::UnexpectedByte(c))
}

/// Explains a failure that the one-pass parser reported at `p` (its
/// `Err(p)`). `require_end` is the mode it ran in.
pub(crate) fn diagnose(s: &[u8], require_end: bool, p: usize) -> Error {
    if s.len() > crate::spec::MAX_INPUT {
        return at(s, (0, ErrorKind::TooLarge));
    }
    let start = if s.starts_with(&[0xEF, 0xBB, 0xBF]) { 3 } else { 0 };
    let p = p.clamp(start, s.len());
    // The parser checks UTF-8 after the grammar, and reports a UTF-8
    // failure at the end of the text it checked. Report the first bad byte
    // if it comes before the grammar error.
    let utf8 = |end: usize| std::str::from_utf8(&s[start..end]).err().map(|e| (start + e.valid_up_to(), ErrorKind::InvalidUtf8));
    if let Some(f) = utf8(p) {
        return at(s, f);
    }
    if require_end {
        if let Ok((_, end)) = crate::parser::parse_document(s, false) {
            let mut e = end;
            while e < s.len() && is_ws(s[e]) {
                e += 1;
            }
            if e < s.len() {
                return at(s, (e, ErrorKind::TrailingData));
            }
        }
    }
    if let Some(f) = utf8(s.len()) {
        if p >= s.len() || crate::parser::parse_document(s, false).is_ok() {
            return at(s, f);
        }
    }
    let sc = scan(s, start, p);
    at(s, explain(s, &sc, p))
}
