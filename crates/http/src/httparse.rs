//! The API of the [`httparse`](https://docs.rs/httparse/1) crate (the
//! parser hyper uses), implemented on the verified core.
//!
//! Every name, type and signature is httparse 1.10's, so a program written
//! for httparse builds against this module unchanged, and the
//! `compat/httparse` crate re-exports it under httparse's crate name for
//! use with `[patch.crates-io]`. What is parsed differs, deliberately:
//!
//! - The grammar is vhttp's strict one: lines end in CRLF, no obsolete line
//!   folding, no whitespace before a colon, one SP between request line
//!   parts. The leniency switches on [`ParserConfig`] are accepted and
//!   ignored.
//! - Requests and responses whose body framing is ambiguous are rejected
//!   with [`Error::HeaderValue`]: a malformed or repeated Content-Length,
//!   Content-Length with Transfer-Encoding, a malformed Transfer-Encoding,
//!   Transfer-Encoding in HTTP/1.0, and (requests only) a
//!   Transfer-Encoding whose last coding is not `chunked`. The rules are
//!   `spec::request_framing` and `spec::response_body`. Host is not
//!   checked: httparse does not, and it does not affect framing.
//! - On `Status::Partial` and on errors, the method, path, version, code
//!   and reason are left as they were, except that on an invalid request
//!   target `method` is set (so callers that tell method errors from path
//!   errors by it, as hyper does, still can).
//! - `HTTP/1.x` with `x` > 1 is rejected with [`Error::Version`], as in
//!   httparse.
//! - [`parse_chunk_size`] uses the verified chunked state machine, so chunk
//!   extensions must match the RFC 9112 grammar.
use crate::api::Error as VError;
use crate::chunked::{step_exec, CState};
use crate::diagnose;
use crate::framing::{request_framing_fx, response_body_fx};
use crate::parse::{headers_at, request_fx, response_fx, Header as SpanHeader, Out};
use core::fmt;
use core::mem::MaybeUninit;
use std::cell::RefCell;

/// An error in parsing.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Error {
    /// Invalid byte in header name.
    HeaderName,
    /// Invalid byte in header value.
    HeaderValue,
    /// Invalid byte in new line.
    NewLine,
    /// Invalid byte in Response status.
    Status,
    /// Invalid byte where token is required.
    Token,
    /// Parsed more headers than provided buffer can contain.
    TooManyHeaders,
    /// Invalid byte in HTTP version.
    Version,
}

impl Error {
    fn description_str(&self) -> &'static str {
        match *self {
            Error::HeaderName => "invalid header name",
            Error::HeaderValue => "invalid header value",
            Error::NewLine => "invalid new line",
            Error::Status => "invalid response status",
            Error::Token => "invalid token",
            Error::TooManyHeaders => "too many headers",
            Error::Version => "invalid HTTP version",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.description_str())
    }
}

impl std::error::Error for Error {}

impl From<VError> for Error {
    fn from(e: VError) -> Error {
        match e {
            VError::Method | VError::Target => Error::Token,
            VError::Version => Error::Version,
            VError::Status => Error::Status,
            VError::NewLine => Error::NewLine,
            VError::HeaderName => Error::HeaderName,
            VError::TooManyHeaders => Error::TooManyHeaders,
            _ => Error::HeaderValue,
        }
    }
}

/// An error in parsing a chunk size.
#[derive(Debug, PartialEq, Eq)]
pub struct InvalidChunkSize;

impl fmt::Display for InvalidChunkSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid chunk size")
    }
}

/// A Result of any parsing action.
pub type Result<T> = core::result::Result<Status<T>, Error>;

/// The result of a successful parse pass.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Status<T> {
    /// The completed result.
    Complete(T),
    /// A partial result.
    Partial,
}

impl<T> Status<T> {
    /// Convenience method to check if status is complete.
    #[inline]
    pub fn is_complete(&self) -> bool {
        matches!(*self, Status::Complete(..))
    }

    /// Convenience method to check if status is partial.
    #[inline]
    pub fn is_partial(&self) -> bool {
        matches!(*self, Status::Partial)
    }

    /// Convenience method to unwrap a Complete value. Panics if the status
    /// is `Partial`.
    #[inline]
    pub fn unwrap(self) -> T {
        match self {
            Status::Complete(t) => t,
            Status::Partial => panic!("Tried to unwrap Status::Partial"),
        }
    }
}

/// Parser configuration. The leniency switches are accepted for
/// compatibility and have no effect: vhttp parses one strict grammar.
#[derive(Clone, Debug, Default)]
pub struct ParserConfig {
    allow_spaces_after_header_name_in_responses: bool,
    allow_obsolete_multiline_headers_in_responses: bool,
    allow_multiple_spaces_in_request_line_delimiters: bool,
    allow_multiple_spaces_in_response_status_delimiters: bool,
    allow_space_before_first_header_name: bool,
    ignore_invalid_headers_in_responses: bool,
    ignore_invalid_headers_in_requests: bool,
}

impl ParserConfig {
    /// Accepted and ignored.
    pub fn allow_spaces_after_header_name_in_responses(&mut self, value: bool) -> &mut Self {
        self.allow_spaces_after_header_name_in_responses = value;
        self
    }

    /// Accepted and ignored.
    pub fn allow_multiple_spaces_in_request_line_delimiters(&mut self, value: bool) -> &mut Self {
        self.allow_multiple_spaces_in_request_line_delimiters = value;
        self
    }

    /// Whether multiple spaces were requested (they are never allowed).
    pub fn multiple_spaces_in_request_line_delimiters_are_allowed(&self) -> bool {
        self.allow_multiple_spaces_in_request_line_delimiters
    }

    /// Accepted and ignored.
    pub fn allow_multiple_spaces_in_response_status_delimiters(&mut self, value: bool) -> &mut Self {
        self.allow_multiple_spaces_in_response_status_delimiters = value;
        self
    }

    /// Whether multiple spaces were requested (they are never allowed).
    pub fn multiple_spaces_in_response_status_delimiters_are_allowed(&self) -> bool {
        self.allow_multiple_spaces_in_response_status_delimiters
    }

    /// Accepted and ignored.
    pub fn allow_obsolete_multiline_headers_in_responses(&mut self, value: bool) -> &mut Self {
        self.allow_obsolete_multiline_headers_in_responses = value;
        self
    }

    /// Whether obsolete line folding was requested (it is never allowed).
    pub fn obsolete_multiline_headers_in_responses_are_allowed(&self) -> bool {
        self.allow_obsolete_multiline_headers_in_responses
    }

    /// Accepted and ignored.
    pub fn allow_space_before_first_header_name(&mut self, value: bool) -> &mut Self {
        self.allow_space_before_first_header_name = value;
        self
    }

    /// Whether a space before the first header was requested (it is never
    /// allowed).
    pub fn space_before_first_header_name_are_allowed(&self) -> bool {
        self.allow_space_before_first_header_name
    }

    /// Accepted and ignored.
    pub fn ignore_invalid_headers_in_responses(&mut self, value: bool) -> &mut Self {
        self.ignore_invalid_headers_in_responses = value;
        self
    }

    /// Accepted and ignored.
    pub fn ignore_invalid_headers_in_requests(&mut self, value: bool) -> &mut Self {
        self.ignore_invalid_headers_in_requests = value;
        self
    }

    /// Parses a request with the given config.
    pub fn parse_request<'buf>(&self, request: &mut Request<'_, 'buf>, buf: &'buf [u8]) -> Result<usize> {
        request.parse(buf)
    }

    /// Parses a request with the given config and buffer for headers.
    pub fn parse_request_with_uninit_headers<'headers, 'buf>(
        &self,
        request: &mut Request<'headers, 'buf>,
        buf: &'buf [u8],
        headers: &'headers mut [MaybeUninit<Header<'buf>>],
    ) -> Result<usize> {
        request.parse_with_uninit_headers(buf, headers)
    }

    /// Parses a response with the given config.
    pub fn parse_response<'buf>(&self, response: &mut Response<'_, 'buf>, buf: &'buf [u8]) -> Result<usize> {
        response.parse(buf)
    }

    /// Parses a response with the given config and buffer for headers.
    pub fn parse_response_with_uninit_headers<'headers, 'buf>(
        &self,
        response: &mut Response<'headers, 'buf>,
        buf: &'buf [u8],
        headers: &'headers mut [MaybeUninit<Header<'buf>>],
    ) -> Result<usize> {
        response.parse_with_uninit_headers(buf, headers)
    }
}

/// A parsed Request.
#[derive(Debug, Eq, PartialEq)]
pub struct Request<'headers, 'buf> {
    /// The request method, such as `GET`.
    pub method: Option<&'buf str>,
    /// The request path, such as `/about-us`.
    pub path: Option<&'buf str>,
    /// The request minor version, such as `1` for `HTTP/1.1`.
    pub version: Option<u8>,
    /// The request headers.
    pub headers: &'headers mut [Header<'buf>],
}

/// A parsed Response.
#[derive(Debug, Eq, PartialEq)]
pub struct Response<'headers, 'buf> {
    /// The response minor version, such as `1` for `HTTP/1.1`.
    pub version: Option<u8>,
    /// The response code, such as `200`.
    pub code: Option<u16>,
    /// The response reason-phrase, such as `OK`. Empty if the reason
    /// phrase was missing or was not ASCII.
    pub reason: Option<&'buf str>,
    /// The response headers.
    pub headers: &'headers mut [Header<'buf>],
}

/// Represents a parsed header.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Header<'a> {
    /// The name portion of a header.
    pub name: &'a str,
    /// The value portion of a header.
    pub value: &'a [u8],
}

impl fmt::Debug for Header<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_struct("Header");
        f.field("name", &self.name);
        if let Ok(value) = core::str::from_utf8(self.value) {
            f.field("value", &value);
        } else {
            f.field("value", &self.value);
        }
        f.finish()
    }
}

/// An empty header, useful for constructing a `Header` array to pass in for
/// parsing.
pub const EMPTY_HEADER: Header<'static> = Header { name: "", value: b"" };

thread_local! {
    static SPANS: RefCell<Vec<SpanHeader>> = const { RefCell::new(Vec::new()) };
}

/// Bytes known to be ASCII: tokens (methods and field names), which the
/// verified grammar guarantees, or bytes just checked.
fn ascii(b: &[u8]) -> &str {
    debug_assert!(b.is_ascii());
    // SAFETY: tokens are ASCII by `spec::is_tchar`, which the parser is
    // proven to enforce.
    unsafe { core::str::from_utf8_unchecked(b) }
}

/// Writes the parsed field lines into `out`, which has room for them (the
/// parser was given `out.len()` as its limit). Returns the initialized
/// prefix.
fn fill<'h, 'b>(buf: &'b [u8], spans: &[SpanHeader], out: &'h mut [MaybeUninit<Header<'b>>]) -> &'h mut [Header<'b>] {
    let n = spans.len();
    for (o, h) in out.iter_mut().zip(spans) {
        o.write(Header {
            name: ascii(h.name.of(buf)),
            value: h.value.of(buf),
        });
    }
    let init = &mut out[..n];
    // SAFETY: the first `n` entries were just written.
    unsafe { &mut *(init as *mut [MaybeUninit<Header<'b>>] as *mut [Header<'b>]) }
}

/// Views initialized headers as possibly uninitialized, for reuse as
/// output space. Writing only valid `Header`s through it keeps them
/// initialized.
fn as_uninit<'h, 'b>(hs: &'h mut [Header<'b>]) -> &'h mut [MaybeUninit<Header<'b>>] {
    // SAFETY: same layout; callers only write initialized values.
    unsafe { &mut *(hs as *mut [Header<'b>] as *mut [MaybeUninit<Header<'b>>]) }
}

impl<'h, 'b> Request<'h, 'b> {
    /// Creates a new Request, using a slice of headers you allocate.
    #[inline]
    pub fn new(headers: &'h mut [Header<'b>]) -> Request<'h, 'b> {
        Request { method: None, path: None, version: None, headers }
    }

    /// Try to parse a buffer of bytes into the Request.
    ///
    /// Returns byte offset in `buf` to start of HTTP body.
    pub fn parse(&mut self, buf: &'b [u8]) -> Result<usize> {
        let headers = core::mem::take(&mut self.headers);
        let headers: *mut [Header<'b>] = headers;
        // SAFETY: `headers` is the caller's exclusive borrow for 'h,
        // reborrowed once here; on failure it is put back unchanged in
        // length (entries may have been overwritten with valid headers).
        match self.parse_with_uninit_headers(buf, as_uninit(unsafe { &mut *headers })) {
            Ok(Status::Complete(n)) => Ok(Status::Complete(n)),
            other => {
                self.headers = unsafe { &mut *headers };
                other
            }
        }
    }

    /// Try to parse a buffer of bytes into the Request, except use an
    /// uninitialized slice of `Header`s.
    pub fn parse_with_uninit_headers(
        &mut self,
        buf: &'b [u8],
        headers: &'h mut [MaybeUninit<Header<'b>>],
    ) -> Result<usize> {
        SPANS.with(|cell| {
            let spans = &mut *cell.borrow_mut();
            let mut fx = None;
            let (r, _) = request_fx(buf, headers.len(), spans, true, &mut fx);
            match r {
                Out::Done(line, len) => {
                    if line.minor > 1 {
                        return Err(Error::Version);
                    }
                    if request_framing_fx(buf, line.minor, spans, fx).is_none() {
                        return Err(Error::HeaderValue);
                    }
                    // Targets may hold obs-text; httparse wants UTF-8.
                    let t = line.target.of(buf);
                    let path = if t.is_ascii() {
                        ascii(t)
                    } else {
                        core::str::from_utf8(t).map_err(|_| {
                            self.method = Some(ascii(line.method.of(buf)));
                            Error::Token
                        })?
                    };
                    self.method = Some(ascii(line.method.of(buf)));
                    self.path = Some(path);
                    self.version = Some(line.minor);
                    self.headers = fill(buf, spans, headers);
                    Ok(Status::Complete(len))
                }
                Out::Partial => Ok(Status::Partial),
                Out::Invalid => {
                    let e = diagnose::request(buf, headers.len());
                    if e == VError::Target {
                        let s = diagnose::request_start(buf);
                        let me = s + buf[s..].iter().position(|&c| c == b' ').unwrap_or(0);
                        self.method = Some(ascii(&buf[s..me]));
                    }
                    Err(e.into())
                }
            }
        })
    }
}

impl<'h, 'b> Response<'h, 'b> {
    /// Creates a new `Response` using a slice of `Header`s you have
    /// allocated.
    #[inline]
    pub fn new(headers: &'h mut [Header<'b>]) -> Response<'h, 'b> {
        Response { version: None, code: None, reason: None, headers }
    }

    /// Try to parse a buffer of bytes into this `Response`.
    pub fn parse(&mut self, buf: &'b [u8]) -> Result<usize> {
        let headers = core::mem::take(&mut self.headers);
        let headers: *mut [Header<'b>] = headers;
        // SAFETY: as in `Request::parse`.
        match self.parse_with_uninit_headers(buf, as_uninit(unsafe { &mut *headers })) {
            Ok(Status::Complete(n)) => Ok(Status::Complete(n)),
            other => {
                self.headers = unsafe { &mut *headers };
                other
            }
        }
    }

    /// Try to parse a buffer of bytes into this `Response`, except use an
    /// uninitialized slice of `Header`s.
    pub fn parse_with_uninit_headers(
        &mut self,
        buf: &'b [u8],
        headers: &'h mut [MaybeUninit<Header<'b>>],
    ) -> Result<usize> {
        SPANS.with(|cell| {
            let spans = &mut *cell.borrow_mut();
            let mut fx = None;
            let (r, _) = response_fx(buf, headers.len(), spans, true, &mut fx);
            match r {
                Out::Done(line, len) => {
                    if line.minor > 1 {
                        return Err(Error::Version);
                    }
                    // The conflict checks of `response_body` do not depend
                    // on the request method.
                    if response_body_fx(buf, line, spans, fx, false, false).is_none() {
                        return Err(Error::HeaderValue);
                    }
                    let reason = line.reason.of(buf);
                    self.version = Some(line.minor);
                    self.code = Some(line.status);
                    self.reason = Some(if reason.is_ascii() { ascii(reason) } else { "" });
                    self.headers = fill(buf, spans, headers);
                    Ok(Status::Complete(len))
                }
                Out::Partial => Ok(Status::Partial),
                Out::Invalid => Err(diagnose::response(buf, headers.len()).into()),
            }
        })
    }
}

/// Parse a buffer of bytes as headers.
///
/// The return value, if complete and successful, includes the index of the
/// buffer that parsing stopped at, and a sliced reference to the parsed
/// headers.
pub fn parse_headers<'b: 'h, 'h>(src: &'b [u8], dst: &'h mut [Header<'b>]) -> Result<(usize, &'h [Header<'b>])> {
    SPANS.with(|cell| {
        let spans = &mut *cell.borrow_mut();
        spans.clear();
        let (r, _) = headers_at(src, 0, dst.len(), spans);
        match r {
            Out::Done(_, n) => Ok(Status::Complete((n, &*fill(src, spans, as_uninit(dst))))),
            Out::Partial => Ok(Status::Partial),
            Out::Invalid => Err(diagnose::headers(src, 0, dst.len()).into()),
        }
    })
}

/// Parse a buffer of bytes as a chunk size line: the size in hex, optional
/// chunk extensions, and CRLF. Returns the length of the line and the size.
pub fn parse_chunk_size(buf: &[u8]) -> core::result::Result<Status<(usize, u64)>, InvalidChunkSize> {
    let mut s = CState::SizeStart;
    for (i, &c) in buf.iter().enumerate() {
        if let (CState::SizeLf { n }, b'\n') = (s, c) {
            return Ok(Status::Complete((i + 1, n)));
        }
        s = match step_exec(s, c) {
            Some((t, _)) => t,
            None => return Err(InvalidChunkSize),
        };
    }
    Ok(Status::Partial)
}
