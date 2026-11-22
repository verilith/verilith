//! The Rust API: thin, unverified wrappers that turn the verified results
//! into slices. Every span they slice by is proven in bounds (`hdrs_ok`
//! and the parser postconditions), so the slicing never panics.
use crate::chunked::{decode, CState, Decoded};
use crate::framing::{request_body_exec, request_body_fx, response_body_fx};
use crate::parse::{request_fx, request_resume, response_fx, Header, Out, RequestLine, Span, StatusLine};
use crate::diagnose;
use crate::spec::Body;

/// Default limit on field lines per head.
pub const DEFAULT_MAX_HEADERS: usize = 100;

/// Why a message was rejected.
///
/// The decision to reject is verified; the reason is worked out afterwards
/// by unverified code that walks the grammar again (`diagnose.rs`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The request method is not a token followed by one SP.
    Method,
    /// The request target is empty, has a byte not allowed in it, or is
    /// not followed by one SP.
    Target,
    /// The version is not `HTTP/1.` and a digit.
    Version,
    /// The status code is not three digits, or the reason phrase has a
    /// byte not allowed in it.
    Status,
    /// A line ends in a bare LF or CR instead of CRLF.
    NewLine,
    /// A field name is empty or has a byte not allowed in it. This includes
    /// whitespace before the colon and obsolete line folding (a line that
    /// starts with whitespace).
    HeaderName,
    /// A field value has a byte not allowed in it.
    HeaderValue,
    /// More field lines than allowed.
    TooManyHeaders,
    /// Content-Length is not one decimal number of at most 19 digits, or
    /// appears more than once, or a look-alike name (`Content_Length`).
    ContentLength,
    /// Transfer-Encoding is not a list of tokens, appears on more than one
    /// line, has a look-alike name (`Transfer_Encoding`), or (in a
    /// request) `chunked` is missing, not last, or applied twice.
    TransferEncoding,
    /// Content-Length and Transfer-Encoding together.
    ContentLengthAndTransferEncoding,
    /// Transfer-Encoding in an HTTP/1.0 message.
    TransferEncodingHttp10,
    /// No Host in an HTTP/1.1 request, or more than one.
    Host,
    /// A malformed chunked body.
    Chunked,
}

impl Error {
    /// Whether the head is well formed but its framing is ambiguous or
    /// invalid: the request smuggling shapes.
    pub fn is_framing(self) -> bool {
        matches!(
            self,
            Error::ContentLength
                | Error::TransferEncoding
                | Error::ContentLengthAndTransferEncoding
                | Error::TransferEncodingHttp10
                | Error::Host
        )
    }

    fn as_str(self) -> &'static str {
        match self {
            Error::Method => "invalid method",
            Error::Target => "invalid request target",
            Error::Version => "invalid HTTP version",
            Error::Status => "invalid status line",
            Error::NewLine => "line not ended by CRLF",
            Error::HeaderName => "invalid field name",
            Error::HeaderValue => "invalid field value",
            Error::TooManyHeaders => "too many field lines",
            Error::ContentLength => "invalid or repeated Content-Length",
            Error::TransferEncoding => "invalid Transfer-Encoding",
            Error::ContentLengthAndTransferEncoding => "both Content-Length and Transfer-Encoding",
            Error::TransferEncodingHttp10 => "Transfer-Encoding in HTTP/1.0",
            Error::Host => "missing or repeated Host",
            Error::Chunked => "invalid chunked body",
        }
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl std::error::Error for Error {}

/// The result of parsing a head from a buffer that may not hold all of it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status<T> {
    Complete(T),
    /// The buffer ends before the head does; read more and call again.
    Partial,
}

impl Span {
    /// The bytes of this span in `buf`.
    #[inline]
    pub fn of<'b>(&self, buf: &'b [u8]) -> &'b [u8] {
        &buf[self.start..self.end]
    }
}

/// A parsed request head. Field lines are in the `Vec<Header>` passed to
/// the parser.
#[derive(Clone, Copy, Debug)]
pub struct Request<'b> {
    buf: &'b [u8],
    line: RequestLine,
    /// Length of the head; the body starts here.
    pub head_len: usize,
    /// How the body is delimited.
    pub body: Body,
}

impl<'b> Request<'b> {
    pub fn method(&self) -> &'b [u8] {
        self.line.method.of(self.buf)
    }
    pub fn target(&self) -> &'b [u8] {
        self.line.target.of(self.buf)
    }
    /// `x` in `HTTP/1.x`.
    pub fn minor_version(&self) -> u8 {
        self.line.minor
    }
    /// The (name, value) pairs of `headers`, which must be the vector this
    /// request was parsed into.
    pub fn headers<'h>(&self, headers: &'h [Header]) -> impl Iterator<Item = (&'b [u8], &'b [u8])> + 'h + use<'b, 'h>
    where
        'b: 'h,
    {
        let buf = self.buf;
        headers.iter().map(move |h| (h.name.of(buf), h.value.of(buf)))
    }
}

/// A parsed response head.
#[derive(Clone, Copy, Debug)]
pub struct Response<'b> {
    buf: &'b [u8],
    line: StatusLine,
    pub head_len: usize,
    pub body: Body,
}

impl<'b> Response<'b> {
    pub fn minor_version(&self) -> u8 {
        self.line.minor
    }
    pub fn status(&self) -> u16 {
        self.line.status
    }
    pub fn reason(&self) -> &'b [u8] {
        self.line.reason.of(self.buf)
    }
    pub fn headers<'h>(&self, headers: &'h [Header]) -> impl Iterator<Item = (&'b [u8], &'b [u8])> + 'h + use<'b, 'h>
    where
        'b: 'h,
    {
        let buf = self.buf;
        headers.iter().map(move |h| (h.name.of(buf), h.value.of(buf)))
    }
}

/// Parses a request head at the start of `buf`, with at most
/// [`DEFAULT_MAX_HEADERS`] field lines, into `headers` (cleared first).
pub fn parse_request<'b>(
    buf: &'b [u8],
    headers: &mut Vec<Header>,
) -> Result<Status<Request<'b>>, Error> {
    parse_request_with(buf, 0, DEFAULT_MAX_HEADERS, headers)
}

/// [`parse_request`] with a field line limit, and `last_len`, the buffer
/// length at the previous call on the same growing buffer (0 if none):
/// with it, a head that arrives in many small reads costs linear time in
/// total instead of quadratic.
pub fn parse_request_with<'b>(
    buf: &'b [u8],
    last_len: usize,
    max_headers: usize,
    headers: &mut Vec<Header>,
) -> Result<Status<Request<'b>>, Error> {
    let mut fx = None;
    let (r, _) = if last_len == 0 {
        request_fx(buf, max_headers, headers, true, &mut fx)
    } else {
        request_resume(buf, last_len, max_headers, headers)
    };
    match r {
        Out::Done(line, head_len) => match if last_len == 0 {
            request_body_fx(buf, line, headers, fx)
        } else {
            request_body_exec(buf, line, headers)
        } {
            Some(body) => Ok(Status::Complete(Request { buf, line, head_len, body })),
            None => Err(diagnose::framing(buf, headers, line.minor, true, true)),
        },
        Out::Partial => Ok(Status::Partial),
        Out::Invalid => Err(diagnose::request(buf, max_headers)),
    }
}

/// Parses a response head. `head_request` and `connect_request` say
/// whether the request it answers was HEAD or CONNECT, which changes the
/// framing (RFC 9112 §6.3).
pub fn parse_response<'b>(
    buf: &'b [u8],
    head_request: bool,
    connect_request: bool,
    headers: &mut Vec<Header>,
) -> Result<Status<Response<'b>>, Error> {
    let mut fx = None;
    let (r, _) = response_fx(buf, DEFAULT_MAX_HEADERS, headers, true, &mut fx);
    match r {
        Out::Done(line, head_len) => {
            match response_body_fx(buf, line, headers, fx, head_request, connect_request) {
                Some(body) => Ok(Status::Complete(Response { buf, line, head_len, body })),
                None => Err(diagnose::framing(buf, headers, line.minor, false, false)),
            }
        }
        Out::Partial => Ok(Status::Partial),
        Out::Invalid => Err(diagnose::response(buf, DEFAULT_MAX_HEADERS)),
    }
}

/// The result of one [`ChunkedDecoder::decode`] call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Chunked {
    /// All input consumed; `out` body bytes are at the front of the buffer.
    More { out: usize },
    /// The body ended. `out` body bytes are at the front of the buffer,
    /// followed by the `rest` bytes that came after the body.
    Done { out: usize, rest: usize },
}

/// A streaming, in-place decoder for the chunked transfer coding.
///
/// The decoding is proven independent of how the body is split across
/// calls (`chunked::theorem_split`).
#[derive(Clone, Copy, Debug)]
pub struct ChunkedDecoder {
    state: CState,
    keep_trailers: bool,
}

impl Default for ChunkedDecoder {
    fn default() -> Self {
        Self::new()
    }
}

impl ChunkedDecoder {
    pub fn new() -> Self {
        ChunkedDecoder { state: CState::SizeStart, keep_trailers: false }
    }

    /// A decoder that stops at the trailer section, leaving it (and the
    /// final CRLF) unconsumed for the caller.
    pub fn keeping_trailers() -> Self {
        ChunkedDecoder { state: CState::SizeStart, keep_trailers: true }
    }

    /// Whether the decoder is inside chunk data.
    pub fn in_data(&self) -> bool {
        matches!(self.state, CState::Data { .. })
    }

    /// Decodes `buf` in place.
    pub fn decode(&mut self, buf: &mut [u8]) -> Result<Chunked, Error> {
        let len = buf.len();
        match decode(&mut self.state, buf, len, self.keep_trailers).0 {
            Decoded::Invalid => Err(Error::Chunked),
            Decoded::More { out } => Ok(Chunked::More { out }),
            Decoded::Done { out, consumed } => Ok(Chunked::Done { out, rest: len - consumed }),
        }
    }

    pub(crate) fn state(&self) -> CState {
        self.state
    }

    pub(crate) fn from_state(state: CState, keep_trailers: bool) -> Self {
        ChunkedDecoder { state, keep_trailers }
    }
}
