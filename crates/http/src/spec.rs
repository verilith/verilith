//! The specification: HTTP/1.1 message heads (RFC 9112 §2-5) and message
//! framing (RFC 9112 §6) as total functions over `Seq<u8>`.
//!
//! This file is the trusted part of the crate: read it to check that it says
//! what RFC 9112 says. Every exec parser in the crate is proven to compute
//! exactly these functions. Where RFC 9112 lets a recipient choose between
//! leniency and rejection, the spec rejects; each such choice is marked
//! "Strict".
use vstd::prelude::*;
#[cfg(verus_only)]
pub use verilith_core::num::is_digit;

verus! {

pub const CR: u8 = 0x0D;
pub const LF: u8 = 0x0A;
pub const SP: u8 = 0x20;
pub const HTAB: u8 = 0x09;
pub const COLON: u8 = 0x3A;
pub const COMMA: u8 = 0x2C;

// ---------------------------------------------------------------------------
// Character classes (RFC 9110 §5.6.2, RFC 5234 Appendix B.1)
// ---------------------------------------------------------------------------


pub open spec fn is_alpha(c: u8) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// `tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" / "." /
///          "^" / "_" / "`" / "|" / "~" / DIGIT / ALPHA`
pub open spec fn is_tchar(c: u8) -> bool {
    is_digit(c) || is_alpha(c) || c == 0x21 || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26
        || c == 0x27 || c == 0x2A || c == 0x2B || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F
        || c == 0x60 || c == 0x7C || c == 0x7E
}

/// A byte of a request-target: VCHAR or obs-text. RFC 3986 allows fewer
/// characters; the exact URI grammar is left to the URI layer, as in
/// llhttp and picohttpparser. What matters for framing is that SP and
/// controls (including CR and LF) end the target.
pub open spec fn is_target_char(c: u8) -> bool {
    (0x21 <= c <= 0x7E) || c >= 0x80
}

/// A byte of a field value: `field-vchar / SP / HTAB`, where
/// `field-vchar = VCHAR / obs-text` (RFC 9110 §5.5). NUL, CR, LF and the
/// other controls are never part of a value.
pub open spec fn is_value_char(c: u8) -> bool {
    c == HTAB || (0x20 <= c && c != 0x7F)
}

/// `OWS = *( SP / HTAB )`
pub open spec fn is_ows(c: u8) -> bool {
    c == SP || c == HTAB
}

/// The byte classes the scanners work with.
pub enum Cls {
    Token,
    Target,
    Value,
    Ows,
    Digit,
}

pub open spec fn in_cls(k: Cls, c: u8) -> bool {
    match k {
        Cls::Token => is_tchar(c),
        Cls::Target => is_target_char(c),
        Cls::Value => is_value_char(c),
        Cls::Ows => is_ows(c),
        Cls::Digit => is_digit(c),
    }
}

/// The end of the longest run of class `k` starting at `i`.
pub open spec fn run_end(b: Seq<u8>, i: int, k: Cls) -> int
    decreases b.len() - i,
{
    if i < 0 || i >= b.len() || !in_cls(k, b[i]) {
        i
    } else {
        run_end(b, i + 1, k)
    }
}

/// The end of `b[s..e]` with trailing OWS removed.
pub open spec fn trim_end(b: Seq<u8>, s: int, e: int) -> int
    decreases e - s,
{
    if e <= s || !is_ows(b[e - 1]) {
        e
    } else {
        trim_end(b, s, e - 1)
    }
}

// ---------------------------------------------------------------------------
// Results
// ---------------------------------------------------------------------------

/// The outcome of parsing from some position.
/// - `Done(v, end)`: parsed `v`, and the next unread position is `end`.
/// - `Partial`: every byte so far is consistent with the grammar, but the
///   input ends before the construct does. More input may complete it.
/// - `Invalid`: no extension of the input can be accepted.
pub enum Parsed<T> {
    Done(T, int),
    Partial,
    Invalid,
}

/// A run of class `k` at `i`, nonempty and followed by the byte `d`.
/// The value is the end of the run; the next position is just past `d`.
pub open spec fn run_then(b: Seq<u8>, i: int, k: Cls, d: u8) -> Parsed<int> {
    let e = run_end(b, i, k);
    if e >= b.len() {
        Parsed::Partial
    } else if e == i || b[e] != d {
        Parsed::Invalid
    } else {
        Parsed::Done(e, e + 1)
    }
}

/// The literal `s` at `i`.
pub open spec fn lit(b: Seq<u8>, i: int, s: Seq<u8>) -> Parsed<()> {
    let n = if b.len() - i < s.len() {
        b.len() - i
    } else {
        s.len() as int
    };
    if b.subrange(i, i + n) != s.subrange(0, n) {
        Parsed::Invalid
    } else if n < s.len() {
        Parsed::Partial
    } else {
        Parsed::Done((), i + s.len())
    }
}

pub open spec fn crlf() -> Seq<u8> {
    seq![CR, LF]
}

/// `"HTTP/1."`: the only major version this crate speaks.
pub open spec fn http1_prefix() -> Seq<u8> {
    seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E]
}

// ---------------------------------------------------------------------------
// Message heads (RFC 9112 §2-5)
// ---------------------------------------------------------------------------

/// Positions `start..end` in the input.
pub struct SpecSpan {
    pub start: int,
    pub end: int,
}

pub struct SpecHeader {
    pub name: SpecSpan,
    /// The value with leading and trailing OWS removed (RFC 9112 §5).
    pub value: SpecSpan,
}

pub struct SpecRequest {
    pub method: SpecSpan,
    pub target: SpecSpan,
    /// `x` in `HTTP/1.x`.
    pub minor: u8,
    pub headers: Seq<SpecHeader>,
}

pub struct SpecResponse {
    pub minor: u8,
    pub status: u16,
    pub reason: SpecSpan,
    pub headers: Seq<SpecHeader>,
}

/// `HTTP-version = HTTP-name "/" DIGIT "." DIGIT` with major version 1.
/// The value is the minor version.
pub open spec fn parse_version(b: Seq<u8>, i: int) -> Parsed<u8> {
    match lit(b, i, http1_prefix()) {
        Parsed::Done(_, j) => if j >= b.len() {
            Parsed::Partial
        } else if !is_digit(b[j]) {
            Parsed::Invalid
        } else {
            Parsed::Done((b[j] - 0x30) as u8, j + 1)
        },
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

/// Empty lines before a request line, which RFC 9112 §2.2 says a server
/// SHOULD ignore. The next position is the start of the request line.
pub open spec fn skip_empty_lines(b: Seq<u8>, i: int) -> Parsed<()>
    decreases b.len() - i,
{
    if i < 0 || i >= b.len() {
        Parsed::Partial
    } else if b[i] != CR {
        Parsed::Done((), i)
    } else if i + 1 >= b.len() {
        Parsed::Partial
    } else if b[i + 1] != LF {
        Parsed::Invalid
    } else {
        skip_empty_lines(b, i + 2)
    }
}

/// `field-line = field-name ":" OWS field-value OWS` followed by CRLF
/// (RFC 9112 §5).
///
/// Strict: whitespace between the name and the colon is rejected (RFC 9112
/// §5.1 requires this of servers), and so is a line that starts with
/// whitespace, which is how obsolete line folding begins (§5.2). A line
/// must end in CRLF: a bare LF or CR is rejected (§2.2 allows accepting a
/// bare LF; the strict reading removes a known source of disagreement
/// between parsers).
pub open spec fn parse_header(b: Seq<u8>, i: int) -> Parsed<SpecHeader> {
    match run_then(b, i, Cls::Token, COLON) {
        Parsed::Done(ne, v0) => {
            let vs = run_end(b, v0, Cls::Ows);
            let e = run_end(b, vs, Cls::Value);
            match lit(b, e, crlf()) {
                Parsed::Done(_, next) => Parsed::Done(
                    SpecHeader {
                        name: SpecSpan { start: i, end: ne },
                        value: SpecSpan { start: vs, end: trim_end(b, vs, e) },
                    },
                    next,
                ),
                Parsed::Partial => Parsed::Partial,
                Parsed::Invalid => Parsed::Invalid,
            }
        },
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

/// `*( field-line CRLF ) CRLF`, with at most `max` field lines. A message
/// with more is rejected: the limit is part of the contract, like the
/// header array size in picohttpparser.
pub open spec fn parse_headers(b: Seq<u8>, i: int, max: nat) -> Parsed<Seq<SpecHeader>>
    decreases b.len() - i,
{
    if i < 0 || i >= b.len() {
        Parsed::Partial
    } else if b[i] == CR {
        match lit(b, i, crlf()) {
            Parsed::Done(_, n) => Parsed::Done(Seq::empty(), n),
            Parsed::Partial => Parsed::Partial,
            Parsed::Invalid => Parsed::Invalid,
        }
    } else if max == 0 {
        Parsed::Invalid
    } else {
        match parse_header(b, i) {
            Parsed::Done(h, n) => if n <= i {
                Parsed::Invalid  // unreachable: a field line is never empty

            } else {
                match parse_headers(b, n, (max - 1) as nat) {
                    Parsed::Done(hs, m) => Parsed::Done(seq![h] + hs, m),
                    Parsed::Partial => Parsed::Partial,
                    Parsed::Invalid => Parsed::Invalid,
                }
            },
            Parsed::Partial => Parsed::Partial,
            Parsed::Invalid => Parsed::Invalid,
        }
    }
}

/// `request-line = method SP request-target SP HTTP-version CRLF`
/// (RFC 9112 §3), then the field lines. The `end` of a `Done` is the length
/// of the head; the body, if any, starts there.
///
/// Strict: exactly one SP between the parts (§3 allows a recipient to
/// accept other whitespace, which is another source of disagreement).
pub open spec fn parse_request(b: Seq<u8>, max: nat) -> Parsed<SpecRequest> {
    match skip_empty_lines(b, 0) {
        Parsed::Done(_, s) => match run_then(b, s, Cls::Token, SP) {
            Parsed::Done(me, t) => match run_then(b, t, Cls::Target, SP) {
                Parsed::Done(te, v) => match parse_version(b, v) {
                    Parsed::Done(minor, h) => match lit(b, h, crlf()) {
                        Parsed::Done(_, h2) => match parse_headers(b, h2, max) {
                            Parsed::Done(hs, end) => Parsed::Done(
                                SpecRequest {
                                    method: SpecSpan { start: s, end: me },
                                    target: SpecSpan { start: t, end: te },
                                    minor,
                                    headers: hs,
                                },
                                end,
                            ),
                            Parsed::Partial => Parsed::Partial,
                            Parsed::Invalid => Parsed::Invalid,
                        },
                        Parsed::Partial => Parsed::Partial,
                        Parsed::Invalid => Parsed::Invalid,
                    },
                    Parsed::Partial => Parsed::Partial,
                    Parsed::Invalid => Parsed::Invalid,
                },
                Parsed::Partial => Parsed::Partial,
                Parsed::Invalid => Parsed::Invalid,
            },
            Parsed::Partial => Parsed::Partial,
            Parsed::Invalid => Parsed::Invalid,
        },
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

/// `status-code = 3DIGIT`
pub open spec fn parse_status(b: Seq<u8>, i: int) -> Parsed<u16> {
    if i + 3 > b.len() {
        if (i < b.len() ==> is_digit(b[i])) && (i + 1 < b.len() ==> is_digit(b[i + 1])) {
            Parsed::Partial
        } else {
            Parsed::Invalid
        }
    } else if is_digit(b[i]) && is_digit(b[i + 1]) && is_digit(b[i + 2]) {
        Parsed::Done(
            ((b[i] - 0x30) * 100 + (b[i + 1] - 0x30) * 10 + (b[i + 2] - 0x30)) as u16,
            i + 3,
        )
    } else {
        Parsed::Invalid
    }
}

/// `status-line = HTTP-version SP status-code SP [ reason-phrase ]` CRLF
/// (RFC 9112 §4), where `reason-phrase = 1*( HTAB / SP / VCHAR / obs-text )`.
///
/// Lenient, as picohttpparser and llhttp are: the SP after the status code
/// may be omitted when the reason phrase is empty (then CRLF must follow
/// the code directly). The reason phrase plays
/// no part in framing.
pub open spec fn parse_status_line(b: Seq<u8>, i: int) -> Parsed<(u8, u16, SpecSpan)> {
    match parse_version(b, i) {
        Parsed::Done(minor, j) => if j >= b.len() {
            Parsed::Partial
        } else if b[j] != SP {
            Parsed::Invalid
        } else {
            match parse_status(b, j + 1) {
                Parsed::Done(code, k) => {
                    let rs = if k < b.len() && b[k] == SP {
                        k + 1
                    } else {
                        k
                    };
                    let re = if rs > k {
                        run_end(b, rs, Cls::Value)
                    } else {
                        k
                    };
                    match lit(b, re, crlf()) {
                        Parsed::Done(_, n) => Parsed::Done(
                            (minor, code, SpecSpan { start: rs, end: re }),
                            n,
                        ),
                        Parsed::Partial => Parsed::Partial,
                        Parsed::Invalid => Parsed::Invalid,
                    }
                },
                Parsed::Partial => Parsed::Partial,
                Parsed::Invalid => Parsed::Invalid,
            }
        },
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

pub open spec fn parse_response(b: Seq<u8>, max: nat) -> Parsed<SpecResponse> {
    match parse_status_line(b, 0) {
        Parsed::Done((minor, status, reason), h) => match parse_headers(b, h, max) {
            Parsed::Done(hs, end) => Parsed::Done(
                SpecResponse { minor, status, reason, headers: hs },
                end,
            ),
            Parsed::Partial => Parsed::Partial,
            Parsed::Invalid => Parsed::Invalid,
        },
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

// ---------------------------------------------------------------------------
// Framing (RFC 9112 §6)
// ---------------------------------------------------------------------------

/// How the body of a message is delimited.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Body {
    /// No body.
    Empty,
    /// Exactly this many bytes.
    Length(u64),
    /// The chunked transfer coding (RFC 9112 §7.1).
    Chunked,
    /// Everything until the connection closes (responses only).
    Close,
}

/// ASCII lowercase.
pub open spec fn lower(c: u8) -> u8 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u8
    } else {
        c
    }
}

/// Case-insensitive equality with `lit`, which is given in lowercase.
pub open spec fn ci_eq(s: Seq<u8>, lit: Seq<u8>) -> bool {
    s.len() == lit.len() && forall|i: int| 0 <= i < s.len() ==> lower(#[trigger] s[i]) == lit[i]
}

/// "content-length"
pub open spec fn name_content_length() -> Seq<u8> {
    seq![
        0x63u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68,
    ]
}

/// "transfer-encoding"
pub open spec fn name_transfer_encoding() -> Seq<u8> {
    seq![
        0x74u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69,
        0x6e, 0x67,
    ]
}

/// "host"
pub open spec fn name_host() -> Seq<u8> {
    seq![0x68u8, 0x6f, 0x73, 0x74]
}

/// "chunked"
pub open spec fn coding_chunked() -> Seq<u8> {
    seq![0x63u8, 0x68, 0x75, 0x6e, 0x6b, 0x65, 0x64]
}

/// The decimal value of the digits `s`.
pub open spec fn decimal(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        decimal(s.drop_last()) * 10 + (s.last() - 0x30) as nat
    }
}

/// Most digits accepted in a Content-Length: 19 digits always fit a `u64`.
pub spec const MAX_CL_DIGITS: nat = 19;

/// `Content-Length = 1*DIGIT` (RFC 9110 §8.6).
///
/// Strict: a list of values (`5, 5`) is rejected, as is anything but
/// digits, and more than 19 digits.
pub open spec fn content_length_value(v: Seq<u8>) -> Option<u64> {
    if 1 <= v.len() <= MAX_CL_DIGITS && forall|i: int| 0 <= i < v.len() ==> is_digit(#[trigger] v[i]) {
        Some(decimal(v) as u64)
    } else {
        None
    }
}

/// What the Transfer-Encoding lines seen so far say.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TeState {
    /// A Transfer-Encoding line has been seen.
    pub present: bool,
    /// The last coding listed so far is `chunked`.
    pub chunked_last: bool,
}

/// Adds one coding to the list. Strict: nothing may follow `chunked`
/// (RFC 9112 §6.1 forbids applying it twice, and requires it to be final
/// in a request; in a response a coding after `chunked` is legal but never
/// sent in practice, and rejecting it removes a framing ambiguity).
pub open spec fn te_add(st: TeState, coding: Seq<u8>) -> Option<TeState> {
    if st.chunked_last {
        None
    } else {
        Some(TeState { present: true, chunked_last: ci_eq(coding, coding_chunked()) })
    }
}

/// The comma-separated list of transfer codings `v[i..]` (RFC 9110 §5.6.1:
/// empty elements are allowed and ignored).
///
/// Strict: an element must be a bare token. Transfer parameters (`;q=...`)
/// are rejected: no coding this crate handles takes any.
pub open spec fn te_list(v: Seq<u8>, i: int, st: TeState) -> Option<TeState>
    decreases v.len() - i,
{
    let a = run_end(v, i, Cls::Ows);
    if i < 0 || a >= v.len() {
        Some(st)
    } else if a < i {
        None  // unreachable: a run never ends before it starts

    } else if v[a] == COMMA {
        te_list(v, a + 1, st)
    } else {
        let e = run_end(v, a, Cls::Token);
        if e == a {
            None
        } else {
            match te_add(st, v.subrange(a, e)) {
                None => None,
                Some(st2) => {
                    let f = run_end(v, e, Cls::Ows);
                    if f >= v.len() {
                        Some(st2)
                    } else if f < i {
                        None  // unreachable
                    } else if v[f] == COMMA {
                        te_list(v, f + 1, st2)
                    } else {
                        None
                    }
                },
            }
        }
    }
}

/// What the framing-relevant field lines say, folded over the headers.
pub struct Fields {
    /// The Content-Length value, if a Content-Length line was seen.
    pub cl: Option<u64>,
    pub te: TeState,
    /// Number of Host lines.
    pub hosts: nat,
}

pub open spec fn fields_init() -> Fields {
    Fields { cl: None, te: TeState { present: false, chunked_last: false }, hosts: 0 }
}

pub open spec fn span_bytes(b: Seq<u8>, s: SpecSpan) -> Seq<u8> {
    b.subrange(s.start, s.end)
}

/// Case-insensitive equality with `lit`, where `_` in `s` also matches `-`
/// in `lit`: how CGI-style software (which maps both to `_`) and some
/// parsers compare field names.
pub open spec fn ci_eq_dash(s: Seq<u8>, lit: Seq<u8>) -> bool {
    s.len() == lit.len() && forall|i: int|
        0 <= i < s.len() ==> lower(#[trigger] s[i]) == lit[i] || (s[i] == 0x5F && lit[i] == 0x2D)
}

/// Folds one field line into `f`.
///
/// Strict, beyond RFC 9112, so that recipients that deviate from it in
/// ways seen in deployed parsers still agree (see `unique.rs`):
/// - a repeated Content-Length line must carry the same number, as RFC
///   9112 §6.3 allows (every recipient then reads that number);
/// - a second Transfer-Encoding line is rejected (some parsers read only
///   the first or only the last);
/// - a name that matches Content-Length or Transfer-Encoding once `_` is
///   read as `-` (`Content_Length`) is rejected.
pub open spec fn fields_step(b: Seq<u8>, f: Fields, h: SpecHeader) -> Option<Fields> {
    let name = span_bytes(b, h.name);
    let value = span_bytes(b, h.value);
    if ci_eq(name, name_content_length()) {
        match content_length_value(value) {
            Some(n) => if f.cl is None || f.cl == Some(n) {
                Some(Fields { cl: Some(n), ..f })
            } else {
                None
            },
            None => None,
        }
    } else if ci_eq(name, name_transfer_encoding()) {
        if f.te.present {
            None
        } else {
            match te_list(value, 0, TeState { present: true, chunked_last: false }) {
                Some(te) => Some(Fields { te, ..f }),
                None => None,
            }
        }
    } else if ci_eq_dash(name, name_content_length()) || ci_eq_dash(name, name_transfer_encoding()) {
        None
    } else if ci_eq(name, name_host()) {
        Some(Fields { hosts: f.hosts + 1, ..f })
    } else {
        Some(f)
    }
}

/// `fields_step` folded over `hs`, left to right.
pub open spec fn fields_of(b: Seq<u8>, hs: Seq<SpecHeader>) -> Option<Fields>
    decreases hs.len(),
{
    if hs.len() == 0 {
        Some(fields_init())
    } else {
        match fields_of(b, hs.drop_last()) {
            Some(f) => fields_step(b, f, hs.last()),
            None => None,
        }
    }
}

/// The body framing of a request (RFC 9112 §6.3), or `None` if the request
/// must be rejected. These are the rules that rule out request smuggling:
///
/// - Transfer-Encoding and Content-Length together are rejected (§6.1 lets
///   a server reject them, and an intermediary that forwarded such a
///   message is how CL.TE and TE.CL smuggling works).
/// - With Transfer-Encoding, `chunked` must be the final coding (§6.3
///   rule 4), and Transfer-Encoding in an HTTP/1.0 request is rejected
///   (§6.1: such framing is faulty).
/// - Content-Length must be a single valid value (§6.3 rule 5).
/// - Host must appear exactly once in HTTP/1.1, and at most once in
///   HTTP/1.0 (RFC 9112 §3.2).
pub open spec fn request_body(b: Seq<u8>, r: SpecRequest) -> Option<Body> {
    match fields_of(b, r.headers) {
        None => None,
        Some(f) => if f.hosts > 1 || (r.minor >= 1 && f.hosts == 0) {
            None
        } else {
            request_framing(f, r.minor)
        },
    }
}

/// The Content-Length and Transfer-Encoding part of `request_body`, without
/// the Host rule.
pub open spec fn request_framing(f: Fields, minor: u8) -> Option<Body> {
    if f.te.present {
        if minor == 0 || f.cl is Some || !f.te.chunked_last {
            None
        } else {
            Some(Body::Chunked)
        }
    } else {
        match f.cl {
            Some(n) => Some(Body::Length(n)),
            None => Some(Body::Empty),
        }
    }
}

/// The body framing of a response (RFC 9112 §6.3), given whether the
/// request was HEAD and whether it was CONNECT, or `None` if the response
/// must be rejected. The conflict checks are the same as for requests, and
/// apply even when the status means there is no body.
pub open spec fn response_body(b: Seq<u8>, r: SpecResponse, head: bool, connect: bool) -> Option<
    Body,
> {
    match fields_of(b, r.headers) {
        None => None,
        Some(f) => response_framing(f, r.minor, r.status, head, connect),
    }
}

/// The Content-Length and Transfer-Encoding part of `response_body`.
pub open spec fn response_framing(f: Fields, minor: u8, status: u16, head: bool, connect: bool) -> Option<
    Body,
> {
    if f.te.present && (f.cl is Some || minor == 0) {
        None
    } else if head || (100 <= status <= 199) || status == 204 || status == 304 || (connect && 200
        <= status <= 299) {
        Some(Body::Empty)
    } else if f.te.present {
        if f.te.chunked_last {
            Some(Body::Chunked)
        } else {
            Some(Body::Close)
        }
    } else {
        match f.cl {
            Some(n) => Some(Body::Length(n)),
            None => Some(Body::Close),
        }
    }
}

} // verus!
