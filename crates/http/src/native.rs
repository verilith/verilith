//! The native C API (`include/vhttp.h`), behind the `capi` feature.
//!
//! The Rust API of `api.rs` with C types. Unlike the picohttpparser shape
//! (`capi.rs`), it reports how the body is framed, which is the decision
//! the smuggling proofs are about, and why a message was rejected.
//!
//! This layer is NOT verified. It is kept mechanical: pointer checks, a
//! call to the function of the same name in `api.rs`, and the copying of
//! the result into C structs. All parsing happens in the verified code.
#![allow(non_camel_case_types)]
#![allow(clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn)]

use crate::api::{self, Chunked, ChunkedDecoder, Error, Status};
use crate::capi::{pack, unpack};
use crate::parse::Header;
use crate::spec::Body;
use std::cell::RefCell;
use std::os::raw::{c_char, c_int};

pub const VHTTP_OK: c_int = 0;
pub const VHTTP_PARTIAL: c_int = 1;
pub const VHTTP_E_ARGUMENT: c_int = -100;

/// Bytes `start..end` of the buffer that was parsed.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct vhttp_span {
    pub start: usize,
    pub end: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct vhttp_header {
    pub name: vhttp_span,
    /// Without leading and trailing whitespace.
    pub value: vhttp_span,
}

#[repr(C)]
pub struct vhttp_request {
    pub method: vhttp_span,
    pub target: vhttp_span,
    /// Length of the head; the body starts here.
    pub head_len: usize,
    /// For `VHTTP_BODY_LENGTH`.
    pub content_length: u64,
    /// `VHTTP_BODY_*`.
    pub body: c_int,
    pub minor_version: u8,
}

#[repr(C)]
pub struct vhttp_response {
    pub reason: vhttp_span,
    pub head_len: usize,
    pub content_length: u64,
    pub body: c_int,
    pub status: u16,
    pub minor_version: u8,
}

thread_local! {
    static HEADERS: RefCell<Vec<Header>> = const { RefCell::new(Vec::new()) };
}

fn error_code(e: Error) -> c_int {
    match e {
        Error::Method => -1,
        Error::Target => -2,
        Error::Version => -3,
        Error::Status => -4,
        Error::NewLine => -5,
        Error::HeaderName => -6,
        Error::HeaderValue => -7,
        Error::TooManyHeaders => -8,
        Error::ContentLength => -9,
        Error::TransferEncoding => -10,
        Error::ContentLengthAndTransferEncoding => -11,
        Error::TransferEncodingHttp10 => -12,
        Error::Host => -13,
        Error::Chunked => -14,
    }
}

fn body(b: Body) -> (c_int, u64) {
    match b {
        Body::Empty => (0, 0),
        Body::Length(n) => (1, n),
        Body::Chunked => (2, 0),
        Body::Close => (3, 0),
    }
}

/// Where `part`, a subslice of `buf`, lies in it.
fn span(buf: &[u8], part: &[u8]) -> vhttp_span {
    let start = part.as_ptr() as usize - buf.as_ptr() as usize;
    vhttp_span { start, end: start + part.len() }
}

unsafe fn slice<'a>(buf: *const c_char, len: usize) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        std::slice::from_raw_parts(buf as *const u8, len)
    }
}

/// Copies `hs` out. The caller checked that `out` has room.
unsafe fn export(hs: &[Header], out: *mut vhttp_header, num: *mut usize) {
    for (i, h) in hs.iter().enumerate() {
        out.add(i).write(vhttp_header {
            name: vhttp_span { start: h.name.start, end: h.name.end },
            value: vhttp_span { start: h.value.start, end: h.value.end },
        });
    }
    *num = hs.len();
}

/// Parses a request head at the start of `buf`. Returns `VHTTP_OK`,
/// `VHTTP_PARTIAL` or a negative `VHTTP_E_*`.
///
/// # Safety
/// `buf` points to `len` readable bytes, `num_headers` is valid and
/// `headers` has room for `*num_headers` entries, and `out` is null or
/// valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vhttp_parse_request(
    buf: *const c_char,
    len: usize,
    last_len: usize,
    headers: *mut vhttp_header,
    num_headers: *mut usize,
    out: *mut vhttp_request,
) -> c_int {
    if (buf.is_null() && len != 0) || num_headers.is_null() || (headers.is_null() && *num_headers != 0) {
        return VHTTP_E_ARGUMENT;
    }
    let b = slice(buf, len);
    let max = *num_headers;
    *num_headers = 0;
    // A `last_len` that is not a shorter length of this buffer is ignored.
    let last_len = if last_len < len { last_len } else { 0 };
    HEADERS.with(|cell| {
        let hs = &mut *cell.borrow_mut();
        match api::parse_request_with(b, last_len, max, hs) {
            Ok(Status::Complete(r)) => {
                export(hs, headers, num_headers);
                if !out.is_null() {
                    let (kind, n) = body(r.body);
                    out.write(vhttp_request {
                        method: span(b, r.method()),
                        target: span(b, r.target()),
                        head_len: r.head_len,
                        content_length: n,
                        body: kind,
                        minor_version: r.minor_version(),
                    });
                }
                VHTTP_OK
            }
            Ok(Status::Partial) => VHTTP_PARTIAL,
            Err(e) => error_code(e),
        }
    })
}

/// Parses a response head at the start of `buf`. `head_request` and
/// `connect_request` say whether the request it answers was HEAD or
/// CONNECT, which changes the framing.
///
/// # Safety
/// As for `vhttp_parse_request`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vhttp_parse_response(
    buf: *const c_char,
    len: usize,
    head_request: bool,
    connect_request: bool,
    headers: *mut vhttp_header,
    num_headers: *mut usize,
    out: *mut vhttp_response,
) -> c_int {
    if (buf.is_null() && len != 0) || num_headers.is_null() || (headers.is_null() && *num_headers != 0) {
        return VHTTP_E_ARGUMENT;
    }
    let b = slice(buf, len);
    let max = *num_headers;
    *num_headers = 0;
    HEADERS.with(|cell| {
        let hs = &mut *cell.borrow_mut();
        match api::parse_response(b, head_request, connect_request, hs) {
            // The Rust API allows `DEFAULT_MAX_HEADERS` field lines; the
            // caller's array may hold fewer.
            Ok(Status::Complete(_)) if hs.len() > max => error_code(Error::TooManyHeaders),
            Ok(Status::Complete(r)) => {
                export(hs, headers, num_headers);
                if !out.is_null() {
                    let (kind, n) = body(r.body);
                    out.write(vhttp_response {
                        reason: span(b, r.reason()),
                        head_len: r.head_len,
                        content_length: n,
                        body: kind,
                        status: r.status(),
                        minor_version: r.minor_version(),
                    });
                }
                VHTTP_OK
            }
            Ok(Status::Partial) => VHTTP_PARTIAL,
            Err(e) => error_code(e),
        }
    })
}

/// A static, NUL-terminated description of a result code.
#[unsafe(no_mangle)]
pub extern "C" fn vhttp_error_message(code: c_int) -> *const c_char {
    let s: &'static [u8] = match code {
        0 => b"no error\0",
        1 => b"incomplete\0",
        -1 => b"invalid method\0",
        -2 => b"invalid request target\0",
        -3 => b"invalid HTTP version\0",
        -4 => b"invalid status line\0",
        -5 => b"line not ended by CRLF\0",
        -6 => b"invalid field name\0",
        -7 => b"invalid field value\0",
        -8 => b"too many field lines\0",
        -9 => b"invalid or repeated Content-Length\0",
        -10 => b"invalid Transfer-Encoding\0",
        -11 => b"both Content-Length and Transfer-Encoding\0",
        -12 => b"Transfer-Encoding in HTTP/1.0\0",
        -13 => b"missing or repeated Host\0",
        -14 => b"invalid chunked body\0",
        _ => b"invalid argument\0",
    };
    s.as_ptr() as *const c_char
}

/// Whether a code is one of the framing errors: the head is well formed
/// but its framing is ambiguous (the request smuggling shapes).
#[unsafe(no_mangle)]
pub extern "C" fn vhttp_error_is_framing(code: c_int) -> bool {
    (-13..=-9).contains(&code)
}

/// The state of a chunked decoder. All zeros is a new decoder that
/// consumes the trailer section.
#[repr(C)]
pub struct vhttp_chunked {
    /// Private: the decoder's position, as `capi::pack` encodes it.
    n: usize,
    state: u8,
    /// Set before the first call to stop at the trailer section, leaving
    /// it (and the final CRLF) for the caller.
    pub keep_trailers: bool,
}

/// Decodes `len` bytes of chunked body in place. On `VHTTP_PARTIAL` all
/// input was consumed and `*out_len` body bytes are at the front of `buf`.
/// On `VHTTP_OK` the body ended: `*out_len` body bytes are at the front,
/// followed by the `*rest` bytes that came after the body.
///
/// # Safety
/// `d` is a valid decoder, `buf` points to `len` writable bytes, and
/// `out_len` and `rest` are null or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vhttp_chunked_decode(
    d: *mut vhttp_chunked,
    buf: *mut c_char,
    len: usize,
    out_len: *mut usize,
    rest: *mut usize,
) -> c_int {
    if d.is_null() || (buf.is_null() && len != 0) {
        return VHTTP_E_ARGUMENT;
    }
    let d = &mut *d;
    let Some(state) = unpack(d.state as c_char, d.n) else { return VHTTP_E_ARGUMENT };
    let b: &mut [u8] = if len == 0 { &mut [] } else { std::slice::from_raw_parts_mut(buf as *mut u8, len) };
    let mut dec = ChunkedDecoder::from_state(state, d.keep_trailers);
    let r = dec.decode(b);
    let (tag, n) = pack(dec.state());
    d.state = tag as u8;
    d.n = n;
    let (code, out, after) = match r {
        Err(e) => return error_code(e),
        Ok(Chunked::More { out }) => (VHTTP_PARTIAL, out, 0),
        Ok(Chunked::Done { out, rest }) => (VHTTP_OK, out, rest),
    };
    if !out_len.is_null() {
        *out_len = out;
    }
    if !rest.is_null() {
        *rest = after;
    }
    code
}

/// Whether the decoder is inside chunk data.
///
/// # Safety
/// `d` is null or a valid decoder.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vhttp_chunked_in_data(d: *const vhttp_chunked) -> bool {
    !d.is_null() && unpack((*d).state as c_char, (*d).n).is_some_and(|s| ChunkedDecoder::from_state(s, false).in_data())
}
