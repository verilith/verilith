//! C API compatible with picohttpparser (`include/picohttpparser.h`).
//!
//! A thin adapter, not verified: pointer checks, the conversion of results
//! to picohttpparser's return codes, and the packing of the chunked decoder
//! state into `struct phr_chunked_decoder`. All parsing happens in the
//! verified code. With the `phr-abi` feature the functions are exported
//! under picohttpparser's own symbol names; otherwise they are prefixed
//! with `vhttp_`.
//!
//! Differences from picohttpparser, all deliberate (see README):
//! - stricter grammar: lines must end in CRLF, no whitespace before a
//!   colon, no obsolete line folding, exactly one SP in the request line;
//! - requests and responses whose framing is ambiguous (the request
//!   smuggling shapes) are rejected with -1, as is a request with a
//!   missing or repeated Host.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::chunked::CState;
use crate::framing::{request_body_exec, request_body_fx, response_body_exec, response_body_fx};
use crate::parse::{headers_at, request_at, request_fx, request_resume, response_at, response_fx, Header, Out};
use crate::api::ChunkedDecoder;
use std::cell::RefCell;
use std::os::raw::{c_char, c_int};

#[repr(C)]
pub struct phr_header {
    pub name: *const c_char,
    pub name_len: usize,
    pub value: *const c_char,
    pub value_len: usize,
}

#[repr(C)]
pub struct phr_chunked_decoder {
    pub bytes_left_in_chunk: usize,
    pub consume_trailer: c_char,
    pub _hex_count: c_char,
    pub _state: c_char,
    pub _total_read: u64,
    pub _total_overhead: u64,
}

thread_local! {
    static HEADERS: RefCell<Vec<Header>> = const { RefCell::new(Vec::new()) };
}

unsafe fn slice<'a>(buf: *const c_char, len: usize) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        std::slice::from_raw_parts(buf as *const u8, len)
    }
}

/// Copies `hs` out as `phr_header`s.
unsafe fn export_headers(buf: *const c_char, hs: &[Header], out: *mut phr_header, num: *mut usize) {
    for (i, h) in hs.iter().enumerate() {
        let o = &mut *out.add(i);
        o.name = buf.add(h.name.start);
        o.name_len = h.name.end - h.name.start;
        o.value = buf.add(h.value.start);
        o.value_len = h.value.end - h.value.start;
    }
    *num = hs.len();
}

/// Drop-in for `phr_parse_request`.
///
/// # Safety
/// As for picohttpparser: `buf` must point to `len` readable bytes, the out
/// pointers must be valid for writes, and `headers` must have room for
/// `*num_headers` entries.
#[cfg_attr(feature = "phr-abi", unsafe(export_name = "phr_parse_request"))]
#[cfg_attr(not(feature = "phr-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vhttp_phr_parse_request(
    buf: *const c_char,
    len: usize,
    method: *mut *const c_char,
    method_len: *mut usize,
    path: *mut *const c_char,
    path_len: *mut usize,
    minor_version: *mut c_int,
    headers: *mut phr_header,
    num_headers: *mut usize,
    last_len: usize,
) -> c_int {
    let b = slice(buf, len);
    let max = *num_headers;
    *num_headers = 0;
    HEADERS.with(|cell| {
        let hs = &mut *cell.borrow_mut();
        // One pass: the framing fields are gathered while the headers are
        // parsed, as `api::parse_request` does.
        let mut fx = None;
        let fresh = last_len == 0;
        let (r, _) = if fresh {
            request_fx(b, max, hs, true, &mut fx)
        } else {
            request_resume(b, last_len, max, hs)
        };
        match r {
            Out::Done(line, end) => {
                let body = if fresh { request_body_fx(b, line, hs, fx) } else { request_body_exec(b, line, hs) };
                if body.is_none() || end > c_int::MAX as usize {
                    return -1;
                }
                *method = buf.add(line.method.start);
                *method_len = line.method.end - line.method.start;
                *path = buf.add(line.target.start);
                *path_len = line.target.end - line.target.start;
                *minor_version = line.minor as c_int;
                export_headers(buf, hs, headers, num_headers);
                end as c_int
            }
            Out::Partial => -2,
            Out::Invalid => -1,
        }
    })
}

/// Drop-in for `phr_parse_response`. The framing conflict checks are
/// applied as for a response to a GET.
///
/// # Safety
/// As for `vhttp_phr_parse_request`.
#[cfg_attr(feature = "phr-abi", unsafe(export_name = "phr_parse_response"))]
#[cfg_attr(not(feature = "phr-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vhttp_phr_parse_response(
    buf: *const c_char,
    len: usize,
    minor_version: *mut c_int,
    status: *mut c_int,
    msg: *mut *const c_char,
    msg_len: *mut usize,
    headers: *mut phr_header,
    num_headers: *mut usize,
    _last_len: usize,
) -> c_int {
    let b = slice(buf, len);
    let max = *num_headers;
    *num_headers = 0;
    HEADERS.with(|cell| {
        let hs = &mut *cell.borrow_mut();
        let mut fx = None;
        let (r, _) = response_fx(b, max, hs, true, &mut fx);
        match r {
            Out::Done(line, end) => {
                if response_body_fx(b, line, hs, fx, false, false).is_none() || end > c_int::MAX as usize
                {
                    return -1;
                }
                // picohttpparser rejects a status code outside 100..=599.
                if !(100..=599).contains(&line.status) {
                    return -1;
                }
                *minor_version = line.minor as c_int;
                *status = line.status as c_int;
                *msg = buf.add(line.reason.start);
                *msg_len = line.reason.end - line.reason.start;
                export_headers(buf, hs, headers, num_headers);
                end as c_int
            }
            Out::Partial => -2,
            Out::Invalid => -1,
        }
    })
}

/// Drop-in for `phr_parse_headers`.
///
/// # Safety
/// As for `vhttp_phr_parse_request`.
#[cfg_attr(feature = "phr-abi", unsafe(export_name = "phr_parse_headers"))]
#[cfg_attr(not(feature = "phr-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vhttp_phr_parse_headers(
    buf: *const c_char,
    len: usize,
    headers: *mut phr_header,
    num_headers: *mut usize,
    _last_len: usize,
) -> c_int {
    let b = slice(buf, len);
    let max = *num_headers;
    *num_headers = 0;
    HEADERS.with(|cell| {
        let hs = &mut *cell.borrow_mut();
        hs.clear();
        match headers_at(b, 0, max, hs).0 {
            Out::Done(_, end) if end <= c_int::MAX as usize => {
                export_headers(buf, hs, headers, num_headers);
                end as c_int
            }
            Out::Partial => -2,
            _ => -1,
        }
    })
}

pub(crate) fn pack(s: CState) -> (c_char, usize) {
    match s {
        CState::SizeStart => (0, 0),
        CState::Size { n } => (1, n as usize),
        CState::SizeWs { n } => (2, n as usize),
        CState::ExtPreName { n } => (3, n as usize),
        CState::ExtName { n } => (4, n as usize),
        CState::ExtNameWs { n } => (5, n as usize),
        CState::ExtPreVal { n } => (6, n as usize),
        CState::ExtTok { n } => (7, n as usize),
        CState::ExtQ { n } => (8, n as usize),
        CState::ExtQEsc { n } => (9, n as usize),
        CState::ExtValEnd { n } => (10, n as usize),
        CState::ExtValWs { n } => (11, n as usize),
        CState::SizeLf { n } => (12, n as usize),
        CState::Data { left } => (13, left as usize),
        CState::DataCr => (14, 0),
        CState::DataLf => (15, 0),
        CState::TrStart => (16, 0),
        CState::TrName => (17, 0),
        CState::TrValue => (18, 0),
        CState::TrLf => (19, 0),
        CState::EndLf => (20, 0),
        CState::Done => (21, 0),
    }
}

pub(crate) fn unpack(tag: c_char, n: usize) -> Option<CState> {
    let n = n as u64;
    Some(match tag {
        0 => CState::SizeStart,
        1 => CState::Size { n },
        2 => CState::SizeWs { n },
        3 => CState::ExtPreName { n },
        4 => CState::ExtName { n },
        5 => CState::ExtNameWs { n },
        6 => CState::ExtPreVal { n },
        7 => CState::ExtTok { n },
        8 => CState::ExtQ { n },
        9 => CState::ExtQEsc { n },
        10 => CState::ExtValEnd { n },
        11 => CState::ExtValWs { n },
        12 => CState::SizeLf { n },
        13 => CState::Data { left: n },
        14 => CState::DataCr,
        15 => CState::DataLf,
        16 => CState::TrStart,
        17 => CState::TrName,
        18 => CState::TrValue,
        19 => CState::TrLf,
        20 => CState::EndLf,
        21 => CState::Done,
        _ => return None,
    })
}

/// Drop-in for `phr_decode_chunked`, including its overhead limit (an
/// error once chunk framing exceeds 100 KB and 80% of what was read).
///
/// # Safety
/// `decoder` must be valid (zero-filled before the first call), and `buf`
/// must point to `*bufsz` writable bytes.
#[cfg_attr(feature = "phr-abi", unsafe(export_name = "phr_decode_chunked"))]
#[cfg_attr(not(feature = "phr-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vhttp_phr_decode_chunked(
    decoder: *mut phr_chunked_decoder,
    buf: *mut c_char,
    bufsz: *mut usize,
) -> isize {
    let d = &mut *decoder;
    let len = *bufsz;
    let state = match unpack(d._state, d.bytes_left_in_chunk) {
        Some(s) => s,
        None => return -1,
    };
    // In picohttpparser a decoder that has finished starts over.
    let state = if let CState::Done = state { CState::SizeStart } else { state };
    let keep_trailers = d.consume_trailer == 0;
    let state = if keep_trailers && matches!(state, CState::TrStart) { CState::SizeStart } else { state };
    d._total_read += len as u64;
    let b: &mut [u8] = if len == 0 { &mut [] } else { std::slice::from_raw_parts_mut(buf as *mut u8, len) };
    let mut dec = ChunkedDecoder::from_state(state, keep_trailers);
    let r = dec.decode(b);
    let (tag, n) = pack(dec.state());
    d._state = tag;
    d.bytes_left_in_chunk = n;
    match r {
        Err(_) => -1,
        Ok(crate::api::Chunked::Done { out, rest }) => {
            *bufsz = out;
            rest as isize
        }
        Ok(crate::api::Chunked::More { out }) => {
            *bufsz = out;
            d._total_overhead += (len - out) as u64;
            if d._total_overhead >= 102400 && d._total_read - d._total_overhead < d._total_read / 4 {
                -1
            } else {
                -2
            }
        }
    }
}

/// Drop-in for `phr_decode_chunked_is_in_data`.
///
/// # Safety
/// `decoder` must be valid.
#[cfg_attr(feature = "phr-abi", unsafe(export_name = "phr_decode_chunked_is_in_data"))]
#[cfg_attr(not(feature = "phr-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vhttp_phr_decode_chunked_is_in_data(decoder: *mut phr_chunked_decoder) -> c_int {
    ((*decoder)._state == 13) as c_int
}
