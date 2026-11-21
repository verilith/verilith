//! Error reasons. Not verified, and not trusted: these functions run only
//! after the verified parser has rejected a message, to say why. They
//! cannot turn a rejection into an acceptance or change a parse; at worst
//! they would name the wrong reason. They walk the same grammar as
//! `spec.rs`, reading with `get`, so they never panic.
use crate::api::Error;
use crate::framing::{content_length_exec, te_list_exec};
use crate::parse::Header;
use crate::spec::TeState;

fn tchar(c: u8) -> bool {
    matches!(c, b'!' | b'#' | b'$' | b'%' | b'&' | b'\'' | b'*' | b'+' | b'-' | b'.' | b'^' | b'_' | b'`' | b'|' | b'~')
        || c.is_ascii_alphanumeric()
}

fn target_char(c: u8) -> bool {
    (0x21..=0x7E).contains(&c) || c >= 0x80
}

fn value_char(c: u8) -> bool {
    c == b'\t' || (c >= 0x20 && c != 0x7F)
}

fn run(b: &[u8], mut i: usize, f: fn(u8) -> bool) -> usize {
    while b.get(i).is_some_and(|&c| f(c)) {
        i += 1;
    }
    i
}

/// `NewLine` if a line break at `i` is malformed (a bare CR or LF), else
/// `other`.
fn line_end(b: &[u8], i: usize, other: Error) -> Error {
    match b.get(i) {
        Some(b'\n') => Error::NewLine,
        Some(b'\r') if b.get(i + 1).is_some_and(|&c| c != b'\n') => Error::NewLine,
        _ => other,
    }
}

fn crlf(b: &[u8], i: usize) -> bool {
    b.get(i) == Some(&b'\r') && b.get(i + 1) == Some(&b'\n')
}

/// Why `parse_headers` rejects `b` from `i`.
pub(crate) fn headers(b: &[u8], mut i: usize, max: usize) -> Error {
    let mut n = 0;
    loop {
        match b.get(i) {
            Some(b'\r') | Some(b'\n') => return line_end(b, i, Error::NewLine),
            None => return Error::NewLine,
            _ => {}
        }
        if n == max {
            return Error::TooManyHeaders;
        }
        let ne = run(b, i, tchar);
        if ne == i || b.get(ne) != Some(&b':') {
            // Includes a line that starts with whitespace (obsolete line
            // folding) and whitespace before the colon.
            return Error::HeaderName;
        }
        let vs = run(b, ne + 1, |c| c == b' ' || c == b'\t');
        let e = run(b, vs, value_char);
        if !crlf(b, e) {
            return line_end(b, e, Error::HeaderValue);
        }
        i = e + 2;
        n += 1;
    }
}

fn version(b: &[u8], i: usize) -> Option<usize> {
    let v = b.get(i..i + 8)?;
    (v.starts_with(b"HTTP/1.") && v[7].is_ascii_digit()).then_some(i + 8)
}

/// Where the request line starts, after empty lines.
pub(crate) fn request_start(b: &[u8]) -> usize {
    let mut i = 0;
    while crlf(b, i) {
        i += 2;
    }
    i
}

/// Why `parse_request` rejects `b`.
pub(crate) fn request(b: &[u8], max: usize) -> Error {
    let s = request_start(b);
    if b.get(s) == Some(&b'\r') || b.get(s) == Some(&b'\n') {
        return Error::NewLine;
    }
    let me = run(b, s, tchar);
    if me == s || b.get(me) != Some(&b' ') {
        return Error::Method;
    }
    let te = run(b, me + 1, target_char);
    if te == me + 1 || b.get(te) != Some(&b' ') {
        return Error::Target;
    }
    let Some(h) = version(b, te + 1) else {
        return Error::Version;
    };
    if !crlf(b, h) {
        return line_end(b, h, Error::Version);
    }
    headers(b, h + 2, max)
}

/// Why `parse_response` rejects `b`.
pub(crate) fn response(b: &[u8], max: usize) -> Error {
    let Some(j) = version(b, 0) else {
        return Error::Version;
    };
    if b.get(j) != Some(&b' ') || !b.get(j + 1..j + 4).is_some_and(|d| d.iter().all(u8::is_ascii_digit)) {
        return Error::Status;
    }
    let k = j + 4;
    let re = if b.get(k) == Some(&b' ') { run(b, k + 1, value_char) } else { k };
    if !crlf(b, re) {
        return line_end(b, re, Error::Status);
    }
    headers(b, re + 2, max)
}

/// Why the framing rules reject a well-formed head (spec `fields_of`,
/// then `request_body` or `response_body`, in the same order).
pub(crate) fn framing(b: &[u8], hs: &[Header], minor: u8, request: bool, check_host: bool) -> Error {
    let (mut cl, mut te, mut hosts) = (None, TeState { present: false, chunked_last: false }, 0);
    for h in hs {
        let name = &b[h.name.start..h.name.end];
        let value = &b[h.value.start..h.value.end];
        if name.eq_ignore_ascii_case(b"content-length") {
            match (cl, content_length_exec(value)) {
                (_, None) => return Error::ContentLength,
                (Some(m), Some(n)) if m != n => return Error::ContentLength,
                (_, n) => cl = n,
            }
        } else if name.eq_ignore_ascii_case(b"transfer-encoding") {
            if te.present {
                return Error::TransferEncoding;
            }
            match te_list_exec(value, TeState { present: true, chunked_last: false }) {
                Some(t) => te = t,
                None => return Error::TransferEncoding,
            }
        } else if dash_eq(name, b"content-length") {
            return Error::ContentLength;
        } else if dash_eq(name, b"transfer-encoding") {
            return Error::TransferEncoding;
        } else if name.eq_ignore_ascii_case(b"host") {
            hosts += 1;
        }
    }
    if check_host && (hosts > 1 || (minor >= 1 && hosts == 0)) {
        return Error::Host;
    }
    if te.present && minor == 0 {
        return Error::TransferEncodingHttp10;
    }
    if te.present && cl.is_some() {
        return Error::ContentLengthAndTransferEncoding;
    }
    if request && te.present && !te.chunked_last {
        return Error::TransferEncoding;
    }
    // Unreachable if the verified framing rejected the head.
    Error::TransferEncoding
}

fn dash_eq(name: &[u8], lit: &[u8]) -> bool {
    name.len() == lit.len() && name.iter().zip(lit).all(|(&c, &l)| c.to_ascii_lowercase() == l || (c == b'_' && l == b'-'))
}
