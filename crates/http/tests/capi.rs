//! The native C API (`src/native.rs`) against the Rust API it wraps: the
//! same verdict, spans, framing and error for every input.
#![cfg(feature = "capi")]
use std::os::raw::c_char;
use verilith_http::native::*;
use verilith_http::{Body, Chunked, ChunkedDecoder, Header, Status};

const CAP: usize = 8;

fn body(b: Body) -> (i32, u64) {
    match b {
        Body::Empty => (0, 0),
        Body::Length(n) => (1, n),
        Body::Chunked => (2, 0),
        Body::Close => (3, 0),
    }
}

fn spans(h: &[vhttp_header]) -> Vec<[usize; 4]> {
    h.iter().map(|h| [h.name.start, h.name.end, h.value.start, h.value.end]).collect()
}

fn rust_spans(h: &[Header]) -> Vec<[usize; 4]> {
    h.iter().map(|h| [h.name.start, h.name.end, h.value.start, h.value.end]).collect()
}

/// Returns the C result code.
fn check_request(b: &[u8], last_len: usize) -> i32 {
    let mut hs = Vec::new();
    let want = verilith_http::parse_request_with(b, last_len, CAP, &mut hs);
    unsafe {
        let mut h = [std::mem::zeroed::<vhttp_header>(); CAP];
        let mut n = CAP;
        let mut r = std::mem::zeroed::<vhttp_request>();
        let rc = vhttp_parse_request(b.as_ptr() as *const c_char, b.len(), last_len, h.as_mut_ptr(), &mut n, &mut r);
        match want {
            Ok(Status::Complete(q)) => {
                assert_eq!(rc, VHTTP_OK);
                assert_eq!(&b[r.method.start..r.method.end], q.method());
                assert_eq!(&b[r.target.start..r.target.end], q.target());
                assert_eq!((r.minor_version, r.head_len, (r.body, r.content_length)), (q.minor_version(), q.head_len, body(q.body)));
                assert_eq!(spans(&h[..n]), rust_spans(&hs));
            }
            Ok(Status::Partial) => assert_eq!((rc, n), (VHTTP_PARTIAL, 0)),
            Err(e) => {
                assert!((-14..=-1).contains(&rc) && n == 0);
                let msg = std::ffi::CStr::from_ptr(vhttp_error_message(rc)).to_str().unwrap();
                assert_eq!(msg, e.to_string());
                assert_eq!(vhttp_error_is_framing(rc), e.is_framing());
            }
        }
        rc
    }
}

fn check_response(b: &[u8], head: bool, connect: bool) -> i32 {
    let mut hs = Vec::new();
    let want = verilith_http::parse_response(b, head, connect, &mut hs);
    unsafe {
        let mut h = [std::mem::zeroed::<vhttp_header>(); CAP];
        let mut n = CAP;
        let mut r = std::mem::zeroed::<vhttp_response>();
        let rc = vhttp_parse_response(b.as_ptr() as *const c_char, b.len(), head, connect, h.as_mut_ptr(), &mut n, &mut r);
        match want {
            Ok(Status::Complete(_)) if hs.len() > CAP => assert_eq!((rc, n), (-8, 0)),
            Ok(Status::Complete(q)) => {
                assert_eq!(rc, VHTTP_OK);
                assert_eq!(&b[r.reason.start..r.reason.end], q.reason());
                assert_eq!((r.status, r.minor_version, r.head_len, (r.body, r.content_length)), (q.status(), q.minor_version(), q.head_len, body(q.body)));
                assert_eq!(spans(&h[..n]), rust_spans(&hs));
            }
            Ok(Status::Partial) => assert_eq!((rc, n), (VHTTP_PARTIAL, 0)),
            Err(e) => {
                assert!((-14..=-1).contains(&rc) && n == 0);
                assert_eq!(std::ffi::CStr::from_ptr(vhttp_error_message(rc)).to_str().unwrap(), e.to_string());
            }
        }
        rc
    }
}

const REQUESTS: &[&str] = &[
    "GET / HTTP/1.1\r\nHost: a\r\n\r\n",
    "\r\nPOST /p?q=1 HTTP/1.1\r\nHost: example.com\r\nContent-Length: 10\r\nAccept: */*\r\n\r\n0123456789",
    "PUT /x HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip, chunked\r\nX-A:  v \t\r\n\r\n",
    "GET http://a/b HTTP/1.0\r\nUser-Agent: t\r\n\r\n",
    "OPTIONS * HTTP/1.1\r\nHost: a\r\nA: 1\r\nB: 2\r\nC: 3\r\nD: 4\r\nE: 5\r\nF: 6\r\nG: 7\r\n\r\n",
    "OPTIONS * HTTP/1.1\r\nHost: a\r\nA: 1\r\nB: 2\r\nC: 3\r\nD: 4\r\nE: 5\r\nF: 6\r\nG: 7\r\nH: 8\r\n\r\n",
    "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\n\r\n",
    "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 6\r\nContent-Length: 6\r\n\r\n",
    "POST / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n",
    "POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n",
    "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, gzip\r\n\r\n",
];

const RESPONSES: &[&str] = &[
    "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello",
    "HTTP/1.1 204 No Content\r\nServer: s\r\n\r\n",
    "HTTP/1.0 200 \r\n\r\n",
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n",
    "HTTP/1.1 304 Not Modified\r\nContent-Length: 9\r\n\r\n",
    "HTTP/1.1 200 OK\r\nA: 1\r\nB: 2\r\nC: 3\r\nD: 4\r\nE: 5\r\nF: 6\r\nG: 7\r\nH: 8\r\nI: 9\r\n\r\n",
    "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\n",
];

const BYTES: &[u8] = b"\r\n :\t;,=/1a\x00\x7f\xff";

#[test]
fn requests_agree() {
    let (mut ok, mut partial, mut bad) = (0, 0, 0);
    for m in REQUESTS {
        let m = m.as_bytes();
        let mut codes = vec![check_request(m, 0)];
        // Prefixes, alone and as the next read after a shorter one.
        for i in 0..m.len() {
            codes.push(check_request(&m[..i], 0));
            codes.push(check_request(&m[..i], i / 2));
            codes.push(check_request(m, i));
        }
        for i in 0..m.len() {
            for &c in BYTES {
                let mut x = m.to_vec();
                x[i] = c;
                codes.push(check_request(&x, 0));
            }
        }
        for c in codes {
            match c {
                0 => ok += 1,
                1 => partial += 1,
                _ => bad += 1,
            }
        }
    }
    assert!(ok > 500 && partial > 500 && bad > 500, "{ok} {partial} {bad}");
}

#[test]
fn responses_agree() {
    let mut ok = 0;
    for m in RESPONSES {
        let m = m.as_bytes();
        for (head, connect) in [(false, false), (true, false), (false, true)] {
            ok += (check_response(m, head, connect) == 0) as usize;
            for i in 0..m.len() {
                check_response(&m[..i], head, connect);
                for &c in BYTES {
                    let mut x = m.to_vec();
                    x[i] = c;
                    ok += (check_response(&x, head, connect) == 0) as usize;
                }
            }
        }
    }
    assert!(ok > 500, "{ok}");
}

/// The C decoder against the Rust one, over every split in two and every
/// single-byte change of a body.
#[test]
fn chunked_agrees() {
    let body = b"3\r\nabc\r\n10;x=\"q\\\"\"\r\n0123456789abcdef\r\n0\r\nT: 1\r\n\r\nrest";
    let mut cases = vec![body.to_vec()];
    for i in 0..body.len() {
        for &c in BYTES {
            let mut x = body.to_vec();
            x[i] = c;
            cases.push(x);
        }
    }
    for case in &cases {
        for keep in [false, true] {
            for cut in 0..=case.len() {
                let mut rust = if keep { ChunkedDecoder::keeping_trailers() } else { ChunkedDecoder::new() };
                let mut c: vhttp_chunked = unsafe { std::mem::zeroed() };
                c.keep_trailers = keep;
                for piece in [&case[..cut], &case[cut..]] {
                    let (mut a, mut b) = (piece.to_vec(), piece.to_vec());
                    let want = rust.decode(&mut a);
                    let (mut out, mut rest) = (usize::MAX, usize::MAX);
                    let rc = unsafe { vhttp_chunked_decode(&mut c, b.as_mut_ptr() as *mut c_char, b.len(), &mut out, &mut rest) };
                    match want {
                        Err(_) => {
                            assert_eq!(rc, -14);
                            break;
                        }
                        Ok(Chunked::More { out: o }) => {
                            assert_eq!((rc, out, rest), (VHTTP_PARTIAL, o, 0));
                            assert_eq!(a[..o], b[..o]);
                            assert_eq!(unsafe { vhttp_chunked_in_data(&c) }, rust.in_data());
                        }
                        Ok(Chunked::Done { out: o, rest: r }) => {
                            assert_eq!((rc, out, rest), (VHTTP_OK, o, r));
                            assert_eq!(a[..o + r], b[..o + r]);
                            break;
                        }
                    }
                }
            }
        }
    }
}
