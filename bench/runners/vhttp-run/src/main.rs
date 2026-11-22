//! HTTP/1.1 through vhttp's own API, the native side of the comparisons
//! with picohttpparser and llhttp. The originals run the same drivers as in
//! the drop-in comparisons (suites/http/pico.c, suites/http/llhttp.c read).
//!
//!   vhttp-run pico     cases pico/MSG: verilith_http::parse_request or
//!                      parse_response into a reused header vector.
//!                      check = head length * 1000 + header count.
//!                      vhttp also works out the body framing here, which
//!                      picohttpparser leaves to the caller.
//!   vhttp-run llhttp   cases llhttp/MSG: parse the head, read the target
//!                      or reason and every header name and value, then
//!                      the body: by Content-Length, or through
//!                      ChunkedDecoder. check = header fields * 1000003 +
//!                      the bytes of all of those.
//!                      ChunkedDecoder decodes in place, so a chunked body
//!                      is first copied into a reused scratch buffer to
//!                      keep the input intact; that copy is in our time.
use verilith_http::{Body, Chunked, ChunkedDecoder, Header, Status};

fn head(msg: &[u8], response: bool, hs: &mut Vec<Header>) -> u64 {
    let n = if response {
        match verilith_http::parse_response(msg, false, false, hs) {
            Ok(Status::Complete(r)) => r.head_len,
            _ => std::process::abort(),
        }
    } else {
        match verilith_http::parse_request(msg, hs) {
            Ok(Status::Complete(r)) => r.head_len,
            _ => std::process::abort(),
        }
    };
    n as u64 * 1000 + hs.len() as u64
}

fn message(msg: &[u8], response: bool, hs: &mut Vec<Header>, scratch: &mut Vec<u8>) -> u64 {
    let (mut bytes, head_len, body);
    if response {
        let Ok(Status::Complete(r)) = verilith_http::parse_response(msg, false, false, hs) else { std::process::abort() };
        bytes = r.reason().len();
        for (n, v) in r.headers(hs) {
            bytes += n.len() + v.len();
        }
        (head_len, body) = (r.head_len, r.body);
    } else {
        let Ok(Status::Complete(r)) = verilith_http::parse_request(msg, hs) else { std::process::abort() };
        bytes = r.target().len();
        for (n, v) in r.headers(hs) {
            bytes += n.len() + v.len();
        }
        (head_len, body) = (r.head_len, r.body);
    }
    let rest = &msg[head_len..];
    bytes += match body {
        Body::Empty => 0,
        Body::Length(n) => {
            if (rest.len() as u64) < n {
                std::process::abort();
            }
            n as usize
        }
        Body::Close => rest.len(),
        Body::Chunked => {
            scratch.clear();
            scratch.extend_from_slice(rest);
            match ChunkedDecoder::new().decode(scratch) {
                Ok(Chunked::Done { out, .. }) => {
                    std::hint::black_box(&scratch[..out]);
                    out
                }
                _ => std::process::abort(),
            }
        }
    };
    hs.len() as u64 * 1000003 + bytes as u64
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "pico".into());
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".http") else { continue };
        let msg = std::fs::read(format!("{dir}/{name}")).unwrap();
        let response = stem.starts_with("resp");
        let len = msg.len() as u64;
        let mut hs: Vec<Header> = Vec::with_capacity(100);
        let mut scratch = Vec::with_capacity(msg.len());
        if mode == "llhttp" {
            r.case(format!("llhttp/{stem}"), len, move || message(std::hint::black_box(&msg), response, &mut hs, &mut scratch));
        } else {
            r.case(format!("pico/{stem}"), len, move || head(std::hint::black_box(&msg), response, &mut hs));
        }
    }
    r.main();
}
