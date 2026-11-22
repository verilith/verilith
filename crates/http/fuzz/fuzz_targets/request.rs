//! The Rust API on arbitrary input: no panics, results in bounds, and the
//! same answer whether the head arrives at once or in two reads.
#![no_main]
use libfuzzer_sys::fuzz_target;
use verilith_http::{parse_request, parse_request_with, parse_response, Status};

fuzz_target!(|data: &[u8]| {
    if data.is_empty() {
        return;
    }
    let (ctl, buf) = (data[0], &data[1..]);
    let mut hs = Vec::new();
    let _ = parse_response(buf, ctl & 1 != 0, ctl & 2 != 0, &mut hs);
    let whole = parse_request(buf, &mut hs).map(|s| match s {
        Status::Complete(r) => {
            assert!(r.head_len <= buf.len());
            for (n, v) in r.headers(&hs) {
                assert!(!n.is_empty() && n.len() + v.len() <= r.head_len);
            }
            Some((r.head_len, r.body, hs.len(), r.method().to_vec(), r.target().to_vec()))
        }
        Status::Partial => None,
    });
    // A second read after a first of `cut` bytes, with picohttpparser's
    // last_len: the same complete head. (An invalid head may instead stay
    // Partial until CR LF CR LF arrives, as in picohttpparser.)
    let cut = (ctl as usize * buf.len()) / 255;
    let mut hs2 = Vec::new();
    if !matches!(parse_request_with(&buf[..cut], 0, 100, &mut hs2), Ok(Status::Partial)) {
        return;
    }
    let again = parse_request_with(buf, cut, 100, &mut hs2).map(|s| match s {
        Status::Complete(r) => Some((r.head_len, r.body, hs2.len(), r.method().to_vec(), r.target().to_vec())),
        Status::Partial => None,
    });
    if matches!(whole, Ok(Some(_))) || matches!(again, Ok(Some(_))) {
        assert_eq!(whole, again);
    }
});
