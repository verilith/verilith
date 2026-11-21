//! `verilith_http::httparse` against httparse: whenever vhttp accepts, httparse
//! accepts with the same results.
#![no_main]
use libfuzzer_sys::fuzz_target;
use verilith_http::httparse as v;

fuzz_target!(|data: &[u8]| {
    let mut ours_h = [v::EMPTY_HEADER; 16];
    let mut ours = v::Request::new(&mut ours_h);
    if let Ok(v::Status::Complete(n)) = ours.parse(data) {
        let mut theirs_h = [httparse::EMPTY_HEADER; 16];
        let mut theirs = httparse::Request::new(&mut theirs_h);
        assert_eq!(theirs.parse(data), Ok(httparse::Status::Complete(n)));
        assert_eq!((ours.method, ours.path, ours.version), (theirs.method, theirs.path, theirs.version));
        assert_eq!(ours.headers.len(), theirs.headers.len());
        for (a, b) in ours.headers.iter().zip(theirs.headers.iter()) {
            assert_eq!((a.name, a.value), (b.name, b.value));
        }
    }
    let mut ours_h = [v::EMPTY_HEADER; 16];
    let mut ours = v::Response::new(&mut ours_h);
    if let Ok(v::Status::Complete(n)) = ours.parse(data) {
        let mut theirs_h = [httparse::EMPTY_HEADER; 16];
        let mut theirs = httparse::Response::new(&mut theirs_h);
        assert_eq!(theirs.parse(data), Ok(httparse::Status::Complete(n)));
        assert_eq!((ours.version, ours.code, ours.reason), (theirs.version, theirs.code, theirs.reason));
    }
    let _ = v::parse_chunk_size(data);
    let mut hs = [v::EMPTY_HEADER; 16];
    let _ = v::parse_headers(data, &mut hs);
});
