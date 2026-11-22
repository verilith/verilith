//! google/brotli's test vectors (`tests/testdata`): every `X.compressed*`
//! decodes to `X`, one shot and in small pieces.
use verilith_brotli::stream::{Result, Stream};

fn decode_chunked(input: &[u8], in_step: usize, out_step: usize) -> (Result, Vec<u8>) {
    let mut s = Stream::open();
    let mut out = Vec::new();
    let mut ip = 0;
    let mut buf = vec![0u8; out_step];
    loop {
        let end = (ip + in_step).min(input.len());
        let (r, used, made) = s.decompress(&input[ip..end], &mut buf);
        ip += used;
        out.extend_from_slice(&buf[..made]);
        match r {
            Result::NeedsMoreInput => {
                if ip >= input.len() {
                    return (r, out);
                }
            },
            Result::NeedsMoreOutput => {},
            _ => return (r, out),
        }
    }
}

#[test]
fn testdata() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");
    let mut n = 0;
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        let name = p.file_name().unwrap().to_str().unwrap().to_string();
        let Some(i) = name.find(".compressed") else { continue };
        let want = std::fs::read(format!("{}/{}", dir, &name[..i])).unwrap();
        let input = std::fs::read(&p).unwrap();
        for (a, b) in [(usize::MAX, usize::MAX >> 40), (1, 1), (7, 13), (4096, 100)] {
            let (r, got) = decode_chunked(&input, a, b.max(1));
            assert!(r == Result::Success, "{} ({}, {}): not success", name, a, b);
            assert!(got == want, "{} ({}, {}): wrong output", name, a, b);
        }
        n += 1;
    }
    assert!(n > 30);
}

/// The completeness theorem of `Stream::decompress`, run: all of the input
/// and an output buffer of exactly the decoded size finish in one call.
#[test]
fn one_call_exact_fit() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        let name = p.file_name().unwrap().to_str().unwrap().to_string();
        let Some(i) = name.find(".compressed") else { continue };
        let want = std::fs::read(format!("{}/{}", dir, &name[..i])).unwrap();
        let input = std::fs::read(&p).unwrap();
        let mut s = Stream::open();
        let mut buf = vec![0u8; want.len()];
        let (r, used, made) = s.decompress(&input, &mut buf);
        assert!(r == Result::Success, "{}: {:?}", name, r as u8);
        assert!(made == want.len() && buf == want, "{}: wrong output", name);
        assert!(used <= input.len());
    }
}
