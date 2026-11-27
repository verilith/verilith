//! zlib, verilith-zlib's Rust API against zlib's API (suites/zlib/zlib.c),
//! the same cases and check values:
//!
//!   vzlib-run inflate   inflate/FILE: `Decompressor::decompress_into` of
//!                       FILE.z6 into a reused buffer, one call;
//!                       inflate-chunked/FILE: `stream::Stream::inflate` fed
//!                       1 KB of input per call into a 16 KB buffer
//!   vzlib-run deflate   deflate-L/FILE: `zlib_compress(FILE, L)`
use verilith_zlib::stream::{Progress, Stream, Wrapper};
use verilith_zlib::{Decompressor, Format};

/// The Adler-32 in a zlib stream's trailer: zlib's `adler` after inflate,
/// which the decompressor has checked against the output.
fn trailer(z: &[u8]) -> u64 {
    u32::from_be_bytes(z[z.len() - 4..].try_into().unwrap()) as u64
}

fn chunked(st: &mut Stream, z: &[u8], out: &mut [u8]) -> u64 {
    st.restart(Wrapper::Zlib);
    let (mut p, mut total) = (0usize, 0u64);
    loop {
        assert!(p < z.len(), "truncated stream");
        let end = (p + 1024).min(z.len());
        let mut input = &z[p..end];
        p = end;
        loop {
            let (used, made, pr) = st.inflate(input, &mut out[..16384]).expect("inflate");
            input = &input[used..];
            total += made as u64;
            if let Progress::End = pr {
                return total ^ ((st.check() as u64) << 32);
            }
            if made == 16384 || (!input.is_empty() && (used > 0 || made > 0)) {
                continue;
            }
            assert!(input.is_empty(), "inflate stalled with input left");
            break;
        }
    }
}

fn main() {
    let mode = vbrun::mode("inflate");
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let orig = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = orig.len();
        if mode == "inflate" {
            let z = std::fs::read(format!("{dir}/z6/{name}.z6")).unwrap();
            let mut d = Decompressor::new();
            let mut out = vec![0u8; len + 1];
            let (_, n) = d.decompress_into(Format::Zlib, &z, &mut out).unwrap();
            assert!(n == len && out[..n] == orig[..], "inflate of {name} does not give the original");
            let zc = z.clone();
            r.case(format!("inflate/{name}"), len as u64, move || {
                let (_, n) = d.decompress_into(Format::Zlib, std::hint::black_box(&zc), &mut out).unwrap();
                n as u64 ^ (trailer(&zc) << 32)
            });
            let mut st = Stream::open(Wrapper::Zlib);
            let mut buf = vec![0u8; 16384];
            assert_eq!(chunked(&mut st, &z, &mut buf) & 0xffff_ffff, len as u64 & 0xffff_ffff);
            r.case(format!("inflate-chunked/{name}"), len as u64, move || chunked(&mut st, std::hint::black_box(&z), &mut buf));
        } else {
            for level in [1u32, 6, 9] {
                let c = verilith_zlib::zlib_compress(&orig, level);
                assert!(verilith_zlib::zlib_decompress(&c).unwrap() == orig, "deflate-{level} of {name} does not round-trip");
                let data = orig.clone();
                r.case(format!("deflate-{level}/{name}"), len as u64, move || {
                    verilith_zlib::zlib_compress(std::hint::black_box(&data), level).len() as u64
                });
            }
        }
    }
    if mode == "inflate" {
        if let Ok(z) = std::fs::read(format!("{dir}/chunk/rle-16m.z6")) {
            let mut st = Stream::open(Wrapper::Zlib);
            let mut buf = vec![0u8; 16384];
            r.case("inflate-chunked/rle-16m", 16 << 20, move || chunked(&mut st, std::hint::black_box(&z), &mut buf));
        }
    }
    r.main();
}
