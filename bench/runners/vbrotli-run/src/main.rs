//! Brotli, verilith-brotli's Rust API (`Stream`) against google/brotli's
//! decoder API (suites/brotli/brotli.c), the same cases and check values:
//! decode-qQ/FILE in one `Stream::decompress` call into a reused buffer,
//! decode-chunked-qQ/FILE fed 1 KB per call into a 16 KB buffer.
use verilith_brotli::{Stream, StreamResult};

fn chunked(z: &[u8], out: &mut [u8]) -> u64 {
    let mut s = Stream::open();
    let (mut p, mut total, mut h) = (0usize, 0u64, 0u64);
    loop {
        assert!(p < z.len(), "truncated stream");
        let end = (p + 1024).min(z.len());
        let mut input = &z[p..end];
        p = end;
        loop {
            let (r, used, got) = s.decompress(input, &mut out[..16384]);
            input = &input[used..];
            assert!(r != StreamResult::Error, "decode error");
            // Every 61st byte of the whole output, as the C driver.
            let mut j = ((61 - total % 61) % 61) as usize;
            while j < got {
                h = (h ^ out[j] as u64).wrapping_mul(0x100000001b3);
                j += 61;
            }
            total += got as u64;
            match r {
                StreamResult::Success => return total ^ (h << 20),
                StreamResult::NeedsMoreOutput => continue,
                _ => break,
            }
        }
    }
}

fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let orig = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = orig.len();
        for q in [5, 11] {
            let z = std::fs::read(format!("{dir}/br/{name}.q{q}.br")).unwrap();
            let mut out = vec![0u8; len + 1];
            let (res, _, n) = Stream::open().decompress(&z, &mut out);
            assert!(res == StreamResult::Success && n == len && out[..n] == orig[..], "decoding {name}.q{q}.br does not give the original");
            let zc = z.clone();
            r.case(format!("decode-q{q}/{name}"), len as u64, move || {
                let (res, _, n) = Stream::open().decompress(std::hint::black_box(&zc), &mut out);
                assert!(res == StreamResult::Success);
                vbrun::mix(n as u64, &out[..n])
            });
            let mut buf = vec![0u8; 16384];
            assert_eq!(chunked(&z, &mut buf) & 0xfffff, len as u64 & 0xfffff);
            r.case(format!("decode-chunked-q{q}/{name}"), len as u64, move || chunked(std::hint::black_box(&z), &mut buf));
        }
    }
    r.main();
}
