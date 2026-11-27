//! The compressor: its frames decoded by the proven decoder and by the
//! system libzstd (loaded with `dlopen`), and its C API.
#![allow(unsafe_op_in_unsafe_fn)]
use verilith_zstd::ccapi::*;
use verilith_zstd::capi::{InBuffer, OutBuffer};
use verilith_zstd::{compress, compress_exec, decompress, Params};

#[path = "libzstd.rs"]
#[allow(dead_code)]
mod lz;
use lz::{sample, Rng, Zstd};

const BIG: usize = if usize::BITS == 64 { (1u64 << 40) as usize } else { 1 << 30 };

fn is_err(r: usize) -> bool {
    r > 120usize.wrapping_neg()
}

/// Inputs of every kind the tests use: the sample kinds, plus a few
/// shapes the encoder treats specially.
fn inputs(r: &mut Rng) -> Vec<Vec<u8>> {
    let mut v = vec![vec![], vec![7], vec![0; 100_000], b"abcabcabcabcabcabcabcabc".to_vec()];
    for n in [2usize, 3, 7, 31, 63, 64, 65, 255, 256, 257, 1000, 4096, 65535, 131071, 131072, 131073, 300_000] {
        v.push(sample(r, n));
    }
    // A long input with matches far back (beyond small windows).
    let mut far = sample(r, 1 << 20);
    let head = far[..200_000].to_vec();
    far.extend_from_slice(&head);
    v.push(far);
    v
}

#[test]
fn round_trips_all_levels() {
    let z = Zstd::load();
    if z.is_none() {
        eprintln!("libzstd.so.1 not found: checking with the proven decoder only");
    }
    let mut r = Rng(0x1234_5678_9ABC_DEF1);
    let ins = inputs(&mut r);
    let mut count = 0;
    for level in [-5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 16, 19, 22] {
        for (k, src) in ins.iter().enumerate() {
            // The slow levels on the first inputs only.
            if level >= 16 && src.len() > 300_000 {
                continue;
            }
            let checksum = k % 2 == 0;
            let f = compress(src, level, checksum);
            assert_eq!(decompress(&f, BIG).as_deref(), Ok(&src[..]), "level {level} input {k}");
            if let Some(z) = &z {
                assert_eq!(z.decompress(&f, src.len()).as_deref(), Some(&src[..]), "libzstd: level {level} input {k}");
            }
            assert!(f.len() <= unsafe { zstd_compress_bound(src.len()) }, "bound: level {level} input {k}");
            count += 1;
        }
    }
    eprintln!("{count} frames");
}

#[test]
fn windows() {
    let z = Zstd::load();
    let mut r = Rng(77);
    let src = sample(&mut r, 700_000);
    for wlog in [10u32, 11, 13, 17, 20, 27, 31] {
        for level in [1, 3, 7] {
            let f = compress_exec(&src, Params { wlog, checksum: true, level });
            assert_eq!(decompress(&f, BIG).as_deref(), Ok(&src[..]), "wlog {wlog} level {level}");
            if let Some(z) = &z {
                if wlog <= 27 {
                    assert_eq!(z.decompress(&f, src.len()).as_deref(), Some(&src[..]), "libzstd: wlog {wlog}");
                }
            }
        }
    }
}

#[test]
fn random_inputs() {
    let z = Zstd::load();
    let mut r = Rng(0xDEAD_BEEF);
    for i in 0..300 {
        let n = match i % 3 {
            0 => r.below(300) as usize,
            1 => r.below(20_000) as usize,
            _ => r.below(400_000) as usize,
        };
        let src = sample(&mut r, n);
        let level = [1, 2, 3, 5, 6, 8, 9, 11][i % 8];
        let f = compress(&src, level, i % 5 == 0);
        assert_eq!(decompress(&f, BIG).as_deref(), Ok(&src[..]), "case {i}");
        if let Some(z) = &z {
            assert_eq!(z.decompress(&f, src.len()).as_deref(), Some(&src[..]), "libzstd: case {i}");
        }
    }
}

#[test]
fn c_one_shot() {
    let mut r = Rng(5);
    let src = sample(&mut r, 50_000);
    unsafe {
        let cap = zstd_compress_bound(src.len());
        let mut dst = vec![0u8; cap];
        let n = zstd_compress(dst.as_mut_ptr().cast(), cap, src.as_ptr().cast(), src.len(), 3);
        assert!(!is_err(n));
        assert_eq!(decompress(&dst[..n], BIG).as_deref(), Ok(&src[..]));
        // Too small a destination.
        let m = zstd_compress(dst.as_mut_ptr().cast(), n - 1, src.as_ptr().cast(), src.len(), 3);
        assert_eq!(m, 70usize.wrapping_neg());
        // A context, with parameters.
        let c = zstd_create_cctx();
        assert_eq!(zstd_cctx_set_parameter(c, 100, 19), 0);
        assert_eq!(zstd_cctx_set_parameter(c, 201, 1), 0);
        assert_eq!(zstd_cctx_set_parameter(c, 101, 12), 0);
        assert!(is_err(zstd_cctx_set_parameter(c, 101, 40)));
        assert!(is_err(zstd_cctx_set_parameter(c, 9999, 1)));
        let n = zstd_compress2(c, dst.as_mut_ptr().cast(), cap, src.as_ptr().cast(), src.len());
        assert!(!is_err(n));
        assert_eq!(decompress(&dst[..n], BIG).as_deref(), Ok(&src[..]));
        // Window 2^12 and a checksum: the frame header says so.
        assert_eq!(dst[4] & 0x04, 0x04);
        let n2 = zstd_compress_cctx(c, dst.as_mut_ptr().cast(), cap, src.as_ptr().cast(), src.len(), 1);
        assert!(!is_err(n2));
        assert_eq!(decompress(&dst[..n2], BIG).as_deref(), Ok(&src[..]));
        let mut v = 0;
        assert_eq!(zstd_cctx_get_parameter(c, 100, &mut v), 0);
        assert_eq!(v, 19);
        assert_eq!(zstd_cctx_reset(c, 3), 0);
        assert_eq!(zstd_cctx_get_parameter(c, 100, &mut v), 0);
        assert_eq!(v, 3);
        zstd_free_cctx(c);
        // Empty input.
        let n = zstd_compress(dst.as_mut_ptr().cast(), cap, std::ptr::null(), 0, 1);
        assert!(!is_err(n));
        assert_eq!(decompress(&dst[..n], BIG).as_deref(), Ok(&[][..]));
    }
}

/// Streams `src` in random pieces with random flushes into random-sized
/// output pieces.
unsafe fn stream(r: &mut Rng, src: &[u8], level: i32) -> Vec<u8> {
    let c = zstd_create_cstream();
    zstd_init_cstream(c, level);
    let mut out = Vec::new();
    let mut buf = vec![0u8; 1 << 18];
    let mut ip = 0;
    loop {
        let take = (r.below(70_000) as usize).min(src.len() - ip);
        let mut i = InBuffer { src: src[ip..].as_ptr().cast(), size: take, pos: 0 };
        let end = if ip + take == src.len() { 2 } else if r.below(8) == 0 { 1 } else { 0 };
        loop {
            let cap = 1 + r.below(buf.len() as u64) as usize;
            let mut o = OutBuffer { dst: buf.as_mut_ptr().cast(), size: cap, pos: 0 };
            let left = zstd_compress_stream2(c, &mut o, &mut i, end);
            assert!(!is_err(left), "stream error {}", left.wrapping_neg());
            out.extend_from_slice(&buf[..o.pos]);
            if i.pos == i.size && (end == 0 || left == 0) {
                break;
            }
        }
        ip += take;
        if end == 2 {
            break;
        }
    }
    zstd_free_cstream(c);
    out
}

#[test]
fn c_streaming() {
    let z = Zstd::load();
    let mut r = Rng(99);
    for case in 0..40 {
        let n = if case % 10 == 0 { 3_000_000 } else { r.below(400_000) as usize };
        let src = sample(&mut r, n);
        let level = [1, 3, 5, 9][case % 4];
        let f = unsafe { stream(&mut r, &src, level) };
        assert_eq!(decompress(&f, BIG).as_deref(), Ok(&src[..]), "case {case}");
        if let Some(z) = &z {
            assert_eq!(z.decompress(&f, src.len()).as_deref(), Some(&src[..]), "libzstd: case {case}");
        }
    }
    // Pledged size, wrong.
    unsafe {
        let c = zstd_create_cctx();
        assert_eq!(zstd_cctx_set_pledged_src_size(c, 10), 0);
        let src = [1u8; 11];
        let mut buf = vec![0u8; 100];
        let mut o = OutBuffer { dst: buf.as_mut_ptr().cast(), size: 100, pos: 0 };
        let mut i = InBuffer { src: src.as_ptr().cast(), size: 11, pos: 0 };
        assert!(is_err(zstd_compress_stream2(c, &mut o, &mut i, 2)));
        zstd_free_cctx(c);
    }
}

/// The fuzz target's checks (`fuzz/fuzz_targets/compress.rs`) on sample
/// inputs. `VZSTD_STRESS=n` runs `n` rounds (default 300).
#[test]
fn fuzz_checks() {
    let rounds: u64 = std::env::var("VZSTD_STRESS").ok().and_then(|s| s.parse().ok()).unwrap_or(300);
    let mut r = Rng(0xC0FFEE);
    for round in 0..rounds {
        let mut data: Vec<u8> = (0..4).map(|_| r.next() as u8).collect();
        let n = r.below(if round % 25 == 0 { 300_000 } else { 5000 }) as usize;
        // Keep the slow levels on small inputs.
        if n > 5000 {
            data[0] %= 10;
        }
        data.extend_from_slice(&sample(&mut r, n));
        verilith_zstd::ccapi::exercise(&data);
    }
}
