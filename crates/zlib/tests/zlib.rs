mod common;
use common::*;
use verilith_zlib::{Decompressor, Error, Format};

/// (level, strategy, flush) combinations: default, stored, fixed, RLE,
/// Huffman only, filtered, with full flushes.
const MODES: &[(i32, i32, usize)] = &[(6, 0, 0), (9, 0, 0), (1, 0, 0), (0, 0, 0), (6, 4, 0), (6, 3, 0), (6, 2, 0), (6, 1, 0), (6, 0, 3000)];

#[test]
fn roundtrip_all_formats() {
    let mut d = Decompressor::new();
    for data in corpus() {
        for &(level, strategy, flush) in MODES {
            for (fmt, wb) in [(Format::Raw, -15), (Format::Zlib, 15), (Format::Gzip, 31), (Format::Raw, -9)] {
                let c = compress(&data, level, wb, strategy, flush);
                let (out, used) = d.decompress_vec(fmt, &c, 1 << 30).unwrap_or_else(|e| panic!("{e:?} level {level} strategy {strategy} fmt {fmt:?} len {}", data.len()));
                assert_eq!(out, data, "level {level} strategy {strategy} fmt {fmt:?}");
                assert_eq!(used, c.len());
                // Exact-size buffer.
                let mut buf = vec![0u8; data.len()];
                assert_eq!(d.decompress_into(fmt, &c, &mut buf), Ok((c.len(), data.len())));
                assert_eq!(buf, data);
                // One byte short.
                if !data.is_empty() {
                    let mut buf = vec![0u8; data.len() - 1];
                    assert_eq!(d.decompress_into(fmt, &c, &mut buf), Err(Error::InsufficientSpace));
                }
            }
        }
    }
}

#[test]
fn output_limit() {
    let data = vec![7u8; 1 << 20];
    let c = compress(&data, 9, -15, 0, 0);
    let mut d = Decompressor::new();
    assert_eq!(d.decompress_vec(Format::Raw, &c, 1000).unwrap_err(), Error::InsufficientSpace);
    assert_eq!(d.decompress_vec(Format::Raw, &c, 1 << 20).unwrap().0, data);
}

#[test]
fn trailing_data_and_truncation() {
    let data = text(&mut Rng(5), 20_000);
    for (fmt, wb) in [(Format::Raw, -15), (Format::Zlib, 15), (Format::Gzip, 31)] {
        let c = compress(&data, 6, wb, 0, 0);
        let mut t = c.clone();
        t.extend_from_slice(b"trailing");
        let mut d = Decompressor::new();
        assert_eq!(d.decompress_vec(fmt, &t, 1 << 30).unwrap(), (data.clone(), c.len()));
        for cut in [0, 1, 2, c.len() / 2, c.len() - 1] {
            assert!(d.decompress_vec(fmt, &c[..cut], 1 << 30).is_err(), "cut {cut} {fmt:?}");
        }
    }
}

/// Mutated streams: vzlib must accept exactly what zlib accepts, with the
/// same output and the same input length.
#[test]
fn differential_mutations() {
    let mut rng = Rng(12345);
    let mut d = Decompressor::new();
    let bases: Vec<Vec<u8>> = corpus().into_iter().filter(|b| b.len() < 60_000).collect();
    let mut accepted = 0;
    for iter in 0..20_000 {
        let data = &bases[iter % bases.len()];
        let &(level, strategy, _) = &MODES[rng.below(8) as usize];
        let mut c = compress(data, level, -15, strategy, 0);
        let k = 1 + rng.below(4);
        for _ in 0..k {
            if c.is_empty() {
                break;
            }
            let i = if rng.below(2) == 0 { rng.below(c.len().min(64) as u64) as usize } else { rng.below(c.len() as u64) as usize };
            match rng.below(3) {
                0 => c[i] ^= 1 << rng.below(8),
                1 => c[i] = rng.next() as u8,
                _ => c.truncate(i),
            }
        }
        let ours = d.decompress_vec(Format::Raw, &c, 1 << 30).ok();
        let theirs = zinflate(&c, -15);
        if theirs.is_some() {
            accepted += 1;
        }
        assert_eq!(ours.is_some(), theirs.is_some(), "iter {iter}: ours {:?}", ours.as_ref().map(|o| o.0.len()));
        if let (Some(a), Some(b)) = (ours, theirs) {
            assert_eq!(a.0, b.0, "iter {iter}");
            assert_eq!(a.1, b.1, "iter {iter}");
        }
    }
    eprintln!("{accepted} of 20000 mutated streams were valid");
}

/// Random bytes, mostly invalid: same verdict as zlib.
#[test]
fn differential_random() {
    let mut rng = Rng(777);
    let mut d = Decompressor::new();
    for iter in 0..50_000 {
        let n = rng.below(200) as usize;
        let mut c: Vec<u8> = (0..n).map(|_| rng.next() as u8).collect();
        if !c.is_empty() && rng.below(2) == 0 {
            // Favour fixed and dynamic block types.
            c[0] = (c[0] & !6) | if rng.below(2) == 0 { 2 } else { 4 };
        }
        let ours = d.decompress_vec(Format::Raw, &c, 1 << 24).ok();
        let theirs = zinflate(&c, -15);
        assert_eq!(ours.is_some(), theirs.is_some(), "iter {iter}: {c:?}");
        if let (Some(a), Some(b)) = (ours, theirs) {
            assert_eq!(a.0, b.0);
            assert_eq!(a.1, b.1);
        }
    }
}

/// The SIMD checksums agree with the verified scalar ones.
#[test]
fn checksums_agree() {
    let mut rng = Rng(99);
    let data: Vec<u8> = (0..200_000).map(|_| rng.next() as u8).collect();
    for n in [0, 1, 15, 16, 63, 64, 127, 128, 129, 200, 1000, 32767, 32768, 32769, 70_000, 200_000] {
        for off in [0, 1, 7] {
            if off + n > data.len() {
                continue;
            }
            let d = &data[off..off + n];
            assert_eq!(verilith_zlib::checksum::crc32(d), !verilith_zlib::checksum::crc32_update(0xffff_ffff, d), "crc n {n}");
            let (a, b) = verilith_zlib::checksum::adler32_update(1, 0, d);
            // Scalar reference.
            let (mut ra, mut rb) = (1u32, 0u32);
            for &x in d {
                ra = (ra + x as u32) % 65521;
                rb = (rb + ra) % 65521;
            }
            assert_eq!((a, b), (ra, rb), "adler n {n}");
            assert_eq!(verilith_zlib::checksum::adler32(d), (rb << 16) | ra);
        }
    }
    // Long runs of 0xff stress the lane bounds.
    let ff = vec![0xffu8; 1 << 20];
    let (mut ra, mut rb) = (1u32, 0u32);
    for &x in &ff {
        ra = (ra + x as u32) % 65521;
        rb = (rb + ra) % 65521;
    }
    assert_eq!(verilith_zlib::checksum::adler32(&ff), (rb << 16) | ra);
}

/// Streaming in pieces of every size gives the same output and the same
/// input length as one call.
#[test]
fn streaming_pieces() {
    use verilith_zlib::stream::{Progress, Stream, Wrapper};
    let mut rng = Rng(4242);
    let inputs = corpus();
    for (k, data) in inputs.iter().enumerate() {
        for &(level, strategy, flush) in &MODES[..] {
            for (w, wb) in [(Wrapper::Raw, -15), (Wrapper::Zlib, 15), (Wrapper::Gzip, 31), (Wrapper::Auto, 31), (Wrapper::Auto, 15)] {
                let mut c = compress(data, level, wb, strategy, flush);
                let clen = c.len();
                c.extend_from_slice(b"TRAILING");
                let mut s = Stream::open(w);
                let mut out = Vec::new();
                let mut ip = 0;
                let mut buf = vec![0u8; 1 + rng.below(70_000) as usize];
                let mut stalls = 0;
                loop {
                    let lim = if rng.below(4) == 0 { 3 } else { 5000 };
                    let n = 1 + rng.below(lim) as usize;
                    let m = 1 + rng.below(buf.len() as u64) as usize;
                    let end = (ip + n).min(c.len());
                    let (used, made, p) = s.inflate(&c[ip..end], &mut buf[..m]).unwrap_or_else(|e| panic!("{e:?} input {k} level {level} {w:?}"));
                    ip += used;
                    out.extend_from_slice(&buf[..made]);
                    if p == Progress::End {
                        break;
                    }
                    if p == Progress::Stalled {
                        stalls += 1;
                        assert!(stalls < 1000, "stuck at {ip} of {clen}");
                    }
                }
                assert_eq!(&out, data, "input {k} level {level} strategy {strategy} {w:?}");
                assert_eq!(ip, clen, "input {k} level {level} strategy {strategy} {w:?}");
            }
        }
    }
}
