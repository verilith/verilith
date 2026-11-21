//! The C API against the system liblz4's (loaded with `dlopen`).
mod common;
use common::{frame_has_zero_offset, open_liblz4, sample, sym, Lz4, Lz4f, Rng, KINDS};
use std::ffi::{c_char, c_int, c_void, CStr};
use verilith_lz4::capi::{self, Dctx, FrameInfo, Preferences};

type DecFn = unsafe extern "C" fn(*mut c_void, *mut c_void, *mut usize, *const c_void, *mut usize, *const c_void) -> usize;
type InfoFn = unsafe extern "C" fn(*mut c_void, *mut FrameInfo, *const c_void, *mut usize) -> usize;
type DictFn = unsafe extern "C" fn(*const c_char, *mut c_char, c_int, c_int, *const c_char, c_int) -> c_int;

struct Dec {
    create: unsafe extern "C" fn(*mut *mut c_void, u32) -> usize,
    free: unsafe extern "C" fn(*mut c_void) -> usize,
    dec: DecFn,
    info: InfoFn,
    is_error: unsafe extern "C" fn(usize) -> u32,
}

fn ours() -> Dec {
    unsafe {
        Dec {
            create: std::mem::transmute(capi::f_create_dctx as unsafe extern "C" fn(*mut *mut Dctx, u32) -> usize),
            free: std::mem::transmute(capi::f_free_dctx as unsafe extern "C" fn(*mut Dctx) -> usize),
            dec: std::mem::transmute(capi::f_decompress as unsafe extern "C" fn(*mut Dctx, *mut c_void, *mut usize, *const c_void, *mut usize, *const c_void) -> usize),
            info: std::mem::transmute(capi::f_get_frame_info as unsafe extern "C" fn(*mut Dctx, *mut FrameInfo, *const c_void, *mut usize) -> usize),
            is_error: capi::f_is_error,
        }
    }
}

fn theirs() -> Option<Dec> {
    unsafe {
        let h = open_liblz4();
        if h.is_null() {
            return None;
        }
        Some(Dec {
            create: std::mem::transmute(sym(h, "LZ4F_createDecompressionContext")),
            free: std::mem::transmute(sym(h, "LZ4F_freeDecompressionContext")),
            dec: std::mem::transmute(sym(h, "LZ4F_decompress")),
            info: std::mem::transmute(sym(h, "LZ4F_getFrameInfo")),
            is_error: std::mem::transmute(sym(h, "LZ4F_isError")),
        })
    }
}

/// Feeds `src` to a decoder in pieces chosen by `seed`, one context for
/// the whole input. Gives the content, the input positions where a call
/// returned 0 (frame ends), and whether it ended with an error.
fn stream(d: &Dec, src: &[u8], seed: u64) -> (Vec<u8>, Vec<usize>, bool) {
    let mut r = Rng(seed | 1);
    unsafe {
        let mut ctx = std::ptr::null_mut();
        assert_eq!((d.create)(&mut ctx, 100), 0);
        let mut out = Vec::new();
        let mut ends = Vec::new();
        let mut buf = vec![0u8; 300_000];
        let mut pos = 0;
        let mut failed = false;
        let mut stalls = 0;
        loop {
            let big = if r.below(4) == 0 { 300_000 } else { 700 };
            let fed = (1 + r.below(big)).min(src.len() - pos);
            let big = if r.below(4) == 0 { 300_000 } else { 700 };
            let mut dn = 1 + r.below(big);
            let mut sn = fed;
            let ret = (d.dec)(ctx, buf.as_mut_ptr() as *mut c_void, &mut dn, src.as_ptr().add(pos) as *const c_void, &mut sn, std::ptr::null());
            if (d.is_error)(ret) != 0 {
                failed = true;
                break;
            }
            assert!(sn <= fed);
            out.extend_from_slice(&buf[..dn]);
            pos += sn;
            if ret == 0 {
                ends.push(pos);
            }
            if pos == src.len() && dn == 0 && sn == 0 {
                stalls += 1;
                if ret == 0 || stalls > 2 {
                    break;
                }
            } else {
                stalls = 0;
            }
            if pos == src.len() && ret == 0 {
                break;
            }
        }
        (d.free)(ctx);
        (out, ends, failed)
    }
}

fn prefs(round: usize, len: usize) -> Preferences {
    let mut p = Preferences::default();
    p.frame_info.block_size_id = [0u32, 4, 5, 6, 7][round % 5];
    p.frame_info.block_mode = (round / 5 % 2) as u32;
    p.frame_info.content_checksum_flag = (round / 10 % 2) as u32;
    p.frame_info.block_checksum_flag = (round / 20 % 2) as u32;
    p.frame_info.content_size = if round / 40 % 2 == 0 { len as u64 } else { 0 };
    p
}

fn their_prefs(p: &Preferences) -> common::Preferences {
    // The same layout, declared twice.
    unsafe { std::mem::transmute(*p) }
}

fn our_frame(input: &[u8], p: &Preferences) -> Vec<u8> {
    unsafe {
        let cap = capi::f_compress_frame_bound(input.len(), p);
        let mut out = vec![0u8; cap];
        let n = capi::f_compress_frame(out.as_mut_ptr() as *mut c_void, cap, input.as_ptr() as *const c_void, input.len(), p);
        assert_eq!(capi::f_is_error(n), 0);
        out.truncate(n);
        out
    }
}

#[test]
fn blocks() {
    let Some(l) = Lz4::load() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0x13198a2e03707344);
    unsafe {
        assert_eq!(capi::version_number(), 10904);
        assert_eq!(CStr::from_ptr(capi::version_string()).to_str().unwrap(), "1.9.4");
        for n in [0usize, 1, 254, 255, 256, 65536, 1 << 20, 0x7E000000, 0x7E000001, 0x7FFFFFFF] {
            assert_eq!(capi::compress_bound_c(n as c_int) as usize, l.bound(n), "bound {n}");
        }
        assert_eq!(capi::compress_bound_c(-1), 0);
        for round in 0..600 {
            let size = [0usize, 1, 4, 12, 13, 40, 300, 5000, 70000, 300_000][round % 10];
            let input = sample(&mut rng, size, round % KINDS);
            let accel = [1, 1, 0, -5, 7, 100, 70000][round % 7];
            let cap = l.bound(size);
            let mut c = vec![0u8; cap];
            let n = capi::compress_fast(input.as_ptr() as *const c_char, c.as_mut_ptr() as *mut c_char, size as c_int, cap as c_int, accel);
            assert!(n > 0, "round {round}");
            c.truncate(n as usize);
            // liblz4 reads it back, with exactly the room needed.
            assert_eq!(l.decompress(&c, size).as_deref(), Some(&input[..]), "round {round}");
            // Too little room: 0, and nothing written past it.
            if n > 1 {
                let small = rng.below(n as usize);
                let mut d = vec![0xAAu8; n as usize + 8];
                let m = capi::compress_default(input.as_ptr() as *const c_char, d.as_mut_ptr() as *mut c_char, size as c_int, small as c_int);
                assert!(m == 0 || (m as usize) <= small);
                assert!(d[small..].iter().all(|&b| b == 0xAA), "round {round}");
            }
            // And the other way, with room to spare, exact room, too little.
            let c = l.compress(&input, 1);
            for cap in [size + 100, size, size.saturating_sub(1 + rng.below(20))] {
                let mut d = vec![0xAAu8; cap + 8];
                let m = capi::decompress_safe(c.as_ptr() as *const c_char, d.as_mut_ptr() as *mut c_char, c.len() as c_int, cap as c_int);
                if cap >= size {
                    assert_eq!(m as usize, size, "round {round}");
                    assert_eq!(&d[..size], &input[..]);
                } else {
                    assert!(m < 0, "round {round}");
                }
                assert!(d[cap..].iter().all(|&b| b == 0xAA), "round {round}");
            }
        }
    }
}

#[test]
fn blocks_with_a_dictionary() {
    let Some(l) = Lz4::load() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let their_dict: DictFn = unsafe { std::mem::transmute(sym(l.h, "LZ4_decompress_safe_usingDict")) };
    let mut rng = Rng(0xa4093822299f31d0);
    for round in 0..300 {
        let dict_len = [0usize, 5, 300, 65536, 100_000][round % 5];
        let size = [1usize, 40, 3000, 80_000][round % 4];
        // Data that repeats what the dictionary holds.
        let mut all = sample(&mut rng, dict_len, round % KINDS);
        while all.len() < dict_len + size {
            if dict_len > 0 && rng.below(3) > 0 {
                let from = rng.below(dict_len);
                let n = (1 + rng.below(200)).min(dict_len - from);
                let piece = all[from..from + n].to_vec();
                all.extend_from_slice(&piece);
            } else {
                all.push(rng.next() as u8);
            }
        }
        all.truncate(dict_len + size);
        let mut c = vec![0u8; verilith_lz4::compress::compress_bound(size)];
        let mut table = [0u32; verilith_lz4::compress::BIG_SIZE];
        let lo = dict_len.saturating_sub(65535);
        let n = verilith_lz4::compress::compress_block(&all, lo, dict_len, all.len(), &mut c, 0, &mut table, 1).unwrap();
        c.truncate(n);
        let (dict, data) = all.split_at(dict_len);
        let mut a = vec![0u8; size];
        let mut b = vec![0u8; size];
        unsafe {
            let x = capi::decompress_safe_using_dict(c.as_ptr() as *const c_char, a.as_mut_ptr() as *mut c_char, n as c_int, size as c_int, dict.as_ptr() as *const c_char, dict_len as c_int);
            let y = their_dict(c.as_ptr() as *const c_char, b.as_mut_ptr() as *mut c_char, n as c_int, size as c_int, dict.as_ptr() as *const c_char, dict_len as c_int);
            assert_eq!(x as usize, size, "round {round}");
            assert_eq!(y as usize, size, "round {round}");
        }
        assert_eq!(a, data, "round {round}");
        assert_eq!(b, data, "round {round}");
    }
}

#[test]
fn frames() {
    let (Some(l), Some(t)) = (Lz4f::load(), theirs()) else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let o = ours();
    let mut rng = Rng(0x082efa98ec4e6c89);
    for round in 0..800 {
        let size = [0usize, 1, 30, 4000, 65536, 70000, 300_000, 1_200_000][round % 8];
        let input = sample(&mut rng, size, round % KINDS);
        let mut p = prefs(round, size);
        p.compression_level = [0, 0, -3, 5][round / 80 % 4];
        // Ours fits the room liblz4 says is enough, and liblz4 reads it.
        let mine = our_frame(&input, &p);
        let (out, ends, failed) = stream(&t, &mine, rng.next());
        assert!(!failed, "round {round}");
        assert_eq!(out, input, "round {round}");
        assert_eq!(ends.last(), Some(&mine.len()), "round {round}");
        // Ours reads liblz4's, in pieces.
        let theirs = l.compress(&input, &their_prefs(&p));
        let (out, ends, failed) = stream(&o, &theirs, rng.next());
        assert!(!failed, "round {round}");
        assert_eq!(out, input, "round {round}");
        assert_eq!(ends.last(), Some(&theirs.len()), "round {round}");
        // The header says the same to both.
        unsafe {
            let mut infos = Vec::new();
            for d in [&o, &t] {
                let mut ctx = std::ptr::null_mut();
                (d.create)(&mut ctx, 100);
                let mut info = FrameInfo::default();
                let mut n = theirs.len();
                let r = (d.info)(ctx, &mut info, theirs.as_ptr() as *const c_void, &mut n);
                assert_eq!((d.is_error)(r), 0, "round {round}");
                // (liblz4 picks a smaller block size and independent blocks
                // for small inputs, so the preferences are not what to expect.)
                assert_eq!(info.content_size, p.frame_info.content_size, "round {round}");
                infos.push((info, n));
                // And the rest decodes from there.
                let mut out = vec![0u8; size + 1];
                let (mut dn, mut sn) = (out.len(), theirs.len() - n);
                let r = (d.dec)(ctx, out.as_mut_ptr() as *mut c_void, &mut dn, theirs.as_ptr().add(n) as *const c_void, &mut sn, std::ptr::null());
                assert_eq!(r, 0, "round {round}");
                assert_eq!(&out[..dn], &input[..], "round {round}");
                (d.free)(ctx);
            }
            assert_eq!(infos[0], infos[1], "round {round}");
        }
    }
}

#[test]
fn several_frames_one_context() {
    let (Some(l), Some(t)) = (Lz4f::load(), theirs()) else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let o = ours();
    let mut rng = Rng(0x38d01377be5466cf);
    for round in 0..200 {
        let mut all = Vec::new();
        let mut content = Vec::new();
        let mut want_ends = Vec::new();
        for k in 0..1 + rng.below(5) {
            if rng.below(4) == 0 {
                let n = rng.below(300);
                all.extend_from_slice(&(0x184D2A50u32 + rng.below(16) as u32).to_le_bytes());
                all.extend_from_slice(&(n as u32).to_le_bytes());
                all.extend((0..n).map(|_| rng.next() as u8));
            } else {
                let len = rng.below(100_000);
                let input = sample(&mut rng, len, (round + k) % KINDS);
                let p = prefs(round * 7 + k, input.len());
                if rng.below(2) == 0 {
                    all.extend_from_slice(&l.compress(&input, &their_prefs(&p)));
                } else {
                    all.extend_from_slice(&our_frame(&input, &p));
                }
                content.extend_from_slice(&input);
            }
            want_ends.push(all.len());
        }
        let seed = rng.next();
        let a = stream(&o, &all, seed);
        let b = stream(&t, &all, seed);
        assert!(!a.2 && !b.2, "round {round}");
        assert_eq!(a.0, content, "round {round}");
        assert_eq!(b.0, content, "round {round}");
        assert_eq!(a.1, want_ends, "round {round}");
        assert_eq!(b.1, want_ends, "round {round}");
    }
}

#[test]
fn corrupted_frames_agree() {
    let (Some(l), Some(t)) = (Lz4f::load(), theirs()) else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let o = ours();
    let mut rng = Rng(0x243f6a8885a308d3);
    let (mut both, mut ours_only, mut theirs_only, mut neither) = (0, 0, 0, 0);
    for round in 0..20000 {
        let size = [0usize, 5, 20, 300, 5000, 70000][round % 6];
        let input = sample(&mut rng, size, round % KINDS);
        let mut c = l.compress(&input, &their_prefs(&prefs(round, size)));
        for _ in 0..1 + rng.below(2) {
            let at = rng.below(c.len());
            match rng.below(4) {
                0 => c[at] ^= 1 << rng.below(8),
                1 => c[at] = rng.next() as u8,
                2 => c.truncate(at),
                _ => c.insert(at, rng.next() as u8),
            }
            if c.is_empty() {
                break;
            }
        }
        let seed = rng.next();
        let a = stream(&o, &c, seed);
        let b = stream(&t, &c, seed);
        // Accepted: no error, and the input ended where a frame did.
        let ok = |r: &(Vec<u8>, Vec<usize>, bool)| !r.2 && r.1.last() == Some(&c.len());
        match (ok(&a), ok(&b)) {
            (true, true) => {
                assert_eq!(a.0, b.0, "round {round}");
                assert_eq!(a.1, b.1, "round {round}");
                both += 1;
            }
            (true, false) => ours_only += 1,
            (false, true) => {
                assert!(frame_has_zero_offset(&c), "round {round}: liblz4 accepts what vlz4 rejects");
                theirs_only += 1;
            }
            (false, false) => neither += 1,
        }
    }
    eprintln!("both accept {both}, vlz4 only {ours_only}, liblz4 only {theirs_only}, neither {neither}");
}

#[test]
fn errors() {
    unsafe {
        let e = capi::f_compress_frame(std::ptr::null_mut(), 0, b"abc".as_ptr() as *const c_void, 3, std::ptr::null());
        assert_eq!(capi::f_is_error(e), 1);
        assert_eq!(CStr::from_ptr(capi::f_get_error_name(e)).to_str().unwrap(), "ERROR_dstMaxSize_tooSmall");
        assert_eq!(capi::f_is_error(0), 0);
        assert_eq!(capi::f_is_error(12345), 0);
        let mut ctx = std::ptr::null_mut();
        assert_eq!(capi::f_create_dctx(&mut ctx, 100), 0);
        let mut out = [0u8; 16];
        let (mut dn, mut sn) = (16usize, 8usize);
        let r = capi::f_decompress(ctx, out.as_mut_ptr() as *mut c_void, &mut dn, b"notlz4!!".as_ptr() as *const c_void, &mut sn, std::ptr::null());
        assert_eq!(CStr::from_ptr(capi::f_get_error_name(r)).to_str().unwrap(), "ERROR_frameType_unknown");
        capi::f_free_dctx(ctx);
    }
}
