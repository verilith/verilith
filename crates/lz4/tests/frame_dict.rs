//! Frames with a dictionary: liblz4 compresses them
//! (`LZ4F_compressFrame_usingCDict`), and the proven decoder and the C API
//! (`LZ4F_decompress_usingDict`) must give what liblz4's decoder gives.
mod common;
use common::{frame_has_zero_offset, open_liblz4, sample, sym, Rng, KINDS};
use std::ffi::c_void;
use verilith_lz4::capi::{self, Dctx, Preferences};
use verilith_lz4::frame::{decode_frame_dict, Error, MAX_DICT_OUT};

type CreateCDict = unsafe extern "C" fn(*const c_void, usize) -> *mut c_void;
type FreeCDict = unsafe extern "C" fn(*mut c_void);
type CreateC = unsafe extern "C" fn(*mut *mut c_void, u32) -> usize;
type FreeC = unsafe extern "C" fn(*mut c_void) -> usize;
type CompressCDict =
    unsafe extern "C" fn(*mut c_void, *mut c_void, usize, *const c_void, usize, *const c_void, *const Preferences) -> usize;
type Bound = unsafe extern "C" fn(usize, *const Preferences) -> usize;
type DecDict = unsafe extern "C" fn(*mut c_void, *mut c_void, *mut usize, *const c_void, *mut usize, *const c_void, usize, *const c_void) -> usize;
type CreateD = unsafe extern "C" fn(*mut *mut c_void, u32) -> usize;
type FreeD = unsafe extern "C" fn(*mut c_void) -> usize;
type IsError = unsafe extern "C" fn(usize) -> u32;

struct Lib {
    create_cdict: CreateCDict,
    free_cdict: FreeCDict,
    create_c: CreateC,
    free_c: FreeC,
    compress: CompressCDict,
    bound: Bound,
    dec: DecDict,
    create_d: CreateD,
    free_d: FreeD,
    is_error: IsError,
}

fn lib() -> Option<Lib> {
    unsafe {
        let h = open_liblz4();
        if h.is_null() {
            return None;
        }
        Some(Lib {
            create_cdict: std::mem::transmute(sym(h, "LZ4F_createCDict")),
            free_cdict: std::mem::transmute(sym(h, "LZ4F_freeCDict")),
            create_c: std::mem::transmute(sym(h, "LZ4F_createCompressionContext")),
            free_c: std::mem::transmute(sym(h, "LZ4F_freeCompressionContext")),
            compress: std::mem::transmute(sym(h, "LZ4F_compressFrame_usingCDict")),
            bound: std::mem::transmute(sym(h, "LZ4F_compressFrameBound")),
            dec: std::mem::transmute(sym(h, "LZ4F_decompress_usingDict")),
            create_d: std::mem::transmute(sym(h, "LZ4F_createDecompressionContext")),
            free_d: std::mem::transmute(sym(h, "LZ4F_freeDecompressionContext")),
            is_error: std::mem::transmute(sym(h, "LZ4F_isError")),
        })
    }
}

/// Ours, behind the same signature as liblz4's.
fn our_dec() -> (DecDict, CreateD, FreeD, IsError) {
    unsafe {
        (
            std::mem::transmute(
                capi::f_decompress_using_dict
                    as unsafe extern "C" fn(*mut Dctx, *mut c_void, *mut usize, *const c_void, *mut usize, *const c_void, usize, *const c_void) -> usize,
            ),
            std::mem::transmute(capi::f_create_dctx as unsafe extern "C" fn(*mut *mut Dctx, u32) -> usize),
            std::mem::transmute(capi::f_free_dctx as unsafe extern "C" fn(*mut Dctx) -> usize),
            capi::f_is_error,
        )
    }
}

fn their_dec(l: &Lib) -> (DecDict, CreateD, FreeD, IsError) {
    (l.dec, l.create_d, l.free_d, l.is_error)
}

fn compress(l: &Lib, input: &[u8], dict: &[u8], p: &Preferences) -> Vec<u8> {
    unsafe {
        let cd = (l.create_cdict)(dict.as_ptr() as *const c_void, dict.len());
        assert!(!cd.is_null());
        let mut cctx = std::ptr::null_mut();
        assert_eq!((l.create_c)(&mut cctx, 100), 0);
        let cap = (l.bound)(input.len(), p);
        let mut out = vec![0u8; cap];
        let n = (l.compress)(cctx, out.as_mut_ptr() as *mut c_void, cap, input.as_ptr() as *const c_void, input.len(), cd, p);
        assert_eq!((l.is_error)(n), 0);
        out.truncate(n);
        (l.free_c)(cctx);
        (l.free_cdict)(cd);
        out
    }
}

/// Feeds `src` in pieces chosen by `seed`, the dictionary given with every
/// call. Gives the content and whether every call succeeded and the last
/// one ended the frame.
fn stream(d: (DecDict, CreateD, FreeD, IsError), src: &[u8], dict: &[u8], seed: u64) -> (Vec<u8>, bool) {
    let (dec, create, free, is_error) = d;
    let mut r = Rng(seed | 1);
    unsafe {
        let mut ctx = std::ptr::null_mut();
        assert_eq!(create(&mut ctx, 100), 0);
        let mut out = Vec::new();
        let mut buf = vec![0u8; 300_000];
        let mut pos = 0;
        let mut ok = false;
        let mut stalls = 0;
        loop {
            let big = if r.below(4) == 0 { 300_000 } else { 700 };
            let fed = (1 + r.below(big)).min(src.len() - pos);
            let big = if r.below(4) == 0 { 300_000 } else { 700 };
            let mut dn = 1 + r.below(big);
            let mut sn = fed;
            let ret = dec(ctx, buf.as_mut_ptr() as *mut c_void, &mut dn, src.as_ptr().add(pos) as *const c_void, &mut sn, dict.as_ptr() as *const c_void, dict.len(), std::ptr::null());
            if is_error(ret) != 0 {
                break;
            }
            out.extend_from_slice(&buf[..dn]);
            pos += sn;
            if ret == 0 && pos == src.len() {
                ok = true;
                break;
            }
            if dn == 0 && sn == 0 {
                stalls += 1;
                if stalls > 3 {
                    break;
                }
            } else {
                stalls = 0;
            }
        }
        free(ctx);
        (out, ok)
    }
}

/// A dictionary, and input that repeats pieces of it.
fn case(rng: &mut Rng, round: usize) -> (Vec<u8>, Vec<u8>, Preferences) {
    let dict_len = [1usize, 300, 5000, 65536, 70_000, 200_000][round % 6];
    let size = [0usize, 1, 40, 3000, 80_000, 300_000][round / 6 % 6];
    let dict = sample(rng, dict_len, round % KINDS);
    let mut input = Vec::with_capacity(size);
    while input.len() < size {
        if rng.below(3) > 0 {
            let from = rng.below(dict_len);
            let n = (4 + rng.below(300)).min(dict_len - from);
            input.extend_from_slice(&dict[from..from + n]);
        } else {
            input.push(rng.next() as u8);
        }
    }
    input.truncate(size);
    let mut p = Preferences::default();
    p.frame_info.block_size_id = [0u32, 4, 5, 6, 7][rng.below(5)];
    p.frame_info.block_mode = rng.below(2) as u32;
    p.frame_info.content_checksum_flag = rng.below(2) as u32;
    p.frame_info.block_checksum_flag = rng.below(2) as u32;
    p.frame_info.content_size = if rng.below(2) == 0 { size as u64 } else { 0 };
    p.frame_info.dict_id = if rng.below(2) == 0 { rng.next() as u32 } else { 0 };
    (dict, input, p)
}

#[test]
fn frames_with_a_dictionary() {
    let Some(l) = lib() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0x082efa98ec4e6c89);
    for round in 0..216 {
        let (dict, input, p) = case(&mut rng, round);
        let c = compress(&l, &input, &dict, &p);
        // The proven decoder.
        let mut out = vec![7u8; 3];
        assert_eq!(decode_frame_dict(&c, 0, &dict, &mut out, MAX_DICT_OUT), Ok(c.len()), "round {round}");
        assert_eq!(&out[..3], &[7, 7, 7]);
        assert_eq!(&out[3..], &input[..], "round {round}");
        // The C API, in pieces and in one call, against liblz4.
        let seed = rng.next();
        let a = stream(our_dec(), &c, &dict, seed);
        let b = stream(their_dec(&l), &c, &dict, seed);
        assert!(a.1 && b.1, "round {round}: ours {} theirs {}", a.1, b.1);
        assert_eq!(a.0, input, "round {round}");
        assert_eq!(b.0, input, "round {round}");
        let whole = stream(our_dec(), &c, &dict, u64::MAX);
        assert_eq!(whole.0, input, "round {round}");
        // Without the dictionary, or with another one: content that
        // reaches into the dictionary cannot be decoded.
        let mut no = Vec::new();
        let r = decode_frame_dict(&c, 0, &[], &mut no, MAX_DICT_OUT);
        if r.is_ok() {
            assert_eq!(no, input, "round {round}");
        }
    }
}

#[test]
fn the_dictionary_lasts_one_frame() {
    let Some(l) = lib() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0x452821e638d01377);
    let (dict, input, mut p) = case(&mut rng, 3 + 6 * 3);
    p.frame_info.block_mode = 0;
    let c = compress(&l, &input, &dict, &p);
    unsafe {
        let (dec, create, free, is_error) = our_dec();
        let mut ctx = std::ptr::null_mut();
        assert_eq!(create(&mut ctx, 100), 0);
        let mut buf = vec![0u8; input.len() + 10];
        // With the dictionary: decoded.
        let (mut dn, mut sn) = (buf.len(), c.len());
        let ret = dec(ctx, buf.as_mut_ptr() as *mut c_void, &mut dn, c.as_ptr() as *const c_void, &mut sn, dict.as_ptr() as *const c_void, dict.len(), std::ptr::null());
        assert_eq!(ret, 0);
        assert_eq!(&buf[..dn], &input[..]);
        // The same frame again through LZ4F_decompress on the same
        // context: the dictionary is gone, and the frame needs it.
        let (mut dn, mut sn) = (buf.len(), c.len());
        let ret = capi::f_decompress(ctx as *mut Dctx, buf.as_mut_ptr() as *mut c_void, &mut dn, c.as_ptr() as *const c_void, &mut sn, std::ptr::null());
        assert_ne!(is_error(ret), 0);
        free(ctx);
    }
}

#[test]
fn corrupted_frames_with_a_dictionary_agree() {
    let Some(l) = lib() else {
        eprintln!("liblz4 not found: skipped");
        return;
    };
    let mut rng = Rng(0xbe5466cf34e90c6c);
    let (mut both, mut ours_only, mut theirs_only, mut neither) = (0, 0, 0, 0);
    for round in 0..6000 {
        let (dict, input, p) = case(&mut rng, round % 24);
        let mut c = compress(&l, &input, &dict, &p);
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
        let a = stream(our_dec(), &c, &dict, seed);
        let b = stream(their_dec(&l), &c, &dict, seed);
        // The proven decoder decides as the C API does.
        let mut v = Vec::new();
        let r = decode_frame_dict(&c, 0, &dict, &mut v, MAX_DICT_OUT);
        assert_eq!(r == Ok(c.len()), a.1, "round {round}");
        if a.1 {
            assert_eq!(v, a.0, "round {round}");
        }
        assert_ne!(r, Err(Error::TooLarge));
        match (a.1, b.1) {
            (true, true) => {
                assert_eq!(a.0, b.0, "round {round}");
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
