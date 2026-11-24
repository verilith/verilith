//! The C API against the system libzstd's (loaded with `dlopen`).
use std::ffi::{c_char, c_int, c_void, CString};
use verilith_zstd::capi::*;

#[path = "libzstd.rs"]
#[allow(dead_code)]
mod lz;
use lz::{open_libzstd, sample, Rng, Zstd};

#[cfg(unix)]
unsafe extern "C" {
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

// No dynamic loading on wasm32-wasip1: the reference library is never
// found there, and the tests that compare with it skip.
#[cfg(not(unix))]
unsafe fn dlopen(_name: *const c_char, _flags: c_int) -> *mut c_void {
    std::ptr::null_mut()
}

#[cfg(not(unix))]
unsafe fn dlsym(_h: *mut c_void, _name: *const c_char) -> *mut c_void {
    std::ptr::null_mut()
}

type Stream = unsafe extern "C" fn(*mut c_void, *mut OutBuffer, *mut InBuffer) -> usize;
type Create = unsafe extern "C" fn() -> *mut c_void;
type Free = unsafe extern "C" fn(*mut c_void) -> usize;
type Size = unsafe extern "C" fn(*const c_void, usize) -> u64;
type Find = unsafe extern "C" fn(*const c_void, usize) -> usize;
type Code = unsafe extern "C" fn(usize) -> c_int;

struct Lib {
    stream: Stream,
    create: Create,
    free: Free,
    content_size: Size,
    find: Find,
    code: Code,
}

fn lib() -> Option<(Zstd, Lib)> {
    let z = Zstd::load()?;
    unsafe {
        let h = open_libzstd();
        let sym = |n: &str| dlsym(h, CString::new(n).unwrap().as_ptr());
        Some((
            z,
            Lib {
                stream: std::mem::transmute(sym("ZSTD_decompressStream")),
                create: std::mem::transmute(sym("ZSTD_createDCtx")),
                free: std::mem::transmute(sym("ZSTD_freeDCtx")),
                content_size: std::mem::transmute(sym("ZSTD_getFrameContentSize")),
                find: std::mem::transmute(sym("ZSTD_findFrameCompressedSize")),
                code: std::mem::transmute(sym("ZSTD_getErrorCode")),
            },
        ))
    }
}

/// Streams `c` through a decoder in random pieces. Returns the output,
/// the positions in the input where a call returned 0, and the error code.
fn run(c: &[u8], r: &mut Rng, mut call: impl FnMut(&mut OutBuffer, &mut InBuffer) -> usize, is_err: impl Fn(usize) -> Option<i32>) -> (Vec<u8>, Vec<usize>, Option<i32>) {
    let mut out = Vec::new();
    let mut ends = Vec::new();
    let mut ipos = 0;
    let mut stalls = 0;
    loop {
        let big = if r.below(4) == 0 { 300_000 } else { 1000 };
        let isz = (1 + r.below(big) as usize).min(c.len() - ipos);
        let big = if r.below(4) == 0 { 300_000 } else { 1000 };
        let osz = 1 + r.below(big) as usize;
        let mut obuf = vec![0u8; osz];
        let mut o = OutBuffer { dst: obuf.as_mut_ptr() as *mut c_void, size: osz, pos: 0 };
        let mut i = InBuffer { src: c[ipos..].as_ptr() as *const c_void, size: isz, pos: 0 };
        let ret = call(&mut o, &mut i);
        if let Some(e) = is_err(ret) {
            return (out, ends, Some(e));
        }
        out.extend_from_slice(&obuf[..o.pos]);
        ipos += i.pos;
        if ret == 0 {
            ends.push(ipos);
        }
        if i.pos == 0 && o.pos == 0 {
            stalls += 1;
        } else {
            stalls = 0;
        }
        if (ipos == c.len() && (ret == 0 || stalls > 3)) || stalls > 50 {
            return (out, ends, None);
        }
    }
}

#[test]
fn streaming_matches_libzstd() {
    let Some((z, l)) = lib() else { return };
    let mut r = Rng(4242);
    let mut agree = 0;
    let mut mismatches = 0;
    for round in 0..800 {
        let mut c = Vec::new();
        for _ in 0..1 + r.below(3) {
            let n = r.below(if round % 8 == 0 { 2_000_000 } else { 20_000 }) as usize;
            let src = sample(&mut r, n);
            let wlog = if r.below(3) == 0 { 10 + r.below(10) as i32 } else { 0 };
            c.extend_from_slice(&z.compress(&src, [1, 3, 9, 19][r.below(4) as usize], r.below(2) == 0, wlog, r.below(2) == 0, 0));
            if r.below(5) == 0 {
                c.extend_from_slice(&0x184D2A53u32.to_le_bytes());
                let k = r.below(10) as u32;
                c.extend_from_slice(&k.to_le_bytes());
                c.extend((0..k).map(|_| 7u8));
            }
        }
        let corrupt = round % 3 == 0;
        if corrupt && c.len() > 1 {
            let i = r.below(c.len() as u64) as usize;
            c[i] ^= 1 << r.below(8);
        }
        let seed = r.next();
        let theirs = unsafe {
            let d = (l.create)();
            let res = run(&c, &mut Rng(seed), |o, i| (l.stream)(d, o, i), |x| { let e = (l.code)(x); if e != 0 { Some(e) } else { None } });
            (l.free)(d);
            res
        };
        let ours = unsafe {
            let d = zstd_create_dctx();
            let res = run(&c, &mut Rng(seed), |o, i| zstd_decompress_stream(d, o, i), |x| { let e = zstd_get_error_code(x); if e != 0 { Some(e) } else { None } });
            zstd_free_dctx(d);
            res
        };
        if theirs.2.is_none() && ours.2.is_none() {
            assert_eq!(theirs.0, ours.0, "round {round}: output");
            assert_eq!(theirs.1, ours.1, "round {round}: frame ends");
            agree += 1;
        } else if theirs.2.is_some() && ours.2.is_some() {
            // Both fail: the output before the failure is a prefix of the same stream.
            let k = theirs.0.len().min(ours.0.len());
            assert_eq!(theirs.0[..k], ours.0[..k], "round {round}: output before error");
            if theirs.2 != ours.2 {
                eprintln!("round {round}: error codes libzstd {:?} vzstd {:?}", theirs.2, ours.2);
            }
            agree += 1;
        } else {
            mismatches += 1;
            eprintln!("round {round}: libzstd {:?} vzstd {:?} (corrupt {corrupt})", theirs.2, ours.2);
            assert!(theirs.2.is_none(), "round {round}: we accept what libzstd rejects");
        }
    }
    eprintln!("agree {agree}, libzstd-only accepts {mismatches}");
}

#[test]
fn one_shot_and_sizes() {
    let Some((z, l)) = lib() else { return };
    let mut r = Rng(99);
    for round in 0..400 {
        let n = r.below(50_000) as usize;
        let src = sample(&mut r, n);
        let mut c = z.compress(&src, 3, r.below(2) == 0, 0, r.below(2) == 0, 0);
        if round % 2 == 0 && c.len() > 1 {
            match r.below(3) {
                0 => {
                    let i = r.below(c.len() as u64) as usize;
                    c[i] ^= 1 << r.below(8);
                },
                1 => c.truncate(r.below(c.len() as u64) as usize),
                _ => {
                    let i = r.below(c.len().min(20) as u64) as usize;
                    c[i] ^= 1 << r.below(8);
                },
            }
        }
        unsafe {
            let p = c.as_ptr() as *const c_void;
            assert_eq!((l.content_size)(p, c.len()), zstd_get_frame_content_size(p, c.len()), "round {round}: content size");
            let (a, b) = ((l.find)(p, c.len()), zstd_find_frame_compressed_size(p, c.len()));
            let (ea, eb) = ((l.code)(a), zstd_get_error_code(b));
            assert_eq!((ea, if ea == 0 { a } else { 0 }), (eb, if eb == 0 { b } else { 0 }), "round {round}: frame size");
            for cap in [0, n / 2, n, n + 10] {
                let mut d1 = vec![0u8; cap];
                let mut d2 = vec![0u8; cap];
                let ra = { let f: unsafe extern "C" fn(*mut u8, usize, *const u8, usize) -> usize = std::mem::transmute(dlsym(open_libzstd(), CString::new("ZSTD_decompress").unwrap().as_ptr())); f(d1.as_mut_ptr(), cap, c.as_ptr(), c.len()) };
                let rb = zstd_decompress(d2.as_mut_ptr() as *mut c_void, cap, p, c.len());
                let (ea, eb) = ((l.code)(ra), zstd_get_error_code(rb));
                if ea == 0 && eb == 0 {
                    assert_eq!(ra, rb);
                    assert_eq!(d1[..ra], d2[..rb]);
                } else if ea != eb {
                    eprintln!("round {round} cap {cap} n {n}: libzstd {ea} vzstd {eb}");
                    if let Ok(dir) = std::env::var("VZSTD_DUMP") {
                        std::fs::write(format!("{dir}/r{round}_c{cap}_l{ea}_v{eb}.zst"), &c).unwrap();
                    }
                }
            }
        }
    }
}
