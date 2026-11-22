//! Differential tests against the system's libzstd, loaded at run time
//! with `dlopen` (nothing is built or linked from C). Skipped, with a
//! message, when libzstd.so.1 is not installed.
#![allow(unsafe_op_in_unsafe_fn)]
use std::ffi::{c_char, c_int, c_void, CString};
use verilith_zstd::frame::{decompress_exec, Error};

unsafe extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

type Compress2 = unsafe extern "C" fn(*mut c_void, *mut u8, usize, *const u8, usize) -> usize;
type Bound = unsafe extern "C" fn(usize) -> usize;
type Decompress = unsafe extern "C" fn(*mut u8, usize, *const u8, usize) -> usize;
type IsError = unsafe extern "C" fn(usize) -> u32;
type CreateCCtx = unsafe extern "C" fn() -> *mut c_void;
type SetParam = unsafe extern "C" fn(*mut c_void, c_int, c_int) -> usize;
type Reset = unsafe extern "C" fn(*mut c_void, c_int) -> usize;

/// libzstd, under its Linux or macOS name (or VZSTD_LIBZSTD).
pub unsafe fn open_libzstd() -> *mut c_void {
    let mut names: Vec<String> = std::env::var("VZSTD_LIBZSTD").into_iter().collect();
    names.extend(["libzstd.so.1", "libzstd.1.dylib", "/opt/homebrew/lib/libzstd.1.dylib", "/usr/local/lib/libzstd.1.dylib"].iter().map(|s| s.to_string()));
    for n in names {
        let h = dlopen(CString::new(n).unwrap().as_ptr(), 2);
        if !h.is_null() {
            return h;
        }
    }
    std::ptr::null_mut()
}

pub struct Zstd {
    compress2: Compress2,
    bound: Bound,
    decompress: Decompress,
    is_error: IsError,
    set_param: SetParam,
    reset: Reset,
    cctx: *mut c_void,
}

const C_LEVEL: c_int = 100;
const C_WINDOWLOG: c_int = 101;
const C_CHECKSUM: c_int = 201;
const C_CONTENTSIZE: c_int = 200;
const C_STRATEGY: c_int = 107;

impl Zstd {
    pub fn load() -> Option<Zstd> {
        unsafe {
            let h = open_libzstd();
            if h.is_null() {
                return None;
            }
            let sym = |n: &str| {
                let p = dlsym(h, CString::new(n).unwrap().as_ptr());
                assert!(!p.is_null(), "{n}");
                p
            };
            let create: CreateCCtx = std::mem::transmute(sym("ZSTD_createCCtx"));
            Some(Zstd {
                compress2: std::mem::transmute(sym("ZSTD_compress2")),
                bound: std::mem::transmute(sym("ZSTD_compressBound")),
                decompress: std::mem::transmute(sym("ZSTD_decompress")),
                is_error: std::mem::transmute(sym("ZSTD_isError")),
                set_param: std::mem::transmute(sym("ZSTD_CCtx_setParameter")),
                reset: std::mem::transmute(sym("ZSTD_CCtx_reset")),
                cctx: create(),
            })
        }
    }

    pub fn compress(&self, src: &[u8], level: i32, checksum: bool, wlog: i32, size: bool, strategy: i32) -> Vec<u8> {
        unsafe {
            (self.reset)(self.cctx, 3);
            (self.set_param)(self.cctx, C_LEVEL, level);
            (self.set_param)(self.cctx, C_CHECKSUM, checksum as c_int);
            (self.set_param)(self.cctx, C_CONTENTSIZE, size as c_int);
            if wlog != 0 {
                (self.set_param)(self.cctx, C_WINDOWLOG, wlog);
            }
            if strategy != 0 {
                (self.set_param)(self.cctx, C_STRATEGY, strategy);
            }
            let mut dst = vec![0u8; (self.bound)(src.len())];
            let n = (self.compress2)(self.cctx, dst.as_mut_ptr(), dst.len(), src.as_ptr(), src.len());
            assert!((self.is_error)(n) == 0, "compress failed");
            dst.truncate(n);
            dst
        }
    }

    /// libzstd's one-shot decompression, with room for `cap` bytes.
    pub fn decompress(&self, src: &[u8], cap: usize) -> Option<Vec<u8>> {
        let mut dst = vec![0u8; cap];
        let n = unsafe { (self.decompress)(dst.as_mut_ptr(), cap, src.as_ptr(), src.len()) };
        if unsafe { (self.is_error)(n) } != 0 {
            return None;
        }
        dst.truncate(n);
        Some(dst)
    }
}

pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

/// Test inputs of several kinds: random, runs, text-like, repeats with
/// edits, and mixtures.
pub fn sample(r: &mut Rng, n: usize) -> Vec<u8> {
    let kind = r.below(6);
    let mut v = Vec::with_capacity(n);
    match kind {
        0 => (0..n).for_each(|_| v.push(r.next() as u8)),
        1 => {
            while v.len() < n {
                let c = r.next() as u8;
                let k = 1 + r.below(300) as usize;
                v.extend(std::iter::repeat(c).take(k));
            }
        },
        2 => {
            let words: Vec<Vec<u8>> = (0..200)
                .map(|_| (0..1 + r.below(10)).map(|_| b'a' + r.below(26) as u8).collect())
                .collect();
            while v.len() < n {
                // Skewed word choice, like text.
                let i = (r.below(200) * r.below(200) / 200) as usize;
                v.extend_from_slice(&words[i]);
                v.push(if r.below(12) == 0 { b'\n' } else { b' ' });
            }
        },
        3 => {
            let base: Vec<u8> = (0..1 + r.below(5000)).map(|_| r.next() as u8).collect();
            while v.len() < n {
                let mut b = base.clone();
                for _ in 0..r.below(20) {
                    let i = r.below(b.len() as u64) as usize;
                    b[i] = r.next() as u8;
                }
                v.extend_from_slice(&b);
            }
        },
        4 => (0..n).for_each(|_| v.push(b'a' + r.below(4) as u8)),
        _ => {
            while v.len() < n {
                let k = 1 + r.below(2000) as usize;
                let s = sample(r, k);
                v.extend_from_slice(&s);
            }
        },
    }
    v.truncate(n);
    v
}

fn lib() -> Option<Zstd> {
    let z = Zstd::load();
    if z.is_none() {
        eprintln!("libzstd.so.1 not found: skipping");
    }
    z
}

#[test]
fn round_trips() {
    let Some(z) = lib() else { return };
    let mut r = Rng(0x9E3779B97F4A7C15);
    let sizes = [0usize, 1, 2, 3, 7, 31, 32, 33, 100, 1000, 4096, 65535, 131072, 131073, 300_000, 1_500_000];
    let mut count = 0;
    for &n in sizes.iter() {
        for _ in 0..6 {
            let src = sample(&mut r, n);
            let level = [-5, -1, 1, 3, 6, 9, 12, 16, 19][r.below(9) as usize];
            let checksum = r.below(2) == 0;
            let size = r.below(3) != 0;
            let wlog = if r.below(3) == 0 { 10 + r.below(8) as i32 } else { 0 };
            let strategy = if r.below(4) == 0 { 1 + r.below(9) as i32 } else { 0 };
            let c = z.compress(&src, level, checksum, wlog, size, strategy);
            let ours = decompress_exec(&c, 1 << 40);
            assert_eq!(ours.as_deref().ok(), Some(&src[..]), "n={n} level={level} wlog={wlog} strategy={strategy}");
            count += 1;
        }
    }
    eprintln!("{count} round trips");
}

#[test]
fn concatenated_and_skippable() {
    let Some(z) = lib() else { return };
    let mut r = Rng(12345);
    for _ in 0..50 {
        let mut all = Vec::new();
        let mut want = Vec::new();
        for _ in 0..1 + r.below(4) {
            if r.below(3) == 0 {
                let k = r.below(20) as u32;
                all.extend_from_slice(&(0x184D2A50u32 + r.below(16) as u32).to_le_bytes());
                all.extend_from_slice(&k.to_le_bytes());
                all.extend((0..k).map(|_| r.next() as u8));
            } else {
                let n = r.below(5000) as usize;
                let src = sample(&mut r, n);
                all.extend_from_slice(&z.compress(&src, 3, r.below(2) == 0, 0, true, 0));
                want.extend_from_slice(&src);
            }
        }
        assert_eq!(decompress_exec(&all, 1 << 40).ok(), Some(want.clone()));
        assert_eq!(z.decompress(&all, want.len()), Some(want));
    }
}

#[test]
fn output_limit() {
    let Some(z) = lib() else { return };
    let mut r = Rng(777);
    let src = sample(&mut r, 200_000);
    let c = z.compress(&src, 3, true, 0, true, 0);
    assert_eq!(decompress_exec(&c, src.len()).ok(), Some(src.clone()));
    assert_eq!(decompress_exec(&c, src.len() - 1), Err(Error::TooLarge));
    assert_eq!(decompress_exec(&c, 0), Err(Error::TooLarge));
}

/// Corrupted frames: wherever libzstd accepts, we must give the same
/// bytes, and wherever we accept, libzstd must too, unless the difference
/// is one of the documented departures (both are counted).
#[test]
fn mutations_agree() {
    let Some(z) = lib() else { return };
    let mut r = Rng(0xDEADBEEF);
    let (mut both_ok, mut both_err, mut only_lib, mut only_us) = (0, 0, 0, 0);
    for round in 0..3000 {
        let n = r.below(if round % 10 == 0 { 300_000 } else { 3000 }) as usize;
        let src = sample(&mut r, n);
        let level = [-1, 1, 3, 9, 19][r.below(5) as usize];
        let mut c = z.compress(&src, level, r.below(2) == 0, 0, r.below(2) == 0, 0);
        let edits = 1 + r.below(4);
        for _ in 0..edits {
            match r.below(4) {
                0 if c.len() > 1 => {
                    let i = r.below(c.len() as u64) as usize;
                    c[i] ^= 1 << r.below(8);
                },
                1 if c.len() > 1 => {
                    let i = r.below(c.len() as u64) as usize;
                    c[i] = r.next() as u8;
                },
                2 if c.len() > 1 => {
                    let i = r.below(c.len() as u64) as usize;
                    c.truncate(i);
                },
                _ => {
                    let i = r.below(c.len() as u64 + 1) as usize;
                    c.insert(i, r.next() as u8);
                },
            }
        }
        let cap = 4 * n + 1000;
        let theirs = z.decompress(&c, cap);
        let ours = decompress_exec(&c, cap);
        match (&theirs, &ours) {
            (Some(a), Ok(b)) => {
                assert_eq!(a, b, "round {round}: outputs differ");
                both_ok += 1;
            },
            (None, Err(_)) => both_err += 1,
            (Some(_), Err(e)) => {
                only_lib += 1;
                if let Ok(dir) = std::env::var("VZSTD_DUMP") {
                    eprintln!("round {round}: libzstd accepts, we say {e:?}");
                    std::fs::write(format!("{dir}/case{round}.zst"), &c).unwrap();
                }
            },
            (None, Ok(_)) => {
                only_us += 1;
                eprintln!("round {round}: we accept, libzstd rejects: {:02x?}", &c[..c.len().min(64)]);
            },
        }
    }
    eprintln!("both ok {both_ok}, both err {both_err}, only libzstd ok {only_lib}, only vzstd ok {only_us}");
    assert_eq!(only_us, 0);
}

/// Compresses each file in VZSTD_SAMPLES/raw at levels 3 and 19 into
/// VZSTD_SAMPLES, for profiling.
#[test]
#[ignore]
fn write_samples() {
    let (Some(z), Ok(dir)) = (lib(), std::env::var("VZSTD_SAMPLES")) else { return };
    for e in std::fs::read_dir(format!("{dir}/raw")).unwrap() {
        let p = e.unwrap().path();
        let src = std::fs::read(&p).unwrap();
        for l in [3, 19] {
            let name = p.file_name().unwrap().to_string_lossy();
            std::fs::write(format!("{dir}/{name}.{l}.zst"), z.compress(&src, l, true, 0, true, 0)).unwrap();
        }
    }
}
