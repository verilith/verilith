#![allow(dead_code)]
use std::ffi::{c_char, c_int, c_void, CString};

extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

/// libsnappy, under its Linux or macOS name (or VSNAPPY_LIBSNAPPY).
pub unsafe fn open_libsnappy() -> *mut c_void {
    let mut names: Vec<String> = std::env::var("VSNAPPY_LIBSNAPPY").into_iter().collect();
    names.extend(
        ["libsnappy.so.1", "libsnappy.1.dylib", "/opt/homebrew/lib/libsnappy.1.dylib", "/usr/local/lib/libsnappy.1.dylib"]
            .iter()
            .map(|s| s.to_string()),
    );
    for n in names {
        let h = dlopen(CString::new(n).unwrap().as_ptr(), 2);
        if !h.is_null() {
            return h;
        }
    }
    std::ptr::null_mut()
}

unsafe fn sym(h: *mut c_void, n: &str) -> *mut c_void {
    let p = dlsym(h, CString::new(n).unwrap().as_ptr());
    assert!(!p.is_null(), "{n}");
    p
}

type Compress = unsafe extern "C" fn(*const u8, usize, *mut u8, *mut usize) -> c_int;
type Uncompress = unsafe extern "C" fn(*const u8, usize, *mut u8, *mut usize) -> c_int;
type MaxLen = unsafe extern "C" fn(usize) -> usize;
type ULen = unsafe extern "C" fn(*const u8, usize, *mut usize) -> c_int;
type Validate = unsafe extern "C" fn(*const u8, usize) -> c_int;

/// google/snappy through its C API (snappy-c.h).
pub struct Snappy {
    compress: Compress,
    uncompress: Uncompress,
    max_len: MaxLen,
    ulen: ULen,
    validate: Validate,
}

impl Snappy {
    pub fn load() -> Option<Snappy> {
        unsafe {
            let h = open_libsnappy();
            if h.is_null() {
                return None;
            }
            Some(Snappy {
                compress: std::mem::transmute(sym(h, "snappy_compress")),
                uncompress: std::mem::transmute(sym(h, "snappy_uncompress")),
                max_len: std::mem::transmute(sym(h, "snappy_max_compressed_length")),
                ulen: std::mem::transmute(sym(h, "snappy_uncompressed_length")),
                validate: std::mem::transmute(sym(h, "snappy_validate_compressed_buffer")),
            })
        }
    }

    pub fn max_len(&self, n: usize) -> usize {
        unsafe { (self.max_len)(n) }
    }

    pub fn compress(&self, input: &[u8]) -> Vec<u8> {
        let mut out = vec![0u8; self.max_len(input.len())];
        let n = self.compress_into(input, &mut out);
        out.truncate(n);
        out
    }

    pub fn compress_into(&self, input: &[u8], out: &mut [u8]) -> usize {
        let mut n = out.len();
        let r = unsafe { (self.compress)(input.as_ptr(), input.len(), out.as_mut_ptr(), &mut n) };
        assert_eq!(r, 0);
        n
    }

    pub fn uncompressed_length(&self, src: &[u8]) -> Option<usize> {
        let mut n = 0;
        let r = unsafe { (self.ulen)(src.as_ptr(), src.len(), &mut n) };
        (r == 0).then_some(n)
    }

    pub fn validate(&self, src: &[u8]) -> bool {
        unsafe { (self.validate)(src.as_ptr(), src.len()) == 0 }
    }

    /// 0 OK, 1 invalid input, 2 buffer too small.
    pub fn uncompress_into(&self, src: &[u8], out: &mut [u8]) -> Result<usize, c_int> {
        let mut n = out.len();
        let r = unsafe { (self.uncompress)(src.as_ptr(), src.len(), out.as_mut_ptr(), &mut n) };
        if r == 0 {
            Ok(n)
        } else {
            Err(r)
        }
    }

    pub fn uncompress(&self, src: &[u8]) -> Option<Vec<u8>> {
        let n = self.uncompressed_length(src)?;
        if n > 1 << 28 {
            return None;
        }
        let mut out = vec![0u8; n + 1];
        let m = self.uncompress_into(src, &mut out[..n]).ok()?;
        out.truncate(m);
        Some(out)
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

    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

pub fn sizes() -> Vec<usize> {
    let mut v: Vec<usize> = (0..=40).collect();
    v.extend([63, 64, 65, 100, 255, 256, 270, 271, 300, 1000, 4096, 65535, 65536, 65537, 70000, 200_000, 1_500_000]);
    v
}

pub const KINDS: usize = 7;

/// Test data of several kinds: random, runs, short periods, text-like,
/// far repeats, mixed.
pub fn sample(rng: &mut Rng, size: usize, kind: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(size);
    match kind {
        0 => {
            while v.len() < size {
                v.push(rng.next() as u8);
            }
        }
        1 => {
            while v.len() < size {
                let b = rng.next() as u8;
                let n = 1 + rng.below(600);
                for _ in 0..n {
                    v.push(b);
                }
            }
        }
        2 => {
            while v.len() < size {
                let period = 1 + rng.below(20);
                let pat: Vec<u8> = (0..period).map(|_| rng.next() as u8).collect();
                let n = 1 + rng.below(300);
                for i in 0..n {
                    v.push(pat[i % period]);
                }
            }
        }
        3 => {
            let words: Vec<Vec<u8>> = (0..200)
                .map(|_| {
                    let n = 1 + rng.below(10);
                    (0..n).map(|_| b'a' + rng.below(26) as u8).collect()
                })
                .collect();
            while v.len() < size {
                v.extend_from_slice(&words[rng.below(words.len())]);
                v.push(b' ');
            }
        }
        4 => {
            // Repeats from far back, some beyond 64 KiB.
            while v.len() < size {
                if v.len() > 100 && rng.below(3) > 0 {
                    let back = 1 + rng.below(v.len().min(140_000));
                    let n = 4 + rng.below(100);
                    let from = v.len() - back;
                    for i in 0..n {
                        let b = v[from + i % back];
                        v.push(b);
                    }
                } else {
                    for _ in 0..1 + rng.below(40) {
                        v.push(rng.next() as u8);
                    }
                }
            }
        }
        5 => {
            // Few distinct bytes.
            while v.len() < size {
                v.push(b"ab"[(rng.next() % 2) as usize]);
            }
        }
        _ => {
            while v.len() < size {
                let k = rng.below(6);
                let n = 1 + rng.below(3000);
                let part = sample(rng, n, k);
                v.extend_from_slice(&part);
            }
        }
    }
    v.truncate(size);
    v
}

