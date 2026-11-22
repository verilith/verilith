#![allow(dead_code)]
#![allow(unsafe_op_in_unsafe_fn)]
use std::ffi::{c_char, c_int, c_void, CString};

unsafe extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

/// liblz4, under its Linux or macOS name (or VLZ4_LIBLZ4).
pub unsafe fn open_liblz4() -> *mut c_void {
    let mut names: Vec<String> = std::env::var("VLZ4_LIBLZ4").into_iter().collect();
    names.extend(
        ["liblz4.so.1", "liblz4.1.dylib", "/opt/homebrew/lib/liblz4.1.dylib", "/usr/local/lib/liblz4.1.dylib"]
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

pub unsafe fn sym(h: *mut c_void, n: &str) -> *mut c_void {
    let p = dlsym(h, CString::new(n).unwrap().as_ptr());
    assert!(!p.is_null(), "{n}");
    p
}

type CompressFast = unsafe extern "C" fn(*const u8, *mut u8, c_int, c_int, c_int) -> c_int;
type DecompressSafe = unsafe extern "C" fn(*const u8, *mut u8, c_int, c_int) -> c_int;
type Bound = unsafe extern "C" fn(c_int) -> c_int;

pub struct Lz4 {
    pub h: *mut c_void,
    compress_fast: CompressFast,
    decompress_safe: DecompressSafe,
    bound: Bound,
}

impl Lz4 {
    pub fn load() -> Option<Lz4> {
        unsafe {
            let h = open_liblz4();
            if h.is_null() {
                return None;
            }
            Some(Lz4 {
                h,
                compress_fast: std::mem::transmute(sym(h, "LZ4_compress_fast")),
                decompress_safe: std::mem::transmute(sym(h, "LZ4_decompress_safe")),
                bound: std::mem::transmute(sym(h, "LZ4_compressBound")),
            })
        }
    }

    pub fn bound(&self, n: usize) -> usize {
        unsafe { (self.bound)(n as c_int) as usize }
    }

    pub fn compress(&self, input: &[u8], accel: i32) -> Vec<u8> {
        let mut out = vec![0u8; self.bound(input.len())];
        let n = unsafe { (self.compress_fast)(input.as_ptr(), out.as_mut_ptr(), input.len() as c_int, out.len() as c_int, accel) };
        assert!(n > 0);
        out.truncate(n as usize);
        out
    }

    pub fn compress_into(&self, input: &[u8], out: &mut [u8]) -> usize {
        unsafe { (self.compress_fast)(input.as_ptr(), out.as_mut_ptr(), input.len() as c_int, out.len() as c_int, 1) as usize }
    }

    pub fn decompress_into(&self, src: &[u8], out: &mut [u8]) -> usize {
        unsafe { (self.decompress_safe)(src.as_ptr(), out.as_mut_ptr(), src.len() as c_int, out.len() as c_int) as usize }
    }

    pub fn decompress(&self, src: &[u8], cap: usize) -> Option<Vec<u8>> {
        // A dangling pointer is fine for liblz4 only with a capacity of 0;
        // keep one spare byte so the pointer is always real.
        let mut out = vec![0u8; cap + 1];
        let n = unsafe { (self.decompress_safe)(src.as_ptr(), out.as_mut_ptr(), src.len() as c_int, cap as c_int) };
        if n < 0 {
            None
        } else {
            out.truncate(n as usize);
            Some(out)
        }
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

/// Parses a block the way the format describes and says whether some
/// match breaks an end-of-block rule for an output buffer of `cap` bytes,
/// which is what liblz4 checks: a match must end at least 5 bytes before
/// the end of the buffer if it ends within 12 of it, the literals before
/// a match must end at least 12 bytes before the end of the buffer, and
/// at least 8 bytes of input must follow them.
pub fn breaks_end_rules(c: &[u8], _decoded: usize, cap: usize) -> bool {
    let n = c.len();
    let (mut i, mut op) = (0usize, 0usize);
    loop {
        if i >= n {
            return false;
        }
        let token = c[i];
        i += 1;
        let mut ll = (token >> 4) as usize;
        if ll == 15 {
            loop {
                if i >= n {
                    return false;
                }
                let b = c[i];
                i += 1;
                ll += b as usize;
                if b != 255 {
                    break;
                }
            }
        }
        let lit_end = i + ll;
        if lit_end >= n {
            return false;
        }
        // Not the last sequence.
        if op + ll + 12 > cap || lit_end + 8 > n {
            return true;
        }
        op += ll;
        i = lit_end + 2;
        let mut ml = (token & 15) as usize;
        if ml == 15 {
            loop {
                if i >= n {
                    return false;
                }
                let b = c[i];
                i += 1;
                ml += b as usize;
                if b != 255 {
                    break;
                }
            }
        }
        ml += 4;
        if op + ml + 12 > cap && op + ml + 5 > cap {
            return true;
        }
        op += ml;
    }
}

/// Whether some sequence of the block has offset 0.
pub fn has_zero_offset(c: &[u8]) -> bool {
    let n = c.len();
    let mut i = 0usize;
    loop {
        if i >= n {
            return false;
        }
        let token = c[i];
        i += 1;
        let mut ll = (token >> 4) as usize;
        if ll == 15 {
            loop {
                if i >= n {
                    return false;
                }
                let b = c[i];
                i += 1;
                ll += b as usize;
                if b != 255 {
                    break;
                }
            }
        }
        i += ll;
        if i + 2 > n {
            return false;
        }
        if c[i] == 0 && c[i + 1] == 0 {
            return true;
        }
        i += 2;
        if token & 15 == 15 {
            loop {
                if i >= n {
                    return false;
                }
                let b = c[i];
                i += 1;
                if b != 255 {
                    break;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// liblz4's frame API
// ---------------------------------------------------------------------------

#[repr(C)]
#[derive(Default, Clone, Copy)]
pub struct FrameInfo {
    pub block_size_id: c_int,
    pub block_mode: c_int,
    pub content_checksum: c_int,
    pub frame_type: c_int,
    pub content_size: u64,
    pub dict_id: u32,
    pub block_checksum: c_int,
}

#[repr(C)]
#[derive(Default, Clone, Copy)]
pub struct Preferences {
    pub frame_info: FrameInfo,
    pub compression_level: c_int,
    pub auto_flush: u32,
    pub favor_dec_speed: u32,
    pub reserved: [u32; 3],
}

type FBound = unsafe extern "C" fn(usize, *const Preferences) -> usize;
type FCompress = unsafe extern "C" fn(*mut u8, usize, *const u8, usize, *const Preferences) -> usize;
type FIsError = unsafe extern "C" fn(usize) -> u32;
type FCreateD = unsafe extern "C" fn(*mut *mut c_void, u32) -> usize;
type FFreeD = unsafe extern "C" fn(*mut c_void) -> usize;
type FDecompress = unsafe extern "C" fn(*mut c_void, *mut u8, *mut usize, *const u8, *mut usize, *const c_void) -> usize;

pub struct Lz4f {
    bound: FBound,
    compress: FCompress,
    is_error: FIsError,
    create_d: FCreateD,
    free_d: FFreeD,
    decompress: FDecompress,
}

impl Lz4f {
    pub fn load() -> Option<Lz4f> {
        unsafe {
            let h = open_liblz4();
            if h.is_null() {
                return None;
            }
            Some(Lz4f {
                bound: std::mem::transmute(sym(h, "LZ4F_compressFrameBound")),
                compress: std::mem::transmute(sym(h, "LZ4F_compressFrame")),
                is_error: std::mem::transmute(sym(h, "LZ4F_isError")),
                create_d: std::mem::transmute(sym(h, "LZ4F_createDecompressionContext")),
                free_d: std::mem::transmute(sym(h, "LZ4F_freeDecompressionContext")),
                decompress: std::mem::transmute(sym(h, "LZ4F_decompress")),
            })
        }
    }

    pub fn compress(&self, input: &[u8], p: &Preferences) -> Vec<u8> {
        unsafe {
            let mut out = vec![0u8; (self.bound)(input.len(), p)];
            let n = (self.compress)(out.as_mut_ptr(), out.len(), input.as_ptr(), input.len(), p);
            assert_eq!((self.is_error)(n), 0);
            out.truncate(n);
            out
        }
    }

    /// Decodes one frame with LZ4F_decompress, feeding `piece` bytes at a
    /// time. Gives the content and how much input the frame took, or
    /// `None` on an error or if the input ends before the frame does.
    pub fn decompress(&self, src: &[u8], piece: usize) -> Option<(Vec<u8>, usize)> {
        unsafe {
            let mut ctx = std::ptr::null_mut();
            assert_eq!((self.is_error)((self.create_d)(&mut ctx, 100)), 0);
            let mut out = Vec::new();
            let mut buf = vec![0u8; 70000];
            let mut pos = 0;
            let res = loop {
                let mut dn = buf.len();
                let mut sn = piece.min(src.len() - pos);
                let fed = sn;
                let r = (self.decompress)(ctx, buf.as_mut_ptr(), &mut dn, src.as_ptr().add(pos), &mut sn, std::ptr::null());
                if (self.is_error)(r) != 0 {
                    break None;
                }
                out.extend_from_slice(&buf[..dn]);
                pos += sn;
                if r == 0 {
                    break Some((out, pos));
                }
                if dn == 0 && sn == 0 && fed == 0 {
                    break None;
                }
            };
            (self.free_d)(ctx);
            res
        }
    }
}

/// Whether some compressed block of the frame has a sequence with offset
/// 0 (which liblz4 does not reject).
pub fn frame_has_zero_offset(c: &[u8]) -> bool {
    let Some(h) = verilith_lz4::frame::read_header(c, 0) else {
        return false;
    };
    let mut i = h.end;
    while i + 4 <= c.len() {
        let w = u32::from_le_bytes(c[i..i + 4].try_into().unwrap());
        let size = (w & 0x7fff_ffff) as usize;
        if size == 0 || i + 4 + size > c.len() {
            break;
        }
        if w >> 31 == 0 && has_zero_offset(&c[i + 4..i + 4 + size]) {
            return true;
        }
        i += 4 + size + if h.bsum { 4 } else { 0 };
    }
    false
}
