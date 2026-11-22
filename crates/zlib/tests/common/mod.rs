//! Reference zlib (the system libz) through its C API, and test inputs.
#![allow(dead_code)]
use std::os::raw::{c_char, c_int, c_uint, c_ulong, c_void};

#[repr(C)]
pub struct ZStream {
    pub next_in: *const u8,
    pub avail_in: c_uint,
    pub total_in: c_ulong,
    pub next_out: *mut u8,
    pub avail_out: c_uint,
    pub total_out: c_ulong,
    pub msg: *const c_char,
    pub state: *mut c_void,
    pub zalloc: *const c_void,
    pub zfree: *const c_void,
    pub opaque: *mut c_void,
    pub data_type: c_int,
    pub adler: c_ulong,
    pub reserved: c_ulong,
}

#[link(name = "z")]
extern "C" {
    fn zlibVersion() -> *const c_char;
    fn deflateInit2_(s: *mut ZStream, level: c_int, method: c_int, wbits: c_int, mem: c_int, strategy: c_int, ver: *const c_char, size: c_int) -> c_int;
    fn deflate(s: *mut ZStream, flush: c_int) -> c_int;
    fn deflateEnd(s: *mut ZStream) -> c_int;
    fn inflateInit2_(s: *mut ZStream, wbits: c_int, ver: *const c_char, size: c_int) -> c_int;
    fn inflate(s: *mut ZStream, flush: c_int) -> c_int;
    fn inflateEnd(s: *mut ZStream) -> c_int;
    fn deflateSetDictionary(s: *mut ZStream, d: *const u8, n: c_uint) -> c_int;
    fn deflateSetHeader(s: *mut ZStream, h: *mut verilith_zlib::capi::GzHeader) -> c_int;
    pub fn inflateSetDictionary(s: *mut ZStream, d: *const u8, n: c_uint) -> c_int;
    pub fn inflateGetDictionary(s: *mut ZStream, d: *mut u8, n: *mut c_uint) -> c_int;
    pub fn inflateSync(s: *mut ZStream) -> c_int;
    pub fn adler32_combine(a: c_ulong, b: c_ulong, n: std::os::raw::c_long) -> c_ulong;
    pub fn crc32_combine(a: c_ulong, b: c_ulong, n: std::os::raw::c_long) -> c_ulong;
    pub fn crc32_combine_gen(n: std::os::raw::c_long) -> c_ulong;
    pub fn crc32_combine_op(a: c_ulong, b: c_ulong, op: c_ulong) -> c_ulong;
    pub fn get_crc_table() -> *const ZCrc;
}

/// The system zlib's `z_crc_t`. Upstream zlib's zconf.h makes it a 32-bit
/// `unsigned int`; Apple's SDK zconf.h makes it `unsigned long` (64 bits).
#[cfg(target_os = "macos")]
pub type ZCrc = c_ulong;
#[cfg(not(target_os = "macos"))]
pub type ZCrc = u32;

/// Starts a reference zlib inflate stream.
pub unsafe fn zinflate_init(s: *mut ZStream, wbits: i32) {
    assert_eq!(inflateInit2_(s, wbits, zlibVersion(), std::mem::size_of::<ZStream>() as c_int), 0);
}

/// Runs a reference zlib `inflate` on the stream with the given buffers;
/// returns the result and the input used and output made.
pub unsafe fn zinflate_step(s: *mut ZStream, input: &[u8], out: &mut [u8]) -> (c_int, usize, usize) {
    (*s).next_in = input.as_ptr();
    (*s).avail_in = input.len() as c_uint;
    (*s).next_out = out.as_mut_ptr();
    (*s).avail_out = out.len() as c_uint;
    let r = inflate(s, 0);
    (r, input.len() - (*s).avail_in as usize, out.len() - (*s).avail_out as usize)
}

pub unsafe fn zinflate_end(s: *mut ZStream) {
    inflateEnd(s);
}

fn zeroed() -> ZStream {
    unsafe { std::mem::zeroed() }
}

/// Compresses with zlib. `wbits`: 8..15 zlib, -8..-15 raw, 24..31 gzip.
/// `flush_every` > 0 inserts a full flush (an empty stored block) that often.
pub fn compress(data: &[u8], level: i32, wbits: i32, strategy: i32, flush_every: usize) -> Vec<u8> {
    compress_ex(data, level, wbits, strategy, flush_every, None, std::ptr::null_mut())
}

/// `compress` with a preset dictionary and, for gzip, a header to write.
pub fn compress_ex(
    data: &[u8],
    level: i32,
    wbits: i32,
    strategy: i32,
    flush_every: usize,
    dict: Option<&[u8]>,
    head: *mut verilith_zlib::capi::GzHeader,
) -> Vec<u8> {
    unsafe {
        let mut s = zeroed();
        assert_eq!(deflateInit2_(&mut s, level, 8, wbits, 8, strategy, zlibVersion(), std::mem::size_of::<ZStream>() as c_int), 0);
        if let Some(d) = dict {
            assert_eq!(deflateSetDictionary(&mut s, d.as_ptr(), d.len() as c_uint), 0);
        }
        if !head.is_null() {
            assert_eq!(deflateSetHeader(&mut s, head), 0);
        }
        let mut out = vec![0u8; data.len() + data.len() / 8 + 1024];
        let mut op = 0;
        let mut ip = 0;
        loop {
            let chunk = if flush_every > 0 { flush_every.min(data.len() - ip) } else { data.len() - ip };
            let last = ip + chunk == data.len();
            s.next_in = data.as_ptr().add(ip);
            s.avail_in = chunk as c_uint;
            ip += chunk;
            loop {
                if out.len() - op < 64 {
                    out.resize(out.len() * 2, 0);
                }
                s.next_out = out.as_mut_ptr().add(op);
                s.avail_out = (out.len() - op) as c_uint;
                let r = deflate(&mut s, if last { 4 } else { 3 });
                op = out.len() - s.avail_out as usize;
                if last && r == 1 {
                    deflateEnd(&mut s);
                    out.truncate(op);
                    return out;
                }
                if !last && s.avail_out > 0 {
                    break;
                }
            }
        }
    }
}

/// Decompresses with zlib in one call, the way `uncompress` does. Returns
/// the output and the input bytes used, or None if zlib rejects the input.
pub fn zinflate(data: &[u8], wbits: i32) -> Option<(Vec<u8>, usize)> {
    unsafe {
        let mut s = zeroed();
        assert_eq!(inflateInit2_(&mut s, wbits, zlibVersion(), std::mem::size_of::<ZStream>() as c_int), 0);
        let mut out = vec![0u8; data.len() * 8 + 4096];
        s.next_in = data.as_ptr();
        s.avail_in = data.len() as c_uint;
        let mut op = 0;
        loop {
            s.next_out = out.as_mut_ptr().add(op);
            s.avail_out = (out.len() - op) as c_uint;
            let r = inflate(&mut s, 0);
            op = out.len() - s.avail_out as usize;
            if r == 1 {
                let used = data.len() - s.avail_in as usize;
                inflateEnd(&mut s);
                out.truncate(op);
                return Some((out, used));
            }
            if r == 0 && s.avail_out == 0 {
                out.resize(out.len() * 2, 0);
                continue;
            }
            inflateEnd(&mut s);
            return None;
        }
    }
}

/// A small deterministic PRNG.
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Text-like data: words from a small vocabulary with skewed frequencies.
pub fn text(rng: &mut Rng, n: usize) -> Vec<u8> {
    let words: Vec<&[u8]> = b"the of and a to in is you that it he was for on are as with his they I at be this have from or one had by word but not what all were we when your can said there use an each which she do how their if will up other about out many then them these so some her would make like him into time has look two more write go see number no way could people my than first water been call who oil its now find long down day did get come made may part"
        .split(|&c| c == b' ')
        .collect();
    let mut out = Vec::with_capacity(n + 16);
    while out.len() < n {
        let i = (rng.below(words.len() as u64) * rng.below(words.len() as u64) / words.len() as u64) as usize;
        out.extend_from_slice(words[i]);
        out.push(if rng.below(12) == 0 { b'\n' } else { b' ' });
    }
    out.truncate(n);
    out
}

/// A mix of inputs that exercise every block type and code shape.
pub fn corpus() -> Vec<Vec<u8>> {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let mut v: Vec<Vec<u8>> = Vec::new();
    v.push(Vec::new());
    v.push(b"a".to_vec());
    v.push(b"hello, hello, hello world".to_vec());
    v.push(vec![0u8; 100_000]);
    v.push((0..70_000).map(|i| (i % 7) as u8).collect());
    v.push((0..50_000).map(|_| rng.next() as u8).collect());
    v.push((0..50_000).map(|_| (rng.below(4) * 60) as u8).collect());
    v.push(text(&mut rng, 300_000));
    v.push(text(&mut rng, 5_000));
    // Rust source files from this crate, if present.
    for p in ["src/inflate.rs", "src/spec.rs", "src/crc_tables.rs"] {
        if let Ok(b) = std::fs::read(p) {
            v.push(b);
        }
    }
    v
}
