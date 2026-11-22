//! The decoding half of the TurboJPEG API (libjpeg-turbo's `turbojpeg.h`),
//! over the verified decoder. This file is not verified: it checks
//! arguments, calls `decode`, and copies the pixels out in the layout asked
//! for.
//!
//! Every function is exported as `vjpeg_<name>`; with the `turbojpeg-abi`
//! feature also under TurboJPEG's own name, so that a program written for
//! `turbojpeg.h` links against this library unchanged.
//!
//! What is here: `tj3Init`, `tj3InitVersion`, `tj3Destroy`, `tj3Set`, `tj3Get`,
//! `tj3DecompressHeader`, `tj3Decompress8`, `tj3GetErrorStr`,
//! `tj3GetErrorCode`, `tj3Alloc`, `tj3Free`, `tj3GetScalingFactors`,
//! `tj3SetScalingFactor`, and the older `tjInitDecompress`,
//! `tjDecompressHeader`, `tjDecompressHeader2`, `tjDecompressHeader3`,
//! `tjDecompress2`, `tjDestroy`, `tjGetErrorStr`, `tjGetErrorStr2`,
//! `tjGetErrorCode`, `tjAlloc`, `tjFree`, `tjGetScalingFactors`.
//!
//! Where it differs from TurboJPEG (README, "The TurboJPEG API"):
//! - the only scaling factor is 1/1, and there is no cropping;
//! - no YUV output, no 12- or 16-bit output, no ICC profile, no CMYK;
//! - a color image cannot be decoded to `TJPF_GRAY`;
//! - a damaged file that libjpeg-turbo decodes with a warning decodes here
//!   with no warning, so `TJPARAM_STOPONWARNING` has nothing to stop on;
//! - `TJPARAM_FASTUPSAMPLE` and `TJPARAM_FASTDCT` are accepted and ignored.
use crate::decode::{decode, decode_to, read_header, Header, Picture};
use crate::types::Error;
use core::ffi::{c_char, c_int, c_ulong, c_void};
use std::cell::RefCell;

extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
}

const ERR_LEN: usize = 200;

const TJINIT_DECOMPRESS: c_int = 1;
const TJINIT_TRANSFORM: c_int = 2;
const TJ_NUMINIT: c_int = 3;
/// `TURBOJPEG_VERSION_NUMBER` of 3.1 (what 3.2's own `tj3Init` passes) and of 3.2.
const API_3_1: c_int = 3_001_000;
const API_3_2: c_int = 3_002_000;

const TJSAMP_444: c_int = 0;
const TJSAMP_422: c_int = 1;
const TJSAMP_420: c_int = 2;
const TJSAMP_GRAY: c_int = 3;
const TJSAMP_440: c_int = 4;
const TJSAMP_411: c_int = 5;
const TJSAMP_441: c_int = 6;
const TJSAMP_410: c_int = 7;
const TJSAMP_24: c_int = 8;
const TJSAMP_UNKNOWN: c_int = -1;

const TJPF_GRAY: c_int = 6;
const TJPF_CMYK: c_int = 11;

const TJCS_RGB: c_int = 0;
const TJCS_YCBCR: c_int = 1;
const TJCS_GRAY: c_int = 2;

const TJERR_FATAL: c_int = 1;

const TJPARAM_STOPONWARNING: c_int = 0;
const TJPARAM_BOTTOMUP: c_int = 1;
const TJPARAM_NOREALLOC: c_int = 2;
const TJPARAM_SUBSAMP: c_int = 4;
const TJPARAM_JPEGWIDTH: c_int = 5;
const TJPARAM_JPEGHEIGHT: c_int = 6;
const TJPARAM_PRECISION: c_int = 7;
const TJPARAM_COLORSPACE: c_int = 8;
const TJPARAM_FASTUPSAMPLE: c_int = 9;
const TJPARAM_FASTDCT: c_int = 10;
const TJPARAM_PROGRESSIVE: c_int = 12;
const TJPARAM_SCANLIMIT: c_int = 13;
const TJPARAM_ARITHMETIC: c_int = 14;
const TJPARAM_LOSSLESS: c_int = 15;
const TJPARAM_LOSSLESSPSV: c_int = 16;
const TJPARAM_LOSSLESSPT: c_int = 17;
const TJPARAM_XDENSITY: c_int = 20;
const TJPARAM_YDENSITY: c_int = 21;
const TJPARAM_DENSITYUNITS: c_int = 22;
const TJPARAM_MAXMEMORY: c_int = 23;
const TJPARAM_MAXPIXELS: c_int = 24;
const TJPARAM_SAVEMARKERS: c_int = 25;

const TJFLAG_BOTTOMUP: c_int = 2;

/// Bytes per pixel of each `TJPF_*`.
const PIXEL_SIZE: [usize; 12] = [3, 3, 4, 4, 4, 4, 1, 4, 4, 4, 4, 4];
/// Where red, green and blue go in a pixel of each `TJPF_*`.
const RGB_AT: [[usize; 3]; 12] = [
    [0, 1, 2],
    [2, 1, 0],
    [0, 1, 2],
    [2, 1, 0],
    [3, 2, 1],
    [1, 2, 3],
    [0, 0, 0],
    [0, 1, 2],
    [2, 1, 0],
    [3, 2, 1],
    [1, 2, 3],
    [0, 0, 0],
];

/// A scaling factor, as `tjscalingfactor`.
#[repr(C)]
pub struct ScalingFactor {
    pub num: c_int,
    pub denom: c_int,
}

static UNITY: [ScalingFactor; 1] = [ScalingFactor { num: 1, denom: 1 }];

/// What a `tjhandle` points to.
pub struct Handle {
    init: c_int,
    /// The `turbojpeg.h` the caller was compiled with (`tj3InitVersion`).
    api_version: c_int,
    err: [u8; ERR_LEN],
    stop_on_warning: c_int,
    bottom_up: c_int,
    no_realloc: c_int,
    subsamp: c_int,
    jpeg_width: c_int,
    jpeg_height: c_int,
    precision: c_int,
    colorspace: c_int,
    fast_upsample: c_int,
    fast_dct: c_int,
    progressive: c_int,
    scan_limit: c_int,
    max_memory: c_int,
    max_pixels: c_int,
    save_markers: c_int,
}

thread_local! {
    /// The message `tjGetErrorStr` and a null handle report.
    static LAST: RefCell<[u8; ERR_LEN]> = const { RefCell::new(no_error()) };
}

const fn no_error() -> [u8; ERR_LEN] {
    let mut b = [0u8; ERR_LEN];
    let m = b"No error";
    let mut i = 0;
    while i < m.len() {
        b[i] = m[i];
        i += 1;
    }
    b
}

fn message(func: &str, msg: &str) -> [u8; ERR_LEN] {
    let mut b = [0u8; ERR_LEN];
    let text = [func.as_bytes(), b"(): ", msg.as_bytes()].concat();
    let n = text.len().min(ERR_LEN - 1);
    b[..n].copy_from_slice(&text[..n]);
    b
}

/// Records an error on the handle (if there is one) and for the thread.
unsafe fn fail(h: *mut Handle, func: &str, msg: &str) -> c_int {
    let b = message(func, msg);
    if !h.is_null() {
        (*h).err = b;
    }
    LAST.with(|l| *l.borrow_mut() = b);
    -1
}

fn error_text(e: Error) -> &'static str {
    match e {
        Error::Invalid => "Not a JPEG file, or one that is damaged or not supported",
        Error::OutOfMemory => "Memory allocation failure",
    }
}

fn subsamp_of(h: &Header, api_version: c_int) -> c_int {
    if h.nc == 1 {
        return TJSAMP_GRAY;
    }
    if h.hs[1] != 1 || h.vs[1] != 1 || h.hs[2] != 1 || h.vs[2] != 1 {
        // TurboJPEG also names two unusual spellings of 4:2:2 and 4:4:0.
        if h.hs[0] == 2 && h.vs[0] == 2 && h.hs[1] == h.hs[2] && h.vs[1] == h.vs[2] {
            if h.hs[1] == 1 && h.vs[1] == 2 {
                return TJSAMP_422;
            }
            if h.hs[1] == 2 && h.vs[1] == 1 {
                return TJSAMP_440;
            }
        }
        return TJSAMP_UNKNOWN;
    }
    match (h.hs[0], h.vs[0]) {
        (1, 1) => TJSAMP_444,
        (2, 1) => TJSAMP_422,
        (2, 2) => TJSAMP_420,
        (1, 2) => TJSAMP_440,
        (4, 1) => TJSAMP_411,
        (1, 4) => TJSAMP_441,
        // TurboJPEG 3.2 names these two, for callers compiled against it.
        (4, 2) if api_version >= API_3_2 => TJSAMP_410,
        (2, 4) if api_version >= API_3_2 => TJSAMP_24,
        _ => TJSAMP_UNKNOWN,
    }
}

unsafe fn input<'a>(buf: *const u8, len: usize) -> &'a [u8] {
    core::slice::from_raw_parts(buf, len)
}

/// Reads the header into the handle's parameters.
unsafe fn header(h: *mut Handle, func: &str, buf: *const u8, len: usize) -> c_int {
    if h.is_null() {
        return fail(h, func, "Invalid handle");
    }
    if (*h).init != TJINIT_DECOMPRESS && (*h).init != TJINIT_TRANSFORM {
        return fail(h, func, "Instance has not been initialized for decompression");
    }
    if buf.is_null() || len == 0 {
        return fail(h, func, "Invalid argument");
    }
    match read_header(input(buf, len)) {
        Ok(hd) => {
            let this = &mut *h;
            this.subsamp = subsamp_of(&hd, this.api_version);
            this.jpeg_width = hd.w as c_int;
            this.jpeg_height = hd.h as c_int;
            this.precision = 8;
            this.colorspace = match hd.color {
                0 => TJCS_GRAY,
                1 => TJCS_YCBCR,
                _ => TJCS_RGB,
            };
            this.progressive = hd.prog as c_int;
            0
        }
        Err(e) => fail(h, func, error_text(e)),
    }
}

/// Decodes into `dst`, `pitch` bytes per row (0 for no padding).
unsafe fn decompress(
    h: *mut Handle,
    func: &str,
    buf: *const u8,
    len: usize,
    dst: *mut u8,
    pitch: c_int,
    pf: c_int,
    want: Option<(c_int, c_int)>,
) -> c_int {
    if h.is_null() {
        return fail(h, func, "Invalid handle");
    }
    if (*h).init != TJINIT_DECOMPRESS && (*h).init != TJINIT_TRANSFORM {
        return fail(h, func, "Instance has not been initialized for decompression");
    }
    if buf.is_null() || len == 0 || dst.is_null() || pitch < 0 || pf < 0 || pf > TJPF_CMYK {
        return fail(h, func, "Invalid argument");
    }
    if pf == TJPF_CMYK {
        return fail(h, func, "CMYK output is not supported");
    }
    if header(h, func, buf, len) != 0 {
        return -1;
    }
    let (w, ht) = ((*h).jpeg_width as usize, (*h).jpeg_height as usize);
    if let Some((ww, wh)) = want {
        if (ww != 0 && ww as usize != w) || (wh != 0 && wh as usize != ht) {
            return fail(h, func, "Could not scale down to desired image dimensions");
        }
    }
    if (*h).max_pixels > 0 && (w as u64) * (ht as u64) > (*h).max_pixels as u64 {
        return fail(h, func, "Image is too large");
    }
    if pf == TJPF_GRAY && (*h).colorspace != TJCS_GRAY {
        return fail(h, func, "Decoding a color image to grayscale is not supported");
    }
    let ps = PIXEL_SIZE[pf as usize];
    let pitch = if pitch == 0 { w * ps } else { pitch as usize };
    if pitch < w * ps {
        return fail(h, func, "Invalid argument");
    }
    // When the caller's layout is the decoder's own (rows top to bottom
    // with no padding, gray or red-green-blue bytes), decode straight into
    // the caller's buffer. `decode_to` writes nothing unless the buffer is
    // exactly the picture's size.
    let jnc: usize = if (*h).colorspace == TJCS_GRAY { 1 } else { 3 };
    if (*h).bottom_up == 0 && pitch == w * ps && ps == jnc && (ps == 1 || RGB_AT[pf as usize] == [0, 1, 2]) {
        if let Some(n) = pitch.checked_mul(ht) {
            let out = core::slice::from_raw_parts_mut(dst, n);
            match decode_to(input(buf, len), out) {
                Ok(Some(_)) => return 0,
                Ok(None) => {}
                Err(e) => return fail(h, func, error_text(e)),
            }
        }
    }
    let Picture { w: pw, h: ph, nc, px } = match decode(input(buf, len)) {
        Ok(p) => p,
        Err(e) => return fail(h, func, error_text(e)),
    };
    let (w, ht, nc) = (pw as usize, ph as usize, nc as usize);
    let at = RGB_AT[pf as usize];
    for y in 0..ht {
        let src = &px[y * w * nc..(y + 1) * w * nc];
        let row = if (*h).bottom_up != 0 { ht - 1 - y } else { y };
        // Only the pixels are written: the caller's row padding is left alone.
        let out = core::slice::from_raw_parts_mut(dst.add(row * pitch), w * ps);
        if ps == 1 {
            out.copy_from_slice(src);
        } else if ps == 3 && nc == 3 && at[0] == 0 {
            out.copy_from_slice(src);
        } else {
            for (o, s) in out.chunks_exact_mut(ps).zip(src.chunks_exact(nc)) {
                if ps == 4 {
                    o[0] = 0xFF;
                    o[3] = 0xFF;
                }
                if nc == 3 {
                    o[at[0]] = s[0];
                    o[at[1]] = s[1];
                    o[at[2]] = s[2];
                } else {
                    o[at[0]] = s[0];
                    o[at[1]] = s[0];
                    o[at[2]] = s[0];
                }
            }
        }
    }
    0
}

/// `tj3Init`, as a caller compiled against TurboJPEG 3.1 or earlier calls
/// it. Since 3.2 `turbojpeg.h` defines `tj3Init` as `tj3InitVersion` with
/// its own version number.
#[no_mangle]
pub extern "C" fn vjpeg_tj3Init(init_type: c_int) -> *mut Handle {
    vjpeg_tj3InitVersion(init_type, API_3_1)
}

/// `tj3InitVersion` (TurboJPEG 3.2). Only decompression is here:
/// `TJINIT_COMPRESS` gives null. A `TJINIT_TRANSFORM` handle can decompress,
/// as TurboJPEG's can. `api_version` is the `TURBOJPEG_VERSION_NUMBER` of
/// the caller's header: from 3.2 on, 4:1:0 and 2:4 images are reported as
/// `TJSAMP_410` and `TJSAMP_24`, which earlier headers do not have.
#[no_mangle]
pub extern "C" fn vjpeg_tj3InitVersion(init_type: c_int, api_version: c_int) -> *mut Handle {
    if !(0..TJ_NUMINIT).contains(&init_type) || !(1_000_000..=999_999_999).contains(&api_version) {
        unsafe {
            fail(core::ptr::null_mut(), "tj3Init", "Invalid argument");
        }
        return core::ptr::null_mut();
    }
    if init_type != TJINIT_DECOMPRESS && init_type != TJINIT_TRANSFORM {
        unsafe {
            fail(core::ptr::null_mut(), "tj3Init", "Only decompression is supported");
        }
        return core::ptr::null_mut();
    }
    Box::into_raw(Box::new(Handle {
        init: init_type,
        api_version,
        err: no_error(),
        stop_on_warning: 0,
        bottom_up: 0,
        no_realloc: 0,
        subsamp: TJSAMP_UNKNOWN,
        jpeg_width: -1,
        jpeg_height: -1,
        precision: 8,
        colorspace: -1,
        fast_upsample: 0,
        fast_dct: 0,
        progressive: 0,
        scan_limit: 0,
        max_memory: 0,
        max_pixels: 0,
        save_markers: 2,
    }))
}

/// `tj3Destroy`.
///
/// # Safety
/// `h` must be null or a handle from `tj3Init` not yet destroyed.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3Destroy(h: *mut Handle) {
    if !h.is_null() {
        drop(Box::from_raw(h));
    }
}

/// `tj3GetErrorStr`: the last error on this handle, or on this thread if
/// the handle is null.
///
/// # Safety
/// `h` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3GetErrorStr(h: *mut Handle) -> *mut c_char {
    if h.is_null() {
        LAST.with(|l| l.as_ptr() as *mut c_char)
    } else {
        (*h).err.as_mut_ptr() as *mut c_char
    }
}

/// `tj3GetErrorCode`: always `TJERR_FATAL`, as this decoder has no warnings.
///
/// # Safety
/// `h` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3GetErrorCode(_h: *mut Handle) -> c_int {
    TJERR_FATAL
}

/// `tj3Set`.
///
/// # Safety
/// `h` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3Set(h: *mut Handle, param: c_int, value: c_int) -> c_int {
    const F: &str = "tj3Set";
    if h.is_null() {
        return fail(h, F, "Invalid handle");
    }
    let this = &mut *h;
    let flag = |v: c_int| (0..=1).contains(&v);
    match param {
        TJPARAM_STOPONWARNING if flag(value) => this.stop_on_warning = value,
        TJPARAM_BOTTOMUP if flag(value) => this.bottom_up = value,
        TJPARAM_NOREALLOC if flag(value) => this.no_realloc = value,
        TJPARAM_FASTUPSAMPLE if flag(value) => this.fast_upsample = value,
        TJPARAM_FASTDCT if flag(value) => this.fast_dct = value,
        TJPARAM_SCANLIMIT if value >= 0 => this.scan_limit = value,
        TJPARAM_MAXMEMORY if value >= 0 => this.max_memory = value,
        TJPARAM_MAXPIXELS if value >= 0 => this.max_pixels = value,
        TJPARAM_SAVEMARKERS if (0..=4).contains(&value) => this.save_markers = value,
        TJPARAM_STOPONWARNING | TJPARAM_BOTTOMUP | TJPARAM_NOREALLOC | TJPARAM_FASTUPSAMPLE | TJPARAM_FASTDCT
        | TJPARAM_SCANLIMIT | TJPARAM_MAXMEMORY | TJPARAM_MAXPIXELS | TJPARAM_SAVEMARKERS => {
            return fail(h, F, "Parameter value out of range")
        }
        TJPARAM_SUBSAMP | TJPARAM_JPEGWIDTH | TJPARAM_JPEGHEIGHT | TJPARAM_PRECISION | TJPARAM_COLORSPACE
        | TJPARAM_PROGRESSIVE | TJPARAM_ARITHMETIC | TJPARAM_LOSSLESS | TJPARAM_LOSSLESSPSV | TJPARAM_LOSSLESSPT
        | TJPARAM_XDENSITY | TJPARAM_YDENSITY | TJPARAM_DENSITYUNITS => {
            return fail(h, F, "Parameter is not applicable to decompression instances.")
        }
        _ => return fail(h, F, "Invalid parameter"),
    }
    0
}

/// `tj3Get`.
///
/// # Safety
/// `h` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3Get(h: *mut Handle, param: c_int) -> c_int {
    if h.is_null() {
        return -1;
    }
    let this = &*h;
    match param {
        TJPARAM_STOPONWARNING => this.stop_on_warning,
        TJPARAM_BOTTOMUP => this.bottom_up,
        TJPARAM_NOREALLOC => this.no_realloc,
        TJPARAM_SUBSAMP => this.subsamp,
        TJPARAM_JPEGWIDTH => this.jpeg_width,
        TJPARAM_JPEGHEIGHT => this.jpeg_height,
        TJPARAM_PRECISION => this.precision,
        TJPARAM_COLORSPACE => this.colorspace,
        TJPARAM_FASTUPSAMPLE => this.fast_upsample,
        TJPARAM_FASTDCT => this.fast_dct,
        TJPARAM_PROGRESSIVE => this.progressive,
        TJPARAM_SCANLIMIT => this.scan_limit,
        TJPARAM_ARITHMETIC | TJPARAM_LOSSLESS => 0,
        TJPARAM_MAXMEMORY => this.max_memory,
        TJPARAM_MAXPIXELS => this.max_pixels,
        TJPARAM_SAVEMARKERS => this.save_markers,
        _ => -1,
    }
}

/// `tj3Alloc`: C's `malloc`.
#[no_mangle]
pub extern "C" fn vjpeg_tj3Alloc(bytes: usize) -> *mut c_void {
    unsafe { malloc(bytes) }
}

/// `tj3Free`: C's `free`.
///
/// # Safety
/// `p` must be null or a buffer from `tj3Alloc`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3Free(p: *mut c_void) {
    free(p)
}

/// `tj3DecompressHeader`.
///
/// # Safety
/// `h` must be null or a live handle, and `buf` point to `len` bytes.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3DecompressHeader(h: *mut Handle, buf: *const u8, len: usize) -> c_int {
    header(h, "tj3DecompressHeader", buf, len)
}

/// `tj3GetScalingFactors`: the one factor here is 1/1.
///
/// # Safety
/// `n` must be null or point to a writable `int`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3GetScalingFactors(n: *mut c_int) -> *const ScalingFactor {
    if n.is_null() {
        fail(core::ptr::null_mut(), "tj3GetScalingFactors", "Invalid argument");
        return core::ptr::null();
    }
    *n = 1;
    UNITY.as_ptr()
}

/// `tj3SetScalingFactor`: accepts 1/1 only.
///
/// # Safety
/// `h` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3SetScalingFactor(h: *mut Handle, f: ScalingFactor) -> c_int {
    if h.is_null() {
        return fail(h, "tj3SetScalingFactor", "Invalid handle");
    }
    if f.num != f.denom || f.num < 1 {
        return fail(h, "tj3SetScalingFactor", "Unsupported scaling factor");
    }
    0
}

/// `tj3Decompress8`.
///
/// # Safety
/// `h` must be null or a live handle, `buf` point to `len` bytes, and `dst`
/// to a buffer of `pitch` bytes (or the image's width in pixels, if `pitch`
/// is 0) times the image's height.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tj3Decompress8(
    h: *mut Handle,
    buf: *const u8,
    len: usize,
    dst: *mut u8,
    pitch: c_int,
    pf: c_int,
) -> c_int {
    decompress(h, "tj3Decompress8", buf, len, dst, pitch, pf, None)
}

/// `tjInitDecompress`.
#[no_mangle]
pub extern "C" fn vjpeg_tjInitDecompress() -> *mut Handle {
    vjpeg_tj3Init(TJINIT_DECOMPRESS)
}

/// `tjDestroy`.
///
/// # Safety
/// As `tj3Destroy`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjDestroy(h: *mut Handle) -> c_int {
    if h.is_null() {
        return fail(h, "tjDestroy", "Invalid handle");
    }
    vjpeg_tj3Destroy(h);
    0
}

/// `tjGetErrorStr`: the last error on this thread.
#[no_mangle]
pub extern "C" fn vjpeg_tjGetErrorStr() -> *mut c_char {
    LAST.with(|l| l.as_ptr() as *mut c_char)
}

/// `tjGetErrorStr2`.
///
/// # Safety
/// As `tj3GetErrorStr`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjGetErrorStr2(h: *mut Handle) -> *mut c_char {
    vjpeg_tj3GetErrorStr(h)
}

/// `tjGetErrorCode`.
///
/// # Safety
/// As `tj3GetErrorCode`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjGetErrorCode(h: *mut Handle) -> c_int {
    vjpeg_tj3GetErrorCode(h)
}

/// `tjAlloc`.
#[no_mangle]
pub extern "C" fn vjpeg_tjAlloc(bytes: c_int) -> *mut u8 {
    if bytes < 0 {
        return core::ptr::null_mut();
    }
    vjpeg_tj3Alloc(bytes as usize) as *mut u8
}

/// `tjFree`.
///
/// # Safety
/// As `tj3Free`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjFree(p: *mut u8) {
    vjpeg_tj3Free(p as *mut c_void)
}

/// `tjGetScalingFactors`.
///
/// # Safety
/// As `tj3GetScalingFactors`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjGetScalingFactors(n: *mut c_int) -> *const ScalingFactor {
    vjpeg_tj3GetScalingFactors(n)
}

/// `tjDecompressHeader3`.
///
/// # Safety
/// `h` must be null or a live handle, `buf` point to `len` bytes, and the
/// four outputs be null or writable.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjDecompressHeader3(
    h: *mut Handle,
    buf: *const u8,
    len: c_ulong,
    width: *mut c_int,
    height: *mut c_int,
    subsamp: *mut c_int,
    colorspace: *mut c_int,
) -> c_int {
    const F: &str = "tjDecompressHeader3";
    if h.is_null() {
        return fail(h, F, "Invalid handle");
    }
    if width.is_null() || height.is_null() || subsamp.is_null() || colorspace.is_null() {
        return fail(h, F, "Invalid argument");
    }
    let r = header(h, F, buf, len as usize);
    if r != 0 {
        return r;
    }
    *width = (*h).jpeg_width;
    *height = (*h).jpeg_height;
    *subsamp = (*h).subsamp;
    *colorspace = (*h).colorspace;
    if (*h).subsamp == TJSAMP_UNKNOWN {
        return fail(h, F, "Could not determine subsampling level of JPEG image");
    }
    0
}

/// `tjDecompressHeader2`.
///
/// # Safety
/// As `tjDecompressHeader3`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjDecompressHeader2(
    h: *mut Handle,
    buf: *mut u8,
    len: c_ulong,
    width: *mut c_int,
    height: *mut c_int,
    subsamp: *mut c_int,
) -> c_int {
    let mut cs: c_int = 0;
    vjpeg_tjDecompressHeader3(h, buf, len, width, height, subsamp, &mut cs)
}

/// `tjDecompressHeader`.
///
/// # Safety
/// As `tjDecompressHeader3`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjDecompressHeader(
    h: *mut Handle,
    buf: *mut u8,
    len: c_ulong,
    width: *mut c_int,
    height: *mut c_int,
) -> c_int {
    let mut ss: c_int = 0;
    vjpeg_tjDecompressHeader2(h, buf, len, width, height, &mut ss)
}

/// `tjDecompress2`. `width` and `height` must be 0 or the image's own, as
/// there is no scaling. Of the flags, `TJFLAG_BOTTOMUP` is honored and the
/// rest are ignored.
///
/// # Safety
/// As `tj3Decompress8`.
#[no_mangle]
pub unsafe extern "C" fn vjpeg_tjDecompress2(
    h: *mut Handle,
    buf: *const u8,
    len: c_ulong,
    dst: *mut u8,
    width: c_int,
    pitch: c_int,
    height: c_int,
    pf: c_int,
    flags: c_int,
) -> c_int {
    const F: &str = "tjDecompress2";
    if h.is_null() {
        return fail(h, F, "Invalid handle");
    }
    if width < 0 || height < 0 {
        return fail(h, F, "Invalid argument");
    }
    (*h).bottom_up = (flags & TJFLAG_BOTTOMUP != 0) as c_int;
    decompress(h, F, buf, len as usize, dst, pitch, pf, Some((width, height)))
}

#[cfg(feature = "turbojpeg-abi")]
mod abi {
    use super::*;

    #[no_mangle]
    pub extern "C" fn tj3Init(init_type: c_int) -> *mut Handle {
        vjpeg_tj3Init(init_type)
    }
    #[no_mangle]
    pub extern "C" fn tj3InitVersion(init_type: c_int, api_version: c_int) -> *mut Handle {
        vjpeg_tj3InitVersion(init_type, api_version)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3Destroy(h: *mut Handle) {
        vjpeg_tj3Destroy(h)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3GetErrorStr(h: *mut Handle) -> *mut c_char {
        vjpeg_tj3GetErrorStr(h)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3GetErrorCode(h: *mut Handle) -> c_int {
        vjpeg_tj3GetErrorCode(h)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3Set(h: *mut Handle, param: c_int, value: c_int) -> c_int {
        vjpeg_tj3Set(h, param, value)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3Get(h: *mut Handle, param: c_int) -> c_int {
        vjpeg_tj3Get(h, param)
    }
    #[no_mangle]
    pub extern "C" fn tj3Alloc(bytes: usize) -> *mut c_void {
        vjpeg_tj3Alloc(bytes)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3Free(p: *mut c_void) {
        vjpeg_tj3Free(p)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3DecompressHeader(h: *mut Handle, buf: *const u8, len: usize) -> c_int {
        vjpeg_tj3DecompressHeader(h, buf, len)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3GetScalingFactors(n: *mut c_int) -> *const ScalingFactor {
        vjpeg_tj3GetScalingFactors(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3SetScalingFactor(h: *mut Handle, f: ScalingFactor) -> c_int {
        vjpeg_tj3SetScalingFactor(h, f)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tj3Decompress8(
        h: *mut Handle,
        buf: *const u8,
        len: usize,
        dst: *mut u8,
        pitch: c_int,
        pf: c_int,
    ) -> c_int {
        vjpeg_tj3Decompress8(h, buf, len, dst, pitch, pf)
    }
    #[no_mangle]
    pub extern "C" fn tjInitDecompress() -> *mut Handle {
        vjpeg_tjInitDecompress()
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjDestroy(h: *mut Handle) -> c_int {
        vjpeg_tjDestroy(h)
    }
    #[no_mangle]
    pub extern "C" fn tjGetErrorStr() -> *mut c_char {
        vjpeg_tjGetErrorStr()
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjGetErrorStr2(h: *mut Handle) -> *mut c_char {
        vjpeg_tjGetErrorStr2(h)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjGetErrorCode(h: *mut Handle) -> c_int {
        vjpeg_tjGetErrorCode(h)
    }
    #[no_mangle]
    pub extern "C" fn tjAlloc(bytes: c_int) -> *mut u8 {
        vjpeg_tjAlloc(bytes)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjFree(p: *mut u8) {
        vjpeg_tjFree(p)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjGetScalingFactors(n: *mut c_int) -> *const ScalingFactor {
        vjpeg_tjGetScalingFactors(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjDecompressHeader3(
        h: *mut Handle,
        buf: *const u8,
        len: c_ulong,
        width: *mut c_int,
        height: *mut c_int,
        subsamp: *mut c_int,
        colorspace: *mut c_int,
    ) -> c_int {
        vjpeg_tjDecompressHeader3(h, buf, len, width, height, subsamp, colorspace)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjDecompressHeader2(
        h: *mut Handle,
        buf: *mut u8,
        len: c_ulong,
        width: *mut c_int,
        height: *mut c_int,
        subsamp: *mut c_int,
    ) -> c_int {
        vjpeg_tjDecompressHeader2(h, buf, len, width, height, subsamp)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjDecompressHeader(
        h: *mut Handle,
        buf: *mut u8,
        len: c_ulong,
        width: *mut c_int,
        height: *mut c_int,
    ) -> c_int {
        vjpeg_tjDecompressHeader(h, buf, len, width, height)
    }
    #[no_mangle]
    pub unsafe extern "C" fn tjDecompress2(
        h: *mut Handle,
        buf: *const u8,
        len: c_ulong,
        dst: *mut u8,
        width: c_int,
        pitch: c_int,
        height: c_int,
        pf: c_int,
        flags: c_int,
    ) -> c_int {
        vjpeg_tjDecompress2(h, buf, len, dst, width, pitch, height, pf, flags)
    }
}
