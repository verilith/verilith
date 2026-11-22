//! The libwebp-compatible API: a safe Rust API, and C functions with
//! libwebp's signatures and struct layouts.
//!
//! This file is trusted glue, not verified. It calls the verified decoder
//! (`container::webp_decode_exec`), converts its ARGB pixels to the layout
//! the caller asked for, in safe Rust over slices, and turns the caller's
//! pointers into slices at the C boundary. The C functions are exported as
//! `vwebp_*`; with the `webp-abi` feature also under libwebp's names, so
//! vwebp can replace libwebp's decoder at link time.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::container::{header_exec, pad_exec, parse_headers_exec, webp_decode_exec, ParsedX};
use crate::lossy::{decode_lossy, decode_lossy_planes, lossy_layout, LossyPlanes};
use crate::vp8yuv::{planes_to_argb, planes_to_bytes};
use crate::pixels::Error;
use core::ffi::{c_int, c_void};

/// libwebp's `WEBP_DECODER_ABI_VERSION`, whose major byte callers check.
pub const WEBP_DECODER_ABI_VERSION: c_int = 0x0210;
/// The libwebp version whose API this implements.
pub const LIBWEBP_VERSION: c_int = 0x01_06_00;

/// `VP8StatusCode`.
pub type VP8StatusCode = c_int;
pub const VP8_STATUS_OK: c_int = 0;
pub const VP8_STATUS_OUT_OF_MEMORY: c_int = 1;
pub const VP8_STATUS_INVALID_PARAM: c_int = 2;
pub const VP8_STATUS_BITSTREAM_ERROR: c_int = 3;
pub const VP8_STATUS_UNSUPPORTED_FEATURE: c_int = 4;
pub const VP8_STATUS_NOT_ENOUGH_DATA: c_int = 7;

/// `WEBP_CSP_MODE`: the output layouts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    RGB = 0,
    RGBA = 1,
    BGR = 2,
    BGRA = 3,
    ARGB = 4,
    RGBA4444 = 5,
    RGB565 = 6,
    PremulRGBA = 7,
    PremulBGRA = 8,
    PremulARGB = 9,
    PremulRGBA4444 = 10,
}

impl Mode {
    pub fn from_c(m: c_int) -> Option<Mode> {
        Some(match m {
            0 => Mode::RGB,
            1 => Mode::RGBA,
            2 => Mode::BGR,
            3 => Mode::BGRA,
            4 => Mode::ARGB,
            5 => Mode::RGBA4444,
            6 => Mode::RGB565,
            7 => Mode::PremulRGBA,
            8 => Mode::PremulBGRA,
            9 => Mode::PremulARGB,
            10 => Mode::PremulRGBA4444,
            _ => return None,
        })
    }

    /// Bytes per pixel.
    pub fn bpp(self) -> usize {
        match self {
            Mode::RGB | Mode::BGR => 3,
            Mode::RGBA4444 | Mode::RGB565 | Mode::PremulRGBA4444 => 2,
            _ => 4,
        }
    }
}

/// A decoded image: ARGB pixels (alpha in the high byte), row by row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Image {
    pub width: usize,
    pub height: usize,
    pub argb: Vec<u32>,
}

/// Decodes a WebP file, lossless or lossy.
pub fn decode(data: &[u8]) -> Result<Image, Error> {
    let r = match webp_decode_exec(data).0 {
        Err(Error::Unsupported) => decode_lossy(data),
        r => r,
    };
    r.map(|d| Image { width: d.w, height: d.h, argb: d.px })
}

/// What `WebPGetFeatures` reports.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Features {
    pub width: usize,
    pub height: usize,
    pub has_alpha: bool,
    /// A lossy (VP8) image.
    pub lossy: bool,
}

/// The size and alpha hint of a lossless WebP file, from its headers.
pub fn get_features(data: &[u8]) -> Result<Features, VP8StatusCode> {
    if data.len() < 12 {
        return Err(VP8_STATUS_NOT_ENOUGH_DATA);
    }
    match parse_headers_exec(data) {
        ParsedX::Lossless(p) => {
            let sub = &data[p..];
            let hdr = if sub.len() < 8 { header_exec(&pad_exec(sub)) } else { header_exec(sub) };
            match hdr {
                Some((w, h, a)) => Ok(Features { width: w as usize, height: h as usize, has_alpha: a != 0, lossy: false }),
                None => Err(VP8_STATUS_BITSTREAM_ERROR),
            }
        }
        ParsedX::Lossy => match lossy_layout(data) {
            Some(l) => Ok(Features { width: l.width, height: l.height, has_alpha: l.has_alpha, lossy: true }),
            None => Err(VP8_STATUS_BITSTREAM_ERROR),
        },
        ParsedX::Fail => Err(VP8_STATUS_BITSTREAM_ERROR),
    }
}

/// libwebp's premultiplication: `(x * a * 32897) >> 23`.
#[inline]
fn premul(x: u32, a: u32) -> u8 {
    ((x * (a * 32897)) >> 23) as u8
}

/// libwebp's 4444 premultiplication (`ApplyAlphaMultiply4444_C`).
#[inline]
fn premul4444(rg: u8, ba: u8) -> (u8, u8) {
    let a = ba & 0x0f;
    let mult = a as u32 * 0x1111;
    let hi = |x: u8| (x & 0xf0) | (x >> 4);
    let lo = |x: u8| (x & 0x0f) | (x << 4);
    let m = |x: u8| ((x as u32 * mult) >> 16) as u8;
    let r = m(hi(rg));
    let g = m(lo(rg));
    let b = m(hi(ba));
    ((r & 0xf0) | ((g >> 4) & 0x0f), (b & 0xf0) | a)
}

/// Writes one pixel in `mode` to `o`, which is `mode.bpp()` bytes.
#[inline]
fn put(o: &mut [u8], c: u32, mode: Mode) {
    let a = (c >> 24) as u8;
    let r = (c >> 16) as u8;
    let g = (c >> 8) as u8;
    let b = c as u8;
    match mode {
        Mode::RGB => o.copy_from_slice(&[r, g, b]),
        Mode::BGR => o.copy_from_slice(&[b, g, r]),
        Mode::RGBA => o.copy_from_slice(&[r, g, b, a]),
        Mode::BGRA => o.copy_from_slice(&[b, g, r, a]),
        Mode::ARGB => o.copy_from_slice(&[a, r, g, b]),
        Mode::PremulRGBA | Mode::PremulBGRA | Mode::PremulARGB => {
            let (r, g, b) = if a != 0xff {
                (premul(r as u32, a as u32), premul(g as u32, a as u32), premul(b as u32, a as u32))
            } else {
                (r, g, b)
            };
            match mode {
                Mode::PremulRGBA => o.copy_from_slice(&[r, g, b, a]),
                Mode::PremulBGRA => o.copy_from_slice(&[b, g, r, a]),
                _ => o.copy_from_slice(&[a, r, g, b]),
            }
        }
        Mode::RGBA4444 | Mode::PremulRGBA4444 => {
            let rg = ((c >> 16) & 0xf0) as u8 | ((c >> 12) & 0xf) as u8;
            let ba = (c & 0xf0) as u8 | ((c >> 28) & 0xf) as u8;
            let (rg, ba) = if mode == Mode::PremulRGBA4444 { premul4444(rg, ba) } else { (rg, ba) };
            o.copy_from_slice(&[rg, ba]);
        }
        Mode::RGB565 => {
            let rg = ((c >> 16) & 0xf8) as u8 | ((c >> 13) & 0x7) as u8;
            let gb = ((c >> 5) & 0xe0) as u8 | ((c >> 3) & 0x1f) as u8;
            o.copy_from_slice(&[rg, gb]);
        }
    }
}

/// Writes `img` to `out` in `mode`, `stride` bytes per row, rows flipped
/// if `flip`. `out` must hold `stride * (height - 1) + width * bpp` bytes
/// and `stride >= width * bpp`.
pub fn convert(img: &Image, mode: Mode, out: &mut [u8], stride: usize, flip: bool) {
    let bpp = mode.bpp();
    let row_bytes = img.width * bpp;
    for y in 0..img.height {
        let oy = if flip { img.height - 1 - y } else { y };
        let row = &mut out[oy * stride..oy * stride + row_bytes];
        let src = &img.argb[y * img.width..(y + 1) * img.width];
        // Fast paths for the common 32-bit layouts: the decoder's ARGB word is
        // 0xAARRGGBB, so a little-endian u32 store already yields B,G,R,A (BGRA);
        // RGBA is the same with R and B swapped. Writing whole words (which the
        // compiler can vectorise) avoids the per-pixel match and slice copy.
        match mode {
            Mode::BGRA => {
                for (o, &c) in row.chunks_exact_mut(4).zip(src) {
                    o.copy_from_slice(&c.to_le_bytes());
                }
            }
            Mode::RGBA => {
                for (o, &c) in row.chunks_exact_mut(4).zip(src) {
                    let rb = (c & 0xff00_ff00) | ((c >> 16) & 0xff) | ((c & 0xff) << 16);
                    o.copy_from_slice(&rb.to_le_bytes());
                }
            }
            _ => {
                for (o, &c) in row.chunks_exact_mut(bpp).zip(src) {
                    put(o, c, mode);
                }
            }
        }
    }
}

/// The verified byte layout (`vp8yuv::kind_bpp`) that is `mode` for a lossy
/// image, if there is one: the premultiplied modes only without alpha.
fn byte_kind(mode: Mode, has_alpha: bool) -> Option<u8> {
    Some(match mode {
        Mode::RGBA => 1,
        Mode::BGRA => 2,
        Mode::ARGB => 3,
        Mode::RGB => 4,
        Mode::BGR => 5,
        Mode::PremulRGBA if !has_alpha => 1,
        Mode::PremulBGRA if !has_alpha => 2,
        Mode::PremulARGB if !has_alpha => 3,
        _ => return None,
    })
}

/// A decoded file, before it is written out: an ARGB image, or (lossy) the
/// planes, which go straight to the output layouts `byte_kind` has.
enum Decoding {
    Image(Image),
    Lossy(LossyPlanes),
}

impl Decoding {
    fn new(data: &[u8]) -> Result<Decoding, Error> {
        match webp_decode_exec(data).0 {
            Err(Error::Unsupported) => decode_lossy_planes(data).map(Decoding::Lossy),
            r => r.map(|d| Decoding::Image(Image { width: d.w, height: d.h, argb: d.px })),
        }
    }

    fn size(&self) -> (usize, usize) {
        match self {
            Decoding::Image(i) => (i.width, i.height),
            Decoding::Lossy(p) => (p.pl.width, p.pl.height),
        }
    }

    /// The image as ARGB words.
    fn image(self) -> Result<Image, Error> {
        Ok(match self {
            Decoding::Image(i) => i,
            Decoding::Lossy(p) => {
                let px = planes_to_argb(&p.pl, &p.alpha, p.has_alpha)?;
                Image { width: p.pl.width, height: p.pl.height, argb: px }
            }
        })
    }

    /// Writes the image to `out` in `mode`, rows packed.
    fn write(self, mode: Mode, out: &mut [u8]) -> Result<(), Error> {
        if let Decoding::Lossy(p) = &self {
            if let Some(k) = byte_kind(mode, p.has_alpha) {
                return planes_to_bytes(&p.pl, &p.alpha, p.has_alpha, out, k);
            }
        }
        let img = self.image()?;
        convert(&img, mode, out, img.width * mode.bpp(), false);
        Ok(())
    }
}

/// Decodes to a new buffer in `mode`, rows packed.
pub fn decode_to(data: &[u8], mode: Mode) -> Result<(Vec<u8>, usize, usize), Error> {
    let d = Decoding::new(data)?;
    let (w, h) = d.size();
    let mut out = Vec::new();
    out.try_reserve_exact(w * mode.bpp() * h).map_err(|_| Error::OutOfMemory)?;
    out.resize(w * mode.bpp() * h, 0);
    d.write(mode, &mut out)?;
    Ok((out, w, h))
}

// ---------------------------------------------------------------------------
// The C API
// ---------------------------------------------------------------------------

unsafe extern "C" {
    fn malloc(size: usize) -> *mut c_void;
    fn calloc(n: usize, size: usize) -> *mut c_void;
    fn free(p: *mut c_void);
}

#[repr(C)]
pub struct WebPBitstreamFeatures {
    pub width: c_int,
    pub height: c_int,
    pub has_alpha: c_int,
    pub has_animation: c_int,
    pub format: c_int,
    pub pad: [u32; 5],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct WebPRGBABuffer {
    pub rgba: *mut u8,
    pub stride: c_int,
    pub size: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct WebPYUVABuffer {
    pub y: *mut u8,
    pub u: *mut u8,
    pub v: *mut u8,
    pub a: *mut u8,
    pub y_stride: c_int,
    pub u_stride: c_int,
    pub v_stride: c_int,
    pub a_stride: c_int,
    pub y_size: usize,
    pub u_size: usize,
    pub v_size: usize,
    pub a_size: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union WebPBufferUnion {
    pub rgba: WebPRGBABuffer,
    pub yuva: WebPYUVABuffer,
}

#[repr(C)]
pub struct WebPDecBuffer {
    pub colorspace: c_int,
    pub width: c_int,
    pub height: c_int,
    pub is_external_memory: c_int,
    pub u: WebPBufferUnion,
    pub pad: [u32; 4],
    pub private_memory: *mut u8,
}

#[repr(C)]
pub struct WebPDecoderOptions {
    pub bypass_filtering: c_int,
    pub no_fancy_upsampling: c_int,
    pub use_cropping: c_int,
    pub crop_left: c_int,
    pub crop_top: c_int,
    pub crop_width: c_int,
    pub crop_height: c_int,
    pub use_scaling: c_int,
    pub scaled_width: c_int,
    pub scaled_height: c_int,
    pub use_threads: c_int,
    pub dithering_strength: c_int,
    pub flip: c_int,
    pub alpha_dithering_strength: c_int,
    pub pad: [u32; 5],
}

#[repr(C)]
pub struct WebPDecoderConfig {
    pub input: WebPBitstreamFeatures,
    pub output: WebPDecBuffer,
    pub options: WebPDecoderOptions,
}

/// The input as a slice, or `None` for a null pointer.
unsafe fn input<'a>(data: *const u8, size: usize) -> Option<&'a [u8]> {
    if data.is_null() {
        None
    } else {
        // SAFETY: the caller passes `size` readable bytes at `data`.
        Some(core::slice::from_raw_parts(data, size))
    }
}

/// Decodes into a new `malloc`ed buffer (freed with `WebPFree` or `free`).
unsafe fn decode_malloc(data: *const u8, size: usize, w: *mut c_int, h: *mut c_int, mode: Mode) -> *mut u8 {
    let Some(d) = input(data, size) else { return core::ptr::null_mut() };
    let Ok(dec) = Decoding::new(d) else { return core::ptr::null_mut() };
    let (iw, ih) = dec.size();
    let total = iw * mode.bpp() * ih;
    // `calloc`: the buffer is initialized (zero pages for large sizes) before
    // a slice is made of it.
    let p = calloc(total, 1) as *mut u8;
    if p.is_null() {
        return core::ptr::null_mut();
    }
    // SAFETY: `p` holds `total` initialized bytes, just allocated.
    let out = core::slice::from_raw_parts_mut(p, total);
    if dec.write(mode, out).is_err() {
        free(p as *mut c_void);
        return core::ptr::null_mut();
    }
    if !w.is_null() {
        *w = iw as c_int;
    }
    if !h.is_null() {
        *h = ih as c_int;
    }
    p
}

/// The bytes a buffer of `h` rows of `w` pixels at `stride` needs
/// (libwebp's `MIN_BUFFER_SIZE`), if the stride is wide enough.
fn needed(w: usize, h: usize, bpp: usize, stride: c_int) -> Option<usize> {
    if stride < 0 || (stride as usize) < w * bpp {
        return None;
    }
    Some(stride as usize * (h - 1) + w * bpp)
}

/// Decodes into the caller's buffer.
unsafe fn decode_into(data: *const u8, size: usize, out: *mut u8, out_size: usize, stride: c_int, mode: Mode) -> *mut u8 {
    let Some(d) = input(data, size) else { return core::ptr::null_mut() };
    if out.is_null() {
        return core::ptr::null_mut();
    }
    let Ok(dec) = Decoding::new(d) else { return core::ptr::null_mut() };
    let (w, h) = dec.size();
    match needed(w, h, mode.bpp(), stride) {
        Some(n) if n <= out_size => {
            // SAFETY: the caller passes `out_size` writable bytes at `out`.
            let o = core::slice::from_raw_parts_mut(out, out_size);
            // Packed rows go straight from the planes to the caller's buffer.
            if stride as usize == w * mode.bpp() {
                return if dec.write(mode, &mut o[..n]).is_ok() { out } else { core::ptr::null_mut() };
            }
            let img = match dec.image() {
                Ok(i) => i,
                Err(_) => return core::ptr::null_mut(),
            };
            convert(&img, mode, o, stride as usize, false);
            out
        }
        _ => core::ptr::null_mut(),
    }
}

macro_rules! simple_decoders {
    ($(($v:ident, $vi:ident, $w:ident, $wi:ident, $mode:expr)),*) => {
        $(
            /// libwebp's simple decoding function for this layout.
            #[unsafe(no_mangle)]
            pub unsafe extern "C" fn $v(data: *const u8, size: usize, w: *mut c_int, h: *mut c_int) -> *mut u8 {
                decode_malloc(data, size, w, h, $mode)
            }
            /// libwebp's decoding function into a caller's buffer.
            #[unsafe(no_mangle)]
            pub unsafe extern "C" fn $vi(data: *const u8, size: usize, out: *mut u8, out_size: usize, stride: c_int) -> *mut u8 {
                decode_into(data, size, out, out_size, stride, $mode)
            }
            #[cfg(feature = "webp-abi")]
            #[unsafe(no_mangle)]
            pub unsafe extern "C" fn $w(data: *const u8, size: usize, w: *mut c_int, h: *mut c_int) -> *mut u8 {
                $v(data, size, w, h)
            }
            #[cfg(feature = "webp-abi")]
            #[unsafe(no_mangle)]
            pub unsafe extern "C" fn $wi(data: *const u8, size: usize, out: *mut u8, out_size: usize, stride: c_int) -> *mut u8 {
                $vi(data, size, out, out_size, stride)
            }
        )*
    };
}

simple_decoders!(
    (vwebp_DecodeRGBA, vwebp_DecodeRGBAInto, WebPDecodeRGBA, WebPDecodeRGBAInto, Mode::RGBA),
    (vwebp_DecodeARGB, vwebp_DecodeARGBInto, WebPDecodeARGB, WebPDecodeARGBInto, Mode::ARGB),
    (vwebp_DecodeBGRA, vwebp_DecodeBGRAInto, WebPDecodeBGRA, WebPDecodeBGRAInto, Mode::BGRA),
    (vwebp_DecodeRGB, vwebp_DecodeRGBInto, WebPDecodeRGB, WebPDecodeRGBInto, Mode::RGB),
    (vwebp_DecodeBGR, vwebp_DecodeBGRInto, WebPDecodeBGR, WebPDecodeBGRInto, Mode::BGR)
);

/// `WebPGetDecoderVersion`.
#[unsafe(no_mangle)]
pub extern "C" fn vwebp_GetDecoderVersion() -> c_int {
    LIBWEBP_VERSION
}

/// `WebPGetInfo`: 1 with the size of a lossless image, else 0.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_GetInfo(data: *const u8, size: usize, w: *mut c_int, h: *mut c_int) -> c_int {
    let Some(d) = input(data, size) else { return 0 };
    match get_features(d) {
        Ok(f) => {
            if !w.is_null() {
                *w = f.width as c_int;
            }
            if !h.is_null() {
                *h = f.height as c_int;
            }
            1
        }
        Err(_) => 0,
    }
}

/// `WebPGetFeaturesInternal`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_GetFeaturesInternal(
    data: *const u8,
    size: usize,
    features: *mut WebPBitstreamFeatures,
    version: c_int,
) -> VP8StatusCode {
    if (version >> 8) != (WEBP_DECODER_ABI_VERSION >> 8) || features.is_null() {
        return VP8_STATUS_INVALID_PARAM;
    }
    let Some(d) = input(data, size) else { return VP8_STATUS_INVALID_PARAM };
    core::ptr::write_bytes(features, 0, 1);
    match get_features(d) {
        Ok(f) => {
            (*features).width = f.width as c_int;
            (*features).height = f.height as c_int;
            (*features).has_alpha = f.has_alpha as c_int;
            (*features).format = if f.lossy { 1 } else { 2 };
            VP8_STATUS_OK
        }
        Err(s) => s,
    }
}

/// `WebPInitDecBufferInternal`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_InitDecBufferInternal(buffer: *mut WebPDecBuffer, version: c_int) -> c_int {
    if (version >> 8) != (WEBP_DECODER_ABI_VERSION >> 8) || buffer.is_null() {
        return 0;
    }
    core::ptr::write_bytes(buffer, 0, 1);
    1
}

/// `WebPFreeDecBuffer`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_FreeDecBuffer(buffer: *mut WebPDecBuffer) {
    if buffer.is_null() {
        return;
    }
    if (*buffer).is_external_memory <= 0 && !(*buffer).private_memory.is_null() {
        free((*buffer).private_memory as *mut c_void);
    }
    (*buffer).private_memory = core::ptr::null_mut();
}

/// `WebPInitDecoderConfigInternal`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_InitDecoderConfigInternal(config: *mut WebPDecoderConfig, version: c_int) -> c_int {
    if (version >> 8) != (WEBP_DECODER_ABI_VERSION >> 8) || config.is_null() {
        return 0;
    }
    core::ptr::write_bytes(config, 0, 1);
    1
}

fn status_of(e: Error) -> VP8StatusCode {
    match e {
        Error::Bitstream => VP8_STATUS_BITSTREAM_ERROR,
        Error::OutOfMemory => VP8_STATUS_OUT_OF_MEMORY,
        Error::Unsupported => VP8_STATUS_UNSUPPORTED_FEATURE,
    }
}

/// `WebPDecode`: RGB output layouts and vertical flipping; cropping,
/// scaling and YUV output give `VP8_STATUS_UNSUPPORTED_FEATURE`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_Decode(data: *const u8, size: usize, config: *mut WebPDecoderConfig) -> VP8StatusCode {
    if config.is_null() {
        return VP8_STATUS_INVALID_PARAM;
    }
    let Some(d) = input(data, size) else { return VP8_STATUS_INVALID_PARAM };
    let s = vwebp_GetFeaturesInternal(data, size, &mut (*config).input, WEBP_DECODER_ABI_VERSION);
    if s != VP8_STATUS_OK {
        return s;
    }
    let opts = &(*config).options;
    if opts.use_cropping != 0 || opts.use_scaling != 0 {
        return VP8_STATUS_UNSUPPORTED_FEATURE;
    }
    let flip = opts.flip != 0;
    let out = &mut (*config).output;
    let Some(mode) = Mode::from_c(out.colorspace) else {
        return if out.colorspace == 11 || out.colorspace == 12 {
            VP8_STATUS_UNSUPPORTED_FEATURE
        } else {
            VP8_STATUS_INVALID_PARAM
        };
    };
    let img = match decode(d) {
        Ok(i) => i,
        Err(e) => return status_of(e),
    };
    let bpp = mode.bpp();
    if out.is_external_memory > 0 {
        let rgba = out.u.rgba;
        match needed(img.width, img.height, bpp, rgba.stride) {
            Some(n) if n <= rgba.size && !rgba.rgba.is_null() => {
                // SAFETY: the caller passes `size` writable bytes at `rgba`.
                let o = core::slice::from_raw_parts_mut(rgba.rgba, rgba.size);
                convert(&img, mode, o, rgba.stride as usize, flip);
            }
            _ => return VP8_STATUS_INVALID_PARAM,
        }
    } else {
        let stride = img.width * bpp;
        let total = stride * img.height;
        let p = malloc(total) as *mut u8;
        if p.is_null() {
            return VP8_STATUS_OUT_OF_MEMORY;
        }
        // SAFETY: `p` holds `total` bytes, just allocated.
        let o = core::slice::from_raw_parts_mut(p, total);
        convert(&img, mode, o, stride, flip);
        out.private_memory = p;
        out.u.rgba = WebPRGBABuffer { rgba: p, stride: stride as c_int, size: total };
    }
    out.width = img.width as c_int;
    out.height = img.height as c_int;
    VP8_STATUS_OK
}

/// `WebPMalloc`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_Malloc(size: usize) -> *mut c_void {
    malloc(size)
}

/// `WebPFree`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_Free(p: *mut c_void) {
    free(p)
}

/// `WebPDecodeYUV`: lossless images have no YUV form here; always null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vwebp_DecodeYUV(
    _data: *const u8,
    _size: usize,
    _w: *mut c_int,
    _h: *mut c_int,
    _u: *mut *mut u8,
    _v: *mut *mut u8,
    _stride: *mut c_int,
    _uv_stride: *mut c_int,
) -> *mut u8 {
    core::ptr::null_mut()
}

#[cfg(feature = "webp-abi")]
mod abi {
    use super::*;

    #[unsafe(no_mangle)]
    pub extern "C" fn WebPGetDecoderVersion() -> c_int {
        vwebp_GetDecoderVersion()
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPGetInfo(data: *const u8, size: usize, w: *mut c_int, h: *mut c_int) -> c_int {
        vwebp_GetInfo(data, size, w, h)
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPGetFeaturesInternal(
        data: *const u8,
        size: usize,
        features: *mut WebPBitstreamFeatures,
        version: c_int,
    ) -> VP8StatusCode {
        vwebp_GetFeaturesInternal(data, size, features, version)
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPInitDecBufferInternal(buffer: *mut WebPDecBuffer, version: c_int) -> c_int {
        vwebp_InitDecBufferInternal(buffer, version)
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPFreeDecBuffer(buffer: *mut WebPDecBuffer) {
        vwebp_FreeDecBuffer(buffer)
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPInitDecoderConfigInternal(config: *mut WebPDecoderConfig, version: c_int) -> c_int {
        vwebp_InitDecoderConfigInternal(config, version)
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPDecode(data: *const u8, size: usize, config: *mut WebPDecoderConfig) -> VP8StatusCode {
        vwebp_Decode(data, size, config)
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPMalloc(size: usize) -> *mut c_void {
        vwebp_Malloc(size)
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPFree(p: *mut c_void) {
        vwebp_Free(p)
    }
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn WebPDecodeYUV(
        data: *const u8,
        size: usize,
        w: *mut c_int,
        h: *mut c_int,
        u: *mut *mut u8,
        v: *mut *mut u8,
        stride: *mut c_int,
        uv_stride: *mut c_int,
    ) -> *mut u8 {
        vwebp_DecodeYUV(data, size, w, h, u, v, stride, uv_stride)
    }
}
