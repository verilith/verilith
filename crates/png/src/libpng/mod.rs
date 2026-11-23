//! libpng's read API (`png.h` of libpng 1.6.59) over the verified decoder.
//!
//! This module is not verified. It reads the file through the caller's I/O
//! functions, hands the bytes to the verified container parser and decoder
//! (`decode::container_exec`, `top::decode`), and then gives the pixels to
//! the caller the way libpng does: row by row, through libpng's
//! transformations, with libpng's interlace handling, error handling
//! (`setjmp`/`longjmp` and the caller's error functions) and `png_get_*`
//! functions. It is safe Rust apart from the pointers that cross the C
//! boundary.
//!
//! Every function is exported as `vpng_<name>` (`png_read_info` as
//! `vpng_read_info`); with the `libpng-abi` feature, under libpng's own
//! name instead, so that a program written for `png.h` links against this
//! library unchanged. `include/pnglibconf.h` describes what is here to a
//! program compiled against libpng's `png.h`.
//!
//! What is here, and how it differs from libpng, is in the README ("The
//! libpng API"). In short: the sequential and the progressive reader,
//! `png_read_png`, the transformations that do not need gamma (expand,
//! strip and scale 16, strip alpha, gray to RGB, filler and add alpha,
//! BGR, swap alpha, invert alpha, invert mono, shift, packing, packswap,
//! swap, user transforms), interlace handling, the ancillary chunks of
//! `pnglibconf.h`, unknown and user chunks, and user memory, error and I/O
//! functions. Not here: writing, the simplified API (`png_image_*`), gamma
//! correction, background composition, alpha modes, RGB to gray and
//! quantizing.
//!
//! Errors. libpng's error functions do not return: `png_error` calls the
//! caller's error function and then `longjmp`s to the caller's `setjmp`.
//! A `longjmp` may cross Rust frames only if they own nothing that needs to
//! be dropped, so the code here is arranged that way: the functions that do
//! the work return `Result<_, E>` (`E` is `Copy`), every buffer lives in
//! the heap-allocated `Png` and `Info` structures rather than on the stack,
//! and `png_error` is called only by the exported function itself, after
//! the work function has returned. The caller's own callbacks (I/O, chunk,
//! row, transform and warning functions) may `longjmp` too; they are
//! called only at points where the frames above them own nothing.
#![allow(non_camel_case_types, non_snake_case, clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn, non_upper_case_globals, dangerous_implicit_autorefs)]

use core::ffi::{c_char, c_int, c_void};

mod err;
mod info;
mod mem;
mod read;
mod stubs;
mod xform;

pub use info::Info;
pub use read::Png;

/// Exports each function as `vpng_<name>`, or with the `libpng-abi`
/// feature as libpng's `png_<name>`.
macro_rules! api {
    ($( $(#[$m:meta])* pub unsafe extern "C" fn $name:ident ($($args:tt)*) $(-> $ret:ty)? $body:block )*) => {
        $(
            $(#[$m])*
            #[cfg_attr(feature = "libpng-abi", unsafe(no_mangle))]
            #[cfg_attr(not(feature = "libpng-abi"), unsafe(export_name = concat!("v", stringify!($name))))]
            pub unsafe extern "C" fn $name($($args)*) $(-> $ret)? $body
        )*
    };
}
pub(crate) use api;

pub type png_uint_32 = u32;
pub type png_int_32 = i32;
pub type png_uint_16 = u16;
pub type png_byte = u8;
pub type png_fixed_point = i32;
pub type png_structp = *mut Png;
pub type png_infop = *mut Info;
pub type png_bytep = *mut u8;
pub type png_charp = *mut c_char;
pub type png_voidp = *mut c_void;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct png_color {
    pub red: u8,
    pub green: u8,
    pub blue: u8,
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct png_color_16 {
    pub index: u8,
    pub red: u16,
    pub green: u16,
    pub blue: u16,
    pub gray: u16,
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct png_color_8 {
    pub red: u8,
    pub green: u8,
    pub blue: u8,
    pub gray: u8,
    pub alpha: u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct png_text {
    pub compression: c_int,
    pub key: *mut c_char,
    pub text: *mut c_char,
    pub text_length: usize,
    pub itxt_length: usize,
    pub lang: *mut c_char,
    pub lang_key: *mut c_char,
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct png_time {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct png_unknown_chunk {
    pub name: [u8; 5],
    pub data: *mut u8,
    pub size: usize,
    pub location: u8,
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct png_row_info {
    pub width: u32,
    pub rowbytes: usize,
    pub color_type: u8,
    pub bit_depth: u8,
    pub channels: u8,
    pub pixel_depth: u8,
}

pub type ErrorFn = Option<unsafe extern "C" fn(png_structp, *const c_char)>;
pub type RwFn = Option<unsafe extern "C" fn(png_structp, png_bytep, usize)>;
pub type FlushFn = Option<unsafe extern "C" fn(png_structp)>;
pub type ReadStatusFn = Option<unsafe extern "C" fn(png_structp, png_uint_32, c_int)>;
pub type WriteStatusFn = Option<unsafe extern "C" fn(png_structp, png_uint_32, c_int)>;
pub type LongjmpFn = Option<unsafe extern "C" fn(*mut c_void, c_int)>;
pub type MallocFn = Option<unsafe extern "C" fn(png_structp, usize) -> png_voidp>;
pub type FreeFn = Option<unsafe extern "C" fn(png_structp, png_voidp)>;
pub type UserChunkFn = Option<unsafe extern "C" fn(png_structp, *mut png_unknown_chunk) -> c_int>;
pub type UserTransformFn = Option<unsafe extern "C" fn(png_structp, *mut png_row_info, png_bytep)>;
pub type ProgressiveInfoFn = Option<unsafe extern "C" fn(png_structp, png_infop)>;
pub type ProgressiveRowFn = Option<unsafe extern "C" fn(png_structp, png_bytep, png_uint_32, c_int)>;
pub type ProgressiveEndFn = Option<unsafe extern "C" fn(png_structp, png_infop)>;

pub const LIBPNG_VER_STRING: &[u8] = b"1.6.59\0";
pub const LIBPNG_VER: u32 = 10659;

pub const COLOR_MASK_PALETTE: u8 = 1;
pub const COLOR_MASK_COLOR: u8 = 2;
pub const COLOR_MASK_ALPHA: u8 = 4;
pub const CT_GRAY: u8 = 0;
pub const CT_PALETTE: u8 = 3;
pub const CT_RGB: u8 = 2;
pub const CT_RGBA: u8 = 6;
pub const CT_GA: u8 = 4;

pub const INFO_gAMA: u32 = 0x0001;
pub const INFO_sBIT: u32 = 0x0002;
pub const INFO_cHRM: u32 = 0x0004;
pub const INFO_PLTE: u32 = 0x0008;
pub const INFO_tRNS: u32 = 0x0010;
pub const INFO_bKGD: u32 = 0x0020;
pub const INFO_hIST: u32 = 0x0040;
pub const INFO_pHYs: u32 = 0x0080;
pub const INFO_oFFs: u32 = 0x0100;
pub const INFO_tIME: u32 = 0x0200;
pub const INFO_sRGB: u32 = 0x0800;
pub const INFO_iCCP: u32 = 0x1000;
pub const INFO_IDAT: u32 = 0x8000;
pub const INFO_eXIf: u32 = 0x10000;

pub const FREE_HIST: u32 = 0x0008;
pub const FREE_ICCP: u32 = 0x0010;
pub const FREE_ROWS: u32 = 0x0040;
pub const FREE_UNKN: u32 = 0x0200;
pub const FREE_PLTE: u32 = 0x1000;
pub const FREE_TRNS: u32 = 0x2000;
pub const FREE_TEXT: u32 = 0x4000;
pub const FREE_EXIF: u32 = 0x8000;

pub const HANDLE_CHUNK_AS_DEFAULT: c_int = 0;
pub const HANDLE_CHUNK_NEVER: c_int = 1;
pub const HANDLE_CHUNK_IF_SAFE: c_int = 2;
pub const HANDLE_CHUNK_ALWAYS: c_int = 3;
pub const HANDLE_CHUNK_LAST: c_int = 4;

/// `PNG_HAVE_*` and the other `mode` bits.
pub const HAVE_IHDR: u32 = 0x01;
pub const HAVE_PLTE: u32 = 0x02;
pub const HAVE_IDAT: u32 = 0x04;
pub const AFTER_IDAT: u32 = 0x08;
pub const HAVE_IEND: u32 = 0x10;
pub const HAVE_SIG: u32 = 0x1000;

/// Chunk types as big-endian numbers.
pub const fn ctype(n: &[u8; 4]) -> u32 {
    u32::from_be_bytes(*n)
}
pub const IHDR: u32 = ctype(b"IHDR");
pub const PLTE: u32 = ctype(b"PLTE");
pub const IDAT: u32 = ctype(b"IDAT");
pub const IEND: u32 = ctype(b"IEND");
pub const TRNS: u32 = ctype(b"tRNS");

/// `PNG_ROWBYTES`.
pub fn rowbytes(pixel_depth: u32, width: u32) -> usize {
    if pixel_depth >= 8 {
        width as usize * (pixel_depth as usize >> 3)
    } else {
        (width as usize * pixel_depth as usize + 7) >> 3
    }
}

pub(crate) unsafe fn cstr_len(s: *const c_char) -> usize {
    let mut n = 0;
    while *s.add(n) != 0 {
        n += 1;
    }
    n
}
