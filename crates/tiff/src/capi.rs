//! libtiff's reading API (libtiff 4.5, `tiffio.h`) over the verified
//! decoder: `TIFFOpen`, `TIFFClientOpen`, `TIFFGetField`, the size and
//! layout functions, `TIFFReadEncodedStrip`/`Tile`, `TIFFReadScanline`,
//! `TIFFReadRGBAImage`, and the rest that programs reading TIFF files use.
//!
//! This file is trusted glue, not verified. The file is read in full when
//! it is opened; the header and IFD 0 are read by the verified
//! `header_exec` and `params_exec`, and each strip or tile is decoded by the
//! verified `chunk_exec` when it is asked for, as libtiff decodes them. The
//! glue reads the fields the verified decoder does not use (resolution,
//! strings, ICC profile, ...) itself, with bounds-checked slices, and does
//! the conversion of `TIFFReadRGBAImage` the way libtiff's
//! `tif_getimage.c` does for the photometric interpretations it supports.
//!
//! Where libtiff and the TIFF 6.0 standard disagree, this follows the
//! standard: fields are reported as the file has them (a field of a type
//! other than BYTE, SHORT or LONG where an integer is expected is skipped,
//! and absent fields have the standard's defaults), strips are the file's
//! strips, extra samples are only alpha when ExtraSamples says so, and a
//! ColorMap is always 16-bit.
//! The variadic functions (`TIFFGetField`, `TIFFError`, ...) are in
//! `capi/tiffshim.c`, which calls the functions here.
//!
//! The functions are exported as `vtiff_*`; with the `tiff-abi` feature
//! also under libtiff's names. Writing is not provided, and only the first
//! image of a file can be read.
#![allow(non_snake_case, non_camel_case_types, unsafe_op_in_unsafe_fn, clippy::missing_safety_doc)]
use crate::chunk::Error;
use crate::decode::chunk_exec;
use crate::ifd::{field_exec, header_exec, value_exec};
use crate::params::{params_exec, ParamsX};
use core::ffi::{c_char, c_int, c_void};
use std::ffi::{CStr, CString};

pub type tmsize_t = isize;
pub type toff_t = u64;
pub type thandle_t = *mut c_void;
pub type ReadProc = Option<unsafe extern "C" fn(thandle_t, *mut c_void, tmsize_t) -> tmsize_t>;
pub type SeekProc = Option<unsafe extern "C" fn(thandle_t, toff_t, c_int) -> toff_t>;
pub type CloseProc = Option<unsafe extern "C" fn(thandle_t) -> c_int>;
pub type SizeProc = Option<unsafe extern "C" fn(thandle_t) -> toff_t>;
pub type MapProc = Option<unsafe extern "C" fn(thandle_t, *mut *mut c_void, *mut toff_t) -> c_int>;
pub type UnmapProc = Option<unsafe extern "C" fn(thandle_t, *mut c_void, toff_t)>;

unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn calloc(n: usize, m: usize) -> *mut c_void;
    fn realloc(p: *mut c_void, n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
    fn vtiff_report(warning: c_int, fd: thandle_t, module: *const c_char, msg: *const c_char);
}

/// The libtiff version whose API this implements.
const VERSION: &[u8] = b"LIBTIFF, Version 4.5.1 (verilith-tiff)\0";

/// An open file: what `TIFF *` points to.
pub struct Handle {
    name: CString,
    data: Vec<u8>,
    p: ParamsX,
    /// IFD 0: its offset and number of entries.
    ifd: usize,
    n: usize,
    client: thandle_t,
    close: CloseProc,
    unmap: UnmapProc,
    fd: c_int,
    /// The strip or tile decoded last.
    cache: Option<(u32, Vec<u8>)>,
    off: Vec<u32>,
    len: Vec<u32>,
    // What `TIFFGetField` hands out, alive as long as the file is open.
    offsets: Vec<u64>,
    counts: Vec<u64>,
    cmap: Option<[Vec<u16>; 3]>,
    extra: Vec<u16>,
    strings: Vec<(u32, CString)>,
    blobs: Vec<(u32, Vec<u8>)>,
    row: u32,
    strip: u32,
    tile: u32,
}

unsafe fn handle<'a>(t: *mut c_void) -> Option<&'a mut Handle> {
    if t.is_null() { None } else { Some(&mut *(t as *mut Handle)) }
}

fn report(warning: bool, client: thandle_t, module: &CStr, msg: &str) {
    let m = CString::new(msg.replace('\0', " ")).unwrap_or_default();
    unsafe { vtiff_report(warning as c_int, client, module.as_ptr(), m.as_ptr()) }
}

impl Handle {
    fn error(&self, msg: &str) {
        report(false, self.client, &self.name, msg);
    }

    fn le(&self) -> bool {
        self.p.le
    }

    /// The raw entry with tag `tag`, if any: its type, count and where its
    /// values are.
    fn entry(&self, tag: u16) -> Option<(u16, u32, usize)> {
        let b = &self.data;
        let le = self.le();
        let u16v = |i: usize| -> Option<u16> {
            let s = b.get(i..i + 2)?;
            Some(if le { u16::from_le_bytes([s[0], s[1]]) } else { u16::from_be_bytes([s[0], s[1]]) })
        };
        let u32v = |i: usize| -> Option<u32> {
            let s = b.get(i..i + 4)?;
            Some(if le { u32::from_le_bytes([s[0], s[1], s[2], s[3]]) } else { u32::from_be_bytes([s[0], s[1], s[2], s[3]]) })
        };
        for i in 0..self.n {
            let e = self.ifd + 2 + 12 * i;
            if u16v(e)? != tag {
                continue;
            }
            let ty = u16v(e + 2)?;
            let cnt = u32v(e + 4)?;
            let size = type_size(ty)? as u64 * cnt as u64;
            let pos = if size <= 4 { e + 8 } else { u32v(e + 8)? as usize };
            if pos as u64 + size > b.len() as u64 {
                return None;
            }
            return Some((ty, cnt, pos));
        }
        None
    }

    /// A SHORT field with one value (N = 1), as TIFF 6.0 reads it: of type
    /// BYTE, SHORT or LONG ("TIFF readers should accept BYTE, SHORT, or
    /// LONG values for any unsigned integer field"), else skipped, and at
    /// most 65535.
    fn short(&self, tag: u16) -> Option<u32> {
        match field_exec(&self.data, self.le(), self.ifd, self.n, tag) {
            Ok(Some(f)) if f.count == 1 => Some(value_exec(&self.data, self.le(), f, 0)).filter(|v| *v <= 0xffff),
            _ => None,
        }
    }

    /// Orientation: one of the eight values TIFF 6.0 defines, else not set.
    fn orientation(&self) -> Option<u32> {
        self.short(274).filter(|v| (1..=8).contains(v))
    }

    /// Whether an integer field is present: an entry of type BYTE, SHORT or
    /// LONG (fields of other types are skipped).
    fn present(&self, tag: u16) -> bool {
        matches!(self.entry(tag), Some((1 | 3 | 4, _, _)))
    }

    /// An unsigned integer field's first value.
    fn uint(&self, tag: u16) -> Option<u32> {
        match field_exec(&self.data, self.le(), self.ifd, self.n, tag) {
            Ok(Some(f)) if f.count >= 1 => Some(value_exec(&self.data, self.le(), f, 0)),
            _ => None,
        }
    }

    /// A RATIONAL field with one value (fields of other types are
    /// skipped).
    fn rational(&self, tag: u16) -> Option<f32> {
        let (ty, cnt, pos) = self.entry(tag)?;
        if cnt != 1 || ty != 5 {
            return None;
        }
        let s = self.data.get(pos..pos + 8)?;
        let (a, b) = if self.le() {
            (u32::from_le_bytes([s[0], s[1], s[2], s[3]]), u32::from_le_bytes([s[4], s[5], s[6], s[7]]))
        } else {
            (u32::from_be_bytes([s[0], s[1], s[2], s[3]]), u32::from_be_bytes([s[4], s[5], s[6], s[7]]))
        };
        Some(if b == 0 { 0.0 } else { (a as f64 / b as f64) as f32 })
    }

    /// An ASCII field, cut at its first NUL.
    fn ascii(&self, tag: u16) -> Option<CString> {
        let (ty, cnt, pos) = self.entry(tag)?;
        if ty != 2 {
            return None;
        }
        let s = self.data.get(pos..pos + cnt as usize)?;
        let s = match s.iter().position(|&c| c == 0) {
            Some(z) => &s[..z],
            None => s,
        };
        CString::new(s).ok()
    }

    /// A field's raw bytes (UNDEFINED or BYTE).
    fn bytes(&self, tag: u16) -> Option<Vec<u8>> {
        let (ty, cnt, pos) = self.entry(tag)?;
        let size = type_size(ty)? * cnt as usize;
        self.data.get(pos..pos + size).map(|s| s.to_vec())
    }

    fn planes(&self) -> u64 {
        if self.p.planar == 2 { self.p.spp as u64 } else { 1 }
    }

    fn sc(&self) -> u64 {
        if self.p.planar == 2 { 1 } else { self.p.spp as u64 }
    }

    fn scanline(&self) -> u64 {
        (self.p.width as u64 * self.sc() * self.p.bps as u64).div_ceil(8)
    }

    /// Rows per strip, as the file has them.
    fn rps_eff(&self) -> u32 {
        self.p.rps
    }

    fn rps(&self) -> u64 {
        (self.rps_eff() as u64).min(self.p.height as u64)
    }

    fn strips_per_plane(&self) -> u64 {
        (self.p.height as u64).div_ceil(self.rps_eff() as u64)
    }

    fn tile_row(&self) -> u64 {
        (self.p.tw as u64 * self.sc() * self.p.bps as u64).div_ceil(8)
    }

    /// Strips or tiles in the file.
    fn chunks(&self) -> u32 {
        self.offsets.len() as u32
    }

    /// Strip or tile `k`, decoded by the verified decoder (the last one
    /// asked for is kept).
    fn chunk(&mut self, k: u32) -> Result<&[u8], Error> {
        if !matches!(&self.cache, Some((c, _)) if *c == k) {
            self.cache = None;
            let v = chunk_exec(&self.data, &self.p, k, usize::MAX, &mut self.off, &mut self.len)?;
            self.cache = Some((k, v));
        }
        Ok(&self.cache.as_ref().unwrap().1)
    }
}

fn type_size(ty: u16) -> Option<usize> {
    Some(match ty {
        1 | 2 | 6 | 7 => 1,
        3 | 8 => 2,
        4 | 9 | 11 | 13 => 4,
        5 | 10 | 12 | 16 | 17 | 18 => 8,
        _ => return None,
    })
}

fn chunk_error(e: Error) -> &'static str {
    match e {
        Error::Invalid => "Decoding error: the data is not what the TIFF specification allows",
        Error::Unsupported => "Decoding error: a feature verilith-tiff does not read",
        Error::TooLarge => "Decoding error: the strip or tile is too large",
        Error::OutOfMemory => "Out of memory",
    }
}

/// Opens the bytes `data` of a file named `name`.
unsafe fn open_bytes(name: &CStr, mode: *const c_char, data: Vec<u8>, client: thandle_t, close: CloseProc, unmap: UnmapProc, fd: c_int) -> *mut c_void {
    let fail = |msg: &str| {
        report(false, client, name, msg);
        core::ptr::null_mut()
    };
    let (le, o) = match header_exec(&data) {
        Some(x) => x,
        None => {
            if data.len() >= 4 && (&data[..4] == b"II\x2b\x00" || &data[..4] == b"MM\x00\x2b") {
                return fail("Sorry, BigTIFF files are not read by verilith-tiff");
            }
            if data.len() < 8 {
                return fail("Cannot read TIFF header");
            }
            return fail("Not a TIFF file, bad magic number");
        },
    };
    let p = match params_exec(&data, le, o) {
        Some(p) => p,
        None => return fail("TIFFReadDirectory: the first directory is not one verilith-tiff reads"),
    };
    let ifd = o as usize;
    let n = data.get(ifd..ifd + 2).map(|s| if le { u16::from_le_bytes([s[0], s[1]]) } else { u16::from_be_bytes([s[0], s[1]]) }).unwrap_or(0) as usize;
    let mut h = Handle {
        name: name.to_owned(),
        data,
        p,
        ifd,
        n,
        client,
        close,
        unmap,
        fd,
        cache: None,
        off: vec![0; 4096],
        len: vec![0; 4096],
        offsets: Vec::new(),
        counts: Vec::new(),
        cmap: None,
        extra: Vec::new(),
        strings: Vec::new(),
        blobs: Vec::new(),
        row: u32::MAX,
        strip: u32::MAX,
        tile: u32::MAX,
    };
    for k in 0..h.p.offsets.count {
        h.offsets.push(value_exec(&h.data, le, h.p.offsets, k) as u64);
        h.counts.push(value_exec(&h.data, le, h.p.counts, k) as u64);
    }
    let _ = mode;
    // The ColorMap: required for a palette image (the decoder has checked
    // it), and reported for any image that has one of 3 * 2**BitsPerSample
    // values.
    if h.p.bps <= 16 {
        if let Ok(Some(f)) = field_exec(&h.data, le, ifd, n, 320) {
            let m = 1u32 << h.p.bps;
            if f.count == 3 * m {
                let v: Vec<u16> = (0..f.count).map(|k| value_exec(&h.data, le, f, k) as u16).collect();
                h.cmap = Some([v[..m as usize].to_vec(), v[m as usize..2 * m as usize].to_vec(), v[2 * m as usize..].to_vec()]);
            }
        }
    }
    // ExtraSamples as the file has it: "The default is no extra samples".
    if let Ok(Some(f)) = field_exec(&h.data, le, ifd, n, 338) {
        h.extra = (0..f.count).map(|k| value_exec(&h.data, le, f, k) as u16).collect();
    }
    for tag in [269u16, 270, 271, 272, 285, 305, 306, 315, 316, 33432] {
        if let Some(s) = h.ascii(tag) {
            h.strings.push((tag as u32, s));
        }
    }
    for tag in [34675u16, 700, 33723, 34377] {
        if let Some(v) = h.bytes(tag) {
            h.blobs.push((tag as u32, v));
        }
    }
    Box::into_raw(Box::new(h)) as *mut c_void
}

fn read_only(mode: *const c_char) -> bool {
    if mode.is_null() {
        return false;
    }
    let m = unsafe { CStr::from_ptr(mode) }.to_bytes();
    m.first() == Some(&b'r') && !m.contains(&b'+')
}

macro_rules! api {
    ($( $(#[$m:meta])* fn $name:ident / $v:ident ( $($a:ident : $t:ty),* $(,)? ) -> $r:ty $body:block )*) => {
        $(
            $(#[$m])*
            #[unsafe(no_mangle)]
            pub unsafe extern "C" fn $v($($a: $t),*) -> $r $body

            $(#[$m])*
            #[cfg(feature = "tiff-abi")]
            #[unsafe(no_mangle)]
            pub unsafe extern "C" fn $name($($a: $t),*) -> $r {
                $v($($a),*)
            }
        )*
    };
}

#[cfg(unix)]
fn path_of(name: &CStr) -> std::path::PathBuf {
    use std::os::unix::ffi::OsStrExt;
    std::path::PathBuf::from(std::ffi::OsStr::from_bytes(name.to_bytes()))
}

#[cfg(not(unix))]
fn path_of(name: &CStr) -> std::path::PathBuf {
    std::path::PathBuf::from(name.to_string_lossy().into_owned())
}

api! {
    /// `TIFFOpen`, for reading.
    fn TIFFOpen / vtiff_TIFFOpen(name: *const c_char, mode: *const c_char) -> *mut c_void {
        if name.is_null() {
            return core::ptr::null_mut();
        }
        let name = CStr::from_ptr(name);
        if !read_only(mode) {
            report(false, core::ptr::null_mut(), name, "verilith-tiff opens files for reading only");
            return core::ptr::null_mut();
        }
        match std::fs::read(path_of(name)) {
            Ok(d) => open_bytes(name, mode, d, core::ptr::null_mut(), None, None, -1),
            Err(e) => {
                report(false, core::ptr::null_mut(), name, &format!("Cannot open: {e}"));
                core::ptr::null_mut()
            },
        }
    }

    /// `TIFFClientOpen`, for reading: the whole file is read through
    /// `read` (or `map`) now, and `close` is called by `TIFFClose`.
    fn TIFFClientOpen / vtiff_TIFFClientOpen(
        name: *const c_char,
        mode: *const c_char,
        client: thandle_t,
        read: ReadProc,
        _write: ReadProc,
        seek: SeekProc,
        close: CloseProc,
        size: SizeProc,
        map: MapProc,
        unmap: UnmapProc,
    ) -> *mut c_void {
        let name = if name.is_null() { c"" } else { CStr::from_ptr(name) };
        if !read_only(mode) {
            report(false, client, name, "verilith-tiff opens files for reading only");
            return core::ptr::null_mut();
        }
        let Some(read) = read else { return core::ptr::null_mut() };
        let total = size.map(|f| f(client)).unwrap_or(0);
        let mut data = Vec::new();
        let no_map = !mode.is_null() && CStr::from_ptr(mode).to_bytes().contains(&b'm');
        if let (Some(map), false) = (map, no_map) {
            let mut base: *mut c_void = core::ptr::null_mut();
            let mut n: toff_t = 0;
            if map(client, &mut base, &mut n) != 0 && !base.is_null() {
                data.extend_from_slice(core::slice::from_raw_parts(base as *const u8, n as usize));
                if let Some(u) = unmap {
                    u(client, base, n);
                }
            }
        }
        if data.is_empty() {
            if let Some(seek) = seek {
                seek(client, 0, 0);
            }
            let mut chunk = vec![0u8; 1 << 16];
            loop {
                let r = read(client, chunk.as_mut_ptr() as *mut c_void, chunk.len() as tmsize_t);
                if r <= 0 {
                    break;
                }
                data.extend_from_slice(&chunk[..(r as usize).min(chunk.len())]);
                if total > 0 && data.len() as u64 >= total {
                    break;
                }
            }
        }
        open_bytes(name, mode, data, client, close, None, -1)
    }

    /// `TIFFClose`.
    fn TIFFClose / vtiff_TIFFClose(t: *mut c_void) -> () {
        let Some(h) = handle(t) else { return };
        let (close, client, fd) = (h.close, h.client, h.fd);
        let _ = h.unmap;
        drop(Box::from_raw(t as *mut Handle));
        if let Some(c) = close {
            c(client);
        }
        #[cfg(unix)]
        if fd >= 0 {
            use std::os::unix::io::FromRawFd;
            drop(std::fs::File::from_raw_fd(fd));
        }
        #[cfg(not(unix))]
        let _ = fd;
    }

    /// `TIFFCleanup`: as `TIFFClose`, but the client's close function is not
    /// called.
    fn TIFFCleanup / vtiff_TIFFCleanup(t: *mut c_void) -> () {
        if !t.is_null() {
            drop(Box::from_raw(t as *mut Handle));
        }
    }

    /// `TIFFGetVersion`.
    fn TIFFGetVersion / vtiff_TIFFGetVersion() -> *const c_char {
        VERSION.as_ptr() as *const c_char
    }

    /// `TIFFFileName`.
    fn TIFFFileName / vtiff_TIFFFileName(t: *mut c_void) -> *const c_char {
        handle(t).map(|h| h.name.as_ptr()).unwrap_or(core::ptr::null())
    }

    /// `TIFFFileno`.
    fn TIFFFileno / vtiff_TIFFFileno(t: *mut c_void) -> c_int {
        handle(t).map(|h| h.fd).unwrap_or(-1)
    }

    /// `TIFFClientdata`.
    fn TIFFClientdata / vtiff_TIFFClientdata(t: *mut c_void) -> thandle_t {
        handle(t).map(|h| h.client).unwrap_or(core::ptr::null_mut())
    }

    /// `TIFFGetMode`: always `O_RDONLY`.
    fn TIFFGetMode / vtiff_TIFFGetMode(_t: *mut c_void) -> c_int {
        0
    }

    /// `TIFFIsTiled`.
    fn TIFFIsTiled / vtiff_TIFFIsTiled(t: *mut c_void) -> c_int {
        handle(t).map(|h| h.p.tiled as c_int).unwrap_or(0)
    }

    /// `TIFFIsBigEndian`.
    fn TIFFIsBigEndian / vtiff_TIFFIsBigEndian(t: *mut c_void) -> c_int {
        handle(t).map(|h| !h.p.le as c_int).unwrap_or(0)
    }

    /// `TIFFIsByteSwapped`: whether the file's byte order is not this
    /// machine's.
    fn TIFFIsByteSwapped / vtiff_TIFFIsByteSwapped(t: *mut c_void) -> c_int {
        handle(t).map(|h| (h.p.le != cfg!(target_endian = "little")) as c_int).unwrap_or(0)
    }

    /// `TIFFIsMSB2LSB`: FillOrder 1, the only one read.
    fn TIFFIsMSB2LSB / vtiff_TIFFIsMSB2LSB(_t: *mut c_void) -> c_int {
        1
    }

    /// `TIFFIsUpSampled`: YCbCr images are not read.
    fn TIFFIsUpSampled / vtiff_TIFFIsUpSampled(_t: *mut c_void) -> c_int {
        0
    }

    /// `TIFFIsBigTIFF`: BigTIFF files are not read.
    fn TIFFIsBigTIFF / vtiff_TIFFIsBigTIFF(_t: *mut c_void) -> c_int {
        0
    }

    /// `TIFFIsCODECConfigured`: none, PackBits, LZW and Deflate.
    fn TIFFIsCODECConfigured / vtiff_TIFFIsCODECConfigured(c: u16) -> c_int {
        matches!(c, 1 | 5 | 8 | 32773) as c_int
    }

    /// `TIFFCurrentRow`: the row `TIFFReadScanline` read last.
    fn TIFFCurrentRow / vtiff_TIFFCurrentRow(t: *mut c_void) -> u32 {
        handle(t).map(|h| h.row).unwrap_or(u32::MAX)
    }

    /// `TIFFCurrentStrip`.
    fn TIFFCurrentStrip / vtiff_TIFFCurrentStrip(t: *mut c_void) -> u32 {
        handle(t).map(|h| h.strip).unwrap_or(u32::MAX)
    }

    /// `TIFFCurrentTile`.
    fn TIFFCurrentTile / vtiff_TIFFCurrentTile(t: *mut c_void) -> u32 {
        handle(t).map(|h| h.tile).unwrap_or(u32::MAX)
    }

    /// `TIFFCurrentDirectory`: the first, the only one read.
    fn TIFFCurrentDirectory / vtiff_TIFFCurrentDirectory(_t: *mut c_void) -> u32 {
        0
    }

    /// `TIFFCurrentDirOffset`.
    fn TIFFCurrentDirOffset / vtiff_TIFFCurrentDirOffset(t: *mut c_void) -> u64 {
        handle(t).map(|h| h.ifd as u64).unwrap_or(0)
    }

    /// `TIFFNumberOfDirectories`: 1, as only the first image is read.
    fn TIFFNumberOfDirectories / vtiff_TIFFNumberOfDirectories(_t: *mut c_void) -> u32 {
        1
    }

    /// `TIFFLastDirectory`: always.
    fn TIFFLastDirectory / vtiff_TIFFLastDirectory(_t: *mut c_void) -> c_int {
        1
    }

    /// `TIFFReadDirectory`: there is no next directory to read.
    fn TIFFReadDirectory / vtiff_TIFFReadDirectory(_t: *mut c_void) -> c_int {
        0
    }

    /// `TIFFSetDirectory`: 0 is the only one.
    fn TIFFSetDirectory / vtiff_TIFFSetDirectory(t: *mut c_void, d: u32) -> c_int {
        if d == 0 && handle(t).is_some() { 1 } else { 0 }
    }

    /// `TIFFScanlineSize64`.
    fn TIFFScanlineSize64 / vtiff_TIFFScanlineSize64(t: *mut c_void) -> u64 {
        handle(t).map(|h| h.scanline()).unwrap_or(0)
    }

    /// `TIFFScanlineSize`.
    fn TIFFScanlineSize / vtiff_TIFFScanlineSize(t: *mut c_void) -> tmsize_t {
        vtiff_TIFFScanlineSize64(t) as tmsize_t
    }

    /// `TIFFRasterScanlineSize64`: a row of every sample.
    fn TIFFRasterScanlineSize64 / vtiff_TIFFRasterScanlineSize64(t: *mut c_void) -> u64 {
        handle(t).map(|h| {
            let bits = h.p.width as u64 * h.p.bps as u64;
            if h.p.planar == 2 { bits.div_ceil(8) * h.p.spp as u64 } else { (bits * h.p.spp as u64).div_ceil(8) }
        }).unwrap_or(0)
    }

    /// `TIFFRasterScanlineSize`.
    fn TIFFRasterScanlineSize / vtiff_TIFFRasterScanlineSize(t: *mut c_void) -> tmsize_t {
        vtiff_TIFFRasterScanlineSize64(t) as tmsize_t
    }

    /// `TIFFVStripSize64`: `nrows` rows (all of them for `(uint32_t)-1`).
    fn TIFFVStripSize64 / vtiff_TIFFVStripSize64(t: *mut c_void, nrows: u32) -> u64 {
        handle(t).map(|h| {
            let n = if nrows == u32::MAX { h.p.height } else { nrows };
            n as u64 * h.scanline()
        }).unwrap_or(0)
    }

    /// `TIFFVStripSize`.
    fn TIFFVStripSize / vtiff_TIFFVStripSize(t: *mut c_void, nrows: u32) -> tmsize_t {
        vtiff_TIFFVStripSize64(t, nrows) as tmsize_t
    }

    /// `TIFFStripSize64`: a strip of `RowsPerStrip` rows (or the image,
    /// if it is shorter).
    fn TIFFStripSize64 / vtiff_TIFFStripSize64(t: *mut c_void) -> u64 {
        handle(t).map(|h| h.rps() * h.scanline()).unwrap_or(0)
    }

    /// `TIFFStripSize`.
    fn TIFFStripSize / vtiff_TIFFStripSize(t: *mut c_void) -> tmsize_t {
        vtiff_TIFFStripSize64(t) as tmsize_t
    }

    /// `TIFFRawStripSize64`: the strip's byte count.
    fn TIFFRawStripSize64 / vtiff_TIFFRawStripSize64(t: *mut c_void, s: u32) -> u64 {
        handle(t).and_then(|h| h.counts.get(s as usize).copied()).unwrap_or(u64::MAX)
    }

    /// `TIFFRawStripSize`.
    fn TIFFRawStripSize / vtiff_TIFFRawStripSize(t: *mut c_void, s: u32) -> tmsize_t {
        let n = vtiff_TIFFRawStripSize64(t, s);
        if n == u64::MAX || n == 0 { -1 } else { n as tmsize_t }
    }

    /// `TIFFTileRowSize64`.
    fn TIFFTileRowSize64 / vtiff_TIFFTileRowSize64(t: *mut c_void) -> u64 {
        handle(t).map(|h| if h.p.tiled { h.tile_row() } else { h.scanline() }).unwrap_or(0)
    }

    /// `TIFFTileRowSize`.
    fn TIFFTileRowSize / vtiff_TIFFTileRowSize(t: *mut c_void) -> tmsize_t {
        vtiff_TIFFTileRowSize64(t) as tmsize_t
    }

    /// `TIFFVTileSize64`.
    fn TIFFVTileSize64 / vtiff_TIFFVTileSize64(t: *mut c_void, nrows: u32) -> u64 {
        handle(t).map(|h| nrows as u64 * if h.p.tiled { h.tile_row() } else { h.scanline() }).unwrap_or(0)
    }

    /// `TIFFVTileSize`.
    fn TIFFVTileSize / vtiff_TIFFVTileSize(t: *mut c_void, nrows: u32) -> tmsize_t {
        vtiff_TIFFVTileSize64(t, nrows) as tmsize_t
    }

    /// `TIFFTileSize64`.
    fn TIFFTileSize64 / vtiff_TIFFTileSize64(t: *mut c_void) -> u64 {
        handle(t).map(|h| if h.p.tiled { h.p.th as u64 * h.tile_row() } else { (h.rps_eff() as u64).saturating_mul(h.scanline()) }).unwrap_or(0)
    }

    /// `TIFFTileSize`.
    fn TIFFTileSize / vtiff_TIFFTileSize(t: *mut c_void) -> tmsize_t {
        vtiff_TIFFTileSize64(t) as tmsize_t
    }

    /// `TIFFNumberOfStrips`.
    fn TIFFNumberOfStrips / vtiff_TIFFNumberOfStrips(t: *mut c_void) -> u32 {
        handle(t).map(|h| (h.planes() * h.strips_per_plane()) as u32).unwrap_or(0)
    }

    /// `TIFFNumberOfTiles`.
    fn TIFFNumberOfTiles / vtiff_TIFFNumberOfTiles(t: *mut c_void) -> u32 {
        handle(t).map(|h| {
            let (tw, th) = if h.p.tiled { (h.p.tw as u64, h.p.th as u64) } else { (h.p.width as u64, h.rps_eff() as u64) };
            let n = (h.p.width as u64).div_ceil(tw) * (h.p.height as u64).div_ceil(th);
            (n * h.planes()) as u32
        }).unwrap_or(0)
    }

    /// `TIFFComputeStrip`.
    fn TIFFComputeStrip / vtiff_TIFFComputeStrip(t: *mut c_void, row: u32, sample: u16) -> u32 {
        let Some(h) = handle(t) else { return 0 };
        let mut s = row / h.rps_eff();
        if h.p.planar == 2 {
            if sample as u32 >= h.p.spp {
                h.error(&format!("{sample}: Sample out of range, max {}", h.p.spp));
                return 0;
            }
            s += sample as u32 * h.strips_per_plane() as u32;
        }
        s
    }

    /// `TIFFComputeTile`.
    fn TIFFComputeTile / vtiff_TIFFComputeTile(t: *mut c_void, x: u32, y: u32, _z: u32, s: u16) -> u32 {
        let Some(h) = handle(t) else { return 0 };
        if !h.p.tiled {
            return 0;
        }
        let xpt = (h.p.width as u64).div_ceil(h.p.tw as u64);
        let ypt = (h.p.height as u64).div_ceil(h.p.th as u64);
        let mut k = xpt * (y as u64 / h.p.th as u64) + x as u64 / h.p.tw as u64;
        if h.p.planar == 2 {
            k += xpt * ypt * s as u64;
        }
        k as u32
    }

    /// `TIFFCheckTile`.
    fn TIFFCheckTile / vtiff_TIFFCheckTile(t: *mut c_void, x: u32, y: u32, z: u32, s: u16) -> c_int {
        let Some(h) = handle(t) else { return 0 };
        if x >= h.p.width {
            h.error(&format!("{x}: Col out of range, max {}", h.p.width - 1));
            return 0;
        }
        if y >= h.p.height {
            h.error(&format!("{y}: Row out of range, max {}", h.p.height - 1));
            return 0;
        }
        if z != 0 {
            h.error(&format!("{z}: Depth out of range, max 0"));
            return 0;
        }
        if h.p.planar == 2 && s as u32 >= h.p.spp {
            h.error(&format!("{s}: Sample out of range, max {}", h.p.spp - 1));
            return 0;
        }
        1
    }

    /// `TIFFReadEncodedStrip`: strip `s`, decoded, into `buf` (at most
    /// `size` bytes, or the whole strip for -1). The number of bytes, or -1.
    fn TIFFReadEncodedStrip / vtiff_TIFFReadEncodedStrip(t: *mut c_void, s: u32, buf: *mut c_void, size: tmsize_t) -> tmsize_t {
        let Some(h) = handle(t) else { return -1 };
        if h.p.tiled {
            h.error("Can not read strips from a tiled image");
            return -1;
        }
        read_chunk(h, s, buf, size)
    }

    /// `TIFFReadEncodedTile`.
    fn TIFFReadEncodedTile / vtiff_TIFFReadEncodedTile(t: *mut c_void, k: u32, buf: *mut c_void, size: tmsize_t) -> tmsize_t {
        let Some(h) = handle(t) else { return -1 };
        if !h.p.tiled {
            h.error("Can not read tiles from a striped image");
            return -1;
        }
        read_chunk(h, k, buf, size)
    }

    /// `TIFFReadTile`: the tile holding pixel (`x`, `y`) of sample `s`.
    fn TIFFReadTile / vtiff_TIFFReadTile(t: *mut c_void, buf: *mut c_void, x: u32, y: u32, z: u32, s: u16) -> tmsize_t {
        if vtiff_TIFFCheckTile(t, x, y, z, s) == 0 {
            return -1;
        }
        vtiff_TIFFReadEncodedTile(t, vtiff_TIFFComputeTile(t, x, y, z, s), buf, -1)
    }

    /// `TIFFReadRawStrip`: strip `s` as stored.
    fn TIFFReadRawStrip / vtiff_TIFFReadRawStrip(t: *mut c_void, s: u32, buf: *mut c_void, size: tmsize_t) -> tmsize_t {
        let Some(h) = handle(t) else { return -1 };
        if h.p.tiled {
            h.error("Can not read raw strips from a tiled image");
            return -1;
        }
        read_raw(h, s, buf, size)
    }

    /// `TIFFReadRawTile`.
    fn TIFFReadRawTile / vtiff_TIFFReadRawTile(t: *mut c_void, k: u32, buf: *mut c_void, size: tmsize_t) -> tmsize_t {
        let Some(h) = handle(t) else { return -1 };
        if !h.p.tiled {
            h.error("Can not read raw tiles from a striped image");
            return -1;
        }
        read_raw(h, k, buf, size)
    }

    /// `TIFFReadScanline`: row `row` of sample `sample` (for planar
    /// images). 1, or -1.
    fn TIFFReadScanline / vtiff_TIFFReadScanline(t: *mut c_void, buf: *mut c_void, row: u32, sample: u16) -> c_int {
        let Some(h) = handle(t) else { return -1 };
        if h.p.tiled {
            h.error("Can not read scanlines from a tiled image");
            return -1;
        }
        if row >= h.p.height {
            h.error(&format!("{row}: Row out of range, max {}", h.p.height - 1));
            return -1;
        }
        let mut s = row / h.rps_eff();
        if h.p.planar == 2 {
            if sample as u32 >= h.p.spp {
                h.error(&format!("{sample}: Sample out of range, max {}", h.p.spp));
                return -1;
            }
            s += sample as u32 * h.strips_per_plane() as u32;
        }
        let line = h.scanline() as usize;
        let at = (row % h.rps_eff()) as usize * line;
        match h.chunk(s) {
            Ok(v) => {
                core::ptr::copy_nonoverlapping(v[at..at + line].as_ptr(), buf as *mut u8, line);
                h.row = row;
                h.strip = s;
                1
            },
            Err(e) => {
                h.error(chunk_error(e));
                -1
            },
        }
    }

    /// `_TIFFmalloc`.
    fn _TIFFmalloc / vtiff__TIFFmalloc(n: tmsize_t) -> *mut c_void {
        if n <= 0 { core::ptr::null_mut() } else { malloc(n as usize) }
    }

    /// `_TIFFcalloc`.
    fn _TIFFcalloc / vtiff__TIFFcalloc(n: tmsize_t, m: tmsize_t) -> *mut c_void {
        if n <= 0 || m <= 0 { core::ptr::null_mut() } else { calloc(n as usize, m as usize) }
    }

    /// `_TIFFrealloc`.
    fn _TIFFrealloc / vtiff__TIFFrealloc(p: *mut c_void, n: tmsize_t) -> *mut c_void {
        realloc(p, n.max(0) as usize)
    }

    /// `_TIFFfree`.
    fn _TIFFfree / vtiff__TIFFfree(p: *mut c_void) -> () {
        free(p)
    }

    /// `_TIFFmemset`.
    fn _TIFFmemset / vtiff__TIFFmemset(p: *mut c_void, v: c_int, n: tmsize_t) -> () {
        core::ptr::write_bytes(p as *mut u8, v as u8, n.max(0) as usize)
    }

    /// `_TIFFmemcpy`.
    fn _TIFFmemcpy / vtiff__TIFFmemcpy(d: *mut c_void, s: *const c_void, n: tmsize_t) -> () {
        core::ptr::copy(s as *const u8, d as *mut u8, n.max(0) as usize)
    }

    /// `_TIFFmemcmp`.
    fn _TIFFmemcmp / vtiff__TIFFmemcmp(a: *const c_void, b: *const c_void, n: tmsize_t) -> c_int {
        let n = n.max(0) as usize;
        let (a, b) = (core::slice::from_raw_parts(a as *const u8, n), core::slice::from_raw_parts(b as *const u8, n));
        match a.cmp(b) {
            core::cmp::Ordering::Less => -1,
            core::cmp::Ordering::Equal => 0,
            core::cmp::Ordering::Greater => 1,
        }
    }

    /// `TIFFSwabShort`.
    fn TIFFSwabShort / vtiff_TIFFSwabShort(p: *mut u16) -> () {
        *p = (*p).swap_bytes()
    }

    /// `TIFFSwabLong`.
    fn TIFFSwabLong / vtiff_TIFFSwabLong(p: *mut u32) -> () {
        *p = (*p).swap_bytes()
    }

    /// `TIFFSwabArrayOfShort`.
    fn TIFFSwabArrayOfShort / vtiff_TIFFSwabArrayOfShort(p: *mut u16, n: tmsize_t) -> () {
        for i in 0..n.max(0) as usize {
            *p.add(i) = (*p.add(i)).swap_bytes();
        }
    }

    /// `TIFFSwabArrayOfLong`.
    fn TIFFSwabArrayOfLong / vtiff_TIFFSwabArrayOfLong(p: *mut u32, n: tmsize_t) -> () {
        for i in 0..n.max(0) as usize {
            *p.add(i) = (*p.add(i)).swap_bytes();
        }
    }

    /// `TIFFReverseBits`.
    fn TIFFReverseBits / vtiff_TIFFReverseBits(p: *mut u8, n: tmsize_t) -> () {
        for i in 0..n.max(0) as usize {
            *p.add(i) = (*p.add(i)).reverse_bits();
        }
    }
}

/// `TIFFFdOpen` (Unix), for reading: the whole file is read from `fd` now,
/// and `TIFFClose` closes `fd`.
#[cfg(unix)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtiff_TIFFFdOpen(fd: c_int, name: *const c_char, mode: *const c_char) -> *mut c_void {
    use std::io::{Read, Seek, SeekFrom};
    use std::os::unix::io::{FromRawFd, IntoRawFd};
    let name = if name.is_null() { c"" } else { CStr::from_ptr(name) };
    if !read_only(mode) {
        report(false, core::ptr::null_mut(), name, "verilith-tiff opens files for reading only");
        return core::ptr::null_mut();
    }
    let mut f = std::fs::File::from_raw_fd(fd);
    let mut data = Vec::new();
    let ok = f.seek(SeekFrom::Start(0)).is_ok() && f.read_to_end(&mut data).is_ok();
    let fd = f.into_raw_fd();
    if !ok {
        report(false, core::ptr::null_mut(), name, "Cannot read file");
        return core::ptr::null_mut();
    }
    open_bytes(name, mode, data, core::ptr::null_mut(), None, None, fd)
}

#[cfg(all(unix, feature = "tiff-abi"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn TIFFFdOpen(fd: c_int, name: *const c_char, mode: *const c_char) -> *mut c_void {
    vtiff_TIFFFdOpen(fd, name, mode)
}

unsafe fn read_chunk(h: &mut Handle, k: u32, buf: *mut c_void, size: tmsize_t) -> tmsize_t {
    if k >= h.chunks() {
        h.error(&format!("{k}: {} out of range, max {}", if h.p.tiled { "Tile" } else { "Strip" }, h.chunks()));
        return -1;
    }
    let tiled = h.p.tiled;
    match h.chunk(k) {
        Ok(v) => {
            let n = if size < 0 { v.len() } else { (size as usize).min(v.len()) };
            core::ptr::copy_nonoverlapping(v.as_ptr(), buf as *mut u8, n);
            if tiled { h.tile = k } else { h.strip = k }
            n as tmsize_t
        },
        Err(e) => {
            h.error(chunk_error(e));
            -1
        },
    }
}

unsafe fn read_raw(h: &mut Handle, k: u32, buf: *mut c_void, size: tmsize_t) -> tmsize_t {
    let (Some(&o), Some(&c)) = (h.offsets.get(k as usize), h.counts.get(k as usize)) else {
        h.error(&format!("{k}: out of range, max {}", h.chunks()));
        return -1;
    };
    let n = if size < 0 { c } else { c.min(size as u64) };
    match h.data.get(o as usize..(o + n) as usize) {
        Some(s) => {
            core::ptr::copy_nonoverlapping(s.as_ptr(), buf as *mut u8, s.len());
            s.len() as tmsize_t
        },
        None => {
            h.error(&format!("Read error on strip {k}"));
            -1
        },
    }
}

// ---------------------------------------------------------------------------
// TIFFGetField (called from capi/tiffshim.c)
// ---------------------------------------------------------------------------

/// How many pointers `TIFFGetField` takes for `tag`.
#[unsafe(no_mangle)]
pub extern "C" fn vtiff_field_args(tag: u32) -> c_int {
    match tag {
        320 => 3,
        338 | 297 | 34675 | 700 | 33723 | 34377 | 530 | 336 | 321 => 2,
        _ => 1,
    }
}

/// `TIFFGetField` (and, with `defaulted`, `TIFFGetFieldDefaulted`): 1 with
/// the field's value written through `a` (and `b`, `c`), or 0.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtiff_get_field(t: *mut c_void, tag: u32, a: *mut c_void, b: *mut c_void, c: *mut c_void, defaulted: c_int) -> c_int {
    let Some(h) = handle(t) else { return 0 };
    if a.is_null() {
        return 0;
    }
    let d = defaulted != 0;
    let t16 = tag as u16;
    let has = tag <= 0xffff && h.present(t16);
    let put16 = |v: u32| *(a as *mut u16) = v as u16;
    let put32 = |v: u32| *(a as *mut u32) = v;
    let p = &h.p;
    match tag {
        256 => put32(p.width),
        257 => put32(p.height),
        258 if has || d => put16(p.bps),
        259 => put16(p.compression),
        262 => put16(p.photometric),
        266 if has || d => put16(h.short(266).unwrap_or(1)),
        274 if h.orientation().is_some() || d => put16(h.orientation().unwrap_or(1)),
        277 if has || d => put16(p.spp),
        278 if has || d => put32(p.rps),
        280 if has || d => put16(h.short(280).unwrap_or(0)),
        281 if has || d => put16(h.short(281).unwrap_or(if p.bps <= 16 { (1u32 << p.bps) - 1 } else { 65535 })),
        282 | 283 | 286 | 287 => {
            let Some(v) = h.rational(t16) else { return 0 };
            *(a as *mut f32) = v;
        },
        284 => put16(p.planar),
        296 if has || d => put16(h.short(296).unwrap_or(2)),
        317 => {
            if !matches!(p.compression, 5 | 8) {
                if d {
                    put16(0);
                }
                return 0;
            }
            if !has && !d {
                return 0;
            }
            put16(h.short(317).unwrap_or(1));
        },
        322 if p.tiled => put32(p.tw),
        323 if p.tiled => put32(p.th),
        339 if has || d => put16(p.sample_format),
        254 if has || d => put32(h.uint(254).unwrap_or(0)),
        273 | 279 | 324 | 325 => {
            let tiled_tag = tag >= 324;
            if tiled_tag != p.tiled && !has {
                return 0;
            }
            let v = if tag == 279 || tag == 325 { &h.counts } else { &h.offsets };
            *(a as *mut *const u64) = v.as_ptr();
        },
        320 => {
            let Some(m) = &h.cmap else { return 0 };
            if b.is_null() || c.is_null() {
                return 0;
            }
            *(a as *mut *const u16) = m[0].as_ptr();
            *(b as *mut *const u16) = m[1].as_ptr();
            *(c as *mut *const u16) = m[2].as_ptr();
        },
        338 if has || d => {
            if b.is_null() {
                return 0;
            }
            put16(h.extra.len() as u32);
            *(b as *mut *const u16) = if h.extra.is_empty() { core::ptr::null() } else { h.extra.as_ptr() };
        },
        297 if has => {
            let Ok(Some(f)) = field_exec(&h.data, h.le(), h.ifd, h.n, 297) else { return 0 };
            if f.count < 2 || b.is_null() {
                return 0;
            }
            put16(value_exec(&h.data, h.le(), f, 0));
            *(b as *mut u16) = value_exec(&h.data, h.le(), f, 1) as u16;
        },
        34675 | 700 | 33723 | 34377 => {
            let Some((_, v)) = h.blobs.iter().find(|(x, _)| *x == tag) else { return 0 };
            if b.is_null() {
                return 0;
            }
            put32(v.len() as u32);
            *(b as *mut *const u8) = v.as_ptr();
        },
        269 | 270 | 271 | 272 | 285 | 305 | 306 | 315 | 316 | 33432 => {
            let Some((_, s)) = h.strings.iter().find(|(x, _)| *x == tag) else { return 0 };
            *(a as *mut *const c_char) = s.as_ptr();
        },
        _ => return 0,
    }
    1
}

/// `TIFFSetField`: the file is open for reading only. libtiff's readers
/// use it to set codec options (`TIFFTAG_JPEGCOLORMODE`, ...); those are
/// accepted and ignored, the rest refused.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtiff_set_field(t: *mut c_void, tag: u32) -> c_int {
    let Some(h) = handle(t) else { return 0 };
    // Pseudo-tags (65536 on) are codec options.
    if tag >= 65536 {
        return 1;
    }
    h.error(&format!("Cannot set tag {tag}: verilith-tiff opens files for reading only"));
    0
}

// ---------------------------------------------------------------------------
// TIFFReadRGBAImage
// ---------------------------------------------------------------------------

const EXTRASAMPLE_ASSOCALPHA: u16 = 1;
const EXTRASAMPLE_UNASSALPHA: u16 = 2;

/// What `TIFFRGBAImageBegin` works out: the alpha channel (its kind, and
/// which sample it is), and whether the image can be converted.
struct Rgba {
    alpha: u16,
    ai: u64,
    photometric: u32,
}

/// libtiff's `TIFFRGBAImageOK`, check for check.
fn rgba_ok(h: &Handle) -> Result<u32, String> {
    let p = &h.p;
    if !matches!(p.bps, 1 | 2 | 4 | 8 | 16) {
        return Err(format!("Sorry, can not handle images with {}-bit samples", p.bps));
    }
    if p.sample_format == 3 {
        return Err("Sorry, can not handle images with IEEE floating-point samples".into());
    }
    let colour = p.spp as i64 - h.extra.len() as i64;
    let photometric = p.photometric;
    match photometric {
        0 | 1 | 3 => {
            if p.planar == 1 && p.spp != 1 && p.bps < 8 {
                return Err(format!(
                    "Sorry, can not handle contiguous data with PhotometricInterpretation={photometric}, and Samples/pixel={} and Bits/Sample={}",
                    p.spp, p.bps
                ));
            }
        },
        2 => {
            if colour < 3 {
                return Err(format!("Sorry, can not handle RGB image with Color channels={colour}"));
            }
        },
        5 => {
            let inkset = h.short(332).unwrap_or(1);
            if inkset != 1 {
                return Err(format!("Sorry, can not handle separated image with InkSet={inkset}"));
            }
            if p.spp < 4 {
                return Err(format!("Sorry, can not handle separated image with Samples/pixel={}", p.spp));
            }
        },
        8 => {
            if p.spp != 3 || (p.bps != 8 && p.bps != 16) {
                return Err("Sorry, can not handle CIE L*a*b* image".into());
            }
        },
        x => return Err(format!("Sorry, can not handle image with PhotometricInterpretation={x}")),
    }
    Ok(photometric)
}

/// What `TIFFRGBAImageBegin` works out (the alpha channel), and whether
/// one of the conversions here (those of `tif_getimage.c` for grey,
/// palette, RGB and CMYK images) applies.
fn rgba_begin(h: &Handle) -> Result<Rgba, String> {
    let photometric = rgba_ok(h)?;
    let p = &h.p;
    // Alpha is the first extra sample that ExtraSamples says is alpha
    // ("1 = Associated alpha data", "2 = Unassociated alpha data"); extra
    // samples are "the last components" of a pixel. "0 = Unspecified data"
    // is not alpha, and neither is a sample ExtraSamples does not describe.
    let colours: u64 = if photometric == 2 { 3 } else { 1 };
    let (alpha, ai) = h
        .extra
        .iter()
        .enumerate()
        .find(|(_, v)| matches!(**v, EXTRASAMPLE_ASSOCALPHA | EXTRASAMPLE_UNASSALPHA))
        .map(|(i, v)| (*v, colours + i as u64))
        .unwrap_or((0, 0));
    // Planar images of several samples go through libtiff's
    // `PickSeparateCase`: grey as RGB, no palette, CMYK of exactly 4.
    let separate = p.planar == 2 && p.spp > 1;
    let ok = match (photometric, separate) {
        (0 | 1, false) => true,
        (0 | 1, true) => p.bps == 8 || p.bps == 16,
        (3, false) => h.cmap.is_some() && p.bps <= 8,
        (3, true) => false,
        (2, _) => p.bps == 8 || p.bps == 16,
        (5, false) => p.bps == 8,
        (5, true) => p.bps == 8 && p.spp == 4,
        _ => false,
    };
    if photometric == 3 && h.cmap.is_none() {
        return Err("Missing required \"Colormap\" tag".into());
    }
    if !ok {
        return Err("Can not handle format".into());
    }
    Ok(Rgba { alpha, ai, photometric })
}

/// The colour of pixel (`x`, `y`), from the decoded image (all planes):
/// what `tif_getimage.c`'s put routines give.
struct Conv<'a> {
    px: &'a [u8],
    h: &'a Handle,
    alpha: u16,
    ai: u64,
    photometric: u32,
    cmap8: Option<[Vec<u8>; 3]>,
    grey: Vec<u8>,
}

impl<'a> Conv<'a> {
    fn new(h: &'a Handle, px: &'a [u8], r: &Rgba) -> Conv<'a> {
        let p = &h.p;
        let photometric = r.photometric;
        // ColorMap values are 16-bit: "black is represented by 0,0,0 and
        // white is represented by 65535, 65535, 65535" (§5).
        let cmap8 = h.cmap.as_ref().map(|m| {
            let f = |c: &Vec<u16>| c.iter().map(|&v| (v >> 8) as u8).collect::<Vec<u8>>();
            [f(&m[0]), f(&m[1]), f(&m[2])]
        });
        let range: u32 = if p.bps == 16 { 255 } else { (1 << p.bps) - 1 };
        let grey = (0..=range).map(|x| if photometric == 0 { ((range - x) * 255 / range) as u8 } else { (x * 255 / range) as u8 }).collect();
        Conv { px, h, alpha: r.alpha, ai: r.ai, photometric, cmap8, grey }
    }

    /// Sample `s` of pixel (`x`, `y`): its raw value (16-bit samples are
    /// little-endian in the decoded image).
    fn sample(&self, x: u64, y: u64, s: u64) -> u32 {
        let p = &self.h.p;
        let bps = p.bps as u64;
        let rb = self.h.scanline();
        let (base, idx) = if p.planar == 2 {
            (s * p.height as u64 * rb + y * rb, x)
        } else {
            (y * rb, x * p.spp as u64 + s)
        };
        match bps {
            8 => self.px[(base + idx) as usize] as u32,
            16 => {
                let i = (base + 2 * idx) as usize;
                self.px[i] as u32 | (self.px[i + 1] as u32) << 8
            },
            _ => {
                let bit = idx * bps;
                let byte = self.px[(base + bit / 8) as usize] as u32;
                (byte >> (8 - bps - bit % 8)) & ((1 << bps) - 1)
            },
        }
    }

    fn b16(v: u32) -> u32 {
        (v + 128) / 257
    }

    fn ua(v: u32, a: u32) -> u32 {
        (v * a + 127) / 255
    }

    fn pixel(&self, x: u64, y: u64) -> u32 {
        let p = &self.h.p;
        let pack = |r: u32, g: u32, b: u32, a: u32| r | g << 8 | b << 16 | a << 24;
        if p.planar == 2 && p.spp > 1 && matches!(self.photometric, 0 | 1) {
            // libtiff's gtStripSeparate: grey as RGB, from the sample as it
            // is, with the alpha plane after it.
            let c = |v: u32| if p.bps == 16 { Self::b16(v) } else { v };
            let v = c(self.sample(x, y, 0));
            return match self.alpha {
                EXTRASAMPLE_ASSOCALPHA => pack(v, v, v, c(self.sample(x, y, self.ai))),
                EXTRASAMPLE_UNASSALPHA => {
                    let a = c(self.sample(x, y, self.ai));
                    let u = Self::ua(v, a);
                    pack(u, u, u, a)
                },
                _ => pack(v, v, v, 255),
            };
        }
        match self.photometric {
            0 | 1 => {
                let v = self.sample(x, y, 0);
                let g = self.grey[if p.bps == 16 { (v >> 8) as usize } else { v as usize }] as u32;
                if p.bps == 8 && self.alpha != 0 {
                    pack(g, g, g, self.sample(x, y, self.ai))
                } else {
                    pack(g, g, g, 255)
                }
            },
            3 => {
                let v = self.sample(x, y, 0) as usize;
                let m = self.cmap8.as_ref().unwrap();
                pack(m[0][v] as u32, m[1][v] as u32, m[2][v] as u32, 255)
            },
            2 => {
                let (r, g, b) = (self.sample(x, y, 0), self.sample(x, y, 1), self.sample(x, y, 2));
                let wide = p.bps == 16;
                let c = |v: u32| if wide { Self::b16(v) } else { v };
                match self.alpha {
                    EXTRASAMPLE_ASSOCALPHA => pack(c(r), c(g), c(b), c(self.sample(x, y, self.ai))),
                    EXTRASAMPLE_UNASSALPHA => {
                        let a = c(self.sample(x, y, self.ai));
                        pack(Self::ua(c(r), a), Self::ua(c(g), a), Self::ua(c(b), a), a)
                    },
                    _ => pack(c(r), c(g), c(b), 255),
                }
            },
            _ => {
                let k = 255 - self.sample(x, y, 3);
                let f = |v: u32| (k * (255 - v)) / 255;
                pack(f(self.sample(x, y, 0)), f(self.sample(x, y, 1)), f(self.sample(x, y, 2)), 255)
            },
        }
    }
}

/// libtiff's `setorientation`: which flips take the file's orientation to
/// the one asked for. Bit 0: vertically; bit 1: horizontally.
fn flips(file: u32, req: u32) -> u32 {
    let group = |o: u32| match o {
        2 | 6 => 1,
        3 | 7 => 2,
        4 | 8 => 3,
        _ => 0,
    };
    // Each orientation as (flipped vertically, flipped horizontally) from
    // top-left.
    let bits = |g: u32| match g {
        1 => (false, true),
        2 => (true, true),
        3 => (true, false),
        _ => (false, false),
    };
    let (fv, fh) = bits(group(file));
    let (rv, rh) = bits(group(req));
    ((fv != rv) as u32) | (((fh != rh) as u32) << 1)
}

/// Converts the region of `w` x `h` pixels at (`col`, `row`) to RGBA into
/// `raster` (rows of `stride`), in orientation `req`, as libtiff's
/// `TIFFRGBAImageGet` does.
unsafe fn rgba_region(t: *mut c_void, col: u32, row: u32, w: u32, h: u32, raster: *mut u32, stride: u32, req: u32) -> c_int {
    let Some(hd) = handle(t) else { return 0 };
    let r = match rgba_begin(hd) {
        Ok(r) => r,
        Err(m) => {
            hd.error(&m);
            return 0;
        },
    };
    let img = match crate::decode::decode(&hd.data, usize::MAX) {
        Ok(i) => i,
        Err(e) => {
            hd.error(chunk_error(e));
            return 0;
        },
    };
    let c = Conv::new(hd, &img.pixels, &r);
    let f = flips(hd.orientation().unwrap_or(1), req);
    for yy in 0..h {
        let ty = if f & 1 != 0 { h - 1 - yy } else { yy };
        for xx in 0..w {
            let tx = if f & 2 != 0 { w - 1 - xx } else { xx };
            *raster.add(ty as usize * stride as usize + tx as usize) = c.pixel((col + xx) as u64, (row + yy) as u64);
        }
    }
    1
}

api! {
    /// `TIFFRGBAImageOK`: 1 if `TIFFReadRGBAImage` can convert the image,
    /// else 0 with why in `emsg` (1024 bytes).
    fn TIFFRGBAImageOK / vtiff_TIFFRGBAImageOK(t: *mut c_void, emsg: *mut c_char) -> c_int {
        let Some(h) = handle(t) else { return 0 };
        match rgba_ok(h) {
            Ok(_) => 1,
            Err(m) => {
                if !emsg.is_null() {
                    let b = m.as_bytes();
                    let n = b.len().min(1023);
                    core::ptr::copy_nonoverlapping(b.as_ptr(), emsg as *mut u8, n);
                    *emsg.add(n) = 0;
                }
                0
            },
        }
    }

    /// `TIFFReadRGBAImageOriented`: the image in RGBA (red in the low
    /// byte) into a `rwidth` x `rheight` raster, in orientation `req`. The
    /// raster must be at least as tall as the image (libtiff would write
    /// before it otherwise); only the image's columns are written.
    fn TIFFReadRGBAImageOriented / vtiff_TIFFReadRGBAImageOriented(t: *mut c_void, rwidth: u32, rheight: u32, raster: *mut u32, req: c_int, _stop: c_int) -> c_int {
        let Some(h) = handle(t) else { return 0 };
        let (w, ih) = (h.p.width, h.p.height);
        if rheight < ih {
            h.error("Raster is shorter than the image");
            return 0;
        }
        let base = raster.add((rheight - ih) as usize * rwidth as usize);
        rgba_region(t, 0, 0, w.min(rwidth), ih, base, rwidth, req as u32)
    }

    /// `TIFFReadRGBAImage`: as `TIFFReadRGBAImageOriented`, bottom row
    /// first (`ORIENTATION_BOTLEFT`).
    fn TIFFReadRGBAImage / vtiff_TIFFReadRGBAImage(t: *mut c_void, rwidth: u32, rheight: u32, raster: *mut u32, stop: c_int) -> c_int {
        vtiff_TIFFReadRGBAImageOriented(t, rwidth, rheight, raster, 4, stop)
    }

    /// `TIFFReadRGBAStrip`: the strip that starts at `row`, in RGBA,
    /// bottom row first, into a raster of the image's width.
    fn TIFFReadRGBAStrip / vtiff_TIFFReadRGBAStrip(t: *mut c_void, row: u32, raster: *mut u32) -> c_int {
        vtiff_TIFFReadRGBAStripExt(t, row, raster, 0)
    }

    /// `TIFFReadRGBAStripExt`.
    fn TIFFReadRGBAStripExt / vtiff_TIFFReadRGBAStripExt(t: *mut c_void, row: u32, raster: *mut u32, _stop: c_int) -> c_int {
        let Some(h) = handle(t) else { return 0 };
        if h.p.tiled {
            h.error("Can't use TIFFReadRGBAStrip() with tiled file.");
            return 0;
        }
        let rps = h.rps_eff();
        if row % rps != 0 {
            h.error("Row passed to TIFFReadRGBAStrip() must be first in a strip.");
            return 0;
        }
        if row >= h.p.height {
            return 0;
        }
        let n = (h.p.height - row).min(rps);
        let w = h.p.width;
        rgba_region(t, 0, row, w, n, raster, w, 4)
    }

    /// `TIFFReadRGBATile`: the tile whose top left is (`col`, `row`), in
    /// RGBA, bottom row first, into a tile-sized raster (zero outside the
    /// image).
    fn TIFFReadRGBATile / vtiff_TIFFReadRGBATile(t: *mut c_void, col: u32, row: u32, raster: *mut u32) -> c_int {
        vtiff_TIFFReadRGBATileExt(t, col, row, raster, 0)
    }

    /// `TIFFReadRGBATileExt`.
    fn TIFFReadRGBATileExt / vtiff_TIFFReadRGBATileExt(t: *mut c_void, col: u32, row: u32, raster: *mut u32, _stop: c_int) -> c_int {
        let Some(h) = handle(t) else { return 0 };
        if !h.p.tiled {
            h.error("Can't use TIFFReadRGBATile() with striped file.");
            return 0;
        }
        let (tw, th) = (h.p.tw, h.p.th);
        if col % tw != 0 || row % th != 0 {
            h.error("Row/col passed to TIFFReadRGBATile() must be topleft corner of a tile.");
            return 0;
        }
        if col >= h.p.width || row >= h.p.height {
            return 0;
        }
        let rh = (h.p.height - row).min(th);
        let rw = (h.p.width - col).min(tw);
        core::ptr::write_bytes(raster, 0, tw as usize * th as usize);
        // The region bottom row first, at the bottom of the tile.
        let base = raster.add((th - rh) as usize * tw as usize);
        rgba_region(t, col, row, rw, rh, base, tw, 4)
    }
}
