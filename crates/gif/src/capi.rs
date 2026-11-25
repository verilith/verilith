//! giflib's decoding API (giflib 5.2, `gif_lib.h`): the same functions,
//! structs and memory rules, over the verified decoder.
//!
//! This file is trusted glue, not verified. `DGifSlurp` runs the verified
//! decoder (`decode::decode`) on the whole file; the record-by-record API
//! (`DGifGetRecordType`, `DGifGetImageDesc`, `DGifGetLine`, ...) walks the
//! blocks itself and has each image decoded by the verified `image_exec`.
//! The bytes are read in full when the file is opened. Everything the
//! caller may free or reallocate (colour maps, rasters, extension blocks,
//! the `GifFileType` itself) is allocated with the C allocator, as giflib
//! does, so giflib's own helpers (`GifFreeSavedImages`, ...) and the
//! caller's `free` work on it.
//!
//! The functions are exported as `vgif_*`; with the `gif-abi` feature also
//! under giflib's names, so verilith-gif can replace giflib's decoder at
//! link time. giflib's encoder (`EGif*`) and `GifQuantizeBuffer` are not
//! provided.
#![allow(non_snake_case, unsafe_op_in_unsafe_fn, clippy::missing_safety_doc)]
use crate::decode::{decode, image_exec, screen_exec, Error, Frame};
use core::ffi::{c_char, c_int, c_uint, c_void};

unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn calloc(n: usize, m: usize) -> *mut c_void;
    fn realloc(p: *mut c_void, n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
}

pub const GIF_ERROR: c_int = 0;
pub const GIF_OK: c_int = 1;

pub const D_GIF_SUCCEEDED: c_int = 0;
pub const D_GIF_ERR_OPEN_FAILED: c_int = 101;
pub const D_GIF_ERR_READ_FAILED: c_int = 102;
pub const D_GIF_ERR_NOT_GIF_FILE: c_int = 103;
pub const D_GIF_ERR_NO_SCRN_DSCR: c_int = 104;
pub const D_GIF_ERR_NO_IMAG_DSCR: c_int = 105;
pub const D_GIF_ERR_NO_COLOR_MAP: c_int = 106;
pub const D_GIF_ERR_WRONG_RECORD: c_int = 107;
pub const D_GIF_ERR_DATA_TOO_BIG: c_int = 108;
pub const D_GIF_ERR_NOT_ENOUGH_MEM: c_int = 109;
pub const D_GIF_ERR_CLOSE_FAILED: c_int = 110;
pub const D_GIF_ERR_NOT_READABLE: c_int = 111;
pub const D_GIF_ERR_IMAGE_DEFECT: c_int = 112;
pub const D_GIF_ERR_EOF_TOO_SOON: c_int = 113;

pub const UNDEFINED_RECORD_TYPE: c_int = 0;
pub const SCREEN_DESC_RECORD_TYPE: c_int = 1;
pub const IMAGE_DESC_RECORD_TYPE: c_int = 2;
pub const EXTENSION_RECORD_TYPE: c_int = 3;
pub const TERMINATE_RECORD_TYPE: c_int = 4;

pub const CONTINUE_EXT_FUNC_CODE: c_int = 0x00;
pub const GRAPHICS_EXT_FUNC_CODE: c_int = 0xf9;
pub const NO_TRANSPARENT_COLOR: c_int = -1;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct GifColorType {
    pub Red: u8,
    pub Green: u8,
    pub Blue: u8,
}

#[repr(C)]
pub struct ColorMapObject {
    pub ColorCount: c_int,
    pub BitsPerPixel: c_int,
    pub SortFlag: bool,
    pub Colors: *mut GifColorType,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct GifImageDesc {
    pub Left: c_int,
    pub Top: c_int,
    pub Width: c_int,
    pub Height: c_int,
    pub Interlace: bool,
    pub ColorMap: *mut ColorMapObject,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct ExtensionBlock {
    pub ByteCount: c_int,
    pub Bytes: *mut u8,
    pub Function: c_int,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SavedImage {
    pub ImageDesc: GifImageDesc,
    pub RasterBits: *mut u8,
    pub ExtensionBlockCount: c_int,
    pub ExtensionBlocks: *mut ExtensionBlock,
}

#[repr(C)]
pub struct GifFileType {
    pub SWidth: c_int,
    pub SHeight: c_int,
    pub SColorResolution: c_int,
    pub SBackGroundColor: c_int,
    pub AspectByte: u8,
    pub SColorMap: *mut ColorMapObject,
    pub ImageCount: c_int,
    pub Image: GifImageDesc,
    pub SavedImages: *mut SavedImage,
    pub ExtensionBlockCount: c_int,
    pub ExtensionBlocks: *mut ExtensionBlock,
    pub Error: c_int,
    pub UserData: *mut c_void,
    pub Private: *mut c_void,
}

#[repr(C)]
pub struct GraphicsControlBlock {
    pub DisposalMode: c_int,
    pub UserInputFlag: bool,
    pub DelayTime: c_int,
    pub TransparentColor: c_int,
}

pub type InputFunc = Option<unsafe extern "C" fn(*mut GifFileType, *mut u8, c_int) -> c_int>;

/// The decoder's state behind `GifFileType::Private`.
struct Private {
    /// The whole file.
    data: Vec<u8>,
    /// Where the record-by-record API is in the file.
    pos: usize,
    /// Where the blocks start, after the screen descriptor.
    blocks: usize,
    gif89: bool,
    /// giflib's buffer for extension and code blocks: length, then bytes.
    buf: [u8; 256],
    /// The image the record API is reading.
    img: Option<Current>,
    /// Scratch space for the LZW decoder.
    off: Vec<u32>,
    len: Vec<u32>,
}

/// The image the record API is reading.
struct Current {
    /// The decoded image, or why it did not decode.
    frame: Result<Frame, Error>,
    width: usize,
    height: usize,
    interlace: bool,
    /// Pixels delivered so far, in the order of the file (pass by pass for
    /// an interlaced image).
    done: usize,
    min_code: u8,
    /// Where the image's sub-blocks start.
    data_start: usize,
    /// `DGifGetLZCodes`'s state.
    lz: Lz,
}

#[derive(Default)]
struct Lz {
    started: bool,
    running_code: u32,
    running_bits: u32,
    max_code1: u32,
    shift_state: u32,
    shift_dword: u64,
    /// The sub-block being read, and how much of it is.
    block: Vec<u8>,
    at: usize,
}

unsafe fn private<'a>(g: *mut GifFileType) -> Option<&'a mut Private> {
    if g.is_null() || (*g).Private.is_null() {
        return None;
    }
    Some(&mut *((*g).Private as *mut Private))
}

unsafe fn set_err(e: *mut c_int, v: c_int) {
    if !e.is_null() {
        *e = v;
    }
}

// ---------------------------------------------------------------------------
// gifalloc.c
// ---------------------------------------------------------------------------

macro_rules! api {
    ($( $(#[$m:meta])* fn $name:ident / $v:ident ( $($a:ident : $t:ty),* $(,)? ) -> $r:ty $body:block )*) => {
        $(
            $(#[$m])*
            #[unsafe(no_mangle)]
            pub unsafe extern "C" fn $v($($a: $t),*) -> $r $body

            $(#[$m])*
            #[cfg(feature = "gif-abi")]
            #[unsafe(no_mangle)]
            pub unsafe extern "C" fn $name($($a: $t),*) -> $r {
                $v($($a),*)
            }
        )*
    };
}

fn bit_size(n: c_int) -> c_int {
    let mut i = 1;
    while i <= 8 {
        if (1 << i) >= n {
            break;
        }
        i += 1;
    }
    i
}

unsafe fn free_extensions(count: *mut c_int, blocks: *mut *mut ExtensionBlock) {
    if (*blocks).is_null() {
        return;
    }
    for i in 0..(*count).max(0) as usize {
        free((*(*blocks).add(i)).Bytes as *mut c_void);
    }
    free(*blocks as *mut c_void);
    *blocks = core::ptr::null_mut();
    *count = 0;
}

unsafe fn add_extension(count: *mut c_int, blocks: *mut *mut ExtensionBlock, function: c_int, data: &[u8]) -> c_int {
    let n = (*count).max(0) as usize + 1;
    let p = realloc(*blocks as *mut c_void, n * core::mem::size_of::<ExtensionBlock>()) as *mut ExtensionBlock;
    if p.is_null() {
        return GIF_ERROR;
    }
    *blocks = p;
    let ep = &mut *p.add(n - 1);
    *count = n as c_int;
    ep.Function = function;
    ep.ByteCount = data.len() as c_int;
    ep.Bytes = malloc(data.len().max(1)) as *mut u8;
    if ep.Bytes.is_null() {
        return GIF_ERROR;
    }
    core::ptr::copy_nonoverlapping(data.as_ptr(), ep.Bytes, data.len());
    GIF_OK
}

/// A colour map of `table` (3 bytes per entry), as giflib makes them.
unsafe fn map_of(table: &[u8], sorted: bool) -> *mut ColorMapObject {
    let n = (table.len() / 3) as c_int;
    let m = vgif_GifMakeMapObject(n, table.as_ptr() as *const GifColorType);
    if !m.is_null() {
        (*m).SortFlag = sorted;
    }
    m
}

api! {
    /// `GifBitSize`.
    fn GifBitSize / vgif_GifBitSize(n: c_int) -> c_int {
        bit_size(n)
    }

    /// `GifMakeMapObject`: `NULL` unless `count` is a power of 2 up to 256.
    fn GifMakeMapObject / vgif_GifMakeMapObject(count: c_int, map: *const GifColorType) -> *mut ColorMapObject {
        if count != 1 << bit_size(count) {
            return core::ptr::null_mut();
        }
        let o = malloc(core::mem::size_of::<ColorMapObject>()) as *mut ColorMapObject;
        if o.is_null() {
            return o;
        }
        let colors = calloc(count as usize, core::mem::size_of::<GifColorType>()) as *mut GifColorType;
        if colors.is_null() {
            free(o as *mut c_void);
            return core::ptr::null_mut();
        }
        if !map.is_null() {
            core::ptr::copy_nonoverlapping(map, colors, count as usize);
        }
        o.write(ColorMapObject { ColorCount: count, BitsPerPixel: bit_size(count), SortFlag: false, Colors: colors });
        o
    }

    /// `GifFreeMapObject`.
    fn GifFreeMapObject / vgif_GifFreeMapObject(o: *mut ColorMapObject) -> () {
        if !o.is_null() {
            free((*o).Colors as *mut c_void);
            free(o as *mut c_void);
        }
    }

    /// `GifUnionColorMap`: the colours of both maps, and where those of the
    /// second went.
    fn GifUnionColorMap / vgif_GifUnionColorMap(a: *const ColorMapObject, b: *const ColorMapObject, trans: *mut u8) -> *mut ColorMapObject {
        if a.is_null() || b.is_null() {
            return core::ptr::null_mut();
        }
        let (a, b) = (&*a, &*b);
        let u = vgif_GifMakeMapObject(a.ColorCount.max(b.ColorCount) * 2, core::ptr::null());
        if u.is_null() {
            return u;
        }
        let ca = core::slice::from_raw_parts(a.Colors, a.ColorCount as usize);
        let cb = core::slice::from_raw_parts(b.Colors, b.ColorCount as usize);
        let cu = core::slice::from_raw_parts_mut((*u).Colors, (*u).ColorCount as usize);
        cu[..ca.len()].copy_from_slice(ca);
        let mut slot = ca.len();
        while slot > 0 && { let c = ca[slot - 1]; c.Red == 0 && c.Green == 0 && c.Blue == 0 } {
            slot -= 1;
        }
        let mut i = 0;
        while i < cb.len() && slot <= 256 {
            let c = cb[i];
            match ca.iter().position(|x| x.Red == c.Red && x.Green == c.Green && x.Blue == c.Blue) {
                Some(j) => *trans.add(i) = j as u8,
                None => {
                    if slot < cu.len() {
                        cu[slot] = c;
                    }
                    *trans.add(i) = slot as u8;
                    slot += 1;
                }
            }
            i += 1;
        }
        if slot > 256 {
            vgif_GifFreeMapObject(u);
            return core::ptr::null_mut();
        }
        let bits = bit_size(slot as c_int);
        let round = 1usize << bits;
        for c in cu.iter_mut().take(round).skip(slot) {
            *c = GifColorType { Red: 0, Green: 0, Blue: 0 };
        }
        if round < cu.len() {
            let p = realloc((*u).Colors as *mut c_void, round * 3) as *mut GifColorType;
            if p.is_null() {
                vgif_GifFreeMapObject(u);
                return core::ptr::null_mut();
            }
            (*u).Colors = p;
        }
        (*u).ColorCount = round as c_int;
        (*u).BitsPerPixel = bits;
        u
    }

    /// `GifApplyTranslation`.
    fn GifApplyTranslation / vgif_GifApplyTranslation(img: *mut SavedImage, trans: *const u8) -> () {
        let d = &(*img).ImageDesc;
        let n = (d.Width.max(0) as usize) * (d.Height.max(0) as usize);
        for i in 0..n {
            let p = (*img).RasterBits.add(i);
            *p = *trans.add(*p as usize);
        }
    }

    /// `GifAddExtensionBlock`.
    fn GifAddExtensionBlock / vgif_GifAddExtensionBlock(count: *mut c_int, blocks: *mut *mut ExtensionBlock, function: c_int, len: c_uint, data: *mut u8) -> c_int {
        let n = len as usize;
        let p = malloc(n.max(1)) as *mut u8;
        if p.is_null() {
            return GIF_ERROR;
        }
        if !data.is_null() {
            core::ptr::copy_nonoverlapping(data, p, n);
        }
        let r = add_extension(count, blocks, function, core::slice::from_raw_parts(p, n));
        free(p as *mut c_void);
        r
    }

    /// `GifFreeExtensions`.
    fn GifFreeExtensions / vgif_GifFreeExtensions(count: *mut c_int, blocks: *mut *mut ExtensionBlock) -> () {
        free_extensions(count, blocks)
    }

    /// `GifMakeSavedImage`: a new last image, a copy of `from` (whose
    /// extension blocks' bytes are shared, as in giflib) or zeroed.
    fn GifMakeSavedImage / vgif_GifMakeSavedImage(g: *mut GifFileType, from: *const SavedImage) -> *mut SavedImage {
        let n = (*g).ImageCount.max(0) as usize + 1;
        let p = realloc((*g).SavedImages as *mut c_void, n * core::mem::size_of::<SavedImage>()) as *mut SavedImage;
        if p.is_null() {
            return p;
        }
        (*g).SavedImages = p;
        (*g).ImageCount = n as c_int;
        let sp = p.add(n - 1);
        if from.is_null() {
            core::ptr::write_bytes(sp, 0, 1);
            return sp;
        }
        let f = &*from;
        sp.write(*f);
        (*sp).ImageDesc.ColorMap = core::ptr::null_mut();
        (*sp).RasterBits = core::ptr::null_mut();
        (*sp).ExtensionBlocks = core::ptr::null_mut();
        (*sp).ExtensionBlockCount = 0;
        if !f.ImageDesc.ColorMap.is_null() {
            let m = &*f.ImageDesc.ColorMap;
            (*sp).ImageDesc.ColorMap = vgif_GifMakeMapObject(m.ColorCount, m.Colors);
            if (*sp).ImageDesc.ColorMap.is_null() {
                free_last(g);
                return core::ptr::null_mut();
            }
        }
        let size = (f.ImageDesc.Width.max(0) as usize) * (f.ImageDesc.Height.max(0) as usize);
        (*sp).RasterBits = malloc(size.max(1)) as *mut u8;
        if (*sp).RasterBits.is_null() {
            free_last(g);
            return core::ptr::null_mut();
        }
        if !f.RasterBits.is_null() {
            core::ptr::copy_nonoverlapping(f.RasterBits, (*sp).RasterBits, size);
        }
        if !f.ExtensionBlocks.is_null() {
            let k = f.ExtensionBlockCount.max(0) as usize;
            let e = malloc((k * core::mem::size_of::<ExtensionBlock>()).max(1)) as *mut ExtensionBlock;
            if e.is_null() {
                free_last(g);
                return core::ptr::null_mut();
            }
            core::ptr::copy_nonoverlapping(f.ExtensionBlocks, e, k);
            (*sp).ExtensionBlocks = e;
            (*sp).ExtensionBlockCount = k as c_int;
        }
        sp
    }

    /// `GifFreeSavedImages`.
    fn GifFreeSavedImages / vgif_GifFreeSavedImages(g: *mut GifFileType) -> () {
        if g.is_null() || (*g).SavedImages.is_null() {
            return;
        }
        for i in 0..(*g).ImageCount.max(0) as usize {
            free_saved((*g).SavedImages.add(i));
        }
        free((*g).SavedImages as *mut c_void);
        (*g).SavedImages = core::ptr::null_mut();
    }

    /// `GifErrorString`: giflib's message for an error code, or `NULL`.
    fn GifErrorString / vgif_GifErrorString(code: c_int) -> *const c_char {
        let s: &'static [u8] = match code {
            1 | 101 => b"Failed to open given file\0",
            2 => b"Failed to write to given file\0",
            3 => b"Screen descriptor has already been set\0",
            4 => b"Image descriptor is still active\0",
            5 | 106 => b"Neither global nor local color map\0",
            6 | 108 => b"Number of pixels bigger than width * height\0",
            7 | 109 => b"Failed to allocate required memory\0",
            8 => b"Write failed (disk full?)\0",
            9 | 110 => b"Failed to close given file\0",
            10 => b"Given file was not opened for write\0",
            102 => b"Failed to read from given file\0",
            103 => b"Data is not in GIF format\0",
            104 => b"No screen descriptor detected\0",
            105 => b"No Image Descriptor detected\0",
            107 => b"Wrong record type detected\0",
            111 => b"Given file was not opened for read\0",
            112 => b"Image is defective, decoding aborted\0",
            113 => b"Image EOF detected before image complete\0",
            _ => return core::ptr::null(),
        };
        s.as_ptr() as *const c_char
    }
}

unsafe fn free_saved(sp: *mut SavedImage) {
    vgif_GifFreeMapObject((*sp).ImageDesc.ColorMap);
    (*sp).ImageDesc.ColorMap = core::ptr::null_mut();
    free((*sp).RasterBits as *mut c_void);
    (*sp).RasterBits = core::ptr::null_mut();
    free_extensions(&mut (*sp).ExtensionBlockCount, &mut (*sp).ExtensionBlocks);
}

unsafe fn free_last(g: *mut GifFileType) {
    if (*g).SavedImages.is_null() || (*g).ImageCount <= 0 {
        return;
    }
    (*g).ImageCount -= 1;
    free_saved((*g).SavedImages.add((*g).ImageCount as usize));
}

// ---------------------------------------------------------------------------
// Opening and closing
// ---------------------------------------------------------------------------

/// A new `GifFileType` for the bytes `data`, read through its screen
/// descriptor as `DGifOpen` does, or `NULL` with `*err` set.
unsafe fn open_bytes(g: *mut GifFileType, data: Vec<u8>, err: *mut c_int) -> *mut GifFileType {
    let fail = |g: *mut GifFileType, code: c_int| {
        set_err(err, code);
        free(g as *mut c_void);
        core::ptr::null_mut()
    };
    if data.len() < 6 {
        return fail(g, D_GIF_ERR_READ_FAILED);
    }
    if &data[..3] != b"GIF" {
        return fail(g, D_GIF_ERR_NOT_GIF_FILE);
    }
    let (s, blocks) = match screen_exec(&data) {
        Some(x) => x,
        None => return fail(g, D_GIF_ERR_READ_FAILED),
    };
    (*g).SWidth = s.width as c_int;
    (*g).SHeight = s.height as c_int;
    (*g).SColorResolution = ((((s.flags & 0x70) as c_int) + 1) >> 4) + 1;
    (*g).SBackGroundColor = s.bg as c_int;
    (*g).AspectByte = s.aspect;
    (*g).SColorMap = core::ptr::null_mut();
    if let Some(t) = &s.gct {
        (*g).SColorMap = map_of(t, s.flags & 0x08 != 0);
        if (*g).SColorMap.is_null() {
            return fail(g, D_GIF_ERR_NOT_ENOUGH_MEM);
        }
    }
    let gif89 = data[4] == b'9';
    let p = Box::new(Private {
        data,
        pos: blocks,
        blocks,
        gif89,
        buf: [0; 256],
        img: None,
        off: vec![0; 4096],
        len: vec![0; 4096],
    });
    (*g).Private = Box::into_raw(p) as *mut c_void;
    (*g).Error = 0;
    g
}

unsafe fn new_file(user: *mut c_void) -> *mut GifFileType {
    let g = calloc(1, core::mem::size_of::<GifFileType>()) as *mut GifFileType;
    if !g.is_null() {
        (*g).UserData = user;
    }
    g
}

api! {
    /// `DGifOpen`: reads the whole input through `read`, then the header and
    /// screen descriptor.
    fn DGifOpen / vgif_DGifOpen(user: *mut c_void, read: InputFunc, err: *mut c_int) -> *mut GifFileType {
        let g = new_file(user);
        if g.is_null() {
            set_err(err, D_GIF_ERR_NOT_ENOUGH_MEM);
            return g;
        }
        let Some(read) = read else {
            set_err(err, D_GIF_ERR_READ_FAILED);
            free(g as *mut c_void);
            return core::ptr::null_mut();
        };
        let mut data = Vec::new();
        let mut chunk = vec![0u8; 1 << 16];
        loop {
            let n = read(g, chunk.as_mut_ptr(), chunk.len() as c_int);
            if n <= 0 {
                break;
            }
            let n = (n as usize).min(chunk.len());
            data.extend_from_slice(&chunk[..n]);
        }
        open_bytes(g, data, err)
    }

    /// `DGifOpenFileName`.
    fn DGifOpenFileName / vgif_DGifOpenFileName(name: *const c_char, err: *mut c_int) -> *mut GifFileType {
        if name.is_null() {
            set_err(err, D_GIF_ERR_OPEN_FAILED);
            return core::ptr::null_mut();
        }
        let path = core::ffi::CStr::from_ptr(name);
        #[cfg(unix)]
        let path = {
            use std::os::unix::ffi::OsStrExt;
            std::path::PathBuf::from(std::ffi::OsStr::from_bytes(path.to_bytes()))
        };
        #[cfg(not(unix))]
        let path = std::path::PathBuf::from(path.to_string_lossy().into_owned());
        let data = match std::fs::read(&path) {
            Ok(d) => d,
            Err(_) => {
                set_err(err, D_GIF_ERR_OPEN_FAILED);
                return core::ptr::null_mut();
            }
        };
        let g = new_file(core::ptr::null_mut());
        if g.is_null() {
            set_err(err, D_GIF_ERR_NOT_ENOUGH_MEM);
            return g;
        }
        open_bytes(g, data, err)
    }

    /// `DGifCloseFile`: frees everything the file has, and the file.
    fn DGifCloseFile / vgif_DGifCloseFile(g: *mut GifFileType, err: *mut c_int) -> c_int {
        if g.is_null() || (*g).Private.is_null() {
            return GIF_ERROR;
        }
        vgif_GifFreeMapObject((*g).Image.ColorMap);
        (*g).Image.ColorMap = core::ptr::null_mut();
        vgif_GifFreeMapObject((*g).SColorMap);
        (*g).SColorMap = core::ptr::null_mut();
        vgif_GifFreeSavedImages(g);
        free_extensions(&mut (*g).ExtensionBlockCount, &mut (*g).ExtensionBlocks);
        drop(Box::from_raw((*g).Private as *mut Private));
        free(g as *mut c_void);
        set_err(err, D_GIF_SUCCEEDED);
        GIF_OK
    }
}

/// `DGifOpenFileHandle` (Unix): reads the whole file from `fd`, then
/// closes it, as giflib's `DGifCloseFile` would.
#[cfg(unix)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vgif_DGifOpenFileHandle(fd: c_int, err: *mut c_int) -> *mut GifFileType {
    use std::io::Read;
    use std::os::unix::io::FromRawFd;
    let mut f = std::fs::File::from_raw_fd(fd);
    let mut data = Vec::new();
    if f.read_to_end(&mut data).is_err() {
        set_err(err, D_GIF_ERR_READ_FAILED);
        return core::ptr::null_mut();
    }
    drop(f);
    let g = new_file(core::ptr::null_mut());
    if g.is_null() {
        set_err(err, D_GIF_ERR_NOT_ENOUGH_MEM);
        return g;
    }
    open_bytes(g, data, err)
}

#[cfg(all(unix, feature = "gif-abi"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn DGifOpenFileHandle(fd: c_int, err: *mut c_int) -> *mut GifFileType {
    vgif_DGifOpenFileHandle(fd, err)
}

// ---------------------------------------------------------------------------
// DGifSlurp
// ---------------------------------------------------------------------------

/// The data sub-blocks of the chain at `q`, and the position after it.
fn chain(b: &[u8], mut q: usize) -> Option<(Vec<&[u8]>, usize)> {
    let mut v = Vec::new();
    loop {
        let n = *b.get(q)? as usize;
        if n == 0 {
            return Some((v, q + 1));
        }
        v.push(b.get(q + 1..q + 1 + n)?);
        q += 1 + n;
    }
}

/// The extension blocks from `q` to the next image separator or the
/// trailer, as giflib keeps them: the first sub-block with the extension's
/// label, the others as continuations.
unsafe fn extensions(b: &[u8], mut q: usize, count: *mut c_int, blocks: *mut *mut ExtensionBlock) -> Option<()> {
    while b.get(q) == Some(&0x21) {
        let label = *b.get(q + 1)? as c_int;
        let (subs, e) = chain(b, q + 2)?;
        for (k, s) in subs.iter().enumerate() {
            let f = if k == 0 { label } else { CONTINUE_EXT_FUNC_CODE };
            if add_extension(count, blocks, f, s) != GIF_OK {
                return None;
            }
        }
        q = e;
    }
    Some(())
}

unsafe fn desc_of(f: &Frame) -> GifImageDesc {
    GifImageDesc {
        Left: f.left as c_int,
        Top: f.top as c_int,
        Width: f.width as c_int,
        Height: f.height as c_int,
        Interlace: f.flags & 0x40 != 0,
        ColorMap: match &f.lct {
            Some(t) => map_of(t, f.flags & 0x20 != 0),
            None => core::ptr::null_mut(),
        },
    }
}

fn err_code(e: Error) -> c_int {
    match e {
        Error::Invalid => D_GIF_ERR_IMAGE_DEFECT,
        Error::TooLarge => D_GIF_ERR_DATA_TOO_BIG,
        Error::OutOfMemory => D_GIF_ERR_NOT_ENOUGH_MEM,
    }
}

api! {
    /// `DGifSlurp`: decodes the whole file with the verified decoder into
    /// `SavedImages`, each with the extension blocks before it, and the
    /// extensions after the last image in `ExtensionBlocks`.
    fn DGifSlurp / vgif_DGifSlurp(g: *mut GifFileType) -> c_int {
        let Some(p) = private(g) else { return GIF_ERROR };
        let gif = match decode(&p.data, usize::MAX) {
            Ok(x) => x,
            Err(e) => {
                (*g).Error = err_code(e);
                return GIF_ERROR;
            }
        };
        let b = &p.data;
        let mut q = p.blocks;
        for f in &gif.frames {
            let sp = vgif_GifMakeSavedImage(g, core::ptr::null());
            if sp.is_null() {
                (*g).Error = D_GIF_ERR_NOT_ENOUGH_MEM;
                return GIF_ERROR;
            }
            (*sp).ImageDesc = desc_of(f);
            let n = f.pixels.len();
            (*sp).RasterBits = malloc(n.max(1)) as *mut u8;
            if (*sp).RasterBits.is_null() {
                (*g).Error = D_GIF_ERR_NOT_ENOUGH_MEM;
                return GIF_ERROR;
            }
            core::ptr::copy_nonoverlapping(f.pixels.as_ptr(), (*sp).RasterBits, n);
            if extensions(b, q, &mut (*sp).ExtensionBlockCount, &mut (*sp).ExtensionBlocks).is_none() {
                (*g).Error = D_GIF_ERR_NOT_ENOUGH_MEM;
                return GIF_ERROR;
            }
            q = f.end;
        }
        if extensions(b, q, &mut (*g).ExtensionBlockCount, &mut (*g).ExtensionBlocks).is_none() {
            (*g).Error = D_GIF_ERR_NOT_ENOUGH_MEM;
            return GIF_ERROR;
        }
        if let Some(f) = gif.frames.last() {
            vgif_GifFreeMapObject((*g).Image.ColorMap);
            (*g).Image = desc_of(f);
        }
        p.pos = p.data.len();
        p.img = None;
        GIF_OK
    }

    /// `DGifExtensionToGCB`.
    fn DGifExtensionToGCB / vgif_DGifExtensionToGCB(len: usize, ext: *const u8, gcb: *mut GraphicsControlBlock) -> c_int {
        if len != 4 || ext.is_null() || gcb.is_null() {
            return GIF_ERROR;
        }
        let e = core::slice::from_raw_parts(ext, 4);
        (*gcb).DisposalMode = ((e[0] >> 2) & 7) as c_int;
        (*gcb).UserInputFlag = e[0] & 2 != 0;
        (*gcb).DelayTime = e[1] as c_int | (e[2] as c_int) << 8;
        (*gcb).TransparentColor = if e[0] & 1 != 0 { e[3] as c_int } else { NO_TRANSPARENT_COLOR };
        GIF_OK
    }

    /// `DGifSavedExtensionToGCB`: the graphic control of image `i`, from its
    /// first graphic control extension block.
    fn DGifSavedExtensionToGCB / vgif_DGifSavedExtensionToGCB(g: *mut GifFileType, i: c_int, gcb: *mut GraphicsControlBlock) -> c_int {
        if g.is_null() || gcb.is_null() || i < 0 || i > (*g).ImageCount - 1 {
            return GIF_ERROR;
        }
        (*gcb).DisposalMode = 0;
        (*gcb).UserInputFlag = false;
        (*gcb).DelayTime = 0;
        (*gcb).TransparentColor = NO_TRANSPARENT_COLOR;
        let sp = &*(*g).SavedImages.add(i as usize);
        for k in 0..sp.ExtensionBlockCount.max(0) as usize {
            let ep = &*sp.ExtensionBlocks.add(k);
            if ep.Function == GRAPHICS_EXT_FUNC_CODE {
                return vgif_DGifExtensionToGCB(ep.ByteCount.max(0) as usize, ep.Bytes, gcb);
            }
        }
        GIF_ERROR
    }

    /// `DGifGetGifVersion`.
    fn DGifGetGifVersion / vgif_DGifGetGifVersion(g: *mut GifFileType) -> *const c_char {
        let Some(p) = private(g) else { return core::ptr::null() };
        if p.gif89 { b"GIF89a\0".as_ptr() as *const c_char } else { b"GIF87a\0".as_ptr() as *const c_char }
    }
}

// ---------------------------------------------------------------------------
// The record-by-record API
// ---------------------------------------------------------------------------

/// The image row that stream row `r` of an image of height `h` holds:
/// passes of every 8th row from 0, every 8th from 4, every 4th from 2,
/// every 2nd from 1 (`spec::interlaced_row`, the other way round).
fn image_row(h: usize, r: usize) -> usize {
    let n1 = h.div_ceil(8);
    let n2 = (h + 3) / 8;
    let n3 = (h + 1) / 4;
    if r < n1 {
        8 * r
    } else if r < n1 + n2 {
        8 * (r - n1) + 4
    } else if r < n1 + n2 + n3 {
        4 * (r - n1 - n2) + 2
    } else {
        2 * (r - n1 - n2 - n3) + 1
    }
}

/// Reads the sub-block at `p.pos` into `p.buf`: its pointer, or `NULL` for
/// the terminator. `None` if the file ends.
fn next_block(p: &mut Private) -> Option<*mut u8> {
    let n = *p.data.get(p.pos)? as usize;
    if n == 0 {
        p.pos += 1;
        return Some(core::ptr::null_mut());
    }
    let s = p.data.get(p.pos + 1..p.pos + 1 + n)?;
    p.buf[0] = n as u8;
    p.buf[1..1 + n].copy_from_slice(s);
    p.pos += 1 + n;
    Some(p.buf.as_mut_ptr())
}

/// Reads an image descriptor at `p.pos` into `GifFile->Image`, and
/// decodes the image with the verified decoder for `DGifGetLine`.
unsafe fn image_header(g: *mut GifFileType) -> c_int {
    let Some(p) = private(g) else { return GIF_ERROR };
    let at = p.pos;
    let b = &p.data;
    let Some(d) = b.get(at..at + 9) else {
        (*g).Error = D_GIF_ERR_READ_FAILED;
        return GIF_ERROR;
    };
    let w = u16::from_le_bytes([d[4], d[5]]) as usize;
    let h = u16::from_le_bytes([d[6], d[7]]) as usize;
    let flags = d[8];
    let lct_len = if flags & 0x80 != 0 { 3 << ((flags & 7) + 1) } else { 0 };
    let c = at + 9 + lct_len;
    let Some(&m) = b.get(c) else {
        (*g).Error = D_GIF_ERR_READ_FAILED;
        return GIF_ERROR;
    };
    if !(2..=8).contains(&m) {
        (*g).Error = D_GIF_ERR_READ_FAILED;
        return GIF_ERROR;
    }
    vgif_GifFreeMapObject((*g).Image.ColorMap);
    (*g).Image = GifImageDesc {
        Left: u16::from_le_bytes([d[0], d[1]]) as c_int,
        Top: u16::from_le_bytes([d[2], d[3]]) as c_int,
        Width: w as c_int,
        Height: h as c_int,
        Interlace: flags & 0x40 != 0,
        ColorMap: if lct_len > 0 { map_of(&b[at + 9..c], false) } else { core::ptr::null_mut() },
    };
    let frame = image_exec(b, at, None, usize::MAX, &mut p.off, &mut p.len).map(|(f, _)| f);
    p.pos = c + 1;
    p.img = Some(Current {
        frame,
        width: w,
        height: h,
        interlace: flags & 0x40 != 0,
        done: 0,
        min_code: m,
        data_start: c + 1,
        lz: Lz::default(),
    });
    GIF_OK
}

api! {
    /// `DGifGetScreenDesc`: the screen descriptor is read when the file is
    /// opened; this does nothing more.
    fn DGifGetScreenDesc / vgif_DGifGetScreenDesc(g: *mut GifFileType) -> c_int {
        if private(g).is_none() { GIF_ERROR } else { GIF_OK }
    }

    /// `DGifGetRecordType`.
    fn DGifGetRecordType / vgif_DGifGetRecordType(g: *mut GifFileType, t: *mut c_int) -> c_int {
        let Some(p) = private(g) else { return GIF_ERROR };
        let Some(&c) = p.data.get(p.pos) else {
            (*g).Error = D_GIF_ERR_READ_FAILED;
            return GIF_ERROR;
        };
        p.pos += 1;
        let r = match c {
            0x2C => IMAGE_DESC_RECORD_TYPE,
            0x21 => EXTENSION_RECORD_TYPE,
            0x3B => TERMINATE_RECORD_TYPE,
            _ => {
                *t = UNDEFINED_RECORD_TYPE;
                (*g).Error = D_GIF_ERR_WRONG_RECORD;
                return GIF_ERROR;
            }
        };
        *t = r;
        GIF_OK
    }

    /// `DGifGetImageHeader`.
    fn DGifGetImageHeader / vgif_DGifGetImageHeader(g: *mut GifFileType) -> c_int {
        image_header(g)
    }

    /// `DGifGetImageDesc`: the descriptor, and a new entry at the end of
    /// `SavedImages` with it (and no raster), as giflib does.
    fn DGifGetImageDesc / vgif_DGifGetImageDesc(g: *mut GifFileType) -> c_int {
        if image_header(g) != GIF_OK {
            return GIF_ERROR;
        }
        let sp = vgif_GifMakeSavedImage(g, core::ptr::null());
        if sp.is_null() {
            (*g).Error = D_GIF_ERR_NOT_ENOUGH_MEM;
            return GIF_ERROR;
        }
        let d = (*g).Image;
        (*sp).ImageDesc = d;
        if !d.ColorMap.is_null() {
            (*sp).ImageDesc.ColorMap = vgif_GifMakeMapObject((*d.ColorMap).ColorCount, (*d.ColorMap).Colors);
        }
        GIF_OK
    }

    /// `DGifGetLine`: the next `len` pixels (a row if `len` is 0), in the
    /// order of the file.
    fn DGifGetLine / vgif_DGifGetLine(g: *mut GifFileType, line: *mut u8, len: c_int) -> c_int {
        let Some(p) = private(g) else { return GIF_ERROR };
        let Some(img) = p.img.as_mut() else {
            (*g).Error = D_GIF_ERR_NOT_READABLE;
            return GIF_ERROR;
        };
        let n = if len == 0 { img.width } else { len.max(0) as usize };
        let total = img.width * img.height;
        if n > total - img.done {
            (*g).Error = D_GIF_ERR_DATA_TOO_BIG;
            return GIF_ERROR;
        }
        let f = match &img.frame {
            Ok(f) => f,
            Err(e) => {
                (*g).Error = err_code(*e);
                return GIF_ERROR;
            }
        };
        for k in 0..n {
            let s = img.done + k;
            let (r, x) = (s / img.width, s % img.width);
            let y = if img.interlace { image_row(img.height, r) } else { r };
            *line.add(k) = f.pixels[y * img.width + x];
        }
        img.done += n;
        if img.done == total {
            p.pos = f.end;
        }
        GIF_OK
    }

    /// `DGifGetPixel`: takes the next pixel, which (as in giflib, whose
    /// argument is passed by value) the caller does not get.
    fn DGifGetPixel / vgif_DGifGetPixel(g: *mut GifFileType, px: u8) -> c_int {
        let mut v = px;
        vgif_DGifGetLine(g, &mut v, 1)
    }

    /// `DGifGetExtension`: the label, and the first sub-block (`NULL` if
    /// there is none) as length then bytes.
    fn DGifGetExtension / vgif_DGifGetExtension(g: *mut GifFileType, code: *mut c_int, ext: *mut *mut u8) -> c_int {
        let Some(p) = private(g) else { return GIF_ERROR };
        let Some(&c) = p.data.get(p.pos) else {
            (*g).Error = D_GIF_ERR_READ_FAILED;
            return GIF_ERROR;
        };
        p.pos += 1;
        *code = c as c_int;
        vgif_DGifGetExtensionNext(g, ext)
    }

    /// `DGifGetExtensionNext`: the next sub-block, or `NULL` at the
    /// terminator.
    fn DGifGetExtensionNext / vgif_DGifGetExtensionNext(g: *mut GifFileType, ext: *mut *mut u8) -> c_int {
        let Some(p) = private(g) else { return GIF_ERROR };
        match next_block(p) {
            Some(b) => {
                *ext = b;
                GIF_OK
            },
            None => {
                (*g).Error = D_GIF_ERR_READ_FAILED;
                GIF_ERROR
            },
        }
    }

    /// `DGifGetCode`: the LZW minimum code size, and the image's first
    /// sub-block.
    fn DGifGetCode / vgif_DGifGetCode(g: *mut GifFileType, size: *mut c_int, block: *mut *mut u8) -> c_int {
        let Some(p) = private(g) else { return GIF_ERROR };
        let Some(img) = p.img.as_ref() else {
            (*g).Error = D_GIF_ERR_NOT_READABLE;
            return GIF_ERROR;
        };
        *size = img.min_code as c_int;
        vgif_DGifGetCodeNext(g, block)
    }

    /// `DGifGetCodeNext`: the image's next sub-block, or `NULL` at the
    /// terminator (which ends the image).
    fn DGifGetCodeNext / vgif_DGifGetCodeNext(g: *mut GifFileType, block: *mut *mut u8) -> c_int {
        let Some(p) = private(g) else { return GIF_ERROR };
        match next_block(p) {
            Some(b) => {
                *block = b;
                if b.is_null() {
                    if let Some(img) = p.img.as_mut() {
                        img.done = img.width * img.height;
                    }
                }
                GIF_OK
            },
            None => {
                (*g).Error = D_GIF_ERR_READ_FAILED;
                GIF_ERROR
            },
        }
    }

    /// `DGifGetLZCodes`: the image's next LZW code, or -1 after the end
    /// code (and the rest of the image's sub-blocks).
    fn DGifGetLZCodes / vgif_DGifGetLZCodes(g: *mut GifFileType, code: *mut c_int) -> c_int {
        let Some(p) = private(g) else { return GIF_ERROR };
        let Some(img) = p.img.as_mut() else {
            (*g).Error = D_GIF_ERR_NOT_READABLE;
            return GIF_ERROR;
        };
        let clear = 1u32 << img.min_code;
        let lz = &mut img.lz;
        if !lz.started {
            *lz = Lz {
                started: true,
                running_code: clear + 2,
                running_bits: img.min_code as u32 + 1,
                max_code1: 1 << (img.min_code as u32 + 1),
                ..Lz::default()
            };
            p.pos = img.data_start;
        }
        if lz.running_bits > 12 {
            (*g).Error = D_GIF_ERR_IMAGE_DEFECT;
            return GIF_ERROR;
        }
        while lz.shift_state < lz.running_bits {
            if lz.at == lz.block.len() {
                // The next sub-block; an empty one here is a defect, as in
                // giflib (the end code should have come first).
                let Some(&n) = p.data.get(p.pos) else {
                    (*g).Error = D_GIF_ERR_READ_FAILED;
                    return GIF_ERROR;
                };
                if n == 0 {
                    (*g).Error = D_GIF_ERR_IMAGE_DEFECT;
                    return GIF_ERROR;
                }
                let Some(s) = p.data.get(p.pos + 1..p.pos + 1 + n as usize) else {
                    (*g).Error = D_GIF_ERR_READ_FAILED;
                    return GIF_ERROR;
                };
                lz.block = s.to_vec();
                lz.at = 0;
                p.pos += 1 + n as usize;
            }
            let byte = lz.block[lz.at];
            lz.at += 1;
            lz.shift_dword |= (byte as u64) << lz.shift_state;
            lz.shift_state += 8;
        }
        let c = (lz.shift_dword & ((1u64 << lz.running_bits) - 1)) as u32;
        lz.shift_dword >>= lz.running_bits;
        lz.shift_state -= lz.running_bits;
        if lz.running_code < 4097 {
            lz.running_code += 1;
            if lz.running_code > lz.max_code1 && lz.running_bits < 12 {
                lz.max_code1 <<= 1;
                lz.running_bits += 1;
            }
        }
        if c == clear + 1 {
            // Skip the rest of the image's sub-blocks.
            loop {
                match next_block(p) {
                    Some(b) if b.is_null() => break,
                    Some(_) => {},
                    None => {
                        (*g).Error = D_GIF_ERR_READ_FAILED;
                        return GIF_ERROR;
                    },
                }
            }
            *code = -1;
        } else {
            if c == clear {
                lz.running_code = clear + 2;
                lz.running_bits = img.min_code as u32 + 1;
                lz.max_code1 = 1 << lz.running_bits;
            }
            *code = c as c_int;
        }
        GIF_OK
    }
}
