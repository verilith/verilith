//! The read structure, the caller's I/O, chunk reading (`pngrutil.c`'s
//! chunk handlers for the critical chunks, tRNS and unknown chunks), the
//! sequential reader (`pngread.c`), the progressive reader (`pngpread.c`)
//! and the transformation and interlace settings.
//!
//! The chunks before the image data are read and handled as libpng does.
//! The image data is the verified decoder's: at the first row, the IDAT
//! chunks are read, and the decoder gets a file made of the signature,
//! IHDR, the PLTE and tRNS chunks that libpng accepted, the IDAT chunks
//! and IEND, all with correct CRCs (whether a chunk is used despite a bad
//! CRC is the caller's choice, `png_set_crc_action`, made here). The
//! decoder's pixels then go through libpng's row logic.
use super::err::*;
use super::info::{self, alloc_rows, be16, be32, free_rows};
use super::xform::{self, *};
use super::*;
use crate::decode::Tail;
use crate::top::{decode_tail, PixelFormat};

/// `mode` bits that are only used here.
pub const HAVE_CHUNK_AFTER_IDAT: u32 = 0x2000;
pub const IS_READ_STRUCT: u32 = 0x8000;
/// `Png::seen` bit for tRNS (the others are in `info`).
const SEEN_TRNS: u32 = 1 << 12;

// `png_set_crc_action` flags (`Png::crc_flags`).
const CRC_ANC_USE: u32 = 1;
const CRC_ANC_NOWARN: u32 = 2;
const CRC_CRIT_USE: u32 = 4;
const CRC_CRIT_IGNORE: u32 = 8;

const IO_READING: u32 = 0x0001;
const IO_SIGNATURE: u32 = 0x0010;
const IO_CHUNK_HDR: u32 = 0x0020;
const IO_CHUNK_DATA: u32 = 0x0040;
const IO_CHUNK_CRC: u32 = 0x0080;

/// Chunks longer than this (other than IDAT) are skipped rather than read
/// into memory; no handler accepts them.
const SKIP_LEN: usize = 1 << 26;

const SIGNATURE: [u8; 8] = [137, 80, 78, 71, 13, 10, 26, 10];

/// Adam7: (x0, dx, y0, dy) for each pass.
const ADAM7: [(u32, u32, u32, u32); 7] =
    [(0, 8, 0, 8), (4, 8, 0, 8), (0, 4, 4, 8), (2, 4, 0, 4), (0, 2, 2, 4), (1, 2, 0, 2), (0, 1, 1, 2)];

// Progressive reader states.
const PUSH_SIG: u8 = 0;
const PUSH_CHUNK: u8 = 1;
const PUSH_IDAT: u8 = 2;
const PUSH_DONE: u8 = 3;

pub struct Png {
    // Errors (`err.rs`).
    pub msg: [u8; MSG_LEN],
    pub error_fn: ErrorFn,
    pub warning_fn: ErrorFn,
    pub error_ptr: png_voidp,
    pub chunk_name: u32,
    pub flags: u32,
    pub longjmp_fn: LongjmpFn,
    pub jmp_buf: Option<Box<[u128]>>,
    pub jmp_buf_size: usize,
    // Memory (`mem.rs`).
    pub mem_ptr: png_voidp,
    pub malloc_fn: MallocFn,
    pub free_fn: FreeFn,
    // I/O.
    pub io_ptr: png_voidp,
    pub read_fn: RwFn,
    pub read_row_fn: ReadStatusFn,
    pub sig_bytes: u8,
    pub io_state: u32,
    // What has been read.
    pub mode: u32,
    pub seen: u32,
    pub width: u32,
    pub height: u32,
    pub bit_depth: u8,
    pub color_type: u8,
    pub interlaced: u8,
    pub channels: u8,
    pub pixel_depth: u8,
    pub rowbytes: usize,
    pub palette: [png_color; 256],
    pub num_palette: u16,
    pub trans_alpha: [u8; 256],
    pub num_trans: u16,
    pub trans_color: png_color_16,
    pub sig_bit: png_color_8,
    pub num_palette_max: c_int,
    // Limits.
    pub user_width_max: u32,
    pub user_height_max: u32,
    pub chunk_cache_max: u32,
    pub chunk_malloc_max: usize,
    pub crc_flags: u32,
    // Unknown chunks.
    pub unknown_default: c_int,
    pub chunk_list: Vec<([u8; 4], u8)>,
    pub read_user_chunk_fn: UserChunkFn,
    pub user_chunk_ptr: png_voidp,
    pub unknown_chunk: png_unknown_chunk,
    // Transformations.
    pub transformations: u32,
    pub filler: u16,
    pub shift: png_color_8,
    pub read_user_transform_fn: UserTransformFn,
    pub user_transform_ptr: png_voidp,
    pub user_transform_depth: u8,
    pub user_transform_channels: u8,
    // Rows.
    pub row_number: u32,
    pub num_rows: u32,
    pub pass: u8,
    pub iwidth: u32,
    /// The row being delivered, after a leading byte (libpng's filter
    /// byte), so that `row_buf[1..]` is what the caller sees.
    pub row_buf: Vec<u8>,
    pub row_info: png_row_info,
    pub transformed_pixel_depth: u8,
    pub info_rowbytes: usize,
    /// Whether the decoder's RGBA output is the transformed row.
    pub fast: bool,
    /// The progressive reader's data row within the pass.
    pub kdata: u32,
    // The current chunk.
    pub chunk_buf: Vec<u8>,
    pub chunk_len: u32,
    pub chunk_crc: u32,
    pub chunk_crc_calc: u32,
    pub chunk_skipped: bool,
    /// A chunk header that has been read and not yet handled.
    pub pending: Option<u32>,
    // The image.
    /// The file given to the decoder.
    pub file: Vec<u8>,
    pub image: Vec<u8>,
    /// 0: IDAT not read; 1: read; 2: decoded.
    pub image_state: u8,
    pub idat_unknown: bool,
    /// The lengths of the IDAT chunks in `file`.
    pub idat_lens: Vec<u32>,
    /// The error reading the header of the chunk after the image data,
    /// given when libpng would read that header.
    pub deferred: Option<[u8; MSG_LEN]>,
    pub iend_warned: bool,
    /// In a run of IDAT chunks after the first.
    pub push_extra: bool,
    /// What the image data held beyond the image (`decode::Tail`), and
    /// whether libpng's warnings about it have been given.
    pub tail_more: bool,
    pub tail_trailing: bool,
    pub tail_done: bool,
    // Progressive reading.
    pub info_fn: ProgressiveInfoFn,
    pub row_fn: ProgressiveRowFn,
    pub end_fn: ProgressiveEndFn,
    pub push: Vec<u8>,
    pub push_pos: usize,
    pub push_mode: u8,
    pub push_header: bool,
    pub push_len: u32,
    pub push_active: bool,
    pub push_paused: bool,
    pub push_call_start: usize,
    // Other settings.
    pub options: u32,
    pub idat_read_size: u32,
    pub time_buffer: [u8; 29],
}

impl Png {
    fn new() -> Png {
        Png {
            msg: [0; MSG_LEN],
            error_fn: None,
            warning_fn: None,
            error_ptr: core::ptr::null_mut(),
            chunk_name: 0,
            flags: F_BENIGN_WARN | F_APP_WARNINGS_WARN,
            longjmp_fn: None,
            jmp_buf: None,
            jmp_buf_size: 0,
            mem_ptr: core::ptr::null_mut(),
            malloc_fn: None,
            free_fn: None,
            io_ptr: core::ptr::null_mut(),
            read_fn: None,
            read_row_fn: None,
            sig_bytes: 0,
            io_state: 0,
            mode: IS_READ_STRUCT,
            seen: 0,
            width: 0,
            height: 0,
            bit_depth: 0,
            color_type: 0,
            interlaced: 0,
            channels: 0,
            pixel_depth: 0,
            rowbytes: 0,
            palette: [png_color::default(); 256],
            num_palette: 0,
            trans_alpha: [255; 256],
            num_trans: 0,
            trans_color: png_color_16::default(),
            sig_bit: png_color_8::default(),
            num_palette_max: 0,
            user_width_max: 1_000_000,
            user_height_max: 1_000_000,
            chunk_cache_max: 1000,
            chunk_malloc_max: 8_000_000,
            crc_flags: 0,
            unknown_default: HANDLE_CHUNK_AS_DEFAULT,
            chunk_list: Vec::new(),
            read_user_chunk_fn: None,
            user_chunk_ptr: core::ptr::null_mut(),
            unknown_chunk: png_unknown_chunk { name: [0; 5], data: core::ptr::null_mut(), size: 0, location: 0 },
            transformations: 0,
            filler: 0,
            shift: png_color_8::default(),
            read_user_transform_fn: None,
            user_transform_ptr: core::ptr::null_mut(),
            user_transform_depth: 0,
            user_transform_channels: 0,
            row_number: 0,
            num_rows: 0,
            pass: 0,
            iwidth: 0,
            row_buf: Vec::new(),
            row_info: png_row_info::default(),
            transformed_pixel_depth: 0,
            info_rowbytes: 0,
            fast: false,
            kdata: 0,
            chunk_buf: Vec::new(),
            chunk_len: 0,
            chunk_crc: 0,
            chunk_crc_calc: 0,
            chunk_skipped: false,
            pending: None,
            file: Vec::new(),
            image: Vec::new(),
            image_state: 0,
            idat_unknown: false,
            idat_lens: Vec::new(),
            deferred: None,
            iend_warned: false,
            push_extra: false,
            tail_more: false,
            tail_trailing: false,
            tail_done: false,
            info_fn: None,
            row_fn: None,
            end_fn: None,
            push: Vec::new(),
            push_pos: 0,
            push_mode: PUSH_SIG,
            push_header: false,
            push_len: 0,
            push_active: false,
            push_paused: false,
            push_call_start: 0,
            options: 0,
            idat_read_size: 8192,
            time_buffer: [0; 29],
        }
    }
}

fn critical(name: u32) -> bool {
    name & 0x2000_0000 == 0
}

/// `check_chunk_name`: four letters, the third uppercase.
fn check_chunk_name(name: u32) -> bool {
    let b = name.to_be_bytes();
    b.iter().all(|c| c.is_ascii_alphabetic()) && b[2].is_ascii_uppercase()
}

fn crc_update(reg: u32, d: &[u8]) -> u32 {
    verilith_zlib::checksum::cpu::crc32_update(reg, d)
}

/// Appends a chunk with a correct CRC to the decoder's file.
fn put_chunk(file: &mut Vec<u8>, name: u32, d: &[u8]) {
    let c = !crc_update(crc_update(!0, &name.to_be_bytes()), d);
    put_chunk_crc(file, name, d, c);
}

/// The same, with the chunk's CRC already computed.
fn put_chunk_crc(file: &mut Vec<u8>, name: u32, d: &[u8], crc: u32) {
    file.extend_from_slice(&(d.len() as u32).to_be_bytes());
    file.extend_from_slice(&name.to_be_bytes());
    file.extend_from_slice(d);
    file.extend_from_slice(&crc.to_be_bytes());
}

/// The current chunk's data, as read into `chunk_buf`. The slice is made
/// from a raw pointer so that it does not borrow `*p`; nothing changes
/// `chunk_buf` while a chunk is being handled.
unsafe fn data<'a>(p: *mut Png) -> &'a [u8] {
    if (*p).chunk_skipped {
        &[]
    } else {
        core::slice::from_raw_parts((*p).chunk_buf.as_ptr(), (*p).chunk_len as usize)
    }
}

// ---------------------------------------------------------------------------
// I/O
// ---------------------------------------------------------------------------

unsafe extern "C" {
    fn fread(ptr: *mut c_void, size: usize, n: usize, f: *mut c_void) -> usize;
}

/// Reads `n` bytes: from the progressive reader's buffer, the caller's
/// read function, or (`png_init_io`) the `FILE *`.
unsafe fn read_data(p: *mut Png, buf: *mut u8, n: usize) -> R<()> {
    if n == 0 {
        return Ok(());
    }
    if (*p).push_active {
        let avail = (*p).push.len() - (*p).push_pos;
        if avail < n {
            return Err(fail(p, "Read Error"));
        }
        core::ptr::copy_nonoverlapping((*p).push.as_ptr().add((*p).push_pos), buf, n);
        (*p).push_pos += n;
        return Ok(());
    }
    match (*p).read_fn {
        Some(f) => {
            f(p, buf, n);
            Ok(())
        }
        None => {
            if (*p).io_ptr.is_null() {
                return Err(fail(p, "Call to NULL read function"));
            }
            if fread(buf as *mut c_void, 1, n, (*p).io_ptr) != n {
                return Err(fail(p, "Read Error"));
            }
            Ok(())
        }
    }
}

/// `png_read_sig`.
unsafe fn read_sig(p: *mut Png, info: *mut Info) -> R<()> {
    let checked = (*p).sig_bytes as usize;
    if checked >= 8 {
        return Ok(());
    }
    (*p).io_state = IO_READING | IO_SIGNATURE;
    read_data(p, (*info).signature.as_mut_ptr().add(checked), 8 - checked)?;
    (*p).sig_bytes = 8;
    check_sig(p, &(*info).signature, checked, 8 - checked)
}

unsafe fn check_sig(p: *mut Png, sig: &[u8; 8], checked: usize, n: usize) -> R<()> {
    if sig_cmp(sig, checked, n) != 0 {
        if checked < 4 && sig_cmp(sig, checked, n.wrapping_sub(4)) != 0 {
            return Err(fail(p, "Not a PNG file"));
        }
        return Err(fail(p, "PNG file corrupted by ASCII conversion"));
    }
    Ok(())
}

fn sig_cmp(sig: &[u8], start: usize, n: usize) -> c_int {
    let mut n = n;
    if n > 8 {
        n = 8;
    } else if n < 1 {
        return -1;
    }
    if start > 7 {
        return -1;
    }
    if start + n > 8 {
        n = 8 - start;
    }
    for i in start..start + n {
        if sig[i] != SIGNATURE[i] {
            return sig[i] as c_int - SIGNATURE[i] as c_int;
        }
    }
    0
}

/// `png_read_chunk_header`: the length; the name goes to `chunk_name`.
unsafe fn read_header(p: *mut Png) -> R<u32> {
    let len = read_header_unchecked(p)?;
    if !check_chunk_name((*p).chunk_name) {
        return Err(chunk_fail(p, "bad header (invalid type)"));
    }
    Ok(len)
}

/// A chunk header as the progressive reader reads one after an IDAT
/// chunk: without checking the chunk's name.
unsafe fn read_header_unchecked(p: *mut Png) -> R<u32> {
    let mut b = [0u8; 8];
    (*p).io_state = IO_READING | IO_CHUNK_HDR;
    read_data(p, b.as_mut_ptr(), 8)?;
    let len = be32(&b);
    (*p).chunk_name = be32(&b[4..]);
    if len > 0x7fff_ffff {
        return Err(fail(p, "PNG unsigned integer out of range"));
    }
    (*p).io_state = IO_READING | IO_CHUNK_DATA;
    Ok(len)
}

/// Reads the chunk's data and CRC.
unsafe fn read_body(p: *mut Png, len: u32) -> R<()> {
    let name = (*p).chunk_name;
    let mut crc = crc_update(!0, &name.to_be_bytes());
    (*p).chunk_len = len;
    if len as usize > SKIP_LEN && name != IDAT {
        (*p).chunk_skipped = true;
        (*p).chunk_buf.resize(8192, 0);
        let mut left = len as usize;
        while left > 0 {
            let n = left.min(8192);
            read_data(p, (*p).chunk_buf.as_mut_ptr(), n)?;
            crc = crc_update(crc, &(*p).chunk_buf[..n]);
            left -= n;
        }
    } else {
        (*p).chunk_skipped = false;
        if (*p).chunk_buf.len() < len as usize {
            (*p).chunk_buf.resize(len as usize, 0);
        }
        read_data(p, (*p).chunk_buf.as_mut_ptr(), len as usize)?;
        crc = crc_update(crc, &(*p).chunk_buf[..len as usize]);
    }
    let mut c = [0u8; 4];
    (*p).io_state = IO_READING | IO_CHUNK_CRC;
    read_data(p, c.as_mut_ptr(), 4)?;
    (*p).chunk_crc = be32(&c);
    (*p).chunk_crc_calc = !crc;
    Ok(())
}

/// `png_crc_finish_critical`'s check of the CRC that `read_body` read:
/// whether it is bad and the data is to be discarded, after the warning
/// or error the CRC action asks for.
pub unsafe fn crc_check(p: *mut Png, as_ancillary: bool) -> R<bool> {
    let f = (*p).crc_flags;
    let as_anc = as_ancillary && f & CRC_CRIT_IGNORE == 0;
    let anc = as_anc || !critical((*p).chunk_name);
    let need = if anc { f & (CRC_ANC_USE | CRC_ANC_NOWARN) != CRC_ANC_USE | CRC_ANC_NOWARN } else { f & CRC_CRIT_IGNORE == 0 };
    if !need || (*p).chunk_crc == (*p).chunk_crc_calc {
        return Ok(false);
    }
    let warn_only = if anc { f & CRC_ANC_NOWARN == 0 } else { f & CRC_CRIT_USE != 0 };
    if warn_only {
        chunk_warn(p, "CRC error");
        Ok(true)
    } else {
        Err(chunk_fail(p, "CRC error"))
    }
}

// ---------------------------------------------------------------------------
// Chunk handling
// ---------------------------------------------------------------------------

/// `png_chunk_unknown_handling`.
unsafe fn unknown_handling(p: *mut Png, name: u32) -> c_int {
    let n = name.to_be_bytes();
    for (c, k) in (*p).chunk_list.iter().rev() {
        if *c == n {
            return *k as c_int;
        }
    }
    HANDLE_CHUNK_AS_DEFAULT
}

/// libpng's `check_location` for a read struct: the top-most of the IHDR,
/// PLTE and IDAT-after bits; `None` (an error in libpng) if none is set.
pub fn location_of(loc: u32) -> Option<u8> {
    let mut l = loc & (HAVE_IHDR | HAVE_PLTE | AFTER_IDAT);
    if l == 0 {
        return None;
    }
    while l != l & l.wrapping_neg() {
        l &= !(l & l.wrapping_neg());
    }
    Some(l as u8)
}

/// `png_handle_unknown`.
unsafe fn handle_unknown(p: *mut Png, info: *mut Info, keep: c_int) -> R<()> {
    let mut keep = keep;
    let mut handled = false;
    let name = (*p).chunk_name;
    let len = (*p).chunk_len as usize;
    let limit = if (*p).chunk_malloc_max == 0 { usize::MAX } else { (*p).chunk_malloc_max };
    // `png_cache_unknown_chunk`: the CRC is checked (and reported), and
    // the chunk kept whatever its CRC.
    let cache = |p: *mut Png| -> R<bool> {
        if len > limit || (*p).chunk_skipped {
            crc_check(p, false)?;
            chunk_benign(p, "unknown chunk exceeds memory limits")?;
            return Ok(false);
        }
        let mut n = [0u8; 5];
        n[..4].copy_from_slice(&name.to_be_bytes());
        (*p).unknown_chunk = png_unknown_chunk {
            name: n,
            data: if len == 0 { core::ptr::null_mut() } else { (*p).chunk_buf.as_mut_ptr() },
            size: len,
            location: (*p).mode as u8,
        };
        crc_check(p, false)?;
        Ok(true)
    };
    if let Some(f) = (*p).read_user_chunk_fn {
        if cache(p)? {
            let ret = f(p, &mut (*p).unknown_chunk);
            if ret < 0 {
                return Err(chunk_fail(p, "error in user chunk"));
            } else if ret == 0 {
                if keep < HANDLE_CHUNK_IF_SAFE {
                    if (*p).unknown_default < HANDLE_CHUNK_IF_SAFE {
                        chunk_warn(p, "Saving unknown chunk:");
                        app_warning(p, "forcing save of an unhandled chunk; please call png_set_keep_unknown_chunks")?;
                    }
                    keep = HANDLE_CHUNK_IF_SAFE;
                }
            } else {
                handled = true;
                keep = HANDLE_CHUNK_NEVER;
            }
        } else {
            keep = HANDLE_CHUNK_NEVER;
        }
    } else {
        if keep == HANDLE_CHUNK_AS_DEFAULT {
            keep = (*p).unknown_default;
        }
        if keep == HANDLE_CHUNK_ALWAYS || (keep == HANDLE_CHUNK_IF_SAFE && !critical(name)) {
            if !cache(p)? {
                keep = HANDLE_CHUNK_NEVER;
            }
        } else {
            crc_check(p, false)?;
        }
    }
    if keep == HANDLE_CHUNK_ALWAYS || (keep == HANDLE_CHUNK_IF_SAFE && !critical(name)) {
        let store = match (*p).chunk_cache_max {
            2 => {
                (*p).chunk_cache_max = 1;
                chunk_benign(p, "no space in chunk cache")?;
                false
            }
            1 => false,
            0 => true,
            _ => {
                (*p).chunk_cache_max -= 1;
                true
            }
        };
        if store && !info.is_null() {
            let u = (*p).unknown_chunk;
            let d: &[u8] = if u.data.is_null() { &[] } else { core::slice::from_raw_parts(u.data, u.size) };
            let loc = match location_of(u.location as u32) {
                Some(l) => l,
                None => return Err(fail(p, "invalid location in png_set_unknown_chunks")),
            };
            (*info).add_unknown(name, d, loc);
            handled = true;
        }
    }
    (*p).unknown_chunk.data = core::ptr::null_mut();
    if !handled && critical(name) {
        return Err(chunk_fail(p, "unhandled critical chunk"));
    }
    Ok(())
}

/// `png_handle_chunk` for a chunk that is not IDAT, whose data has been
/// read.
unsafe fn handle_known(p: *mut Png, info: *mut Info) -> R<()> {
    let name = (*p).chunk_name;
    let len = (*p).chunk_len;
    let mode = (*p).mode;
    // (max length, min length, must be before, must be after, may repeat)
    let t = match name {
        IHDR => (13, 13, HAVE_IHDR, 0, false),
        PLTE => (u32::MAX, 0, 0, HAVE_IHDR, true),
        IEND => (u32::MAX, 0, 0, AFTER_IDAT, false),
        TRNS => (256, 0, HAVE_IDAT, HAVE_IHDR, false),
        _ => {
            if info::is_known(name) {
                if mode & HAVE_IHDR == 0 {
                    return Err(chunk_fail(p, "missing IHDR"));
                }
                if (*p).chunk_skipped {
                    crc_check(p, false)?;
                    return chunk_benign(p, "length exceeds libpng limit");
                }
                return info::handle(p, info, name, data(p));
            }
            return handle_unknown(p, info, HANDLE_CHUNK_AS_DEFAULT);
        }
    };
    if name != IHDR && mode & HAVE_IHDR == 0 {
        return Err(chunk_fail(p, "missing IHDR"));
    }
    let (max, min, before, after, multiple) = t;
    let dup = match name {
        IHDR => mode & HAVE_IHDR != 0,
        IEND => mode & HAVE_IEND != 0,
        TRNS => (*p).seen & SEEN_TRNS != 0,
        _ => false,
    };
    let msg = if mode & before != 0 || mode & after != after {
        Some("out of place")
    } else if !multiple && dup {
        Some("duplicate")
    } else if len < min {
        Some("too short")
    } else if max != u32::MAX && len > max {
        Some("too long")
    } else {
        None
    };
    if let Some(m) = msg {
        if critical(name) {
            return Err(chunk_fail(p, m));
        }
        crc_check(p, false)?;
        return chunk_benign(p, m);
    }
    match name {
        IHDR => handle_ihdr(p, info),
        PLTE => handle_plte(p, info),
        IEND => {
            (*p).mode |= AFTER_IDAT | HAVE_IEND;
            if len != 0 && !(*p).iend_warned {
                chunk_benign(p, "invalid")?;
            }
            crc_check(p, true)?;
            Ok(())
        }
        _ => handle_trns(p, info),
    }
}

/// The errors `png_handle_chunk` gives before it reads the chunk's data:
/// a critical chunk out of place or of the wrong length, or a known chunk
/// before IHDR (`before_idat`: from `png_read_info`).
unsafe fn precheck(p: *mut Png, len: u32, before_idat: bool) -> R<()> {
    let name = (*p).chunk_name;
    let mode = (*p).mode;
    let msg = match name {
        IHDR if mode & HAVE_IHDR != 0 => Some("out of place"),
        IHDR if len != 13 => Some(if len < 13 { "too short" } else { "too long" }),
        IEND if mode & HAVE_IHDR == 0 => Some("missing IHDR"),
        IEND if mode & AFTER_IDAT == 0 => Some("out of place"),
        IEND if mode & HAVE_IEND != 0 => Some("duplicate"),
        _ if before_idat
            && name != IHDR
            && mode & HAVE_IHDR == 0
            && (name == PLTE || name == TRNS || info::is_known(name))
            && unknown_handling(p, name) == 0 =>
        {
            Some("missing IHDR")
        }
        _ => None,
    };
    match msg {
        Some(m) => Err(chunk_fail(p, m)),
        None if name == IEND && len != 0 => {
            // png_handle_IEND complains before it reads the data.
            (*p).iend_warned = true;
            chunk_benign(p, "invalid")
        }
        None => Ok(()),
    }
}

/// `png_handle_IHDR` and `png_check_IHDR`.
unsafe fn handle_ihdr(p: *mut Png, info: *mut Info) -> R<()> {
    (*p).mode |= HAVE_IHDR;
    crc_check(p, false)?;
    let d = data(p);
    let w = be32(d);
    let h = be32(&d[4..]);
    if w > 0x7fff_ffff || h > 0x7fff_ffff {
        return Err(fail(p, "PNG unsigned integer out of range"));
    }
    let (bd, ct, comp, filt, il) = (d[8], d[9], d[10], d[11], d[12]);
    (*p).width = w;
    (*p).height = h;
    (*p).bit_depth = bd;
    (*p).color_type = ct;
    (*p).interlaced = il;
    (*p).channels = match ct {
        CT_RGB => 3,
        CT_GA => 2,
        CT_RGBA => 4,
        _ => 1,
    };
    (*p).pixel_depth = bd.wrapping_mul((*p).channels);
    (*p).rowbytes = rowbytes((*p).pixel_depth as u32, w);
    check_ihdr(p, w, h, bd, ct, il, comp, filt)?;
    if !info.is_null() {
        let i = &mut *info;
        i.width = w;
        i.height = h;
        i.bit_depth = bd;
        i.color_type = ct;
        i.compression_type = comp;
        i.filter_type = filt;
        i.interlace_type = il;
        i.channels = (*p).channels;
        i.pixel_depth = (*p).pixel_depth;
        i.rowbytes = (*p).rowbytes;
    }
    (*p).file.clear();
    (*p).file.extend_from_slice(&SIGNATURE);
    put_chunk(&mut (*p).file, IHDR, d);
    Ok(())
}

/// `png_check_IHDR`: a warning for each problem, then an error.
#[allow(clippy::too_many_arguments)]
pub unsafe fn check_ihdr(p: *mut Png, w: u32, h: u32, bd: u8, ct: u8, il: u8, comp: u8, filt: u8) -> R<()> {
    let mut bad = false;
    let mut warn_if = |c: bool, m: &str| {
        if c {
            warn(p, m);
            bad = true;
        }
    };
    warn_if(w == 0, "Image width is zero in IHDR");
    warn_if(w > 0x7fff_ffff, "Invalid image width in IHDR");
    warn_if(w > (*p).user_width_max, "Image width exceeds user limit in IHDR");
    warn_if(h == 0, "Image height is zero in IHDR");
    warn_if(h > 0x7fff_ffff, "Invalid image height in IHDR");
    warn_if(h > (*p).user_height_max, "Image height exceeds user limit in IHDR");
    warn_if(!matches!(bd, 1 | 2 | 4 | 8 | 16), "Invalid bit depth in IHDR");
    warn_if(!matches!(ct, 0 | 2 | 3 | 4 | 6), "Invalid color type in IHDR");
    warn_if(
        (ct == CT_PALETTE && bd > 8) || (matches!(ct, 2 | 4 | 6) && bd < 8),
        "Invalid color type/bit depth combination in IHDR",
    );
    warn_if(il >= 2, "Unknown interlace method in IHDR");
    warn_if(comp != 0, "Unknown compression method in IHDR");
    warn_if(filt != 0, "Unknown filter method in IHDR");
    if bad {
        return Err(fail(p, "Invalid IHDR data"));
    }
    Ok(())
}

/// `png_handle_PLTE`.
unsafe fn handle_plte(p: *mut Png, info: *mut Info) -> R<()> {
    let mode = (*p).mode;
    let ct = (*p).color_type;
    let len = (*p).chunk_len;
    let msg = if mode & HAVE_PLTE != 0 {
        Some("duplicate")
    } else if mode & HAVE_IDAT != 0 {
        Some("out of place")
    } else if ct & COLOR_MASK_COLOR == 0 {
        Some("ignored in grayscale PNG")
    } else if len > 768 || len % 3 != 0 {
        Some("invalid")
    } else if ct != CT_PALETTE && (*p).seen & (SEEN_TRNS | 64) != 0 {
        Some("out of place")
    } else {
        None
    };
    if let Some(m) = msg {
        if ct == CT_PALETTE {
            crc_check(p, false)?;
            return Err(chunk_fail(p, m));
        }
        crc_check(p, true)?;
        return chunk_benign(p, m);
    }
    let max = if ct == CT_PALETTE { 1u32 << (*p).bit_depth } else { 256 };
    let num = if len > 3 * max { max } else { len / 3 };
    crc_check(p, ct != CT_PALETTE)?;
    let d = data(p);
    for i in 0..num as usize {
        (*p).palette[i] = png_color { red: d[3 * i], green: d[3 * i + 1], blue: d[3 * i + 2] };
    }
    for i in num as usize..256 {
        (*p).palette[i] = png_color::default();
    }
    (*p).num_palette = num as u16;
    (*p).mode |= HAVE_PLTE;
    if num == 0 {
        // `png_set_PLTE`: "Invalid palette".
        return Err(fail(p, "Invalid palette"));
    }
    if !info.is_null() {
        (*info).palette = (*p).palette[..num as usize].to_vec();
        (*info).valid |= INFO_PLTE;
        (*info).free_me |= FREE_PLTE;
    }
    if ct == CT_PALETTE {
        put_chunk(&mut (*p).file, PLTE, d);
    }
    Ok(())
}

/// `png_handle_tRNS`.
unsafe fn handle_trns(p: *mut Png, info: *mut Info) -> R<()> {
    let ct = (*p).color_type;
    let len = (*p).chunk_len as usize;
    let msg = match ct {
        CT_GRAY if len != 2 => Some("invalid"),
        CT_RGB if len != 6 => Some("invalid"),
        CT_PALETTE if (*p).mode & HAVE_PLTE == 0 => Some("out of place"),
        CT_PALETTE if len > (*p).num_palette as usize || len > 256 || len == 0 => Some("invalid"),
        CT_GA | CT_RGBA => Some("invalid with alpha channel"),
        _ => None,
    };
    if let Some(m) = msg {
        crc_check(p, false)?;
        return chunk_benign(p, m);
    }
    if crc_check(p, false)? {
        (*p).num_trans = 0;
        return Ok(());
    }
    let d = data(p);
    let mut tc = (*p).trans_color;
    match ct {
        CT_GRAY => {
            tc.gray = be16(d);
            (*p).num_trans = 1;
        }
        CT_RGB => {
            tc.red = be16(d);
            tc.green = be16(&d[2..]);
            tc.blue = be16(&d[4..]);
            (*p).num_trans = 1;
        }
        _ => {
            (*p).trans_alpha[..len].copy_from_slice(d);
            (*p).num_trans = len as u16;
        }
    }
    (*p).trans_color = tc;
    if ct != CT_PALETTE && (*p).bit_depth < 16 {
        let m = (1u16 << (*p).bit_depth) - 1;
        if (ct == CT_GRAY && tc.gray > m) || (ct == CT_RGB && (tc.red > m || tc.green > m || tc.blue > m)) {
            warn(p, "tRNS chunk has out-of-range samples for bit_depth");
        }
    }
    if !info.is_null() {
        if ct == CT_PALETTE {
            (*info).trans_alpha = d.to_vec();
        }
        (*info).trans_color = tc;
        (*info).num_trans = (*p).num_trans;
        (*info).valid |= INFO_tRNS;
        (*info).free_me |= FREE_TRNS;
    }
    (*p).seen |= SEEN_TRNS;
    put_chunk(&mut (*p).file, TRNS, d);
    Ok(())
}

/// One chunk other than IDAT before the image data, its data read
/// (`png_read_info`'s loop body).
unsafe fn info_chunk(p: *mut Png, info: *mut Info) -> R<()> {
    let name = (*p).chunk_name;
    if name == IHDR || name == IEND {
        return handle_known(p, info);
    }
    let keep = unknown_handling(p, name);
    if keep != 0 {
        handle_unknown(p, info, keep)?;
        if name == PLTE {
            (*p).mode |= HAVE_PLTE;
            if (*p).color_type == CT_PALETTE {
                put_chunk(&mut (*p).file, PLTE, data(p));
            }
        }
        return Ok(());
    }
    handle_known(p, info)
}

/// The IDAT checks of `png_read_info`, at an IDAT header.
unsafe fn idat_header(p: *mut Png) -> R<()> {
    if (*p).mode & HAVE_IHDR == 0 {
        return Err(chunk_fail(p, "Missing IHDR before IDAT"));
    }
    if (*p).color_type == CT_PALETTE && (*p).mode & HAVE_PLTE == 0 {
        return Err(chunk_fail(p, "Missing PLTE before IDAT"));
    }
    if (*p).mode & AFTER_IDAT != 0 {
        chunk_benign(p, "Too many IDATs found")?;
    }
    (*p).mode |= HAVE_IDAT;
    Ok(())
}

/// At the first IDAT: the verified container parser checks what libpng
/// accepted so far.
unsafe fn check_prefix(p: *mut Png) -> R<()> {
    let n = (*p).file.len();
    put_chunk(&mut (*p).file, IDAT, &[]);
    put_chunk(&mut (*p).file, IEND, &[]);
    let ok = crate::decode::container_exec(&(*p).file).is_some();
    (*p).file.truncate(n);
    if !ok {
        return Err(fail(p, "Invalid PNG header chunks"));
    }
    Ok(())
}

/// The IDAT chunk whose header has just been read: its data goes to the
/// decoder's file.
unsafe fn take_idat(p: *mut Png, len: u32) -> R<()> {
    read_body(p, len)?;
    crc_check(p, false)?;
    let d = data(p);
    put_chunk_crc(&mut (*p).file, IDAT, d, (*p).chunk_crc_calc);
    (*p).idat_lens.push(len);
    Ok(())
}

/// Reads the rest of the first run of IDAT chunks (the header of the first
/// is in `pending`), leaving the header of the chunk after them in
/// `pending`.
unsafe fn read_idat_run(p: *mut Png) -> R<()> {
    if (*p).image_state != 0 {
        return Ok(());
    }
    let mut len = match (*p).pending.take() {
        Some(l) => l,
        None => return Err(fail(p, "Not enough image data")),
    };
    loop {
        take_idat(p, len)?;
        len = match read_header(p) {
            Ok(l) => l,
            // libpng reads this header only once the image data it has is
            // used up, so its errors (a file that ends here, a damaged
            // header) come later: at png_read_end when the image is whole.
            // A caller's read function can raise its own error at once.
            Err(e) if (*p).read_fn.is_none() => {
                let _ = e;
                (*p).deferred = Some((*p).msg);
                (*p).chunk_name = IDAT;
                break;
            }
            Err(e) => return Err(e),
        };
        if (*p).chunk_name != IDAT {
            (*p).pending = Some(len);
            break;
        }
    }
    (*p).image_state = 1;
    Ok(())
}

/// Decodes the image data.
unsafe fn decode_image(p: *mut Png) -> R<()> {
    if (*p).image_state == 2 {
        return Ok(());
    }
    if (*p).idat_unknown || (*p).image_state == 0 {
        return Err(fail(p, "Not enough image data"));
    }
    let n = (*p).file.len();
    put_chunk(&mut (*p).file, IEND, &[]);
    let fmt = if (*p).fast { PixelFormat::Rgba8 } else { PixelFormat::Native };
    let mut tail = Tail::new();
    let r = decode_tail(&(*p).file, fmt, usize::MAX >> 2, &mut tail);
    (*p).file.truncate(n);
    match r {
        Ok((_, px)) => {
            (*p).image = px;
            (*p).image_state = 2;
            (*p).tail_more = tail.more;
            // libpng warns of bytes after the end of the zlib stream in the
            // IDAT chunk where it ends, not in later ones.
            let mut end = 0usize;
            for &l in &(*p).idat_lens {
                end += l as usize;
                if l > 0 && end >= tail.used {
                    break;
                }
            }
            (*p).tail_trailing = end > tail.used;
            Ok(())
        }
        Err(e) => {
            (*p).chunk_name = IDAT;
            Err(chunk_fail(
                p,
                match e {
                    crate::decode::Error::Invalid => "invalid image data",
                    crate::decode::Error::TooLarge => "image too large",
                    crate::decode::Error::OutOfMemory => "out of memory",
                },
            ))
        }
    }
}

/// The warnings of `png_read_finish_IDAT` about the image data after the
/// image; `early` when the caller has not read every row, so the rest of
/// the image is extra data too.
unsafe fn finish_idat(p: *mut Png, early: bool) -> R<()> {
    if (*p).image_state != 2 || (*p).tail_done {
        return Ok(());
    }
    (*p).tail_done = true;
    let name = (*p).chunk_name;
    (*p).chunk_name = IDAT;
    let r = (|| {
        if (*p).tail_trailing {
            chunk_benign(p, "Extra compressed data")?;
        }
        if (*p).tail_more || early {
            chunk_benign(p, "Too much image data")?;
        }
        Ok(())
    })();
    (*p).chunk_name = name;
    r
}

/// `png_read_info`.
unsafe fn read_info(p: *mut Png, info: *mut Info) -> R<()> {
    read_sig(p, info)?;
    loop {
        let len = read_header(p)?;
        let name = (*p).chunk_name;
        if name == IDAT {
            idat_header(p)?;
        } else if (*p).mode & HAVE_IDAT != 0 {
            (*p).mode |= HAVE_CHUNK_AFTER_IDAT | AFTER_IDAT;
        }
        if name == IDAT {
            check_prefix(p)?;
            if unknown_handling(p, IDAT) != 0 {
                read_body(p, len)?;
                handle_unknown(p, info, unknown_handling(p, IDAT))?;
                (*p).idat_unknown = true;
            } else {
                (*p).pending = Some(len);
            }
            return Ok(());
        }
        precheck(p, len, true)?;
        read_body(p, len)?;
        info_chunk(p, info)?;
    }
}

/// `png_read_end`.
unsafe fn read_end(p: *mut Png, info: *mut Info) -> R<()> {
    if !(*p).idat_unknown {
        read_idat_run(p)?;
        let done = if (*p).interlaced != 0 { (*p).pass >= 7 } else { (*p).row_number >= (*p).num_rows };
        finish_idat(p, !done)?;
    }
    if (*p).color_type == CT_PALETTE && (*p).num_palette_max >= (*p).num_palette as c_int {
        // libpng has not read the next chunk header yet.
        let name = (*p).chunk_name;
        (*p).chunk_name = IDAT;
        benign(p, "Read palette index exceeding num_palette")?;
        (*p).chunk_name = name;
    }
    loop {
        if let Some(m) = (*p).deferred {
            (*p).msg = m;
            return Err(E);
        }
        let len = match (*p).pending.take() {
            Some(l) => l,
            None => read_header(p)?,
        };
        let name = (*p).chunk_name;
        if name != IDAT {
            (*p).mode |= HAVE_CHUNK_AFTER_IDAT | AFTER_IDAT;
        }
        precheck(p, len, false)?;
        read_body(p, len)?;
        end_chunk(p, info, len)?;
        if (*p).mode & HAVE_IEND != 0 {
            return Ok(());
        }
    }
}

/// One chunk after the image data (`png_read_end`'s loop body).
unsafe fn end_chunk(p: *mut Png, info: *mut Info, len: u32) -> R<()> {
    let name = (*p).chunk_name;
    let ended = (*p).image_state != 0;
    if name == IEND || name == IHDR {
        return handle_known(p, info);
    }
    if info.is_null() {
        crc_check(p, false)?;
        return Ok(());
    }
    let keep = unknown_handling(p, name);
    if keep != 0 {
        if name == IDAT && ((len > 0 && !ended) || (*p).mode & HAVE_CHUNK_AFTER_IDAT != 0) {
            benign(p, ".Too many IDATs found")?;
        }
        handle_unknown(p, info, keep)?;
        if name == PLTE {
            (*p).mode |= HAVE_PLTE;
        }
        return Ok(());
    }
    if name == IDAT {
        if (len > 0 && !ended) || (*p).mode & HAVE_CHUNK_AFTER_IDAT != 0 {
            benign(p, "..Too many IDATs found")?;
        }
        crc_check(p, false)?;
        return Ok(());
    }
    handle_known(p, info)
}

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

fn pass_width(width: u32, pass: u8) -> u32 {
    let (x0, dx, _, _) = ADAM7[pass as usize];
    (width + dx - 1 - x0) / dx
}

fn pass_rows(height: u32, pass: u8) -> u32 {
    let (_, _, y0, dy) = ADAM7[pass as usize];
    (height + dy - 1 - y0) / dy
}

/// Whether the decoder's RGBA output is exactly what the transformations
/// make of the image.
unsafe fn fast_ok(p: *mut Png) -> bool {
    let t = (*p).transformations & !(T_INTERLACE | T_USER_TRANSFORM);
    let ct = (*p).color_type;
    let trns = (*p).num_trans > 0;
    if t & T_EXPAND == 0 {
        return false;
    }
    let mut need = T_EXPAND;
    // Gray to RGB does nothing to a color image, nor 16 to 8 to an image
    // of 8 bits or fewer.
    let mut allowed = T_EXPAND | T_EXPAND_tRNS | T_ADD_ALPHA | T_GRAY_TO_RGB;
    if (*p).bit_depth != 16 {
        allowed |= T_16_TO_8 | T_SCALE_16_TO_8;
    }
    if trns && ct != CT_PALETTE {
        need |= T_EXPAND_tRNS;
    }
    if (*p).bit_depth == 16 {
        need |= T_16_TO_8;
    }
    if ct & COLOR_MASK_COLOR == 0 {
        need |= T_GRAY_TO_RGB;
    }
    let alpha = ct & COLOR_MASK_ALPHA != 0 || trns;
    if alpha {
        allowed |= T_FILLER;
    } else {
        if (*p).flags & F_FILLER_AFTER == 0 || (*p).filler & 0xff != 0xff {
            return false;
        }
        need |= T_FILLER;
    }
    allowed |= need;
    t & need == need && t & !allowed == 0
}

/// `png_read_start_row` with `png_init_read_transformations`.
unsafe fn start_row(p: *mut Png) -> R<()> {
    let t = &mut (*p).transformations;
    if *t & T_STRIP_ALPHA != 0 {
        *t &= !T_EXPAND_tRNS;
        (*p).num_trans = 0;
    }
    if *t & T_EXPAND_16 != 0 && *t & T_EXPAND == 0 {
        *t &= !T_EXPAND_16;
    }
    if *t & T_SHIFT != 0 && *t & T_EXPAND == 0 && (*p).color_type == CT_PALETTE {
        *t &= !T_SHIFT;
        let sb = (*p).sig_bit;
        for i in 0..(*p).num_palette as usize {
            let c = &mut (*p).palette[i];
            for (v, s) in [(&mut c.red, sb.red), (&mut c.green, sb.green), (&mut c.blue, sb.blue)] {
                let sh = 8i32 - s as i32;
                if sh > 0 && sh < 8 {
                    *v >>= sh;
                }
            }
        }
    }
    let t = (*p).transformations;
    if (*p).interlaced != 0 {
        (*p).num_rows = if t & T_INTERLACE == 0 { pass_rows((*p).height, 0) } else { (*p).height };
        (*p).iwidth = pass_width((*p).width, (*p).pass);
    } else {
        (*p).num_rows = (*p).height;
        (*p).iwidth = (*p).width;
    }
    (*p).fast = fast_ok(p);
    let upd = (*p).user_transform_depth as usize * (*p).user_transform_channels as usize;
    let bytes = ((*p).width as usize + 7) / 8 * 8 * upd.max(64).div_ceil(8) + 64;
    (*p).row_buf.clear();
    (*p).row_buf.resize(bytes, 0);
    (*p).transformed_pixel_depth = 0;
    (*p).flags |= F_ROW_INIT;
    Ok(())
}

/// `png_read_transform_info`.
unsafe fn transform_info(p: *mut Png, info: *mut Info) {
    let t = (*p).transformations;
    let i = &mut *info;
    if i.color_type == CT_PALETTE && !i.palette.is_empty() {
        let n = i.palette.len();
        i.palette.copy_from_slice(&(*p).palette[..n]);
    }
    let (ct, bd, ch) = xform::out_format(
        t,
        (*p).color_type,
        (*p).bit_depth,
        (*p).num_trans,
        (*p).user_transform_depth,
        (*p).user_transform_channels,
    );
    if t & (T_EXPAND | T_STRIP_ALPHA) != 0 {
        i.num_trans = 0;
    }
    i.color_type = ct;
    i.bit_depth = bd;
    i.channels = ch;
    i.pixel_depth = bd.wrapping_mul(ch);
    i.rowbytes = rowbytes(i.pixel_depth as u32, i.width);
    (*p).info_rowbytes = i.rowbytes;
}

/// Gets bits `[bit, bit + d)` of `row`, `d` < 8, from the most significant
/// bit of each byte, or the least with `swap`.
#[inline]
fn get_px(row: &[u8], x: usize, d: usize, swap: bool) -> u8 {
    let bit = x * d;
    let s = if swap { bit & 7 } else { 8 - d - (bit & 7) };
    (row[bit >> 3] >> s) & ((1u16 << d) - 1) as u8
}

#[inline]
fn set_px(row: &mut [u8], x: usize, d: usize, swap: bool, v: u8) {
    let bit = x * d;
    let s = if swap { bit & 7 } else { 8 - d - (bit & 7) };
    let m = (((1u16 << d) - 1) as u8) << s;
    row[bit >> 3] = (row[bit >> 3] & !m) | ((v << s) & m);
}

/// Copies pixel `x` of `src` to `dst`.
#[inline]
fn copy_px(dst: &mut [u8], src: &[u8], x: usize, pd: usize, swap: bool) {
    if pd >= 8 {
        let b = pd / 8;
        dst[x * b..x * b + b].copy_from_slice(&src[x * b..x * b + b]);
    } else {
        set_px(dst, x, pd, swap, get_px(src, x, pd, swap));
    }
}

/// Puts data row `k` of the current pass, from the decoded image, into
/// `row_buf`, and runs the transformations on it.
unsafe fn load_row(p: *mut Png, k: u32) -> R<()> {
    let interlaced = (*p).interlaced != 0;
    let (x0, dx, y0, dy) = if interlaced { ADAM7[(*p).pass as usize] } else { (0, 1, 0, 1) };
    let y = y0 as u64 + k as u64 * dy as u64;
    if y >= (*p).height as u64 {
        return Err(fail(p, "Not enough image data"));
    }
    let y = y as usize;
    let iw = (*p).iwidth as usize;
    let fast = (*p).fast;
    let pd = if fast { 32 } else { (*p).pixel_depth as usize };
    let stride = rowbytes(pd as u32, (*p).width);
    let src = core::slice::from_raw_parts((*p).image.as_ptr().add(y * stride), stride);
    let rb = rowbytes(pd as u32, iw as u32);
    {
        let dst = &mut (*p).row_buf[1..];
        if dx == 1 {
            dst[..rb].copy_from_slice(&src[..rb]);
        } else if pd >= 8 {
            let b = pd / 8;
            for j in 0..iw {
                let x = x0 as usize + j * dx as usize;
                dst[j * b..j * b + b].copy_from_slice(&src[x * b..x * b + b]);
            }
        } else {
            for j in 0..iw {
                let x = x0 as usize + j * dx as usize;
                set_px(dst, j, pd, false, get_px(src, x, pd, false));
            }
        }
    }
    let t = (*p).transformations;
    if fast {
        // As the transformations leave it: the filler does not change
        // the row's color type.
        let ct = if (*p).color_type & COLOR_MASK_ALPHA != 0 || (*p).num_trans > 0 { CT_RGBA } else { CT_RGB };
        (*p).row_info = png_row_info { width: iw as u32, rowbytes: rb, color_type: ct, bit_depth: 8, channels: 4, pixel_depth: 32 };
    } else {
        (*p).row_info = png_row_info {
            width: iw as u32,
            rowbytes: rb,
            color_type: (*p).color_type,
            bit_depth: (*p).bit_depth,
            channels: (*p).channels,
            pixel_depth: (*p).pixel_depth,
        };
        let pr = Params {
            transformations: t,
            filler_after: (*p).flags & F_FILLER_AFTER != 0,
            filler: (*p).filler,
            shift: (*p).shift,
            palette: &(*p).palette,
            num_palette: (*p).num_palette,
            trans_alpha: &(*p).trans_alpha,
            num_trans: (*p).num_trans,
            trans_color: (*p).trans_color,
            check_index: (*p).num_palette_max >= 0,
        };
        let row = core::slice::from_raw_parts_mut((*p).row_buf.as_mut_ptr().add(1), (*p).row_buf.len() - 1);
        if let Some(m) = xform::transform(&pr, &mut (*p).row_info, row) {
            if m as c_int > (*p).num_palette_max {
                (*p).num_palette_max = m as c_int;
            }
        }
    }
    if t & T_USER_TRANSFORM != 0 {
        if let Some(f) = (*p).read_user_transform_fn {
            f(p, &mut (*p).row_info, (*p).row_buf.as_mut_ptr().add(1));
        }
        let ri = &mut (*p).row_info;
        if (*p).user_transform_depth != 0 {
            ri.bit_depth = (*p).user_transform_depth;
        }
        if (*p).user_transform_channels != 0 {
            ri.channels = (*p).user_transform_channels;
        }
        ri.pixel_depth = ri.bit_depth.wrapping_mul(ri.channels);
        ri.rowbytes = rowbytes(ri.pixel_depth as u32, ri.width);
    }
    let pdt = (*p).row_info.pixel_depth;
    if (*p).transformed_pixel_depth == 0 {
        (*p).transformed_pixel_depth = pdt;
    } else if (*p).transformed_pixel_depth != pdt {
        return Err(fail(p, "internal sequential row size calculation error"));
    }
    Ok(())
}

/// `png_do_read_interlace`: widens the pass row to `iwidth * dx` pixels,
/// each pixel repeated `dx` times.
unsafe fn read_interlace(p: *mut Png) {
    let pass = (*p).pass as usize;
    let dx = ADAM7[pass].1 as usize;
    let ri = &mut (*p).row_info;
    let w = ri.width as usize;
    let pd = ri.pixel_depth as usize;
    let swap = (*p).transformations & T_PACKSWAP != 0;
    let row = &mut (*p).row_buf[1..];
    for j in (0..w * dx).rev() {
        let s = j / dx;
        if pd >= 8 {
            let b = pd / 8;
            row.copy_within(s * b..s * b + b, j * b);
        } else {
            let v = get_px(row, s, pd, swap);
            set_px(row, j, pd, swap, v);
        }
    }
    ri.width = (w * dx) as u32;
    ri.rowbytes = rowbytes(pd as u32, ri.width);
}

/// `S_COPY` and `B_COPY` of `png_combine_row`.
fn s_copy(p: u32, x: u32) -> bool {
    (if p < 4 { 0x8008_8822u32 >> ((3 - p) * 8 + (7 - x)) } else { 0xaa55_ff00u32 >> ((7 - p) * 8 + (7 - x)) }) & 1 != 0
}

fn b_copy(p: u32, x: u32) -> bool {
    (if p < 4 { 0xff0f_ff33u32 >> ((3 - p) * 8 + (7 - x)) } else { 0xff55_ff00u32 >> ((7 - p) * 8 + (7 - x)) }) & 1 != 0
}

/// `png_combine_row`: `display` 0 copies the pass's pixels, 1 the blocks
/// they stand for, -1 everything.
unsafe fn combine_row(p: *const Png, dp: *mut u8, display: c_int) -> R<()> {
    let pd = (*p).transformed_pixel_depth as usize;
    if pd == 0 {
        return Err(fail(p as *mut Png, "internal row logic error"));
    }
    let width = (*p).width as usize;
    let pass = (*p).pass as u32;
    let swap = (*p).transformations & T_PACKSWAP != 0;
    let rb = rowbytes(pd as u32, width as u32);
    if (*p).info_rowbytes != 0 && (*p).info_rowbytes != rb {
        return Err(fail(p as *mut Png, "internal row size calculation error"));
    }
    let dst = core::slice::from_raw_parts_mut(dp, rb);
    let src = &(*p).row_buf[1..];
    if (*p).interlaced != 0
        && (*p).transformations & T_INTERLACE != 0
        && pass < 6
        && (display == 0 || (display == 1 && pass & 1 != 0))
    {
        for x in 0..width {
            let c = if display == 0 { s_copy(pass, (x & 7) as u32) } else { b_copy(pass, (x & 7) as u32) };
            if c {
                copy_px(dst, src, x, pd, swap);
            }
        }
    } else {
        let bits = pd * width;
        let full = bits / 8;
        dst[..full].copy_from_slice(&src[..full]);
        let rem = bits & 7;
        if rem != 0 {
            let keep: u8 = if swap { 0xffu8 << rem } else { 0xff >> rem };
            dst[full] = (dst[full] & keep) | (src[full] & !keep);
        }
    }
    Ok(())
}

/// `png_read_finish_row`.
unsafe fn finish_row(p: *mut Png) -> R<()> {
    (*p).row_number += 1;
    if (*p).row_number < (*p).num_rows {
        return Ok(());
    }
    if (*p).interlaced != 0 {
        (*p).row_number = 0;
        loop {
            (*p).pass += 1;
            if (*p).pass >= 7 {
                break;
            }
            (*p).iwidth = pass_width((*p).width, (*p).pass);
            if (*p).transformations & T_INTERLACE == 0 {
                (*p).num_rows = pass_rows((*p).height, (*p).pass);
            } else {
                break;
            }
            if (*p).num_rows != 0 && (*p).iwidth != 0 {
                break;
            }
        }
        if (*p).pass < 7 {
            return Ok(());
        }
    }
    finish_idat(p, false)
}

/// `png_read_row`.
unsafe fn read_row(p: *mut Png, row: *mut u8, dsp: *mut u8) -> R<()> {
    if (*p).flags & F_ROW_INIT == 0 {
        start_row(p)?;
    }
    if (*p).interlaced != 0 && (*p).pass >= 7 || (*p).interlaced == 0 && (*p).row_number >= (*p).num_rows {
        return Err(fail(p, "Read past the end of the image"));
    }
    let r = (*p).row_number;
    if (*p).interlaced != 0 && (*p).transformations & T_INTERLACE != 0 {
        let w = (*p).width;
        let skip = match (*p).pass {
            0 => r & 7 != 0,
            1 => r & 7 != 0 || w < 5,
            2 => r & 7 != 4,
            3 => r & 3 != 0 || w < 3,
            4 => r & 3 != 2,
            5 => r & 1 != 0 || w < 2,
            _ => r & 1 == 0,
        };
        if skip {
            let comb = match (*p).pass {
                2 => r & 4 != 0,
                4 => r & 2 != 0,
                6 => false,
                _ => true,
            };
            if !dsp.is_null() && comb {
                combine_row(p, dsp, 1)?;
            }
            finish_row(p)?;
            return Ok(());
        }
    }
    if (*p).mode & HAVE_IDAT == 0 {
        return Err(fail(p, "Invalid attempt to read row data"));
    }
    read_idat_run(p)?;
    decode_image(p)?;
    let k = if (*p).interlaced != 0 && (*p).transformations & T_INTERLACE != 0 {
        let (_, _, y0, dy) = ADAM7[(*p).pass as usize];
        (r - y0) / dy
    } else {
        r
    };
    load_row(p, k)?;
    if (*p).interlaced != 0 && (*p).transformations & T_INTERLACE != 0 {
        if (*p).pass < 6 {
            read_interlace(p);
        }
        if !dsp.is_null() {
            combine_row(p, dsp, 1)?;
        }
        if !row.is_null() {
            combine_row(p, row, 0)?;
        }
    } else {
        if !row.is_null() {
            combine_row(p, row, -1)?;
        }
        if !dsp.is_null() {
            combine_row(p, dsp, -1)?;
        }
    }
    finish_row(p)?;
    if let Some(f) = (*p).read_row_fn {
        f(p, (*p).row_number, (*p).pass as c_int);
    }
    Ok(())
}

unsafe fn read_image(p: *mut Png, image: *mut *mut u8) -> R<()> {
    let passes = if (*p).flags & F_ROW_INIT == 0 {
        let n = set_interlace_handling(p);
        start_row(p)?;
        n
    } else {
        if (*p).interlaced != 0 && (*p).transformations & T_INTERLACE == 0 {
            warn(p, "Interlace handling should be turned on when using png_read_image");
            (*p).num_rows = (*p).height;
        }
        set_interlace_handling(p)
    };
    for _ in 0..passes {
        for y in 0..(*p).height as usize {
            read_row(p, *image.add(y), core::ptr::null_mut())?;
        }
    }
    Ok(())
}

unsafe fn set_interlace_handling(p: *mut Png) -> c_int {
    if (*p).interlaced != 0 {
        (*p).transformations |= T_INTERLACE;
        7
    } else {
        1
    }
}

unsafe fn update_info(p: *mut Png, info: *mut Info) -> R<()> {
    if (*p).flags & F_ROW_INIT == 0 {
        start_row(p)?;
        if !info.is_null() {
            transform_info(p, info);
        }
        Ok(())
    } else {
        app_error(p, "png_read_update_info/png_start_read_image: duplicate call")
    }
}

unsafe fn read_png(p: *mut Png, info: *mut Info, transforms: c_int) -> R<()> {
    read_info(p, info)?;
    let t = transforms as u32;
    if t & 0x8000 != 0 {
        png_set_scale_16(p);
    }
    if t & 0x0001 != 0 {
        png_set_strip_16(p);
    }
    if t & 0x0002 != 0 {
        png_set_strip_alpha(p);
    }
    if t & 0x0004 != 0 {
        png_set_packing(p);
    }
    if t & 0x0008 != 0 {
        png_set_packswap(p);
    }
    if t & 0x0010 != 0 {
        png_set_expand(p);
    }
    if t & 0x0020 != 0 {
        png_set_invert_mono(p);
    }
    if t & 0x0040 != 0 && (*info).valid & INFO_sBIT != 0 {
        let sb = (*info).sig_bit;
        set_shift(p, &sb)?;
    }
    if t & 0x0080 != 0 {
        png_set_bgr(p);
    }
    if t & 0x0100 != 0 {
        png_set_swap_alpha(p);
    }
    if t & 0x0200 != 0 {
        png_set_swap(p);
    }
    if t & 0x0400 != 0 {
        png_set_invert_alpha(p);
    }
    if t & 0x2000 != 0 {
        png_set_gray_to_rgb(p);
    }
    if t & 0x4000 != 0 {
        png_set_expand_16(p);
    }
    set_interlace_handling(p);
    update_info(p, info)?;
    free_rows(p, info);
    if (*info).row_pointers.is_null() {
        alloc_rows(p, info)?;
    }
    read_image(p, (*info).row_pointers)?;
    (*info).valid |= INFO_IDAT;
    read_end(p, info)
}

unsafe fn set_shift(p: *mut Png, tb: &png_color_8) -> R<()> {
    let bd = (*p).bit_depth;
    let mut invalid = if (*p).color_type & COLOR_MASK_COLOR != 0 {
        tb.red == 0 || tb.red > bd || tb.green == 0 || tb.green > bd || tb.blue == 0 || tb.blue > bd
    } else {
        tb.gray == 0 || tb.gray > bd
    };
    if (*p).color_type & COLOR_MASK_ALPHA != 0 && (tb.alpha == 0 || tb.alpha > bd) {
        invalid = true;
    }
    if invalid {
        return app_error(p, "png_set_shift: invalid shift values");
    }
    (*p).transformations |= T_SHIFT;
    (*p).shift = *tb;
    Ok(())
}

/// `png_rtran_ok`.
unsafe fn rtran_ok(p: *mut Png, need_ihdr: bool) -> R<bool> {
    if p.is_null() {
        return Ok(false);
    }
    if (*p).flags & F_ROW_INIT != 0 {
        app_error(p, "invalid after png_start_read_image or png_read_update_info")?;
        Ok(false)
    } else if need_ihdr && (*p).mode & HAVE_IHDR == 0 {
        app_error(p, "invalid before the PNG header has been read")?;
        Ok(false)
    } else {
        (*p).flags |= F_DETECT_UNINIT;
        Ok(true)
    }
}

/// Sets transformation bits if `png_rtran_ok`.
unsafe fn rtran_set(p: *mut Png, bits: u32) {
    if p.is_null() {
        return;
    }
    let r = rtran_ok(p, false);
    if run(p, r, false) {
        (*p).transformations |= bits;
    }
}

// ---------------------------------------------------------------------------
// The progressive reader
// ---------------------------------------------------------------------------

/// `png_read_push_finish_row`.
unsafe fn push_finish_row(p: *mut Png) {
    (*p).row_number += 1;
    if (*p).row_number < (*p).num_rows {
        return;
    }
    if (*p).interlaced != 0 {
        (*p).row_number = 0;
        let w = (*p).width;
        loop {
            (*p).pass += 1;
            if ((*p).pass == 1 && w < 5) || ((*p).pass == 3 && w < 3) || ((*p).pass == 5 && w < 2) {
                (*p).pass += 1;
            }
            if (*p).pass > 7 {
                (*p).pass -= 1;
            }
            if (*p).pass >= 7 {
                break;
            }
            (*p).iwidth = pass_width(w, (*p).pass);
            if (*p).transformations & T_INTERLACE != 0 {
                break;
            }
            (*p).num_rows = pass_rows((*p).height, (*p).pass);
            if (*p).iwidth != 0 && (*p).num_rows != 0 {
                break;
            }
        }
    }
}

unsafe fn have_row(p: *mut Png, row: bool) {
    if let Some(f) = (*p).row_fn {
        let r = if row { (*p).row_buf.as_mut_ptr().add(1) } else { core::ptr::null_mut() };
        f(p, r, (*p).row_number, (*p).pass as c_int);
    }
}

/// `png_push_process_row`, for the row in `row_buf`.
unsafe fn push_process_row(p: *mut Png) {
    if (*p).interlaced == 0 || (*p).transformations & T_INTERLACE == 0 {
        have_row(p, true);
        push_finish_row(p);
        return;
    }
    if (*p).pass < 6 {
        read_interlace(p);
    }
    let h = (*p).height;
    // Up to `n` rows while the pass is `pass`.
    let rows = |p: *mut Png, n: usize, pass: u8, row: bool| {
        let mut i = 0;
        while i < n && (*p).pass == pass {
            have_row(p, row);
            push_finish_row(p);
            i += 1;
        }
    };
    match (*p).pass {
        0 => {
            rows(p, 8, 0, true);
            if (*p).pass == 2 {
                rows(p, 4, 2, false);
            }
            if (*p).pass == 4 && h <= 4 {
                rows(p, 2, 4, false);
            }
            if (*p).pass == 6 && h <= 4 {
                have_row(p, false);
                push_finish_row(p);
            }
        }
        1 => {
            rows(p, 8, 1, true);
            if (*p).pass == 2 {
                rows(p, 4, 2, false);
            }
        }
        2 => {
            rows(p, 4, 2, true);
            rows(p, 4, 2, false);
            if (*p).pass == 4 {
                rows(p, 2, 4, false);
            }
        }
        3 => {
            rows(p, 4, 3, true);
            if (*p).pass == 4 {
                rows(p, 2, 4, false);
            }
        }
        4 => {
            rows(p, 2, 4, true);
            rows(p, 2, 4, false);
            if (*p).pass == 6 {
                have_row(p, false);
                push_finish_row(p);
            }
        }
        5 => {
            rows(p, 2, 5, true);
            if (*p).pass == 6 {
                have_row(p, false);
                push_finish_row(p);
            }
        }
        _ => {
            have_row(p, true);
            push_finish_row(p);
            if (*p).pass == 6 {
                have_row(p, false);
                push_finish_row(p);
            }
        }
    }
}

/// Decodes the image and hands every row to the row callback.
unsafe fn push_rows(p: *mut Png) -> R<()> {
    if (*p).flags & F_ROW_INIT == 0 {
        start_row(p)?;
    }
    (*p).image_state = 1;
    decode_image(p)?;
    (*p).kdata = 0;
    let limit = (*p).height as u64 * 16 + 16;
    let mut n = 0u64;
    loop {
        if (*p).interlaced != 0 {
            if (*p).pass >= 7 {
                break;
            }
        } else if (*p).row_number >= (*p).num_rows {
            break;
        }
        n += 1;
        if n > limit {
            return Err(fail(p, "internal progressive row logic error"));
        }
        let pass = (*p).pass;
        let k = if (*p).interlaced != 0 && (*p).transformations & T_INTERLACE != 0 { (*p).kdata } else { (*p).row_number };
        load_row(p, k)?;
        push_process_row(p);
        if (*p).pass != pass {
            (*p).kdata = 0;
        } else {
            (*p).kdata += 1;
        }
    }
    Ok(())
}

/// Bytes in the progressive buffer not yet used.
unsafe fn push_avail(p: *mut Png) -> usize {
    (*p).push.len() - (*p).push_pos
}

/// One step of `png_process_some_data`. `Ok(false)`: needs more data.
unsafe fn push_step(p: *mut Png, info: *mut Info) -> R<bool> {
    match (*p).push_mode {
        PUSH_SIG => {
            let checked = (*p).sig_bytes as usize;
            let n = (8 - checked).min(push_avail(p));
            if n == 0 {
                return Ok(false);
            }
            read_data(p, (*info).signature.as_mut_ptr().add(checked), n)?;
            (*p).sig_bytes += n as u8;
            check_sig(p, &(*info).signature, checked, n)?;
            if (*p).sig_bytes >= 8 {
                (*p).push_mode = PUSH_CHUNK;
            }
            Ok(true)
        }
        PUSH_CHUNK => {
            if !(*p).push_header {
                if push_avail(p) < 8 {
                    return Ok(false);
                }
                (*p).push_len = if (*p).push_extra { read_header_unchecked(p)? } else { read_header(p)? };
                (*p).push_header = true;
                let name = (*p).chunk_name;
                if name != IDAT {
                    (*p).push_extra = false;
                }
                if name == IDAT {
                    if (*p).mode & AFTER_IDAT != 0 {
                        (*p).mode |= HAVE_CHUNK_AFTER_IDAT;
                    }
                    if (*p).mode & HAVE_IHDR == 0 {
                        return Err(fail(p, "Missing IHDR before IDAT"));
                    }
                    if (*p).color_type == CT_PALETTE && (*p).mode & HAVE_PLTE == 0 {
                        return Err(fail(p, "Missing PLTE before IDAT"));
                    }
                    if (*p).mode & HAVE_IDAT == 0 {
                        (*p).mode |= HAVE_IDAT;
                        check_prefix(p)?;
                        if unknown_handling(p, IDAT) == 0 {
                            (*p).push_mode = PUSH_IDAT;
                            if let Some(f) = (*p).info_fn {
                                f(p, info);
                            }
                            return Ok(true);
                        }
                    } else if (*p).mode & AFTER_IDAT != 0 && !(*p).push_extra {
                        benign(p, "Too many IDATs found")?;
                    }
                    if !(*p).push_extra && unknown_handling(p, IDAT) == 0 {
                        // Another run of IDAT chunks: libpng gives the
                        // info callback again, and ignores the data.
                        (*p).push_extra = true;
                        if let Some(f) = (*p).info_fn {
                            f(p, info);
                        }
                    }
                } else if (*p).mode & HAVE_IDAT != 0 {
                    (*p).mode |= HAVE_CHUNK_AFTER_IDAT | AFTER_IDAT;
                }
                if name == IHDR && (*p).push_len != 13 {
                    return Err(fail(p, "Invalid IHDR length"));
                }
            }
            let len = (*p).push_len;
            if push_avail(p) < len as usize + 4 {
                return Ok(false);
            }
            read_body(p, len)?;
            (*p).push_header = false;
            let name = (*p).chunk_name;
            if name == IDAT {
                // An IDAT chunk after the image data, or one kept as
                // unknown.
                let keep = unknown_handling(p, IDAT);
                if keep != 0 {
                    handle_unknown(p, info, keep)?;
                } else {
                    crc_check(p, false)?;
                }
                return Ok(true);
            }
            if (*p).mode & HAVE_IDAT != 0 {
                end_chunk(p, info, len)?;
            } else {
                info_chunk(p, info)?;
            }
            if name == IEND {
                (*p).push_mode = PUSH_DONE;
                if let Some(f) = (*p).end_fn {
                    f(p, info);
                }
            }
            Ok(true)
        }
        PUSH_IDAT => {
            if !(*p).push_header {
                if push_avail(p) < 8 {
                    return Ok(false);
                }
                (*p).push_len = read_header_unchecked(p)?;
                (*p).push_header = true;
                if (*p).chunk_name != IDAT {
                    // The image data is complete.
                    let name = (*p).chunk_name;
                    (*p).chunk_name = IDAT;
                    push_rows(p)?;
                    (*p).chunk_name = name;
                    (*p).push_mode = PUSH_CHUNK;
                    (*p).mode |= HAVE_CHUNK_AFTER_IDAT | AFTER_IDAT;
                    if name == IHDR && (*p).push_len != 13 {
                        return Err(fail(p, "Invalid IHDR length"));
                    }
                    return Ok(true);
                }
            }
            let len = (*p).push_len;
            if push_avail(p) < len as usize + 4 {
                return Ok(false);
            }
            read_body(p, len)?;
            (*p).push_header = false;
            crc_check(p, false)?;
            put_chunk_crc(&mut (*p).file, IDAT, data(p), (*p).chunk_crc_calc);
            (*p).idat_lens.push(len);
            Ok(true)
        }
        _ => {
            (*p).push_pos = (*p).push.len();
            Ok(false)
        }
    }
}

unsafe fn process_data(p: *mut Png, info: *mut Info, buf: *const u8, n: usize) -> R<()> {
    // Drop what has been used.
    let used = (*p).push_pos;
    (*p).push.drain(..used);
    (*p).push_pos = 0;
    (*p).push_call_start = (*p).push.len();
    if n > 0 {
        (*p).push.extend_from_slice(core::slice::from_raw_parts(buf, n));
    }
    (*p).push_paused = false;
    (*p).push_active = true;
    let r = (|| {
        while !(*p).push_paused && push_step(p, info)? {}
        Ok(())
    })();
    (*p).push_active = false;
    r
}

// ---------------------------------------------------------------------------
// The exported functions
// ---------------------------------------------------------------------------

/// `png_user_version_check`: the first two parts of the version must be
/// ours.
unsafe fn version_ok(p: *mut Png, v: *const c_char) -> bool {
    let mut ok = !v.is_null();
    if ok {
        let mut dots = 0;
        let mut i = 0;
        loop {
            let c = *v.add(i) as u8;
            let o = LIBPNG_VER_STRING[i];
            if c != o {
                ok = false;
            }
            if c == b'.' {
                dots += 1;
            }
            if dots >= 2 || c == 0 || o == 0 {
                break;
            }
            i += 1;
        }
    }
    if !ok {
        let user = if v.is_null() { &b""[..] } else { core::slice::from_raw_parts(v as *const u8, cstr_len(v)) };
        let s = format!(
            "Application built with libpng-{} but running with 1.6.59",
            String::from_utf8_lossy(&user[..user.len().min(64)])
        );
        warn(p, &s);
    }
    ok
}

api! {
    pub unsafe extern "C" fn png_create_read_struct(ver: *const c_char, error_ptr: png_voidp, error_fn: ErrorFn, warn_fn: ErrorFn) -> png_structp {
        png_create_read_struct_2(ver, error_ptr, error_fn, warn_fn, core::ptr::null_mut(), None, None)
    }

    pub unsafe extern "C" fn png_create_read_struct_2(ver: *const c_char, error_ptr: png_voidp, error_fn: ErrorFn, warn_fn: ErrorFn,
        mem_ptr: png_voidp, malloc_fn: MallocFn, free_fn: FreeFn) -> png_structp {
        let p = Box::into_raw(Box::new(Png::new()));
        (*p).error_ptr = error_ptr;
        (*p).error_fn = error_fn;
        (*p).warning_fn = warn_fn;
        (*p).mem_ptr = mem_ptr;
        (*p).malloc_fn = malloc_fn;
        (*p).free_fn = free_fn;
        if !version_ok(p, ver) {
            drop(Box::from_raw(p));
            return core::ptr::null_mut();
        }
        p
    }

    pub unsafe extern "C" fn png_destroy_read_struct(pp: *mut png_structp, info_pp: *mut png_infop, end_pp: *mut png_infop) {
        if pp.is_null() || (*pp).is_null() {
            return;
        }
        let p = *pp;
        info::png_destroy_info_struct(p, end_pp);
        info::png_destroy_info_struct(p, info_pp);
        *pp = core::ptr::null_mut();
        drop(Box::from_raw(p));
    }

    pub unsafe extern "C" fn png_set_read_fn(p: png_structp, io_ptr: png_voidp, f: RwFn) {
        if p.is_null() {
            return;
        }
        (*p).io_ptr = io_ptr;
        (*p).read_fn = f;
    }

    pub unsafe extern "C" fn png_init_io(p: png_structp, fp: png_voidp) {
        if p.is_null() {
            return;
        }
        (*p).io_ptr = fp;
    }

    pub unsafe extern "C" fn png_get_io_ptr(p: png_structp) -> png_voidp {
        if p.is_null() { core::ptr::null_mut() } else { (*p).io_ptr }
    }

    pub unsafe extern "C" fn png_get_io_state(p: png_structp) -> png_uint_32 {
        if p.is_null() { 0 } else { (*p).io_state }
    }

    pub unsafe extern "C" fn png_get_io_chunk_type(p: png_structp) -> png_uint_32 {
        if p.is_null() { 0 } else { (*p).chunk_name }
    }

    pub unsafe extern "C" fn png_set_read_status_fn(p: png_structp, f: ReadStatusFn) {
        if !p.is_null() {
            (*p).read_row_fn = f;
        }
    }

    pub unsafe extern "C" fn png_set_sig_bytes(p: png_structp, n: c_int) {
        if p.is_null() {
            return;
        }
        let n = if n < 0 { 0 } else { n as u32 };
        if n > 8 {
            fail(p, "Too many bytes for PNG signature");
            raise(p)
        }
        (*p).sig_bytes = n as u8;
    }

    pub unsafe extern "C" fn png_sig_cmp(sig: *const u8, start: usize, n: usize) -> c_int {
        if sig.is_null() {
            return -1;
        }
        let mut b = [0u8; 8];
        let end = (start.saturating_add(n.min(8))).min(8);
        if start < 8 {
            core::ptr::copy_nonoverlapping(sig.add(start), b.as_mut_ptr().add(start), end - start);
        }
        sig_cmp(&b, start, n)
    }

    pub unsafe extern "C" fn png_read_info(p: png_structp, info: png_infop) {
        if p.is_null() || info.is_null() {
            return;
        }
        let r = read_info(p, info);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_read_update_info(p: png_structp, info: png_infop) {
        if p.is_null() {
            return;
        }
        let r = update_info(p, info);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_start_read_image(p: png_structp) {
        if p.is_null() {
            return;
        }
        let r = if (*p).flags & F_ROW_INIT == 0 {
            start_row(p)
        } else {
            app_error(p, "png_start_read_image/png_read_update_info: duplicate call")
        };
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_read_row(p: png_structp, row: png_bytep, dsp: png_bytep) {
        if p.is_null() {
            return;
        }
        let r = read_row(p, row, dsp);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_read_rows(p: png_structp, rows: *mut png_bytep, dsp: *mut png_bytep, n: png_uint_32) {
        if p.is_null() {
            return;
        }
        for i in 0..n as usize {
            let r = if rows.is_null() { core::ptr::null_mut() } else { *rows.add(i) };
            let d = if dsp.is_null() { core::ptr::null_mut() } else { *dsp.add(i) };
            if rows.is_null() && dsp.is_null() {
                return;
            }
            png_read_row(p, r, d);
        }
    }

    pub unsafe extern "C" fn png_read_image(p: png_structp, image: *mut png_bytep) {
        if p.is_null() || image.is_null() {
            return;
        }
        let r = read_image(p, image);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_read_end(p: png_structp, info: png_infop) {
        if p.is_null() {
            return;
        }
        let r = read_end(p, info);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_read_png(p: png_structp, info: png_infop, transforms: c_int, params: png_voidp) {
        let _ = params;
        if p.is_null() || info.is_null() {
            return;
        }
        let r = read_png(p, info, transforms);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_set_progressive_read_fn(p: png_structp, progressive_ptr: png_voidp, info_fn: ProgressiveInfoFn,
        row_fn: ProgressiveRowFn, end_fn: ProgressiveEndFn) {
        if p.is_null() {
            return;
        }
        (*p).info_fn = info_fn;
        (*p).row_fn = row_fn;
        (*p).end_fn = end_fn;
        (*p).io_ptr = progressive_ptr;
        (*p).read_fn = None;
    }

    pub unsafe extern "C" fn png_get_progressive_ptr(p: png_structp) -> png_voidp {
        if p.is_null() { core::ptr::null_mut() } else { (*p).io_ptr }
    }

    pub unsafe extern "C" fn png_process_data(p: png_structp, info: png_infop, buf: png_bytep, n: usize) {
        if p.is_null() || info.is_null() {
            return;
        }
        let r = process_data(p, info, buf, n);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_process_data_pause(p: png_structp, save: c_int) -> usize {
        if p.is_null() {
            return 0;
        }
        (*p).push_paused = true;
        if save != 0 {
            return 0;
        }
        // The bytes of the current call that have not been used go back to
        // the caller.
        let keep = (*p).push_pos.max((*p).push_call_start);
        let n = (*p).push.len() - keep;
        (*p).push.truncate(keep);
        n
    }

    pub unsafe extern "C" fn png_process_data_skip(p: png_structp) -> png_uint_32 {
        if !p.is_null() {
            let r = app_warning(p, "png_process_data_skip is not implemented in any current version of libpng");
            run(p, r, ());
        }
        0
    }

    pub unsafe extern "C" fn png_progressive_combine_row(p: png_structp, old_row: png_bytep, new_row: *const u8) {
        if p.is_null() || new_row.is_null() || old_row.is_null() {
            return;
        }
        let r = combine_row(p, old_row, 1);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_set_crc_action(p: png_structp, crit: c_int, ancil: c_int) {
        if p.is_null() {
            return;
        }
        let f = &mut (*p).crc_flags;
        match crit {
            5 => {}
            3 => *f = (*f & !(CRC_CRIT_USE | CRC_CRIT_IGNORE)) | CRC_CRIT_USE,
            4 => *f = (*f & !(CRC_CRIT_USE | CRC_CRIT_IGNORE)) | CRC_CRIT_USE | CRC_CRIT_IGNORE,
            c => {
                if c == 2 {
                    warn(p, "Can't discard critical data on CRC error");
                }
                (*p).crc_flags &= !(CRC_CRIT_USE | CRC_CRIT_IGNORE);
            }
        }
        let f = &mut (*p).crc_flags;
        match ancil {
            5 => {}
            3 => *f = (*f & !(CRC_ANC_USE | CRC_ANC_NOWARN)) | CRC_ANC_USE,
            4 => *f = (*f & !(CRC_ANC_USE | CRC_ANC_NOWARN)) | CRC_ANC_USE | CRC_ANC_NOWARN,
            1 => *f = (*f & !(CRC_ANC_USE | CRC_ANC_NOWARN)) | CRC_ANC_NOWARN,
            _ => *f &= !(CRC_ANC_USE | CRC_ANC_NOWARN),
        }
    }

    pub unsafe extern "C" fn png_set_user_limits(p: png_structp, w: png_uint_32, h: png_uint_32) {
        if !p.is_null() {
            (*p).user_width_max = w;
            (*p).user_height_max = h;
        }
    }

    pub unsafe extern "C" fn png_get_user_width_max(p: png_structp) -> png_uint_32 {
        if p.is_null() { 0 } else { (*p).user_width_max }
    }

    pub unsafe extern "C" fn png_get_user_height_max(p: png_structp) -> png_uint_32 {
        if p.is_null() { 0 } else { (*p).user_height_max }
    }

    pub unsafe extern "C" fn png_set_chunk_cache_max(p: png_structp, n: png_uint_32) {
        if !p.is_null() {
            (*p).chunk_cache_max = n;
        }
    }

    pub unsafe extern "C" fn png_get_chunk_cache_max(p: png_structp) -> png_uint_32 {
        if p.is_null() { 0 } else { (*p).chunk_cache_max }
    }

    pub unsafe extern "C" fn png_set_chunk_malloc_max(p: png_structp, n: usize) {
        if !p.is_null() {
            (*p).chunk_malloc_max = n;
        }
    }

    pub unsafe extern "C" fn png_get_chunk_malloc_max(p: png_structp) -> usize {
        if p.is_null() { 0 } else { (*p).chunk_malloc_max }
    }

    pub unsafe extern "C" fn png_set_keep_unknown_chunks(p: png_structp, keep: c_int, list: *const u8, num: c_int) {
        if p.is_null() {
            return;
        }
        if !(0..HANDLE_CHUNK_LAST).contains(&keep) {
            let r = app_error(p, "png_set_keep_unknown_chunks: invalid keep");
            return run(p, r, ());
        }
        if num <= 0 {
            (*p).unknown_default = keep;
            if num == 0 {
                return;
            }
        }
        let names: Vec<[u8; 4]> = if num < 0 {
            [
                b"bKGD", b"cHRM", b"cICP", b"cLLI", b"eXIf", b"gAMA", b"hIST", b"iCCP", b"iTXt", b"mDCV", b"oFFs", b"pCAL",
                b"pHYs", b"sBIT", b"sCAL", b"sPLT", b"sTER", b"sRGB", b"tEXt", b"tIME", b"zTXt",
            ]
            .iter()
            .map(|n| **n)
            .collect()
        } else {
            if list.is_null() {
                let r = app_error(p, "png_set_keep_unknown_chunks: no chunk list");
                return run(p, r, ());
            }
            (0..num as usize).map(|i| {
                let mut n = [0u8; 4];
                core::ptr::copy_nonoverlapping(list.add(5 * i), n.as_mut_ptr(), 4);
                n
            }).collect()
        };
        // `add_one_chunk`: replace an entry, or append one unless it is
        // the default; IHDR and IEND are always handled by libpng.
        for n in names {
            if &n == b"IHDR" || &n == b"IEND" {
                continue;
            }
            match (*p).chunk_list.iter_mut().find(|e| e.0 == n) {
                Some(e) => e.1 = keep as u8,
                None => {
                    if keep != 0 {
                        (*p).chunk_list.push((n, keep as u8));
                    }
                }
            }
        }
        (*p).chunk_list.retain(|e| e.1 != 0);
    }

    pub unsafe extern "C" fn png_handle_as_unknown(p: png_structp, name: *const u8) -> c_int {
        if p.is_null() || name.is_null() {
            return 0;
        }
        let mut n = [0u8; 4];
        core::ptr::copy_nonoverlapping(name, n.as_mut_ptr(), 4);
        unknown_handling(p, u32::from_be_bytes(n))
    }

    pub unsafe extern "C" fn png_set_read_user_chunk_fn(p: png_structp, ptr: png_voidp, f: UserChunkFn) {
        if !p.is_null() {
            (*p).read_user_chunk_fn = f;
            (*p).user_chunk_ptr = ptr;
        }
    }

    pub unsafe extern "C" fn png_get_user_chunk_ptr(p: png_structp) -> png_voidp {
        if p.is_null() { core::ptr::null_mut() } else { (*p).user_chunk_ptr }
    }

    pub unsafe extern "C" fn png_set_read_user_transform_fn(p: png_structp, f: UserTransformFn) {
        if !p.is_null() {
            (*p).transformations |= T_USER_TRANSFORM;
            (*p).read_user_transform_fn = f;
        }
    }

    pub unsafe extern "C" fn png_set_user_transform_info(p: png_structp, ptr: png_voidp, depth: c_int, channels: c_int) {
        if p.is_null() {
            return;
        }
        if (*p).flags & F_ROW_INIT != 0 {
            let r = app_error(p, "info change after png_start_read_image or png_read_update_info");
            return run(p, r, ());
        }
        (*p).user_transform_ptr = ptr;
        (*p).user_transform_depth = depth as u8;
        (*p).user_transform_channels = channels as u8;
    }

    pub unsafe extern "C" fn png_get_user_transform_ptr(p: png_structp) -> png_voidp {
        if p.is_null() { core::ptr::null_mut() } else { (*p).user_transform_ptr }
    }

    pub unsafe extern "C" fn png_get_current_row_number(p: png_structp) -> png_uint_32 {
        if p.is_null() { u32::MAX } else { (*p).row_number }
    }

    pub unsafe extern "C" fn png_get_current_pass_number(p: png_structp) -> png_byte {
        if p.is_null() { 8 } else { (*p).pass }
    }

    pub unsafe extern "C" fn png_set_check_for_invalid_index(p: png_structp, allowed: c_int) {
        if !p.is_null() {
            (*p).num_palette_max = if allowed > 0 { 0 } else { -1 };
        }
    }

    pub unsafe extern "C" fn png_set_option(p: png_structp, option: c_int, onoff: c_int) -> c_int {
        if !p.is_null() && (0..16).contains(&option) && option & 1 == 0 {
            let mask = 3u32 << option;
            let setting = (2u32 + (onoff != 0) as u32) << option;
            let cur = (*p).options;
            (*p).options = (cur & !mask) | setting;
            return ((cur & mask) >> option) as c_int;
        }
        1
    }

    pub unsafe extern "C" fn png_set_compression_buffer_size(p: png_structp, size: usize) {
        if p.is_null() {
            return;
        }
        if size == 0 || size > 0x7fff_ffff {
            fail(p, "invalid compression buffer size");
            raise(p)
        }
        (*p).idat_read_size = size as u32;
    }

    pub unsafe extern "C" fn png_get_compression_buffer_size(p: png_structp) -> usize {
        if p.is_null() { 0 } else { (*p).idat_read_size as usize }
    }

    pub unsafe extern "C" fn png_reset_zstream(p: png_structp) -> c_int {
        if p.is_null() { -2 } else { 0 }
    }

    // Transformations.

    pub unsafe extern "C" fn png_set_expand(p: png_structp) {
        rtran_set(p, T_EXPAND | T_EXPAND_tRNS)
    }

    pub unsafe extern "C" fn png_set_palette_to_rgb(p: png_structp) {
        rtran_set(p, T_EXPAND | T_EXPAND_tRNS)
    }

    pub unsafe extern "C" fn png_set_expand_gray_1_2_4_to_8(p: png_structp) {
        rtran_set(p, T_EXPAND)
    }

    pub unsafe extern "C" fn png_set_tRNS_to_alpha(p: png_structp) {
        rtran_set(p, T_EXPAND | T_EXPAND_tRNS)
    }

    pub unsafe extern "C" fn png_set_expand_16(p: png_structp) {
        rtran_set(p, T_EXPAND_16 | T_EXPAND | T_EXPAND_tRNS)
    }

    pub unsafe extern "C" fn png_set_gray_to_rgb(p: png_structp) {
        if p.is_null() {
            return;
        }
        let r = rtran_ok(p, false);
        if run(p, r, false) {
            png_set_expand_gray_1_2_4_to_8(p);
            (*p).transformations |= T_GRAY_TO_RGB;
        }
    }

    pub unsafe extern "C" fn png_set_scale_16(p: png_structp) {
        rtran_set(p, T_SCALE_16_TO_8)
    }

    pub unsafe extern "C" fn png_set_strip_16(p: png_structp) {
        rtran_set(p, T_16_TO_8)
    }

    pub unsafe extern "C" fn png_set_strip_alpha(p: png_structp) {
        rtran_set(p, T_STRIP_ALPHA)
    }

    pub unsafe extern "C" fn png_set_bgr(p: png_structp) {
        if !p.is_null() {
            (*p).transformations |= T_BGR;
        }
    }

    pub unsafe extern "C" fn png_set_swap(p: png_structp) {
        if !p.is_null() && (*p).bit_depth == 16 {
            (*p).transformations |= T_SWAP_BYTES;
        }
    }

    pub unsafe extern "C" fn png_set_packing(p: png_structp) {
        if !p.is_null() && (*p).bit_depth < 8 {
            (*p).transformations |= T_PACK;
        }
    }

    pub unsafe extern "C" fn png_set_packswap(p: png_structp) {
        if !p.is_null() && (*p).bit_depth < 8 {
            (*p).transformations |= T_PACKSWAP;
        }
    }

    pub unsafe extern "C" fn png_set_shift(p: png_structp, true_bits: *const png_color_8) {
        if p.is_null() || true_bits.is_null() {
            return;
        }
        let tb = *true_bits;
        let r = set_shift(p, &tb);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_set_interlace_handling(p: png_structp) -> c_int {
        if p.is_null() { 1 } else { set_interlace_handling(p) }
    }

    pub unsafe extern "C" fn png_set_filler(p: png_structp, filler: png_uint_32, loc: c_int) {
        if p.is_null() {
            return;
        }
        (*p).filler = filler as u16;
        (*p).transformations |= T_FILLER;
        if loc == 1 {
            (*p).flags |= F_FILLER_AFTER;
        } else {
            (*p).flags &= !F_FILLER_AFTER;
        }
    }

    pub unsafe extern "C" fn png_set_add_alpha(p: png_structp, filler: png_uint_32, loc: c_int) {
        if p.is_null() {
            return;
        }
        png_set_filler(p, filler, loc);
        if (*p).transformations & T_FILLER != 0 {
            (*p).transformations |= T_ADD_ALPHA;
        }
    }

    pub unsafe extern "C" fn png_set_swap_alpha(p: png_structp) {
        if !p.is_null() {
            (*p).transformations |= T_SWAP_ALPHA;
        }
    }

    pub unsafe extern "C" fn png_set_invert_alpha(p: png_structp) {
        if !p.is_null() {
            (*p).transformations |= T_INVERT_ALPHA;
        }
    }

    pub unsafe extern "C" fn png_set_invert_mono(p: png_structp) {
        if !p.is_null() {
            (*p).transformations |= T_INVERT_MONO;
        }
    }

    // Version, strings and numbers.

    pub unsafe extern "C" fn png_access_version_number() -> png_uint_32 {
        LIBPNG_VER
    }

    pub unsafe extern "C" fn png_get_libpng_ver(p: png_structp) -> *const c_char {
        let _ = p;
        LIBPNG_VER_STRING.as_ptr() as *const c_char
    }

    pub unsafe extern "C" fn png_get_header_ver(p: png_structp) -> *const c_char {
        let _ = p;
        LIBPNG_VER_STRING.as_ptr() as *const c_char
    }

    pub unsafe extern "C" fn png_get_header_version(p: png_structp) -> *const c_char {
        let _ = p;
        b" libpng version 1.6.59 (verilith-png)\n\0".as_ptr() as *const c_char
    }

    pub unsafe extern "C" fn png_get_copyright(p: png_structp) -> *const c_char {
        let _ = p;
        concat!(
            "\nlibpng version 1.6.59\n",
            "Copyright (c) 2018-2026 Cosmin Truta\n",
            "Copyright (c) 1998-2002,2004,2006-2018 Glenn Randers-Pehrson\n",
            "Copyright (c) 1996-1997 Andreas Dilger\n",
            "Copyright (c) 1995-1996 Guy Eric Schalnat, Group 42, Inc.\n",
            "verilith-png: a verified decoder behind libpng's read API\n\0"
        )
        .as_ptr() as *const c_char
    }

    pub unsafe extern "C" fn png_get_uint_32(buf: *const u8) -> png_uint_32 {
        be32(core::slice::from_raw_parts(buf, 4))
    }

    pub unsafe extern "C" fn png_get_uint_16(buf: *const u8) -> png_uint_16 {
        be16(core::slice::from_raw_parts(buf, 2))
    }

    pub unsafe extern "C" fn png_get_int_32(buf: *const u8) -> png_int_32 {
        be32(core::slice::from_raw_parts(buf, 4)) as i32
    }

    pub unsafe extern "C" fn png_get_uint_31(p: png_structp, buf: *const u8) -> png_uint_32 {
        let v = be32(core::slice::from_raw_parts(buf, 4));
        if v > 0x7fff_ffff {
            fail(p, "PNG unsigned integer out of range");
            raise(p)
        }
        v
    }

    pub unsafe extern "C" fn png_convert_to_rfc1123_buffer(out: *mut c_char, t: *const png_time) -> c_int {
        if out.is_null() || t.is_null() {
            return 0;
        }
        let t = *t;
        if t.year > 9999 || t.month == 0 || t.month > 12 || t.day == 0 || t.day > 31 || t.hour > 23 || t.minute > 59 || t.second > 60 {
            return 0;
        }
        const M: [&str; 12] = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
        let s = format!("{} {} {} {:02}:{:02}:{:02} +0000", t.day, M[t.month as usize - 1], t.year, t.hour, t.minute, t.second);
        let b = s.as_bytes();
        let n = b.len().min(28);
        core::ptr::copy_nonoverlapping(b.as_ptr(), out as *mut u8, n);
        *out.add(n) = 0;
        1
    }

    pub unsafe extern "C" fn png_convert_to_rfc1123(p: png_structp, t: *const png_time) -> *const c_char {
        if p.is_null() {
            return core::ptr::null();
        }
        if png_convert_to_rfc1123_buffer((*p).time_buffer.as_mut_ptr() as *mut c_char, t) == 0 {
            warn(p, "Ignoring invalid time value");
            return core::ptr::null();
        }
        (*p).time_buffer.as_ptr() as *const c_char
    }

    pub unsafe extern "C" fn png_build_grayscale_palette(bit_depth: c_int, palette: *mut png_color) {
        if palette.is_null() {
            return;
        }
        let (n, inc) = match bit_depth {
            1 => (2, 0xff),
            2 => (4, 0x55),
            4 => (16, 0x11),
            8 => (256, 1),
            _ => (0, 0),
        };
        for i in 0..n {
            let v = ((i * inc) & 0xff) as u8;
            *palette.add(i) = png_color { red: v, green: v, blue: v };
        }
    }
}
