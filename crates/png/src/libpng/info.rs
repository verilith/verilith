//! `png_info`: what the file says, the ancillary chunk handlers that fill
//! it (`png_handle_*` in libpng's `pngrutil.c`), and the `png_get_*` and
//! `png_set_*` functions.
use super::err::*;
use super::mem::{alloc, dealloc};
use super::*;
use verilith_zlib::{Decompressor, Format};

/// A text chunk's strings, NUL-terminated, which `png_text` points into.
pub struct TextStore {
    compression: c_int,
    key: Vec<u8>,
    text: Vec<u8>,
    lang: Option<Vec<u8>>,
    lang_key: Option<Vec<u8>>,
}

pub struct Info {
    pub valid: u32,
    pub free_me: u32,
    pub width: u32,
    pub height: u32,
    pub bit_depth: u8,
    pub color_type: u8,
    pub compression_type: u8,
    pub filter_type: u8,
    pub interlace_type: u8,
    pub channels: u8,
    pub pixel_depth: u8,
    pub rowbytes: usize,
    pub signature: [u8; 8],
    pub palette: Vec<png_color>,
    pub trans_alpha: Vec<u8>,
    pub num_trans: u16,
    pub trans_color: png_color_16,
    pub gamma: i32,
    pub chrm: [i32; 8],
    pub srgb: c_int,
    pub iccp_name: Vec<u8>,
    pub iccp_profile: Vec<u8>,
    pub sig_bit: png_color_8,
    pub background: png_color_16,
    pub hist: Vec<u16>,
    pub phys: (u32, u32, c_int),
    pub offs: (i32, i32, c_int),
    pub time: png_time,
    pub text: Vec<TextStore>,
    pub text_c: Vec<png_text>,
    pub exif: Vec<u8>,
    pub unknown: Vec<(png_unknown_chunk, Vec<u8>)>,
    pub unknown_c: Vec<png_unknown_chunk>,
    pub row_pointers: *mut *mut u8,
}

impl Info {
    pub fn new() -> Info {
        Info {
            valid: 0,
            free_me: 0,
            width: 0,
            height: 0,
            bit_depth: 0,
            color_type: 0,
            compression_type: 0,
            filter_type: 0,
            interlace_type: 0,
            channels: 0,
            pixel_depth: 0,
            rowbytes: 0,
            signature: [0; 8],
            palette: Vec::new(),
            trans_alpha: Vec::new(),
            num_trans: 0,
            trans_color: png_color_16::default(),
            gamma: 0,
            chrm: [0; 8],
            srgb: 0,
            iccp_name: Vec::new(),
            iccp_profile: Vec::new(),
            sig_bit: png_color_8::default(),
            background: png_color_16::default(),
            hist: Vec::new(),
            phys: (0, 0, 0),
            offs: (0, 0, 0),
            time: png_time::default(),
            text: Vec::new(),
            text_c: Vec::new(),
            exif: Vec::new(),
            unknown: Vec::new(),
            unknown_c: Vec::new(),
            row_pointers: core::ptr::null_mut(),
        }
    }

    fn rebuild_text(&mut self) {
        self.text_c = self
            .text
            .iter_mut()
            .map(|t| png_text {
                compression: t.compression,
                key: t.key.as_mut_ptr() as *mut c_char,
                text: t.text.as_mut_ptr() as *mut c_char,
                text_length: if t.compression >= 1 { 0 } else { t.text.len() - 1 },
                itxt_length: if t.compression >= 1 { t.text.len() - 1 } else { 0 },
                lang: t.lang.as_mut().map_or(core::ptr::null_mut(), |v| v.as_mut_ptr() as *mut c_char),
                lang_key: t.lang_key.as_mut().map_or(core::ptr::null_mut(), |v| v.as_mut_ptr() as *mut c_char),
            })
            .collect();
    }

    pub fn add_text(&mut self, compression: c_int, key: &[u8], text: &[u8], lang: Option<&[u8]>, lang_key: Option<&[u8]>) {
        fn z(b: &[u8]) -> Vec<u8> {
            let n = b.iter().position(|&c| c == 0).unwrap_or(b.len());
            let mut v = Vec::with_capacity(n + 1);
            v.extend_from_slice(&b[..n]);
            v.push(0);
            v
        }
        // The text keeps any NUL it holds out of the length, as libpng's
        // `strlen` would.
        self.text.push(TextStore { compression, key: z(key), text: z(text), lang: lang.map(z), lang_key: lang_key.map(z) });
        self.rebuild_text();
        self.free_me |= FREE_TEXT;
    }

    pub fn add_unknown(&mut self, name: u32, data: &[u8], location: u8) {
        let mut v = data.to_vec();
        let mut n = [0u8; 5];
        n[..4].copy_from_slice(&name.to_be_bytes());
        let c = png_unknown_chunk { name: n, data: if v.is_empty() { core::ptr::null_mut() } else { v.as_mut_ptr() }, size: v.len(), location };
        self.unknown.push((c, v));
        self.unknown_c = self.unknown.iter().map(|u| u.0).collect();
        self.free_me |= FREE_UNKN;
    }

    /// `png_free_data` for everything that is not the row pointers.
    fn clear(&mut self, mask: u32) {
        if mask & FREE_TEXT != 0 {
            self.text.clear();
            self.text_c.clear();
        }
        if mask & FREE_TRNS != 0 {
            self.trans_alpha.clear();
            self.num_trans = 0;
            self.valid &= !INFO_tRNS;
        }
        if mask & FREE_ICCP != 0 {
            self.iccp_name.clear();
            self.iccp_profile.clear();
            self.valid &= !INFO_iCCP;
        }
        if mask & FREE_UNKN != 0 {
            self.unknown.clear();
            self.unknown_c.clear();
        }
        if mask & FREE_EXIF != 0 {
            self.exif.clear();
            self.valid &= !INFO_eXIf;
        }
        if mask & FREE_HIST != 0 {
            self.hist.clear();
            self.valid &= !INFO_hIST;
        }
        if mask & FREE_PLTE != 0 {
            self.palette.clear();
            self.valid &= !INFO_PLTE;
        }
    }
}

impl Default for Info {
    fn default() -> Self {
        Info::new()
    }
}

pub unsafe fn free_rows(p: *mut Png, info: *mut Info) {
    let i = &mut *info;
    if i.free_me & FREE_ROWS != 0 && !i.row_pointers.is_null() {
        for y in 0..i.height as usize {
            dealloc(p, *i.row_pointers.add(y) as *mut c_void);
        }
        dealloc(p, i.row_pointers as *mut c_void);
        i.row_pointers = core::ptr::null_mut();
        i.valid &= !INFO_IDAT;
    }
    i.free_me &= !FREE_ROWS;
}

/// `be32`, `be16`.
pub fn be32(b: &[u8]) -> u32 {
    u32::from_be_bytes([b[0], b[1], b[2], b[3]])
}
pub fn be16(b: &[u8]) -> u16 {
    u16::from_be_bytes([b[0], b[1]])
}

/// What libpng's chunk table (`read_chunks` in `pngrutil.c`) says about a
/// known ancillary chunk: (max length, min length, must be before, must be
/// after, may repeat). `u32::MAX` as max length: no check; 0: the chunk
/// size limit.
fn table(ty: u32) -> Option<(u32, u32, u32, u32, bool)> {
    const NO: u32 = u32::MAX;
    const LIM: u32 = 0;
    let hcol = HAVE_PLTE | HAVE_IDAT;
    let lkmin = 5;
    Some(match &ty.to_be_bytes() {
        b"cHRM" => (32, 32, hcol, HAVE_IHDR, false),
        b"gAMA" => (4, 4, hcol, HAVE_IHDR, false),
        b"iCCP" => (NO, lkmin, hcol, HAVE_IHDR, false),
        b"sBIT" => (4, 1, hcol, HAVE_IHDR, false),
        b"sRGB" => (1, 1, hcol, HAVE_IHDR, false),
        b"eXIf" => (LIM, 4, 0, HAVE_IHDR, false),
        b"tEXt" => (NO, 2, 0, HAVE_IHDR, true),
        b"zTXt" => (LIM, lkmin, 0, HAVE_IHDR, true),
        b"iTXt" => (NO, 6, 0, HAVE_IHDR, true),
        b"bKGD" => (6, 1, HAVE_IDAT, HAVE_IHDR, false),
        b"hIST" => (1024, 0, HAVE_IDAT, HAVE_PLTE, false),
        b"pHYs" => (9, 9, HAVE_IDAT, HAVE_IHDR, false),
        b"tIME" => (7, 7, 0, HAVE_IHDR, false),
        b"oFFs" => (9, 9, HAVE_IDAT, HAVE_IHDR, false),
        _ => return None,
    })
}

/// Whether this build handles the chunk itself (libpng's known chunks
/// with a handler in `pnglibconf.h`), other than the critical ones and
/// tRNS, which the verified parser reads.
pub fn is_known(ty: u32) -> bool {
    table(ty).is_some()
}

/// `Png::seen` bit for bKGD.
pub const SEEN_BKGD: u32 = 64;

/// Bit for `Png::seen`.
fn seen_bit(ty: u32) -> u32 {
    match &ty.to_be_bytes() {
        b"cHRM" => 1,
        b"gAMA" => 2,
        b"iCCP" => 4,
        b"sBIT" => 8,
        b"sRGB" => 16,
        b"eXIf" => 32,
        b"bKGD" => SEEN_BKGD,
        b"hIST" => 128,
        b"pHYs" => 256,
        b"tIME" => 512,
        b"oFFs" => 1024,
        _ => 0,
    }
}

/// Decompresses a zlib stream of at most `limit` bytes.
fn inflate(d: &[u8], limit: usize) -> Result<Vec<u8>, &'static str> {
    match Decompressor::new().decompress_vec(Format::Zlib, d, limit) {
        Ok((v, _)) => Ok(v),
        Err(verilith_zlib::Error::InsufficientSpace) => Err("insufficient memory"),
        Err(_) => Err("bad compressed data"),
    }
}

/// libpng's text and unknown chunk cache: whether there is room for one
/// more (`user_chunk_cache_max`).
unsafe fn cache_ok(p: *mut Png) -> R<bool> {
    let c = (*p).chunk_cache_max;
    if c != 0 {
        if c == 1 {
            return Ok(false);
        }
        (*p).chunk_cache_max -= 1;
        if (*p).chunk_cache_max == 1 {
            chunk_benign(p, "no space in chunk cache")?;
            return Ok(false);
        }
    }
    Ok(true)
}

/// `png_handle_chunk` for a known ancillary chunk whose CRC was checked.
pub unsafe fn handle(p: *mut Png, info: *mut Info, ty: u32, d: &[u8]) -> R<()> {
    let (max, min, before, after, multiple) = match table(ty) {
        Some(t) => t,
        None => return Ok(()),
    };
    let mode = (*p).mode;
    let len = d.len() as u32;
    let bit = seen_bit(ty);
    let msg = if mode & before != 0 || mode & after != after {
        Some("out of place")
    } else if !multiple && (*p).seen & bit != 0 {
        Some("duplicate")
    } else if len < min {
        Some("too short")
    } else if max == 0 && len as usize > (*p).chunk_malloc_max.max(1) {
        Some("length exceeds libpng limit")
    } else if max != u32::MAX && max != 0 && len > max {
        Some("too long")
    } else {
        None
    };
    // libpng reads the chunk (checking its CRC) before reporting what is
    // wrong with it, and discards a chunk with a bad CRC.
    if let Some(m) = msg {
        super::read::crc_check(p, false)?;
        return chunk_benign(p, m);
    }
    // The text chunks count against the chunk cache before libpng reads
    // them.
    let text = matches!(&ty.to_be_bytes(), b"tEXt" | b"zTXt" | b"iTXt");
    if text && !cache_ok(p)? {
        super::read::crc_check(p, false)?;
        return Ok(());
    }
    if super::read::crc_check(p, false)? {
        // A bad CRC: libpng still reports what it checks before reading
        // the data (or, for iCCP, before checking the CRC).
        return bad_crc_checks(p, ty, d);
    }
    if info.is_null() {
        return Ok(());
    }
    let ok = handle_one(p, info, ty, d)?;
    if ok {
        (*p).seen |= bit;
    }
    Ok(())
}

/// The warnings libpng gives for a chunk whose CRC is bad.
unsafe fn bad_crc_checks(p: *mut Png, ty: u32, d: &[u8]) -> R<()> {
    let ct = (*p).color_type;
    let n = d.len();
    let m = match &ty.to_be_bytes() {
        b"sBIT" => {
            let want = if ct == CT_PALETTE { 3 } else { (*p).channels as usize };
            (n != want).then_some("bad length")
        }
        b"bKGD" => {
            if ct == CT_PALETTE && (*p).mode & HAVE_PLTE == 0 {
                Some("out of place")
            } else {
                let want = if ct == CT_PALETTE { 1 } else if ct & COLOR_MASK_COLOR != 0 { 6 } else { 2 };
                (n != want).then_some("invalid")
            }
        }
        b"hIST" => (n % 2 != 0 || n / 2 != (*p).num_palette as usize || n / 2 > 256).then_some("invalid"),
        b"iCCP" => {
            // libpng checks the profile and reports what is wrong with it
            // before the CRC; a good profile is then dropped.
            let mut scratch = Info::new();
            let _ = handle_one(p, &mut scratch, ty, d)?;
            None
        }
        _ => None,
    };
    match m {
        Some(m) => chunk_benign(p, m),
        None => Ok(()),
    }
}

/// The handlers. `Ok(true)`: stored.
unsafe fn handle_one(p: *mut Png, info: *mut Info, ty: u32, d: &[u8]) -> R<bool> {
    let ct = (*p).color_type;
    let bd = (*p).bit_depth;
    match &ty.to_be_bytes() {
        b"gAMA" => {
            let g = be32(d);
            if g > 0x7fff_ffff {
                chunk_benign(p, "invalid")?;
                return Ok(false);
            }
            if g == 0 {
                // png_set_gAMA_fixed: "Invalid file gamma"
                chunk_benign(p, "invalid")?;
                return Ok(false);
            }
            (*info).gamma = g as i32;
            (*info).valid |= INFO_gAMA;
        }
        b"sRGB" => {
            if d[0] > 3 {
                chunk_benign(p, "invalid")?;
                return Ok(false);
            }
            (*info).srgb = d[0] as c_int;
            (*info).valid |= INFO_sRGB;
        }
        b"cHRM" => {
            let mut v = [0i32; 8];
            for (k, x) in v.iter_mut().enumerate() {
                // Signed, as libpng reads them; only -2^31 is refused.
                let u = be32(&d[4 * k..]);
                if u == 0x8000_0000 {
                    chunk_benign(p, "invalid")?;
                    return Ok(false);
                }
                *x = u as i32;
            }
            (*info).chrm = v;
            (*info).valid |= INFO_cHRM;
        }
        b"sBIT" => {
            let (n, sd) = if ct == CT_PALETTE { (3usize, 8u8) } else { ((*p).channels as usize, bd) };
            if d.len() != n {
                chunk_benign(p, "bad length")?;
                return Ok(false);
            }
            let mut b = [sd; 4];
            b[..n].copy_from_slice(d);
            if b[..n].iter().any(|&x| x == 0 || x > sd) {
                chunk_benign(p, "invalid")?;
                return Ok(false);
            }
            let s = if ct & COLOR_MASK_COLOR != 0 {
                png_color_8 { red: b[0], green: b[1], blue: b[2], gray: 0, alpha: b[3] }
            } else {
                png_color_8 { red: b[0], green: b[0], blue: b[0], gray: b[0], alpha: b[1] }
            };
            (*p).sig_bit = s;
            (*info).sig_bit = s;
            (*info).valid |= INFO_sBIT;
        }
        b"bKGD" => {
            let n = if ct == CT_PALETTE {
                if (*p).mode & HAVE_PLTE == 0 {
                    chunk_benign(p, "out of place")?;
                    return Ok(false);
                }
                1
            } else if ct & COLOR_MASK_COLOR != 0 {
                6
            } else {
                2
            };
            if d.len() != n {
                chunk_benign(p, "invalid")?;
                return Ok(false);
            }
            let mut bg = png_color_16::default();
            if ct == CT_PALETTE {
                bg.index = d[0];
                let np = (*info).palette.len();
                if np != 0 {
                    if d[0] as usize >= np {
                        chunk_benign(p, "invalid index")?;
                        return Ok(false);
                    }
                    let c = (*p).palette[d[0] as usize];
                    bg.red = c.red as u16;
                    bg.green = c.green as u16;
                    bg.blue = c.blue as u16;
                }
            } else if ct & COLOR_MASK_COLOR == 0 {
                if bd <= 8 && (d[0] != 0 || d[1] as u32 >= 1u32 << bd) {
                    chunk_benign(p, "invalid gray level")?;
                    return Ok(false);
                }
                let g = be16(d);
                bg.red = g;
                bg.green = g;
                bg.blue = g;
                bg.gray = g;
            } else {
                if bd <= 8 && (d[0] != 0 || d[2] != 0 || d[4] != 0) {
                    chunk_benign(p, "invalid color")?;
                    return Ok(false);
                }
                bg.red = be16(d);
                bg.green = be16(&d[2..]);
                bg.blue = be16(&d[4..]);
            }
            (*info).background = bg;
            (*info).valid |= INFO_bKGD;
        }
        b"hIST" => {
            let n = d.len() / 2;
            if d.len() != 2 * n || n != (*p).num_palette as usize || n > 256 {
                chunk_benign(p, "invalid")?;
                return Ok(false);
            }
            let h: Vec<u16> = (0..n).map(|i| be16(&d[2 * i..])).collect();
            (*info).hist = h;
            (*info).valid |= INFO_hIST;
            (*info).free_me |= FREE_HIST;
        }
        b"pHYs" => {
            (*info).phys = (be32(d), be32(&d[4..]), d[8] as c_int);
            (*info).valid |= INFO_pHYs;
        }
        b"oFFs" => {
            (*info).offs = (be32(d) as i32, be32(&d[4..]) as i32, d[8] as c_int);
            (*info).valid |= INFO_oFFs;
        }
        b"tIME" => {
            (*info).time = png_time { year: be16(d), month: d[2], day: d[3], hour: d[4], minute: d[5], second: d[6] };
            (*info).valid |= INFO_tIME;
        }
        b"eXIf" => {
            let h = be32(d);
            if h != 0x4949_2A00 && h != 0x4D4D_002A {
                chunk_benign(p, "invalid")?;
                return Ok(false);
            }
            (*info).exif = d.to_vec();
            (*info).valid |= INFO_eXIf;
            (*info).free_me |= FREE_EXIF;
        }
        b"tEXt" => {
            let k = d.iter().position(|&c| c == 0).unwrap_or(d.len());
            let text = if k < d.len() { &d[k + 1..] } else { &d[d.len()..] };
            (*info).add_text(-1, &d[..k], text, None, None);
        }
        b"zTXt" => {
            let k = d.iter().position(|&c| c == 0).unwrap_or(d.len());
            let err = if !(1..=79).contains(&k) {
                Some("bad keyword")
            } else if k + 3 > d.len() {
                Some("truncated")
            } else if d[k + 1] != 0 {
                Some("unknown compression type")
            } else {
                match inflate(&d[k + 2..], (*p).chunk_malloc_max) {
                    Ok(t) => {
                        (*info).add_text(0, &d[..k], &t, None, None);
                        None
                    }
                    Err(m) => Some(m),
                }
            };
            if let Some(m) = err {
                chunk_benign(p, m)?;
                return Ok(false);
            }
        }
        b"iTXt" => {
            let k = d.iter().position(|&c| c == 0).unwrap_or(d.len());
            let err = if !(1..=79).contains(&k) {
                Some("bad keyword")
            } else if k + 5 > d.len() {
                Some("truncated")
            } else if d[k + 1] == 0 || (d[k + 1] == 1 && d[k + 2] == 0) {
                let compressed = d[k + 1] != 0;
                let lang_off = k + 3;
                let mut q = lang_off;
                while q < d.len() && d[q] != 0 {
                    q += 1;
                }
                let tk_off = q + 1;
                q = tk_off;
                while q < d.len() && d[q] != 0 {
                    q += 1;
                }
                q += 1;
                let lang = &d[lang_off.min(d.len())..];
                let tk = &d[tk_off.min(d.len())..];
                if !compressed && q <= d.len() {
                    (*info).add_text(1, &d[..k], &d[q..], Some(lang), Some(tk));
                    None
                } else if compressed && q < d.len() {
                    match inflate(&d[q..], (*p).chunk_malloc_max) {
                        Ok(t) => {
                            (*info).add_text(2, &d[..k], &t, Some(lang), Some(tk));
                            None
                        }
                        Err(m) => Some(m),
                    }
                } else {
                    Some("truncated")
                }
            } else {
                Some("bad compression info")
            };
            if let Some(m) = err {
                chunk_benign(p, m)?;
                return Ok(false);
            }
        }
        b"iCCP" => {
            let k = d.iter().take(80).position(|&c| c == 0).unwrap_or(80.min(d.len()));
            // libpng reads up to 81 bytes for the keyword and wants a
            // minimal zlib stream after them.
            let err = if d.len() - d.len().min(81) < 11 {
                Some("too short")
            } else if !(1..=79).contains(&k) {
                Some("bad keyword")
            } else if k + 1 >= d.len() || d[k + 1] != 0 {
                Some("bad compression method")
            } else {
                match inflate(&d[k + 2..], (*p).chunk_malloc_max) {
                    Ok(prof) => {
                        if prof.len() < 132 {
                            Some("too short")
                        } else if be32(&prof) as usize != prof.len() {
                            Some("profile length does not match")
                        } else if &prof[36..40] != b"acsp" {
                            Some("invalid signature")
                        } else {
                            let mut name = d[..k].to_vec();
                            name.push(0);
                            (*info).iccp_name = name;
                            (*info).iccp_profile = prof;
                            (*info).valid |= INFO_iCCP;
                            (*info).free_me |= FREE_ICCP;
                            None
                        }
                    }
                    Err(m) => Some(m),
                }
            };
            if let Some(m) = err {
                chunk_benign(p, m)?;
                return Ok(false);
            }
        }
        _ => return Ok(false),
    }
    Ok(true)
}

// ---------------------------------------------------------------------------
// png_get_* and png_set_*
// ---------------------------------------------------------------------------

unsafe fn ok(p: png_structp, i: *const Info) -> bool {
    !p.is_null() && !i.is_null()
}

api! {
    pub unsafe extern "C" fn png_create_info_struct(p: png_structp) -> png_infop {
        if p.is_null() {
            return core::ptr::null_mut();
        }
        Box::into_raw(Box::new(Info::new()))
    }

    pub unsafe extern "C" fn png_destroy_info_struct(p: png_structp, info_ptr_ptr: *mut png_infop) {
        if p.is_null() || info_ptr_ptr.is_null() || (*info_ptr_ptr).is_null() {
            return;
        }
        free_rows(p, *info_ptr_ptr);
        drop(Box::from_raw(*info_ptr_ptr));
        *info_ptr_ptr = core::ptr::null_mut();
    }

    pub unsafe extern "C" fn png_info_init_3(info_ptr_ptr: *mut png_infop, size: usize) {
        if info_ptr_ptr.is_null() {
            return;
        }
        let _ = size;
        if !(*info_ptr_ptr).is_null() {
            free_rows(core::ptr::null_mut(), *info_ptr_ptr);
            drop(Box::from_raw(*info_ptr_ptr));
        }
        *info_ptr_ptr = Box::into_raw(Box::new(Info::new()));
    }

    pub unsafe extern "C" fn png_free_data(p: png_structp, info: png_infop, mask: png_uint_32, num: c_int) {
        if !ok(p, info) {
            return;
        }
        let i = &mut *info;
        if mask & FREE_TEXT != 0 && num >= 0 {
            if (num as usize) < i.text.len() {
                i.text.remove(num as usize);
                i.rebuild_text();
            }
        } else if mask & FREE_TEXT != 0 {
            i.clear(FREE_TEXT);
        }
        if mask & FREE_UNKN != 0 && num >= 0 {
            if (num as usize) < i.unknown.len() {
                i.unknown.remove(num as usize);
                i.unknown_c = i.unknown.iter().map(|u| u.0).collect();
            }
        } else if mask & FREE_UNKN != 0 {
            i.clear(FREE_UNKN);
        }
        i.clear(mask & !(FREE_TEXT | FREE_UNKN));
        if mask & FREE_ROWS != 0 {
            free_rows(p, info);
        }
    }

    pub unsafe extern "C" fn png_data_freer(p: png_structp, info: png_infop, freer: c_int, mask: png_uint_32) {
        if !ok(p, info) {
            return;
        }
        if freer == 1 {
            (*info).free_me |= mask;
        } else if freer == 2 {
            (*info).free_me &= !mask;
        } else {
            let _ = app_error(p, "Unknown freer parameter in png_data_freer");
        }
    }

    pub unsafe extern "C" fn png_get_valid(p: png_structp, info: png_infop, flag: png_uint_32) -> png_uint_32 {
        if !ok(p, info) {
            return 0;
        }
        // libpng 1.6.59: a gAMA, cHRM or iCCP overridden by sRGB, and the
        // other way round, are still all reported.
        (*info).valid & flag
    }

    pub unsafe extern "C" fn png_get_rowbytes(p: png_structp, info: png_infop) -> usize {
        if !ok(p, info) { 0 } else { (*info).rowbytes }
    }

    pub unsafe extern "C" fn png_get_rows(p: png_structp, info: png_infop) -> *mut *mut u8 {
        if !ok(p, info) { core::ptr::null_mut() } else { (*info).row_pointers }
    }

    pub unsafe extern "C" fn png_set_rows(p: png_structp, info: png_infop, rows: *mut *mut u8) {
        if !ok(p, info) {
            return;
        }
        if !(*info).row_pointers.is_null() && (*info).row_pointers != rows {
            free_rows(p, info);
        }
        (*info).row_pointers = rows;
        if !rows.is_null() {
            (*info).valid |= INFO_IDAT;
        }
    }

    pub unsafe extern "C" fn png_get_image_width(p: png_structp, info: png_infop) -> png_uint_32 {
        if !ok(p, info) { 0 } else { (*info).width }
    }

    pub unsafe extern "C" fn png_get_image_height(p: png_structp, info: png_infop) -> png_uint_32 {
        if !ok(p, info) { 0 } else { (*info).height }
    }

    pub unsafe extern "C" fn png_get_bit_depth(p: png_structp, info: png_infop) -> png_byte {
        if !ok(p, info) { 0 } else { (*info).bit_depth }
    }

    pub unsafe extern "C" fn png_get_color_type(p: png_structp, info: png_infop) -> png_byte {
        if !ok(p, info) { 0 } else { (*info).color_type }
    }

    pub unsafe extern "C" fn png_get_filter_type(p: png_structp, info: png_infop) -> png_byte {
        if !ok(p, info) { 0 } else { (*info).filter_type }
    }

    pub unsafe extern "C" fn png_get_interlace_type(p: png_structp, info: png_infop) -> png_byte {
        if !ok(p, info) { 0 } else { (*info).interlace_type }
    }

    pub unsafe extern "C" fn png_get_compression_type(p: png_structp, info: png_infop) -> png_byte {
        if !ok(p, info) { 0 } else { (*info).compression_type }
    }

    pub unsafe extern "C" fn png_get_channels(p: png_structp, info: png_infop) -> png_byte {
        if !ok(p, info) { 0 } else { (*info).channels }
    }

    pub unsafe extern "C" fn png_get_signature(p: png_structp, info: png_infop) -> *const u8 {
        if !ok(p, info) { core::ptr::null() } else { (*info).signature.as_ptr() }
    }

    pub unsafe extern "C" fn png_get_IHDR(p: png_structp, info: png_infop, width: *mut png_uint_32, height: *mut png_uint_32,
        bit_depth: *mut c_int, color_type: *mut c_int, interlace: *mut c_int, compression: *mut c_int, filter: *mut c_int) -> png_uint_32 {
        if !ok(p, info) {
            return 0;
        }
        let i = &*info;
        if !width.is_null() { *width = i.width; }
        if !height.is_null() { *height = i.height; }
        if !bit_depth.is_null() { *bit_depth = i.bit_depth as c_int; }
        if !color_type.is_null() { *color_type = i.color_type as c_int; }
        if !compression.is_null() { *compression = i.compression_type as c_int; }
        if !filter.is_null() { *filter = i.filter_type as c_int; }
        if !interlace.is_null() { *interlace = i.interlace_type as c_int; }
        let r = super::read::check_ihdr(p, i.width, i.height, i.bit_depth, i.color_type, i.interlace_type, i.compression_type, i.filter_type);
        run(p, r, ());
        1
    }

    pub unsafe extern "C" fn png_set_IHDR(p: png_structp, info: png_infop, width: png_uint_32, height: png_uint_32,
        bit_depth: c_int, color_type: c_int, interlace: c_int, compression: c_int, filter: c_int) {
        if !ok(p, info) {
            return;
        }
        let i = &mut *info;
        i.width = width;
        i.height = height;
        i.bit_depth = bit_depth as u8;
        i.color_type = color_type as u8;
        i.compression_type = compression as u8;
        i.filter_type = filter as u8;
        i.interlace_type = interlace as u8;
        i.channels = match i.color_type { CT_RGB => 3, CT_GA => 2, CT_RGBA => 4, _ => 1 };
        i.pixel_depth = i.channels * i.bit_depth;
        i.rowbytes = rowbytes(i.pixel_depth as u32, width);
    }

    pub unsafe extern "C" fn png_get_PLTE(p: png_structp, info: png_infop, palette: *mut *mut png_color, num: *mut c_int) -> png_uint_32 {
        if !ok(p, info) || palette.is_null() || (*info).valid & INFO_PLTE == 0 {
            return 0;
        }
        *palette = (*info).palette.as_mut_ptr();
        if !num.is_null() {
            *num = (*info).palette.len() as c_int;
        }
        INFO_PLTE
    }

    pub unsafe extern "C" fn png_set_PLTE(p: png_structp, info: png_infop, palette: *const png_color, num: c_int) {
        if !ok(p, info) {
            return;
        }
        if !(0..=256).contains(&num) || (num > 0 && palette.is_null()) {
            let _ = app_error(p, "Invalid palette");
            return;
        }
        let pal = if num > 0 { core::slice::from_raw_parts(palette, num as usize).to_vec() } else { Vec::new() };
        (*info).palette = pal;
        (*info).valid |= INFO_PLTE;
        (*info).free_me |= FREE_PLTE;
    }

    pub unsafe extern "C" fn png_get_tRNS(p: png_structp, info: png_infop, trans_alpha: *mut *mut u8, num_trans: *mut c_int,
        trans_color: *mut *mut png_color_16) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_tRNS == 0 {
            return 0;
        }
        let i = &mut *info;
        if i.color_type == CT_PALETTE {
            if !trans_alpha.is_null() {
                *trans_alpha = i.trans_alpha.as_mut_ptr();
            }
            if !trans_color.is_null() {
                *trans_color = &mut i.trans_color;
            }
        } else {
            if !trans_color.is_null() {
                *trans_color = &mut i.trans_color;
            }
            if !trans_alpha.is_null() {
                *trans_alpha = core::ptr::null_mut();
            }
        }
        if !num_trans.is_null() {
            *num_trans = i.num_trans as c_int;
        }
        INFO_tRNS
    }

    pub unsafe extern "C" fn png_set_tRNS(p: png_structp, info: png_infop, trans_alpha: *const u8, num_trans: c_int, trans_color: *const png_color_16) {
        if !ok(p, info) {
            return;
        }
        let i = &mut *info;
        if !trans_alpha.is_null() && num_trans > 0 {
            let n = (num_trans as usize).min(256);
            i.trans_alpha = core::slice::from_raw_parts(trans_alpha, n).to_vec();
        }
        if !trans_color.is_null() {
            i.trans_color = *trans_color;
        }
        i.num_trans = num_trans.clamp(0, 256) as u16;
        if num_trans != 0 {
            i.valid |= INFO_tRNS;
            i.free_me |= FREE_TRNS;
        }
    }

    pub unsafe extern "C" fn png_get_gAMA_fixed(p: png_structp, info: png_infop, g: *mut png_fixed_point) -> png_uint_32 {
        if !ok(p, info) || g.is_null() || (*info).valid & INFO_gAMA == 0 {
            return 0;
        }
        *g = (*info).gamma;
        INFO_gAMA
    }

    pub unsafe extern "C" fn png_get_gAMA(p: png_structp, info: png_infop, g: *mut f64) -> png_uint_32 {
        if !ok(p, info) || g.is_null() || (*info).valid & INFO_gAMA == 0 {
            return 0;
        }
        *g = (*info).gamma as f64 / 100000.0;
        INFO_gAMA
    }

    pub unsafe extern "C" fn png_set_gAMA_fixed(p: png_structp, info: png_infop, g: png_fixed_point) {
        if !ok(p, info) {
            return;
        }
        if g <= 0 {
            warn(p, "Invalid gamma value");
            return;
        }
        (*info).gamma = g;
        (*info).valid |= INFO_gAMA;
    }

    pub unsafe extern "C" fn png_set_gAMA(p: png_structp, info: png_infop, g: f64) {
        png_set_gAMA_fixed(p, info, (g * 100000.0 + 0.5) as i32)
    }

    pub unsafe extern "C" fn png_get_sRGB(p: png_structp, info: png_infop, intent: *mut c_int) -> png_uint_32 {
        if !ok(p, info) || intent.is_null() || (*info).valid & INFO_sRGB == 0 {
            return 0;
        }
        *intent = (*info).srgb;
        INFO_sRGB
    }

    pub unsafe extern "C" fn png_set_sRGB(p: png_structp, info: png_infop, intent: c_int) {
        if !ok(p, info) {
            return;
        }
        (*info).srgb = intent;
        (*info).valid |= INFO_sRGB;
    }

    pub unsafe extern "C" fn png_set_sRGB_gAMA_and_cHRM(p: png_structp, info: png_infop, intent: c_int) {
        if !ok(p, info) {
            return;
        }
        png_set_sRGB(p, info, intent);
        png_set_gAMA_fixed(p, info, 45455);
        png_set_cHRM_fixed(p, info, 31270, 32900, 64000, 33000, 30000, 60000, 15000, 6000);
    }

    pub unsafe extern "C" fn png_get_cHRM_fixed(p: png_structp, info: png_infop, wx: *mut i32, wy: *mut i32, rx: *mut i32, ry: *mut i32,
        gx: *mut i32, gy: *mut i32, bx: *mut i32, by: *mut i32) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_cHRM == 0 {
            return 0;
        }
        let c = (*info).chrm;
        for (dst, v) in [wx, wy, rx, ry, gx, gy, bx, by].into_iter().zip(c) {
            if !dst.is_null() {
                *dst = v;
            }
        }
        INFO_cHRM
    }

    pub unsafe extern "C" fn png_get_cHRM(p: png_structp, info: png_infop, wx: *mut f64, wy: *mut f64, rx: *mut f64, ry: *mut f64,
        gx: *mut f64, gy: *mut f64, bx: *mut f64, by: *mut f64) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_cHRM == 0 {
            return 0;
        }
        let c = (*info).chrm;
        for (dst, v) in [wx, wy, rx, ry, gx, gy, bx, by].into_iter().zip(c) {
            if !dst.is_null() {
                *dst = v as f64 / 100000.0;
            }
        }
        INFO_cHRM
    }

    pub unsafe extern "C" fn png_set_cHRM_fixed(p: png_structp, info: png_infop, wx: i32, wy: i32, rx: i32, ry: i32, gx: i32, gy: i32, bx: i32, by: i32) {
        if !ok(p, info) {
            return;
        }
        (*info).chrm = [wx, wy, rx, ry, gx, gy, bx, by];
        (*info).valid |= INFO_cHRM;
    }

    pub unsafe extern "C" fn png_set_cHRM(p: png_structp, info: png_infop, wx: f64, wy: f64, rx: f64, ry: f64, gx: f64, gy: f64, bx: f64, by: f64) {
        let f = |v: f64| (v * 100000.0 + 0.5).floor() as i32;
        png_set_cHRM_fixed(p, info, f(wx), f(wy), f(rx), f(ry), f(gx), f(gy), f(bx), f(by))
    }

    pub unsafe extern "C" fn png_get_cHRM_XYZ_fixed(p: png_structp, info: png_infop, rx: *mut i32, ry: *mut i32, rz: *mut i32,
        gx: *mut i32, gy: *mut i32, gz: *mut i32, bx: *mut i32, by: *mut i32, bz: *mut i32) -> png_uint_32 {
        let mut d = [0f64; 9];
        let r = png_get_cHRM_XYZ(p, info, &mut d[0], &mut d[1], &mut d[2], &mut d[3], &mut d[4], &mut d[5], &mut d[6], &mut d[7], &mut d[8]);
        if r == 0 {
            return 0;
        }
        for (dst, v) in [rx, ry, rz, gx, gy, gz, bx, by, bz].into_iter().zip(d) {
            if !dst.is_null() {
                *dst = (v * 100000.0 + 0.5).floor() as i32;
            }
        }
        r
    }

    /// The XYZ end points of the cHRM chromaticities, for a white point of
    /// Y = 1.
    pub unsafe extern "C" fn png_get_cHRM_XYZ(p: png_structp, info: png_infop, rx: *mut f64, ry: *mut f64, rz: *mut f64,
        gx: *mut f64, gy: *mut f64, gz: *mut f64, bx: *mut f64, by: *mut f64, bz: *mut f64) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_cHRM == 0 {
            return 0;
        }
        let c: Vec<f64> = (*info).chrm.iter().map(|&v| v as f64 / 100000.0).collect();
        let (wx, wy, xr, yr, xg, yg, xb, yb) = (c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]);
        if wy == 0.0 || yr == 0.0 || yg == 0.0 || yb == 0.0 {
            return 0;
        }
        // Solve for the luminances that make the primaries sum to white.
        let w = [wx / wy, 1.0, (1.0 - wx - wy) / wy];
        let m = [[xr / yr, xg / yg, xb / yb], [1.0, 1.0, 1.0], [(1.0 - xr - yr) / yr, (1.0 - xg - yg) / yg, (1.0 - xb - yb) / yb]];
        let det = |a: [[f64; 3]; 3]| {
            a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1]) - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
                + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
        };
        let dm = det(m);
        if dm == 0.0 {
            return 0;
        }
        let mut lum = [0f64; 3];
        for (k, l) in lum.iter_mut().enumerate() {
            let mut a = m;
            for r in 0..3 {
                a[r][k] = w[r];
            }
            *l = det(a) / dm;
        }
        let out = [
            (rx, m[0][0] * lum[0]), (ry, lum[0]), (rz, m[2][0] * lum[0]),
            (gx, m[0][1] * lum[1]), (gy, lum[1]), (gz, m[2][1] * lum[1]),
            (bx, m[0][2] * lum[2]), (by, lum[2]), (bz, m[2][2] * lum[2]),
        ];
        for (dst, v) in out {
            if !dst.is_null() {
                *dst = v;
            }
        }
        INFO_cHRM
    }

    pub unsafe extern "C" fn png_set_cHRM_XYZ(p: png_structp, info: png_infop, rx: f64, ry: f64, rz: f64, gx: f64, gy: f64, gz: f64, bx: f64, by: f64, bz: f64) {
        let sr = rx + ry + rz;
        let sg = gx + gy + gz;
        let sb = bx + by + bz;
        let (wx, wy, wz) = (rx + gx + bx, ry + gy + by, rz + gz + bz);
        let sw = wx + wy + wz;
        if sr == 0.0 || sg == 0.0 || sb == 0.0 || sw == 0.0 {
            warn(p, "invalid end points");
            return;
        }
        png_set_cHRM(p, info, wx / sw, wy / sw, rx / sr, ry / sr, gx / sg, gy / sg, bx / sb, by / sb)
    }

    pub unsafe extern "C" fn png_set_cHRM_XYZ_fixed(p: png_structp, info: png_infop, rx: i32, ry: i32, rz: i32, gx: i32, gy: i32, gz: i32, bx: i32, by: i32, bz: i32) {
        let f = |v: i32| v as f64 / 100000.0;
        png_set_cHRM_XYZ(p, info, f(rx), f(ry), f(rz), f(gx), f(gy), f(gz), f(bx), f(by), f(bz))
    }

    pub unsafe extern "C" fn png_get_iCCP(p: png_structp, info: png_infop, name: *mut *mut c_char, compression: *mut c_int,
        profile: *mut *mut u8, len: *mut png_uint_32) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_iCCP == 0 || name.is_null() || profile.is_null() || len.is_null() {
            return 0;
        }
        *name = (*info).iccp_name.as_mut_ptr() as *mut c_char;
        if !compression.is_null() {
            *compression = 0;
        }
        *profile = (*info).iccp_profile.as_mut_ptr();
        *len = (*info).iccp_profile.len() as u32;
        INFO_iCCP
    }

    pub unsafe extern "C" fn png_set_iCCP(p: png_structp, info: png_infop, name: *const c_char, compression: c_int, profile: *const u8, len: png_uint_32) {
        if !ok(p, info) || name.is_null() || profile.is_null() {
            return;
        }
        let _ = compression;
        if len < 132 {
            let _ = app_error(p, "Invalid iCCP profile length");
            return;
        }
        let n = cstr_len(name);
        let mut v = core::slice::from_raw_parts(name as *const u8, n).to_vec();
        v.push(0);
        (*info).iccp_name = v;
        (*info).iccp_profile = core::slice::from_raw_parts(profile, len as usize).to_vec();
        (*info).valid |= INFO_iCCP;
        (*info).free_me |= FREE_ICCP;
    }

    pub unsafe extern "C" fn png_get_sBIT(p: png_structp, info: png_infop, sig: *mut *mut png_color_8) -> png_uint_32 {
        if !ok(p, info) || sig.is_null() || (*info).valid & INFO_sBIT == 0 {
            return 0;
        }
        *sig = &mut (*info).sig_bit;
        INFO_sBIT
    }

    pub unsafe extern "C" fn png_set_sBIT(p: png_structp, info: png_infop, sig: *const png_color_8) {
        if !ok(p, info) || sig.is_null() {
            return;
        }
        (*info).sig_bit = *sig;
        (*info).valid |= INFO_sBIT;
    }

    pub unsafe extern "C" fn png_get_bKGD(p: png_structp, info: png_infop, bg: *mut *mut png_color_16) -> png_uint_32 {
        if !ok(p, info) || bg.is_null() || (*info).valid & INFO_bKGD == 0 {
            return 0;
        }
        *bg = &mut (*info).background;
        INFO_bKGD
    }

    pub unsafe extern "C" fn png_set_bKGD(p: png_structp, info: png_infop, bg: *const png_color_16) {
        if !ok(p, info) || bg.is_null() {
            return;
        }
        (*info).background = *bg;
        (*info).valid |= INFO_bKGD;
    }

    pub unsafe extern "C" fn png_get_hIST(p: png_structp, info: png_infop, hist: *mut *mut u16) -> png_uint_32 {
        if !ok(p, info) || hist.is_null() || (*info).valid & INFO_hIST == 0 {
            return 0;
        }
        *hist = (*info).hist.as_mut_ptr();
        INFO_hIST
    }

    pub unsafe extern "C" fn png_set_hIST(p: png_structp, info: png_infop, hist: *const u16) {
        if !ok(p, info) || hist.is_null() {
            return;
        }
        let n = (*info).palette.len();
        if n == 0 || n > 256 {
            warn(p, "Invalid palette size, hIST allocation skipped");
            return;
        }
        (*info).hist = core::slice::from_raw_parts(hist, n).to_vec();
        (*info).valid |= INFO_hIST;
        (*info).free_me |= FREE_HIST;
    }

    pub unsafe extern "C" fn png_get_pHYs(p: png_structp, info: png_infop, rx: *mut png_uint_32, ry: *mut png_uint_32, unit: *mut c_int) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_pHYs == 0 {
            return 0;
        }
        let (x, y, u) = (*info).phys;
        if !rx.is_null() { *rx = x; }
        if !ry.is_null() { *ry = y; }
        if !unit.is_null() { *unit = u; }
        INFO_pHYs
    }

    pub unsafe extern "C" fn png_set_pHYs(p: png_structp, info: png_infop, rx: png_uint_32, ry: png_uint_32, unit: c_int) {
        if !ok(p, info) {
            return;
        }
        (*info).phys = (rx, ry, unit);
        (*info).valid |= INFO_pHYs;
    }

    pub unsafe extern "C" fn png_get_pHYs_dpi(p: png_structp, info: png_infop, rx: *mut png_uint_32, ry: *mut png_uint_32, unit: *mut c_int) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_pHYs == 0 {
            return 0;
        }
        let (mut x, mut y, u) = (*info).phys;
        if u == 1 {
            x = ((x as f64) * 0.0254 + 0.5) as u32;
            y = ((y as f64) * 0.0254 + 0.5) as u32;
        }
        if !rx.is_null() { *rx = x; }
        if !ry.is_null() { *ry = y; }
        if !unit.is_null() { *unit = u; }
        INFO_pHYs
    }

    pub unsafe extern "C" fn png_get_x_pixels_per_meter(p: png_structp, info: png_infop) -> png_uint_32 {
        if ok(p, info) && (*info).valid & INFO_pHYs != 0 && (*info).phys.2 == 1 { (*info).phys.0 } else { 0 }
    }

    pub unsafe extern "C" fn png_get_y_pixels_per_meter(p: png_structp, info: png_infop) -> png_uint_32 {
        if ok(p, info) && (*info).valid & INFO_pHYs != 0 && (*info).phys.2 == 1 { (*info).phys.1 } else { 0 }
    }

    pub unsafe extern "C" fn png_get_pixels_per_meter(p: png_structp, info: png_infop) -> png_uint_32 {
        if ok(p, info) && (*info).valid & INFO_pHYs != 0 && (*info).phys.2 == 1 && (*info).phys.0 == (*info).phys.1 { (*info).phys.0 } else { 0 }
    }

    pub unsafe extern "C" fn png_get_pixel_aspect_ratio(p: png_structp, info: png_infop) -> f32 {
        if ok(p, info) && (*info).valid & INFO_pHYs != 0 && (*info).phys.0 != 0 {
            (*info).phys.1 as f32 / (*info).phys.0 as f32
        } else {
            0.0
        }
    }

    pub unsafe extern "C" fn png_get_pixel_aspect_ratio_fixed(p: png_structp, info: png_infop) -> png_fixed_point {
        if ok(p, info) && (*info).valid & INFO_pHYs != 0 && (*info).phys.0 != 0 && (*info).phys.0 <= 0x7fff_ffff && (*info).phys.1 <= 0x7fff_ffff {
            let r = (*info).phys.1 as f64 * 100000.0 / (*info).phys.0 as f64;
            if r <= i32::MAX as f64 { (r + 0.5).floor() as i32 } else { 0 }
        } else {
            0
        }
    }

    pub unsafe extern "C" fn png_get_pixels_per_inch(p: png_structp, info: png_infop) -> png_uint_32 {
        let m = png_get_pixels_per_meter(p, info);
        ((m as f64) * 0.0254 + 0.5) as u32
    }

    pub unsafe extern "C" fn png_get_x_pixels_per_inch(p: png_structp, info: png_infop) -> png_uint_32 {
        let m = png_get_x_pixels_per_meter(p, info);
        ((m as f64) * 0.0254 + 0.5) as u32
    }

    pub unsafe extern "C" fn png_get_y_pixels_per_inch(p: png_structp, info: png_infop) -> png_uint_32 {
        let m = png_get_y_pixels_per_meter(p, info);
        ((m as f64) * 0.0254 + 0.5) as u32
    }

    pub unsafe extern "C" fn png_get_oFFs(p: png_structp, info: png_infop, ox: *mut i32, oy: *mut i32, unit: *mut c_int) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_oFFs == 0 {
            return 0;
        }
        let (x, y, u) = (*info).offs;
        if !ox.is_null() { *ox = x; }
        if !oy.is_null() { *oy = y; }
        if !unit.is_null() { *unit = u; }
        INFO_oFFs
    }

    pub unsafe extern "C" fn png_set_oFFs(p: png_structp, info: png_infop, ox: i32, oy: i32, unit: c_int) {
        if !ok(p, info) {
            return;
        }
        (*info).offs = (ox, oy, unit);
        (*info).valid |= INFO_oFFs;
    }

    pub unsafe extern "C" fn png_get_x_offset_microns(p: png_structp, info: png_infop) -> png_int_32 {
        if ok(p, info) && (*info).valid & INFO_oFFs != 0 && (*info).offs.2 == 1 { (*info).offs.0 } else { 0 }
    }

    pub unsafe extern "C" fn png_get_y_offset_microns(p: png_structp, info: png_infop) -> png_int_32 {
        if ok(p, info) && (*info).valid & INFO_oFFs != 0 && (*info).offs.2 == 1 { (*info).offs.1 } else { 0 }
    }

    pub unsafe extern "C" fn png_get_x_offset_pixels(p: png_structp, info: png_infop) -> png_int_32 {
        if ok(p, info) && (*info).valid & INFO_oFFs != 0 && (*info).offs.2 == 0 { (*info).offs.0 } else { 0 }
    }

    pub unsafe extern "C" fn png_get_y_offset_pixels(p: png_structp, info: png_infop) -> png_int_32 {
        if ok(p, info) && (*info).valid & INFO_oFFs != 0 && (*info).offs.2 == 0 { (*info).offs.1 } else { 0 }
    }

    pub unsafe extern "C" fn png_get_x_offset_inches(p: png_structp, info: png_infop) -> f32 {
        png_get_x_offset_microns(p, info) as f32 * 0.00003937
    }

    pub unsafe extern "C" fn png_get_y_offset_inches(p: png_structp, info: png_infop) -> f32 {
        png_get_y_offset_microns(p, info) as f32 * 0.00003937
    }

    pub unsafe extern "C" fn png_get_x_offset_inches_fixed(p: png_structp, info: png_infop) -> png_fixed_point {
        (png_get_x_offset_microns(p, info) as f64 * 500.0 / 127.0).round() as i32
    }

    pub unsafe extern "C" fn png_get_y_offset_inches_fixed(p: png_structp, info: png_infop) -> png_fixed_point {
        (png_get_y_offset_microns(p, info) as f64 * 500.0 / 127.0).round() as i32
    }

    pub unsafe extern "C" fn png_get_tIME(p: png_structp, info: png_infop, t: *mut *mut png_time) -> png_uint_32 {
        if !ok(p, info) || t.is_null() || (*info).valid & INFO_tIME == 0 {
            return 0;
        }
        *t = &mut (*info).time;
        INFO_tIME
    }

    pub unsafe extern "C" fn png_set_tIME(p: png_structp, info: png_infop, t: *const png_time) {
        if !ok(p, info) || t.is_null() {
            return;
        }
        let v = *t;
        if v.month == 0 || v.month > 12 || v.day == 0 || v.day > 31 || v.hour > 23 || v.minute > 59 || v.second > 60 {
            warn(p, "Ignoring invalid time value");
            return;
        }
        (*info).time = v;
        (*info).valid |= INFO_tIME;
    }

    pub unsafe extern "C" fn png_get_text(p: png_structp, info: png_infop, text: *mut *mut png_text, num: *mut c_int) -> c_int {
        if !ok(p, info) || (*info).text.is_empty() {
            if !text.is_null() { *text = core::ptr::null_mut(); }
            if !num.is_null() { *num = 0; }
            return 0;
        }
        if !text.is_null() {
            *text = (*info).text_c.as_mut_ptr();
        }
        if !num.is_null() {
            *num = (*info).text_c.len() as c_int;
        }
        (*info).text_c.len() as c_int
    }

    pub unsafe extern "C" fn png_set_text(p: png_structp, info: png_infop, text: *const png_text, num: c_int) {
        if !ok(p, info) || text.is_null() {
            return;
        }
        for k in 0..num.max(0) as usize {
            let t = &*text.add(k);
            if t.key.is_null() {
                continue;
            }
            let key = core::slice::from_raw_parts(t.key as *const u8, cstr_len(t.key));
            let body: &[u8] = if t.text.is_null() {
                b""
            } else {
                core::slice::from_raw_parts(t.text as *const u8, cstr_len(t.text))
            };
            let s = |c: *mut c_char| if c.is_null() { None } else { Some(core::slice::from_raw_parts(c as *const u8, cstr_len(c))) };
            let (lang, lk) = if t.compression >= 1 { (s(t.lang).or(Some(b"")), s(t.lang_key).or(Some(b""))) } else { (None, None) };
            let comp = match t.compression { -3 | -1 => -1, -2 | 0 => 0, c => c };
            (*info).add_text(comp, key, body, lang, lk);
        }
    }

    pub unsafe extern "C" fn png_get_eXIf(p: png_structp, info: png_infop, exif: *mut *mut u8) -> png_uint_32 {
        let _ = (p, info, exif);
        // libpng: "png_get_eXIf does not work; use png_get_eXIf_1".
        if !p.is_null() {
            warn(p, "png_get_eXIf does not work; use png_get_eXIf_1");
        }
        0
    }

    pub unsafe extern "C" fn png_get_eXIf_1(p: png_structp, info: png_infop, num: *mut png_uint_32, exif: *mut *mut u8) -> png_uint_32 {
        if !ok(p, info) || (*info).valid & INFO_eXIf == 0 || exif.is_null() {
            return 0;
        }
        if !num.is_null() {
            *num = (*info).exif.len() as u32;
        }
        *exif = (*info).exif.as_mut_ptr();
        INFO_eXIf
    }

    pub unsafe extern "C" fn png_set_eXIf(p: png_structp, info: png_infop, exif: *mut u8) {
        let _ = (info, exif);
        if !p.is_null() {
            warn(p, "png_set_eXIf does not work; use png_set_eXIf_1");
        }
    }

    pub unsafe extern "C" fn png_set_eXIf_1(p: png_structp, info: png_infop, num: png_uint_32, exif: *mut u8) {
        if !ok(p, info) || exif.is_null() {
            return;
        }
        (*info).exif = core::slice::from_raw_parts(exif, num as usize).to_vec();
        (*info).valid |= INFO_eXIf;
        (*info).free_me |= FREE_EXIF;
    }

    pub unsafe extern "C" fn png_get_unknown_chunks(p: png_structp, info: png_infop, entries: *mut *mut png_unknown_chunk) -> c_int {
        if !ok(p, info) || entries.is_null() {
            return 0;
        }
        *entries = if (*info).unknown_c.is_empty() { core::ptr::null_mut() } else { (*info).unknown_c.as_mut_ptr() };
        (*info).unknown_c.len() as c_int
    }

    pub unsafe extern "C" fn png_set_unknown_chunks(p: png_structp, info: png_infop, unknowns: *const png_unknown_chunk, num: c_int) {
        if !ok(p, info) || unknowns.is_null() || num <= 0 {
            return;
        }
        for k in 0..num as usize {
            let u = &*unknowns.add(k);
            let data: &[u8] = if u.data.is_null() || u.size == 0 { &[] } else { core::slice::from_raw_parts(u.data, u.size) };
            let name = u32::from_be_bytes([u.name[0], u.name[1], u.name[2], u.name[3]]);
            let loc = match super::read::location_of(u.location as u32) {
                Some(l) => l,
                None => {
                    fail(p, "invalid location in png_set_unknown_chunks");
                    raise(p)
                }
            };
            (*info).add_unknown(name, data, loc);
        }
    }

    pub unsafe extern "C" fn png_set_unknown_chunk_location(p: png_structp, info: png_infop, chunk: c_int, location: c_int) {
        if !ok(p, info) || chunk < 0 || chunk as usize >= (*info).unknown.len() {
            return;
        }
        let loc = (location as u32 & (HAVE_IHDR | HAVE_PLTE | AFTER_IDAT)) as u8;
        (*info).unknown[chunk as usize].0.location = loc;
        (*info).unknown_c = (*info).unknown.iter().map(|u| u.0).collect();
    }

    pub unsafe extern "C" fn png_set_invalid(p: png_structp, info: png_infop, mask: c_int) {
        if ok(p, info) {
            (*info).valid &= !(mask as u32);
        }
    }

    pub unsafe extern "C" fn png_get_palette_max(p: png_structp, info: png_infop) -> c_int {
        if !ok(p, info) { -1 } else { (*p).num_palette_max }
    }
}

/// Allocates the row pointers and rows `png_read_png` reads into, with the
/// caller's allocator, as libpng does.
pub unsafe fn alloc_rows(p: *mut Png, info: *mut Info) -> R<()> {
    let h = (*info).height as usize;
    let rb = (*info).rowbytes;
    let rows = alloc(p, h * core::mem::size_of::<*mut u8>()) as *mut *mut u8;
    if rows.is_null() {
        return Err(fail(p, "Out of memory"));
    }
    for y in 0..h {
        *rows.add(y) = core::ptr::null_mut();
    }
    (*info).row_pointers = rows;
    (*info).free_me |= FREE_ROWS;
    for y in 0..h {
        let r = alloc(p, rb.max(1)) as *mut u8;
        if r.is_null() {
            return Err(fail(p, "Out of memory"));
        }
        *rows.add(y) = r;
    }
    Ok(())
}
