//! libpng's row transformations (`pngrtran.c`, `pngtrans.c` of libpng
//! 1.6.59), the ones that need no gamma: in libpng's order, with libpng's
//! arithmetic, so that a row comes out byte for byte as libpng gives it.
//! Each works in place on a row buffer big enough for the widest result,
//! from the end of the row backwards where the row grows, as libpng's do.
use super::*;

// `Png::transformations` bits (libpng's `PNG_*` transformation flags).
pub const T_BGR: u32 = 0x0001;
pub const T_INTERLACE: u32 = 0x0002;
pub const T_PACK: u32 = 0x0004;
pub const T_SHIFT: u32 = 0x0008;
pub const T_SWAP_BYTES: u32 = 0x0010;
pub const T_INVERT_MONO: u32 = 0x0020;
pub const T_EXPAND: u32 = 0x1000;
pub const T_16_TO_8: u32 = 0x0400;
pub const T_STRIP_ALPHA: u32 = 0x0800;
pub const T_PACKSWAP: u32 = 0x10000;
pub const T_SWAP_ALPHA: u32 = 0x20000;
pub const T_INVERT_ALPHA: u32 = 0x80000;
pub const T_FILLER: u32 = 0x8000;
pub const T_USER_TRANSFORM: u32 = 0x100000;
pub const T_ADD_ALPHA: u32 = 0x1000000;
pub const T_EXPAND_tRNS: u32 = 0x2000000;
pub const T_SCALE_16_TO_8: u32 = 0x4000000;
pub const T_GRAY_TO_RGB: u32 = 0x4000;
pub const T_EXPAND_16: u32 = 0x0200;

/// What the transformations read from the decoder's state.
pub struct Params<'a> {
    pub transformations: u32,
    pub filler_after: bool,
    pub filler: u16,
    pub shift: png_color_8,
    pub palette: &'a [png_color; 256],
    pub num_palette: u16,
    pub trans_alpha: &'a [u8; 256],
    pub num_trans: u16,
    pub trans_color: png_color_16,
    /// Whether to track the largest palette index (`num_palette_max >= 0`).
    pub check_index: bool,
}

fn set_depth(ri: &mut png_row_info, bd: u8, ch: u8) {
    ri.bit_depth = bd;
    ri.channels = ch;
    ri.pixel_depth = bd * ch;
    ri.rowbytes = rowbytes(ri.pixel_depth as u32, ri.width);
}

/// Pixel `i` of a row of `d`-bit pixels packed from the most significant
/// bit (`d` < 8).
#[inline]
fn packed(row: &[u8], i: usize, d: usize) -> u8 {
    let bit = i * d;
    (row[bit >> 3] >> (8 - d - (bit & 7))) & ((1u16 << d) - 1) as u8
}

/// `png_do_read_transformations`, except the user transform, which the
/// caller runs. Returns the largest palette index seen, when checked.
pub fn transform(pr: &Params, ri: &mut png_row_info, row: &mut [u8]) -> Option<u8> {
    let t = pr.transformations;
    let mut max_index = None;
    if t & T_EXPAND != 0 {
        if ri.color_type == CT_PALETTE {
            expand_palette(ri, row, pr.palette, pr.trans_alpha, pr.num_trans);
        } else if pr.num_trans != 0 && t & T_EXPAND_tRNS != 0 {
            expand(ri, row, Some(&pr.trans_color));
        } else {
            expand(ri, row, None);
        }
    }
    if t & T_STRIP_ALPHA != 0 && (ri.color_type == CT_RGBA || ri.color_type == CT_GA) {
        strip_channel(ri, row);
    }
    if t & T_GRAY_TO_RGB != 0 {
        gray_to_rgb(ri, row);
    }
    if t & T_SCALE_16_TO_8 != 0 {
        scale_16_to_8(ri, row);
    }
    if t & T_16_TO_8 != 0 {
        chop(ri, row);
    }
    if t & T_EXPAND_16 != 0 {
        expand_16(ri, row);
    }
    if t & T_INVERT_MONO != 0 {
        invert_mono(ri, row);
    }
    if t & T_INVERT_ALPHA != 0 {
        invert_alpha(ri, row);
    }
    if t & T_SHIFT != 0 {
        unshift(ri, row, &pr.shift);
    }
    if t & T_PACK != 0 {
        unpack(ri, row);
    }
    if ri.color_type == CT_PALETTE && pr.check_index {
        max_index = palette_max(ri, row, pr.num_palette);
    }
    if t & T_BGR != 0 {
        bgr(ri, row);
    }
    if t & T_PACKSWAP != 0 {
        packswap(ri, row);
    }
    if t & T_FILLER != 0 {
        filler(ri, row, pr.filler, pr.filler_after);
    }
    if t & T_SWAP_ALPHA != 0 {
        swap_alpha(ri, row);
    }
    if t & T_SWAP_BYTES != 0 {
        swap(ri, row);
    }
    max_index
}

/// `png_do_expand_palette`.
fn expand_palette(ri: &mut png_row_info, row: &mut [u8], pal: &[png_color; 256], ta: &[u8; 256], nt: u16) {
    if ri.color_type != CT_PALETTE {
        return;
    }
    let w = ri.width as usize;
    if ri.bit_depth < 8 {
        let d = ri.bit_depth as usize;
        for i in (0..w).rev() {
            row[i] = packed(row, i, d);
        }
        set_depth(ri, 8, 1);
    }
    if ri.bit_depth == 8 {
        if nt > 0 {
            for i in (0..w).rev() {
                let x = row[i] as usize;
                let c = pal[x];
                row[4 * i + 3] = if x >= nt as usize { 0xff } else { ta[x] };
                row[4 * i + 2] = c.blue;
                row[4 * i + 1] = c.green;
                row[4 * i] = c.red;
            }
            ri.color_type = CT_RGBA;
            set_depth(ri, 8, 4);
        } else {
            for i in (0..w).rev() {
                let c = pal[row[i] as usize];
                row[3 * i + 2] = c.blue;
                row[3 * i + 1] = c.green;
                row[3 * i] = c.red;
            }
            ri.color_type = CT_RGB;
            set_depth(ri, 8, 3);
        }
    }
}

/// `png_do_expand`.
fn expand(ri: &mut png_row_info, row: &mut [u8], trans: Option<&png_color_16>) {
    let w = ri.width as usize;
    if ri.color_type == CT_GRAY {
        let mut gray = trans.map(|t| t.gray as u32).unwrap_or(0);
        if ri.bit_depth < 8 {
            let d = ri.bit_depth as usize;
            let (m, s) = match d {
                1 => (1u32, 0xffu32),
                2 => (3, 0x55),
                _ => (15, 0x11),
            };
            gray = (gray & m) * s;
            for i in (0..w).rev() {
                row[i] = (packed(row, i, d) as u32 * s) as u8;
            }
            set_depth(ri, 8, 1);
        }
        if trans.is_some() {
            if ri.bit_depth == 8 {
                let g = (gray & 0xff) as u8;
                for i in (0..w).rev() {
                    let v = row[i];
                    row[2 * i + 1] = if v == g { 0 } else { 0xff };
                    row[2 * i] = v;
                }
            } else if ri.bit_depth == 16 {
                let (gh, gl) = (((gray >> 8) & 0xff) as u8, (gray & 0xff) as u8);
                for i in (0..w).rev() {
                    let (h, l) = (row[2 * i], row[2 * i + 1]);
                    let a = if h == gh && l == gl { 0 } else { 0xff };
                    row[4 * i + 3] = a;
                    row[4 * i + 2] = a;
                    row[4 * i + 1] = l;
                    row[4 * i] = h;
                }
            }
            ri.color_type = CT_GA;
            let bd = ri.bit_depth;
            set_depth(ri, bd, 2);
        }
    } else if ri.color_type == CT_RGB {
        if let Some(t) = trans {
            if ri.bit_depth == 8 {
                let (r, g, b) = ((t.red & 0xff) as u8, (t.green & 0xff) as u8, (t.blue & 0xff) as u8);
                for i in (0..w).rev() {
                    let (pr, pg, pb) = (row[3 * i], row[3 * i + 1], row[3 * i + 2]);
                    row[4 * i + 3] = if pr == r && pg == g && pb == b { 0 } else { 0xff };
                    row[4 * i + 2] = pb;
                    row[4 * i + 1] = pg;
                    row[4 * i] = pr;
                }
            } else if ri.bit_depth == 16 {
                let k = [t.red.to_be_bytes(), t.green.to_be_bytes(), t.blue.to_be_bytes()];
                let k: [u8; 6] = [k[0][0], k[0][1], k[1][0], k[1][1], k[2][0], k[2][1]];
                for i in (0..w).rev() {
                    let mut px = [0u8; 6];
                    px.copy_from_slice(&row[6 * i..6 * i + 6]);
                    let a = if px == k { 0 } else { 0xff };
                    row[8 * i + 7] = a;
                    row[8 * i + 6] = a;
                    row[8 * i..8 * i + 6].copy_from_slice(&px);
                }
            }
            ri.color_type = CT_RGBA;
            let bd = ri.bit_depth;
            set_depth(ri, bd, 4);
        }
    }
}

/// `png_do_strip_channel` with `at_start` false: drops the last channel.
fn strip_channel(ri: &mut png_row_info, row: &mut [u8]) {
    let w = ri.width as usize;
    let b = (ri.bit_depth / 8) as usize;
    if b == 0 || (ri.channels != 2 && ri.channels != 4) {
        return;
    }
    let ch = ri.channels as usize;
    let keep = (ch - 1) * b;
    for i in 0..w {
        row.copy_within(i * ch * b..i * ch * b + keep, i * keep);
    }
    ri.color_type = if ri.color_type == CT_GA {
        CT_GRAY
    } else if ri.color_type == CT_RGBA {
        CT_RGB
    } else {
        ri.color_type
    };
    let bd = ri.bit_depth;
    set_depth(ri, bd, (ch - 1) as u8);
}

/// `png_do_gray_to_rgb`.
fn gray_to_rgb(ri: &mut png_row_info, row: &mut [u8]) {
    if ri.bit_depth < 8 || ri.color_type & COLOR_MASK_COLOR != 0 {
        return;
    }
    let w = ri.width as usize;
    let b = (ri.bit_depth / 8) as usize;
    let alpha = ri.color_type == CT_GA;
    let (si, di) = if alpha { (2 * b, 4 * b) } else { (b, 3 * b) };
    for i in (0..w).rev() {
        let s = i * si;
        let d = i * di;
        let mut g = [0u8; 2];
        let mut a = [0u8; 2];
        g[..b].copy_from_slice(&row[s..s + b]);
        if alpha {
            a[..b].copy_from_slice(&row[s + b..s + 2 * b]);
            row[d + 3 * b..d + 4 * b].copy_from_slice(&a[..b]);
        }
        for k in 0..3 {
            row[d + k * b..d + (k + 1) * b].copy_from_slice(&g[..b]);
        }
    }
    ri.color_type |= COLOR_MASK_COLOR;
    let (bd, ch) = (ri.bit_depth, ri.channels + 2);
    set_depth(ri, bd, ch);
}

/// `png_do_scale_16_to_8`.
fn scale_16_to_8(ri: &mut png_row_info, row: &mut [u8]) {
    if ri.bit_depth != 16 {
        return;
    }
    let n = ri.rowbytes / 2;
    for i in 0..n {
        let mut tmp = row[2 * i] as i32;
        tmp += ((row[2 * i + 1] as i32 - tmp + 128) * 65535) >> 24;
        row[i] = tmp as u8;
    }
    let ch = ri.channels;
    set_depth(ri, 8, ch);
}

/// `png_do_chop`.
fn chop(ri: &mut png_row_info, row: &mut [u8]) {
    if ri.bit_depth != 16 {
        return;
    }
    let n = ri.rowbytes / 2;
    for i in 0..n {
        row[i] = row[2 * i];
    }
    let ch = ri.channels;
    set_depth(ri, 8, ch);
}

/// `png_do_expand_16`.
fn expand_16(ri: &mut png_row_info, row: &mut [u8]) {
    if ri.bit_depth != 8 || ri.color_type == CT_PALETTE {
        return;
    }
    let n = ri.rowbytes;
    for i in (0..n).rev() {
        let v = row[i];
        row[2 * i] = v;
        row[2 * i + 1] = v;
    }
    let ch = ri.channels;
    set_depth(ri, 16, ch);
}

/// `png_do_invert`.
fn invert_mono(ri: &mut png_row_info, row: &mut [u8]) {
    let n = ri.rowbytes;
    if ri.color_type == CT_GRAY {
        for b in &mut row[..n] {
            *b = !*b;
        }
    } else if ri.color_type == CT_GA && ri.bit_depth == 8 {
        for i in (0..n).step_by(2) {
            row[i] = !row[i];
        }
    } else if ri.color_type == CT_GA && ri.bit_depth == 16 {
        for i in (0..n).step_by(4) {
            row[i] = !row[i];
            row[i + 1] = !row[i + 1];
        }
    }
}

/// `png_do_read_invert_alpha`.
fn invert_alpha(ri: &mut png_row_info, row: &mut [u8]) {
    let w = ri.width as usize;
    let b = (ri.bit_depth / 8) as usize;
    let ch = match ri.color_type {
        CT_RGBA => 4,
        CT_GA => 2,
        _ => return,
    };
    if b == 0 {
        return;
    }
    for i in 0..w {
        let a = (i * ch + ch - 1) * b;
        for k in 0..b {
            row[a + k] = !row[a + k];
        }
    }
}

/// `png_do_unshift`.
fn unshift(ri: &mut png_row_info, row: &mut [u8], sig: &png_color_8) {
    if ri.color_type == CT_PALETTE {
        return;
    }
    let bd = ri.bit_depth as i32;
    let mut shift = [0i32; 4];
    let mut n = 0;
    if ri.color_type & COLOR_MASK_COLOR != 0 {
        shift[0] = bd - sig.red as i32;
        shift[1] = bd - sig.green as i32;
        shift[2] = bd - sig.blue as i32;
        n = 3;
    } else {
        shift[0] = bd - sig.gray as i32;
        n += 1;
    }
    if ri.color_type & COLOR_MASK_ALPHA != 0 {
        shift[n] = bd - sig.alpha as i32;
        n += 1;
    }
    let mut have = false;
    for s in shift.iter_mut().take(n) {
        if *s <= 0 || *s >= bd {
            *s = 0;
        } else {
            have = true;
        }
    }
    if !have {
        return;
    }
    let len = ri.rowbytes;
    match bd {
        2 => {
            for b in &mut row[..len] {
                *b = (*b >> 1) & 0x55;
            }
        }
        4 => {
            let gs = shift[0];
            let mut mask = 0xf >> gs;
            mask |= mask << 4;
            for b in &mut row[..len] {
                *b = ((*b as i32 >> gs) & mask) as u8;
            }
        }
        8 => {
            let mut c = 0;
            for b in &mut row[..len] {
                *b >>= shift[c];
                c += 1;
                if c >= n {
                    c = 0;
                }
            }
        }
        16 => {
            let mut c = 0;
            for i in (0..len).step_by(2) {
                let v = ((row[i] as i32) << 8 | row[i + 1] as i32) >> shift[c];
                c += 1;
                if c >= n {
                    c = 0;
                }
                row[i] = (v >> 8) as u8;
                row[i + 1] = v as u8;
            }
        }
        _ => {}
    }
}

/// `png_do_unpack`.
fn unpack(ri: &mut png_row_info, row: &mut [u8]) {
    if ri.bit_depth >= 8 {
        return;
    }
    let w = ri.width as usize;
    let d = ri.bit_depth as usize;
    for i in (0..w).rev() {
        row[i] = packed(row, i, d);
    }
    let ch = ri.channels;
    set_depth(ri, 8, ch);
}

/// `png_do_check_palette_indexes`: the largest index in the row.
fn palette_max(ri: &png_row_info, row: &[u8], num_palette: u16) -> Option<u8> {
    let d = ri.bit_depth as usize;
    if num_palette == 0 || num_palette as u32 >= (1u32 << d) {
        return None;
    }
    let w = ri.width as usize;
    let mut m = 0u8;
    for i in 0..w {
        let v = if d == 8 { row[i] } else { packed(row, i, d) };
        if v > m {
            m = v;
        }
    }
    // libpng records 1 for any set bit of a 1-bit row.
    Some(m)
}

/// `png_do_bgr`.
fn bgr(ri: &mut png_row_info, row: &mut [u8]) {
    if ri.color_type & COLOR_MASK_COLOR == 0 {
        return;
    }
    let w = ri.width as usize;
    let ch = match ri.color_type {
        CT_RGB => 3,
        CT_RGBA => 4,
        _ => return,
    };
    match ri.bit_depth {
        8 => {
            for i in 0..w {
                row.swap(i * ch, i * ch + 2);
            }
        }
        16 => {
            for i in 0..w {
                let p = i * ch * 2;
                row.swap(p, p + 4);
                row.swap(p + 1, p + 5);
            }
        }
        _ => {}
    }
}

/// `png_do_packswap`: reverses the order of the pixels in each byte.
fn packswap(ri: &mut png_row_info, row: &mut [u8]) {
    let d = ri.bit_depth as u32;
    if !(d == 1 || d == 2 || d == 4) {
        return;
    }
    let n = ri.rowbytes;
    for b in &mut row[..n] {
        let v = *b;
        let mut r = 0u8;
        let k = 8 / d;
        let m = ((1u16 << d) - 1) as u8;
        for j in 0..k {
            let px = (v >> (j * d)) & m;
            r |= px << ((k - 1 - j) * d);
        }
        *b = r;
    }
}

/// `png_do_read_filler`.
fn filler(ri: &mut png_row_info, row: &mut [u8], filler: u16, after: bool) {
    let w = ri.width as usize;
    let b = match ri.bit_depth {
        8 => 1usize,
        16 => 2,
        _ => return,
    };
    let ch = match ri.color_type {
        CT_GRAY => 1usize,
        CT_RGB => 3,
        _ => return,
    };
    let f = filler.to_be_bytes();
    let fb: &[u8] = if b == 1 { &f[1..2] } else { &f[..] };
    let (s, dsz) = (ch * b, (ch + 1) * b);
    for i in (0..w).rev() {
        let mut px = [0u8; 6];
        px[..s].copy_from_slice(&row[i * s..i * s + s]);
        let d = i * dsz;
        if after {
            row[d..d + s].copy_from_slice(&px[..s]);
            row[d + s..d + dsz].copy_from_slice(fb);
        } else {
            row[d..d + b].copy_from_slice(fb);
            row[d + b..d + dsz].copy_from_slice(&px[..s]);
        }
    }
    let bd = ri.bit_depth;
    set_depth(ri, bd, (ch + 1) as u8);
}

/// `png_do_read_swap_alpha`.
fn swap_alpha(ri: &mut png_row_info, row: &mut [u8]) {
    let w = ri.width as usize;
    let ch = match ri.color_type {
        CT_RGBA => 4usize,
        CT_GA => 2,
        _ => return,
    };
    let b = match ri.bit_depth {
        8 => 1usize,
        16 => 2,
        _ => return,
    };
    let px = ch * b;
    for i in 0..w {
        row[i * px..i * px + px].rotate_right(b);
    }
}

/// `png_do_swap`.
fn swap(ri: &mut png_row_info, row: &mut [u8]) {
    if ri.bit_depth != 16 {
        return;
    }
    let n = ri.width as usize * ri.channels as usize;
    for i in 0..n {
        row.swap(2 * i, 2 * i + 1);
    }
}

/// `png_read_transform_info`'s arithmetic: the format a row has after the
/// transformations, as (color type, bit depth, channels).
pub fn out_format(t: u32, ct: u8, bd: u8, num_trans: u16, ut_depth: u8, ut_channels: u8) -> (u8, u8, u8) {
    let (mut ct, mut bd) = (ct, bd);
    if t & T_EXPAND != 0 {
        if ct == CT_PALETTE {
            ct = if num_trans > 0 { CT_RGBA } else { CT_RGB };
            bd = 8;
        } else {
            if num_trans != 0 && t & T_EXPAND_tRNS != 0 {
                ct |= COLOR_MASK_ALPHA;
            }
            if bd < 8 {
                bd = 8;
            }
        }
    }
    if bd == 16 && t & (T_SCALE_16_TO_8 | T_16_TO_8) != 0 {
        bd = 8;
    }
    if t & T_GRAY_TO_RGB != 0 {
        ct |= COLOR_MASK_COLOR;
    }
    if t & T_EXPAND_16 != 0 && bd == 8 && ct != CT_PALETTE {
        bd = 16;
    }
    if t & T_PACK != 0 && bd < 8 {
        bd = 8;
    }
    let mut ch = if ct == CT_PALETTE {
        1
    } else if ct & COLOR_MASK_COLOR != 0 {
        3
    } else {
        1
    };
    if t & T_STRIP_ALPHA != 0 {
        ct &= !COLOR_MASK_ALPHA;
    }
    if ct & COLOR_MASK_ALPHA != 0 {
        ch += 1;
    }
    if t & T_FILLER != 0 && (ct == CT_RGB || ct == CT_GRAY) {
        ch += 1;
        if t & T_ADD_ALPHA != 0 {
            ct |= COLOR_MASK_ALPHA;
        }
    }
    if t & T_USER_TRANSFORM != 0 {
        if ut_depth != 0 {
            bd = ut_depth;
        }
        if ut_channels != 0 {
            ch = ut_channels;
        }
    }
    (ct, bd, ch)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn packswap_reverses_pixels() {
        let mut ri = png_row_info { width: 8, rowbytes: 1, color_type: 0, bit_depth: 1, channels: 1, pixel_depth: 1 };
        let mut row = [0b1000_0010u8];
        packswap(&mut ri, &mut row);
        assert_eq!(row[0], 0b0100_0001);
        let mut ri = png_row_info { width: 2, rowbytes: 1, color_type: 0, bit_depth: 4, channels: 1, pixel_depth: 4 };
        let mut row = [0x12u8];
        packswap(&mut ri, &mut row);
        assert_eq!(row[0], 0x21);
    }

    #[test]
    fn scale_matches_formula() {
        for v in [0u32, 1, 127, 128, 129, 255, 256, 32767, 32768, 65280, 65535] {
            let mut ri = png_row_info { width: 1, rowbytes: 2, color_type: 0, bit_depth: 16, channels: 1, pixel_depth: 16 };
            let mut row = [(v >> 8) as u8, v as u8];
            scale_16_to_8(&mut ri, &mut row);
            assert_eq!(row[0] as u32, (v * 255 + 32895) >> 16);
        }
    }
}
