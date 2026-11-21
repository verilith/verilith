//! Building the sanitized font: read the input's tables, rebuild or copy
//! each one, and lay the result out as a new file.
//!
//! This module is verified for memory safety and absence of overflow only.
//! It is not trusted to produce a well-formed font: `sanitize` runs the
//! verified `check_font` on what it builds and returns it only if that
//! says yes.
use crate::cmap::*;
use crate::glyf::*;
use crate::lay::*;
use crate::prims::*;
use crate::spec::*;
use crate::tables::*;
use vstd::prelude::*;

verus! {

/// Inputs and tables larger than this are refused (as OTS refuses them).
pub const MAX_LEN: usize = 0x4000_0000;

/// Most encoding records a `cmap` may have.
pub const MAX_CMAP_RECORDS: usize = 1024;

pub struct Table {
    pub tag: u32,
    pub data: Vec<u8>,
}

pub fn to_vec(s: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == s@,
{
    let mut v = Vec::new();
    v.extend_from_slice(s);
    v
}

pub fn append(v: &mut Vec<u8>, s: &[u8])
    ensures
        final(v)@ == old(v)@ + s@,
{
    v.extend_from_slice(s);
}

pub fn put16(v: &mut Vec<u8>, x: u16)
    ensures
        final(v)@.len() == old(v)@.len() + 2,
{
    v.push((x / 256) as u8);
    v.push((x % 256) as u8);
}

pub fn put32(v: &mut Vec<u8>, x: u32)
    ensures
        final(v)@.len() == old(v)@.len() + 4,
{
    put16(v, (x / 65536) as u16);
    put16(v, (x % 65536) as u16);
}

pub fn set16(v: &mut Vec<u8>, i: usize, x: u16)
    requires
        i + 2 <= old(v).len(),
    ensures
        final(v)@.len() == old(v)@.len(),
{
    v.set(i, (x / 256) as u8);
    v.set(i + 1, (x % 256) as u8);
}

pub fn set32(v: &mut Vec<u8>, i: usize, x: u32)
    requires
        i + 4 <= old(v).len(),
    ensures
        final(v)@.len() == old(v)@.len(),
{
    set16(v, i, (x / 65536) as u16);
    set16(v, i + 2, (x % 65536) as u16);
}

/// Pads `v` with zeros to a multiple of four.
pub fn pad(v: &mut Vec<u8>)
    ensures
        final(v)@.len() == pad4(old(v)@.len() as int),
        final(v)@.len() < old(v)@.len() + 4,
{
    while v.len() % 4 != 0
        invariant
            old(v)@.len() <= v@.len() <= pad4(old(v)@.len() as int),
        decreases pad4(old(v)@.len() as int) - v@.len(),
    {
        v.push(0);
    }
}

/// The index in `ts` of the table with tag `tag`.
pub fn lookup(ts: &Vec<Table>, tag: u32) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> i < ts@.len(),
{
    let mut i: usize = 0;
    while i < ts.len()
        invariant
            i <= ts@.len(),
        decreases ts@.len() - i,
    {
        if ts[i].tag == tag {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Reads the table directory at `base` of an sfnt file (0 for a plain
/// font, or the offset a TrueType Collection gives for one of its fonts)
/// and copies out the tables this sanitizer knows. Fails if there is no
/// directory there, a known table lies outside the file, or a known table
/// appears twice.
pub fn read_sfnt(input: &[u8], base: usize) -> (r: Option<Vec<Table>>) {
    if input.len() > MAX_LEN || base > input.len() || input.len() - base < 12 {
        return None;
    }
    let v = rd32(input, base);
    // 'true' is Apple's name for TrueType outlines.
    if v != TAG_TRUETYPE && v != TAG_OTTO && v != 0x7472_7565 {
        return None;
    }
    let n = rd16(input, base + 4) as usize;
    if 12 + 16 * n > input.len() - base {
        return None;
    }
    let mut ts: Vec<Table> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            base + 12 + 16 * n <= input.len(),
        decreases n - i,
    {
        let r = base + 12 + 16 * i;
        let tag = rd32(input, r);
        if crate::font::is_known_tag(tag) {
            let off = rd32(input, r + 8) as usize;
            let len = rd32(input, r + 12) as usize;
            if off > input.len() || len > input.len() - off {
                return None;
            }
            if lookup(&ts, tag).is_some() {
                return None;
            }
            ts.push(Table { tag, data: to_vec(slice(input, off, off + len)) });
        }
        i += 1;
    }
    Some(ts)
}

/// Reads font `index` of a TrueType Collection.
pub fn read_ttc(input: &[u8], index: u32) -> (r: Option<Vec<Table>>) {
    if input.len() < 12 || input.len() > MAX_LEN {
        return None;
    }
    let n = rd32(input, 8) as usize;
    let i = index as usize;
    if i >= n || 12 + 4 * n > input.len() {
        return None;
    }
    read_sfnt(input, rd32(input, 12 + 4 * i) as usize)
}

/// Most bytes the tables of a WOFF or WOFF2 file may decompress to.
pub const MAX_DECOMPRESSED: usize = 300 * 1024 * 1024;

/// Reads a WOFF 1.0 file: each known table is copied or, if it is stored
/// compressed, inflated with vzlib, and must come out at exactly the
/// length the directory says.
pub fn read_woff(input: &[u8]) -> (r: Option<Vec<Table>>) {
    if input.len() < 44 || input.len() > MAX_LEN {
        return None;
    }
    let n = rd16(input, 12) as usize;
    if 44 + 20 * n > input.len() {
        return None;
    }
    // The header must state the file's true length, so nothing can ride
    // along after the font.
    if rd32(input, 8) as usize != input.len() {
        return None;
    }
    let mut sfnt: usize = 12 + 16 * n;
    let mut last: usize = 0;
    let mut dec = verilith_zlib::wrap::Decompressor::new();
    let mut ts: Vec<Table> = Vec::new();
    let mut total: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            44 + 20 * n <= input.len(),
            total <= MAX_DECOMPRESSED,
            verilith_zlib::wrap::wf(&dec),
            n <= 65535,
            sfnt <= 12 + 16 * n + i * 0x1_0000_0004,
            last <= 0x2_0000_0000,
        decreases n - i,
    {
        let r = 44 + 20 * i;
        let tag = rd32(input, r);
        sfnt = sfnt + (rd32(input, r + 12) as usize + 3) / 4 * 4;
        let e = rd32(input, r + 4) as usize + rd32(input, r + 8) as usize;
        if e > last {
            last = e;
        }
        if crate::font::is_known_tag(tag) {
            let off = rd32(input, r + 4) as usize;
            let comp = rd32(input, r + 8) as usize;
            let orig = rd32(input, r + 12) as usize;
            if off > input.len() || comp > input.len() - off || comp > orig {
                return None;
            }
            if orig > MAX_DECOMPRESSED - total {
                return None;
            }
            total = total + orig;
            if lookup(&ts, tag).is_some() {
                return None;
            }
            let src = slice(input, off, off + comp);
            let data = if comp == orig {
                to_vec(src)
            } else {
                match dec.decompress_vec(verilith_zlib::wrap::Format::Zlib, src, orig) {
                    Ok((v, _)) => {
                        if v.len() != orig {
                            return None;
                        }
                        v
                    },
                    Err(_) => {
                        return None;
                    },
                }
            };
            ts.push(Table { tag, data });
        }
        i += 1;
    }
    // The header must also state the true size of the unpacked font.
    if rd32(input, 16) as usize != sfnt {
        return None;
    }
    // The metadata and private blocks, if any, follow the last table, and
    // the file ends there, with at most three bytes of padding between.
    let mut e = (last + 3) / 4 * 4;
    let meta = rd32(input, 24) as usize;
    if meta != 0 {
        if e != meta {
            return None;
        }
        e = (meta + rd32(input, 28) as usize + 3) / 4 * 4;
    }
    let private = rd32(input, 36) as usize;
    if private != 0 {
        if e != private {
            return None;
        }
        e = (private + rd32(input, 40) as usize + 3) / 4 * 4;
    }
    if e != (input.len() + 3) / 4 * 4 {
        return None;
    }
    Some(ts)
}

/// Reads the tables of a font file in any of the containers this crate
/// understands, told apart by the first four bytes. `index` picks the font
/// in a TrueType Collection and is ignored otherwise.
pub fn read_font(input: &[u8], index: u32) -> (r: Option<Vec<Table>>) {
    if input.len() < 4 {
        return None;
    }
    let magic = rd32(input, 0);
    if magic == 0x774F_4646 {
        read_woff(input)
    } else if magic == 0x774F_4632 {
        crate::woff2::read_woff2(input)
    } else if magic == 0x7474_6366 {
        read_ttc(input, index)
    } else {
        read_sfnt(input, 0)
    }
}

/// The first `n` bytes of `t`, if it has that many.
fn prefix(t: &[u8], n: usize) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(v) ==> v@.len() == n,
{
    if t.len() < n {
        None
    } else {
        Some(to_vec(slice(t, 0, n)))
    }
}

/// `glyf` and `loca` rebuilt: each glyph description cut at its true end
/// and padded to four bytes, empty glyphs left empty, and `loca` written
/// to match. Returns (glyf, loca, indexToLocFormat).
pub fn rebuild_glyf(glyf: &[u8], loca: &[u8], fmt: u16, ng: u16) -> (r: Option<(Vec<u8>, Vec<u8>, u16)>)
    ensures
        r matches Some((_, _, f)) ==> f <= 1,
{
    if fmt > 1 || glyf.len() > MAX_LEN {
        return None;
    }
    let n = ng as usize;
    let w: usize = if fmt == 0 {
        2
    } else {
        4
    };
    if loca.len() < (n + 1) * w {
        return None;
    }
    let mut out: Vec<u8> = Vec::new();
    let mut offs: Vec<u32> = Vec::new();
    offs.push(0);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == ng,
            fmt <= 1,
            w == if fmt == 0 {
                2int
            } else {
                4
            },
            (n + 1) * w <= loca.len(),
            glyf.len() <= MAX_LEN,
            out@.len() <= i * (MAX_LEN + 4),
            offs@.len() == i + 1,
        decreases n - i,
    {
        let a = loca_get(loca, fmt, i);
        let b = loca_get(loca, fmt, i + 1);
        if a > b || b > glyf.len() {
            return None;
        }
        if a < b {
            let g = slice(glyf, a, b);
            if g.len() < 10 {
                return None;
            }
            // A glyph with no contours draws nothing: leave it empty.
            if rd16(g, 0) != 0 {
                let e = match find_glyph_end(g, ng) {
                    Some(e) => e,
                    None => {
                        return None;
                    },
                };
                append(&mut out, slice(g, 0, e));
                pad(&mut out);
            }
        }
        assert(out@.len() <= (i + 1) * (MAX_LEN + 4)) by (nonlinear_arith)
            requires
                out@.len() <= i * (MAX_LEN + 4) + MAX_LEN + 4,
        ;
        if out.len() > u32::MAX as usize {
            return None;
        }
        offs.push(out.len() as u32);
        i += 1;
    }
    if out.len() == 0 {
        // No glyph has an outline: a single zero byte, as OTS writes.
        out.push(0);
    }
    let long = out.len() > 0x1FFFE;
    let mut l: Vec<u8> = Vec::new();
    let mut j: usize = 0;
    while j <= n
        invariant
            j <= n + 1,
            offs@.len() == n + 1,
        decreases n + 1 - j,
    {
        if long {
            put32(&mut l, offs[j]);
        } else {
            put16(&mut l, ((offs[j] / 2) % 65536) as u16);
        }
        j += 1;
    }
    Some((out, l, if long {
        1
    } else {
        0
    }))
}

/// A (source offset, new offset, length) triple for a kept cmap subtable.
struct Kept {
    src: usize,
    dst: usize,
    len: usize,
    fmt: u16,
}

impl Kept {
    fn fmt_ok(&self, pe: u32) -> bool {
        cmap_use(pe, self.fmt)
    }
}

/// The length of the well-formed subtable at `o`.
fn cmap_sub_len(t: &[u8], o: usize, ng: u16) -> (r: usize)
    requires
        o <= u32::MAX,
        wf_cmap_sub(t@, o as int, ng as int),
    ensures
        o + r <= t.len(),
{
    let f = rd16(t, o);
    if f == 0 {
        262
    } else if f == 4 {
        rd16(t, o + 2) as usize
    } else if f == 12 || f == 13 {
        16 + 12 * (rd32(t, o + 12) as usize)
    } else {
        rd32(t, o + 2) as usize
    }
}

/// `cmap` rebuilt from the encoding records whose subtables are well
/// formed, in their original order, skipping any that would break the
/// sort order. Subtables shared by several records stay shared.
pub fn rebuild_cmap(t0: &[u8], ng: u16) -> (r: Option<Vec<u8>>) {
    if t0.len() < 4 || t0.len() > MAX_LEN {
        return None;
    }
    let n0 = rd16(t0, 2) as usize;
    if n0 > MAX_CMAP_RECORDS || 4 + 8 * n0 > t0.len() {
        return None;
    }
    // Many real fonts end a format 4 subtable with a segment for 0xFFFF
    // whose idRangeOffset is 0xFFFF, which points outside the table. Like
    // OTS, repair that segment to map 0xFFFF to glyph 0 directly.
    let mut fixed = to_vec(t0);
    let mut j: usize = 0;
    while j < n0
        invariant
            j <= n0,
            4 + 8 * n0 <= t0.len(),
            fixed@.len() == t0.len(),
        decreases n0 - j,
    {
        let o = rd32(t0, 4 + 8 * j + 4) as usize;
        if o <= fixed.len() && fixed.len() - o >= 16 && rd16(fixed.as_slice(), o) == 4 {
            let sc = (rd16(fixed.as_slice(), o + 6) / 2) as usize;
            if sc >= 1 && 16 + 8 * sc <= fixed.len() - o {
                let k = sc - 1;
                let end = o + 14 + 2 * k;
                let start = o + 16 + 2 * sc + 2 * k;
                let delta = o + 16 + 4 * sc + 2 * k;
                let ro = o + 16 + 6 * sc + 2 * k;
                if rd16(fixed.as_slice(), end) == 0xFFFF && rd16(fixed.as_slice(), start) == 0xFFFF
                    && rd16(fixed.as_slice(), ro) == 0xFFFF {
                    set16(&mut fixed, delta, 1);
                    set16(&mut fixed, ro, 0);
                }
            }
        }
        j += 1;
    }
    rebuild_cmap_from(fixed.as_slice(), ng)
}

fn rebuild_cmap_from(t: &[u8], ng: u16) -> (r: Option<Vec<u8>>) {
    if t.len() < 4 || t.len() > MAX_LEN {
        return None;
    }
    let n = rd16(t, 2) as usize;
    if n > MAX_CMAP_RECORDS || 4 + 8 * n > t.len() {
        return None;
    }
    // Pass 1: decide which records to keep and where their subtables go.
    let mut kept: Vec<Kept> = Vec::new();
    let mut recs: Vec<(u32, usize)> = Vec::new();  // (platform/encoding, index in kept)
    let mut last: u32 = 0;
    let mut body: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n <= MAX_CMAP_RECORDS,
            4 + 8 * n <= t.len(),
            t.len() <= MAX_LEN,
            kept@.len() <= i,
            recs@.len() <= i,
            body <= i * MAX_LEN,
            forall|k: int| 0 <= k < kept@.len() ==> (#[trigger] kept@[k]).src + kept@[k].len <= t.len(),
            forall|k: int| 0 <= k < kept@.len() ==> (#[trigger] kept@[k]).dst <= i * MAX_LEN,
            forall|k: int| 0 <= k < recs@.len() ==> (#[trigger] recs@[k]).1 < kept@.len(),
        decreases n - i,
    {
        let r = 4 + 8 * i;
        let pe = rd32(t, r);
        let o = rd32(t, r + 4) as usize;
        assert(i * MAX_LEN + MAX_LEN == (i + 1) * MAX_LEN) by (nonlinear_arith);
        assert(i * MAX_LEN <= (i + 1) * MAX_LEN) by (nonlinear_arith);
        if recs.len() == 0 || pe > last {
            // Already kept?
            let mut found: Option<usize> = None;
            let mut k: usize = 0;
            while k < kept.len()
                invariant
                    k <= kept@.len(),
                    found matches Some(x) ==> x < kept@.len(),
                decreases kept@.len() - k,
            {
                if kept[k].src == o {
                    found = Some(k);
                }
                k += 1;
            }
            match found {
                Some(x) => {
                    if kept[x].fmt_ok(pe) {
                        recs.push((pe, x));
                        last = pe;
                    }
                },
                None => {
                    if check_cmap_sub(t, o, ng) && cmap_use(pe, rd16(t, o)) {
                        let len = cmap_sub_len(t, o, ng);
                        kept.push(Kept { src: o, dst: body, len, fmt: rd16(t, o) });
                        recs.push((pe, kept.len() - 1));
                        last = pe;
                        body = body + len;
                    }
                },
            }
        }
        i += 1;
    }
    if recs.len() == 0 {
        return None;
    }
    assert(n * MAX_LEN <= MAX_CMAP_RECORDS * MAX_LEN) by (nonlinear_arith)
        requires
            n <= MAX_CMAP_RECORDS,
    ;
    // Pass 2: write the header, the records and the subtables.
    let hdr = 4 + 8 * recs.len();
    let mut out: Vec<u8> = Vec::new();
    put16(&mut out, 0);
    put16(&mut out, recs.len() as u16);
    let mut j: usize = 0;
    while j < recs.len()
        invariant
            j <= recs@.len() <= MAX_CMAP_RECORDS,
            hdr == 4 + 8 * recs@.len(),
            forall|k: int| 0 <= k < recs@.len() ==> (#[trigger] recs@[k]).1 < kept@.len(),
            forall|k: int|
                0 <= k < kept@.len() ==> (#[trigger] kept@[k]).dst <= MAX_CMAP_RECORDS * MAX_LEN,
        decreases recs@.len() - j,
    {
        let (pe, x) = recs[j];
        let dst = hdr + kept[x].dst;
        if dst > u32::MAX as usize {
            return None;
        }
        put32(&mut out, pe);
        put32(&mut out, dst as u32);
        j += 1;
    }
    let mut k: usize = 0;
    while k < kept.len()
        invariant
            k <= kept@.len(),
            forall|k: int| 0 <= k < kept@.len() ==> (#[trigger] kept@[k]).src + kept@[k].len <= t.len(),
        decreases kept@.len() - k,
    {
        let src = kept[k].src;
        let len = kept[k].len;
        append(&mut out, slice(t, src, src + len));
        k += 1;
    }
    Some(out)
}

/// A copy of `t` if `ok` and it is not empty.
fn keep_if(ok: bool, t: &[u8]) -> (r: Option<Vec<u8>>) {
    if ok && t.len() > 0 {
        Some(to_vec(t))
    } else {
        None
    }
}

fn add(out: &mut Vec<Table>, tag: u32, data: Vec<u8>)
    ensures
        final(out)@.len() == old(out)@.len() + 1,
{
    // Insert in increasing order of tag.
    let mut i: usize = 0;
    while i < out.len() && out[i].tag < tag
        invariant
            i <= out@.len(),
        decreases out@.len() - i,
    {
        i += 1;
    }
    out.insert(i, Table { tag, data });
}

/// Most tables a sanitized font can have.
pub const MAX_TABLES: usize = 64;

/// Raises the 16-bit field at `i` to `v` if it is less. `None` if `v`
/// does not fit.
fn raise16(t: &mut Vec<u8>, i: usize, v: u32) -> (r: Option<()>)
    requires
        i + 2 <= old(t).len(),
    ensures
        final(t)@.len() == old(t)@.len(),
{
    if v > 0xFFFF {
        return None;
    }
    if (rd16(t.as_slice(), i) as u32) < v {
        set16(t, i, v as u16);
    }
    Some(())
}

/// The input table with tag `tag`.
/// A copy of a layout table with its link to variation data cleared,
/// because the variation tables are dropped: the item variation store of
/// a version 1.3 `GDEF`, the feature variations of a version 1.1 `GSUB`
/// or `GPOS`.
fn copy_layout(t: &[u8], gdef: bool) -> (v: Vec<u8>) {
    let mut v = to_vec(t);
    let at: usize = if gdef {
        14
    } else {
        10
    };
    let minor: u16 = if gdef {
        3
    } else {
        1
    };
    if t.len() >= at + 4 && rd16(t, 0) == 1 && rd16(t, 2) == minor {
        v.set(at, 0);
        v.set(at + 1, 0);
        v.set(at + 2, 0);
        v.set(at + 3, 0);
    }
    if !gdef {
        repair_default_langsys(&mut v);
    }
    v
}

/// OTS does not look at a script's default language system, and fonts
/// exist whose default language system is not well formed (a required
/// feature index of 0 in a table with no features). This repairs what can
/// be repaired in place: a non-null lookup order offset is cleared, and a
/// required feature that does not exist becomes "none". A default
/// language system that is still not well formed is removed.
fn repair_default_langsys(v: &mut Vec<u8>) {
    let len = v.len();
    if len < 10 || len > 0xFFFF_FFFF {
        return;
    }
    let sl = rd16(v.as_slice(), 4) as usize;
    let fl = rd16(v.as_slice(), 6) as usize;
    if sl == 0 || !room(v.as_slice(), sl, 2) {
        return;
    }
    let nf: usize = if fl != 0 && room(v.as_slice(), fl, 2) {
        rd16(v.as_slice(), fl) as usize
    } else {
        0
    };
    let n = rd16(v.as_slice(), sl) as usize;
    let mut i: usize = 0;
    while i < n
        invariant
            v@.len() == len,
            len <= 0xFFFF_FFFF,
            sl + 2 <= len,
            n <= 65535,
        decreases n - i,
    {
        let r = sl + 2 + 6 * i;
        i += 1;
        if !room(v.as_slice(), r, 6) {
            return;
        }
        let so = sl + rd16(v.as_slice(), r + 4) as usize;
        if !room(v.as_slice(), so, 2) {
            continue;
        }
        let d = rd16(v.as_slice(), so) as usize;
        if d == 0 {
            continue;
        }
        let l = so + d;
        if !room(v.as_slice(), l, 6) {
            set16(v, so, 0);
            continue;
        }
        if check_langsys(v.as_slice(), l, nf) {
            continue;
        }
        set16(v, l, 0);
        let req = rd16(v.as_slice(), l + 2);
        if req != 0xFFFF && req as usize >= nf {
            set16(v, l + 2, 0xFFFF);
        }
        if !check_langsys(v.as_slice(), l, nf) {
            set16(v, so, 0);
        }
    }
}

fn input<'a>(ts: &'a Vec<Table>, tag: u32) -> (r: Option<&'a [u8]>) {
    match lookup(ts, tag) {
        Some(i) => Some(ts[i].data.as_slice()),
        None => None,
    }
}

/// The sanitized tables, in increasing order of tag. `None` if the font
/// cannot be made well formed.
pub fn build_tables(ts: &Vec<Table>) -> (r: Option<Vec<Table>>)
    ensures
        r matches Some(v) ==> v@.len() <= MAX_TABLES,
{
    let mut head = prefix(input(ts, T_HEAD)?, 54)?;
    let glyf_in = input(ts, T_GLYF);
    // maxp: cut to the length of its version. In version 1.0 maxZones is
    // forced into 1..=2. A CFF font's version 1.0 table that is too short
    // is kept as version 0.5.
    let maxp_in = input(ts, T_MAXP)?;
    if maxp_in.len() < 6 {
        return None;
    }
    let mut maxp = if rd32(maxp_in, 0) == 0x0001_0000 && maxp_in.len() >= 32 {
        let mut m = to_vec(slice(maxp_in, 0, 32));
        let zones = rd16(m.as_slice(), 14);
        if zones < 1 {
            set16(&mut m, 14, 1);
        } else if zones > 2 {
            set16(&mut m, 14, 2);
        }
        m
    } else {
        let mut m = to_vec(slice(maxp_in, 0, 6));
        set32(&mut m, 0, 0x0000_5000);
        m
    };
    let ng = rd16(maxp.as_slice(), 4);
    if ng < 1 {
        return None;
    }
    let hhea = prefix(input(ts, T_HHEA)?, 36)?;
    let nhm = rd16(hhea.as_slice(), 34);
    if nhm > ng {
        return None;
    }
    let hmtx = prefix(input(ts, T_HMTX)?, 4 * (nhm as usize) + 2 * (ng as usize - nhm as usize))?;
    // OS/2: cut to the length its version calls for. A table too short
    // for its version is kept as version 0.
    let os2_in = input(ts, T_OS2)?;
    if os2_in.len() < 78 {
        return None;
    }
    let v = rd16(os2_in, 0);
    let want: usize = if v == 0 {
        78
    } else if v == 1 {
        86
    } else if v <= 4 {
        96
    } else {
        100
    };
    let os2 = if os2_in.len() >= want {
        to_vec(slice(os2_in, 0, want))
    } else {
        let mut o = to_vec(slice(os2_in, 0, 78));
        set16(&mut o, 0, 0);
        o
    };
    let cmap = rebuild_cmap(input(ts, T_CMAP)?, ng)?;
    // name: kept if well formed, otherwise replaced by an empty one.
    let name_in = input(ts, T_NAME)?;
    let name = if check_name(name_in) {
        to_vec(name_in)
    } else {
        let mut e: Vec<u8> = Vec::new();
        put16(&mut e, 0);
        put16(&mut e, 0);
        put16(&mut e, 6);
        e
    };
    // post: kept if well formed, otherwise cut down to a version 3.0
    // header (no glyph names).
    let post_in = input(ts, T_POST)?;
    let post = if check_post(post_in, ng) {
        to_vec(post_in)
    } else {
        let mut p = prefix(post_in, 32)?;
        set32(&mut p, 0, 0x0003_0000);
        p
    };
    set32(&mut head, 8, 0);
    let mut out: Vec<Table> = Vec::new();
    let (glyf, loca) = match glyf_in {
        Some(glyf_in) => {
            let (glyf, loca, fmt) = rebuild_glyf(
                glyf_in,
                input(ts, T_LOCA)?,
                rd16(head.as_slice(), 50),
                ng,
            )?;
            set16(&mut head, 50, fmt);
            // Make maxp tell the truth about the glyphs: raise each limit
            // to what the glyphs need. A font whose composite glyphs form
            // a cycle or nest too deep has no such limits and is refused.
            if maxp.len() != 32 || !check_loca(loca.as_slice(), fmt, ng, glyf.len()) {
                return None;
            }
            let l = crate::graph::glyf_limits(glyf.as_slice(), loca.as_slice(), fmt, ng)?;
            raise16(&mut maxp, 6, l.points)?;
            raise16(&mut maxp, 8, l.contours)?;
            raise16(&mut maxp, 10, l.cpoints)?;
            raise16(&mut maxp, 12, l.ccontours)?;
            raise16(&mut maxp, 26, l.ilen)?;
            raise16(&mut maxp, 28, l.elems)?;
            raise16(&mut maxp, 30, l.depth)?;
            (glyf, loca)
        },
        None => {
            // CFF outlines: the table is copied. The final check refuses
            // the font if it is not well formed.
            let cff = input(ts, T_CFF)?;
            add(&mut out, T_CFF, to_vec(cff));
            (Vec::new(), Vec::new())
        },
    };
    let truetype = glyf_in.is_some();
    add(&mut out, T_OS2, os2);
    add(&mut out, T_CMAP, cmap);
    if truetype {
    match input(ts, T_CVT) {
        Some(t) => match keep_if(check_cvt(t), t) {
            Some(d) => add(&mut out, T_CVT, d),
            None => {},
        },
        None => {},
    }
    match input(ts, T_FPGM) {
        Some(t) => match keep_if(true, t) {
            Some(d) => add(&mut out, T_FPGM, d),
            None => {},
        },
        None => {},
    }
    match input(ts, T_GASP) {
        Some(t) => match keep_if(check_gasp(t), t) {
            Some(d) => add(&mut out, T_GASP, d),
            None => {},
        },
        None => {},
    }
    add(&mut out, T_GLYF, glyf);
    }
    match input(ts, T_KERN) {
        Some(t) => {
            if check_kern(t, ng) {
                add(&mut out, T_KERN, to_vec(t));
            }
        },
        None => {},
    }
    // The layout tables are copied. The final check refuses the font if
    // one of them is malformed, as OTS does.
    match input(ts, T_GDEF) {
        Some(t) => add(&mut out, T_GDEF, copy_layout(t, true)),
        None => {},
    }
    match input(ts, T_GPOS) {
        Some(t) => add(&mut out, T_GPOS, copy_layout(t, false)),
        None => {},
    }
    match input(ts, T_GSUB) {
        Some(t) => add(&mut out, T_GSUB, copy_layout(t, false)),
        None => {},
    }
    // vhea and vmtx are kept together or not at all.
    match (input(ts, T_VHEA), input(ts, T_VMTX)) {
        (Some(vh), Some(vm)) => {
            if vh.len() >= 36 {
                let nvm = rd16(vh, 34);
                if nvm <= ng {
                    let want = 4 * (nvm as usize) + 2 * (ng as usize - nvm as usize);
                    if vm.len() >= want && check_vhea(slice(vh, 0, 36), ng) {
                        add(&mut out, T_VHEA, to_vec(slice(vh, 0, 36)));
                        add(&mut out, T_VMTX, to_vec(slice(vm, 0, want)));
                    }
                }
            }
        },
        _ => {},
    }
    add(&mut out, T_HEAD, head);
    add(&mut out, T_HHEA, hhea);
    add(&mut out, T_HMTX, hmtx);
    if truetype {
        add(&mut out, T_LOCA, loca);
    }
    add(&mut out, T_MAXP, maxp);
    add(&mut out, T_NAME, name);
    add(&mut out, T_POST, post);
    if truetype {
    match input(ts, T_PREP) {
        Some(t) => match keep_if(true, t) {
            Some(d) => add(&mut out, T_PREP, d),
            None => {},
        },
        None => {},
    }
    }
    Some(out)
}

/// Lays the tables out as an sfnt file: header, directory, then each table
/// padded to four bytes, with checksums and `head.checkSumAdjustment`
/// filled in. The tables must already be in increasing order of tag.
pub fn assemble(ts: &Vec<Table>, version: u32) -> (r: Option<Vec<u8>>)
    requires
        ts@.len() <= MAX_TABLES,
{
    let n = ts.len();
    if n == 0 {
        return None;
    }
    let (p, e) = crate::dir::pow2(n as u16);
    let mut out: Vec<u8> = Vec::new();
    put32(&mut out, version);
    put16(&mut out, n as u16);
    put16(&mut out, (16 * p) as u16);
    put16(&mut out, e as u16);
    put16(&mut out, (16 * (n as u32) - 16 * p) as u16);
    let mut i: usize = 0;
    while i < 16 * n
        invariant
            n <= MAX_TABLES,
            i <= 16 * n,
            out@.len() == 12 + i,
        decreases 16 * n - i,
    {
        out.push(0);
        i += 1;
    }
    let mut head_at: Option<usize> = None;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == ts@.len() <= MAX_TABLES,
            12 + 16 * n <= out@.len() <= 12 + 16 * n + i * (MAX_LEN + 4),
            out@.len() % 4 == 0,
            head_at matches Some(h) ==> h + 12 <= out@.len(),
        decreases n - i,
    {
        let t = &ts[i];
        if t.data.len() > MAX_LEN {
            return None;
        }
        let off = out.len();
        if off > 0xFFFF_0000 {
            return None;
        }
        append(&mut out, t.data.as_slice());
        pad(&mut out);
        assert(i * (MAX_LEN + 4) + MAX_LEN + 4 == (i + 1) * (MAX_LEN + 4)) by (nonlinear_arith);
        if t.tag == T_HEAD && t.data.len() >= 12 {
            head_at = Some(off);
        }
        let sum = sum_words(out.as_slice(), off / 4, out.len() / 4);
        let r = 12 + 16 * i;
        set32(&mut out, r, t.tag);
        set32(&mut out, r + 4, sum);
        set32(&mut out, r + 8, off as u32);
        set32(&mut out, r + 12, t.data.len() as u32);
        i += 1;
    }
    match head_at {
        Some(h) => {
            let total = sum_words(out.as_slice(), 0, out.len() / 4);
            let adj = if 0xB1B0_AFBAu32 >= total {
                0xB1B0_AFBAu32 - total
            } else {
                (0xB1B0_AFBAu64 + 0x1_0000_0000 - total as u64) as u32
            };
            set32(&mut out, h + 8, adj);
        },
        None => {
            return None;
        },
    }
    Some(out)
}

} // verus!
