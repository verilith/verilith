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
use crate::spec_same::*;
use crate::tables::*;
use vstd::prelude::*;

verus! {

/// Inputs and tables larger than this are refused (as OTS refuses them).
pub const MAX_LEN: usize = 0x4000_0000;

/// Most encoding records a `cmap` may have: all that its 16-bit count can
/// say, as in OTS.
pub const MAX_CMAP_RECORDS: usize = 0xFFFF;

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
        final(v)@.subrange(0, old(v)@.len() as int) == old(v)@,
        u16_at(final(v)@, old(v)@.len() as int) == x,
{
    v.push((x / 256) as u8);
    v.push((x % 256) as u8);
    assert(final(v)@.subrange(0, old(v)@.len() as int) =~= old(v)@);
}

pub fn put32(v: &mut Vec<u8>, x: u32)
    ensures
        final(v)@.len() == old(v)@.len() + 4,
        final(v)@.subrange(0, old(v)@.len() as int) == old(v)@,
        u32_at(final(v)@, old(v)@.len() as int) == x,
{
    let ghost v0 = v@;
    put16(v, (x / 65536) as u16);
    let ghost v1 = v@;
    put16(v, (x % 65536) as u16);
    assert(v@.subrange(0, v0.len() as int) =~= v0) by {
        assert(v@.subrange(0, v0.len() as int) =~= v@.subrange(0, v1.len() as int).subrange(0, v0.len() as int));
    }
    assert(v@[v0.len() as int] == v1[v0.len() as int]);
    assert(v@[v0.len() + 1int] == v1[v0.len() + 1int]);
}

pub fn set16(v: &mut Vec<u8>, i: usize, x: u16)
    requires
        i + 2 <= old(v).len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        final(v)@ == old(v)@.update(i as int, (x / 256) as u8).update(i + 1, (x % 256) as u8),
        u16_at(final(v)@, i as int) == x,
        forall|j: int| 0 <= j < old(v)@.len() && !(i <= j < i + 2) ==> final(v)@[j] == old(v)@[j],
{
    v.set(i, (x / 256) as u8);
    v.set(i + 1, (x % 256) as u8);
}

pub fn set32(v: &mut Vec<u8>, i: usize, x: u32)
    requires
        i + 4 <= old(v).len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        u32_at(final(v)@, i as int) == x,
        forall|j: int| 0 <= j < old(v)@.len() && !(i <= j < i + 4) ==> final(v)@[j] == old(v)@[j],
{
    set16(v, i, (x / 65536) as u16);
    set16(v, i + 2, (x % 65536) as u16);
}

/// Pads `v` with zeros to a multiple of four.
pub fn pad(v: &mut Vec<u8>)
    ensures
        final(v)@.len() == pad4(old(v)@.len() as int),
        old(v)@.len() <= final(v)@.len() < old(v)@.len() + 4,
        final(v)@.subrange(0, old(v)@.len() as int) == old(v)@,
        zeros(final(v)@, old(v)@.len() as int, final(v)@.len() as int),
{
    while v.len() % 4 != 0
        invariant
            old(v)@.len() <= v@.len() <= pad4(old(v)@.len() as int),
            v@.subrange(0, old(v)@.len() as int) == old(v)@,
            zeros(v@, old(v)@.len() as int, v@.len() as int),
        decreases pad4(old(v)@.len() as int) - v@.len(),
    {
        let ghost w = v@;
        v.push(0);
        assert(v@.subrange(0, old(v)@.len() as int) =~= w.subrange(0, old(v)@.len() as int));
    }
}

/// The (tag, bytes) pairs of a list of tables.
pub open spec fn tview(ts: Seq<Table>) -> Tables {
    ts.map_values(|t: Table| (t.tag, t.data@))
}

/// `r` is the table set `t` describes: both nothing, or the same pairs.
pub open spec fn read_as(r: Option<Vec<Table>>, t: Option<Tables>) -> bool {
    match t {
        Some(t) => r matches Some(v) && tview(v@) == t,
        None => r is None,
    }
}

/// The index in `ts` of the table with tag `tag`.
pub fn lookup(ts: &Vec<Table>, tag: u32) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> i < ts@.len() && i as int == find_in(tview(ts@), tag as int, 0),
        r is None ==> find_in(tview(ts@), tag as int, 0) == ts@.len(),
{
    let ghost tv = tview(ts@);
    let mut i: usize = 0;
    while i < ts.len()
        invariant
            i <= ts@.len(),
            tv == tview(ts@),
            find_in(tv, tag as int, 0) == find_in(tv, tag as int, i as int),
        decreases ts@.len() - i,
    {
        if ts[i].tag == tag {
            return Some(i);
        }
        i += 1;
    }
    None
}

proof fn lemma_recs_none(s: Seq<u8>, base: int, i: int, j: int)
    requires
        0 <= i <= j,
        sfnt_recs(s, base, i) is None,
    ensures
        sfnt_recs(s, base, j) is None,
    decreases j - i,
{
    if i < j {
        lemma_recs_none(s, base, i, j - 1);
    }
}

/// Reads the table directory at `base` of an sfnt file (0 for a plain
/// font, or the offset a TrueType Collection gives for one of its fonts)
/// and copies out the tables this sanitizer knows. Fails if there is no
/// directory there, a known table lies outside the file, or a known table
/// appears twice.
pub fn read_sfnt(input: &[u8], base: usize) -> (r: Option<Vec<Table>>)
    ensures
        read_as(r, sfnt_tables(input@, base as int)),
{
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
    assert(tview(ts@) =~= Seq::empty());
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == u16_at(input@, base + 4),
            base + 12 + 16 * n <= input.len(),
            sfnt_recs(input@, base as int, i as int) == Some(tview(ts@)),
        decreases n - i,
    {
        let r = base + 12 + 16 * i;
        let tag = rd32(input, r);
        if crate::font::is_known_tag(tag) {
            let off = rd32(input, r + 8) as usize;
            let len = rd32(input, r + 12) as usize;
            if off > input.len() || len > input.len() - off {
                proof { lemma_recs_none(input@, base as int, i + 1, n as int); }
                return None;
            }
            if lookup(&ts, tag).is_some() {
                proof { lemma_recs_none(input@, base as int, i + 1, n as int); }
                return None;
            }
            let ghost t0 = ts@;
            ts.push(Table { tag, data: to_vec(slice(input, off, off + len)) });
            assert(tview(ts@) =~= tview(t0).push((tag, input@.subrange(off as int, off + len))));
        }
        i += 1;
    }
    Some(ts)
}

/// Reads font `index` of a TrueType Collection.
pub fn read_ttc(input: &[u8], index: u32) -> (r: Option<Vec<Table>>)
    ensures
        read_as(r, ttc_tables(input@, index as int)),
{
    if input.len() < 12 || input.len() > MAX_LEN {
        return None;
    }
    let n = rd32(input, 8) as u64;
    let i = index as usize;
    if i as u64 >= n || 12 + 4 * n > input.len() as u64 {
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
    // The sizes the header states, in u64: they can pass a 32-bit usize.
    let mut sfnt: u64 = 12 + 16 * n as u64;
    let mut last: u64 = 0;
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
        sfnt = sfnt + (rd32(input, r + 12) as u64 + 3) / 4 * 4;
        let e = rd32(input, r + 4) as u64 + rd32(input, r + 8) as u64;
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
    if rd32(input, 16) as u64 != sfnt {
        return None;
    }
    // The metadata and private blocks, if any, follow the last table, and
    // the file ends there, with at most three bytes of padding between.
    let mut e = (last + 3) / 4 * 4;
    let meta = rd32(input, 24) as u64;
    if meta != 0 {
        if e != meta {
            return None;
        }
        e = (meta + rd32(input, 28) as u64 + 3) / 4 * 4;
    }
    let private = rd32(input, 36) as u64;
    if private != 0 {
        if e != private {
            return None;
        }
        e = (private + rd32(input, 40) as u64 + 3) / 4 * 4;
    }
    if e != (input.len() as u64 + 3) / 4 * 4 {
        return None;
    }
    Some(ts)
}

/// Reads the tables of a font file in any of the containers this crate
/// understands, told apart by the first four bytes. `index` picks the font
/// in a TrueType Collection and is ignored otherwise.
pub fn read_font(input: &[u8], index: u32) -> (r: Option<Vec<Table>>)
    ensures
        is_plain_sfnt(input@) ==> read_as(r, sfnt_tables(input@, 0)),
        is_ttc(input@) ==> read_as(r, ttc_tables(input@, index as int)),
{
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
    // u64: the sum of the kept lengths can pass a 32-bit usize.
    dst: u64,
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
        t.len() <= MAX_LEN,
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
    let mut body: u64 = 0;
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
                        body = body + len as u64;
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
        let dst = hdr as u64 + kept[x].dst;
        if dst > u32::MAX as u64 {
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
        repair_default_langsys(&mut v, t);
    }
    v
}

/// OTS does not look at a script's default language system, and fonts
/// exist whose default language system is not well formed (a required
/// feature index of 0 in a table with no features). This repairs what can
/// be repaired in place: a non-null lookup order offset is cleared, and a
/// required feature that does not exist becomes "none". A default
/// language system that is still not well formed is removed.
///
/// Where the fields are is read from `t`, the table as the font had it,
/// so that one repair cannot move another: `check_same` holds the output
/// to exactly those places.
fn repair_default_langsys(v: &mut Vec<u8>, t: &[u8])
    requires
        old(v)@.len() == t.len(),
{
    let len = v.len();
    if len < 10 || len > TABLE_MAX {
        return;
    }
    let sl = rd16(t, 4) as usize;
    let fl = rd16(t, 6) as usize;
    if sl == 0 || !room(t, sl, 2) {
        return;
    }
    let nf: usize = if fl != 0 && room(t, fl, 2) {
        rd16(t, fl) as usize
    } else {
        0
    };
    let n = rd16(t, sl) as usize;
    let mut i: usize = 0;
    while i < n
        invariant
            v@.len() == len,
            t.len() == len,
            len <= TABLE_MAX,
            sl + 2 <= len,
            n <= 65535,
        decreases n - i,
    {
        let r = sl + 2 + 6 * i;
        i += 1;
        if !room(t, r, 6) {
            return;
        }
        let so = sl + rd16(t, r + 4) as usize;
        if !room(t, so, 2) {
            continue;
        }
        let d = rd16(t, so) as usize;
        if d == 0 {
            continue;
        }
        let l = so + d;
        if !room(t, l, 6) {
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

// ---------------------------------------------------------------------
// Laying the tables out as a file, proven
// ---------------------------------------------------------------------
/// Each tag is greater than the one before.
pub open spec fn sorted_tags(ts: Seq<Table>) -> bool {
    forall|i: int| 0 < i < ts.len() ==> #[trigger] tag_step(ts, i)
}

pub open spec fn tag_step(ts: Seq<Table>, i: int) -> bool {
    ts[i].tag > ts[i - 1].tag
}

/// Where table `k` starts in the file `assemble` writes for `n` tables.
pub open spec fn place_off(ts: Tables, n: int, k: int) -> int {
    12 + 16 * n + body_len(ts, k)
}

/// The byte of table `k` that `assemble` writes at its offset `j`:
/// the table's own, but zero for `head.checkSumAdjustment`.
pub open spec fn placed_byte(t: (u32, Seq<u8>), j: int) -> u8 {
    if t.0 == T_HEAD && t.1.len() >= 12 && 8 <= j < 12 {
        0
    } else {
        t.1[j]
    }
}

/// Record `k` of `s` and its table are as `assemble` writes them, before
/// the checksum adjustment is filled in.
#[verifier::opaque]
pub open spec fn placed(s: Seq<u8>, ts: Tables, n: int, k: int) -> bool {
    let off = place_off(ts, n, k);
    let len = ts[k].1.len() as int;
    let pend = pad4(off + len);
    &&& 12 + 16 * k + 16 <= s.len()
    &&& rec_tag(s, k) == ts[k].0
    &&& rec_off(s, k) == off
    &&& rec_len(s, k) == len
    &&& rec_sum(s, k) == words_sum(s, off / 4, pend / 4)
    &&& pend <= s.len()
    &&& zeros(s, off + len, pend)
    &&& forall|j: int| 0 <= j < len ==> #[trigger] s[off + j] == placed_byte(ts[k], j)
}

pub proof fn lemma_sum_frame(s1: Seq<u8>, s2: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo,
        4 * hi <= s1.len(),
        4 * hi <= s2.len(),
        forall|b: int| 4 * lo <= b < 4 * hi ==> s1[b] == s2[b],
    ensures
        words_sum(s1, lo, hi) == words_sum(s2, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_frame(s1, s2, lo, hi - 1);
        let w = 4 * (hi - 1);
        assert(s1[w] == s2[w] && s1[w + 1] == s2[w + 1] && s1[w + 2] == s2[w + 2] && s1[w + 3] == s2[w + 3]);
    }
}

pub proof fn lemma_sum_bound(s: Seq<u8>, lo: int, hi: int)
    ensures
        0 <= words_sum(s, lo, hi) < 0x1_0000_0000,
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_bound(s, lo, hi - 1);
    }
}

/// Changing one word changes the sum by the difference, modulo 2^32.
pub proof fn lemma_sum_update(s1: Seq<u8>, s2: Seq<u8>, lo: int, hi: int, w: int)
    requires
        0 <= lo <= w < hi,
        4 * hi <= s1.len(),
        4 * hi <= s2.len(),
        forall|b: int| 4 * lo <= b < 4 * hi && !(4 * w <= b < 4 * w + 4) ==> s1[b] == s2[b],
    ensures
        words_sum(s2, lo, hi) == (words_sum(s1, lo, hi) + u32_at(s2, 4 * w) - u32_at(s1, 4 * w))
            % 0x1_0000_0000,
    decreases hi - lo,
{
    let m: int = 0x1_0000_0000;
    let d = u32_at(s2, 4 * w) - u32_at(s1, 4 * w);
    if hi - 1 == w {
        lemma_sum_frame(s1, s2, lo, w);
        let a = words_sum(s1, lo, w);
        let x1 = u32_at(s1, 4 * w);
        let x2 = u32_at(s2, 4 * w);
        // ((a + x1) % m + d) % m == (a + x2) % m
        vstd::arithmetic::div_mod::lemma_add_mod_noop_right(d, a + x1, m);
    } else {
        lemma_sum_update(s1, s2, lo, hi - 1, w);
        let y = u32_at(s1, 4 * (hi - 1));
        let yb = 4 * (hi - 1);
        assert(s1[yb] == s2[yb] && s1[yb + 1] == s2[yb + 1] && s1[yb + 2] == s2[yb + 2] && s1[yb + 3]
            == s2[yb + 3]);
        assert(u32_at(s2, yb) == y);
        let a = words_sum(s1, lo, hi - 1);
        // ((a + d) % m + y) % m == ((a + y) % m + d) % m
        vstd::arithmetic::div_mod::lemma_add_mod_noop_right(y, a + d, m);
        vstd::arithmetic::div_mod::lemma_add_mod_noop_right(d, a + y, m);
        assert(a + d + y == a + y + d);
    }
}

pub proof fn lemma_pad4(a: int, b: int)
    requires
        a % 4 == 0,
        a >= 0,
        b >= 0,
    ensures
        pad4(a + b) == a + pad4(b),
        pad4(b) % 4 == 0,
        b <= pad4(b) < b + 4,
{
    assert(pad4(a + b) == a + pad4(b)) by (nonlinear_arith)
        requires
            a % 4 == 0,
            a >= 0,
            b >= 0,
    ;
    assert(pad4(b) % 4 == 0 && b <= pad4(b) < b + 4) by (nonlinear_arith)
        requires
            b >= 0,
    ;
}

pub proof fn lemma_body_len4(ts: Tables, a: int)
    requires
        0 <= a <= ts.len(),
    ensures
        body_len(ts, a) % 4 == 0,
        body_len(ts, a) >= 0,
    decreases a,
{
    if a > 0 {
        lemma_body_len4(ts, a - 1);
        lemma_pad4(body_len(ts, a - 1), ts[a - 1].1.len() as int);
        lemma_pad4(0, ts[a - 1].1.len() as int);
        assert(pad4(0 + ts[a - 1].1.len() as int) == pad4(ts[a - 1].1.len() as int));
    }
}

pub proof fn lemma_body_len(ts: Tables, a: int, b: int)
    requires
        0 <= a <= b <= ts.len(),
    ensures
        body_len(ts, a) <= body_len(ts, b),
        body_len(ts, a) % 4 == 0,
        body_len(ts, a) >= 0,
    decreases b - a,
{
    lemma_body_len4(ts, a);
    if a < b {
        lemma_body_len(ts, a, b - 1);
        lemma_pad4(0, ts[b - 1].1.len() as int);
        assert(pad4(0 + ts[b - 1].1.len() as int) == pad4(ts[b - 1].1.len() as int));
    }
}

/// Writes one directory record at `r`.
fn put_rec(out: &mut Vec<u8>, r: usize, tag: u32, sum: u32, off: u32, len: u32)
    requires
        r + 16 <= old(out)@.len(),
        r <= 0x1_0000,
    ensures
        final(out)@.len() == old(out)@.len(),
        u32_at(final(out)@, r as int) == tag,
        u32_at(final(out)@, r + 4) == sum,
        u32_at(final(out)@, r + 8) == off,
        u32_at(final(out)@, r + 12) == len,
        forall|j: int| 0 <= j < old(out)@.len() && !(r <= j < r + 16) ==> final(out)@[j] == old(out)@[j],
{
    let r4 = r + 4;
    let r8 = r + 8;
    let r12 = r + 12;
    set32(out, r, tag);
    let ghost a = out@;
    set32(out, r4, sum);
    let ghost b = out@;
    set32(out, r8, off);
    let ghost c = out@;
    set32(out, r12, len);
    let ghost d = out@;
    assert(u32_at(d, r as int) == u32_at(a, r as int)) by {
        assert(d[r as int] == a[r as int] && d[r + 1] == a[r + 1] && d[r + 2] == a[r + 2] && d[r + 3] == a[r + 3]);
    }
    assert(u32_at(d, r + 4) == u32_at(b, r + 4)) by {
        assert(d[r + 4] == b[r + 4] && d[r + 5] == b[r + 5] && d[r + 6] == b[r + 6] && d[r + 7] == b[r + 7]);
    }
    assert(u32_at(d, r + 8) == u32_at(c, r + 8)) by {
        assert(d[r + 8] == c[r + 8] && d[r + 9] == c[r + 9] && d[r + 10] == c[r + 10] && d[r + 11] == c[r + 11]);
    }
}

/// Table `t` appended to `o0` (giving `oa`), padded (`ob`), and if it
/// is `head`, its checkSumAdjustment zeroed (`o1`).
proof fn lemma_append_facts(o0: Seq<u8>, oa: Seq<u8>, ob: Seq<u8>, o1: Seq<u8>, t: (u32, Seq<u8>))
    requires
        oa == o0 + t.1,
        ob.len() == pad4(oa.len() as int),
        ob.subrange(0, oa.len() as int) == oa,
        zeros(ob, oa.len() as int, ob.len() as int),
        o1.len() == ob.len(),
        if t.0 == T_HEAD && t.1.len() >= 12 {
            &&& u32_at(o1, o0.len() + 8int) == 0
            &&& forall|j: int| 0 <= j < ob.len() && !(o0.len() + 8 <= j < o0.len() + 12) ==> o1[j] == ob[j]
        } else {
            o1 == ob
        },
    ensures
        o1.len() == pad4(o0.len() + t.1.len() as int),
        forall|j: int| 0 <= j < o0.len() ==> o1[j] == o0[j],
        forall|j: int| 0 <= j < t.1.len() ==> #[trigger] o1[o0.len() + j] == placed_byte(t, j),
        zeros(o1, o0.len() + t.1.len() as int, o1.len() as int),
{
    let off = o0.len() as int;
    let len = t.1.len() as int;
    assert forall|j: int| 0 <= j < oa.len() implies ob[j] == oa[j] by {
        assert(ob.subrange(0, oa.len() as int)[j] == ob[j]);
    }
    assert forall|j: int| 0 <= j < off implies o1[j] == o0[j] by {
        assert(ob[j] == oa[j]);
        assert(oa[j] == o0[j]);
    }
    assert forall|j: int| 0 <= j < len implies #[trigger] o1[off + j] == placed_byte(t, j) by {
        assert(ob[off + j] == oa[off + j]);
        assert(oa[off + j] == t.1[j]);
        if t.0 == T_HEAD && len >= 12 && 8 <= j < 12 {
            assert(u32_at(o1, off + 8) == 0);
        }
    }
    assert(zeros(o1, off + len, o1.len() as int)) by {
        assert forall|j: int| off + len <= j < o1.len() implies o1[j] == 0 by {
            assert(ob[j] == 0);
        }
    }
}

/// One step of `assemble`'s loop: table `i` was appended to `o0` (giving
/// `o1`) and its record written (giving `s`).
proof fn lemma_assemble_step(o0: Seq<u8>, o1: Seq<u8>, s: Seq<u8>, tv: Tables, n: int, i: int, sum: int)
    requires
        0 <= i < n == tv.len(),
        o0.len() == place_off(tv, n, i),
        forall|k: int| 0 <= k < i ==> #[trigger] placed(o0, tv, n, k),
        o1.len() == pad4(o0.len() + tv[i].1.len() as int),
        forall|j: int| 0 <= j < o0.len() ==> o1[j] == o0[j],
        forall|j: int| 0 <= j < tv[i].1.len() ==> #[trigger] o1[o0.len() + j] == placed_byte(tv[i], j),
        zeros(o1, o0.len() + tv[i].1.len() as int, o1.len() as int),
        s.len() == o1.len(),
        forall|j: int| 0 <= j < s.len() && !(12 + 16 * i <= j < 12 + 16 * i + 16) ==> s[j] == o1[j],
        rec_tag(s, i) == tv[i].0,
        rec_sum(s, i) == sum,
        rec_off(s, i) == o0.len(),
        rec_len(s, i) == tv[i].1.len(),
        sum == words_sum(o1, o0.len() as int / 4, o1.len() as int / 4),
    ensures
        forall|k: int| 0 <= k <= i ==> #[trigger] placed(s, tv, n, k),
{
    let off = o0.len() as int;
    let len = tv[i].1.len() as int;
    let pend = o1.len() as int;
    reveal(placed);
    lemma_place_next(tv, n, i);
    lemma_body_len(tv, 0, i);
    assert(12 + 16 * n <= off);
    assert(pend % 4 == 0 && off % 4 == 0) by {
        lemma_pad4(off, len);
    }
    assert(4 * (pend / 4) == pend && 4 * (off / 4) == off);
    lemma_sum_frame(o1, s, off / 4, pend / 4);
    assert(placed(s, tv, n, i)) by {
        assert forall|j: int| 0 <= j < len implies #[trigger] s[off + j] == placed_byte(tv[i], j) by {
            assert(o1[off + j] == placed_byte(tv[i], j));
        }
        assert forall|j: int| off + len <= j < pend implies s[j] == 0 by {
            assert(o1[j] == 0);
        }
    }
    assert forall|k: int| 0 <= k <= i implies #[trigger] placed(s, tv, n, k) by {
        if k < i {
            lemma_place_next(tv, n, k);
            lemma_body_len(tv, k + 1, i);
            assert forall|j: int| 0 <= j < o0.len() && !(12 + 16 * i <= j < 12 + 16 * i + 16) implies s[j] == o0[j] by {
                assert(o1[j] == o0[j]);
            }
            assert(placed(o0, tv, n, k));
            lemma_body_len(tv, 0, k);
            assert forall|j: int|
                place_off(tv, n, k) <= j < pad4(place_off(tv, n, k) + tv[k].1.len()) implies o0[j] == s[j] by {
                assert(o1[j] == o0[j]);
            }
            assert forall|j: int| 12 + 16 * k <= j < 12 + 16 * k + 16 implies o0[j] == s[j] by {
                assert(o1[j] == o0[j]);
            }
            lemma_placed_frame(o0, s, tv, n, k);
        }
    }
}

/// Where table `k` ends with its padding is where table `k + 1` starts.
pub proof fn lemma_place_next(ts: Tables, n: int, k: int)
    requires
        0 <= k < ts.len(),
        n >= 0,
    ensures
        pad4(place_off(ts, n, k) + ts[k].1.len()) == place_off(ts, n, k + 1),
        place_off(ts, n, k) % 4 == 0,
{
    lemma_body_len(ts, k, k);
    lemma_pad4(place_off(ts, n, k), ts[k].1.len() as int);
}

/// `placed` survives changes outside record `k` and its table.
pub proof fn lemma_placed_frame(s1: Seq<u8>, s2: Seq<u8>, ts: Tables, n: int, k: int)
    requires
        0 <= k < ts.len(),
        n >= 0,
        placed(s1, ts, n, k),
        s1.len() <= s2.len(),
        forall|j: int| 12 + 16 * k <= j < 12 + 16 * k + 16 ==> s1[j] == s2[j],
        forall|j: int|
            place_off(ts, n, k) <= j < pad4(place_off(ts, n, k) + ts[k].1.len()) ==> s1[j] == s2[j],
    ensures
        placed(s2, ts, n, k),
{
    reveal(placed);
    let off = place_off(ts, n, k);
    let len = ts[k].1.len() as int;
    let pend = pad4(off + len);
    lemma_place_next(ts, n, k);
    lemma_body_len(ts, k, k);
    let r = 12 + 16 * k;
    assert(rec_tag(s2, k) == rec_tag(s1, k));
    assert(rec_sum(s2, k) == rec_sum(s1, k));
    assert(rec_off(s2, k) == rec_off(s1, k));
    assert(rec_len(s2, k) == rec_len(s1, k));
    assert(off % 4 == 0 && pend % 4 == 0) by {
        lemma_pad4(off, len);
    }
    assert(4 * (off / 4) == off && 4 * (pend / 4) == pend);
    lemma_sum_frame(s1, s2, off / 4, pend / 4);
    assert forall|j: int| 0 <= j < len implies #[trigger] s2[off + j] == placed_byte(ts[k], j) by {
        assert(s1[off + j] == placed_byte(ts[k], j));
    }
}

/// The bytes of table `k` of a file `assemble` wrote: its own, except
/// for `head`'s checkSumAdjustment.
pub open spec fn holds_table(s: Seq<u8>, t: (u32, Seq<u8>), k: int) -> bool {
    let x = s.subrange(rec_off(s, k), rec_end(s, k));
    if t.0 == T_HEAD {
        head_eq(x, t.1)
    } else {
        x == t.1
    }
}

/// Record `k` of the finished file, as `rec_ok` and `assemble`'s
/// postcondition need it.
#[verifier::opaque]
pub open spec fn fin_rec(s: Seq<u8>, tv: Tables, n: int, k: int) -> bool {
    let off = place_off(tv, n, k);
    let len = tv[k].1.len() as int;
    &&& rec_tag(s, k) == tv[k].0
    &&& rec_off(s, k) == off
    &&& rec_len(s, k) == len
    &&& pad4(off + len) <= s.len()
    &&& zeros(s, off + len, pad4(off + len))
    &&& rec_sum(s, k) == table_sum(s, k)
    &&& holds_table(s, tv[k], k)
}

/// A record's fields depend only on its 16 bytes.
proof fn lemma_rec_frame(s1: Seq<u8>, s2: Seq<u8>, k: int)
    requires
        forall|j: int| 12 + 16 * k <= j < 12 + 16 * k + 16 ==> s1[j] == s2[j],
    ensures
        rec_tag(s1, k) == rec_tag(s2, k),
        rec_sum(s1, k) == rec_sum(s2, k),
        rec_off(s1, k) == rec_off(s2, k),
        rec_len(s1, k) == rec_len(s2, k),
{
    let r = 12 + 16 * k;
    assert(s1[r] == s2[r] && s1[r + 1] == s2[r + 1] && s1[r + 2] == s2[r + 2] && s1[r + 3] == s2[r + 3]);
    assert(s1[r + 4] == s2[r + 4] && s1[r + 5] == s2[r + 5] && s1[r + 6] == s2[r + 6] && s1[r + 7] == s2[r + 7]);
    assert(s1[r + 8] == s2[r + 8] && s1[r + 9] == s2[r + 9] && s1[r + 10] == s2[r + 10] && s1[r + 11] == s2[r + 11]);
    assert(s1[r + 12] == s2[r + 12] && s1[r + 13] == s2[r + 13] && s1[r + 14] == s2[r + 14] && s1[r + 15] == s2[r + 15]);
}

/// A finished table other than `head`.
proof fn lemma_fin_other(o2: Seq<u8>, s: Seq<u8>, ts: Seq<Table>, tv: Tables, n: int, hk: int, k: int)
    requires
        tv == tview(ts),
        sorted_tags(ts),
        n == ts.len(),
        0 <= hk < n,
        0 <= k < n,
        k != hk,
        ts[hk].tag == T_HEAD,
        ts[hk].data@.len() >= 12,
        placed(o2, tv, n, k),
        s.len() == o2.len(),
        forall|j: int|
            0 <= j < s.len() && !(place_off(tv, n, hk) + 8 <= j < place_off(tv, n, hk) + 12) ==> s[j]
                == o2[j],
    ensures
        fin_rec(s, tv, n, k),
{
    lemma_place_next(tv, n, k);
    lemma_place_next(tv, n, hk);
    lemma_body_len(tv, 0, hk);
    lemma_body_len(tv, 0, k);
    if k < hk {
        lemma_body_len(tv, k + 1, hk);
        lemma_tags_increase(ts, k, hk);
    } else {
        lemma_body_len(tv, hk + 1, k);
        lemma_tags_increase(ts, hk, k);
    }
    assert(tv[k] == (ts[k].tag, ts[k].data@));
    assert(tv[hk] == (ts[hk].tag, ts[hk].data@));
    lemma_pad4(place_off(tv, n, hk), tv[hk].1.len() as int);
    reveal(placed);
    assert(o2.len() >= pad4(place_off(tv, n, k) + tv[k].1.len()));
    assert forall|j: int| 12 + 16 * k <= j < 12 + 16 * k + 16 implies o2[j] == s[j] by {}
    assert forall|j: int|
        place_off(tv, n, k) <= j < pad4(place_off(tv, n, k) + tv[k].1.len()) implies o2[j] == s[j] by {}
    lemma_placed_frame(o2, s, tv, n, k);
    lemma_fin_placed(s, tv, n, k);
}

/// Record `k` of the finished file is as `rec_ok` asks.
proof fn lemma_fin_ok(s: Seq<u8>, ts: Seq<Table>, tv: Tables, n: int, k: int)
    requires
        tv == tview(ts),
        sorted_tags(ts),
        n == ts.len(),
        0 <= k < n,
        num_tables(s) == n,
        fin_rec(s, tv, n, k),
        k > 0 ==> fin_rec(s, tv, n, k - 1),
    ensures
        rec_ok(s, k),
        rec_tag(s, k) == ts[k].tag,
        holds_table(s, tv[k], k),
        k == n - 1 ==> s.len() == place_off(tv, n, n) ==> s.len() == pad4(rec_end(s, n - 1)),
{
    reveal(fin_rec);
    lemma_place_next(tv, n, k);
    assert(tv[k] == (ts[k].tag, ts[k].data@));
    if k > 0 {
        lemma_place_next(tv, n, k - 1);
        assert(tag_step(ts, k));
        assert(tv[k] == (ts[k].tag, ts[k].data@));
        assert(tv[k - 1] == (ts[k - 1].tag, ts[k - 1].data@));
    } else {
        assert(body_len(tv, 0) == 0);
    }
}

/// A table other than `head` is finished once placed.
proof fn lemma_fin_placed(s: Seq<u8>, tv: Tables, n: int, k: int)
    requires
        0 <= k < tv.len(),
        n >= 0,
        placed(s, tv, n, k),
        tv[k].0 != T_HEAD,
    ensures
        fin_rec(s, tv, n, k),
{
    reveal(placed);
    reveal(fin_rec);
    let off = place_off(tv, n, k);
    let len = tv[k].1.len() as int;
    let x = s.subrange(rec_off(s, k), rec_end(s, k));
    assert(x =~= tv[k].1) by {
        assert forall|j: int| 0 <= j < len implies x[j] == tv[k].1[j] by {
            assert(s[off + j] == placed_byte(tv[k], j));
        }
    }
}

/// The `head` record, after its checkSumAdjustment is written.
proof fn lemma_fin_head(o2: Seq<u8>, s: Seq<u8>, tv: Tables, n: int, hk: int, adj: int)
    requires
        0 <= hk < tv.len(),
        n == tv.len(),
        placed(o2, tv, n, hk),
        tv[hk].0 == T_HEAD,
        tv[hk].1.len() >= 12,
        s.len() == o2.len(),
        forall|j: int|
            0 <= j < s.len() && !(place_off(tv, n, hk) + 8 <= j < place_off(tv, n, hk) + 12) ==> s[j]
                == o2[j],
        u32_at(s, place_off(tv, n, hk) + 8) == adj,
        0 <= adj < 0x1_0000_0000,
    ensures
        fin_rec(s, tv, n, hk),
        u32_at(o2, place_off(tv, n, hk) + 8) == 0,
{
    reveal(placed);
    reveal(fin_rec);
    let m: int = 0x1_0000_0000;
    let hoff = place_off(tv, n, hk);
    let hlen = tv[hk].1.len() as int;
    let hpend = pad4(hoff + hlen);
    let h = hoff;
    lemma_place_next(tv, n, hk);
    lemma_body_len(tv, 0, hk);
    assert(o2[h + 8] == 0 && o2[h + 9] == 0 && o2[h + 10] == 0 && o2[h + 11] == 0) by {
        assert(o2[hoff + 8] == placed_byte(tv[hk], 8));
        assert(o2[hoff + 9] == placed_byte(tv[hk], 9));
        assert(o2[hoff + 10] == placed_byte(tv[hk], 10));
        assert(o2[hoff + 11] == placed_byte(tv[hk], 11));
    }
    assert(u32_at(o2, h + 8) == 0);
    lemma_rec_frame(o2, s, hk);
    assert(4 * (hoff / 4) == hoff && 4 * (hpend / 4) == hpend && hoff % 4 == 0) by {
        lemma_pad4(hoff, hlen);
    }
    assert(4 * ((h + 8) / 4) == h + 8);
    lemma_sum_update(o2, s, hoff / 4, hpend / 4, (h + 8) / 4);
    lemma_sum_bound(o2, hoff / 4, hpend / 4);
    let sum0 = words_sum(o2, hoff / 4, hpend / 4);
    let sum1 = words_sum(s, hoff / 4, hpend / 4);
    assert(sum1 == (sum0 + adj) % m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop_right(-(adj as int), sum0 + adj, m);
    assert((sum1 - adj) % m == sum0) by {
        vstd::arithmetic::div_mod::lemma_small_mod(sum0 as nat, m as nat);
    }
    assert(table_sum(s, hk) == rec_sum(s, hk));
    assert(zeros(s, hoff + hlen, hpend));
    let x = s.subrange(rec_off(s, hk), rec_end(s, hk));
    assert forall|j: int| 0 <= j < x.len() && !(8 <= j < 12) implies #[trigger] x[j] == tv[hk].1[j] by {
        assert(o2[hoff + j] == placed_byte(tv[hk], j));
    }
}

/// The checksum of the whole file.
proof fn lemma_fin_total(o2: Seq<u8>, s: Seq<u8>, h: int, total: int, adj: int)
    requires
        o2.len() % 4 == 0,
        0 <= h,
        h % 4 == 0,
        h + 12 <= o2.len(),
        s.len() == o2.len(),
        forall|j: int| 0 <= j < s.len() && !(h + 8 <= j < h + 12) ==> s[j] == o2[j],
        u32_at(s, h + 8) == adj,
        u32_at(o2, h + 8) == 0,
        total == words_sum(o2, 0, o2.len() as int / 4),
        (total + adj) % 0x1_0000_0000 == 0xB1B0_AFBA,
    ensures
        words_sum(s, 0, s.len() as int / 4) == 0xB1B0_AFBA,
{
    assert(4 * ((h + 8) / 4) == h + 8);
    assert(4 * (s.len() as int / 4) == s.len());
    lemma_sum_update(o2, s, 0, s.len() as int / 4, (h + 8) / 4);
}

/// The end of `assemble`: with the checksum adjustment filled in, the
/// file is a well-formed directory over the tables.
proof fn lemma_assemble_finish(
    o2: Seq<u8>,
    s: Seq<u8>,
    ts: Seq<Table>,
    tv: Tables,
    n: int,
    hk: int,
    h: int,
    h0: Seq<u8>,
    total: int,
    adj: int,
    version: u32,
)
    requires
        tv == tview(ts),
        sorted_tags(ts),
        1 <= n == ts.len() <= MAX_TABLES,
        forall|k: int| 0 <= k < n ==> #[trigger] placed(o2, tv, n, k),
        o2.len() == place_off(tv, n, n),
        o2.len() % 4 == 0,
        0 <= hk < n,
        h == place_off(tv, n, hk),
        ts[hk].tag == T_HEAD,
        ts[hk].data@.len() >= 12,
        s.len() == o2.len(),
        forall|j: int| 0 <= j < s.len() && !(h + 8 <= j < h + 12) ==> s[j] == o2[j],
        u32_at(s, h + 8) == adj,
        0 <= adj < 0x1_0000_0000,
        total == words_sum(o2, 0, o2.len() as int / 4),
        (total + adj) % 0x1_0000_0000 == 0xB1B0_AFBA,
        h0.len() == 12,
        forall|j: int| 0 <= j < 12 ==> o2[j] == #[trigger] h0[j],
        version == TAG_TRUETYPE || version == TAG_OTTO,
        u32_at(h0, 0) == version,
        u16_at(h0, 4) == n,
        u16_at(h0, 6) == 16 * pow2_floor(n, 1, 0).0,
        u16_at(h0, 8) == pow2_floor(n, 1, 0).1,
        u16_at(h0, 10) == 16 * n - u16_at(h0, 6),
    ensures
        wf_directory(s),
        words_sum(s, 0, s.len() as int / 4) == 0xB1B0_AFBA,
        num_tables(s) == n,
        u32_at(s, 0) == version,
        forall|k: int| 0 <= k < n ==> #[trigger] rec_tag(s, k) == ts[k].tag,
        forall|k: int| 0 <= k < n ==> #[trigger] holds_table(s, tv[k], k),
{
    assert(tv.len() == n);
    lemma_body_len(tv, 0, n);
    lemma_body_len(tv, hk + 1, n);
    lemma_body_len(tv, 0, hk);
    lemma_place_next(tv, n, hk);
    assert(tv[hk] == (ts[hk].tag, ts[hk].data@));
    lemma_pad4(h, tv[hk].1.len() as int);
    lemma_fin_head(o2, s, tv, n, hk, adj);
    lemma_place_next(tv, n, hk);
    lemma_fin_total(o2, s, h, total, adj);
    assert forall|k: int| 0 <= k < n implies #[trigger] fin_rec(s, tv, n, k) by {
        if k != hk {
            lemma_fin_other(o2, s, ts, tv, n, hk, k);
        }
    }
    assert(num_tables(s) == n) by {
        lemma_body_len(tv, 0, hk);
        assert(s[4] == h0[4] && s[5] == h0[5]) by {
            assert(o2[4] == h0[4] && o2[5] == h0[5]);
        }
    }
    assert forall|k: int| 0 <= k < n implies #[trigger] rec_ok(s, k) by {
        lemma_fin_ok(s, ts, tv, n, k);
    }
    assert(s.len() == pad4(rec_end(s, n - 1))) by {
        lemma_fin_ok(s, ts, tv, n, n - 1);
    }
    lemma_body_len(tv, 0, hk);
    assert(s[0] == h0[0] && s[1] == h0[1] && s[2] == h0[2] && s[3] == h0[3] && s[6] == h0[6] && s[7]
        == h0[7] && s[8] == h0[8] && s[9] == h0[9] && s[10] == h0[10] && s[11] == h0[11]) by {
        assert(o2[0] == h0[0] && o2[1] == h0[1] && o2[2] == h0[2] && o2[3] == h0[3] && o2[6] == h0[6] && o2[7]
            == h0[7] && o2[8] == h0[8] && o2[9] == h0[9] && o2[10] == h0[10] && o2[11] == h0[11]);
    }
    assert(u32_at(s, 0) == u32_at(h0, 0));
    assert(u16_at(s, 6) == u16_at(h0, 6));
    assert(u16_at(s, 8) == u16_at(h0, 8));
    assert(u16_at(s, 10) == u16_at(h0, 10));
    assert forall|k: int| 0 <= k < n implies #[trigger] rec_tag(s, k) == ts[k].tag by {
        lemma_fin_ok(s, ts, tv, n, k);
    }
    assert forall|k: int| 0 <= k < n implies #[trigger] holds_table(s, tv[k], k) by {
        lemma_fin_ok(s, ts, tv, n, k);
    }
}

/// What `assemble` needs to succeed: tables in increasing order of tag,
/// a `head` of at least 12 bytes, no table over 1 GiB and at most 1 GiB
/// in all.
pub open spec fn can_assemble(ts: Seq<Table>) -> bool {
    let tv = tview(ts);
    &&& 1 <= ts.len() <= MAX_TABLES
    &&& sorted_tags(ts)
    &&& in_has(tv, T_HEAD as int)
    &&& in_table(tv, T_HEAD as int).len() >= 12
    &&& body_len(tv, ts.len() as int) <= MAX_LEN
}

/// Lays the tables out as an sfnt file: header, directory, then each table
/// padded to four bytes, with checksums and `head.checkSumAdjustment`
/// filled in. The tables must be in increasing order of tag.
pub fn assemble(ts: &Vec<Table>, version: u32) -> (r: Option<Vec<u8>>)
    requires
        ts@.len() <= MAX_TABLES,
        version == TAG_TRUETYPE || version == TAG_OTTO,
    ensures
        r matches Some(out) ==> {
            &&& wf_directory(out@)
            &&& words_sum(out@, 0, out@.len() as int / 4) == 0xB1B0_AFBA
            &&& num_tables(out@) == ts@.len()
            &&& u32_at(out@, 0) == version
            &&& out@.len() == 12 + 16 * ts@.len() + body_len(tview(ts@), ts@.len() as int)
            &&& forall|k: int| 0 <= k < ts@.len() ==> #[trigger] rec_tag(out@, k) == ts@[k].tag
            &&& forall|k: int| 0 <= k < ts@.len() ==> #[trigger] holds_table(out@, tview(ts@)[k], k)
        },
        can_assemble(ts@) ==> r is Some,
{
    let ghost tv = tview(ts@);
    let n = ts.len();
    if n == 0 {
        return None;
    }
    let mut q: usize = 1;
    while q < n
        invariant
            1 <= q <= n == ts@.len(),
            forall|i: int| 0 < i < q ==> #[trigger] tag_step(ts@, i),
        decreases n - q,
    {
        if ts[q - 1].tag >= ts[q].tag {
            proof {
                if can_assemble(ts@) {
                    assert(tag_step(ts@, q as int));
                }
            }
            return None;
        }
        q += 1;
    }
    assert(sorted_tags(ts@));
    let (p, e) = crate::dir::pow2(n as u16);
    let mut out: Vec<u8> = Vec::new();
    put32(&mut out, version);
    put16(&mut out, n as u16);
    put16(&mut out, (16 * p) as u16);
    put16(&mut out, e as u16);
    put16(&mut out, (16 * (n as u32) - 16 * p) as u16);
    let ghost h0 = out@;
    assert(u32_at(h0, 0) == version && u16_at(h0, 4) == n && u16_at(h0, 6) == 16 * p && u16_at(h0, 8)
        == e && u16_at(h0, 10) == 16 * n - 16 * p) by {
        assert(h0.subrange(0, 4) == h0.subrange(0, 6).subrange(0, 4));
        assert(h0.subrange(0, 6) == h0.subrange(0, 8).subrange(0, 6));
        assert(h0.subrange(0, 8) == h0.subrange(0, 10).subrange(0, 8));
        assert(h0.subrange(0, 4)[0] == h0[0] && h0.subrange(0, 4)[1] == h0[1] && h0.subrange(0, 4)[2]
            == h0[2] && h0.subrange(0, 4)[3] == h0[3]);
        assert(h0.subrange(0, 6)[4] == h0[4] && h0.subrange(0, 6)[5] == h0[5]);
        assert(h0.subrange(0, 8)[6] == h0[6] && h0.subrange(0, 8)[7] == h0[7]);
        assert(h0.subrange(0, 10)[8] == h0[8] && h0.subrange(0, 10)[9] == h0[9]);
    }
    let mut i: usize = 0;
    while i < 16 * n
        invariant
            n <= MAX_TABLES,
            i <= 16 * n,
            out@.len() == 12 + i,
            forall|j: int| 0 <= j < 12 ==> out@[j] == #[trigger] h0[j],
            h0.len() == 12,
        decreases 16 * n - i,
    {
        out.push(0);
        i += 1;
    }
    let mut head_at: Option<usize> = None;
    let ghost mut hk: int = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == ts@.len() <= MAX_TABLES,
            tv == tview(ts@),
            sorted_tags(ts@),
            h0.len() == 12,
            forall|j: int| 0 <= j < 12 ==> out@[j] == #[trigger] h0[j],
            out@.len() == place_off(tv, n as int, i as int),
            out@.len() <= 12 + 16 * n + i * (MAX_LEN + 4),
            out@.len() % 4 == 0,
            forall|k: int| 0 <= k < i ==> #[trigger] placed(out@, tv, n as int, k),
            head_at matches Some(h) ==> {
                &&& h <= 0xFFFF_0000
                &&& h + 12 <= out@.len()
                &&& 0 <= hk < i
                &&& h == place_off(tv, n as int, hk)
                &&& ts@[hk].tag == T_HEAD
                &&& ts@[hk].data@.len() >= 12
            },
            (exists|k: int| 0 <= k < i && #[trigger] ts@[k].tag == T_HEAD && ts@[k].data@.len() >= 12)
                ==> head_at is Some,
            can_assemble(ts@) ==> body_len(tv, i as int) <= MAX_LEN,
        decreases n - i,
    {
        let ghost o0 = out@;
        proof {
            lemma_body_len(tv, i as int, i as int);
            lemma_place_next(tv, n as int, i as int);
            if can_assemble(ts@) {
                lemma_body_len(tv, i as int + 1, n as int);
            }
        }
        let t = &ts[i];
        if t.data.len() > MAX_LEN {
            return None;
        }
        let off = out.len();
        if off > 0xFFFF_0000 {
            return None;
        }
        append(&mut out, t.data.as_slice());
        let ghost oa = out@;
        pad(&mut out);
        let ghost ob = out@;
        assert(i * (MAX_LEN + 4) + MAX_LEN + 4 == (i + 1) * (MAX_LEN + 4)) by (nonlinear_arith);
        if t.tag == T_HEAD && t.data.len() >= 12 {
            set32(&mut out, off + 8, 0);
            head_at = Some(off);
            proof {
                hk = i as int;
            }
        }
        let ghost o1 = out@;
        proof {
            assert(tv[i as int] == (ts@[i as int].tag, ts@[i as int].data@));
            lemma_append_facts(o0, oa, ob, o1, tv[i as int]);
        }
        let sum = sum_words(out.as_slice(), off / 4, out.len() / 4);
        let r = 12 + 16 * i;
        put_rec(&mut out, r, t.tag, sum, off as u32, t.data.len() as u32);
        proof {
            lemma_assemble_step(o0, o1, out@, tv, n as int, i as int, sum as int);
            assert forall|j: int| 0 <= j < 12 implies out@[j] == h0[j] by {
                assert(o1[j] == o0[j]);
            }
        }
        i += 1;
    }
    match head_at {
        Some(h) => {
            let ghost o2 = out@;
            let total = sum_words(out.as_slice(), 0, out.len() / 4);
            let adj = if 0xB1B0_AFBAu32 >= total {
                0xB1B0_AFBAu32 - total
            } else {
                (0xB1B0_AFBAu64 + 0x1_0000_0000 - total as u64) as u32
            };
            set32(&mut out, h + 8, adj);
            proof {
                assert((total + adj) % 0x1_0000_0000 == 0xB1B0_AFBA);
                lemma_assemble_finish(o2, out@, ts@, tv, n as int, hk, h as int, h0, total as int, adj as int, version);
            }
        },
        None => {
            proof {
                if can_assemble(ts@) {
                    let k = find_in(tv, T_HEAD as int, 0);
                    lemma_find_in(tv, T_HEAD as int, 0);
                    assert(tv[k] == (ts@[k].tag, ts@[k].data@));
                    assert(ts@[k].tag == T_HEAD && ts@[k].data@.len() >= 12);
                }
            }
            return None;
        },
    }
    Some(out)
}

/// What `find_in` finds has the tag looked for, and nothing before it.
pub proof fn lemma_find_in(ts: Tables, t: int, i: int)
    requires
        0 <= i,
    ensures
        find_in(ts, t, i) < ts.len() ==> i <= find_in(ts, t, i) && ts[find_in(ts, t, i)].0 == t,
        find_in(ts, t, i) <= ts.len(),
        forall|k: int| i <= k < find_in(ts, t, i) ==> #[trigger] ts[k].0 != t,
    decreases ts.len() - i,
{
    if i < ts.len() && ts[i].0 != t {
        lemma_find_in(ts, t, i + 1);
    }
}

pub proof fn lemma_tags_increase(ts: Seq<Table>, a: int, b: int)
    requires
        sorted_tags(ts),
        0 <= a < b < ts.len(),
    ensures
        ts[a].tag < ts[b].tag,
    decreases b - a,
{
    if a < b - 1 {
        lemma_tags_increase(ts, a, b - 1);
    }
    assert(tag_step(ts, b));
}

} // verus!
