//! The trusted specification: what it means for a byte string to be a
//! well-formed OpenType font (`wf_font`).
//!
//! Everything here is a pure function of the bytes, written from the
//! OpenType specification (ISO/IEC 14496-22). The sanitizer is proven to
//! emit only byte strings that satisfy `wf_font`. Read this file to see
//! what that promise is worth.
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Big-endian fields
// ---------------------------------------------------------------------
pub open spec fn u16_at(s: Seq<u8>, i: int) -> int {
    s[i] as int * 256 + s[i + 1] as int
}

pub open spec fn i16_at(s: Seq<u8>, i: int) -> int {
    if u16_at(s, i) >= 32768 {
        u16_at(s, i) - 65536
    } else {
        u16_at(s, i)
    }
}

pub open spec fn u24_at(s: Seq<u8>, i: int) -> int {
    s[i] as int * 65536 + u16_at(s, i + 1)
}

pub open spec fn u32_at(s: Seq<u8>, i: int) -> int {
    u16_at(s, i) * 65536 + u16_at(s, i + 2)
}

/// A four-character table tag as the big-endian number its bytes spell.
pub open spec fn tag(a: u8, b: u8, c: u8, d: u8) -> int {
    ((a as int * 256 + b as int) * 256 + c as int) * 256 + d as int
}

pub open spec fn pad4(n: int) -> int {
    (n + 3) / 4 * 4
}

/// The sum, modulo 2^32, of the big-endian 32-bit words `lo..hi` of `s`
/// (word `w` is bytes `4w..4w+4`). This is the OpenType table checksum.
pub open spec fn words_sum(s: Seq<u8>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        (words_sum(s, lo, hi - 1) + u32_at(s, 4 * (hi - 1))) % 0x1_0000_0000
    }
}

// ---------------------------------------------------------------------
// The table directory
// ---------------------------------------------------------------------
pub open spec fn num_tables(s: Seq<u8>) -> int {
    u16_at(s, 4)
}

pub open spec fn rec_tag(s: Seq<u8>, i: int) -> int {
    u32_at(s, 12 + 16 * i)
}

pub open spec fn rec_sum(s: Seq<u8>, i: int) -> int {
    u32_at(s, 12 + 16 * i + 4)
}

pub open spec fn rec_off(s: Seq<u8>, i: int) -> int {
    u32_at(s, 12 + 16 * i + 8)
}

pub open spec fn rec_len(s: Seq<u8>, i: int) -> int {
    u32_at(s, 12 + 16 * i + 12)
}

pub open spec fn rec_end(s: Seq<u8>, i: int) -> int {
    rec_off(s, i) + rec_len(s, i)
}

/// The largest power of two that is at most `n`, as (value, log2), found
/// by counting up from `(p, e)`.
pub open spec fn pow2_floor(n: int, p: int, e: int) -> (int, int)
    decreases n - p,
{
    if p <= 0 || 2 * p > n {
        (p, e)
    } else {
        pow2_floor(n, 2 * p, e + 1)
    }
}

pub const TAG_TRUETYPE: u32 = 0x0001_0000;

pub const TAG_OTTO: u32 = 0x4F54_544F;

pub open spec fn zeros(s: Seq<u8>, a: int, b: int) -> bool {
    forall|j: int| a <= j < b ==> s[j] == 0
}

/// Record `i` of the directory and its table: the table
/// starts exactly where the one before it ends (rounded up to a multiple
/// of four; the first starts right after the directory), has a greater tag
/// than the one before, lies inside the file, is followed by zero padding,
/// and has the checksum the record says
/// ([`table_sum`]).
pub open spec fn rec_ok(s: Seq<u8>, i: int) -> bool {
    &&& rec_off(s, i) == if i == 0 {
        12 + 16 * num_tables(s)
    } else {
        pad4(rec_end(s, i - 1))
    }
    &&& (i > 0 ==> rec_tag(s, i - 1) < rec_tag(s, i))
    &&& pad4(rec_end(s, i)) <= s.len()
    &&& zeros(s, rec_end(s, i), pad4(rec_end(s, i)))
    &&& rec_sum(s, i) == table_sum(s, i)
}

/// The checksum of table `i`: the sum of its words, padding included. For
/// `head` the specification says to sum with `checkSumAdjustment` (the
/// word at offset 8) taken as zero, which is the sum less that word.
pub open spec fn table_sum(s: Seq<u8>, i: int) -> int {
    let sum = words_sum(s, rec_off(s, i) / 4, pad4(rec_end(s, i)) / 4);
    if rec_tag(s, i) == 0x6865_6164 && rec_len(s, i) >= 12 {
        (sum - u32_at(s, rec_off(s, i) + 8)) % 0x1_0000_0000
    } else {
        sum
    }
}

/// The header and table directory are well formed, and the tables tile the
/// rest of the file exactly: sorted by tag with no tag twice, each table
/// starting where the last one's padding ends and the file ending with the
/// last table's padding. So no two tables overlap, no table reaches
/// outside the file, and no byte of the file is unaccounted for.
pub open spec fn wf_directory(s: Seq<u8>) -> bool {
    let n = num_tables(s);
    &&& s.len() >= 12
    &&& (u32_at(s, 0) == TAG_TRUETYPE || u32_at(s, 0) == TAG_OTTO)
    &&& n >= 1
    &&& u16_at(s, 6) == 16 * pow2_floor(n, 1, 0).0
    &&& u16_at(s, 8) == pow2_floor(n, 1, 0).1
    &&& u16_at(s, 10) == 16 * n - u16_at(s, 6)
    &&& 12 + 16 * n <= s.len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] rec_ok(s, i)
    &&& s.len() == pad4(rec_end(s, n - 1))
}

/// The index of the first record at or after `i` with tag `t`, or
/// `num_tables(s)` if there is none.
pub open spec fn find_from(s: Seq<u8>, t: int, i: int) -> int
    decreases num_tables(s) - i,
{
    if i >= num_tables(s) {
        num_tables(s)
    } else if rec_tag(s, i) == t {
        i
    } else {
        find_from(s, t, i + 1)
    }
}

pub open spec fn has_table(s: Seq<u8>, t: int) -> bool {
    find_from(s, t, 0) < num_tables(s)
}

/// The bytes of the table with tag `t` (meaningful when `has_table`).
pub open spec fn table(s: Seq<u8>, t: int) -> Seq<u8> {
    let i = find_from(s, t, 0);
    s.subrange(rec_off(s, i), rec_end(s, i))
}

// ---------------------------------------------------------------------
// head, maxp, hhea, hmtx, OS/2
// ---------------------------------------------------------------------
pub open spec fn wf_head(t: Seq<u8>) -> bool {
    &&& t.len() == 54
    &&& u32_at(t, 0) == 0x0001_0000
    &&& u32_at(t, 12) == 0x5F0F_3CF5
    &&& 16 <= u16_at(t, 18) <= 16384
    &&& i16_at(t, 36) <= i16_at(t, 40)
    &&& i16_at(t, 38) <= i16_at(t, 42)
    &&& u16_at(t, 50) <= 1
    &&& u16_at(t, 52) == 0
}

/// `head.indexToLocFormat`: 0 for 16-bit `loca` entries, 1 for 32-bit.
pub open spec fn loc_format(head: Seq<u8>) -> int {
    u16_at(head, 50)
}

/// `truetype` says the font has `glyf` outlines, which need version 1.0.
pub open spec fn wf_maxp(t: Seq<u8>, truetype: bool) -> bool {
    &&& t.len() >= 6
    &&& u16_at(t, 4) >= 1
    &&& if u32_at(t, 0) == 0x0000_5000 {
        t.len() == 6 && !truetype
    } else {
        &&& u32_at(t, 0) == 0x0001_0000
        &&& t.len() == 32
        &&& 1 <= u16_at(t, 14) <= 2
    }
}

pub open spec fn num_glyphs(maxp: Seq<u8>) -> int {
    u16_at(maxp, 4)
}

pub open spec fn wf_hhea(t: Seq<u8>, ng: int) -> bool {
    &&& t.len() == 36
    &&& u16_at(t, 0) == 1
    &&& u16_at(t, 32) == 0
    &&& 1 <= u16_at(t, 34) <= ng
}

pub open spec fn num_hmetrics(hhea: Seq<u8>) -> int {
    u16_at(hhea, 34)
}

/// One (advance, left side bearing) pair for each of the first `nhm`
/// glyphs and one left side bearing for each of the rest, and nothing more.
pub open spec fn wf_hmtx(t: Seq<u8>, ng: int, nhm: int) -> bool {
    t.len() == 4 * nhm + 2 * (ng - nhm)
}

pub open spec fn wf_os2(t: Seq<u8>) -> bool {
    &&& t.len() >= 78
    &&& t.len() == if u16_at(t, 0) == 0 {
        78int
    } else if u16_at(t, 0) == 1 {
        86
    } else if u16_at(t, 0) <= 4 {
        96
    } else {
        100
    }
    &&& u16_at(t, 0) <= 5
}

// ---------------------------------------------------------------------
// loca and glyf
// ---------------------------------------------------------------------
/// Entry `i` of `loca`: the offset of glyph `i` in `glyf`.
pub open spec fn loca_at(loca: Seq<u8>, fmt: int, i: int) -> int {
    if fmt == 0 {
        2 * u16_at(loca, 2 * i)
    } else {
        u32_at(loca, 4 * i)
    }
}

/// Glyph `i` does not end before it starts, and ends at a multiple of
/// four.
pub open spec fn loca_step(loca: Seq<u8>, fmt: int, i: int) -> bool {
    &&& loca_at(loca, fmt, i) <= loca_at(loca, fmt, i + 1)
    &&& loca_at(loca, fmt, i + 1) % 4 == 0
}

/// Glyph `i`'s slot in `glyf`.
pub open spec fn glyph_of(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, i: int) -> Seq<u8> {
    glyf.subrange(loca_at(loca, fmt, i), loca_at(loca, fmt, i + 1))
}

/// `loca` has exactly `ng + 1` entries, they start at 0, never decrease,
/// are multiples of four, and the last is the length of `glyf`. One
/// exception: when no glyph has an outline, `glyf` is a single byte
/// (some systems refuse an empty table), which [`wf_glyf`] requires to be
/// zero.
pub open spec fn wf_loca(loca: Seq<u8>, fmt: int, ng: int, glyf_len: int) -> bool {
    &&& loca.len() == (ng + 1) * (if fmt == 0 {
        2int
    } else {
        4
    })
    &&& loca_at(loca, fmt, 0) == 0
    &&& forall|i: int| 0 <= i < ng ==> #[trigger] loca_step(loca, fmt, i)
    &&& (loca_at(loca, fmt, ng) == glyf_len || (loca_at(loca, fmt, ng) == 0 && glyf_len == 1))
}

/// Bytes of x (or y) coordinate data per point for a flag byte: `short` is
/// the X_SHORT_VECTOR (or Y) bit, `same` the X_IS_SAME (or Y) bit.
pub open spec fn coord_size(short: bool, same: bool) -> int {
    if short {
        1
    } else if same {
        0
    } else {
        2
    }
}

pub open spec fn flag_coord_size(f: u8) -> int {
    coord_size(f & 0x02 != 0, f & 0x10 != 0) + coord_size(f & 0x04 != 0, f & 0x20 != 0)
}

/// Reads flags at `p` until they cover `pts` points. Returns where the
/// flags end and how many bytes of coordinates they call for. A flag may
/// not use the reserved bit 7, and a repeat may not run past the last
/// point.
pub open spec fn flags_end(g: Seq<u8>, p: int, pts: int) -> Option<(int, int)>
    decreases pts,
{
    if pts <= 0 {
        Some((p, 0))
    } else if p < 0 || p >= g.len() {
        None
    } else if g[p] & 0x80 != 0 {
        None
    } else if g[p] & 0x08 != 0 {
        if p + 1 >= g.len() || 1 + g[p + 1] > pts {
            None
        } else {
            match flags_end(g, p + 2, pts - 1 - g[p + 1]) {
                Some((e, c)) => Some((e, c + (1 + g[p + 1]) * flag_coord_size(g[p]))),
                None => None,
            }
        }
    } else {
        match flags_end(g, p + 1, pts - 1) {
            Some((e, c)) => Some((e, c + flag_coord_size(g[p]))),
            None => None,
        }
    }
}

/// End point index of contour `k` of a simple glyph.
pub open spec fn end_pt(g: Seq<u8>, k: int) -> int {
    u16_at(g, 10 + 2 * k)
}

/// Where a simple glyph with `nc >= 1` contours ends: the contour end
/// points strictly increase, and the instructions, flags and coordinates
/// they imply all lie inside `g`.
pub open spec fn simple_end(g: Seq<u8>, nc: int) -> Option<int> {
    let ilen = u16_at(g, 10 + 2 * nc);
    let fp = 12 + 2 * nc + ilen;
    if 12 + 2 * nc > g.len() || fp > g.len() {
        None
    } else if !(forall|k: int| 0 <= k < nc - 1 ==> #[trigger] end_pt(g, k) < end_pt(g, k + 1)) {
        None
    } else {
        match flags_end(g, fp, end_pt(g, nc - 1) + 1) {
            Some((e, c)) => if e + c <= g.len() {
                Some(e + c)
            } else {
                None
            },
            None => None,
        }
    }
}

/// Size of a composite component's arguments and transform, from the low
/// byte of its flags.
pub open spec fn comp_extra(lo: u8) -> int {
    (if lo & 0x01 != 0 {
        4int
    } else {
        2
    }) + (if lo & 0x08 != 0 {
        2int
    } else if lo & 0x40 != 0 {
        4
    } else if lo & 0x80 != 0 {
        8
    } else {
        0
    })
}

/// Where the component list starting at `p` ends: every component names a
/// glyph below `ng` and lies inside `g`, and so do the instructions after
/// the last one, if it says there are any.
pub open spec fn comp_end(g: Seq<u8>, p: int, ng: int) -> Option<int>
    decreases g.len() - p,
{
    if p < 0 || p + 4 > g.len() {
        None
    } else {
        let lo = g[p + 1];
        let q = p + 4 + comp_extra(lo);
        if u16_at(g, p + 2) >= ng || q > g.len() {
            None
        } else if lo & 0x20 != 0 {
            comp_end(g, q, ng)
        } else if g[p] & 0x01 != 0 {
            if q + 2 > g.len() || q + 2 + u16_at(g, q) > g.len() {
                None
            } else {
                Some(q + 2 + u16_at(g, q))
            }
        } else {
            Some(q)
        }
    }
}

/// Where the glyph description at the start of `g` ends.
pub open spec fn glyph_end(g: Seq<u8>, ng: int) -> Option<int> {
    if g.len() < 10 {
        None
    } else if i16_at(g, 0) >= 1 {
        simple_end(g, i16_at(g, 0))
    } else if i16_at(g, 0) == -1 {
        comp_end(g, 10, ng)
    } else {
        None
    }
}

/// `g` is one glyph description followed by fewer than four zero bytes.
pub open spec fn wf_glyph(g: Seq<u8>, ng: int) -> bool {
    match glyph_end(g, ng) {
        Some(e) => {
            &&& g.len() - e < 4
            &&& forall|j: int| e <= j < g.len() ==> g[j] == 0
        },
        None => false,
    }
}

/// Every glyph that `loca` gives a nonempty range is well formed.
pub open spec fn wf_glyf(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, ng: int) -> bool {
    &&& (loca_at(loca, fmt, ng) == 0 && glyf.len() == 1 ==> glyf[0] == 0)
    &&& forall|i: int| 0 <= i < ng ==> #[trigger] glyph_ok(glyf, loca, fmt, ng, i)
}

/// Glyph `i` is empty or well formed.
pub open spec fn glyph_ok(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, ng: int, i: int) -> bool {
    loca_at(loca, fmt, i) < loca_at(loca, fmt, i + 1) ==> wf_glyph(glyph_of(glyf, loca, fmt, i), ng)
}

// ---------------------------------------------------------------------
// Composite glyphs: the component graph, and what maxp promises
// ---------------------------------------------------------------------
/// What drawing a glyph takes once its components are expanded.
pub struct Info {
    /// Points, summed over everything the glyph is made of.
    pub points: int,
    /// Contours, likewise.
    pub contours: int,
    /// Component records visited, at every level.
    pub comps: int,
    /// Levels of nesting: 0 for a simple or empty glyph, one more than its
    /// deepest component for a composite.
    pub depth: int,
    /// Components the glyph itself lists.
    pub elems: int,
}

pub open spec fn info_zero() -> Info {
    Info { points: 0, contours: 0, comps: 0, depth: 0, elems: 0 }
}

/// How many levels of components `glyph_fits` follows: more than a font
/// of at most 65535 glyphs can nest without a glyph being a component of
/// itself, so only a cycle runs out of them. (OTS has no limit either.)
pub const MAX_COMPONENT_DEPTH: usize = 0xFFFF;

/// The totals for glyph `gid`, if they can be worked out with at most
/// `fuel` levels of nesting below it. `None` if a component names a glyph
/// that does not exist, the nesting is deeper than `fuel` (in particular
/// if a glyph is, directly or not, a component of itself), or a total
/// passes 0xFFFF.
pub open spec fn glyph_info(
    glyf: Seq<u8>,
    loca: Seq<u8>,
    fmt: int,
    ng: int,
    gid: int,
    fuel: nat,
) -> Option<Info>
    decreases fuel, 0nat,
{
    let g = glyph_of(glyf, loca, fmt, gid);
    if g.len() < 10 {
        Some(info_zero())
    } else if i16_at(g, 0) >= 0 {
        Some(
            Info {
                points: if i16_at(g, 0) >= 1 && 10 + 2 * i16_at(g, 0) <= g.len() {
                    end_pt(g, i16_at(g, 0) - 1) + 1
                } else {
                    0
                },
                contours: i16_at(g, 0),
                comps: 0,
                depth: 0,
                elems: 0,
            },
        )
    } else if fuel == 0 {
        None
    } else {
        comps_info(glyf, loca, fmt, ng, g, 10, (fuel - 1) as nat, info_zero())
    }
}

/// Adds the components of the composite glyph `g` from position `p` on to
/// the totals in `acc`.
pub open spec fn comps_info(
    glyf: Seq<u8>,
    loca: Seq<u8>,
    fmt: int,
    ng: int,
    g: Seq<u8>,
    p: int,
    fuel: nat,
    acc: Info,
) -> Option<Info>
    decreases fuel, (if p <= g.len() {
        1 + g.len() - p
    } else {
        0
    }) as nat,
{
    if p < 0 || p + 4 > g.len() || u16_at(g, p + 2) >= ng {
        None
    } else {
        match glyph_info(glyf, loca, fmt, ng, u16_at(g, p + 2), fuel) {
            None => None,
            Some(c) => {
                let acc2 = Info {
                    points: acc.points + c.points,
                    contours: acc.contours + c.contours,
                    comps: acc.comps + c.comps + 1,
                    depth: if acc.depth > c.depth + 1 {
                        acc.depth
                    } else {
                        c.depth + 1
                    },
                    elems: acc.elems + 1,
                };
                let q = p + 4 + comp_extra(g[p + 1]);
                if acc2.points > 0xFFFF || acc2.contours > 0xFFFF || acc2.comps > 0xFFFF {
                    None
                } else if g[p + 1] & 0x20 != 0 {
                    if q > g.len() {
                        None
                    } else {
                        comps_info(glyf, loca, fmt, ng, g, q, fuel, acc2)
                    }
                } else {
                    Some(acc2)
                }
            },
        }
    }
}

/// The length of the instructions after the component list at `p`.
pub open spec fn comp_ilen(g: Seq<u8>, p: int) -> int
    decreases g.len() - p,
{
    if p < 0 || p + 4 > g.len() {
        0
    } else {
        let q = p + 4 + comp_extra(g[p + 1]);
        if q > g.len() {
            0
        } else if g[p + 1] & 0x20 != 0 {
            comp_ilen(g, q)
        } else if g[p] & 0x01 != 0 && q + 2 <= g.len() {
            u16_at(g, q)
        } else {
            0
        }
    }
}

/// The length of a glyph's instructions.
pub open spec fn glyph_ilen(g: Seq<u8>) -> int {
    if i16_at(g, 0) >= 1 {
        if 12 + 2 * i16_at(g, 0) <= g.len() {
            u16_at(g, 10 + 2 * i16_at(g, 0))
        } else {
            0
        }
    } else {
        comp_ilen(g, 10)
    }
}

/// Glyph `i` stays within what `maxp` promises a rasterizer: its points,
/// contours and instructions if it is simple; if it is composite, its
/// expanded points and contours, its number of components, how deep they
/// nest, and its instructions. For a composite this also says its
/// component graph is finite: no glyph is a component of itself (a cycle
/// would need more than [`MAX_COMPONENT_DEPTH`] levels).
pub open spec fn glyph_fits(
    glyf: Seq<u8>,
    loca: Seq<u8>,
    fmt: int,
    ng: int,
    maxp: Seq<u8>,
    i: int,
) -> bool {
    let g = glyph_of(glyf, loca, fmt, i);
    g.len() < 10 || {
        &&& glyph_ilen(g) <= u16_at(maxp, 26)
        &&& match glyph_info(glyf, loca, fmt, ng, i, MAX_COMPONENT_DEPTH as nat) {
            Some(x) => if i16_at(g, 0) >= 0 {
                x.points <= u16_at(maxp, 6) && x.contours <= u16_at(maxp, 8)
            } else {
                &&& x.points <= u16_at(maxp, 10)
                &&& x.contours <= u16_at(maxp, 12)
                &&& x.elems <= u16_at(maxp, 28)
                &&& x.depth <= u16_at(maxp, 30)
            },
            None => false,
        }
    }
}

/// Every glyph stays within what `maxp` promises ([`glyph_fits`]).
pub open spec fn wf_glyf_limits(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, ng: int, maxp: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < ng ==> #[trigger] glyph_fits(glyf, loca, fmt, ng, maxp, i)
}

// ---------------------------------------------------------------------
// cmap
// ---------------------------------------------------------------------
/// A format 0 subtable at `o`: 256 glyph ids, each below `ng`.
pub open spec fn wf_cmap0(t: Seq<u8>, o: int, ng: int) -> bool {
    &&& o + 262 <= t.len()
    &&& u16_at(t, o + 2) == 262
    &&& forall|c: int| 0 <= c < 256 ==> (#[trigger] t[o + 6 + c]) < ng
}

/// Format 4 arrays, for a subtable at `o` with `sc` segments.
pub open spec fn c4_end(t: Seq<u8>, o: int, k: int) -> int {
    u16_at(t, o + 14 + 2 * k)
}

pub open spec fn c4_start(t: Seq<u8>, o: int, sc: int, k: int) -> int {
    u16_at(t, o + 16 + 2 * sc + 2 * k)
}

pub open spec fn c4_delta(t: Seq<u8>, o: int, sc: int, k: int) -> int {
    u16_at(t, o + 16 + 4 * sc + 2 * k)
}

pub open spec fn c4_ro_pos(o: int, sc: int, k: int) -> int {
    o + 16 + 6 * sc + 2 * k
}

pub open spec fn c4_ro(t: Seq<u8>, o: int, sc: int, k: int) -> int {
    u16_at(t, c4_ro_pos(o, sc, k))
}

/// Character `c` of segment `k` maps to a glyph below `ng`, and if the
/// segment goes through the glyph id array, the entry it reads lies inside
/// the subtable (which ends at `end`).
pub open spec fn c4_char_ok(t: Seq<u8>, o: int, sc: int, k: int, c: int, end: int, ng: int) -> bool {
    if c4_ro(t, o, sc, k) == 0 {
        (c + c4_delta(t, o, sc, k)) % 65536 < ng
    } else {
        let a = c4_ro_pos(o, sc, k) + c4_ro(t, o, sc, k) + 2 * (c - c4_start(t, o, sc, k));
        &&& a + 2 <= end
        &&& (u16_at(t, a) != 0 ==> (u16_at(t, a) + c4_delta(t, o, sc, k)) % 65536 < ng)
    }
}

pub open spec fn c4_seg_ok(t: Seq<u8>, o: int, sc: int, k: int, end: int, ng: int) -> bool {
    &&& c4_start(t, o, sc, k) <= c4_end(t, o, k)
    &&& (k > 0 ==> c4_end(t, o, k - 1) < c4_start(t, o, sc, k))
    &&& c4_ro(t, o, sc, k) % 2 == 0
    &&& forall|c: int|
        c4_start(t, o, sc, k) <= c <= c4_end(t, o, k) ==> #[trigger] c4_char_ok(
            t,
            o,
            sc,
            k,
            c,
            end,
            ng,
        )
}

/// A format 4 subtable at `o`: the segments are in order and do not
/// overlap, the last ends at 0xFFFF, and every character of every segment
/// maps to a glyph below `ng` without reading outside the subtable.
pub open spec fn wf_cmap4(t: Seq<u8>, o: int, ng: int) -> bool {
    let len = u16_at(t, o + 2);
    let sc = u16_at(t, o + 6) / 2;
    &&& o + 16 <= t.len()
    &&& o + len <= t.len()
    &&& u16_at(t, o + 6) % 2 == 0
    &&& sc >= 1
    &&& 16 + 8 * sc <= len
    &&& c4_end(t, o, sc - 1) == 0xFFFF
    &&& forall|k: int| 0 <= k < sc ==> #[trigger] c4_seg_ok(t, o, sc, k, o + len, ng)
}

/// Group `k` of a format 12 (`many` false) or 13 (`many` true) subtable.
pub open spec fn c12_group_ok(t: Seq<u8>, o: int, k: int, many: bool, ng: int) -> bool {
    let g = o + 16 + 12 * k;
    &&& u32_at(t, g) <= u32_at(t, g + 4)
    &&& u32_at(t, g + 4) <= 0x10FFFF
    &&& (k > 0 ==> u32_at(t, g - 8) < u32_at(t, g))
    &&& if many {
        u32_at(t, g + 8) < ng
    } else {
        u32_at(t, g + 8) + (u32_at(t, g + 4) - u32_at(t, g)) < ng
    }
}

/// A format 12 or 13 subtable at `o`: the groups are in order, do not
/// overlap, stay inside Unicode, and map only to glyphs below `ng`.
pub open spec fn wf_cmap12(t: Seq<u8>, o: int, many: bool, ng: int) -> bool {
    let n = u32_at(t, o + 12);
    &&& o + 16 <= t.len()
    &&& u32_at(t, o + 4) == 16 + 12 * n
    &&& o + 16 + 12 * n <= t.len()
    &&& forall|k: int| 0 <= k < n ==> #[trigger] c12_group_ok(t, o, k, many, ng)
}

/// A default UVS table at `d`, inside a subtable ending at `end`: ranges
/// of Unicode values in order, not overlapping.
pub open spec fn wf_duvs(t: Seq<u8>, d: int, end: int) -> bool {
    let n = u32_at(t, d);
    &&& d + 4 <= end
    &&& n >= 1
    &&& d + 4 + 4 * n <= end
    &&& forall|k: int| 0 <= k < n ==> #[trigger] duvs_ok(t, d, k)
}

pub open spec fn duvs_ok(t: Seq<u8>, d: int, k: int) -> bool {
    let r = d + 4 + 4 * k;
    &&& u24_at(t, r) >= 1
    &&& u24_at(t, r) + t[r + 3] <= 0x10FFFF
    &&& (k > 0 ==> u24_at(t, r - 4) + t[r - 1] < u24_at(t, r))
}

/// A non-default UVS table at `d`: Unicode values in order, each mapped to
/// a glyph below `ng`.
pub open spec fn wf_nduvs(t: Seq<u8>, d: int, end: int, ng: int) -> bool {
    let n = u32_at(t, d);
    &&& d + 4 <= end
    &&& n >= 1
    &&& d + 4 + 5 * n <= end
    &&& forall|k: int| 0 <= k < n ==> #[trigger] nduvs_ok(t, d, k, ng)
}

pub open spec fn nduvs_ok(t: Seq<u8>, d: int, k: int, ng: int) -> bool {
    let r = d + 4 + 5 * k;
    &&& 1 <= u24_at(t, r) <= 0x10FFFF
    &&& (k > 0 ==> u24_at(t, r - 5) < u24_at(t, r))
    &&& 1 <= u16_at(t, r + 3) < ng
}

/// The code points that are variation selectors: Mongolian, the 16 of the
/// BMP, and the 240 supplementary ones. There are 259.
pub open spec fn vs_ok(v: int) -> bool {
    ||| 0x180B <= v <= 0x180D
    ||| 0xFE00 <= v <= 0xFE0F
    ||| 0xE0100 <= v <= 0xE01EF
}

/// Offset of record `k`'s default UVS table (0 for none), and one past its
/// last byte, both from the start of the subtable at `o`.
pub open spec fn c14_doff(t: Seq<u8>, o: int, k: int) -> int {
    u32_at(t, o + 10 + 11 * k + 3)
}

pub open spec fn c14_dend(t: Seq<u8>, o: int, k: int) -> int {
    c14_doff(t, o, k) + 4 + 4 * u32_at(t, o + c14_doff(t, o, k))
}

/// The same for record `k`'s non-default UVS table.
pub open spec fn c14_noff(t: Seq<u8>, o: int, k: int) -> int {
    u32_at(t, o + 10 + 11 * k + 7)
}

pub open spec fn c14_nend(t: Seq<u8>, o: int, k: int) -> int {
    c14_noff(t, o, k) + 4 + 5 * u32_at(t, o + c14_noff(t, o, k))
}

/// The byte ranges `[a0, a1)` and `[b0, b1)` do not overlap.
pub open spec fn apart(a0: int, a1: int, b0: int, b1: int) -> bool {
    a1 <= b0 || b1 <= a0
}

/// The UVS tables of records `i` and `j` do not overlap: two records may
/// name the very same default table, or the very same non-default table,
/// and every other pair of tables occupies separate bytes.
pub open spec fn c14_pair_ok(t: Seq<u8>, o: int, i: int, j: int) -> bool {
    let di = c14_doff(t, o, i);
    let dj = c14_doff(t, o, j);
    let ni = c14_noff(t, o, i);
    let nj = c14_noff(t, o, j);
    &&& (di != 0 && dj != 0 && di != dj ==> apart(di, c14_dend(t, o, i), dj, c14_dend(t, o, j)))
    &&& (ni != 0 && nj != 0 && ni != nj ==> apart(ni, c14_nend(t, o, i), nj, c14_nend(t, o, j)))
    &&& (di != 0 && nj != 0 ==> apart(di, c14_dend(t, o, i), nj, c14_nend(t, o, j)))
}

/// Variation selector record `k` of a format 14 subtable at `o`: a real
/// variation selector, after the one before, with at least one UVS table.
pub open spec fn c14_rec_ok(t: Seq<u8>, o: int, k: int, hdr: int, end: int, ng: int) -> bool {
    let r = o + 10 + 11 * k;
    &&& vs_ok(u24_at(t, r))
    &&& (k > 0 ==> u24_at(t, r - 11) < u24_at(t, r))
    &&& (u32_at(t, r + 3) != 0 || u32_at(t, r + 7) != 0)
    &&& (u32_at(t, r + 3) != 0 ==> u32_at(t, r + 3) >= hdr && wf_duvs(t, o + u32_at(t, r + 3), end))
    &&& (u32_at(t, r + 7) != 0 ==> u32_at(t, r + 7) >= hdr && wf_nduvs(
        t,
        o + u32_at(t, r + 7),
        end,
        ng,
    ))
}

/// A format 14 (Unicode variation sequences) subtable at `o`.
pub open spec fn wf_cmap14(t: Seq<u8>, o: int, ng: int) -> bool {
    let len = u32_at(t, o + 2);
    let n = u32_at(t, o + 6);
    &&& o + 10 <= t.len()
    &&& o + len <= t.len()
    &&& 1 <= n <= 259
    &&& 10 + 11 * n <= len
    &&& forall|k: int| 0 <= k < n ==> #[trigger] c14_rec_ok(t, o, k, 10 + 11 * n, o + len, ng)
    &&& forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger] c14_pair_ok(t, o, i, j)
}

/// The subtable at `o` has one of the formats 0, 4, 12, 13, 14 and is
/// well formed.
pub open spec fn wf_cmap_sub(t: Seq<u8>, o: int, ng: int) -> bool {
    &&& o + 2 <= t.len()
    &&& if u16_at(t, o) == 0 {
        wf_cmap0(t, o, ng)
    } else if u16_at(t, o) == 4 {
        wf_cmap4(t, o, ng)
    } else if u16_at(t, o) == 12 {
        wf_cmap12(t, o, false, ng)
    } else if u16_at(t, o) == 13 {
        wf_cmap12(t, o, true, ng)
    } else if u16_at(t, o) == 14 {
        wf_cmap14(t, o, ng)
    } else {
        false
    }
}

/// The encodings a sanitized font may carry, and the subtable format each
/// may use (the ones OTS keeps): Unicode 0, 1 and 3 with format 4, Unicode
/// 3 and 4 with format 12, Unicode 5 with format 14, Macintosh Roman with
/// format 0, Windows Symbol and Unicode BMP with format 4, and Windows
/// Unicode full with format 12 or 13. `pe` is the platform and encoding
/// ids as one number, platform in the high 16 bits.
pub open spec fn cmap_use_ok(pe: int, fmt: int) -> bool {
    ||| ((pe == 0x0000_0000 || pe == 0x0000_0001 || pe == 0x0000_0003) && fmt == 4)
    ||| ((pe == 0x0000_0003 || pe == 0x0000_0004) && fmt == 12)
    ||| (pe == 0x0000_0005 && fmt == 14)
    ||| (pe == 0x0001_0000 && fmt == 0)
    ||| ((pe == 0x0003_0000 || pe == 0x0003_0001) && fmt == 4)
    ||| (pe == 0x0003_000A && (fmt == 12 || fmt == 13))
}

/// Encoding record `i`: (platform, encoding) sorts after the record
/// before, the offset leads to a well-formed subtable past the header, and
/// the subtable's format is one its encoding may use.
pub open spec fn cmap_rec_ok(t: Seq<u8>, i: int, ng: int) -> bool {
    let r = 4 + 8 * i;
    &&& (i > 0 ==> u32_at(t, r - 8) < u32_at(t, r))
    &&& u32_at(t, r + 4) >= 4 + 8 * u16_at(t, 2)
    &&& wf_cmap_sub(t, u32_at(t, r + 4), ng)
    &&& cmap_use_ok(u32_at(t, r), u16_at(t, u32_at(t, r + 4)))
}

pub open spec fn wf_cmap(t: Seq<u8>, ng: int) -> bool {
    &&& t.len() >= 4
    &&& u16_at(t, 0) == 0
    &&& u16_at(t, 2) >= 1
    &&& 4 + 8 * u16_at(t, 2) <= t.len()
    &&& forall|i: int| 0 <= i < u16_at(t, 2) ==> #[trigger] cmap_rec_ok(t, i, ng)
}

// ---------------------------------------------------------------------
// name, post, and the small TrueType tables
// ---------------------------------------------------------------------
/// The (length, offset) pair at `r` describes a string inside the storage
/// area, which starts at `st`.
pub open spec fn name_str_ok(t: Seq<u8>, r: int, st: int) -> bool {
    st + u16_at(t, r + 2) + u16_at(t, r) <= t.len()
}

pub open spec fn wf_name(t: Seq<u8>) -> bool {
    let n = u16_at(t, 2);
    let st = u16_at(t, 4);
    &&& t.len() >= 6
    &&& u16_at(t, 0) <= 1
    &&& 6 + 12 * n <= t.len()
    &&& st <= t.len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] name_str_ok(t, 6 + 12 * i + 8, st)
    &&& if u16_at(t, 0) == 0 {
        st >= 6 + 12 * n
    } else {
        let l = 6 + 12 * n;
        &&& l + 2 <= t.len()
        &&& l + 2 + 4 * u16_at(t, l) <= st
        &&& forall|i: int| 0 <= i < u16_at(t, l) ==> #[trigger] name_str_ok(t, l + 2 + 4 * i, st)
    }
}

/// The number of Pascal strings that fill `t` from `p` to its end exactly.
pub open spec fn pstrings(t: Seq<u8>, p: int) -> Option<int>
    decreases t.len() - p,
{
    if p < 0 || p > t.len() {
        None
    } else if p == t.len() {
        Some(0)
    } else if p + 1 + t[p] > t.len() {
        None
    } else {
        match pstrings(t, p + 1 + t[p]) {
            Some(k) => Some(k + 1),
            None => None,
        }
    }
}

/// Versions 1.0 and 3.0 are the 32-byte header alone. Version 2.0 adds one
/// name index per glyph and a run of Pascal strings that fills the rest of
/// the table, and every index names a standard name or one of the strings.
pub open spec fn wf_post(t: Seq<u8>, ng: int) -> bool {
    &&& t.len() >= 32
    &&& if u32_at(t, 0) == 0x0001_0000 || u32_at(t, 0) == 0x0003_0000 {
        t.len() == 32
    } else {
        &&& u32_at(t, 0) == 0x0002_0000
        &&& t.len() >= 34
        &&& u16_at(t, 32) == ng
        &&& 34 + 2 * ng <= t.len()
        &&& match pstrings(t, 34 + 2 * ng) {
            Some(k) => forall|i: int| 0 <= i < ng ==> #[trigger] u16_at(t, 34 + 2 * i) < 258 + k,
            None => false,
        }
    }
}

/// `cvt `: a whole number of 16-bit values.
pub open spec fn wf_cvt(t: Seq<u8>) -> bool {
    t.len() % 2 == 0
}

/// `gasp`: version 0 or 1, ranges in increasing order of ppem, nothing
/// after them.
pub open spec fn wf_gasp(t: Seq<u8>) -> bool {
    &&& t.len() >= 4
    &&& u16_at(t, 0) <= 1
    &&& t.len() == 4 + 4 * u16_at(t, 2)
    &&& forall|i: int|
        0 <= i < u16_at(t, 2) - 1 ==> #[trigger] u16_at(t, 4 + 4 * i) < u16_at(t, 4 + 4 * (i + 1))
}

/// `vhea`: as `hhea`, for vertical layout.
pub open spec fn wf_vhea(t: Seq<u8>, ng: int) -> bool {
    &&& t.len() == 36
    &&& (u32_at(t, 0) == 0x0001_0000 || u32_at(t, 0) == 0x0001_1000)
    &&& u16_at(t, 32) == 0
    &&& 1 <= u16_at(t, 34) <= ng
}

/// Pair `k` of the format 0 `kern` subtable at `p`: both glyphs exist, and
/// the pair sorts after the one before it.
pub open spec fn kern_pair_ok(t: Seq<u8>, p: int, k: int, ng: int) -> bool {
    let r = p + 14 + 6 * k;
    &&& u16_at(t, r) < ng
    &&& u16_at(t, r + 2) < ng
    &&& (k > 0 ==> u32_at(t, r - 6) < u32_at(t, r))
}

/// `n` format 0 subtables from `p` fill the rest of the table exactly.
pub open spec fn kern_subs(t: Seq<u8>, p: int, n: int, ng: int) -> bool
    decreases n,
{
    if n <= 0 {
        p == t.len()
    } else {
        let len = u16_at(t, p + 2);
        let np = u16_at(t, p + 6);
        &&& 0 <= p
        &&& p + 14 <= t.len()
        &&& u16_at(t, p) == 0
        &&& t[p + 4] == 0
        &&& len == 14 + 6 * np
        &&& p + len <= t.len()
        &&& (forall|k: int| 0 <= k < np ==> #[trigger] kern_pair_ok(t, p, k, ng))
        &&& kern_subs(t, p + len, n - 1, ng)
    }
}

/// `kern`, version 0, made only of format 0 subtables (sorted lists of
/// glyph pairs).
pub open spec fn wf_kern(t: Seq<u8>, ng: int) -> bool {
    &&& t.len() >= 4
    &&& u16_at(t, 0) == 0
    &&& kern_subs(t, 4, u16_at(t, 2), ng)
}

// ---------------------------------------------------------------------
// The whole font
// ---------------------------------------------------------------------
pub const T_CFF: u32 = 0x4346_4620;

pub const T_CMAP: u32 = 0x636D_6170;

pub const T_CVT: u32 = 0x6376_7420;

pub const T_FPGM: u32 = 0x6670_676D;

pub const T_GASP: u32 = 0x6761_7370;

pub const T_GLYF: u32 = 0x676C_7966;

pub const T_HEAD: u32 = 0x6865_6164;

pub const T_HHEA: u32 = 0x6868_6561;

pub const T_HMTX: u32 = 0x686D_7478;

pub const T_KERN: u32 = 0x6B65_726E;

pub const T_GDEF: u32 = 0x4744_4546;

pub const T_GPOS: u32 = 0x4750_4F53;

pub const T_GSUB: u32 = 0x4753_5542;

pub const T_VHEA: u32 = 0x7668_6561;

pub const T_VMTX: u32 = 0x766D_7478;

pub const T_LOCA: u32 = 0x6C6F_6361;

pub const T_MAXP: u32 = 0x6D61_7870;

pub const T_NAME: u32 = 0x6E61_6D65;

pub const T_OS2: u32 = 0x4F53_2F32;

pub const T_POST: u32 = 0x706F_7374;

pub const T_PREP: u32 = 0x7072_6570;

/// The tables a sanitized font may contain. `fpgm` and `prep` hold
/// TrueType bytecode, which this specification does not constrain.
pub open spec fn known_tag(t: int) -> bool {
    t == T_CFF || t == T_CMAP || t == T_CVT || t == T_FPGM || t == T_GASP || t == T_GLYF || t == T_HEAD || t
        == T_HHEA || t == T_HMTX || t == T_LOCA || t == T_MAXP || t == T_NAME || t == T_OS2 || t
        == T_POST || t == T_PREP || t == T_KERN || t == T_VHEA || t == T_VMTX || t == T_GDEF || t == T_GPOS
        || t == T_GSUB
}

/// The tables every font has.
pub open spec fn has_required(s: Seq<u8>) -> bool {
    &&& has_table(s, T_HEAD as int)
    &&& has_table(s, T_MAXP as int)
    &&& has_table(s, T_HHEA as int)
    &&& has_table(s, T_HMTX as int)
    &&& has_table(s, T_CMAP as int)
    &&& has_table(s, T_NAME as int)
    &&& has_table(s, T_POST as int)
    &&& has_table(s, T_OS2 as int)
}

/// The tables every font has are each well formed and agree with each
/// other.
pub open spec fn wf_core(s: Seq<u8>) -> bool {
    let maxp = table(s, T_MAXP as int);
    let hhea = table(s, T_HHEA as int);
    let ng = num_glyphs(maxp);
    &&& wf_head(table(s, T_HEAD as int))
    &&& wf_maxp(maxp, has_table(s, T_GLYF as int))
    &&& wf_hhea(hhea, ng)
    &&& wf_hmtx(table(s, T_HMTX as int), ng, num_hmetrics(hhea))
    &&& wf_cmap(table(s, T_CMAP as int), ng)
    &&& wf_name(table(s, T_NAME as int))
    &&& wf_post(table(s, T_POST as int), ng)
    &&& wf_os2(table(s, T_OS2 as int))
}

/// The outlines are either TrueType (`glyf` and `loca`, in a file whose
/// version is 0x00010000) or CFF (in a file whose version is `OTTO`),
/// never both and never neither, and they are well formed.
pub open spec fn wf_outlines(s: Seq<u8>) -> bool {
    let head = table(s, T_HEAD as int);
    let maxp = table(s, T_MAXP as int);
    let ng = num_glyphs(maxp);
    if has_table(s, T_GLYF as int) {
        &&& u32_at(s, 0) == TAG_TRUETYPE
        &&& !has_table(s, T_CFF as int)
        &&& has_table(s, T_LOCA as int)
        &&& wf_loca(
            table(s, T_LOCA as int),
            loc_format(head),
            ng,
            table(s, T_GLYF as int).len() as int,
        )
        &&& wf_glyf(table(s, T_GLYF as int), table(s, T_LOCA as int), loc_format(head), ng)
        &&& wf_glyf_limits(
            table(s, T_GLYF as int),
            table(s, T_LOCA as int),
            loc_format(head),
            ng,
            maxp,
        )
    } else {
        &&& u32_at(s, 0) == TAG_OTTO
        &&& !has_table(s, T_LOCA as int)
        &&& has_table(s, T_CFF as int)
        &&& crate::spec_cff::wf_cff(table(s, T_CFF as int), ng)
    }
}

/// How many mark glyph sets a lookup may choose from: those `GDEF`
/// defines. A font without `GDEF` puts no limit on the 16-bit index.
pub open spec fn mark_set_limit(s: Seq<u8>) -> int {
    if has_table(s, T_GDEF as int) {
        crate::spec_layout::gdef_mark_sets(table(s, T_GDEF as int))
    } else {
        0x10000
    }
}

/// The optional tables that are present are well formed.
pub open spec fn wf_extras(s: Seq<u8>) -> bool {
    let ng = num_glyphs(table(s, T_MAXP as int));
    &&& (has_table(s, T_GDEF as int) ==> crate::spec_layout::wf_gdef(table(s, T_GDEF as int), ng))
    &&& (has_table(s, T_GSUB as int) ==> crate::spec_layout::wf_layout(
        table(s, T_GSUB as int),
        false,
        ng,
        mark_set_limit(s),
    ))
    &&& (has_table(s, T_GPOS as int) ==> crate::spec_layout::wf_layout(
        table(s, T_GPOS as int),
        true,
        ng,
        mark_set_limit(s),
    ))
    &&& (has_table(s, T_CVT as int) ==> wf_cvt(table(s, T_CVT as int)))
    &&& (has_table(s, T_GASP as int) ==> wf_gasp(table(s, T_GASP as int)))
    &&& (has_table(s, T_KERN as int) ==> wf_kern(table(s, T_KERN as int), ng))
    &&& has_table(s, T_VHEA as int) == has_table(s, T_VMTX as int)
    &&& (has_table(s, T_VHEA as int) ==> {
        &&& wf_vhea(table(s, T_VHEA as int), ng)
        &&& wf_hmtx(table(s, T_VMTX as int), ng, num_hmetrics(table(s, T_VHEA as int)))
    })
}

/// The tables are each well formed and agree with each other.
pub open spec fn wf_tables(s: Seq<u8>) -> bool {
    &&& wf_core(s)
    &&& wf_outlines(s)
    &&& wf_extras(s)
}

/// A well-formed font: the directory is well formed and tiles the file,
/// the whole-file checksum is the one `head.checkSumAdjustment` exists to
/// produce, only known tables are present, the required ones are all
/// there, and each is well formed and consistent with the others.
///
/// On the checksum: the specification asks that `checkSumAdjustment` be
/// 0xB1B0AFBA minus the sum of the file's words with that field taken as
/// zero. The field is itself one of the words, so that is the same as the
/// words of the file summing to 0xB1B0AFBA.
pub open spec fn wf_font(s: Seq<u8>) -> bool {
    &&& wf_directory(s)
    &&& words_sum(s, 0, s.len() as int / 4) == 0xB1B0_AFBA
    &&& forall|i: int| 0 <= i < num_tables(s) ==> known_tag(#[trigger] rec_tag(s, i))
    &&& has_required(s)
    &&& wf_tables(s)
}

} // verus!
