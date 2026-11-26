//! The trusted specification of what the sanitizer keeps: what it means
//! for an output font to draw the same as the tables it was made from
//! (`draws_same`), and which inputs count as valid fonts
//! (`valid_tables`).
//!
//! Both are about the *table set* of the input: the known tables a
//! container reader found, as (tag, bytes) pairs in the order it found
//! them, the first of each tag counting. For a plain OpenType file and a
//! TrueType Collection, `sfnt_tables` says exactly what that set is. For
//! WOFF and WOFF2 it is what the decoders produce, which is not specified
//! here.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The tables of an input font: (tag, bytes) in the order they were read.
pub type Tables = Seq<(u32, Seq<u8>)>;

// ---------------------------------------------------------------------
// Looking tables up
// ---------------------------------------------------------------------
/// The index of the first table at or after `i` with tag `t`, or the
/// number of tables if there is none.
pub open spec fn find_in(ts: Tables, t: int, i: int) -> int
    decreases ts.len() - i,
{
    if i < 0 || i >= ts.len() {
        ts.len() as int
    } else if ts[i].0 == t {
        i
    } else {
        find_in(ts, t, i + 1)
    }
}

pub open spec fn in_has(ts: Tables, t: int) -> bool {
    find_in(ts, t, 0) < ts.len()
}

/// The bytes of the input's table `t` (meaningful when `in_has`).
pub open spec fn in_table(ts: Tables, t: int) -> Seq<u8> {
    ts[find_in(ts, t, 0)].1
}

// ---------------------------------------------------------------------
// The tables of a plain OpenType file
// ---------------------------------------------------------------------
/// The known tables of records `0..i` of the sfnt directory at `base`,
/// or `None` if one of them lies outside the file or a known tag comes
/// twice. Unknown tables are skipped without looking at them.
pub open spec fn sfnt_recs(s: Seq<u8>, base: int, i: int) -> Option<Tables>
    decreases i,
{
    if i <= 0 {
        Some(Seq::empty())
    } else {
        match sfnt_recs(s, base, i - 1) {
            None => None,
            Some(acc) => {
                let r = base + 12 + 16 * (i - 1);
                let t = u32_at(s, r);
                let off = u32_at(s, r + 8);
                let len = u32_at(s, r + 12);
                if !known_tag(t) {
                    Some(acc)
                } else if off + len > s.len() || in_has(acc, t) {
                    None
                } else {
                    Some(acc.push((t as u32, s.subrange(off, off + len))))
                }
            },
        }
    }
}

/// The table set of the sfnt font whose directory starts at `base`: its
/// version is TrueType, `OTTO` or Apple's `true`, the directory lies
/// inside the file, which is at most 1 GiB, and then as `sfnt_recs`.
pub open spec fn sfnt_tables(s: Seq<u8>, base: int) -> Option<Tables> {
    let v = u32_at(s, base);
    if s.len() > 0x4000_0000 || base < 0 || base > s.len() || s.len() - base < 12 {
        None
    } else if v != TAG_TRUETYPE && v != TAG_OTTO && v != 0x7472_7565 {
        None
    } else if base + 12 + 16 * u16_at(s, base + 4) > s.len() {
        None
    } else {
        sfnt_recs(s, base, u16_at(s, base + 4))
    }
}

/// The input is a plain sfnt file, not WOFF, WOFF2 or a collection.
pub open spec fn is_plain_sfnt(s: Seq<u8>) -> bool {
    s.len() >= 4 && u32_at(s, 0) != 0x774F_4646 && u32_at(s, 0) != 0x774F_4632 && u32_at(s, 0)
        != 0x7474_6366
}

/// The table set of font `index` of a TrueType Collection.
pub open spec fn ttc_tables(s: Seq<u8>, index: int) -> Option<Tables> {
    if s.len() < 12 || s.len() > 0x4000_0000 || index >= u32_at(s, 8) || 12 + 4 * u32_at(s, 8)
        > s.len() {
        None
    } else {
        sfnt_tables(s, u32_at(s, 12 + 4 * index))
    }
}

pub open spec fn is_ttc(s: Seq<u8>) -> bool {
    s.len() >= 4 && u32_at(s, 0) == 0x7474_6366
}

/// The table set of font `index` of the input, for the containers this
/// specification describes: a plain sfnt file (`index` ignored) or a
/// TrueType Collection. `None` for WOFF and WOFF2, whose decoding is not
/// specified here, and for files the reader refuses.
pub open spec fn input_tables(s: Seq<u8>, index: int) -> Option<Tables> {
    if is_ttc(s) {
        ttc_tables(s, index)
    } else if is_plain_sfnt(s) {
        sfnt_tables(s, 0)
    } else {
        None
    }
}

// ---------------------------------------------------------------------
// Draws the same
// ---------------------------------------------------------------------
/// `o` is the first `o.len()` bytes of `i`.
pub open spec fn prefix_of(o: Seq<u8>, i: Seq<u8>) -> bool {
    o.len() <= i.len() && o == i.subrange(0, o.len() as int)
}

/// `head`: the output is the input's first 54 bytes, except for
/// `checkSumAdjustment` (8..12, recomputed) and `indexToLocFormat`
/// (50..52, which says how the rewritten `loca` is stored). So
/// `unitsPerEm`, the flags, the bounding box, `macStyle` and
/// `lowestRecPPEM` are the input's.
pub open spec fn same_head(i: Seq<u8>, o: Seq<u8>) -> bool {
    &&& i.len() >= 54
    &&& o.len() == 54
    &&& forall|j: int|
        0 <= j < 54 && !(8 <= j < 12) && !(50 <= j < 52) ==> #[trigger] o[j] == i[j]
}

pub open spec fn clamp_zones(z: int) -> int {
    if z < 1 {
        1
    } else if z > 2 {
        2
    } else {
        z
    }
}

/// `maxp`: the same number of glyphs. For TrueType outlines, also the
/// same limits a hinting interpreter allocates by (`maxTwilightPoints`,
/// `maxStorage`, `maxFunctionDefs`, `maxInstructionDefs`,
/// `maxStackElements`), and `maxZones` the input's, clamped to 1..=2.
/// The outline limits may differ: the sanitizer recomputes them.
pub open spec fn same_maxp(i: Seq<u8>, o: Seq<u8>, truetype: bool) -> bool {
    &&& i.len() >= 6
    &&& o.len() >= 6
    &&& u16_at(o, 4) == u16_at(i, 4)
    &&& truetype ==> {
        &&& i.len() >= 32
        &&& o.len() >= 32
        &&& forall|j: int| 16 <= j < 26 ==> #[trigger] o[j] == i[j]
        &&& u16_at(o, 14) == clamp_zones(u16_at(i, 14))
    }
}

/// `OS/2`: a prefix of the input, except that the version (0..2) may be
/// lowered to 0 when the input is too short for its own version.
pub open spec fn same_os2(i: Seq<u8>, o: Seq<u8>) -> bool {
    &&& 2 <= o.len() <= i.len()
    &&& forall|j: int| 2 <= j < o.len() ==> #[trigger] o[j] == i[j]
}

/// Glyph `g`'s outline: the bytes of its glyph description (contours or
/// components, and its instructions), cut at the end its own structure
/// gives, or empty for a glyph with no outline. `None` if `loca` or the
/// description is broken.
pub open spec fn outline(glyf: Seq<u8>, loca: Seq<u8>, fmt: int, g: int, ng: int) -> Option<Seq<u8>> {
    let w: int = if fmt == 0 {
        2
    } else {
        4
    };
    if fmt < 0 || fmt > 1 || g < 0 || loca.len() < (g + 2) * w {
        None
    } else {
        let a = loca_at(loca, fmt, g);
        let b = loca_at(loca, fmt, g + 1);
        if a > b || b > glyf.len() {
            None
        } else if a == b {
            Some(Seq::empty())
        } else {
            let r = glyf.subrange(a, b);
            if r.len() < 10 {
                None
            } else if u16_at(r, 0) == 0 {
                Some(Seq::empty())
            } else {
                match glyph_end(r, ng) {
                    Some(e) => if e <= r.len() {
                        Some(r.subrange(0, e))
                    } else {
                        None
                    },
                    None => None,
                }
            }
        }
    }
}

/// The outlines: TrueType in the output exactly when in the input, and
/// then every glyph's outline is the same; a `CFF ` table is the input's
/// byte for byte (charstrings, subroutines, hints, everything).
pub open spec fn same_outlines(ts: Tables, s: Seq<u8>, ng: int) -> bool {
    &&& has_table(s, T_GLYF as int) == in_has(ts, T_GLYF as int)
    &&& has_table(s, T_GLYF as int) ==> {
        &&& in_has(ts, T_LOCA as int)
        &&& forall|g: int|
            0 <= g < ng ==> #[trigger] outline(
                in_table(ts, T_GLYF as int),
                in_table(ts, T_LOCA as int),
                u16_at(in_table(ts, T_HEAD as int), 50),
                g,
                ng,
            ) == outline(
                table(s, T_GLYF as int),
                table(s, T_LOCA as int),
                u16_at(table(s, T_HEAD as int), 50),
                g,
                ng,
            )
    }
    &&& has_table(s, T_CFF as int) ==> in_has(ts, T_CFF as int) && table(s, T_CFF as int) == in_table(
        ts,
        T_CFF as int,
    )
}

/// An output table with tag `t`, if there is one, is the input's.
pub open spec fn kept_as_is(ts: Tables, s: Seq<u8>, t: int) -> bool {
    has_table(s, t) ==> in_has(ts, t) && table(s, t) == in_table(ts, t)
}

/// Vertical metrics: if kept, `vhea` and `vmtx` are prefixes of the
/// input's (so every vertical advance and top side bearing is the
/// input's), and they are kept whenever the input's are well formed.
pub open spec fn same_vertical(ts: Tables, s: Seq<u8>, ng: int) -> bool {
    let vh = in_table(ts, T_VHEA as int);
    let vm = in_table(ts, T_VMTX as int);
    let nvm = u16_at(vh, 34);
    &&& has_table(s, T_VHEA as int) ==> {
        &&& in_has(ts, T_VHEA as int)
        &&& in_has(ts, T_VMTX as int)
        &&& prefix_of(table(s, T_VHEA as int), vh)
        &&& prefix_of(table(s, T_VMTX as int), vm)
    }
    &&& (in_has(ts, T_VHEA as int) && in_has(ts, T_VMTX as int) && vh.len() >= 36 && wf_vhea(
        vh.subrange(0, 36),
        ng,
    ) && vm.len() >= 4 * nvm + 2 * (ng - nvm)) ==> has_table(s, T_VHEA as int)
}

/// Hinting and kerning: `fpgm`, `prep`, `cvt `, `gasp` and `kern` are
/// the input's when present; in a TrueType font the first four are
/// dropped only when empty or malformed, and `kern` in any font only when
/// malformed.
pub open spec fn same_hinting(ts: Tables, s: Seq<u8>, ng: int) -> bool {
    let tt = has_table(s, T_GLYF as int);
    &&& kept_as_is(ts, s, T_FPGM as int)
    &&& kept_as_is(ts, s, T_PREP as int)
    &&& kept_as_is(ts, s, T_CVT as int)
    &&& kept_as_is(ts, s, T_GASP as int)
    &&& kept_as_is(ts, s, T_KERN as int)
    &&& (tt && in_has(ts, T_FPGM as int) && in_table(ts, T_FPGM as int).len() > 0 ==> has_table(
        s,
        T_FPGM as int,
    ))
    &&& (tt && in_has(ts, T_PREP as int) && in_table(ts, T_PREP as int).len() > 0 ==> has_table(
        s,
        T_PREP as int,
    ))
    &&& (tt && in_has(ts, T_CVT as int) && in_table(ts, T_CVT as int).len() > 0 && wf_cvt(
        in_table(ts, T_CVT as int),
    ) ==> has_table(s, T_CVT as int))
    &&& (tt && in_has(ts, T_GASP as int) && wf_gasp(in_table(ts, T_GASP as int)) ==> has_table(
        s,
        T_GASP as int,
    ))
    &&& (in_has(ts, T_KERN as int) && wf_kern(in_table(ts, T_KERN as int), ng) ==> has_table(
        s,
        T_KERN as int,
    ))
}

/// The length of the `cmap` subtable at `o`, as its header gives it.
pub open spec fn sub_len(t: Seq<u8>, o: int) -> int {
    let f = u16_at(t, o);
    if f == 0 {
        262
    } else if f == 4 {
        u16_at(t, o + 2)
    } else if f == 12 || f == 13 {
        16 + 12 * u32_at(t, o + 12)
    } else {
        u32_at(t, o + 2)
    }
}

/// Where the repair of a format 4 subtable at `o` writes, if it applies:
/// (idDelta, idRangeOffset) of the last segment. It applies when the last
/// segment covers only 0xFFFF and its idRangeOffset is 0xFFFF, which
/// points outside any table shorter than 64 KiB.
pub open spec fn repair4_at(t: Seq<u8>, o: int) -> Option<(int, int)> {
    if o < 0 || o + 16 > t.len() || u16_at(t, o) != 4 {
        None
    } else {
        let sc = u16_at(t, o + 6) / 2;
        if sc < 1 || 16 + 8 * sc > t.len() - o {
            None
        } else {
            let k = sc - 1;
            let end = o + 14 + 2 * k;
            let start = o + 16 + 2 * sc + 2 * k;
            let delta = o + 16 + 4 * sc + 2 * k;
            let ro = o + 16 + 6 * sc + 2 * k;
            if u16_at(t, end) == 0xFFFF && u16_at(t, start) == 0xFFFF && u16_at(t, ro) == 0xFFFF {
                Some((delta, ro))
            } else {
                None
            }
        }
    }
}

/// The table with the subtable at `o` repaired, as OTS repairs it: the
/// last segment maps U+FFFF to glyph 0 (idDelta 1, idRangeOffset 0).
/// That one character's mapping is the only thing that changes.
pub open spec fn repair4(t: Seq<u8>, o: int) -> Seq<u8> {
    match repair4_at(t, o) {
        Some((d, r)) => t.update(d, 0).update(d + 1, 1).update(r, 0).update(r + 1, 0),
        None => t,
    }
}

/// Output encoding record `k` is input record `j`: the same platform and
/// encoding, and a subtable with the same bytes (all offsets inside a
/// subtable are relative to its start, so it maps every character the
/// same way), or the same bytes after the format 4 repair.
pub open spec fn cmap_rec_same(i: Seq<u8>, j: int, o: Seq<u8>, k: int) -> bool {
    let ri = 4 + 8 * j;
    let ro = 4 + 8 * k;
    let oi = u32_at(i, ri + 4);
    let oo = u32_at(o, ro + 4);
    let l = sub_len(o, oo);
    &&& 0 <= j
    &&& ri + 8 <= i.len()
    &&& u32_at(i, ri) == u32_at(o, ro)
    &&& oo + l <= o.len()
    &&& oi + l <= i.len()
    &&& (o.subrange(oo, oo + l) == i.subrange(oi, oi + l) || o.subrange(oo, oo + l) == repair4(
        i,
        oi,
    ).subrange(oi, oi + l))
}

pub open spec fn cmap_rec_kept(i: Seq<u8>, o: Seq<u8>, k: int) -> bool {
    exists|j: int| j < u16_at(i, 2) && #[trigger] cmap_rec_same(i, j, o, k)
}

/// `cmap`: every encoding record of the output is one of the input's,
/// with the same subtable. (Records whose subtables are malformed, or
/// that break the sort order, are dropped; the output keeps at least
/// one, as `wf_cmap` requires.)
pub open spec fn same_cmap(i: Seq<u8>, o: Seq<u8>) -> bool {
    &&& o.len() >= 4
    &&& forall|k: int| 0 <= k < u16_at(o, 2) ==> #[trigger] cmap_rec_kept(i, o, k)
}

/// Byte `j` of a `GSUB` or `GPOS` table lies in the default language
/// system of script record `r` and has the value the repair writes:
/// the script's DefaultLangSys offset cleared (the default language
/// system removed), its lookupOrder offset cleared (it is reserved and
/// must be null), or its reqFeatureIndex set to 0xFFFF (none).
pub open spec fn dls_fix(i: Seq<u8>, o: Seq<u8>, r: int, j: int) -> bool {
    let sl = u16_at(i, 4);
    let so = sl + u16_at(i, sl + 2 + 6 * r + 4);
    let d = u16_at(i, so);
    let l = so + d;
    &&& 6 <= i.len()
    &&& sl + 2 <= i.len()
    &&& 0 <= r < u16_at(i, sl)
    &&& sl + 2 + 6 * r + 6 <= i.len()
    &&& so + 2 <= i.len()
    &&& {
        ||| (so <= j < so + 2 && o[j] == 0)
        ||| (d != 0 && l <= j < l + 2 && o[j] == 0)
        ||| (d != 0 && l + 2 <= j < l + 4 && o[j] == 0xFF)
    }
}

/// Byte `j` of the layout table differs from the input in one of the
/// ways the sanitizer repairs: the link to variation data is cleared
/// (`GDEF` 14..18, `GSUB`/`GPOS` 10..14), or the default language system
/// of a script is repaired or removed (`GSUB`/`GPOS`).
pub open spec fn layout_fix(i: Seq<u8>, o: Seq<u8>, gdef: bool, j: int) -> bool {
    ||| (o[j] == 0 && (if gdef {
        14 <= j < 18
    } else {
        10 <= j < 14
    }))
    ||| (!gdef && exists|r: int| #[trigger] dls_fix(i, o, r, j))
}

/// `GDEF`, `GSUB`, `GPOS`: present in the output exactly when in the
/// input, the same length, and the same bytes but for `layout_fix`.
pub open spec fn same_layout(ts: Tables, s: Seq<u8>, t: int, gdef: bool) -> bool {
    let i = in_table(ts, t);
    let o = table(s, t);
    &&& has_table(s, t) == in_has(ts, t)
    &&& has_table(s, t) ==> {
        &&& o.len() == i.len()
        &&& forall|j: int| 0 <= j < o.len() ==> (#[trigger] o[j] == i[j] || layout_fix(i, o, gdef, j))
    }
}

/// `name` is the input's if that is well formed; `post` too, and in any
/// case it keeps the input's italic angle, underline position and
/// thickness, and fixed-pitch flag (bytes 4..32).
pub open spec fn same_name_post(ts: Tables, s: Seq<u8>, ng: int) -> bool {
    let p = in_table(ts, T_POST as int);
    let q = table(s, T_POST as int);
    &&& wf_name(in_table(ts, T_NAME as int)) ==> table(s, T_NAME as int) == in_table(ts, T_NAME as int)
    &&& wf_post(p, ng) ==> q == p
    &&& p.len() >= 32
    &&& q.len() >= 32
    &&& forall|j: int| 4 <= j < 32 ==> #[trigger] q[j] == p[j]
}

/// The output font `s` draws the same as the input tables `ts`: every
/// glyph has the same outline, the same metrics and the same hinting,
/// every character the output maps maps as in the input, the font-wide
/// values that drawing and line layout use are the input's, and the
/// layout tables differ only by the listed repairs.
pub open spec fn draws_same(ts: Tables, s: Seq<u8>) -> bool {
    let ng = num_glyphs(table(s, T_MAXP as int));
    &&& in_has(ts, T_HEAD as int)
    &&& in_has(ts, T_MAXP as int)
    &&& in_has(ts, T_HHEA as int)
    &&& in_has(ts, T_HMTX as int)
    &&& in_has(ts, T_OS2 as int)
    &&& in_has(ts, T_CMAP as int)
    &&& in_has(ts, T_NAME as int)
    &&& in_has(ts, T_POST as int)
    &&& same_head(in_table(ts, T_HEAD as int), table(s, T_HEAD as int))
    &&& same_maxp(in_table(ts, T_MAXP as int), table(s, T_MAXP as int), has_table(s, T_GLYF as int))
    &&& prefix_of(table(s, T_HHEA as int), in_table(ts, T_HHEA as int))
    &&& prefix_of(table(s, T_HMTX as int), in_table(ts, T_HMTX as int))
    &&& same_os2(in_table(ts, T_OS2 as int), table(s, T_OS2 as int))
    &&& same_vertical(ts, s, ng)
    &&& same_outlines(ts, s, ng)
    &&& same_hinting(ts, s, ng)
    &&& same_cmap(in_table(ts, T_CMAP as int), table(s, T_CMAP as int))
    &&& same_layout(ts, s, T_GDEF as int, true)
    &&& same_layout(ts, s, T_GSUB as int, false)
    &&& same_layout(ts, s, T_GPOS as int, false)
    &&& same_name_post(ts, s, ng)
}

// ---------------------------------------------------------------------
// Valid fonts
// ---------------------------------------------------------------------
/// Equal except perhaps bytes 8..12 (`head.checkSumAdjustment`).
pub open spec fn head_eq(a: Seq<u8>, b: Seq<u8>) -> bool {
    &&& a.len() == b.len()
    &&& forall|j: int| 0 <= j < a.len() && !(8 <= j < 12) ==> #[trigger] a[j] == b[j]
}

/// Font `s` has table `t` exactly when the input does, with the same
/// bytes (for `head`, but for `checkSumAdjustment`).
pub open spec fn same_one(ts: Tables, s: Seq<u8>, t: u32) -> bool {
    &&& has_table(s, t as int) == in_has(ts, t as int)
    &&& has_table(s, t as int) ==> if t == T_HEAD {
        head_eq(table(s, t as int), in_table(ts, t as int))
    } else {
        table(s, t as int) == in_table(ts, t as int)
    }
}

/// Font `s` holds exactly the input's known tables.
pub open spec fn same_tables(ts: Tables, s: Seq<u8>) -> bool {
    &&& same_one(ts, s, T_CFF)
    &&& same_one(ts, s, T_GDEF)
    &&& same_one(ts, s, T_GPOS)
    &&& same_one(ts, s, T_GSUB)
    &&& same_one(ts, s, T_OS2)
    &&& same_one(ts, s, T_CMAP)
    &&& same_one(ts, s, T_CVT)
    &&& same_one(ts, s, T_FPGM)
    &&& same_one(ts, s, T_GASP)
    &&& same_one(ts, s, T_GLYF)
    &&& same_one(ts, s, T_HEAD)
    &&& same_one(ts, s, T_HHEA)
    &&& same_one(ts, s, T_HMTX)
    &&& same_one(ts, s, T_KERN)
    &&& same_one(ts, s, T_LOCA)
    &&& same_one(ts, s, T_MAXP)
    &&& same_one(ts, s, T_NAME)
    &&& same_one(ts, s, T_POST)
    &&& same_one(ts, s, T_PREP)
    &&& same_one(ts, s, T_VHEA)
    &&& same_one(ts, s, T_VMTX)
}

/// The known tags in increasing order.
pub open spec fn known_list() -> Seq<u32> {
    seq![
        T_CFF,
        T_GDEF,
        T_GPOS,
        T_GSUB,
        T_OS2,
        T_CMAP,
        T_CVT,
        T_FPGM,
        T_GASP,
        T_GLYF,
        T_HEAD,
        T_HHEA,
        T_HMTX,
        T_KERN,
        T_LOCA,
        T_MAXP,
        T_NAME,
        T_POST,
        T_PREP,
        T_VHEA,
        T_VMTX,
    ]
}

/// The input's known tables among the first `i` of `known_list`, in that
/// order.
pub open spec fn canon_upto(ts: Tables, i: int) -> Tables
    decreases i,
{
    if i <= 0 {
        Seq::empty()
    } else {
        let t = known_list()[i - 1];
        if in_has(ts, t as int) {
            canon_upto(ts, i - 1).push((t, in_table(ts, t as int)))
        } else {
            canon_upto(ts, i - 1)
        }
    }
}

/// The input's known tables, in increasing order of tag.
pub open spec fn canon(ts: Tables) -> Tables {
    canon_upto(ts, 21)
}

/// The bytes tables `0..i` take up in a file, padding included.
pub open spec fn body_len(ts: Tables, i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        body_len(ts, i - 1) + pad4(ts[i - 1].1.len() as int)
    }
}

/// A valid font: its known tables, laid out as a file of their own,
/// would make a well-formed font, and together they take at most 1 GiB.
/// Nothing is asked of the input's table directory beyond what the reader
/// needs (its order, packing, padding and checksums do not matter), nor
/// of its other tables, nor of `head.checkSumAdjustment`.
pub open spec fn valid_tables(ts: Tables) -> bool {
    &&& body_len(canon(ts), canon(ts).len() as int) <= 0x4000_0000
    &&& exists|s: Seq<u8>| wf_font(s) && #[trigger] same_tables(ts, s)
}

} // verus!
