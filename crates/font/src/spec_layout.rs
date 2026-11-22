//! Trusted specification of the OpenType layout tables `GDEF`, `GSUB` and
//! `GPOS` (OpenType 1.9, "OpenType Layout Common Table Formats" and the
//! three table chapters).
//!
//! A position is an index into the table `t`. Every structure is named by
//! the position of its first byte. The rules are those OTS enforces, with
//! the differences listed in the README: every offset a consumer can
//! follow leads to a structure that lies inside the table and is itself
//! well formed, every glyph id that OTS checks is below the glyph count,
//! and every lookup and feature index names a lookup or feature that
//! exists.
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Building blocks
// ---------------------------------------------------------------------
/// The 16-bit offset stored at `a + w * i` is well formed: it can be
/// read; and either it is null (where `null` allows that), or it is at
/// least `min`, and `base` plus the offset is a position inside the table
/// at which `p` holds.
pub open spec fn off_ok(
    t: Seq<u8>,
    a: int,
    i: int,
    w: int,
    base: int,
    min: int,
    null: bool,
    p: spec_fn(int) -> bool,
) -> bool {
    let f = a + w * i;
    let o = u16_at(t, f);
    &&& f + 2 <= t.len()
    &&& ((null && o == 0) || (min <= o && base + o < t.len() && p(base + o)))
}

/// `n` offsets, `w` bytes apart, the first at `a`. `min` is where the
/// header holding them ends, which a 16-bit offset must be able to reach.
pub open spec fn offs(
    t: Seq<u8>,
    a: int,
    n: int,
    w: int,
    base: int,
    min: int,
    null: bool,
    p: spec_fn(int) -> bool,
) -> bool {
    &&& min <= 65535
    &&& forall|i: int| 0 <= i < n ==> #[trigger] off_ok(t, a, i, w, base, min, null, p)
}

pub open spec fn id_ok(t: Seq<u8>, a: int, i: int, lim: int) -> bool {
    u16_at(t, a + 2 * i) < lim
}

/// `n` 16-bit values starting at `a`, all inside the table and below `lim`.
pub open spec fn ids(t: Seq<u8>, a: int, n: int, lim: int) -> bool {
    &&& a + 2 * n <= t.len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] id_ok(t, a, i, lim)
}

pub open spec fn lrec_ok(t: Seq<u8>, a: int, i: int, ng: int, nl: int) -> bool {
    u16_at(t, a + 4 * i) < ng && u16_at(t, a + 4 * i + 2) < nl
}

/// `n` sequence lookup records starting at `a`: each names a lookup that
/// exists (and, as in OTS, a sequence index below the glyph count).
pub open spec fn lrecs(t: Seq<u8>, a: int, n: int, ng: int, nl: int) -> bool {
    &&& a + 4 * n <= t.len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] lrec_ok(t, a, i, ng, nl)
}

// ---------------------------------------------------------------------
// Coverage, class definition, device
// ---------------------------------------------------------------------
pub open spec fn cov_start(t: Seq<u8>, o: int, i: int) -> int {
    u16_at(t, o + 4 + 6 * i)
}

pub open spec fn cov_end(t: Seq<u8>, o: int, i: int) -> int {
    u16_at(t, o + 4 + 6 * i + 2)
}

/// How many glyphs the first `i` ranges of a format 2 coverage table cover.
pub open spec fn cov_count(t: Seq<u8>, o: int, i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        cov_count(t, o, i - 1) + cov_end(t, o, i - 1) - cov_start(t, o, i - 1) + 1
    }
}

pub open spec fn cov_range_ok(t: Seq<u8>, o: int, i: int) -> bool {
    &&& cov_start(t, o, i) <= cov_end(t, o, i)
    &&& i > 0 ==> cov_start(t, o, i) >= cov_end(t, o, i - 1)
    &&& u16_at(t, o + 4 + 6 * i + 4) == cov_count(t, o, i)
}

pub open spec fn wf_cov(t: Seq<u8>, o: int, ng: int) -> bool {
    let n = u16_at(t, o + 2);
    &&& o + 4 <= t.len()
    &&& n <= ng
    &&& if u16_at(t, o) == 1 {
        ids(t, o + 4, n, ng)
    } else {
        &&& u16_at(t, o) == 2
        &&& o + 4 + 6 * n <= t.len()
        &&& forall|i: int| 0 <= i < n ==> #[trigger] cov_range_ok(t, o, i)
    }
}

pub open spec fn cd_range_ok(t: Seq<u8>, o: int, i: int, maxc: int) -> bool {
    let start = u16_at(t, o + 4 + 6 * i);
    let end = u16_at(t, o + 4 + 6 * i + 2);
    let prev = u16_at(t, o + 4 + 6 * (i - 1) + 2);
    &&& start <= end
    &&& i > 0 ==> prev == 0 || start > prev
    &&& u16_at(t, o + 4 + 6 * i + 4) <= maxc
}

/// A class definition table whose classes are at most `maxc`.
pub open spec fn wf_classdef(t: Seq<u8>, o: int, ng: int, maxc: int) -> bool {
    &&& o + 4 <= t.len()
    &&& if u16_at(t, o) == 1 {
        &&& o + 6 <= t.len()
        &&& u16_at(t, o + 2) < ng
        &&& u16_at(t, o + 4) <= ng
        &&& ids(t, o + 6, u16_at(t, o + 4), maxc + 1)
    } else {
        let n = u16_at(t, o + 2);
        &&& u16_at(t, o) == 2
        &&& n <= ng
        &&& o + 4 + 6 * n <= t.len()
        &&& forall|i: int| 0 <= i < n ==> #[trigger] cd_range_ok(t, o, i, maxc)
    }
}

/// Sizes one 16-bit word of a device table covers, by delta format.
pub open spec fn dev_per(f: int) -> int {
    if f == 1 {
        8
    } else if f == 2 {
        4
    } else {
        2
    }
}

/// A device table, or a variation index table (format 0x8000).
pub open spec fn wf_device(t: Seq<u8>, o: int) -> bool {
    let s = u16_at(t, o);
    let e = u16_at(t, o + 2);
    let f = u16_at(t, o + 4);
    &&& o + 6 <= t.len()
    &&& f == 0x8000 || {
        &&& s <= e
        &&& 1 <= f <= 3
        &&& o + 6 + 2 * ((e - s) / dev_per(f) + 1) <= t.len()
    }
}

// ---------------------------------------------------------------------
// Script list, feature list
// ---------------------------------------------------------------------
pub open spec fn wf_langsys(t: Seq<u8>, o: int, nf: int) -> bool {
    &&& o + 6 <= t.len()
    &&& u16_at(t, o) == 0
    &&& u16_at(t, o + 2) == 0xFFFF || u16_at(t, o + 2) < nf
    &&& u16_at(t, o + 4) <= nf
    &&& ids(t, o + 6, u16_at(t, o + 4), nf)
}

/// Tags of 6-byte records starting at `a` do not decrease from record
/// `i - 1` to record `i` (a zero tag is exempt, as in OTS).
pub open spec fn tag_order_ok(t: Seq<u8>, a: int, i: int) -> bool {
    u32_at(t, a + 6 * (i - 1)) == 0 || u32_at(t, a + 6 * (i - 1)) <= u32_at(t, a + 6 * i)
}

pub open spec fn wf_script(t: Seq<u8>, o: int, dflt: bool, nf: int) -> bool {
    let n = u16_at(t, o + 2);
    &&& o + 4 <= t.len()
    &&& dflt ==> u16_at(t, o) != 0
    &&& off_ok(t, o, 0, 2, o, 0, true, |x: int| wf_langsys(t, x, nf))
    &&& offs(t, o + 8, n, 6, o, 4 + 6 * n, false, |x: int| wf_langsys(t, x, nf))
    &&& forall|i: int| 0 < i < n ==> #[trigger] tag_order_ok(t, o + 4, i)
}

pub open spec fn tag_dflt() -> int {
    0x44464c54
}

pub open spec fn script_rec_ok(t: Seq<u8>, o: int, i: int, min: int, nf: int) -> bool {
    let r = o + 2 + 6 * i;
    let off = u16_at(t, r + 4);
    &&& r + 6 <= t.len()
    &&& min <= off
    &&& o + off < t.len()
    &&& wf_script(t, o + off, u32_at(t, r) == tag_dflt(), nf)
}

pub open spec fn wf_scriptlist(t: Seq<u8>, o: int, nf: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& 2 + 6 * n <= 65535
    &&& forall|i: int| 0 <= i < n ==> #[trigger] script_rec_ok(t, o, i, 2 + 6 * n, nf)
}

pub open spec fn wf_feature(t: Seq<u8>, o: int, nl: int) -> bool {
    let params = u16_at(t, o);
    let n = u16_at(t, o + 2);
    &&& o + 4 <= t.len()
    &&& 4 + 2 * n <= 65535
    &&& params == 0 || (4 + 2 * n <= params && o + params < t.len())
    &&& ids(t, o + 4, n, nl)
}

pub open spec fn wf_featurelist(t: Seq<u8>, o: int, nl: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& offs(t, o + 6, n, 6, o, 2 + 6 * n, false, |x: int| wf_feature(t, x, nl))
}

// ---------------------------------------------------------------------
// Contextual subtables (shared by GSUB and GPOS)
// ---------------------------------------------------------------------
/// A sequence rule: `lim` bounds the glyph ids or classes of the input.
pub open spec fn wf_rule(t: Seq<u8>, o: int, lim: int, ng: int, nl: int) -> bool {
    let g = u16_at(t, o);
    &&& o + 4 <= t.len()
    &&& g >= 1
    &&& ids(t, o + 4, g - 1, lim)
    &&& lrecs(t, o + 4 + 2 * (g - 1), u16_at(t, o + 2), ng, nl)
}

pub open spec fn wf_ruleset(t: Seq<u8>, o: int, lim: int, ng: int, nl: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& offs(t, o + 2, n, 2, o, 2 + 2 * n, false, |x: int| wf_rule(t, x, lim, ng, nl))
}

pub open spec fn wf_context(t: Seq<u8>, o: int, ng: int, nl: int) -> bool {
    let fmt = u16_at(t, o);
    &&& o + 6 <= t.len()
    &&& if fmt == 1 {
        let n = u16_at(t, o + 4);
        &&& off_ok(t, o + 2, 0, 2, o, 6 + 2 * n, false, |x: int| wf_cov(t, x, ng))
        &&& offs(t, o + 6, n, 2, o, 6 + 2 * n, false, |x: int| wf_ruleset(t, x, ng, ng, nl))
    } else if fmt == 2 {
        let n = u16_at(t, o + 6);
        &&& o + 8 <= t.len()
        &&& off_ok(t, o + 2, 0, 2, o, 8 + 2 * n, false, |x: int| wf_cov(t, x, ng))
        &&& off_ok(t, o + 4, 0, 2, o, 8 + 2 * n, false, |x: int| wf_classdef(t, x, ng, 0xFFFF))
        &&& offs(t, o + 8, n, 2, o, 8 + 2 * n, true, |x: int| wf_ruleset(t, x, 0x10000, ng, nl))
    } else {
        let g = u16_at(t, o + 2);
        let l = u16_at(t, o + 4);
        &&& fmt == 3
        &&& offs(t, o + 6, g, 2, o, 6 + 2 * g + 4 * l, false, |x: int| wf_cov(t, x, ng))
        &&& lrecs(t, o + 6 + 2 * g, l, ng, nl)
    }
}

/// A chained sequence rule: backtrack, input and lookahead sequences,
/// then the lookup records.
pub open spec fn wf_chainrule(t: Seq<u8>, o: int, lim: int, ng: int, nl: int) -> bool {
    let b = u16_at(t, o);
    let p1 = o + 2 + 2 * b;
    let i = u16_at(t, p1);
    let p2 = p1 + 2 + 2 * (i - 1);
    let a = u16_at(t, p2);
    let p3 = p2 + 2 + 2 * a;
    &&& o + 2 <= t.len()
    &&& ids(t, o + 2, b, lim)
    &&& p1 + 2 <= t.len()
    &&& i >= 1
    &&& ids(t, p1 + 2, i - 1, lim)
    &&& p2 + 2 <= t.len()
    &&& ids(t, p2 + 2, a, lim)
    &&& p3 + 2 <= t.len()
    &&& lrecs(t, p3 + 2, u16_at(t, p3), ng, nl)
}

pub open spec fn wf_chainruleset(t: Seq<u8>, o: int, lim: int, ng: int, nl: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& offs(t, o + 2, n, 2, o, 2 + 2 * n, false, |x: int| wf_chainrule(t, x, lim, ng, nl))
}

pub open spec fn wf_chain3(t: Seq<u8>, o: int, ng: int, nl: int) -> bool {
    let b = u16_at(t, o + 2);
    let p1 = o + 4 + 2 * b;
    let i = u16_at(t, p1);
    let p2 = p1 + 2 + 2 * i;
    let a = u16_at(t, p2);
    let p3 = p2 + 2 + 2 * a;
    let l = u16_at(t, p3);
    let end = 10 + 2 * (b + i + a) + 4 * l;
    &&& p1 + 2 <= t.len()
    &&& p2 + 2 <= t.len()
    &&& p3 + 2 <= t.len()
    &&& lrecs(t, p3 + 2, l, ng, nl)
    &&& offs(t, o + 4, b, 2, o, end, false, |x: int| wf_cov(t, x, ng))
    &&& offs(t, p1 + 2, i, 2, o, end, false, |x: int| wf_cov(t, x, ng))
    &&& offs(t, p2 + 2, a, 2, o, end, false, |x: int| wf_cov(t, x, ng))
}

pub open spec fn wf_chain(t: Seq<u8>, o: int, ng: int, nl: int) -> bool {
    let fmt = u16_at(t, o);
    &&& o + 4 <= t.len()
    &&& if fmt == 1 {
        let n = u16_at(t, o + 4);
        &&& o + 6 <= t.len()
        &&& off_ok(t, o + 2, 0, 2, o, 6 + 2 * n, false, |x: int| wf_cov(t, x, ng))
        &&& offs(t, o + 6, n, 2, o, 6 + 2 * n, false, |x: int| wf_chainruleset(t, x, ng, ng, nl))
    } else if fmt == 2 {
        let n = u16_at(t, o + 10);
        let end = 12 + 2 * n;
        &&& o + 12 <= t.len()
        &&& off_ok(t, o + 2, 0, 2, o, end, false, |x: int| wf_cov(t, x, ng))
        &&& off_ok(t, o + 4, 0, 2, o, end, true, |x: int| wf_classdef(t, x, ng, 0xFFFF))
        &&& off_ok(t, o + 6, 0, 2, o, end, false, |x: int| wf_classdef(t, x, ng, 0xFFFF))
        &&& off_ok(t, o + 8, 0, 2, o, end, true, |x: int| wf_classdef(t, x, ng, 0xFFFF))
        &&& offs(t, o + 12, n, 2, o, end, true, |x: int| wf_chainruleset(t, x, 0x10000, ng, nl))
    } else {
        &&& fmt == 3
        &&& wf_chain3(t, o, ng, nl)
    }
}

// ---------------------------------------------------------------------
// GSUB lookup subtables
// ---------------------------------------------------------------------
/// A count followed by that many glyph ids (Sequence, AlternateSet).
pub open spec fn wf_glyphs(t: Seq<u8>, o: int, ng: int) -> bool {
    &&& o + 2 <= t.len()
    &&& ids(t, o + 2, u16_at(t, o), ng)
}

pub open spec fn wf_single_sub(t: Seq<u8>, o: int, ng: int) -> bool {
    &&& o + 6 <= t.len()
    &&& if u16_at(t, o) == 1 {
        &&& -ng < i16_at(t, o + 4) < ng
        &&& off_ok(t, o + 2, 0, 2, o, 6, false, |x: int| wf_cov(t, x, ng))
    } else {
        let n = u16_at(t, o + 4);
        &&& u16_at(t, o) == 2
        &&& n <= ng
        &&& ids(t, o + 6, n, ng)
        &&& off_ok(t, o + 2, 0, 2, o, 6 + 2 * n, false, |x: int| wf_cov(t, x, ng))
    }
}

/// Multiple and alternate substitution: coverage and an array of glyph lists.
pub open spec fn wf_multi_sub(t: Seq<u8>, o: int, ng: int) -> bool {
    let n = u16_at(t, o + 4);
    &&& o + 6 <= t.len()
    &&& u16_at(t, o) == 1
    &&& off_ok(t, o + 2, 0, 2, o, 6 + 2 * n, false, |x: int| wf_cov(t, x, ng))
    &&& offs(t, o + 6, n, 2, o, 6 + 2 * n, false, |x: int| wf_glyphs(t, x, ng))
}

pub open spec fn wf_ligature(t: Seq<u8>, o: int, ng: int) -> bool {
    &&& o + 4 <= t.len()
    &&& u16_at(t, o) < ng
    &&& u16_at(t, o + 2) >= 1
    &&& ids(t, o + 4, u16_at(t, o + 2) - 1, ng)
}

pub open spec fn wf_ligset(t: Seq<u8>, o: int, ng: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& offs(t, o + 2, n, 2, o, 2 + 2 * n, false, |x: int| wf_ligature(t, x, ng))
}

pub open spec fn wf_lig_sub(t: Seq<u8>, o: int, ng: int) -> bool {
    let n = u16_at(t, o + 4);
    &&& o + 6 <= t.len()
    &&& u16_at(t, o) == 1
    &&& off_ok(t, o + 2, 0, 2, o, 6 + 2 * n, false, |x: int| wf_cov(t, x, ng))
    &&& offs(t, o + 6, n, 2, o, 6 + 2 * n, false, |x: int| wf_ligset(t, x, ng))
}

pub open spec fn wf_rev_chain(t: Seq<u8>, o: int, ng: int) -> bool {
    let b = u16_at(t, o + 4);
    let p1 = o + 6 + 2 * b;
    let a = u16_at(t, p1);
    let p2 = p1 + 2 + 2 * a;
    let g = u16_at(t, p2);
    let end = 10 + 2 * (b + a + g);
    &&& o + 6 <= t.len()
    &&& u16_at(t, o) == 1
    &&& p1 + 2 <= t.len()
    &&& p2 + 2 <= t.len()
    &&& ids(t, p2 + 2, g, ng)
    &&& off_ok(t, o + 2, 0, 2, o, end, false, |x: int| wf_cov(t, x, ng))
    &&& offs(t, o + 6, b, 2, o, end, false, |x: int| wf_cov(t, x, ng))
    &&& offs(t, p1 + 2, a, 2, o, end, false, |x: int| wf_cov(t, x, ng))
}

pub open spec fn wf_gsub_sub(t: Seq<u8>, o: int, ty: int, ng: int, nl: int) -> bool {
    if ty == 1 {
        wf_single_sub(t, o, ng)
    } else if ty == 2 || ty == 3 {
        wf_multi_sub(t, o, ng)
    } else if ty == 4 {
        wf_lig_sub(t, o, ng)
    } else if ty == 5 {
        wf_context(t, o, ng, nl)
    } else if ty == 6 {
        wf_chain(t, o, ng, nl)
    } else {
        ty == 8 && wf_rev_chain(t, o, ng)
    }
}

// ---------------------------------------------------------------------
// GPOS lookup subtables
// ---------------------------------------------------------------------
/// Bit `m` (a power of two) of a value format is set.
pub open spec fn has(f: int, m: int) -> bool {
    (f / m) % 2 == 1
}

pub open spec fn sz(f: int, m: int) -> int {
    if has(f, m) {
        2
    } else {
        0
    }
}

/// Bytes in a value record of format `f`.
pub open spec fn vsize(f: int) -> int {
    sz(f, 1) + sz(f, 2) + sz(f, 4) + sz(f, 8) + sz(f, 16) + sz(f, 32) + sz(f, 64) + sz(f, 128)
}

/// An optional offset to a device table at `p`, relative to `base`.
pub open spec fn dev_ok(t: Seq<u8>, base: int, p: int) -> bool {
    off_ok(t, p, 0, 2, base, 0, true, |x: int| wf_device(t, x))
}

/// A value record of format `f` at `p`, in a structure starting at `base`.
pub open spec fn wf_value(t: Seq<u8>, base: int, p: int, f: int) -> bool {
    let p4 = p + sz(f, 1) + sz(f, 2) + sz(f, 4) + sz(f, 8);
    let p5 = p4 + sz(f, 16);
    let p6 = p5 + sz(f, 32);
    let p7 = p6 + sz(f, 64);
    &&& p + vsize(f) <= t.len()
    &&& has(f, 16) ==> dev_ok(t, base, p4)
    &&& has(f, 32) ==> dev_ok(t, base, p5)
    &&& has(f, 64) ==> dev_ok(t, base, p6)
    &&& has(f, 128) ==> dev_ok(t, base, p7)
}

pub open spec fn value_at(t: Seq<u8>, base: int, a: int, w: int, i: int, f: int) -> bool {
    wf_value(t, base, a + w * i, f)
}

pub open spec fn wf_single_pos(t: Seq<u8>, o: int, ng: int) -> bool {
    let f = u16_at(t, o + 4);
    &&& o + 6 <= t.len()
    &&& if u16_at(t, o) == 1 {
        &&& wf_value(t, o, o + 6, f)
        &&& off_ok(t, o + 2, 0, 2, o, 6 + vsize(f), false, |x: int| wf_cov(t, x, ng))
    } else {
        let n = u16_at(t, o + 6);
        &&& u16_at(t, o) == 2
        &&& o + 8 <= t.len()
        &&& forall|i: int| 0 <= i < n ==> #[trigger] value_at(t, o, o + 8, vsize(f), i, f)
        &&& off_ok(t, o + 2, 0, 2, o, 8 + n * vsize(f), false, |x: int| wf_cov(t, x, ng))
    }
}

pub open spec fn pair_rec_ok(t: Seq<u8>, o: int, i: int, f1: int, f2: int, ng: int) -> bool {
    let r = o + 2 + (2 + vsize(f1) + vsize(f2)) * i;
    &&& r + 2 <= t.len()
    &&& u16_at(t, r) < ng
    &&& wf_value(t, o, r + 2, f1)
    &&& wf_value(t, o, r + 2 + vsize(f1), f2)
}

pub open spec fn wf_pairset(t: Seq<u8>, o: int, f1: int, f2: int, ng: int) -> bool {
    &&& o + 2 <= t.len()
    &&& forall|i: int| 0 <= i < u16_at(t, o) ==> #[trigger] pair_rec_ok(t, o, i, f1, f2, ng)
}

pub open spec fn class_pair_ok(t: Seq<u8>, o: int, k: int, f1: int, f2: int) -> bool {
    let r = o + 16 + (vsize(f1) + vsize(f2)) * k;
    &&& wf_value(t, o, r, f1)
    &&& wf_value(t, o, r + vsize(f1), f2)
}

pub open spec fn wf_pair_pos(t: Seq<u8>, o: int, ng: int) -> bool {
    let f1 = u16_at(t, o + 4);
    let f2 = u16_at(t, o + 6);
    &&& o + 8 <= t.len()
    &&& off_ok(t, o + 2, 0, 2, o, 8, false, |x: int| wf_cov(t, x, ng))
    &&& if u16_at(t, o) == 1 {
        let n = u16_at(t, o + 8);
        &&& o + 10 <= t.len()
        &&& offs(t, o + 10, n, 2, o, 10 + 2 * n, false, |x: int| wf_pairset(t, x, f1, f2, ng))
    } else {
        let w = vsize(f1) + vsize(f2);
        let cells = u16_at(t, o + 12) * u16_at(t, o + 14);
        &&& u16_at(t, o) == 2
        &&& o + 16 <= t.len()
        &&& off_ok(t, o + 8, 0, 2, o, 16 + cells * w, false, |x: int| wf_classdef(t, x, ng, 0xFFFF))
        &&& off_ok(t, o + 10, 0, 2, o, 16 + cells * w, false, |x: int| wf_classdef(t, x, ng, 0xFFFF))
        &&& w > 0 ==> forall|k: int| 0 <= k < cells ==> #[trigger] class_pair_ok(t, o, k, f1, f2)
    }
}

pub open spec fn wf_anchor(t: Seq<u8>, o: int) -> bool {
    let f = u16_at(t, o);
    &&& o + 6 <= t.len()
    &&& 1 <= f <= 3
    &&& f == 2 ==> o + 8 <= t.len()
    &&& f == 3 ==> {
        &&& off_ok(t, o + 6, 0, 2, o, 10, true, |x: int| wf_device(t, x))
        &&& off_ok(t, o + 6, 1, 2, o, 10, true, |x: int| wf_device(t, x))
    }
}

pub open spec fn wf_cursive(t: Seq<u8>, o: int, ng: int) -> bool {
    let n = u16_at(t, o + 4);
    &&& o + 6 <= t.len()
    &&& u16_at(t, o) == 1
    &&& offs(t, o + 6, 2 * n, 2, o, 6 + 4 * n, true, |x: int| wf_anchor(t, x))
    &&& off_ok(t, o + 2, 0, 2, o, 6 + 4 * n, false, |x: int| wf_cov(t, x, ng))
}

pub open spec fn wf_markarray(t: Seq<u8>, o: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& offs(t, o + 4, n, 4, o, 2 + 4 * n, false, |x: int| wf_anchor(t, x))
}

/// `u16(o)` rows of `cc` optional anchors each.
pub open spec fn wf_anchorarray(t: Seq<u8>, o: int, cc: int) -> bool {
    let n = u16_at(t, o) * cc;
    &&& o + 2 <= t.len()
    &&& offs(t, o + 2, n, 2, o, 2 + 2 * n, true, |x: int| wf_anchor(t, x))
}

pub open spec fn wf_ligarray(t: Seq<u8>, o: int, cc: int) -> bool {
    &&& o + 2 <= t.len()
    &&& offs(t, o + 2, u16_at(t, o), 2, o, 2, false, |x: int| wf_anchorarray(t, x, cc))
}

/// Mark-to-base, mark-to-ligature (`lig`) and mark-to-mark attachment.
pub open spec fn wf_mark_pos(t: Seq<u8>, o: int, lig: bool, ng: int) -> bool {
    let cc = u16_at(t, o + 6);
    &&& o + 12 <= t.len()
    &&& u16_at(t, o) == 1
    &&& off_ok(t, o + 2, 0, 2, o, 12, false, |x: int| wf_cov(t, x, ng))
    &&& off_ok(t, o + 4, 0, 2, o, 12, false, |x: int| wf_cov(t, x, ng))
    &&& off_ok(t, o + 8, 0, 2, o, 12, false, |x: int| wf_markarray(t, x))
    &&& if lig {
        off_ok(t, o + 10, 0, 2, o, 12, false, |x: int| wf_ligarray(t, x, cc))
    } else {
        off_ok(t, o + 10, 0, 2, o, 12, false, |x: int| wf_anchorarray(t, x, cc))
    }
}

pub open spec fn wf_gpos_sub(t: Seq<u8>, o: int, ty: int, ng: int, nl: int) -> bool {
    if ty == 1 {
        wf_single_pos(t, o, ng)
    } else if ty == 2 {
        wf_pair_pos(t, o, ng)
    } else if ty == 3 {
        wf_cursive(t, o, ng)
    } else if ty == 4 || ty == 6 {
        wf_mark_pos(t, o, false, ng)
    } else if ty == 5 {
        wf_mark_pos(t, o, true, ng)
    } else if ty == 7 {
        wf_context(t, o, ng, nl)
    } else {
        ty == 8 && wf_chain(t, o, ng, nl)
    }
}

// ---------------------------------------------------------------------
// Lookups and the GSUB / GPOS header
// ---------------------------------------------------------------------
/// The lookup type that means "extension" (`pos`: GPOS, otherwise GSUB).
pub open spec fn ext_type(pos: bool) -> int {
    if pos {
        9
    } else {
        7
    }
}

pub open spec fn wf_plain(t: Seq<u8>, o: int, pos: bool, ty: int, ng: int, nl: int) -> bool {
    if pos {
        wf_gpos_sub(t, o, ty, ng, nl)
    } else {
        wf_gsub_sub(t, o, ty, ng, nl)
    }
}

/// A lookup subtable of type `ty`, directly or through one extension.
pub open spec fn wf_subtable(t: Seq<u8>, o: int, pos: bool, ty: int, ng: int, nl: int) -> bool {
    if ty == ext_type(pos) {
        let ety = u16_at(t, o + 2);
        let eo = u32_at(t, o + 4);
        &&& o + 8 <= t.len()
        &&& u16_at(t, o) == 1
        &&& ety != ext_type(pos)
        &&& 8 <= eo
        &&& o + eo < t.len()
        &&& wf_plain(t, o + eo, pos, ety, ng, nl)
    } else {
        wf_plain(t, o, pos, ty, ng, nl)
    }
}

/// A lookup table. `ms` bounds the mark filtering set it may name.
pub open spec fn wf_lookup(t: Seq<u8>, o: int, pos: bool, ng: int, nl: int, ms: int) -> bool {
    let ty = u16_at(t, o);
    let n = u16_at(t, o + 4);
    let filt = has(u16_at(t, o + 2), 16);
    let end = 6 + 2 * n + if filt { 2int } else { 0 };
    &&& o + 6 <= t.len()
    &&& 1 <= ty <= ext_type(pos)
    &&& offs(t, o + 6, n, 2, o, end, false, |x: int| wf_subtable(t, x, pos, ty, ng, nl))
    &&& filt ==> o + 8 + 2 * n <= t.len() && u16_at(t, o + 6 + 2 * n) < ms
}

pub open spec fn wf_lookuplist(t: Seq<u8>, o: int, pos: bool, ng: int, ms: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& offs(t, o + 2, n, 2, o, 2 + 2 * n, false, |x: int| wf_lookup(t, x, pos, ng, n, ms))
}

/// The count a list at offset `off` starts with; an absent list is empty.
pub open spec fn list_count(t: Seq<u8>, off: int) -> int {
    if off == 0 {
        0
    } else {
        u16_at(t, off)
    }
}

/// A whole `GSUB` (`pos` false) or `GPOS` (`pos` true) table, version 1.0,
/// or 1.1 without feature variations. `ng` is the font's glyph count and
/// `ms` the number of mark glyph sets `GDEF` defines.
pub open spec fn wf_layout(t: Seq<u8>, pos: bool, ng: int, ms: int) -> bool {
    let minor = u16_at(t, 2);
    let hdr: int = if minor == 0 { 10 } else { 14 };
    let sl = u16_at(t, 4);
    let fl = u16_at(t, 6);
    let ll = u16_at(t, 8);
    let nl = list_count(t, ll);
    let nf = list_count(t, fl);
    &&& t.len() >= hdr
    &&& u16_at(t, 0) == 1
    &&& minor <= 1
    &&& minor == 1 ==> u32_at(t, 10) == 0
    &&& ll != 0 ==> hdr <= ll < t.len() && wf_lookuplist(t, ll, pos, ng, ms)
    &&& fl != 0 ==> hdr <= fl < t.len() && wf_featurelist(t, fl, nl)
    &&& sl != 0 ==> hdr <= sl < t.len() && wf_scriptlist(t, sl, nf)
}

// ---------------------------------------------------------------------
// GDEF
// ---------------------------------------------------------------------
/// Contour point indices `j - 1` and `j` of an attach point table increase.
pub open spec fn point_order_ok(t: Seq<u8>, o: int, j: int) -> bool {
    u16_at(t, o + 2 + 2 * (j - 1)) == 0 || u16_at(t, o + 2 + 2 * (j - 1)) < u16_at(t, o + 2 + 2 * j)
}

pub open spec fn wf_attachpoint(t: Seq<u8>, o: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& n >= 1
    &&& o + 2 + 2 * n <= t.len()
    &&& forall|j: int| 0 < j < n ==> #[trigger] point_order_ok(t, o, j)
}

pub open spec fn wf_caret(t: Seq<u8>, o: int) -> bool {
    let f = u16_at(t, o);
    &&& o + 4 <= t.len()
    &&& 1 <= f <= 3
    &&& f == 3 ==> off_ok(t, o + 4, 0, 2, o, 1, false, |x: int| wf_device(t, x))
}

pub open spec fn wf_ligglyph(t: Seq<u8>, o: int) -> bool {
    let n = u16_at(t, o);
    &&& o + 2 <= t.len()
    &&& n >= 1
    &&& offs(t, o + 2, n, 2, o, 2 + 2 * n, false, |x: int| wf_caret(t, x))
}

/// AttachList (`lig` false) or LigCaretList (`lig` true).
pub open spec fn wf_glyphlist(t: Seq<u8>, o: int, lig: bool, ng: int) -> bool {
    let n = u16_at(t, o + 2);
    &&& o + 4 <= t.len()
    &&& n <= ng
    &&& off_ok(t, o, 0, 2, o, 4 + 2 * n, false, |x: int| wf_cov(t, x, ng))
    &&& if lig {
        offs(t, o + 4, n, 2, o, 4 + 2 * n, false, |x: int| wf_ligglyph(t, x))
    } else {
        offs(t, o + 4, n, 2, o, 4 + 2 * n, false, |x: int| wf_attachpoint(t, x))
    }
}

pub open spec fn markset_ok(t: Seq<u8>, o: int, i: int, min: int, ng: int) -> bool {
    let off = u32_at(t, o + 4 + 4 * i);
    &&& min <= off
    &&& o + off < t.len()
    &&& wf_cov(t, o + off, ng)
}

pub open spec fn wf_marksets(t: Seq<u8>, o: int, ng: int) -> bool {
    let n = u16_at(t, o + 2);
    &&& o + 4 <= t.len()
    &&& u16_at(t, o) == 1
    &&& 4 + 2 * n <= 65535
    &&& o + 4 + 4 * n <= t.len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] markset_ok(t, o, i, 4 + 4 * n, ng)
}

pub open spec fn gdef_hdr(minor: int) -> int {
    if minor == 0 {
        12
    } else if minor == 2 {
        14
    } else {
        18
    }
}

/// `GDEF` version 1.0, 1.2, or 1.3 without an item variation store.
pub open spec fn wf_gdef(t: Seq<u8>, ng: int) -> bool {
    let minor = u16_at(t, 2);
    let hdr = gdef_hdr(minor);
    &&& t.len() >= hdr
    &&& u16_at(t, 0) == 1
    &&& minor == 0 || minor == 2 || minor == 3
    &&& off_ok(t, 4, 0, 2, 0, hdr, true, |x: int| wf_classdef(t, x, ng, 4))
    &&& off_ok(t, 6, 0, 2, 0, hdr, true, |x: int| wf_glyphlist(t, x, false, ng))
    &&& off_ok(t, 8, 0, 2, 0, hdr, true, |x: int| wf_glyphlist(t, x, true, ng))
    &&& off_ok(t, 10, 0, 2, 0, hdr, true, |x: int| wf_classdef(t, x, ng, 0xFFFF))
    &&& minor >= 2 ==> off_ok(t, 12, 0, 2, 0, hdr, true, |x: int| wf_marksets(t, x, ng))
    &&& minor == 3 ==> u32_at(t, 14) == 0
}

/// How many mark glyph sets a well-formed `GDEF` defines.
pub open spec fn gdef_mark_sets(t: Seq<u8>) -> int {
    if u16_at(t, 2) >= 2 && u16_at(t, 12) != 0 {
        u16_at(t, u16_at(t, 12) + 2)
    } else {
        0
    }
}

} // verus!
