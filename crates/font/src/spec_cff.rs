//! The trusted specification of a well-formed `CFF ` table (`wf_cff`),
//! written from Adobe Technical Note #5176 (the Compact Font Format).
//!
//! It covers the structure of the table: the header, every INDEX, the Top
//! DICT and Private DICTs, the charset, the encoding, and for CID-keyed
//! fonts the Font DICT array and FDSelect. Every DICT holds only operators
//! this specification knows, each with the operands it takes; every
//! offset the DICTs give leads to a structure that lies inside the table;
//! every string id names a string that exists; and the structures that
//! are per glyph cover exactly the font's glyphs. The contents of the
//! charstrings (the glyph programs) are specified in `spec_cs`.
//!
//! The rules follow what OTS accepts, and are stricter in a few places
//! that the comments point out.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// An unsigned big-endian number of `n` bytes (1 to 4) at `i`.
pub open spec fn un_at(t: Seq<u8>, i: int, n: int) -> int {
    if n == 1 {
        t[i] as int
    } else if n == 2 {
        u16_at(t, i)
    } else if n == 3 {
        u24_at(t, i)
    } else {
        u32_at(t, i)
    }
}

// ---------------------------------------------------------------------
// INDEX
// ---------------------------------------------------------------------
pub open spec fn index_count(t: Seq<u8>, p: int) -> int {
    u16_at(t, p)
}

/// Offset `i` of the INDEX at `p` (which has at least one object).
pub open spec fn index_off(t: Seq<u8>, p: int, i: int) -> int {
    un_at(t, p + 3 + i * t[p + 2], t[p + 2] as int)
}

/// Where object data is measured from: offset 1 is the first data byte.
pub open spec fn index_base(t: Seq<u8>, p: int) -> int {
    p + 2 + (index_count(t, p) + 1) * t[p + 2]
}

/// Object `i` of the INDEX at `p` does not end before it starts.
pub open spec fn index_step(t: Seq<u8>, p: int, i: int) -> bool {
    index_off(t, p, i) <= index_off(t, p, i + 1)
}

/// The INDEX at `p` lies inside `t`: its offsets start at 1, never
/// decrease, and the last one is inside the table.
pub open spec fn wf_index(t: Seq<u8>, p: int) -> bool {
    &&& 0 <= p
    &&& p + 2 <= t.len()
    &&& (index_count(t, p) != 0 ==> {
        &&& p + 3 <= t.len()
        &&& 1 <= t[p + 2] <= 4
        &&& index_base(t, p) + 1 <= t.len()
        &&& index_off(t, p, 0) == 1
        &&& forall|i: int| 0 <= i < index_count(t, p) ==> #[trigger] index_step(t, p, i)
        &&& index_base(t, p) + index_off(t, p, index_count(t, p)) <= t.len()
    })
}

/// The first byte after the INDEX at `p`.
pub open spec fn index_end(t: Seq<u8>, p: int) -> int {
    if index_count(t, p) == 0 {
        p + 2
    } else {
        index_base(t, p) + index_off(t, p, index_count(t, p))
    }
}

/// Object `i` of the INDEX at `p`.
pub open spec fn index_obj(t: Seq<u8>, p: int, i: int) -> Seq<u8> {
    t.subrange(index_base(t, p) + index_off(t, p, i), index_base(t, p) + index_off(t, p, i + 1))
}

// ---------------------------------------------------------------------
// DICT
// ---------------------------------------------------------------------
/// Nibble `k` of the real number whose nibbles start at byte `p`.
pub open spec fn nib(d: Seq<u8>, p: int, k: int) -> int {
    if k % 2 == 0 {
        (d[p + k / 2] >> 4) as int
    } else {
        (d[p + k / 2] & 0x0f) as int
    }
}

/// Where the real number whose nibbles start at byte `p` ends, reading on
/// from nibble `k`: just after the byte with the end nibble (`f`). `None`
/// if the number is malformed: it runs off the DICT, uses the reserved
/// nibble `d`, has a minus sign anywhere but first, has two decimal points
/// or one in the exponent, has two exponents or one of 120 or more, or
/// ends in the high half of a byte whose low half is not `f` too.
/// `point` and `e` say whether a decimal point and an exponent mark have
/// been read, and `exp` is the exponent so far.
pub open spec fn real_end(d: Seq<u8>, p: int, k: int, point: bool, e: bool, exp: int) -> Option<int>
    decreases 2 * (d.len() - p) - k,
{
    if p < 0 || k < 0 || p + k / 2 >= d.len() {
        None
    } else {
        let x = nib(d, p, k);
        if x == 15 {
            if k % 2 == 0 && nib(d, p, k + 1) != 15 {
                None
            } else {
                Some(p + k / 2 + 1)
            }
        } else if x == 13 {
            None
        } else if x == 14 {
            if k == 0 {
                real_end(d, p, k + 1, point, e, exp)
            } else {
                None
            }
        } else if x == 10 {
            if !point && !e {
                real_end(d, p, k + 1, true, e, exp)
            } else {
                None
            }
        } else if x == 11 || x == 12 {
            if !e {
                real_end(d, p, k + 1, point, true, exp)
            } else {
                None
            }
        } else if e {
            if exp * 10 + x < 120 {
                real_end(d, p, k + 1, point, e, exp * 10 + x)
            } else {
                None
            }
        } else {
            real_end(d, p, k + 1, point, e, exp)
        }
    }
}

/// What a real-number operand counts as: a value no integer operand can
/// have. Where an operand must be an integer, it must not be this.
pub spec const REAL: int = 0x1_0000_0000;

/// One DICT token.
pub enum Tok {
    /// An operand and where the next token starts.
    Num(int, int),
    /// An operator (two-byte operators `12 x` are numbered `256 + x`) and
    /// where the next token starts.
    Op(int, int),
    Bad,
}

pub open spec fn i32_at(d: Seq<u8>, i: int) -> int {
    if u32_at(d, i) >= 0x8000_0000 {
        u32_at(d, i) - 0x1_0000_0000
    } else {
        u32_at(d, i)
    }
}

/// The DICT token at `p` (with `0 <= p < d.len()`).
pub open spec fn dict_tok(d: Seq<u8>, p: int) -> Tok {
    let b = d[p];
    if b == 12 {
        if p + 2 <= d.len() && (d[p + 1] <= 14 || 17 <= d[p + 1] <= 23 || 30 <= d[p + 1] <= 38) {
            Tok::Op(256 + d[p + 1], p + 2)
        } else {
            Tok::Bad
        }
    } else if b <= 21 {
        Tok::Op(b as int, p + 1)
    } else if b == 28 {
        if p + 3 <= d.len() {
            Tok::Num(i16_at(d, p + 1), p + 3)
        } else {
            Tok::Bad
        }
    } else if b == 29 {
        if p + 5 <= d.len() {
            Tok::Num(i32_at(d, p + 1), p + 5)
        } else {
            Tok::Bad
        }
    } else if b == 30 {
        match real_end(d, p + 1, 0, false, false, 0) {
            Some(e) => Tok::Num(REAL, e),
            None => Tok::Bad,
        }
    } else if 32 <= b <= 246 {
        Tok::Num(b - 139, p + 1)
    } else if 247 <= b <= 250 {
        if p + 2 <= d.len() {
            Tok::Num((b - 247) * 256 + d[p + 1] + 108, p + 2)
        } else {
            Tok::Bad
        }
    } else if 251 <= b <= 254 {
        if p + 2 <= d.len() {
            Tok::Num(-(b - 251) * 256 - d[p + 1] - 108, p + 2)
        } else {
            Tok::Bad
        }
    } else {
        Tok::Bad
    }
}

/// What this specification reads out of a Top DICT or a Font DICT.
/// Offsets and sizes are 0 when the DICT does not give them.
pub struct Dict {
    /// An operator is unknown, is not allowed in this DICT, appears a
    /// second time where it may appear once, or has the wrong operands.
    pub bad: bool,
    /// An operator has been read.
    pub started: bool,
    /// The DICT begins with a ROS operator: the font is CID-keyed.
    pub cid: bool,
    /// The offset of a custom charset; 0 for a predefined one.
    pub charset: int,
    /// The offset of a custom encoding; 0 for a predefined one.
    pub encoding: int,
    pub has_cs: bool,
    pub charstrings: int,
    pub has_priv: bool,
    pub priv_size: int,
    pub priv_off: int,
    pub has_fda: bool,
    pub fdarray: int,
    pub has_fds: bool,
    pub fdselect: int,
}

pub open spec fn dict_empty() -> Dict {
    Dict {
        bad: false,
        started: false,
        cid: false,
        charset: 0,
        encoding: 0,
        has_cs: false,
        charstrings: 0,
        has_priv: false,
        priv_size: 0,
        priv_off: 0,
        has_fda: false,
        fdarray: 0,
        has_fds: false,
        fdselect: 0,
    }
}

/// `v` is an integer and a string id that exists: `sm` is the largest.
pub open spec fn sid_ok(v: int, sm: int) -> bool {
    v != REAL && 0 <= v <= sm
}

/// `v` is an integer and an offset below `len`.
pub open spec fn off_ok(v: int, len: int) -> bool {
    v != REAL && 0 <= v < len
}

/// `st` with the DICT marked bad if `c` does not hold.
pub open spec fn need(st: Dict, c: bool) -> Dict {
    Dict { bad: st.bad || !c, started: true, ..st }
}

/// `st` after operator `op` of a Top DICT (`fd` false) or a Font DICT
/// (`fd` true) is applied to `n` operands whose top three are `c`, `a`
/// and `b` (the top). `sm` is the largest string id and `len` the length
/// of the table.
///
/// Stricter than OTS: a Font DICT may not hold the operators that describe
/// the whole font (charset, Encoding, ROS and the CID operators), and no
/// DICT may hold two Private operators or two custom encodings.
pub open spec fn dict_apply(
    st: Dict,
    fd: bool,
    sm: int,
    len: int,
    op: int,
    n: int,
    c: int,
    a: int,
    b: int,
) -> Dict {
    if op == 0 || op == 1 || op == 2 || op == 3 || op == 4 || op == 256 || op == 256 + 21 || op
        == 256 + 22 || op == 256 + 38 {
        // version, Notice, FullName, FamilyName, Weight, Copyright,
        // PostScript, BaseFontName, FontName: one string id
        need(st, n == 1 && sid_ok(b, sm))
    } else if op == 5 || op == 14 || op == 256 + 7 || op == 256 + 23 {
        // FontBBox, XUID, FontMatrix, BaseFontBlend: arrays
        need(st, n >= 1)
    } else if op == 13 || op == 256 + 2 || op == 256 + 3 || op == 256 + 4 || op == 256 + 5 || op
        == 256 + 8 || op == 256 + 20 {
        // UniqueID, ItalicAngle, UnderlinePosition, UnderlineThickness,
        // PaintType, StrokeWidth, SyntheticBase: one number
        need(st, n == 1)
    } else if 256 + 31 <= op <= 256 + 35 {
        // CIDFontVersion, CIDFontRevision, CIDFontType, CIDCount, UIDBase
        need(st, n == 1 && st.cid && !fd)
    } else if op == 256 + 6 {
        // CharstringType: must be 2
        need(st, n == 1 && b == 2)
    } else if op == 256 + 1 {
        // isFixedPitch
        need(st, n == 1 && (b == 0 || b == 1))
    } else if op == 15 {
        // charset: 0, 1 and 2 are the predefined ones
        if !fd && n == 1 && 0 <= b <= 2 {
            need(st, true)
        } else {
            Dict { charset: b, ..need(st, !fd && n == 1 && off_ok(b, len) && st.charset == 0) }
        }
    } else if op == 16 {
        // Encoding: 0 and 1 are the predefined ones
        if !fd && n == 1 && 0 <= b <= 1 {
            need(st, true)
        } else {
            Dict { encoding: b, ..need(st, !fd && n == 1 && off_ok(b, len) && st.encoding == 0) }
        }
    } else if op == 17 {
        Dict {
            has_cs: true,
            charstrings: b,
            ..need(st, !fd && n == 1 && off_ok(b, len) && !st.has_cs)
        }
    } else if op == 18 {
        // Private: size and offset
        Dict {
            has_priv: true,
            priv_size: a,
            priv_off: b,
            ..need(
                st,
                n == 2 && a != REAL && b != REAL && 0 <= a < len && 0 <= b <= len && a + b <= len
                    && !st.has_priv,
            )
        }
    } else if op == 256 + 30 {
        // ROS: registry and ordering are string ids; must come first
        Dict { cid: true, ..need(st, !fd && !st.started && n == 3 && sid_ok(c, sm) && sid_ok(a, sm)) }
    } else if op == 256 + 36 {
        Dict { has_fda: true, fdarray: b, ..need(st, !fd && n == 1 && off_ok(b, len) && !st.has_fda) }
    } else if op == 256 + 37 {
        Dict {
            has_fds: true,
            fdselect: b,
            ..need(st, !fd && n == 1 && off_ok(b, len) && !st.has_fds)
        }
    } else {
        need(st, false)
    }
}

/// Reads the DICT `d` from `p` to its end. `n` operands are waiting for
/// an operator, the top three being `c`, `a` and `b`. `None` if a token is
/// malformed, more than 47 operands pile up, or operands are left over at
/// the end.
pub open spec fn dict_scan(
    d: Seq<u8>,
    fd: bool,
    sm: int,
    len: int,
    p: int,
    n: int,
    c: int,
    a: int,
    b: int,
    st: Dict,
) -> Option<Dict>
    decreases d.len() - p,
{
    if p < 0 || p > d.len() {
        None
    } else if p == d.len() {
        if n == 0 {
            Some(st)
        } else {
            None
        }
    } else {
        match dict_tok(d, p) {
            Tok::Num(v, q) => if n < 47 && p < q <= d.len() {
                dict_scan(d, fd, sm, len, q, n + 1, a, b, v, st)
            } else {
                None
            },
            Tok::Op(op, q) => if p < q <= d.len() {
                dict_scan(d, fd, sm, len, q, 0, 0, 0, 0, dict_apply(st, fd, sm, len, op, n, c, a, b))
            } else {
                None
            },
            Tok::Bad => None,
        }
    }
}

pub open spec fn dict_read(d: Seq<u8>, fd: bool, sm: int, len: int) -> Option<Dict> {
    dict_scan(d, fd, sm, len, 0, 0, 0, 0, 0, dict_empty())
}

/// What this specification reads out of a Private DICT.
pub struct Priv {
    /// As [`Dict::bad`].
    pub bad: bool,
    pub has_subrs: bool,
    /// The offset of the local subroutines, from the start of the DICT.
    pub subrs: int,
}

/// `st` after operator `op` of a Private DICT is applied to `n` operands
/// whose top is `b`.
pub open spec fn priv_apply(st: Priv, op: int, n: int, b: int) -> Priv {
    if op == 6 || op == 7 || op == 8 || op == 9 {
        // BlueValues, OtherBlues, FamilyBlues, FamilyOtherBlues: pairs
        Priv { bad: st.bad || n % 2 != 0, ..st }
    } else if op == 256 + 12 || op == 256 + 13 {
        // StemSnapH, StemSnapV: arrays
        Priv { bad: st.bad || n < 1, ..st }
    } else if op == 10 || op == 11 || op == 20 || op == 21 || op == 256 + 9 || op == 256 + 10 || op
        == 256 + 11 || op == 256 + 17 || op == 256 + 18 || op == 256 + 19 {
        // StdHW, StdVW, defaultWidthX, nominalWidthX, BlueScale,
        // BlueShift, BlueFuzz, LanguageGroup, ExpansionFactor,
        // initialRandomSeed: one number
        Priv { bad: st.bad || n != 1, ..st }
    } else if op == 19 {
        // Subrs
        Priv {
            bad: st.bad || !(n == 1 && b != REAL && 0 <= b < 0x4000_0000 && !st.has_subrs),
            has_subrs: true,
            subrs: b,
        }
    } else if op == 256 + 14 {
        // ForceBold
        Priv { bad: st.bad || !(n == 1 && (b == 0 || b == 1)), ..st }
    } else {
        Priv { bad: true, ..st }
    }
}

/// As [`dict_scan`], for a Private DICT.
pub open spec fn priv_scan(d: Seq<u8>, p: int, n: int, b: int, st: Priv) -> Option<Priv>
    decreases d.len() - p,
{
    if p < 0 || p > d.len() {
        None
    } else if p == d.len() {
        if n == 0 {
            Some(st)
        } else {
            None
        }
    } else {
        match dict_tok(d, p) {
            Tok::Num(v, q) => if n < 47 && p < q <= d.len() {
                priv_scan(d, q, n + 1, v, st)
            } else {
                None
            },
            Tok::Op(op, q) => if p < q <= d.len() {
                priv_scan(d, q, 0, 0, priv_apply(st, op, n, b))
            } else {
                None
            },
            Tok::Bad => None,
        }
    }
}

pub open spec fn priv_read(d: Seq<u8>) -> Option<Priv> {
    priv_scan(d, 0, 0, 0, Priv { bad: false, has_subrs: false, subrs: 0 })
}

// ---------------------------------------------------------------------
// Charset, Encoding, FDSelect, Private DICT
// ---------------------------------------------------------------------
/// Ranges of a format 1 (`w` = 1) or 2 (`w` = 2) charset starting at `p`
/// cover exactly `left` more glyphs, inside the table, and name no string
/// id (or CID) above `sm`.
pub open spec fn charset_ranges(t: Seq<u8>, p: int, w: int, left: int, sm: int) -> bool
    decreases left,
{
    if left <= 0 {
        left == 0
    } else if p < 0 || p + 2 + w > t.len() || 1 + un_at(t, p + 2, w) > left || u16_at(t, p) + un_at(
        t,
        p + 2,
        w,
    ) > sm {
        false
    } else {
        charset_ranges(t, p + 2 + w, w, left - 1 - un_at(t, p + 2, w), sm)
    }
}

/// The string id (or CID) that the format 0 charset at `p` gives glyph
/// `j + 1`.
pub open spec fn charset_sid(t: Seq<u8>, p: int, j: int) -> int {
    u16_at(t, p + 1 + 2 * j)
}

/// The charset at `p` names glyphs 1 to `ng - 1` and nothing more, by
/// string ids (or CIDs) no larger than `sm`.
pub open spec fn wf_charset(t: Seq<u8>, p: int, ng: int, sm: int) -> bool {
    &&& 0 <= p < t.len()
    &&& if t[p] == 0 {
        &&& p + 1 + 2 * (ng - 1) <= t.len()
        &&& forall|j: int| 0 <= j < ng - 1 ==> #[trigger] charset_sid(t, p, j) <= sm
    } else if t[p] == 1 {
        charset_ranges(t, p + 1, 1, ng - 1, sm)
    } else if t[p] == 2 {
        charset_ranges(t, p + 1, 2, ng - 1, sm)
    } else {
        false
    }
}

/// The encoding at `p` lies inside the table and has no supplement.
pub open spec fn wf_encoding(t: Seq<u8>, p: int) -> bool {
    &&& 0 <= p
    &&& p + 2 <= t.len()
    &&& (t[p] == 0 || t[p] == 1)
    &&& p + 2 + (if t[p] == 0 {
        t[p + 1] as int
    } else {
        2 * t[p + 1]
    }) <= t.len()
}

/// Range `k` of a format 3 FDSelect at `p`.
pub open spec fn fds_range_ok(t: Seq<u8>, p: int, k: int, nfd: int) -> bool {
    let r = p + 3 + 3 * k;
    &&& u16_at(t, r) < u16_at(t, r + 3)
    &&& t[r + 2] < nfd
}

/// The FDSelect at `p` gives every one of the `ng` glyphs a Font DICT
/// below `nfd`.
pub open spec fn wf_fdselect(t: Seq<u8>, p: int, ng: int, nfd: int) -> bool {
    &&& 0 <= p < t.len()
    &&& if t[p] == 0 {
        &&& p + 1 + ng <= t.len()
        &&& forall|g: int| 0 <= g < ng ==> (#[trigger] t[p + 1 + g]) < nfd
    } else {
        let n = u16_at(t, p + 1);
        &&& t[p] == 3
        &&& p + 3 <= t.len()
        &&& n >= 1
        &&& p + 5 + 3 * n <= t.len()
        &&& u16_at(t, p + 3) == 0
        &&& u16_at(t, p + 3 + 3 * n) == ng
        &&& forall|k: int| 0 <= k < n ==> #[trigger] fds_range_ok(t, p, k, nfd)
    }
}

/// The Private DICT at `off`, `size` bytes long, lies inside the table and
/// is a good one, and its local subroutines, if any, are a well-formed
/// INDEX.
pub open spec fn wf_private(t: Seq<u8>, size: int, off: int) -> bool {
    &&& 0 <= size
    &&& 0 <= off
    &&& off + size <= t.len()
    &&& match priv_read(t.subrange(off, off + size)) {
        Some(d) => !d.bad && (d.has_subrs ==> d.subrs > 0 && wf_index(t, off + d.subrs)),
        None => false,
    }
}

/// Font DICT `i` of the FDArray at `fa` is a good one and has a
/// well-formed Private DICT.
pub open spec fn wf_fontdict(t: Seq<u8>, fa: int, i: int, sm: int) -> bool {
    match dict_read(index_obj(t, fa, i), true, sm, t.len() as int) {
        Some(d) => !d.bad && d.has_priv && wf_private(t, d.priv_size, d.priv_off),
        None => false,
    }
}

// ---------------------------------------------------------------------
// The table
// ---------------------------------------------------------------------
/// The parts of a CFF table that the Top DICT `d` points to. `sm` is the
/// largest string id.
///
/// Stricter than OTS: a font that is not CID-keyed has no FDArray or
/// FDSelect, and a CID-keyed font has both.
pub open spec fn wf_cff_parts(t: Seq<u8>, d: Dict, ng: int, sm: int) -> bool {
    &&& !d.bad
    &&& ng >= 2
    &&& d.has_cs
    &&& d.charstrings > 0
    &&& wf_index(t, d.charstrings)
    &&& index_count(t, d.charstrings) == ng
    &&& (d.charset == 0 || wf_charset(
        t,
        d.charset,
        ng,
        if d.cid {
            65535
        } else {
            sm
        },
    ))
    &&& (d.encoding == 0 || wf_encoding(t, d.encoding))
    &&& wf_private(t, d.priv_size, d.priv_off)
    &&& if d.cid {
        &&& d.has_fda
        &&& d.fdarray > 0
        &&& wf_index(t, d.fdarray)
        &&& 1 <= index_count(t, d.fdarray) <= 256
        &&& forall|i: int|
            0 <= i < index_count(t, d.fdarray) ==> #[trigger] wf_fontdict(t, d.fdarray, i, sm)
        &&& d.has_fds
        &&& d.fdselect > 0
        &&& wf_fdselect(t, d.fdselect, ng, index_count(t, d.fdarray))
    } else {
        !d.has_fda && !d.has_fds
    }
}

/// Byte `i` of a font name `x` is allowed: printable ASCII other than the
/// PostScript delimiters, or a zero first byte (which marks a deleted
/// font).
pub open spec fn name_byte_ok(x: Seq<u8>, i: int) -> bool {
    ||| (i == 0 && x[i] == 0)
    ||| (33 <= x[i] <= 126 && x[i] != 0x5B && x[i] != 0x5D && x[i] != 0x28 && x[i] != 0x29 && x[i]
        != 0x7B && x[i] != 0x7D && x[i] != 0x3C && x[i] != 0x3E && x[i] != 0x2F && x[i] != 0x25)
}

/// The number of standard strings: string ids below it are predefined.
pub spec const STD_STRINGS: int = 390;

/// A well-formed CFF table for a font of `ng` glyphs: the header, then the
/// Name INDEX with one name, the Top DICT INDEX with one DICT, the String
/// INDEX and the Global Subr INDEX, one after another; everything the
/// Top DICT points to ([`wf_cff_parts`]); and every charstring running
/// cleanly ([`crate::spec_cs::wf_charstrings`]).
pub open spec fn wf_cff(t: Seq<u8>, ng: int) -> bool {
    let name = 4int;
    let top = index_end(t, name);
    let strings = index_end(t, top);
    let gsubrs = index_end(t, strings);
    let sm = index_count(t, strings) + STD_STRINGS;
    &&& t.len() >= 4
    &&& t[0] == 1
    &&& t[1] == 0
    &&& t[2] == 4
    &&& 1 <= t[3] <= 4
    &&& wf_index(t, name)
    &&& index_count(t, name) == 1
    &&& index_obj(t, name, 0).len() <= 127
    &&& (forall|i: int|
        0 <= i < index_obj(t, name, 0).len() ==> #[trigger] name_byte_ok(index_obj(t, name, 0), i))
    &&& wf_index(t, top)
    &&& index_count(t, top) == 1
    &&& wf_index(t, strings)
    &&& index_count(t, strings) < 65000 - STD_STRINGS
    &&& wf_index(t, gsubrs)
    &&& match dict_read(index_obj(t, top, 0), false, sm, t.len() as int) {
        Some(d) => wf_cff_parts(t, d, ng, sm) && crate::spec_cs::wf_charstrings(
            t,
            d,
            gsubrs,
            ng,
            sm,
        ),
        None => false,
    }
}

} // verus!
