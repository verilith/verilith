//! UTS #46 (Unicode IDNA Compatibility Processing), sections 4 to 4.3, over
//! the Unicode 18.0 data of `data`.
//!
//! Two deliberate limits, as in the `idna` crate (and for the reason it
//! gives, whatwg/url#824: Punycode is quadratic): a label whose Punycode part
//! is longer than `DECODE_MAX` bytes is an error, and so is a non-ASCII label
//! longer than `ENCODE_MAX` code points in ToASCII.
#[cfg(verus_only)]
use super::super::unicode::data::ccc;
#[cfg(verus_only)]
use super::super::unicode::spec::nf;
use super::data::*;
#[cfg(verus_only)]
use super::punycode::{decode, encode};
use super::tables::*;
use vstd::prelude::*;

verus! {

pub const DOT: u32 = 0x2E;
pub const HYPHEN: u32 = 0x2D;
pub const ZWNJ: u32 = 0x200C;
pub const ZWJ: u32 = 0x200D;
pub const VIRAMA: u8 = 9;
pub const DECODE_MAX: usize = 2000;
pub const ENCODE_MAX: usize = 1000;

/// The flags of UTS #46 (IgnoreInvalidPunycode is always false).
#[derive(Clone, Copy)]
pub struct Options {
    pub check_hyphens: bool,
    pub check_bidi: bool,
    pub check_joiners: bool,
    pub use_std3_ascii_rules: bool,
    pub transitional: bool,
    pub verify_dns_length: bool,
}

// ---------------------------------------------------------------------------
// Sequences
// ---------------------------------------------------------------------------

/// The first index from `p` on of `sep` in `s`, or `s.len()`.
pub open spec fn find<T>(s: Seq<T>, sep: T, p: int) -> int
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() {
        s.len() as int
    } else if s[p] == sep {
        p
    } else {
        find(s, sep, p + 1)
    }
}

pub proof fn lemma_find<T>(s: Seq<T>, sep: T, p: int)
    requires
        0 <= p <= s.len(),
    ensures
        p <= find(s, sep, p) <= s.len(),
        find(s, sep, p) < s.len() ==> s[find(s, sep, p)] == sep,
        forall|k: int| p <= k < find(s, sep, p) ==> s[k] != sep,
    decreases s.len() - p,
{
    if p < s.len() && s[p] != sep {
        lemma_find(s, sep, p + 1);
    }
}

/// `s[p..]` split at each `sep`: one more piece than there are separators.
pub open spec fn split_from<T>(s: Seq<T>, sep: T, p: int) -> Seq<Seq<T>>
    decreases s.len() - p,
    via split_from_decreases::<T>
{
    let d = find(s, sep, p);
    if p < 0 || p > s.len() || d >= s.len() {
        seq![s.subrange(p, s.len() as int)]
    } else {
        seq![s.subrange(p, d)] + split_from(s, sep, d + 1)
    }
}

#[via_fn]
proof fn split_from_decreases<T>(s: Seq<T>, sep: T, p: int) {
    if 0 <= p <= s.len() {
        lemma_find(s, sep, p);
    }
}

pub open spec fn split<T>(s: Seq<T>, sep: T) -> Seq<Seq<T>> {
    split_from(s, sep, 0)
}

/// The pieces of `ls` with `sep` between them.
pub open spec fn join<T>(ls: Seq<Seq<T>>, sep: T) -> Seq<T>
    decreases ls.len(),
{
    if ls.len() == 0 {
        seq![]
    } else if ls.len() == 1 {
        ls[0]
    } else {
        join(ls.drop_last(), sep).push(sep) + ls.last()
    }
}

pub open spec fn all_ascii(l: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < l.len() ==> #[trigger] l[k] < 0x80
}

pub open spec fn narrow(l: Seq<u32>) -> Seq<u8> {
    Seq::new(l.len(), |k: int| l[k] as u8)
}

pub open spec fn widen(l: Seq<u8>) -> Seq<u32> {
    Seq::new(l.len(), |k: int| l[k] as u32)
}

pub open spec fn starts_xn(l: Seq<u32>) -> bool {
    l.len() >= 4 && l[0] == 0x78 && l[1] == 0x6E && l[2] == HYPHEN && l[3] == HYPHEN
}

// ---------------------------------------------------------------------------
// 4 Processing, steps 1 and 2: map and normalize
// ---------------------------------------------------------------------------

pub open spec fn map_one(c: u32, transitional: bool) -> Seq<u32> {
    let st = status(c);
    if transitional && c == 0x1E9E {
        // Since Unicode 15.1, U+1E9E maps to U+00DF, and transitional
        // processing maps it to "ss" as before.
        seq![0x73u32, 0x73]
    } else if st == STATUS_IGNORED {
        seq![]
    } else if st == STATUS_MAPPED || (st == STATUS_DEVIATION && transitional) {
        mapping(c)
    } else {
        // Valid, deviation (nontransitional) and disallowed code points are
        // kept; the validity criteria reject the disallowed ones.
        seq![c]
    }
}

pub open spec fn map_all(cs: Seq<u32>, transitional: bool) -> Seq<u32>
    decreases cs.len(),
{
    if cs.len() == 0 {
        seq![]
    } else {
        map_all(cs.drop_last(), transitional) + map_one(cs.last(), transitional)
    }
}

// ---------------------------------------------------------------------------
// 4.1 Validity criteria
// ---------------------------------------------------------------------------

/// Criteria 6 and 7 for one code point.
pub open spec fn status_ok(c: u32, transitional: bool, std3: bool) -> bool {
    (status(c) == STATUS_VALID || (!transitional && status(c) == STATUS_DEVIATION)) && (std3 && c < 0x80 ==> (
    0x61 <= c <= 0x7A || 0x30 <= c <= 0x39 || c == HYPHEN))
}

pub open spec fn left_joining(c: u32) -> bool {
    joining(c) == JT_L || joining(c) == JT_D
}

pub open spec fn right_joining(c: u32) -> bool {
    joining(c) == JT_R || joining(c) == JT_D
}

/// A left- or dual-joining character before `l[j + 1]`, past transparent ones.
pub open spec fn joins_left(l: Seq<u32>, j: int) -> bool
    decreases j + 1,
{
    if j < 0 || j >= l.len() {
        false
    } else if left_joining(l[j]) {
        true
    } else if joining(l[j]) == JT_T {
        joins_left(l, j - 1)
    } else {
        false
    }
}

/// A right- or dual-joining character from `l[j]` on, past transparent ones.
pub open spec fn joins_right(l: Seq<u32>, j: int) -> bool
    decreases l.len() - j,
{
    if j < 0 || j >= l.len() {
        false
    } else if right_joining(l[j]) {
        true
    } else if joining(l[j]) == JT_T {
        joins_right(l, j + 1)
    } else {
        false
    }
}

/// RFC 5892 Appendix A.1 and A.2 for `l[k]`.
pub open spec fn joiner_ok(l: Seq<u32>, k: int) -> bool {
    (l[k] == ZWNJ ==> k > 0 && (ccc(l[k - 1]) == VIRAMA || (joins_left(l, k - 1) && joins_right(l, k + 1)))) && (
    l[k] == ZWJ ==> k > 0 && ccc(l[k - 1]) == VIRAMA)
}

/// The validity criteria of 4.1, but for criterion 8 (CheckBidi), which
/// `bidi_error` checks over the whole domain name.
pub open spec fn valid(l: Seq<u32>, o: Options, transitional: bool) -> bool {
    &&& nf(l, true, false) == l
    &&& o.check_hyphens ==> !(l.len() >= 4 && l[2] == HYPHEN && l[3] == HYPHEN)
    &&& o.check_hyphens ==> !(l.len() > 0 && (l[0] == HYPHEN || l.last() == HYPHEN))
    &&& !o.check_hyphens ==> !starts_xn(l)
    &&& !l.contains(DOT)
    &&& !(l.len() > 0 && is_mark(l[0]))
    &&& forall|k: int| 0 <= k < l.len() ==> status_ok(#[trigger] l[k], transitional, o.use_std3_ascii_rules)
    &&& o.check_joiners ==> forall|k: int| 0 <= k < l.len() ==> #[trigger] joiner_ok(l, k)
}

// ---------------------------------------------------------------------------
// Criterion 8: RFC 5893 section 2
// ---------------------------------------------------------------------------

pub open spec fn rtl(b: u32) -> bool {
    b == BIDI_R || b == BIDI_AL || b == BIDI_AN
}

pub open spec fn ltr_allowed(b: u32) -> bool {
    b == BIDI_L || b == BIDI_EN || b == BIDI_ES || b == BIDI_CS || b == BIDI_ET || b == BIDI_ON || b == BIDI_BN
        || b == BIDI_NSM
}

pub open spec fn rtl_allowed(b: u32) -> bool {
    b == BIDI_R || b == BIDI_AL || b == BIDI_AN || b == BIDI_EN || b == BIDI_ES || b == BIDI_CS || b == BIDI_ET || b
        == BIDI_ON || b == BIDI_BN || b == BIDI_NSM
}

/// The last character of `l[..=j]` that is not a nonspacing mark, or -1.
pub open spec fn last_non_nsm(l: Seq<u32>, j: int) -> int
    decreases j + 1,
{
    if j < 0 || j >= l.len() {
        -1
    } else if bidi(l[j]) == BIDI_NSM {
        last_non_nsm(l, j - 1)
    } else {
        j
    }
}

pub open spec fn has_bidi(l: Seq<u32>, b: u32) -> bool {
    exists|k: int| 0 <= k < l.len() && bidi(#[trigger] l[k]) == b
}

/// The six rules for a (nonempty) label of a Bidi domain name.
pub open spec fn bidi_ok(l: Seq<u32>) -> bool {
    let f = bidi(l[0]);
    let e = bidi(l[last_non_nsm(l, l.len() - 1)]);
    if f == BIDI_L {
        (forall|k: int| 0 <= k < l.len() ==> ltr_allowed(bidi(#[trigger] l[k]))) && (e == BIDI_L || e == BIDI_EN)
    } else if f == BIDI_R || f == BIDI_AL {
        (forall|k: int| 0 <= k < l.len() ==> rtl_allowed(bidi(#[trigger] l[k]))) && (e == BIDI_R || e == BIDI_AL || e
            == BIDI_EN || e == BIDI_AN) && !(has_bidi(l, BIDI_EN) && has_bidi(l, BIDI_AN))
    } else {
        false
    }
}

/// A Bidi domain name has a character of class R, AL or AN.
pub open spec fn bidi_domain(ls: Seq<Seq<u32>>) -> bool {
    exists|i: int, k: int| 0 <= i < ls.len() && 0 <= k < ls[i].len() && rtl(bidi(#[trigger] ls[i][k]))
}

pub open spec fn bidi_error(ls: Seq<Seq<u32>>, o: Options) -> bool {
    o.check_bidi && bidi_domain(ls) && exists|i: int| 0 <= i < ls.len() && ls[i].len() > 0 && !bidi_ok(#[trigger] ls[i])
}

// ---------------------------------------------------------------------------
// 4 Processing, steps 3 and 4: break and convert/validate
// ---------------------------------------------------------------------------

/// A label after conversion, and whether it has an error.
pub open spec fn convert(l: Seq<u32>, o: Options) -> (Seq<u32>, bool) {
    if starts_xn(l) {
        let p = l.skip(4);
        if !all_ascii(p) || p.len() > DECODE_MAX {
            (l, true)
        } else {
            match decode(narrow(p)) {
                None => (l, true),
                Some(u) => (u, u.len() == 0 || all_ascii(u) || !valid(u, o, false)),
            }
        }
    } else {
        (l, !valid(l, o, o.transitional))
    }
}

/// The labels after mapping, normalization and breaking.
pub open spec fn labels(cs: Seq<u32>, o: Options) -> Seq<Seq<u32>> {
    split(nf(map_all(cs, o.transitional), true, false), DOT)
}

/// The labels after conversion.
pub open spec fn converted(cs: Seq<u32>, o: Options) -> Seq<Seq<u32>> {
    labels(cs, o).map_values(|l: Seq<u32>| convert(l, o).0)
}

/// Whether processing records an error.
pub open spec fn process_error(cs: Seq<u32>, o: Options) -> bool {
    (exists|i: int| 0 <= i < labels(cs, o).len() && (#[trigger] convert(labels(cs, o)[i], o)).1) || bidi_error(
        converted(cs, o),
        o,
    )
}

/// Processing (4): the result, and whether there was an error. ToUnicode
/// (4.3) is the same.
pub open spec fn process(cs: Seq<u32>, o: Options) -> (Seq<u32>, bool) {
    (join(converted(cs, o), DOT), process_error(cs, o))
}

// ---------------------------------------------------------------------------
// 4.2 ToASCII
// ---------------------------------------------------------------------------

pub open spec fn xn_prefix() -> Seq<u8> {
    seq![0x78u8, 0x6E, 0x2D, 0x2D]
}

/// One label of ToASCII's result.
pub open spec fn ascii_label(l: Seq<u32>) -> Option<Seq<u8>> {
    if all_ascii(l) {
        Some(narrow(l))
    } else if l.len() > ENCODE_MAX {
        None
    } else {
        match encode(l) {
            None => None,
            Some(p) => Some(xn_prefix() + p),
        }
    }
}

/// The labels but a trailing root label.
pub open spec fn strip_root(ls: Seq<Seq<u8>>) -> Seq<Seq<u8>> {
    if ls.len() > 1 && ls.last().len() == 0 { ls.drop_last() } else { ls }
}

pub open spec fn labels_len_ok(ls: Seq<Seq<u8>>) -> bool {
    forall|i: int| 0 <= i < ls.len() ==> 1 <= (#[trigger] ls[i]).len() <= 63
}

/// Step 3: the lengths. The total excludes a trailing root label, but
/// every label, the root label too, must have 1 to 63 bytes.
pub open spec fn dns_length_ok(ls: Seq<Seq<u8>>) -> bool {
    1 <= join(strip_root(ls), 0x2Eu8).len() <= 253 && labels_len_ok(ls)
}

pub open spec fn to_ascii(cs: Seq<u32>, o: Options) -> Option<Seq<u8>> {
    let ls = converted(cs, o);
    if process_error(cs, o) || exists|i: int| 0 <= i < ls.len() && (#[trigger] ascii_label(ls[i])) is None {
        None
    } else {
        let als = ls.map_values(|l: Seq<u32>| ascii_label(l)->0);
        if o.verify_dns_length && !dns_length_ok(als) {
            None
        } else {
            Some(join(als, 0x2Eu8))
        }
    }
}

} // verus!
