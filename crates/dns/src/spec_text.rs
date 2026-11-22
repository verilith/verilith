//! Specification of the presentation (text) format of names (trusted, like
//! `spec`), escaped as c-ares does: labels joined by `.`, the bytes
//! `"().;@$\` backslash-escaped, bytes outside 0x20..=0x7e as `\DDD`, and the
//! root name as the empty string. Parsing accepts `\DDD`, `\c`, and an
//! optional trailing dot (RFC 1035 §5.1).
#[allow(unused_imports)]
use crate::spec::*;
#[cfg(verus_only)]
pub use verilith_core::num::is_digit;
use vstd::prelude::*;

verus! {

pub open spec fn is_special(c: u8) -> bool {
    c == 34 || c == 46 || c == 59 || c == 92 || c == 40 || c == 41 || c == 64 || c == 36
}

pub open spec fn esc_byte(c: u8) -> Seq<u8> {
    if c < 0x20 || c > 0x7e {
        seq![92u8, (48 + c / 100) as u8, (48 + (c % 100) / 10) as u8, (48 + c % 10) as u8]
    } else if is_special(c) {
        seq![92u8, c]
    } else {
        seq![c]
    }
}

/// The escaped text of `l[j..]`.
pub open spec fn esc_from(l: Seq<u8>, j: int) -> Seq<u8>
    decreases l.len() - j,
{
    if j < 0 || j >= l.len() {
        Seq::empty()
    } else {
        esc_byte(l[j]) + esc_from(l, j + 1)
    }
}

/// The text of labels `n[k..]`, each preceded by `.` except the first label.
pub open spec fn pres_from(n: SpecName, k: int) -> Seq<u8>
    decreases n.len() - k,
{
    if k < 0 || k >= n.len() {
        Seq::empty()
    } else {
        (if k > 0 {
            seq![46u8]
        } else {
            Seq::empty()
        }) + esc_from(n[k], 0) + pres_from(n, k + 1)
    }
}

pub open spec fn pres_name(n: SpecName) -> Seq<u8> {
    pres_from(n, 0)
}

/// Reads one label's text at `i`, up to a `.` or the end.
pub open spec fn text_label(s: Seq<u8>, i: int) -> Option<(Seq<u8>, int)>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() || s[i] == 46 {
        Some((Seq::empty(), i))
    } else if s[i] == 92 {
        if i + 3 < s.len() && is_digit(s[i + 1]) && is_digit(s[i + 2]) && is_digit(s[i + 3]) {
            let v = (s[i + 1] - 48) * 100 + (s[i + 2] - 48) * 10 + (s[i + 3] - 48);
            if v > 255 {
                None
            } else {
                match text_label(s, i + 4) {
                    Some((rest, e)) => Some((seq![v as u8] + rest, e)),
                    None => None,
                }
            }
        } else if i + 1 < s.len() {
            match text_label(s, i + 2) {
                Some((rest, e)) => Some((seq![s[i + 1]] + rest, e)),
                None => None,
            }
        } else {
            None
        }
    } else {
        match text_label(s, i + 1) {
            Some((rest, e)) => Some((seq![s[i]] + rest, e)),
            None => None,
        }
    }
}

/// Reads labels at `i` to the end of `s`, allowing one trailing dot.
pub open spec fn text_labels(s: Seq<u8>, i: int) -> Option<SpecName>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        None
    } else {
        match text_label(s, i) {
            Some((l, j)) => if l.len() == 0 || l.len() > 63 || j <= i {
                None
            } else if j >= s.len() || j + 1 == s.len() {
                Some(seq![l])
            } else {
                match text_labels(s, j + 1) {
                    Some(rest) => Some(seq![l] + rest),
                    None => None,
                }
            },
            None => None,
        }
    }
}

/// Parses a presentation-format name. `""` and `"."` are the root.
pub open spec fn parse_text_name(s: Seq<u8>) -> Option<SpecName> {
    if s.len() == 0 || s =~= seq![46u8] {
        Some(Seq::empty())
    } else {
        match text_labels(s, 0) {
            Some(n) => if ser_name(n).len() <= MAX_NAME_WIRE_LEN {
                Some(n)
            } else {
                None
            },
            None => None,
        }
    }
}

} // verus!
