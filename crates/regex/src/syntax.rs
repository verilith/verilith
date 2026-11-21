//! The pattern syntax, as mathematics: RE2's.
//!
//! `parse(pat)` is the regular expression a pattern stands for, or `None`
//! if the pattern is not well-formed. It is written as a reference parser:
//! each function reads the pattern from a position and says what it found
//! and where it stopped. The executable parser is proven to compute it.
use crate::data::*;
use crate::spec::*;
use verilith_core::utf8::*;
use vstd::prelude::*;

verus! {

/// `(?i)`, `(?m)`, `(?s)`, `(?U)`.
#[derive(Clone, Copy)]
pub struct Flags {
    /// Letters match either case.
    pub i: bool,
    /// `^` and `$` match at line ends.
    pub m: bool,
    /// `.` matches `\n`.
    pub s: bool,
    /// Repetitions are lazy unless followed by `?`.
    pub u: bool,
}

/// A parsed piece: its expression, and the largest product of nested
/// `{n,m}` counts in it (which may not exceed 1000).
pub ghost struct It {
    pub re: Re,
    pub rep: nat,
}

/// What a pattern's groups have used up so far: how many there are, and
/// the named ones.
pub ghost struct St {
    pub ng: nat,
    pub names: Seq<(Seq<u8>, nat)>,
}

pub ghost struct Out {
    pub it: It,
    pub pos: int,
    pub fl: Flags,
    pub st: St,
}

/// A parsed pattern: group 0 around the whole expression, the number of
/// groups counting group 0, and the named groups.
pub ghost struct Pat {
    pub re: Re,
    pub ngroups: nat,
    pub names: Seq<(Seq<u8>, nat)>,
}

/// Byte `p` of the pattern is `b`.
pub open spec fn at(pat: Seq<u8>, p: int, b: u8) -> bool {
    0 <= p < pat.len() && pat[p] == b
}

pub open spec fn is_digit(b: u8) -> bool {
    0x30 <= b <= 0x39
}

pub open spec fn is_alnum(b: u8) -> bool {
    is_digit(b) || (0x61 <= b <= 0x7A) || (0x41 <= b <= 0x5A)
}

/// The character at `p`: its code point and length; `(u32::MAX, 1)` where
/// no character starts.
pub open spec fn chr(pat: Seq<u8>, p: int) -> (u32, int) {
    match dec(pat, p) {
        Some((c, l)) => (c, l),
        None => (u32::MAX, 1),
    }
}

/// How much of the pattern is left at `p`.
pub open spec fn left(pat: Seq<u8>, p: int) -> int {
    if p < pat.len() {
        pat.len() - p
    } else {
        0
    }
}

/// The first position at or after `p` holding `b`, or the length.
pub open spec fn find(pat: Seq<u8>, p: int, b: u8) -> int
    decreases pat.len() - p,
{
    if p < 0 || p >= pat.len() {
        if p < 0 { p } else { pat.len() as int }
    } else if pat[p] == b {
        p
    } else {
        find(pat, p + 1, b)
    }
}

// ---------------------------------------------------------------------------
// Escapes
// ---------------------------------------------------------------------------

pub open spec fn hexval(c: u32) -> Option<u32> {
    if 0x30 <= c <= 0x39 {
        Some((c - 0x30) as u32)
    } else if 0x61 <= c <= 0x66 {
        Some((c - 0x61 + 10) as u32)
    } else if 0x41 <= c <= 0x46 {
        Some((c - 0x41 + 10) as u32)
    } else {
        None
    }
}

pub open spec fn is_octal(pat: Seq<u8>, p: int) -> bool {
    0 <= p < pat.len() && 0x30 <= pat[p] <= 0x37
}

/// The hex digits of `\x{...}` from `p`, with `code` and `nhex` digits
/// read so far, up to the closing brace.
pub open spec fn hex_run(pat: Seq<u8>, p: int, code: u32, nhex: nat) -> Option<(u32, int)>
    decreases pat.len() - p,
{
    if p < 0 || p >= pat.len() {
        None
    } else {
        let (d, ld) = chr(pat, p);
        match hexval(d) {
            Some(v) => if code * 16 + v > MAXCP {
                None
            } else {
                hex_run(pat, p + ld, (code * 16 + v) as u32, nhex + 1)
            },
            None => if d != 0x7D || nhex == 0 {
                None
            } else {
                Some((code, p + ld))
            },
        }
    }
}

/// An escape that stands for one code point; `pos` holds the backslash.
/// Gives the code point and where the escape ends.
pub open spec fn escape(pat: Seq<u8>, pos: int) -> Option<(u32, int)> {
    let n = pat.len() as int;
    if pos + 1 >= n {
        None
    } else {
        let (c, l) = chr(pat, pos + 1);
        let p = pos + 1 + l;
        if 0x31 <= c <= 0x37 && !is_octal(pat, p) {
            // A backreference.
            None
        } else if 0x30 <= c <= 0x37 {
            // Up to three octal digits.
            let c0 = (c - 0x30) as u32;
            if is_octal(pat, p) {
                let c1 = (c0 * 8 + (pat[p] - 0x30)) as u32;
                if is_octal(pat, p + 1) {
                    Some(((c1 * 8 + (pat[p + 1] - 0x30)) as u32, p + 2))
                } else {
                    Some((c1, p + 1))
                }
            } else {
                Some((c0, p))
            }
        } else if c == 0x78 {
            // \xHH or \x{H...}
            if p >= n {
                None
            } else {
                let (c1, l1) = chr(pat, p);
                let p1 = p + l1;
                if c1 == 0x7B {
                    hex_run(pat, p1, 0, 0)
                } else if p1 >= n {
                    None
                } else {
                    let (c2, l2) = chr(pat, p1);
                    match (hexval(c1), hexval(c2)) {
                        (Some(a), Some(b)) => Some(((a * 16 + b) as u32, p1 + l2)),
                        _ => None,
                    }
                }
            }
        } else if c == 0x6E {
            Some((0x0A, p))
        } else if c == 0x72 {
            Some((0x0D, p))
        } else if c == 0x74 {
            Some((0x09, p))
        } else if c == 0x61 {
            Some((0x07, p))
        } else if c == 0x66 {
            Some((0x0C, p))
        } else if c == 0x76 {
            Some((0x0B, p))
        } else if c < 0x80 && !is_alnum(c as u8) {
            // Punctuation stands for itself.
            Some((c, p))
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Classes
// ---------------------------------------------------------------------------

/// What a class item denotes: `base`, with case variants if `fold`, then
/// complemented if `neg`.
pub open spec fn item(base: ISet<u32>, neg: bool, fold: bool) -> ISet<u32> {
    let c = if fold {
        cs_fold(base)
    } else {
        base
    };
    if neg {
        cs_neg(c)
    } else {
        c
    }
}

/// A literal character under the flags.
pub open spec fn lit(c: u32, fl: Flags) -> ISet<u32> {
    item(cs_range(c, c), false, fl.i)
}

pub open spec fn perl_d() -> Seq<(u32, u32)> {
    seq![(0x30u32, 0x39u32)]
}

pub open spec fn perl_s() -> Seq<(u32, u32)> {
    seq![(0x09u32, 0x0Au32), (0x0Cu32, 0x0Du32), (0x20u32, 0x20u32)]
}

pub open spec fn perl_w() -> Seq<(u32, u32)> {
    seq![(0x30u32, 0x39u32), (0x41u32, 0x5Au32), (0x5Fu32, 0x5Fu32), (0x61u32, 0x7Au32)]
}

/// `\d \s \w \D \S \W` at `pos`.
pub open spec fn perl(pat: Seq<u8>, pos: int, fl: Flags) -> Option<ISet<u32>> {
    if !at(pat, pos, 0x5C) || pos + 1 >= pat.len() {
        None
    } else {
        let b = pat[pos + 1];
        if b == 0x64 {
            Some(item(cs_ranges(perl_d()), false, fl.i))
        } else if b == 0x44 {
            Some(item(cs_ranges(perl_d()), true, fl.i))
        } else if b == 0x73 {
            Some(item(cs_ranges(perl_s()), false, fl.i))
        } else if b == 0x53 {
            Some(item(cs_ranges(perl_s()), true, fl.i))
        } else if b == 0x77 {
            Some(item(cs_ranges(perl_w()), false, fl.i))
        } else if b == 0x57 {
            Some(item(cs_ranges(perl_w()), true, fl.i))
        } else {
            None
        }
    }
}

/// The POSIX class `name` (what stands between `[:` and `:]`).
pub open spec fn posix(name: Seq<u8>) -> Option<Seq<(u32, u32)>> {
    if name == seq![0x61u8, 0x6Cu8, 0x6Eu8, 0x75u8, 0x6Du8] {
        // alnum
        Some(seq![(0x30u32, 0x39u32), (0x41u32, 0x5Au32), (0x61u32, 0x7Au32)])
    } else if name == seq![0x61u8, 0x6Cu8, 0x70u8, 0x68u8, 0x61u8] {
        // alpha
        Some(seq![(0x41u32, 0x5Au32), (0x61u32, 0x7Au32)])
    } else if name == seq![0x61u8, 0x73u8, 0x63u8, 0x69u8, 0x69u8] {
        // ascii
        Some(seq![(0x00u32, 0x7Fu32)])
    } else if name == seq![0x62u8, 0x6Cu8, 0x61u8, 0x6Eu8, 0x6Bu8] {
        // blank
        Some(seq![(0x09u32, 0x09u32), (0x20u32, 0x20u32)])
    } else if name == seq![0x63u8, 0x6Eu8, 0x74u8, 0x72u8, 0x6Cu8] {
        // cntrl
        Some(seq![(0x00u32, 0x1Fu32), (0x7Fu32, 0x7Fu32)])
    } else if name == seq![0x64u8, 0x69u8, 0x67u8, 0x69u8, 0x74u8] {
        // digit
        Some(seq![(0x30u32, 0x39u32)])
    } else if name == seq![0x67u8, 0x72u8, 0x61u8, 0x70u8, 0x68u8] {
        // graph
        Some(seq![(0x21u32, 0x7Eu32)])
    } else if name == seq![0x6Cu8, 0x6Fu8, 0x77u8, 0x65u8, 0x72u8] {
        // lower
        Some(seq![(0x61u32, 0x7Au32)])
    } else if name == seq![0x70u8, 0x72u8, 0x69u8, 0x6Eu8, 0x74u8] {
        // print
        Some(seq![(0x20u32, 0x7Eu32)])
    } else if name == seq![0x70u8, 0x75u8, 0x6Eu8, 0x63u8, 0x74u8] {
        // punct
        Some(seq![(0x21u32, 0x2Fu32), (0x3Au32, 0x40u32), (0x5Bu32, 0x60u32), (0x7Bu32, 0x7Eu32)])
    } else if name == seq![0x73u8, 0x70u8, 0x61u8, 0x63u8, 0x65u8] {
        // space
        Some(seq![(0x09u32, 0x0Du32), (0x20u32, 0x20u32)])
    } else if name == seq![0x75u8, 0x70u8, 0x70u8, 0x65u8, 0x72u8] {
        // upper
        Some(seq![(0x41u32, 0x5Au32)])
    } else if name == seq![0x77u8, 0x6Fu8, 0x72u8, 0x64u8] {
        // word
        Some(seq![(0x30u32, 0x39u32), (0x41u32, 0x5Au32), (0x5Fu32, 0x5Fu32), (0x61u32, 0x7Au32)])
    } else if name == seq![0x78u8, 0x64u8, 0x69u8, 0x67u8, 0x69u8, 0x74u8] {
        // xdigit
        Some(seq![(0x30u32, 0x39u32), (0x41u32, 0x46u32), (0x61u32, 0x66u32)])
    } else {
        None
    }
}

/// The Unicode group called `name`: `Any`, a general category or a script.
pub open spec fn named_set(name: Seq<u8>) -> Option<ISet<u32>> {
    if name == seq![0x41u8, 0x6Eu8, 0x79u8] {
        Some(cs_range(0, MAXCP))
    } else {
        match find_group_from(name, 0) {
            Some(g) => Some(cs_group(g)),
            None => None,
        }
    }
}

/// `\pN`, `\p{Name}`, `\PN`, `\P{Name}`, `\p{^Name}`; `pos` holds the
/// backslash and `pos + 1` the `p` or `P`.
pub open spec fn unicode(pat: Seq<u8>, pos: int, fl: Flags) -> Option<(ISet<u32>, int)> {
    let n = pat.len() as int;
    if pos + 2 >= n {
        None
    } else {
        let neg0 = pat[pos + 1] == 0x50;
        let (c, l) = chr(pat, pos + 2);
        let q = find(pat, pos + 3, 0x7D);
        if c == 0x7B && q >= n {
            None
        } else {
            let a0 = if c == 0x7B { pos + 3 } else { pos + 2 };
            let b = if c == 0x7B { q } else { pos + 2 + l };
            let end = if c == 0x7B { q + 1 } else { b };
            let caret = a0 < b && pat[a0] == 0x5E;
            let a = if caret { a0 + 1 } else { a0 };
            match named_set(pat.subrange(a, b)) {
                Some(base) => Some((item(base, neg0 != caret, fl.i), end)),
                None => None,
            }
        }
    }
}

/// One character of a bracketed class at `pos`.
pub open spec fn cc_char(pat: Seq<u8>, pos: int) -> Option<(u32, int)> {
    if pos < 0 || pos >= pat.len() {
        None
    } else if pat[pos] == 0x5C {
        escape(pat, pos)
    } else {
        let (c, l) = chr(pat, pos);
        if c > MAXCP {
            None
        } else {
            Some((c, pos + l))
        }
    }
}

/// The first `q >= p` where `:]` stands, or a `q` with `q + 1 >= len`.
pub open spec fn find_colon(pat: Seq<u8>, p: int) -> int
    decreases pat.len() - p,
{
    if p < 0 || p + 1 >= pat.len() {
        p
    } else if pat[p] == 0x3A && pat[p + 1] == 0x5D {
        p
    } else {
        find_colon(pat, p + 1)
    }
}

/// The items of a bracketed class from `p` up to its `]`, added to `cl`.
/// Gives the set and the position of the `]`. (A `]` right after the
/// opening is an ordinary character: that is `first`.)
pub open spec fn cc_items(pat: Seq<u8>, p: int, fl: Flags, cl: ISet<u32>, first: bool) -> Option<(ISet<u32>, int)>
    decreases left(pat, p),
{
    let n = pat.len() as int;
    if p < 0 || p >= n {
        None
    } else if pat[p] == 0x5D && !first {
        Some((cl, p))
    } else {
        let q = find_colon(pat, p + 2);
        if p + 2 < n && pat[p] == 0x5B && pat[p + 1] == 0x3A && q + 1 < n {
            // [:name:] or [:^name:]
            let caret = p + 2 < q && pat[p + 2] == 0x5E;
            let a = if caret { p + 3 } else { p + 2 };
            match posix(pat.subrange(a, q)) {
                Some(rs) => if q + 2 > p {
                    cc_items(pat, q + 2, fl, cs_union(cl, item(cs_ranges(rs), caret, fl.i)), false)
                } else {
                    None
                },
                None => None,
            }
        } else if p + 2 < n && pat[p] == 0x5C && (pat[p + 1] == 0x70 || pat[p + 1] == 0x50) {
            match unicode(pat, p, fl) {
                Some((c, r)) => if r > p {
                    cc_items(pat, r, fl, cs_union(cl, c), false)
                } else {
                    None
                },
                None => None,
            }
        } else {
            match perl(pat, p, fl) {
                Some(c) => cc_items(pat, p + 2, fl, cs_union(cl, c), false),
                None => match cc_char(pat, p) {
                    None => None,
                    Some((lo, r)) => if r + 1 < n && pat[r] == 0x2D && pat[r + 1] != 0x5D {
                        // lo-hi
                        match cc_char(pat, r + 1) {
                            None => None,
                            Some((hi, r2)) => if hi < lo || r2 <= p {
                                None
                            } else {
                                cc_items(pat, r2, fl, cs_union(cl, item(cs_range(lo, hi), false, fl.i)), false)
                            },
                        }
                    } else if r <= p {
                        None
                    } else {
                        cc_items(pat, r, fl, cs_union(cl, item(cs_range(lo, lo), false, fl.i)), false)
                    },
                },
            }
        }
    }
}

/// A bracketed class; `pos` holds the `[`.
pub open spec fn bracket(pat: Seq<u8>, pos: int, fl: Flags) -> Option<(Re, int)> {
    let neg = at(pat, pos + 1, 0x5E);
    let p = if neg { pos + 2 } else { pos + 1 };
    match cc_items(pat, p, fl, ISet::empty(), true) {
        Some((cl, r)) => Some((Re::Char(if neg { cs_neg(cl) } else { cl }), r + 1)),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Atoms
// ---------------------------------------------------------------------------

/// One character, class or assertion at `pos` (which is in the pattern).
pub open spec fn atom(pat: Seq<u8>, pos: int, fl: Flags) -> Option<(Re, int)> {
    let n = pat.len() as int;
    let b = pat[pos];
    if b == 0x5B {
        bracket(pat, pos, fl)
    } else if b == 0x2E {
        // .
        Some((Re::Char(if fl.s { cs_range(0, MAXCP) } else { cs_union(cs_range(0, 9), cs_range(11, MAXCP)) }), pos + 1))
    } else if b == 0x5E {
        // ^
        Some((Re::Look(if fl.m { Look::StartLine } else { Look::Start }), pos + 1))
    } else if b == 0x24 {
        // $
        Some((Re::Look(if fl.m { Look::EndLine } else { Look::End }), pos + 1))
    } else if b == 0x5C {
        if at(pat, pos + 1, 0x62) {
            Some((Re::Look(Look::Word), pos + 2))
        } else if at(pat, pos + 1, 0x42) {
            Some((Re::Look(Look::NotWord), pos + 2))
        } else if at(pat, pos + 1, 0x41) {
            Some((Re::Look(Look::Start), pos + 2))
        } else if at(pat, pos + 1, 0x7A) {
            Some((Re::Look(Look::End), pos + 2))
        } else if at(pat, pos + 1, 0x70) || at(pat, pos + 1, 0x50) {
            match unicode(pat, pos, fl) {
                Some((c, q)) => Some((Re::Char(c), q)),
                None => None,
            }
        } else {
            match perl(pat, pos, fl) {
                Some(c) => Some((Re::Char(c), pos + 2)),
                None => match escape(pat, pos) {
                    Some((c, q)) => Some((Re::Char(lit(c, fl)), q)),
                    None => None,
                },
            }
        }
    } else {
        let (c, l) = chr(pat, pos);
        if c > MAXCP {
            None
        } else {
            Some((Re::Char(lit(c, fl)), pos + l))
        }
    }
}

// ---------------------------------------------------------------------------
// Repetition
// ---------------------------------------------------------------------------

/// Decimal digits from `p`, with value `v` so far: the count and where it
/// ends. Counts of 10^8 and more are not counts.
pub open spec fn digits(pat: Seq<u8>, p: int, v: nat) -> Option<(nat, int)>
    decreases pat.len() - p,
{
    if 0 <= p < pat.len() && is_digit(pat[p]) {
        if v >= 100000000 {
            None
        } else {
            digits(pat, p + 1, (v * 10 + (pat[p] - 0x30)) as nat)
        }
    } else {
        Some((v, p))
    }
}

/// A count at `pos`: digits, without a leading zero.
pub open spec fn integer(pat: Seq<u8>, pos: int) -> Option<(nat, int)> {
    let n = pat.len() as int;
    if pos < 0 || pos >= n || !is_digit(pat[pos]) {
        None
    } else if pos + 1 < n && pat[pos] == 0x30 && is_digit(pat[pos + 1]) {
        None
    } else {
        digits(pat, pos, 0)
    }
}

/// `{n}`, `{n,}` or `{n,m}` at `pos`: the least count, the greatest if
/// there is one, and where it ends.
pub open spec fn counts(pat: Seq<u8>, pos: int) -> Option<(nat, Option<nat>, int)> {
    if !at(pat, pos, 0x7B) {
        None
    } else {
        match integer(pat, pos + 1) {
            None => None,
            Some((lo, p)) => if at(pat, p, 0x7D) {
                Some((lo, Some(lo), p + 1))
            } else if at(pat, p, 0x2C) {
                if at(pat, p + 1, 0x7D) {
                    Some((lo, None, p + 2))
                } else {
                    match integer(pat, p + 1) {
                        None => None,
                        Some((hi, q)) => if at(pat, q, 0x7D) {
                            Some((lo, Some(hi), q + 1))
                        } else {
                            None
                        },
                    }
                }
            } else {
                None
            },
        }
    }
}

/// A repetition operator at `p` (which is in the pattern): `*`, `+`, `?`
/// or a count. A `{` that starts no count is an ordinary character.
pub open spec fn rep_op(pat: Seq<u8>, p: int) -> Option<(nat, Option<nat>, int)> {
    let b = pat[p];
    if b == 0x2A {
        Some((0, None, p + 1))
    } else if b == 0x2B {
        Some((1, None, p + 1))
    } else if b == 0x3F {
        Some((0, Some(1), p + 1))
    } else {
        counts(pat, p)
    }
}

/// `k` nested optional copies of `x`: `(x(x(...)?)?)?`.
pub open spec fn opt_tail(x: Re, k: nat, greedy: bool) -> Re
    decreases k,
{
    if k == 0 {
        Re::Empty
    } else {
        Re::Opt(Box::new(Re::Cat(Box::new(x), Box::new(opt_tail(x, (k - 1) as nat, greedy)))), greedy)
    }
}

/// `k` copies of `x`, then `tail`.
pub open spec fn copies(x: Re, k: nat, tail: Re) -> Re
    decreases k,
{
    if k == 0 {
        tail
    } else {
        Re::Cat(Box::new(x), Box::new(copies(x, (k - 1) as nat, tail)))
    }
}

/// `x{min,max}` (`max` is `None` for no upper bound).
pub open spec fn repeat(x: Re, min: nat, max: Option<nat>, greedy: bool) -> Re {
    let plus = Re::Plus(Box::new(x), greedy);
    match max {
        None => if min == 0 {
            Re::Opt(Box::new(plus), greedy)
        } else {
            copies(x, (min - 1) as nat, plus)
        },
        Some(m) => copies(x, min, opt_tail(x, (m - min) as nat, greedy)),
    }
}

/// The repetition `b` (with counts `min`, `max` if `b` is `{`) applied
/// to `x`.
pub open spec fn apply_rep(x: It, b: u8, min: nat, max: Option<nat>, greedy: bool) -> Option<It> {
    if b == 0x2A {
        Some(It { re: Re::Opt(Box::new(Re::Plus(Box::new(x.re), greedy)), greedy), rep: x.rep })
    } else if b == 0x3F {
        Some(It { re: Re::Opt(Box::new(x.re), greedy), rep: x.rep })
    } else if b == 0x2B {
        Some(It { re: Re::Plus(Box::new(x.re), greedy), rep: x.rep })
    } else {
        let m = match max {
            Some(m) => m,
            None => min,
        };
        let rep = if m > 0 { x.rep * m } else { x.rep };
        if min > 1000 || m > 1000 || m < min || (m >= 2 && rep > 1000) {
            None
        } else {
            Some(It { re: repeat(x.re, min, max, greedy), rep: rep })
        }
    }
}

// ---------------------------------------------------------------------------
// Groups, concatenation, alternation
// ---------------------------------------------------------------------------

pub open spec fn maxn(a: nat, b: nat) -> nat {
    if a > b { a } else { b }
}

/// The pieces `xs` joined, as a balanced tree: by `|` if `alt`, else in
/// sequence. (Balanced only to keep trees shallow; either joining is
/// associative.)
pub open spec fn tree(xs: Seq<It>, alt: bool) -> It
    decreases xs.len(),
{
    if xs.len() == 0 {
        It { re: Re::Empty, rep: 1 }
    } else if xs.len() == 1 {
        xs[0]
    } else {
        let mid = xs.len() as int / 2;
        let x = tree(xs.subrange(0, mid), alt);
        let y = tree(xs.subrange(mid, xs.len() as int), alt);
        It {
            re: if alt { Re::Alt(Box::new(x.re), Box::new(y.re)) } else { Re::Cat(Box::new(x.re), Box::new(y.re)) },
            rep: maxn(x.rep, y.rep),
        }
    }
}

/// The flags of `(?flags)` or `(?flags:` from `q`: the new flags, where
/// they end, and whether a `:` ended them. `neg` after a `-`; `saw` if a
/// flag letter followed it.
pub open spec fn flags(pat: Seq<u8>, q: int, nf: Flags, neg: bool, saw: bool) -> Option<(Flags, int, bool)>
    decreases pat.len() - q,
{
    if q < 0 || q >= pat.len() {
        None
    } else {
        let b = pat[q];
        if b == 0x69 {
            flags(pat, q + 1, Flags { i: !neg, ..nf }, neg, true)
        } else if b == 0x6D {
            flags(pat, q + 1, Flags { m: !neg, ..nf }, neg, true)
        } else if b == 0x73 {
            flags(pat, q + 1, Flags { s: !neg, ..nf }, neg, true)
        } else if b == 0x55 {
            flags(pat, q + 1, Flags { u: !neg, ..nf }, neg, true)
        } else if b == 0x2D {
            if neg {
                None
            } else {
                flags(pat, q + 1, nf, true, false)
            }
        } else if b == 0x3A || b == 0x29 {
            if neg && !saw {
                None
            } else {
                Some((nf, q + 1, b == 0x3A))
            }
        } else {
            None
        }
    }
}

/// Where the name of a named group opening at `p` starts: after `(?P<`
/// or `(?<` (but `(?<=` and `(?<!` are lookbehinds, which are not
/// supported).
pub open spec fn named_start(pat: Seq<u8>, p: int) -> Option<int> {
    if at(pat, p + 2, 0x50) && at(pat, p + 3, 0x3C) {
        Some(p + 4)
    } else if at(pat, p + 2, 0x3C) && !at(pat, p + 3, 0x3D) && !at(pat, p + 3, 0x21) {
        Some(p + 3)
    } else {
        None
    }
}

/// The code points of the group called `name`, none if there is no such
/// group.
pub open spec fn group_set(name: Seq<u8>) -> ISet<u32> {
    match find_group_from(name, 0) {
        Some(g) => cs_group(g),
        None => ISet::empty(),
    }
}

/// Whether `c` may appear in a group name: a letter, mark, digit or
/// connector (Lu, Ll, Lt, Lm, Lo, Nl, Mn, Mc, Nd, Pc).
pub open spec fn word_char(c: u32) -> bool {
    group_set(seq![0x4Cu8, 0x75u8]).contains(c) || group_set(seq![0x4Cu8, 0x6Cu8]).contains(c) || group_set(
        seq![0x4Cu8, 0x74u8],
    ).contains(c) || group_set(seq![0x4Cu8, 0x6Du8]).contains(c) || group_set(seq![0x4Cu8, 0x6Fu8]).contains(c)
        || group_set(seq![0x4Eu8, 0x6Cu8]).contains(c) || group_set(seq![0x4Du8, 0x6Eu8]).contains(c) || group_set(
        seq![0x4Du8, 0x63u8],
    ).contains(c) || group_set(seq![0x4Eu8, 0x64u8]).contains(c) || group_set(seq![0x50u8, 0x63u8]).contains(c)
}

/// Whether the characters of `pat[p..b]` are all word characters.
pub open spec fn name_chars(pat: Seq<u8>, p: int, b: int) -> bool
    decreases (if b > p { b - p } else { 0 }),
{
    if p >= b {
        true
    } else {
        let (c, l) = chr(pat, p);
        if word_char(c) && l >= 1 {
            name_chars(pat, p + l, b)
        } else {
            false
        }
    }
}

/// Whether a group is already called `name`.
pub open spec fn has_name(names: Seq<(Seq<u8>, nat)>, name: Seq<u8>) -> bool {
    exists|k: int| 0 <= k < names.len() && (#[trigger] names[k]).0 == name
}

/// The literal characters of `\Q...\E` from `p`, added to `acc`; gives
/// them and where the quote ends.
pub open spec fn quote(pat: Seq<u8>, p: int, fl: Flags, acc: Seq<It>) -> Option<(Seq<It>, int)>
    decreases pat.len() - p,
{
    if p < 0 || p >= pat.len() {
        Some((acc, p))
    } else if pat[p] == 0x5C && at(pat, p + 1, 0x45) {
        Some((acc, p + 2))
    } else {
        let (c, l) = chr(pat, p);
        if c > MAXCP || l < 1 {
            None
        } else {
            quote(pat, p + l, fl, acc.push(It { re: Re::Char(lit(c, fl)), rep: 1 }))
        }
    }
}

/// Alternatives from `pos` up to the end of the pattern or an unmatched
/// `)`, after the alternatives `acc`.
pub open spec fn alts(pat: Seq<u8>, pos: int, fl: Flags, st: St, acc: Seq<It>) -> Option<Out>
    decreases left(pat, pos), 3int,
{
    match items(pat, pos, fl, st, Seq::empty(), false) {
        None => None,
        Some(o) => {
            let acc2 = acc.push(o.it);
            if at(pat, o.pos, 0x7C) && o.pos >= pos {
                alts(pat, o.pos + 1, o.fl, o.st, acc2)
            } else {
                Some(Out { it: tree(acc2, true), pos: o.pos, fl: o.fl, st: o.st })
            }
        },
    }
}

/// A concatenation from `p` up to `|`, `)` or the end, after the pieces
/// `acc`. `after_rep`: the last piece just took a repetition operator
/// (and may not take another).
pub open spec fn items(pat: Seq<u8>, p: int, fl: Flags, st: St, acc: Seq<It>, after_rep: bool) -> Option<Out>
    decreases left(pat, p), 1int,
{
    let n = pat.len() as int;
    if p < 0 || p >= n || pat[p] == 0x7C || pat[p] == 0x29 {
        Some(Out { it: tree(acc, false), pos: p, fl: fl, st: st })
    } else {
        let b = pat[p];
        match rep_op(pat, p) {
            Some((min, max, q0)) => {
                let lazy = at(pat, q0, 0x3F);
                let q = if lazy { q0 + 1 } else { q0 };
                let greedy = fl.u == lazy;
                if after_rep || acc.len() == 0 || q <= p {
                    None
                } else {
                    match apply_rep(acc.last(), b, min, max, greedy) {
                        None => None,
                        Some(y) => items(pat, q, fl, st, acc.drop_last().push(y), true),
                    }
                }
            },
            None => if b == 0x28 {
                if at(pat, p + 1, 0x3F) {
                    match named_start(pat, p) {
                        Some(a) => {
                            // (?P<name>...)
                            let q = find(pat, a, 0x3E);
                            if q >= n || a >= q || !name_chars(pat, a, q) || q + 1 <= p || has_name(st.names, pat.subrange(a, q)) {
                                None
                            } else {
                                let st2 = St { ng: st.ng, names: st.names.push((pat.subrange(a, q), st.ng)) };
                                match group(pat, q + 1, fl, st2, true) {
                                    None => None,
                                    Some((it, r, st3)) => if r <= p {
                                        None
                                    } else {
                                        items(pat, r, fl, st3, acc.push(it), false)
                                    },
                                }
                            }
                        },
                        None => match flags(pat, p + 2, fl, false, false) {
                            None => None,
                            Some((nf, q, colon)) => if q <= p {
                                None
                            } else if colon {
                                // (?flags:...)
                                match group(pat, q, nf, st, false) {
                                    None => None,
                                    Some((it, r, st3)) => if r <= p {
                                        None
                                    } else {
                                        items(pat, r, fl, st3, acc.push(it), false)
                                    },
                                }
                            } else {
                                // (?flags)
                                items(pat, q, nf, st, acc, false)
                            },
                        },
                    }
                } else {
                    match group(pat, p + 1, fl, st, true) {
                        None => None,
                        Some((it, r, st3)) => if r <= p {
                            None
                        } else {
                            items(pat, r, fl, st3, acc.push(it), false)
                        },
                    }
                }
            } else if b == 0x5C && at(pat, p + 1, 0x51) {
                // \Q...\E
                match quote(pat, p + 2, fl, acc) {
                    None => None,
                    Some((acc2, r)) => if r <= p {
                        None
                    } else {
                        items(pat, r, fl, st, acc2, false)
                    },
                }
            } else {
                match atom(pat, p, fl) {
                    None => None,
                    Some((re, r)) => if r <= p {
                        None
                    } else {
                        items(pat, r, fl, st, acc.push(It { re: re, rep: 1 }), false)
                    },
                }
            },
        }
    }
}

/// A group whose content starts at `body`, up to its `)`. Gives the
/// piece, where the group ends, and the groups used. Flags set inside do
/// not reach outside.
pub open spec fn group(pat: Seq<u8>, body: int, fl: Flags, st: St, capture: bool) -> Option<(It, int, St)>
    decreases left(pat, body), 4int,
{
    let k = st.ng;
    let st1 = if capture {
        St { ng: st.ng + 1, names: st.names }
    } else {
        st
    };
    match alts(pat, body, fl, st1, Seq::empty()) {
        None => None,
        Some(o) => if !at(pat, o.pos, 0x29) {
            None
        } else {
            Some(
                (
                    if capture {
                        It { re: Re::Group(k, Box::new(o.it.re)), rep: o.it.rep }
                    } else {
                        o.it
                    },
                    o.pos + 1,
                    o.st,
                ),
            )
        },
    }
}

/// The regular expression the pattern `pat` stands for.
pub open spec fn parse(pat: Seq<u8>) -> Option<Pat> {
    if !utf8_from(pat, 0) {
        None
    } else {
        let fl = Flags { i: false, m: false, s: false, u: false };
        match alts(pat, 0, fl, St { ng: 1, names: Seq::empty() }, Seq::empty()) {
            None => None,
            Some(o) => if o.pos < pat.len() {
                // An unmatched `)`.
                None
            } else {
                Some(Pat { re: Re::Group(0, Box::new(o.it.re)), ngroups: o.st.ng, names: o.st.names })
            },
        }
    }
}

} // verus!
