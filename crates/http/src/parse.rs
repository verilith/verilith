//! The head parser, proven to compute exactly `spec::parse_request`,
//! `spec::parse_response` and `spec::parse_headers`. Verus also proves
//! every index in bounds and every arithmetic operation free of overflow,
//! so it cannot panic, and counts the loop iterations: parsing any input
//! takes at most `3 * len + 16` of them, whatever the outcome.
use crate::framing::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::*;
use crate::scan::{scan_target_fast, scan_value_fast};
use crate::spec::*;
pub use verilith_core::prims::get as get8;
use vstd::prelude::*;

verus! {

/// Positions `start..end` in the input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl View for Span {
    type V = SpecSpan;

    open spec fn view(&self) -> SpecSpan {
        SpecSpan { start: self.start as int, end: self.end as int }
    }
}

/// A field line, as spans into the input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Header {
    pub name: Span,
    /// The value with leading and trailing whitespace removed.
    pub value: Span,
}

impl View for Header {
    type V = SpecHeader;

    open spec fn view(&self) -> SpecHeader {
        SpecHeader { name: self.name@, value: self.value@ }
    }
}

/// Both spans of `h` lie within `0..n`.
pub open spec fn hdr_ok(h: Header, n: int) -> bool {
    h.name.start <= h.name.end <= n && h.value.start <= h.value.end <= n
}

pub open spec fn hdrs_ok(hs: Seq<Header>, n: int) -> bool {
    forall|j: int| 0 <= j < hs.len() ==> hdr_ok(#[trigger] hs[j], n)
}

pub open spec fn headers_view(hs: Seq<Header>) -> Seq<SpecHeader> {
    hs.map_values(|h: Header| h@)
}

/// The result of an exec parse step; mirrors `spec::Parsed`.
pub enum Out<T> {
    Done(T, usize),
    Partial,
    Invalid,
}

/// `o` is the exec counterpart of `p`.
pub open spec fn agrees<T>(o: Out<T>, p: Parsed<T>) -> bool {
    match o {
        Out::Done(x, e) => p matches Parsed::Done(y, f) && x == y && e as int == f,
        Out::Partial => p is Partial,
        Out::Invalid => p is Invalid,
    }
}

/// `o` is the exec counterpart of `p`, for a value with a view.
pub open spec fn agrees_v<T: View>(o: Out<T>, p: Parsed<T::V>) -> bool {
    match o {
        Out::Done(x, e) => p matches Parsed::Done(y, f) && x@ == y && e as int == f,
        Out::Partial => p is Partial,
        Out::Invalid => p is Invalid,
    }
}

// ---------------------------------------------------------------------------
// Byte classes
// ---------------------------------------------------------------------------

/// The tchar table: entry `c` is 1 iff `c` is a tchar.
pub open spec fn tchar_table() -> Seq<u8> {
    seq![
        0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0,
        0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ]
}

/// `tchar_table` is checked against `is_tchar` entry by entry.
pub open spec fn tchar_table_ok(i: int) -> bool
    decreases 256 - i,
{
    if i < 0 || i >= 256 {
        true
    } else {
        (tchar_table()[i] == 1) == is_tchar(i as u8) && tchar_table_ok(i + 1)
    }
}

proof fn lemma_tchar_table_at(i: int, j: int)
    requires
        0 <= i <= j < 256,
        tchar_table_ok(i),
    ensures
        (tchar_table()[j] == 1) == is_tchar(j as u8),
    decreases j - i,
{
    if i < j {
        lemma_tchar_table_at(i + 1, j);
    }
}

pub proof fn lemma_tchar_table()
    ensures
        tchar_table().len() == 256,
        forall|j: int| 0 <= j < 256 ==> (#[trigger] tchar_table()[j] == 1) == is_tchar(j as u8),
{
    assert(tchar_table_ok(0)) by (compute_only);
    assert forall|j: int| 0 <= j < 256 implies (#[trigger] tchar_table()[j] == 1) == is_tchar(
        j as u8,
    ) by {
        lemma_tchar_table_at(0, j);
    }
}

/// The tchar table as data.
pub const TCHAR_TABLE: [u8; 256] = [
    0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

#[inline(always)]
pub fn tchar(c: u8) -> (r: bool)
    ensures
        r == is_tchar(c),
{
    let t = &TCHAR_TABLE;
    proof {
        assert(t@ =~= tchar_table());
        lemma_tchar_table();
    }
    t[c as usize] == 1
}

#[inline(always)]
pub fn target_char(c: u8) -> (r: bool)
    ensures
        r == is_target_char(c),
{
    c > 0x20 && c != 0x7F
}

#[inline(always)]
pub fn value_char(c: u8) -> (r: bool)
    ensures
        r == is_value_char(c),
{
    (c >= 0x20 && c != 0x7F) || c == HTAB
}

#[inline(always)]
pub fn ows(c: u8) -> (r: bool)
    ensures
        r == is_ows(c),
{
    c == SP || c == HTAB
}

// ---------------------------------------------------------------------------
// Scanners. Each returns the run end and its loop iteration count.
// ---------------------------------------------------------------------------

pub proof fn lemma_run_end_bounds(b: Seq<u8>, i: int, k: Cls)
    requires
        0 <= i <= b.len(),
    ensures
        i <= run_end(b, i, k) <= b.len(),
        forall|j: int| i <= j < run_end(b, i, k) ==> in_cls(k, #[trigger] b[j]),
        run_end(b, i, k) < b.len() ==> !in_cls(k, b[run_end(b, i, k)]),
    decreases b.len() - i,
{
    if i < b.len() && in_cls(k, b[i]) {
        lemma_run_end_bounds(b, i + 1, k);
    }
}

pub fn scan_token(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Token),
        r.1@ == r.0 - i,
{
    let mut p = i;
    while p < b.len() && tchar(get8(b, p))
        invariant
            i <= p <= b@.len(),
            run_end(b@, i as int, Cls::Token) == run_end(b@, p as int, Cls::Token),
        decreases b@.len() - p,
    {
        p += 1;
    }
    (p, Ghost((p - i) as nat))
}

pub fn scan_target(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Target),
        r.1@ == r.0 - i,
{
    let mut p = i;
    while p < b.len() && target_char(get8(b, p))
        invariant
            i <= p <= b@.len(),
            run_end(b@, i as int, Cls::Target) == run_end(b@, p as int, Cls::Target),
        decreases b@.len() - p,
    {
        p += 1;
    }
    (p, Ghost((p - i) as nat))
}

pub fn scan_value(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Value),
        r.1@ == r.0 - i,
{
    let mut p = i;
    while p < b.len() && value_char(get8(b, p))
        invariant
            i <= p <= b@.len(),
            run_end(b@, i as int, Cls::Value) == run_end(b@, p as int, Cls::Value),
        decreases b@.len() - p,
    {
        p += 1;
    }
    (p, Ghost((p - i) as nat))
}

pub fn scan_ows(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Ows),
        r.1@ == r.0 - i,
{
    let mut p = i;
    while p < b.len() && ows(get8(b, p))
        invariant
            i <= p <= b@.len(),
            run_end(b@, i as int, Cls::Ows) == run_end(b@, p as int, Cls::Ows),
        decreases b@.len() - p,
    {
        p += 1;
    }
    (p, Ghost((p - i) as nat))
}

/// Trailing OWS of `b[s..e]` removed (spec `trim_end`).
pub fn trim(b: &[u8], s: usize, e: usize) -> (r: (usize, Ghost<nat>))
    requires
        s <= e <= b@.len(),
    ensures
        r.0 == trim_end(b@, s as int, e as int),
        s <= r.0 <= e,
        r.1@ == e - r.0,
{
    let mut p = e;
    while p > s && ows(get8(b, p - 1))
        invariant
            s <= p <= e,
            e <= b@.len(),
            trim_end(b@, s as int, e as int) == trim_end(b@, s as int, p as int),
        decreases p,
    {
        p -= 1;
    }
    (p, Ghost((e - p) as nat))
}

// ---------------------------------------------------------------------------
// Literals
// ---------------------------------------------------------------------------

/// The literal `s` at `i` (spec `lit`).
pub fn lit_exec(b: &[u8], i: usize, s: &[u8]) -> (r: Out<()>)
    requires
        i <= b@.len(),
    ensures
        agrees(r, lit(b@, i as int, s@)),
        r matches Out::Done(_, e) ==> e <= b@.len(),
{
    let avail = b.len() - i;
    let n = if avail < s.len() {
        avail
    } else {
        s.len()
    };
    let mut k = 0;
    while k < n
        invariant
            k <= n,
            n <= s@.len(),
            i + n <= b.len(),
            b@.subrange(i as int, i + k) == s@.subrange(0, k as int),
        decreases n - k,
    {
        if get8(b, i + k) != s[k] {
            proof {
                assert(b@.subrange(i as int, i + n)[k as int] != s@.subrange(0, n as int)[k as int]);
            }
            return Out::Invalid;
        }
        proof {
            assert(b@.subrange(i as int, i + k + 1) =~= s@.subrange(0, k + 1)) by {
                assert forall|j: int| 0 <= j < k implies #[trigger] b@.subrange(i as int, i + k + 1)[j]
                    == s@.subrange(0, k + 1)[j] by {
                    assert(b@.subrange(i as int, i + k)[j] == s@.subrange(0, k as int)[j]);
                }
            }
        }
        k += 1;
    }
    if n < s.len() {
        Out::Partial
    } else {
        Out::Done((), i + s.len())
    }
}

/// CRLF at `i` (spec `lit(b, i, crlf())`).
#[inline(always)]
pub fn crlf_at(b: &[u8], i: usize) -> (r: Out<()>)
    requires
        i <= b@.len(),
    ensures
        agrees(r, lit(b@, i as int, crlf())),
        r matches Out::Done(_, e) ==> e == i + 2 && e <= b@.len(),
{
    let ghost s = crlf();
    let n = b.len() - i;
    if n >= 2 {
        if get8(b, i) == CR && get8(b, i + 1) == LF {
            proof {
                assert(b@.subrange(i as int, i + 2) =~= s.subrange(0, 2));
            }
            Out::Done((), i + 2)
        } else {
            proof {
                if b@[i as int] != CR {
                    assert(b@.subrange(i as int, i + 2)[0] != s.subrange(0, 2)[0]);
                } else {
                    assert(b@.subrange(i as int, i + 2)[1] != s.subrange(0, 2)[1]);
                }
            }
            Out::Invalid
        }
    } else if n == 1 {
        if get8(b, i) == CR {
            proof {
                assert(b@.subrange(i as int, i + 1) =~= s.subrange(0, 1));
            }
            Out::Partial
        } else {
            proof {
                assert(b@.subrange(i as int, i + 1)[0] != s.subrange(0, 1)[0]);
            }
            Out::Invalid
        }
    } else {
        proof {
            assert(b@.subrange(i as int, i as int) =~= s.subrange(0, 0));
        }
        Out::Partial
    }
}

/// `HTTP/1.x` at `i` (spec `parse_version`).
#[inline(always)]
pub fn version_at(b: &[u8], i: usize) -> (r: Out<u8>)
    requires
        i <= b@.len(),
    ensures
        agrees(r, parse_version(b@, i as int)),
        r matches Out::Done(_, e) ==> e == i + 8 && e <= b@.len(),
{
    let pre: [u8; 7] = [0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E];
    proof {
        assert(pre@ =~= http1_prefix());
    }
    // Fast path: the whole version is present and well formed.
    if b.len() - i >= 8 && get8(b, i) == 0x48 && get8(b, i + 1) == 0x54 && get8(b, i + 2) == 0x54
        && get8(b, i + 3) == 0x50 && get8(b, i + 4) == 0x2F && get8(b, i + 5) == 0x31 && get8(
        b,
        i + 6,
    ) == 0x2E {
        let c = get8(b, i + 7);
        if c >= 0x30 && c <= 0x39 {
            proof {
                assert(b@.subrange(i as int, i + 7) =~= http1_prefix().subrange(0, 7));
            }
            return Out::Done(c - 0x30, i + 8);
        }
    }
    match lit_exec(b, i, pre.as_slice()) {
        Out::Done(_, j) => {
            if j >= b.len() {
                Out::Partial
            } else {
                let c = get8(b, j);
                if c < 0x30 || c > 0x39 {
                    Out::Invalid
                } else {
                    Out::Done(c - 0x30, j + 1)
                }
            }
        },
        Out::Partial => Out::Partial,
        Out::Invalid => Out::Invalid,
    }
}

/// A nonempty token at `i` followed by `d` (spec `run_then(b, i, Token, d)`).
#[inline(always)]
pub fn token_then(b: &[u8], i: usize, d: u8) -> (r: (Out<usize>, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        agrees_pos(r.0, run_then(b@, i as int, Cls::Token, d)),
        r.0 matches Out::Done(e, n) ==> i < e && n == e + 1 && n <= b@.len(),
        r.1@ <= run_end(b@, i as int, Cls::Token) - i,
        r.1@ <= b@.len() - i,
{
    let (e, g) = crate::scan::scan_token_fast(b, i);
    proof {
        lemma_run_end_bounds(b@, i as int, Cls::Token);
    }
    if e >= b.len() {
        (Out::Partial, g)
    } else if e == i || get8(b, e) != d {
        (Out::Invalid, g)
    } else {
        (Out::Done(e, e + 1), g)
    }
}

/// `agrees` for results whose value is a position.
pub open spec fn agrees_pos(o: Out<usize>, p: Parsed<int>) -> bool {
    match o {
        Out::Done(x, e) => p matches Parsed::Done(y, f) && x as int == y && e as int == f,
        Out::Partial => p is Partial,
        Out::Invalid => p is Invalid,
    }
}

// ---------------------------------------------------------------------------
// Field lines
// ---------------------------------------------------------------------------

/// One field line at `i` (spec `parse_header`).
#[inline(always)]
pub fn header_at(b: &[u8], i: usize) -> (r: (Out<Header>, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        agrees_v(r.0, parse_header(b@, i as int)),
        r.0 matches Out::Done(_, n) ==> i + 4 <= n <= b@.len(),
        r.0 matches Out::Done(h, _) ==> hdr_ok(h, b@.len() as int),
        r.0 matches Out::Done(_, n) ==> r.1@ <= 2 * (n - i),
        r.1@ <= 2 * (b@.len() - i),
{
    let (t, g1) = token_then(b, i, COLON);
    proof {
        lemma_run_end_bounds(b@, i as int, Cls::Token);
    }
    match t {
        Out::Done(ne, v0) => {
            // Almost always exactly one SP.
            let (vs, g2) = if b.len() - v0 >= 2 && get8(b, v0) == SP && !ows(get8(b, v0 + 1)) {
                proof {
                    assert(run_end(b@, v0 + 1, Cls::Ows) == v0 + 1);
                    assert(run_end(b@, v0 as int, Cls::Ows) == run_end(b@, v0 + 1, Cls::Ows));
                }
                (v0 + 1, Ghost(1nat))
            } else {
                scan_ows(b, v0)
            };
            // The value's end, scanned from the start of the line: the
            // name, colon and OWS are value bytes too, so this is the same
            // position, and it does not wait for the name scan.
            let (e, g3) = scan_value_fast(b, i);
            proof {
                lemma_run_end_bounds(b@, v0 as int, Cls::Ows);
                lemma_run_end_bounds(b@, i as int, Cls::Token);
                assert forall|j: int| i <= j < vs implies is_value_char(#[trigger] b@[j]) by {
                    if j < ne {
                        assert(is_tchar(b@[j]));
                    }
                }
                crate::scan::lemma_run_skip(b@, i as int, vs as int, Cls::Value);
                lemma_run_end_bounds(b@, vs as int, Cls::Value);
            }
            match crlf_at(b, e) {
                Out::Done(_, next) => {
                    let (ve, g4) = trim(b, vs, e);
                    let h = Header {
                        name: Span { start: i, end: ne },
                        value: Span { start: vs, end: ve },
                    };
                    (Out::Done(h, next), Ghost(g1@ + g2@ + g3@ + g4@))
                },
                Out::Partial => (Out::Partial, Ghost(g1@ + g2@ + g3@)),
                Out::Invalid => (Out::Invalid, Ghost(g1@ + g2@ + g3@)),
            }
        },
        Out::Partial => (Out::Partial, g1),
        Out::Invalid => (Out::Invalid, g1),
    }
}

/// `prefix ++` a parse result.
pub open spec fn prepend(acc: Seq<SpecHeader>, r: Parsed<Seq<SpecHeader>>) -> Parsed<
    Seq<SpecHeader>,
> {
    match r {
        Parsed::Done(t, m) => Parsed::Done(acc + t, m),
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

/// The field lines and final CRLF at `i` (spec `parse_headers`), appended
/// to `hs`.
#[inline(always)]
pub fn headers_at(b: &[u8], i: usize, max: usize, hs: &mut Vec<Header>) -> (r: (
    Out<()>,
    Ghost<nat>,
))
    requires
        i <= b@.len(),
        hdrs_ok(old(hs)@, b@.len() as int),
    ensures
        hdrs_ok(final(hs)@, b@.len() as int),
        match parse_headers(b@, i as int, max as nat) {
            Parsed::Done(t, m) => r.0 matches Out::Done(_, e) && e as int == m && e <= b@.len()
                && headers_view(final(hs)@) == headers_view(old(hs)@) + t,
            Parsed::Partial => r.0 is Partial,
            Parsed::Invalid => r.0 is Invalid,
        },
        r.1@ <= 2 * (b@.len() - i) + 1,
{
    let mut fx = None;
    headers_fx(b, i, max, hs, false, &mut fx)
}

/// `headers_at`, and with `want`, the framing fields of the field lines
/// folded into `fx` as they are parsed (`field_step_exec`), so no second
/// pass over them is needed.
pub fn headers_fx(
    b: &[u8],
    i: usize,
    max: usize,
    hs: &mut Vec<Header>,
    want: bool,
    fx: &mut Option<FieldsExec>,
) -> (r: (Out<()>, Ghost<nat>))
    requires
        i <= b@.len(),
        hdrs_ok(old(hs)@, b@.len() as int),
        want ==> fx_agrees(b@, old(hs)@, *old(fx)),
    ensures
        want ==> fx_agrees(b@, final(hs)@, *final(fx)),
        hdrs_ok(final(hs)@, b@.len() as int),
        match parse_headers(b@, i as int, max as nat) {
            Parsed::Done(t, m) => r.0 matches Out::Done(_, e) && e as int == m && e <= b@.len()
                && headers_view(final(hs)@) == headers_view(old(hs)@) + t,
            Parsed::Partial => r.0 is Partial,
            Parsed::Invalid => r.0 is Invalid,
        },
        r.1@ <= 2 * (b@.len() - i) + 1,
{
    let mut p = i;
    let mut left = max;
    let ghost mut acc: Seq<SpecHeader> = Seq::empty();
    let ghost mut steps: nat = 0;
    proof {
        assert(headers_view(hs@) =~= headers_view(old(hs)@) + acc);
        assert(parse_headers(b@, i as int, max as nat) == prepend(
            acc,
            parse_headers(b@, p as int, left as nat),
        )) by {
            if let Parsed::Done(t, m) = parse_headers(b@, i as int, max as nat) {
                assert(acc + t =~= t);
            }
        }
    }
    // The fields stay in registers through the loop.
    let mut cur = *fx;
    loop
        invariant
            i <= p <= b@.len(),
            left <= max,
            headers_view(hs@) == headers_view(old(hs)@) + acc,
            parse_headers(b@, i as int, max as nat) == prepend(
                acc,
                parse_headers(b@, p as int, left as nat),
            ),
            steps <= 2 * (p - i),
            hdrs_ok(hs@, b@.len() as int),
            want ==> fx_agrees(b@, hs@, cur),
        decreases b@.len() - p,
    {
        if p >= b.len() {
            *fx = cur;
            return (Out::Partial, Ghost(steps + 1));
        }
        if get8(b, p) == CR {
            let r = crlf_at(b, p);
            proof {
                if let Out::Done(_, e) = r {
                    assert(acc + Seq::<SpecHeader>::empty() =~= acc);
                }
            }
            *fx = cur;
            return (r, Ghost(steps + 1));
        }
        if left == 0 {
            *fx = cur;
            return (Out::Invalid, Ghost(steps + 1));
        }
        let (h, g) = header_at(b, p);
        match h {
            Out::Done(hd, n) => {
                let ghost old_hs = hs@;
                if want {
                    if let Some(x) = cur {
                        cur = field_step_exec(b, hd, x);
                    }
                }
                hs.push(hd);
                proof {
                    let ghost prev = acc;
                    acc = acc.push(hd@);
                    assert(hs@ =~= old_hs.push(hd));
                    assert(headers_view(old_hs.push(hd)) =~= headers_view(old_hs).push(hd@));
                    assert(headers_view(hs@) =~= headers_view(old(hs)@) + acc);
                    if want {
                        lemma_fields_push(b@, headers_view(old_hs), hd@);
                    }
                    assert(hdrs_ok(hs@, b@.len() as int)) by {
                        assert forall|j: int| 0 <= j < hs@.len() implies hdr_ok(
                            #[trigger] hs@[j],
                            b@.len() as int,
                        ) by {
                            if j < old_hs.len() {
                                assert(hs@[j] == old_hs[j]);
                            }
                        }
                    }
                    if let Parsed::Done(t, m) = parse_headers(b@, n as int, (left - 1) as nat) {
                        assert(prev + (seq![hd@] + t) =~= acc + t);
                    }
                    steps = steps + g@;
                }
                p = n;
                left = left - 1;
            },
            Out::Partial => {
                *fx = cur;
                return (Out::Partial, Ghost(steps + g@ + 1));
            },
            Out::Invalid => {
                *fx = cur;
                return (Out::Invalid, Ghost(steps + g@ + 1));
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Requests and responses
// ---------------------------------------------------------------------------

/// The request line, as spans into the input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RequestLine {
    pub method: Span,
    pub target: Span,
    pub minor: u8,
}

/// The status line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StatusLine {
    pub minor: u8,
    pub status: u16,
    pub reason: Span,
}

/// Leading empty lines (spec `skip_empty_lines(b, 0)`).
pub fn skip_empty(b: &[u8]) -> (r: (Out<()>, Ghost<nat>))
    ensures
        agrees(r.0, skip_empty_lines(b@, 0)),
        r.0 matches Out::Done(_, s) ==> s <= b@.len() && r.1@ <= s,
        r.1@ <= b@.len() + 1,
{
    let mut p: usize = 0;
    loop
        invariant
            p <= b@.len(),
            skip_empty_lines(b@, 0) == skip_empty_lines(b@, p as int),
        decreases b@.len() - p,
    {
        if p >= b.len() {
            return (Out::Partial, Ghost(p as nat + 1));
        }
        if get8(b, p) != CR {
            return (Out::Done((), p), Ghost(p as nat));
        }
        if p + 1 >= b.len() {
            return (Out::Partial, Ghost(p as nat + 1));
        }
        if get8(b, p + 1) != LF {
            return (Out::Invalid, Ghost(p as nat + 1));
        }
        p = p + 2;
    }
}

/// Parses a request head (spec `parse_request`) with at most `max` field
/// lines, which replace the contents of `hs`. On `Done`, the position is
/// the length of the head. The second result counts loop iterations.
#[inline(always)]
pub fn request_at(b: &[u8], max: usize, hs: &mut Vec<Header>) -> (r: (Out<RequestLine>, Ghost<nat>))
    ensures
        match parse_request(b@, max as nat) {
            Parsed::Done(q, end) => r.0 matches Out::Done(l, e) && e as int == end && e
                <= b@.len() && l.method@ == q.method && l.target@ == q.target && l.minor
                == q.minor && headers_view(final(hs)@) == q.headers,
            Parsed::Partial => r.0 is Partial,
            Parsed::Invalid => r.0 is Invalid,
        },
        hdrs_ok(final(hs)@, b@.len() as int),
        r.1@ <= 3 * b@.len() + 16,
{
    let mut fx = None;
    request_fx(b, max, hs, false, &mut fx)
}

/// `request_at`, and with `want`, the framing fields of the head in `fx`
/// (see `headers_fx`).
pub fn request_fx(
    b: &[u8],
    max: usize,
    hs: &mut Vec<Header>,
    want: bool,
    fx: &mut Option<FieldsExec>,
) -> (r: (Out<RequestLine>, Ghost<nat>))
    ensures
        match parse_request(b@, max as nat) {
            Parsed::Done(q, end) => r.0 matches Out::Done(l, e) && e as int == end && e
                <= b@.len() && l.method@ == q.method && l.target@ == q.target && l.minor
                == q.minor && headers_view(final(hs)@) == q.headers,
            Parsed::Partial => r.0 is Partial,
            Parsed::Invalid => r.0 is Invalid,
        },
        hdrs_ok(final(hs)@, b@.len() as int),
        r.1@ <= 3 * b@.len() + 16,
        want ==> fx_agrees(b@, final(hs)@, *final(fx)),
{
    hs.clear();
    *fx = Some(fields_start());
    proof {
        assert(headers_view(hs@) =~= Seq::<SpecHeader>::empty());
    }
    let (sk, g0) = skip_empty(b);
    let s = match sk {
        Out::Done(_, s) => s,
        Out::Partial => return (Out::Partial, g0),
        Out::Invalid => return (Out::Invalid, g0),
    };
    let (m, g1) = token_then(b, s, SP);
    let (me, t) = match m {
        Out::Done(me, t) => (me, t),
        Out::Partial => return (Out::Partial, Ghost(g0@ + g1@)),
        Out::Invalid => return (Out::Invalid, Ghost(g0@ + g1@)),
    };
    let (te, g2) = scan_target_fast(b, t);
    proof {
        lemma_run_end_bounds(b@, t as int, Cls::Target);
    }
    if te >= b.len() {
        return (Out::Partial, Ghost(g0@ + g1@ + g2@));
    }
    if te == t || get8(b, te) != SP {
        return (Out::Invalid, Ghost(g0@ + g1@ + g2@));
    }
    let v = te + 1;
    let ghost g = g0@ + g1@ + g2@;
    let (minor, h) = match version_at(b, v) {
        Out::Done(minor, h) => (minor, h),
        Out::Partial => return (Out::Partial, Ghost(g)),
        Out::Invalid => return (Out::Invalid, Ghost(g)),
    };
    let h2 = match crlf_at(b, h) {
        Out::Done(_, h2) => h2,
        Out::Partial => return (Out::Partial, Ghost(g)),
        Out::Invalid => return (Out::Invalid, Ghost(g)),
    };
    let (rh, g3) = headers_fx(b, h2, max, hs, want, fx);
    let line = RequestLine {
        method: Span { start: s, end: me },
        target: Span { start: t, end: te },
        minor,
    };
    match rh {
        Out::Done(_, end) => (Out::Done(line, end), Ghost(g + g3@)),
        Out::Partial => (Out::Partial, Ghost(g + g3@)),
        Out::Invalid => (Out::Invalid, Ghost(g + g3@)),
    }
}

/// `3DIGIT` at `i` (spec `parse_status`).
pub fn status_at(b: &[u8], i: usize) -> (r: Out<u16>)
    requires
        i <= b@.len(),
    ensures
        agrees(r, parse_status(b@, i as int)),
        r matches Out::Done(_, e) ==> e == i + 3,
{
    let n = b.len() - i;
    if n < 3 {
        if (n >= 1 && !(get8(b, i) >= 0x30 && get8(b, i) <= 0x39)) || (n >= 2 && !(get8(b, i + 1)
            >= 0x30 && get8(b, i + 1) <= 0x39)) {
            Out::Invalid
        } else {
            Out::Partial
        }
    } else {
        let c0 = get8(b, i);
        let c1 = get8(b, i + 1);
        let c2 = get8(b, i + 2);
        if c0 >= 0x30 && c0 <= 0x39 && c1 >= 0x30 && c1 <= 0x39 && c2 >= 0x30 && c2 <= 0x39 {
            Out::Done(
                ((c0 - 0x30) as u16) * 100 + ((c1 - 0x30) as u16) * 10 + ((c2 - 0x30) as u16),
                i + 3,
            )
        } else {
            Out::Invalid
        }
    }
}

/// Parses a response head (spec `parse_response`); see `request_at`.
#[inline(always)]
pub fn response_at(b: &[u8], max: usize, hs: &mut Vec<Header>) -> (r: (
    Out<StatusLine>,
    Ghost<nat>,
))
    ensures
        match parse_response(b@, max as nat) {
            Parsed::Done(q, end) => r.0 matches Out::Done(l, e) && e as int == end && e
                <= b@.len() && l.minor == q.minor && l.status == q.status && l.reason@
                == q.reason && headers_view(final(hs)@) == q.headers,
            Parsed::Partial => r.0 is Partial,
            Parsed::Invalid => r.0 is Invalid,
        },
        hdrs_ok(final(hs)@, b@.len() as int),
        r.1@ <= 3 * b@.len() + 16,
{
    let mut fx = None;
    response_fx(b, max, hs, false, &mut fx)
}

/// `response_at`, and with `want`, the framing fields of the head in `fx`
/// (see `headers_fx`).
pub fn response_fx(
    b: &[u8],
    max: usize,
    hs: &mut Vec<Header>,
    want: bool,
    fx: &mut Option<FieldsExec>,
) -> (r: (Out<StatusLine>, Ghost<nat>))
    ensures
        match parse_response(b@, max as nat) {
            Parsed::Done(q, end) => r.0 matches Out::Done(l, e) && e as int == end && e
                <= b@.len() && l.minor == q.minor && l.status == q.status && l.reason@
                == q.reason && headers_view(final(hs)@) == q.headers,
            Parsed::Partial => r.0 is Partial,
            Parsed::Invalid => r.0 is Invalid,
        },
        hdrs_ok(final(hs)@, b@.len() as int),
        r.1@ <= 3 * b@.len() + 16,
        want ==> fx_agrees(b@, final(hs)@, *final(fx)),
{
    hs.clear();
    *fx = Some(fields_start());
    proof {
        assert(headers_view(hs@) =~= Seq::<SpecHeader>::empty());
    }
    let (minor, j) = match version_at(b, 0) {
        Out::Done(minor, j) => (minor, j),
        Out::Partial => return (Out::Partial, Ghost(0)),
        Out::Invalid => return (Out::Invalid, Ghost(0)),
    };
    if j >= b.len() {
        return (Out::Partial, Ghost(0));
    }
    if get8(b, j) != SP {
        return (Out::Invalid, Ghost(0));
    }
    let (code, k) = match status_at(b, j + 1) {
        Out::Done(code, k) => (code, k),
        Out::Partial => return (Out::Partial, Ghost(0)),
        Out::Invalid => return (Out::Invalid, Ghost(0)),
    };
    let rs = if k < b.len() && get8(b, k) == SP {
        k + 1
    } else {
        k
    };
    let (re, g1) = if rs > k {
        scan_value_fast(b, rs)
    } else {
        (k, Ghost(0nat))
    };
    proof {
        lemma_run_end_bounds(b@, rs as int, Cls::Value);
    }
    let h = match crlf_at(b, re) {
        Out::Done(_, h) => h,
        Out::Partial => return (Out::Partial, g1),
        Out::Invalid => return (Out::Invalid, g1),
    };
    let (rh, g2) = headers_fx(b, h, max, hs, want, fx);
    let line = StatusLine { minor, status: code, reason: Span { start: rs, end: re } };
    match rh {
        Out::Done(_, end) => (Out::Done(line, end), Ghost(g1@ + g2@)),
        Out::Partial => (Out::Partial, Ghost(g1@ + g2@)),
        Out::Invalid => (Out::Invalid, Ghost(g1@ + g2@)),
    }
}

/// Whether some CR LF CR LF ends at a position in `from + 1..=len`.
pub fn crlfcrlf_after(b: &[u8], from: usize) -> (r: bool)
    requires
        from <= b@.len(),
    ensures
        !r ==> forall|e: int| from < e <= b@.len() ==> !crlfcrlf_at(b@, e),
{
    // `i` is the index of the last byte of a candidate.
    let mut i: usize = if from < 3 {
        3
    } else {
        from
    };
    while i < b.len()
        invariant
            i >= 3,
            i >= from,
            forall|f: int| from < f <= i && f <= b@.len() ==> !crlfcrlf_at(b@, f),
        decreases b@.len() - i,
    {
        if get8(b, i) == LF && get8(b, i - 1) == CR && get8(b, i - 2) == LF && get8(b, i - 3) == CR {
            return true;
        }
        i += 1;
    }
    false
}

/// `request_at` for a buffer that grows between calls, as in
/// picohttpparser: `last_len` is the buffer length at the previous call,
/// which returned `Partial` (0 on the first call). If no CR LF CR LF ends
/// in the new bytes, it returns `Partial` without parsing, so feeding a
/// head a byte at a time costs linear, not quadratic, time in total.
///
/// Proven: a `Done` or `Invalid` result is exactly the spec's. A `Partial`
/// result never hides a complete request: if the spec says `Done`, so does
/// this function, unless the head was already complete within `last_len`
/// bytes (which the previous call would have reported). An invalid head
/// may be reported as `Partial` until its CR LF CR LF arrives.
pub fn request_resume(b: &[u8], last_len: usize, max: usize, hs: &mut Vec<Header>) -> (r: (
    Out<RequestLine>,
    Ghost<nat>,
))
    ensures
        hdrs_ok(final(hs)@, b@.len() as int),
        !(r.0 is Partial) || last_len == 0 ==> match parse_request(b@, max as nat) {
            Parsed::Done(q, end) => r.0 matches Out::Done(l, e) && e as int == end && e
                <= b@.len() && l.method@ == q.method && l.target@ == q.target && l.minor
                == q.minor && headers_view(final(hs)@) == q.headers,
            Parsed::Partial => r.0 is Partial,
            Parsed::Invalid => r.0 is Invalid,
        },
        r.0 is Partial ==> !(parse_request(b@, max as nat) is Done) || (0 < last_len <= b@.len()
            && parse_request(b@.subrange(0, last_len as int), max as nat) is Done),
        r.1@ <= 3 * b@.len() + 16 + b@.len(),
{
    if last_len > 0 && last_len <= b.len() && !crlfcrlf_after(b, last_len) {
        proof {
            if !(parse_request(b@.subrange(0, last_len as int), max as nat) is Done) {
                theorem_request_resume(b@, last_len as int, max as nat);
            }
        }
        hs.clear();
        return (Out::Partial, Ghost(b@.len()));
    }
    let (r, g) = request_at(b, max, hs);
    (r, Ghost(g@ + b@.len()))
}

} // verus!
