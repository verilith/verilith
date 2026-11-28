//! Verified content-coding negotiation (RFC 9110 §12.5.3, §12.4.2).
//!
//! The proxy compresses a response only with a coding the request
//! accepts: [`accept_q`] is the weight `Accept-Encoding` gives a coding
//! (its own element, else `*`, else 0), with q-values read as thousandths
//! (`q=0.5` is 500, `q=0` excludes). [`choose`] picks, among Brotli,
//! Zstandard and gzip, one with the highest positive weight (ties in that
//! order), or none: [`chosen_ok`] is the property, and it is proven for
//! every header value. So `gzip;q=0` is never answered with gzip, and a
//! request that names no supported coding gets the representation
//! uncompressed.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use verilith_http::spec::{is_ows, lower, trim_end};
#[cfg(verus_keep_ghost)]
use verilith_server::persist::{comma_end, element, lead};
#[cfg(verus_keep_ghost)]
use verilith_server::persist::{lemma_comma_end, lemma_lead, lemma_trim};
use crate::hop::same_ci_exec;
#[cfg(verus_keep_ghost)]
use crate::hop::same_ci;
use vstd::slice::slice_subrange;
#[cfg(verus_only)]
use verilith_core::num::is_digit;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// The first `;` in `v[i..e]`, or `e`.
pub open spec fn semi_end(v: Seq<u8>, i: int, e: int) -> int
    decreases e - i,
{
    if i >= e || i < 0 || i >= v.len() || v[i] == 0x3b { i } else { semi_end(v, i + 1, e) }
}

pub open spec fn digit_val(c: u8) -> nat {
    (c - 0x30) as nat
}

/// `qvalue = ( "0" [ "." 0*3DIGIT ] ) / ( "1" [ "." 0*3("0") ] )`, in
/// thousandths.
pub open spec fn qvalue(s: Seq<u8>) -> Option<nat> {
    if s.len() == 0 {
        None
    } else if s.len() > 1 && (s[1] != 0x2e || s.len() > 5) {
        None
    } else if s[0] == 0x30 {
        if forall|k: int| 2 <= k < s.len() ==> is_digit(#[trigger] s[k]) {
            let d1: nat = if s.len() > 2 { digit_val(s[2]) } else { 0 };
            let d2: nat = if s.len() > 3 { digit_val(s[3]) } else { 0 };
            let d3: nat = if s.len() > 4 { digit_val(s[4]) } else { 0 };
            Some(d1 * 100 + d2 * 10 + d3)
        } else {
            None
        }
    } else if s[0] == 0x31 {
        if forall|k: int| 2 <= k < s.len() ==> #[trigger] s[k] == 0x30 { Some(1000) } else { None }
    } else {
        None
    }
}

/// The weight of an element whose parameters are `v[s..e]` (just after
/// its `;`): `q=` (either case) and a qvalue, with OWS around; anything
/// else gives 0, so a malformed weight never makes a coding acceptable.
pub open spec fn weight(v: Seq<u8>, s: int, e: int) -> nat {
    let a = lead(v, s, e);
    let w = v.subrange(a, trim_end(v, a, e));
    if w.len() >= 2 && lower(w[0]) == 0x71 && w[1] == 0x3d {
        match qvalue(w.subrange(2, w.len() as int)) {
            Some(q) => q,
            None => 0,
        }
    } else {
        0
    }
}

/// The element `v[i..c]`: its coding, and its weight (1000 without one).
pub open spec fn el_coding(v: Seq<u8>, i: int, c: int) -> Seq<u8> {
    element(v, i, semi_end(v, i, c))
}

pub open spec fn el_weight(v: Seq<u8>, i: int, c: int) -> nat {
    let s = semi_end(v, i, c);
    if s >= c { 1000 } else { weight(v, s + 1, c) }
}

/// The weight of the first element of `v[i..]` whose coding is `name`.
pub open spec fn find_q(v: Seq<u8>, i: int, name: Seq<u8>) -> Option<nat>
    decreases v.len() - i,
{
    if i < 0 || i > v.len() {
        None
    } else {
        let c = comma_end(v, i);
        if same_ci(el_coding(v, i, c), name) {
            Some(el_weight(v, i, c))
        } else if i <= c < v.len() {
            find_q(v, c + 1, name)
        } else {
            None
        }
    }
}

pub open spec fn star() -> Seq<u8> {
    seq![0x2au8]
}

/// The weight `Accept-Encoding: v` gives `name`.
pub open spec fn accept_q(v: Seq<u8>, name: Seq<u8>) -> nat {
    match find_q(v, 0, name) {
        Some(q) => q,
        None => match find_q(v, 0, star()) {
            Some(q) => q,
            None => 0,
        },
    }
}

/// The codings the proxy compresses with, in its order of preference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coding {
    Br,
    Zstd,
    Gzip,
}

pub open spec fn s_br() -> Seq<u8> { seq![0x62u8, 0x72] }
pub open spec fn s_zstd() -> Seq<u8> { seq![0x7au8, 0x73, 0x74, 0x64] }
pub open spec fn s_gzip() -> Seq<u8> { seq![0x67u8, 0x7a, 0x69, 0x70] }

pub open spec fn coding_name(c: Coding) -> Seq<u8> {
    match c {
        Coding::Br => s_br(),
        Coding::Zstd => s_zstd(),
        Coding::Gzip => s_gzip(),
    }
}

/// `r` is a right choice for `Accept-Encoding: v` among the codings
/// `allowed` lets the proxy use: one with positive weight that no allowed
/// coding outweighs, or none when every allowed coding weighs 0.
pub open spec fn chosen_ok(v: Seq<u8>, allowed: spec_fn(Coding) -> bool, r: Option<Coding>) -> bool {
    match r {
        Some(c) => allowed(c) && accept_q(v, coding_name(c)) > 0 && forall|d: Coding| #[trigger] allowed(d)
            ==> accept_q(v, coding_name(d)) <= accept_q(v, coding_name(c)),
        None => forall|d: Coding| #[trigger] allowed(d) ==> accept_q(v, coding_name(d)) == 0,
    }
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

proof fn lemma_semi_end(v: Seq<u8>, i: int, e: int)
    requires
        0 <= i <= e <= v.len(),
    ensures
        i <= semi_end(v, i, e) <= e,
    decreases e - i,
{
    if !(i >= e || v[i] == 0x3b) {
        lemma_semi_end(v, i + 1, e);
    }
}

fn is_digit_exec(c: u8) -> (r: bool)
    ensures
        r == is_digit(c),
{
    c >= 0x30 && c <= 0x39
}

/// [`qvalue`].
pub fn qvalue_exec(s: &[u8]) -> (r: Option<u32>)
    ensures
        match qvalue(s@) {
            Some(q) => r == Some(q as u32) && q <= 1000,
            None => r is None,
        },
{
    let n = s.len();
    if n == 0 {
        return None;
    }
    if n > 1 && (s[1] != 0x2e || n > 5) {
        return None;
    }
    if s[0] == 0x30 {
        let mut k = 2;
        while k < n
            invariant
                n == s@.len(),
                2 <= k,
                forall|j: int| 2 <= j < k && j < n ==> is_digit(#[trigger] s@[j]),
                s@[0] == 0x30,
                n > 1 ==> s@[1] == 0x2e && n <= 5,
            decreases n - k,
        {
            if !is_digit_exec(s[k]) {
                return None;
            }
            k += 1;
        }
        let d1: u32 = if n > 2 { (s[2] - 0x30) as u32 } else { 0 };
        let d2: u32 = if n > 3 { (s[3] - 0x30) as u32 } else { 0 };
        let d3: u32 = if n > 4 { (s[4] - 0x30) as u32 } else { 0 };
        Some(d1 * 100 + d2 * 10 + d3)
    } else if s[0] == 0x31 {
        let mut k = 2;
        while k < n
            invariant
                n == s@.len(),
                2 <= k,
                forall|j: int| 2 <= j < k && j < n ==> #[trigger] s@[j] == 0x30,
                s@[0] == 0x31,
                n > 1 ==> s@[1] == 0x2e && n <= 5,
            decreases n - k,
        {
            if s[k] != 0x30 {
                assert(2 <= k < s@.len() && s@[k as int] != 0x30);
                return None;
            }
            k += 1;
        }
        Some(1000)
    } else {
        None
    }
}

/// `v[s..e]` with OWS trimmed from both ends: (start, end).
fn trim_range(v: &[u8], s: usize, e: usize) -> (r: (usize, usize))
    requires
        s <= e <= v@.len(),
    ensures
        r.0 == lead(v@, s as int, e as int),
        r.1 == trim_end(v@, r.0 as int, e as int),
        s <= r.0 <= r.1 <= e,
{
    let mut a = s;
    proof {
        lemma_lead(v@, s as int, e as int);
    }
    while a < e && (v[a] == 0x20 || v[a] == 0x09)
        invariant
            s <= a <= e <= v@.len(),
            lead(v@, s as int, e as int) == lead(v@, a as int, e as int),
        decreases e - a,
    {
        a += 1;
    }
    let mut t = e;
    proof {
        lemma_trim(v@, a as int, e as int);
    }
    while t > a && (v[t - 1] == 0x20 || v[t - 1] == 0x09)
        invariant
            a <= t <= e <= v@.len(),
            trim_end(v@, a as int, e as int) == trim_end(v@, a as int, t as int),
        decreases t - a,
    {
        t -= 1;
    }
    proof {
        lemma_trim(v@, a as int, t as int);
    }
    (a, t)
}

fn weight_exec(v: &[u8], s: usize, e: usize) -> (r: u32)
    requires
        s <= e <= v@.len(),
    ensures
        r as nat == weight(v@, s as int, e as int),
        r <= 1000,
{
    let (a, t) = trim_range(v, s, e);
    let w = slice_subrange(v, a, t);
    assert(w@ =~= v@.subrange(a as int, trim_end(v@, a as int, e as int)));
    if w.len() >= 2 && (w[0] == 0x71 || w[0] == 0x51) && w[1] == 0x3d {
        assert(lower(w@[0]) == 0x71 <==> (w@[0] == 0x71 || w@[0] == 0x51));
        let q = slice_subrange(w, 2, w.len());
        assert(q@ =~= w@.subrange(2, w@.len() as int));
        match qvalue_exec(q) {
            Some(x) => x,
            None => 0,
        }
    } else {
        assert(w@.len() >= 2 ==> (lower(w@[0]) == 0x71 <==> (w@[0] == 0x71 || w@[0] == 0x51)));
        0
    }
}

/// [`find_q`] from 0, as a weight in thousandths.
pub fn find_q_exec(v: &[u8], name: &[u8]) -> (r: Option<u32>)
    ensures
        match find_q(v@, 0, name@) {
            Some(q) => r == Some(q as u32) && q <= 1000,
            None => r is None,
        },
{
    let len = v.len();
    let mut i: usize = 0;
    loop
        invariant
            len == v@.len(),
            i <= len,
            find_q(v@, 0, name@) == find_q(v@, i as int, name@),
        decreases len - i,
    {
        proof {
            lemma_comma_end(v@, i as int);
        }
        let mut c = i;
        while c < len && v[c] != 0x2c
            invariant
                len == v@.len(),
                i <= c <= len,
                comma_end(v@, i as int) == comma_end(v@, c as int),
            decreases len - c,
        {
            c += 1;
        }
        let mut s = i;
        proof {
            lemma_semi_end(v@, i as int, c as int);
        }
        while s < c && v[s] != 0x3b
            invariant
                len == v@.len(),
                i <= s <= c <= len,
                semi_end(v@, i as int, c as int) == semi_end(v@, s as int, c as int),
            decreases c - s,
        {
            s += 1;
        }
        let (a, t) = trim_range(v, i, s);
        let el = slice_subrange(v, a, t);
        assert(el@ =~= element(v@, i as int, s as int));
        if same_ci_exec(el, name) {
            if s >= c {
                return Some(1000);
            }
            return Some(weight_exec(v, s + 1, c));
        }
        if c >= len {
            return None;
        }
        i = c + 1;
    }
}

/// [`accept_q`], in thousandths.
pub fn accept_q_exec(v: &[u8], name: &[u8]) -> (r: u32)
    ensures
        r as nat == accept_q(v@, name@),
        r <= 1000,
{
    match find_q_exec(v, name) {
        Some(q) => q,
        None => {
            let st: [u8; 1] = [0x2a];
            assert(st@ =~= star());
            match find_q_exec(v, &st) {
                Some(q) => q,
                None => 0,
            }
        },
    }
}

/// The coding to compress with for `Accept-Encoding: v`, among those
/// allowed (`br`, `zstd`, `gzip`): [`chosen_ok`].
pub fn choose(v: &[u8], br: bool, zstd: bool, gzip: bool) -> (r: Option<Coding>)
    ensures
        chosen_ok(v@, |c: Coding| match c {
            Coding::Br => br,
            Coding::Zstd => zstd,
            Coding::Gzip => gzip,
        }, r),
{
    let nb: [u8; 2] = [0x62, 0x72];
    let nz: [u8; 4] = [0x7a, 0x73, 0x74, 0x64];
    let ng: [u8; 4] = [0x67, 0x7a, 0x69, 0x70];
    assert(nb@ =~= s_br());
    assert(nz@ =~= s_zstd());
    assert(ng@ =~= s_gzip());
    let qb = if br { accept_q_exec(v, &nb) } else { 0 };
    let qz = if zstd { accept_q_exec(v, &nz) } else { 0 };
    let qg = if gzip { accept_q_exec(v, &ng) } else { 0 };
    let ghost allowed = |c: Coding| match c {
        Coding::Br => br,
        Coding::Zstd => zstd,
        Coding::Gzip => gzip,
    };
    let r = if qb > 0 && qb >= qz && qb >= qg {
        Some(Coding::Br)
    } else if qz > 0 && qz >= qg {
        Some(Coding::Zstd)
    } else if qg > 0 {
        Some(Coding::Gzip)
    } else {
        None
    };
    proof {
        assert forall|d: Coding| #[trigger] allowed(d) implies accept_q(v@, coding_name(d)) == match d {
            Coding::Br => qb as nat,
            Coding::Zstd => qz as nat,
            Coding::Gzip => qg as nat,
        } by {}
    }
    r
}

} // verus!
