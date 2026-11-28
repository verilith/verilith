//! The tokenizer: each function here computes one function of `spec.rs`,
//! and is proven to return exactly what it returns.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A token. `start..end` are positions in the preprocessed code points the
/// tokenizer was given; `value` is the token's code points after escapes
/// are resolved (empty for kinds without a value); `repr_end` is where a
/// numeric token's number ends (`end` for other kinds).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: Kind,
    pub start: usize,
    pub end: usize,
    pub value: Vec<u32>,
    pub repr_end: usize,
}

impl View for Token {
    type V = SToken;

    open spec fn view(&self) -> SToken {
        SToken {
            kind: self.kind,
            start: self.start as int,
            end: self.end as int,
            value: self.value@,
            repr_end: self.repr_end as int,
        }
    }
}

pub open spec fn views(ts: Seq<Token>) -> Seq<SToken> {
    ts.map_values(|t: Token| t@)
}

// ---------------------------------------------------------------------------
// Preprocessing
// ---------------------------------------------------------------------------

fn x_pre_cp(c: u32) -> (r: u32)
    ensures
        r == pre_cp(c),
{
    if c == 0 || (0xD800 <= c && c <= 0xDFFF) {
        0xFFFD
    } else if c == 0x0C || c == 0x0D {
        0x0A
    } else {
        c
    }
}

/// §3.3: CR LF, CR and FF become LF; NUL and surrogates become U+FFFD.
pub fn preprocess(s: &[u32]) -> (r: Vec<u32>)
    ensures
        r@ == crate::spec::preprocess(s@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ + preprocess_from(s@, i as int) == preprocess_from(s@, 0),
        decreases s.len() - i,
    {
        let c = s[i];
        if c == 0x0D && i + 1 < s.len() && s[i + 1] == 0x0A {
            proof {
                assert(out@ + preprocess_from(s@, i as int) =~= out@.push(0x0Au32) + preprocess_from(s@, i + 2));
            }
            out.push(0x0A);
            i += 2;
        } else {
            let p = x_pre_cp(c);
            proof {
                assert(out@ + preprocess_from(s@, i as int) =~= out@.push(p) + preprocess_from(s@, i + 1));
            }
            out.push(p);
            i += 1;
        }
    }
    proof {
        assert(out@ + preprocess_from(s@, i as int) =~= out@);
    }
    out
}

// ---------------------------------------------------------------------------
// Code points and classes
// ---------------------------------------------------------------------------

/// The code point at `i + d`, or -1 past the end.
#[inline(always)]
fn peek(s: &[u32], i: usize, d: usize) -> (r: i64)
    requires
        d <= 4,
    ensures
        r == at(s@, i + d),
{
    if i < s.len() && d < s.len() - i {
        s[i + d] as i64
    } else {
        -1
    }
}

#[inline(always)]
fn x_digit(c: i64) -> (r: bool)
    ensures
        r == is_digit(c as int),
{
    0x30 <= c && c <= 0x39
}

#[inline(always)]
fn x_hex(c: i64) -> (r: bool)
    ensures
        r == is_hex(c as int),
{
    (0x30 <= c && c <= 0x39) || (0x41 <= c && c <= 0x46) || (0x61 <= c && c <= 0x66)
}

#[inline(always)]
fn x_hex_val(c: i64) -> (r: u32)
    requires
        is_hex(c as int),
    ensures
        r == hex_val(c as int),
        r < 16,
{
    if 0x30 <= c && c <= 0x39 {
        (c - 0x30) as u32
    } else if 0x41 <= c && c <= 0x46 {
        (c - 0x41 + 10) as u32
    } else {
        (c - 0x61 + 10) as u32
    }
}

#[inline(always)]
fn x_ident_start(c: i64) -> (r: bool)
    ensures
        r == is_ident_start(c as int),
{
    (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A) || c >= 0x80 || c == 0x5F
}

#[inline(always)]
fn x_ident_cp(c: i64) -> (r: bool)
    ensures
        r == is_ident_cp(c as int),
{
    x_ident_start(c) || x_digit(c) || c == 0x2D
}

#[inline(always)]
fn x_ws(c: i64) -> (r: bool)
    ensures
        r == is_ws(c as int),
{
    c == 0x0A || c == 0x09 || c == 0x20
}

#[inline(always)]
fn x_non_printable(c: i64) -> (r: bool)
    ensures
        r == is_non_printable(c as int),
{
    (0 <= c && c <= 0x08) || c == 0x0B || (0x0E <= c && c <= 0x1F) || c == 0x7F
}

#[inline(always)]
fn x_valid_escape(a: i64, b: i64) -> (r: bool)
    ensures
        r == valid_escape(a as int, b as int),
{
    a == 0x5C && b != 0x0A
}

#[inline(always)]
fn x_escape_at(s: &[u32], i: usize) -> (r: bool)
    ensures
        r == escape_at(s@, i as int),
{
    x_valid_escape(peek(s, i, 0), peek(s, i, 1))
}

fn x_ident_at(s: &[u32], i: usize) -> (r: bool)
    ensures
        r == ident_at(s@, i as int),
{
    let a = peek(s, i, 0);
    let b = peek(s, i, 1);
    let c = peek(s, i, 2);
    if a == 0x2D {
        x_ident_start(b) || b == 0x2D || x_valid_escape(b, c)
    } else if x_ident_start(a) {
        true
    } else if a == 0x5C {
        x_valid_escape(a, b)
    } else {
        false
    }
}

fn x_number_at(s: &[u32], i: usize) -> (r: bool)
    ensures
        r == number_at(s@, i as int),
{
    let a = peek(s, i, 0);
    let b = peek(s, i, 1);
    let c = peek(s, i, 2);
    if a == 0x2B || a == 0x2D {
        x_digit(b) || (b == 0x2E && x_digit(c))
    } else if a == 0x2E {
        x_digit(b)
    } else {
        x_digit(a)
    }
}

// ---------------------------------------------------------------------------
// Runs
// ---------------------------------------------------------------------------

fn x_ws_end(s: &[u32], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r == ws_end(s@, i as int),
        i <= r <= s.len(),
        is_ws(at(s@, i as int)) ==> r > i,
{
    let mut k = i;
    while k < s.len() && x_ws(s[k] as i64)
        invariant
            i <= k <= s.len(),
            ws_end(s@, k as int) == ws_end(s@, i as int),
            k == i || k > i,
        decreases s.len() - k,
    {
        k += 1;
    }
    k
}

fn x_digits_end(s: &[u32], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r == digits_end(s@, i as int),
        i <= r <= s.len(),
        is_digit(at(s@, i as int)) ==> r > i,
{
    let mut k = i;
    while k < s.len() && x_digit(s[k] as i64)
        invariant
            i <= k <= s.len(),
            digits_end(s@, k as int) == digits_end(s@, i as int),
            k == i || k > i,
        decreases s.len() - k,
    {
        k += 1;
    }
    k
}

pub open spec fn p16(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1
    } else {
        16 * p16((n - 1) as nat)
    }
}

/// The run of at most six hex digits at `i`, and its value.
fn x_hex_run(s: &[u32], i: usize) -> (r: (usize, u32))
    requires
        i <= s.len(),
    ensures
        r.0 == hex_end(s@, i as int, 6),
        r.1 as int == hex_value(s@, i as int, r.0 as int),
        i <= r.0 <= s.len(),
{
    let mut k = i;
    let mut v: u32 = 0;
    while k - i < 6 && k < s.len() && x_hex(s[k] as i64)
        invariant
            i <= k <= s.len(),
            k - i <= 6,
            hex_end(s@, k as int, 6 - (k - i)) == hex_end(s@, i as int, 6),
            v as int == hex_value(s@, i as int, k as int),
            0 <= v < p16((k - i) as nat),
        decreases s.len() - k,
    {
        let d = x_hex_val(s[k] as i64);
        proof {
            assert(p16(6) == 0x1000000) by (compute_only);
            let n = (k - i) as nat;
            assert(p16(n + 1) == 16 * p16(n));
            assert(p16(n) <= p16(6)) by {
                assert(p16(5) == 0x100000) by (compute_only);
                assert(p16(4) == 0x10000) by (compute_only);
                assert(p16(3) == 0x1000) by (compute_only);
                assert(p16(2) == 0x100) by (compute_only);
                assert(p16(1) == 0x10) by (compute_only);
                assert(p16(0) == 1);
            }
            assert(v * 16 + d < 16 * p16(n)) by (nonlinear_arith)
                requires
                    v < p16(n),
                    d < 16,
            ;
        }
        v = v * 16 + d;
        k += 1;
    }
    (k, v)
}

// ---------------------------------------------------------------------------
// §4.3.2 Comments
// ---------------------------------------------------------------------------

fn x_comment_end(s: &[u32], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r == comment_end(s@, i as int),
        i <= r <= s.len(),
{
    let mut k = i;
    while k < s.len() && !(peek(s, k, 0) == 0x2A && peek(s, k, 1) == 0x2F)
        invariant
            i <= k <= s.len(),
            comment_end(s@, k as int) == comment_end(s@, i as int),
        decreases s.len() - k,
    {
        k += 1;
    }
    if k < s.len() {
        k + 2
    } else {
        k
    }
}

fn x_skip_comments(s: &[u32], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r == skip_comments(s@, i as int),
        i <= r <= s.len(),
{
    let mut k = i;
    while peek(s, k, 0) == 0x2F && peek(s, k, 1) == 0x2A
        invariant
            i <= k <= s.len(),
            skip_comments(s@, k as int) == skip_comments(s@, i as int),
        decreases s.len() - k,
    {
        k = x_comment_end(s, k + 2);
    }
    k
}

// ---------------------------------------------------------------------------
// §4.3.7 Escapes and §4.3.12 ident sequences
// ---------------------------------------------------------------------------

fn x_escape(s: &[u32], i: usize) -> (r: (u32, usize))
    requires
        i <= s.len(),
    ensures
        r.0 == escape(s@, i as int).0,
        r.1 == escape(s@, i as int).1,
        i <= r.1 <= s.len(),
{
    let c = peek(s, i, 0);
    if x_hex(c) {
        let (e, v) = x_hex_run(s, i);
        let j = if x_ws(peek(s, e, 0)) {
            e + 1
        } else {
            e
        };
        let cp = if v == 0 || (0xD800 <= v && v <= 0xDFFF) || v > MAX_CP {
            0xFFFD
        } else {
            v
        };
        (cp, j)
    } else if c == -1 {
        (0xFFFD, i)
    } else {
        (c as u32, i + 1)
    }
}

proof fn lemma_cons<T>(a: Seq<T>, x: T, b: Seq<T>)
    ensures
        a + (seq![x] + b) == a.push(x) + b,
{
    assert(a + (seq![x] + b) =~= a.push(x) + b);
}

/// Appends the ident sequence at `i` to `out`; returns its end.
fn x_ident_seq(s: &[u32], i: usize, out: &mut Vec<u32>) -> (j: usize)
    requires
        i <= s.len(),
    ensures
        final(out)@ == old(out)@ + ident_seq(s@, i as int).0,
        j == ident_seq(s@, i as int).1,
        i <= j <= s.len(),
        (is_ident_cp(at(s@, i as int)) || escape_at(s@, i as int)) ==> j > i,
{
    let mut k = i;
    loop
        invariant
            i <= k <= s.len(),
            old(out)@ + ident_seq(s@, i as int).0 == out@ + ident_seq(s@, k as int).0,
            ident_seq(s@, i as int).1 == ident_seq(s@, k as int).1,
            k == i || k > i,
        ensures
            i <= k <= s.len(),
            old(out)@ + ident_seq(s@, i as int).0 == out@,
            ident_seq(s@, i as int).1 == k,
            k == i ==> !(is_ident_cp(at(s@, i as int)) || escape_at(s@, i as int)),
        decreases s.len() - k,
    {
        if k >= s.len() {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            break;
        }
        let c = s[k] as i64;
        if x_ident_cp(c) {
            proof {
                lemma_cons(out@, s@[k as int], ident_seq(s@, k + 1).0);
            }
            out.push(s[k]);
            k += 1;
        } else if x_escape_at(s, k) {
            let (cp, e) = x_escape(s, k + 1);
            proof {
                lemma_cons(out@, cp, ident_seq(s@, e as int).0);
            }
            out.push(cp);
            k = e;
        } else {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            break;
        }
    }
    k
}

// ---------------------------------------------------------------------------
// §4.3.13 Numbers
// ---------------------------------------------------------------------------

fn x_number_end(s: &[u32], i: usize) -> (r: (usize, bool))
    requires
        i <= s.len(),
    ensures
        r.0 == number_end(s@, i as int).0,
        r.1 == number_end(s@, i as int).1,
        i <= r.0 <= s.len(),
        number_at(s@, i as int) ==> r.0 > i,
{
    let a = peek(s, i, 0);
    let j = if a == 0x2B || a == 0x2D {
        i + 1
    } else {
        i
    };
    let k = x_digits_end(s, j);
    let (k2, int1) = if peek(s, k, 0) == 0x2E && x_digit(peek(s, k, 1)) {
        (x_digits_end(s, k + 2), false)
    } else {
        (k, true)
    };
    let e = peek(s, k2, 0);
    let k3 = if e == 0x45 || e == 0x65 {
        let n = peek(s, k2, 1);
        if x_digit(n) {
            x_digits_end(s, k2 + 2)
        } else if (n == 0x2B || n == 0x2D) && x_digit(peek(s, k2, 2)) {
            x_digits_end(s, k2 + 3)
        } else {
            k2
        }
    } else {
        k2
    };
    proof {
        if number_at(s@, i as int) && j == i && !is_digit(at(s@, i as int)) {
            // A number starting with U+002E FULL STOP.
            assert(k == i);
            assert(k2 >= k + 2);
        }
    }
    (k3, int1 && k3 == k2)
}

// ---------------------------------------------------------------------------
// §4.3.5 Strings
// ---------------------------------------------------------------------------

/// Appends the string body at `i` to `out`; returns its end and whether it
/// is bad.
fn x_string_body(s: &[u32], i: usize, q: i64, out: &mut Vec<u32>) -> (r: (usize, bool))
    requires
        i <= s.len(),
    ensures
        final(out)@ == old(out)@ + string_body(s@, i as int, q as int).0,
        r.0 == string_body(s@, i as int, q as int).1,
        r.1 == string_body(s@, i as int, q as int).2,
        i <= r.0 <= s.len(),
{
    let mut k = i;
    loop
        invariant
            i <= k <= s.len(),
            old(out)@ + string_body(s@, i as int, q as int).0 == out@ + string_body(s@, k as int, q as int).0,
            string_body(s@, i as int, q as int).1 == string_body(s@, k as int, q as int).1,
            string_body(s@, i as int, q as int).2 == string_body(s@, k as int, q as int).2,
        decreases s.len() - k,
    {
        if k >= s.len() {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            return (k, false);
        }
        let c = s[k] as i64;
        if c == q {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            return (k + 1, false);
        } else if c == 0x0A {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            return (k, true);
        } else if c == 0x5C {
            if k + 1 >= s.len() {
                proof {
                    assert(out@ + seq![] =~= out@);
                }
                return (k + 1, false);
            } else if s[k + 1] == 0x0A {
                k += 2;
            } else {
                let (cp, e) = x_escape(s, k + 1);
                proof {
                    lemma_cons(out@, cp, string_body(s@, e as int, q as int).0);
                }
                out.push(cp);
                k = e;
            }
        } else {
            proof {
                lemma_cons(out@, s@[k as int], string_body(s@, k + 1, q as int).0);
            }
            out.push(s[k]);
            k += 1;
        }
    }
}

// ---------------------------------------------------------------------------
// §4.3.6 Urls and §4.3.15 the remnants of a bad url
// ---------------------------------------------------------------------------

fn x_bad_url_end(s: &[u32], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r == bad_url_end(s@, i as int),
        i <= r <= s.len(),
{
    let mut k = i;
    loop
        invariant_except_break
            bad_url_end(s@, k as int) == bad_url_end(s@, i as int),
        invariant
            i <= k <= s.len(),
        ensures
            i <= k <= s.len(),
            bad_url_end(s@, i as int) == k,
        decreases s.len() - k,
    {
        if k >= s.len() {
            break;
        }
        if s[k] == 0x29 {
            k += 1;
            break;
        } else if x_escape_at(s, k) {
            let (_, e) = x_escape(s, k + 1);
            k = e;
        } else {
            k += 1;
        }
    }
    k
}

/// Appends the url body at `i` to `out`; returns its end and whether it is
/// a bad url.
fn x_url_body(s: &[u32], i: usize, out: &mut Vec<u32>) -> (r: (usize, bool))
    requires
        i <= s.len(),
    ensures
        final(out)@ == old(out)@ + url_body(s@, i as int).0,
        r.0 == url_body(s@, i as int).1,
        r.1 == url_body(s@, i as int).2,
        i <= r.0 <= s.len(),
{
    let mut k = i;
    loop
        invariant
            i <= k <= s.len(),
            old(out)@ + url_body(s@, i as int).0 == out@ + url_body(s@, k as int).0,
            url_body(s@, i as int).1 == url_body(s@, k as int).1,
            url_body(s@, i as int).2 == url_body(s@, k as int).2,
        decreases s.len() - k,
    {
        if k >= s.len() {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            return (k, false);
        }
        let c = s[k] as i64;
        if c == 0x29 {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            return (k + 1, false);
        } else if x_ws(c) {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            let j = x_ws_end(s, k);
            let n = peek(s, j, 0);
            if n == 0x29 {
                return (j + 1, false);
            } else if n == -1 {
                return (j, false);
            } else {
                return (x_bad_url_end(s, j), true);
            }
        } else if c == 0x22 || c == 0x27 || c == 0x28 || x_non_printable(c) {
            proof {
                assert(out@ + seq![] =~= out@);
            }
            return (x_bad_url_end(s, k + 1), true);
        } else if c == 0x5C {
            if x_escape_at(s, k) {
                let (cp, e) = x_escape(s, k + 1);
                proof {
                    lemma_cons(out@, cp, url_body(s@, e as int).0);
                }
                out.push(cp);
                k = e;
            } else {
                proof {
                    assert(out@ + seq![] =~= out@);
                }
                return (x_bad_url_end(s, k + 1), true);
            }
        } else {
            proof {
                lemma_cons(out@, s@[k as int], url_body(s@, k + 1).0);
            }
            out.push(s[k]);
            k += 1;
        }
    }
}

// ---------------------------------------------------------------------------
// §4.3.4 Ident-like tokens and §4.3.3 numeric tokens
// ---------------------------------------------------------------------------

#[inline(always)]
fn x_lower(c: u32) -> (r: u32)
    ensures
        r == lower(c),
{
    if 0x41 <= c && c <= 0x5A {
        c + 0x20
    } else {
        c
    }
}

fn x_is_url(v: &Vec<u32>) -> (r: bool)
    ensures
        r == is_url(v@),
{
    v.len() == 3 && x_lower(v[0]) == 0x75 && x_lower(v[1]) == 0x72 && x_lower(v[2]) == 0x6C
}

fn x_url_ws(s: &[u32], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r == url_ws(s@, i as int),
        i <= r <= s.len(),
{
    let mut k = i;
    while k < s.len() && x_ws(s[k] as i64) && x_ws(peek(s, k, 1))
        invariant
            i <= k <= s.len(),
            url_ws(s@, k as int) == url_ws(s@, i as int),
        decreases s.len() - k,
    {
        k += 1;
    }
    k
}

fn mk(kind: Kind, start: usize, end: usize, value: Vec<u32>) -> (t: Token)
    ensures
        t@ == tok(kind, start as int, end as int, value@),
{
    Token { kind, start, end, value, repr_end: end }
}

fn x_ident_like(s: &[u32], i: usize) -> (t: Token)
    requires
        i <= s.len(),
        ident_at(s@, i as int) || escape_at(s@, i as int),
    ensures
        t@ == ident_like(s@, i as int),
        i < t.end <= s.len(),
{
    let mut v: Vec<u32> = Vec::new();
    let j = x_ident_seq(s, i, &mut v);
    proof {
        assert(v@ =~= ident_seq(s@, i as int).0);
        // An ident sequence starts with an ident code point or an escape.
        assert(is_ident_cp(at(s@, i as int)) || escape_at(s@, i as int));
    }
    if x_is_url(&v) && peek(s, j, 0) == 0x28 {
        let k = x_url_ws(s, j + 1);
        let c0 = peek(s, k, 0);
        let c1 = peek(s, k, 1);
        if c0 == 0x22 || c0 == 0x27 || (x_ws(c0) && (c1 == 0x22 || c1 == 0x27)) {
            mk(Kind::Function, i, k, v)
        } else {
            let w = x_ws_end(s, k);
            let mut u: Vec<u32> = Vec::new();
            let (e, bad) = x_url_body(s, w, &mut u);
            proof {
                assert(u@ =~= url_body(s@, w as int).0);
            }
            if bad {
                mk(Kind::BadUrl, i, e, Vec::new())
            } else {
                mk(Kind::Url, i, e, u)
            }
        }
    } else if peek(s, j, 0) == 0x28 {
        mk(Kind::Function, i, j + 1, v)
    } else {
        mk(Kind::Ident, i, j, v)
    }
}

fn x_numeric(s: &[u32], i: usize) -> (t: Token)
    requires
        i <= s.len(),
        number_at(s@, i as int),
    ensures
        t@ == numeric(s@, i as int),
        i < t.end <= s.len(),
{
    let (e, integer) = x_number_end(s, i);
    if x_ident_at(s, e) {
        let mut v: Vec<u32> = Vec::new();
        let u = x_ident_seq(s, e, &mut v);
        proof {
            assert(v@ =~= ident_seq(s@, e as int).0);
        }
        Token { kind: Kind::Dimension { integer }, start: i, end: u, value: v, repr_end: e }
    } else if peek(s, e, 0) == 0x25 {
        Token { kind: Kind::Percentage { integer }, start: i, end: e + 1, value: Vec::new(), repr_end: e }
    } else {
        Token { kind: Kind::Number { integer }, start: i, end: e, value: Vec::new(), repr_end: e }
    }
}

// ---------------------------------------------------------------------------
// §4.3.1 Consume a token
// ---------------------------------------------------------------------------

#[inline(always)]
fn x_delim(i: usize, c: i64) -> (t: Token)
    requires
        0 <= c <= u32::MAX,
        i < usize::MAX,
    ensures
        t@ == delim(i as int, c as int),
{
    mk(Kind::Delim(c as u32), i, i + 1, Vec::new())
}

fn x_next_token(s: &[u32], i: usize) -> (t: Token)
    requires
        i < s.len(),
    ensures
        t@ == next_token(s@, i as int),
        i < t.end <= s.len(),
{
    let c = s[i] as i64;
    if x_ws(c) {
        mk(Kind::Whitespace, i, x_ws_end(s, i), Vec::new())
    } else if c == 0x22 || c == 0x27 {
        let mut v: Vec<u32> = Vec::new();
        let (e, bad) = x_string_body(s, i + 1, c, &mut v);
        proof {
            assert(v@ =~= string_body(s@, i + 1, c as int).0);
        }
        if bad {
            mk(Kind::BadString, i, e, Vec::new())
        } else {
            mk(Kind::String, i, e, v)
        }
    } else if c == 0x23 {
        if x_ident_cp(peek(s, i, 1)) || x_escape_at(s, i + 1) {
            let id = x_ident_at(s, i + 1);
            let mut v: Vec<u32> = Vec::new();
            let e = x_ident_seq(s, i + 1, &mut v);
            proof {
                assert(v@ =~= ident_seq(s@, i + 1).0);
            }
            mk(Kind::Hash { id }, i, e, v)
        } else {
            x_delim(i, c)
        }
    } else if c == 0x28 {
        mk(Kind::LeftParen, i, i + 1, Vec::new())
    } else if c == 0x29 {
        mk(Kind::RightParen, i, i + 1, Vec::new())
    } else if c == 0x2B {
        if x_number_at(s, i) {
            x_numeric(s, i)
        } else {
            x_delim(i, c)
        }
    } else if c == 0x2C {
        mk(Kind::Comma, i, i + 1, Vec::new())
    } else if c == 0x2D {
        if x_number_at(s, i) {
            x_numeric(s, i)
        } else if peek(s, i, 1) == 0x2D && peek(s, i, 2) == 0x3E {
            mk(Kind::Cdc, i, i + 3, Vec::new())
        } else if x_ident_at(s, i) {
            x_ident_like(s, i)
        } else {
            x_delim(i, c)
        }
    } else if c == 0x2E {
        if x_number_at(s, i) {
            x_numeric(s, i)
        } else {
            x_delim(i, c)
        }
    } else if c == 0x3A {
        mk(Kind::Colon, i, i + 1, Vec::new())
    } else if c == 0x3B {
        mk(Kind::Semicolon, i, i + 1, Vec::new())
    } else if c == 0x3C {
        if peek(s, i, 1) == 0x21 && peek(s, i, 2) == 0x2D && peek(s, i, 3) == 0x2D {
            mk(Kind::Cdo, i, i + 4, Vec::new())
        } else {
            x_delim(i, c)
        }
    } else if c == 0x40 {
        if x_ident_at(s, i + 1) {
            let mut v: Vec<u32> = Vec::new();
            let e = x_ident_seq(s, i + 1, &mut v);
            proof {
                assert(v@ =~= ident_seq(s@, i + 1).0);
            }
            mk(Kind::AtKeyword, i, e, v)
        } else {
            x_delim(i, c)
        }
    } else if c == 0x5B {
        mk(Kind::LeftBracket, i, i + 1, Vec::new())
    } else if c == 0x5C {
        if x_escape_at(s, i) {
            x_ident_like(s, i)
        } else {
            x_delim(i, c)
        }
    } else if c == 0x5D {
        mk(Kind::RightBracket, i, i + 1, Vec::new())
    } else if c == 0x7B {
        mk(Kind::LeftBrace, i, i + 1, Vec::new())
    } else if c == 0x7D {
        mk(Kind::RightBrace, i, i + 1, Vec::new())
    } else if x_digit(c) {
        x_numeric(s, i)
    } else if x_ident_start(c) {
        x_ident_like(s, i)
    } else {
        x_delim(i, c)
    }
}

// ---------------------------------------------------------------------------
// §4 Tokenization
// ---------------------------------------------------------------------------

/// Tokenizes preprocessed code points (see `preprocess`): the tokens of
/// CSS Syntax Level 3 §4, without the final `<EOF-token>`, proven equal to
/// `spec::tokens`.
pub fn tokenize(s: &[u32]) -> (r: Vec<Token>)
    ensures
        views(r@) == tokens(s@),
{
    let mut out: Vec<Token> = Vec::new();
    let mut i: usize = 0;
    loop
        invariant
            i <= s.len(),
            views(out@) + tokens_from(s@, i as int) == tokens(s@),
        ensures
            views(out@) == tokens(s@),
        decreases s.len() - i,
    {
        let j = x_skip_comments(s, i);
        if j >= s.len() {
            proof {
                assert(views(out@) + seq![] =~= views(out@));
            }
            break;
        }
        let t = x_next_token(s, j);
        let e = t.end;
        proof {
            assert(views(out@.push(t)) =~= views(out@).push(t@));
            lemma_cons(views(out@), t@, tokens_from(s@, e as int));
        }
        out.push(t);
        i = e;
    }
    out
}

} // verus!
