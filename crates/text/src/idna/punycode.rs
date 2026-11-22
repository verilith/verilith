//! Punycode (RFC 3492), verified against a transliteration of the RFC's
//! decoding (6.2) and encoding (6.3) procedures. Integers are bounded by
//! `u32::MAX`, as in the `idna` crate: any step that would exceed it fails.
#[cfg(verus_only)]
use super::super::unicode::data::{is_scalar, scalars};
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

pub const BASE: u32 = 36;
pub const TMIN: u32 = 1;
pub const TMAX: u32 = 26;
pub const SKEW: u32 = 38;
pub const DAMP: u32 = 700;
pub const INITIAL_BIAS: u32 = 72;
pub const INITIAL_N: u32 = 0x80;

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// The value of a digit: `a`-`z` and `A`-`Z` are 0-25, `0`-`9` are 26-35.
pub open spec fn digit_val(b: u8) -> Option<int> {
    if 0x30 <= b <= 0x39 {
        Some(b - 0x30 + 26)
    } else if 0x41 <= b <= 0x5A {
        Some(b - 0x41)
    } else if 0x61 <= b <= 0x7A {
        Some(b - 0x61)
    } else {
        None
    }
}

/// The (lowercase) digit for a value below 36.
pub open spec fn digit_char(d: int) -> u8 {
    if d < 26 {
        (0x61 + d) as u8
    } else {
        (0x30 + d - 26) as u8
    }
}

/// The threshold at position `k` (3.3).
pub open spec fn threshold(k: int, bias: int) -> int {
    if k <= bias {
        TMIN as int
    } else if k >= bias + TMAX as int {
        TMAX as int
    } else {
        k - bias
    }
}

pub open spec fn adapt_loop(delta: int, k: int) -> int
    decreases delta,
{
    if delta > 455 {
        adapt_loop(delta / 35, k + 36)
    } else {
        k + (36 * delta) / (delta + 38)
    }
}

/// Bias adaptation (6.1).
pub open spec fn adapt(delta: int, numpoints: int, firsttime: bool) -> int {
    let d = if firsttime { delta / 700 } else { delta / 2 };
    adapt_loop(d + d / numpoints, 0)
}

/// Decodes one generalized variable-length integer from `x[p..]` into
/// `i`, with weight `w` at position `k` (the inner loop of 6.2). Returns
/// the new `i` and where it stopped.
pub open spec fn vli(x: Seq<u8>, p: int, i: int, w: int, k: int, bias: int) -> Option<(int, int)>
    decreases x.len() - p,
{
    if p < 0 || p >= x.len() {
        None
    } else {
        match digit_val(x[p]) {
            None => None,
            Some(d) => {
                let i2 = i + d * w;
                let t = threshold(k, bias);
                if i2 > (u32::MAX as int) {
                    None
                } else if d < t {
                    Some((i2, p + 1))
                } else if w * (BASE as int - t) > (u32::MAX as int) {
                    None
                } else {
                    vli(x, p + 1, i2, w * (BASE as int - t), k + 36, bias)
                }
            },
        }
    }
}

/// The outer loop of 6.2: from `x[p..]`, with state `n`, `i`, `bias` and
/// the output so far.
pub open spec fn dec_loop(x: Seq<u8>, p: int, n: int, i: int, bias: int, out: Seq<u32>) -> Option<Seq<u32>>
    decreases x.len() - p,
    via dec_loop_decreases
{
    if p < 0 || p >= x.len() {
        Some(out)
    } else {
        match vli(x, p, i, 1, BASE as int, bias) {
            None => None,
            Some((i2, p2)) => {
                let len1 = out.len() + 1int;
                let n2 = n + i2 / len1;
                if n2 > (u32::MAX as int) || !is_scalar(n2 as u32) {
                    None
                } else {
                    let pos = i2 % len1;
                    dec_loop(x, p2, n2, pos + 1, adapt(i2 - i, len1, i == 0), out.insert(pos, n2 as u32))
                }
            },
        }
    }
}

proof fn lemma_vli_advances(x: Seq<u8>, p: int, i: int, w: int, k: int, bias: int)
    ensures
        vli(x, p, i, w, k, bias) matches Some((_, p2)) ==> p < p2 <= x.len(),
    decreases x.len() - p,
{
    if 0 <= p < x.len() {
        lemma_vli_advances(x, p + 1, i + digit_val(x[p])->0 * w, w * (36 - threshold(k, bias)), k + 36, bias);
    }
}

#[via_fn]
proof fn dec_loop_decreases(x: Seq<u8>, p: int, n: int, i: int, bias: int, out: Seq<u32>) {
    lemma_vli_advances(x, p, i, 1, BASE as int, bias);
}

proof fn lemma_dec_loop_scalars(x: Seq<u8>, p: int, n: int, i: int, bias: int, out: Seq<u32>)
    requires
        scalars(out),
    ensures
        dec_loop(x, p, n, i, bias, out) matches Some(u) ==> scalars(u),
    decreases x.len() - p,
{
    if 0 <= p < x.len() {
        lemma_vli_advances(x, p, i, 1, BASE as int, bias);
        if let Some((i2, p2)) = vli(x, p, i, 1, BASE as int, bias) {
            let len1 = out.len() + 1int;
            let n2 = n + i2 / len1;
            if n2 <= (u32::MAX as int) && is_scalar(n2 as u32) {
                let pos = i2 % len1;
                let o2 = out.insert(pos, n2 as u32);
                assert forall|k: int| 0 <= k < o2.len() implies is_scalar(#[trigger] o2[k]) by {
                    if k < pos {
                        assert(o2[k] == out[k]);
                    } else if k > pos {
                        assert(o2[k] == out[k - 1]);
                    }
                }
                lemma_dec_loop_scalars(x, p2, n2, pos + 1, adapt(i2 - i, len1, i == 0), o2);
            }
        }
    }
}

proof fn lemma_last_delim(x: Seq<u8>, p: int)
    requires
        p <= x.len(),
    ensures
        -1 <= last_delim(x, p) < p || (p <= 0 && last_delim(x, p) == -1),
    decreases p,
{
    if p > 0 && x[p - 1] != 0x2D {
        lemma_last_delim(x, p - 1);
    }
}

pub proof fn lemma_decode_scalars(x: Seq<u8>)
    ensures
        decode(x) matches Some(u) ==> scalars(u),
{
    let d = last_delim(x, x.len() as int);
    let b = if d >= 0 { d } else { 0 };
    let start = if d > 0 { d + 1 } else { 0 };
    if !exists|j: int| 0 <= j < b && x[j] >= 0x80 {
        let w = widen(x.take(b));
        lemma_last_delim(x, x.len() as int);
        assert forall|k: int| 0 <= k < w.len() implies is_scalar(#[trigger] w[k]) by {
            assert(x.take(b)[k] == x[k]);
            assert(!(x[k] >= 0x80));
        }
        lemma_dec_loop_scalars(x, start, INITIAL_N as int, 0, INITIAL_BIAS as int, w);
    }
}

/// Index of the last `-` in `x`, or -1.
pub open spec fn last_delim(x: Seq<u8>, p: int) -> int
    decreases p,
{
    if p <= 0 {
        -1
    } else if x[p - 1] == 0x2D {
        p - 1
    } else {
        last_delim(x, p - 1)
    }
}

pub open spec fn widen(x: Seq<u8>) -> Seq<u32> {
    Seq::new(x.len(), |j: int| x[j] as u32)
}

/// Punycode decoding of `x` (6.2): the code points before the last
/// delimiter are copied (they must be ASCII), and the rest are deltas.
pub open spec fn decode(x: Seq<u8>) -> Option<Seq<u32>> {
    let d = last_delim(x, x.len() as int);
    let b = if d >= 0 { d } else { 0 };
    let start = if d > 0 { d + 1 } else { 0 };
    if exists|j: int| 0 <= j < b && x[j] >= 0x80 {
        None
    } else {
        dec_loop(x, start, INITIAL_N as int, 0, INITIAL_BIAS as int, widen(x.take(b)))
    }
}

/// Encodes `q` as a generalized variable-length integer from position `k`.
pub open spec fn vli_enc(q: int, k: int, bias: int) -> Seq<u8>
    decreases q,
    via vli_enc_decreases
{
    let t = threshold(k, bias);
    if q < t || q < 0 {
        seq![digit_char(q)]
    } else {
        seq![digit_char(t + (q - t) % (BASE as int - t))] + vli_enc((q - t) / (BASE as int - t), k + 36, bias)
    }
}

#[via_fn]
proof fn vli_enc_decreases(q: int, k: int, bias: int) {
    let t = threshold(k, bias);
    if !(q < t || q < 0) {
        assert(1 <= t <= 26);
        assert((q - t) / (BASE as int - t) <= q - t) by (nonlinear_arith)
            requires
                q - t >= 0,
                BASE - t >= 1,
        ;
    }
}

/// The smallest element of `x[j..]` that is at least `n`, if any.
pub open spec fn min_ge(x: Seq<u32>, j: int, n: int) -> Option<u32>
    decreases x.len() - j,
{
    if j < 0 || j >= x.len() {
        None
    } else {
        let rest = min_ge(x, j + 1, n);
        if x[j] >= n && (rest is None || x[j] <= rest->0) {
            Some(x[j])
        } else {
            rest
        }
    }
}

/// One pass of 6.3's inner loop over `x[j..]`, for code point `n`.
pub open spec fn enc_pass(x: Seq<u32>, j: int, n: int, delta: int, bias: int, h: int, b: int, out: Seq<u8>) -> Option<
    (int, int, int, Seq<u8>),
>
    decreases x.len() - j,
{
    if j < 0 || j >= x.len() {
        Some((delta, bias, h, out))
    } else if x[j] < n {
        if delta + 1 > (u32::MAX as int) {
            None
        } else {
            enc_pass(x, j + 1, n, delta + 1, bias, h, b, out)
        }
    } else if x[j] == n {
        if h + 1 > (u32::MAX as int) {
            None
        } else {
            enc_pass(x, j + 1, n, 0, adapt(delta, h + 1, h == b), h + 1, b, out + vli_enc(delta, BASE as int, bias))
        }
    } else {
        enc_pass(x, j + 1, n, delta, bias, h, b, out)
    }
}

/// The outer loop of 6.3.
pub open spec fn enc_loop(x: Seq<u32>, n: int, delta: int, bias: int, h: int, b: int, out: Seq<u8>) -> Option<Seq<u8>>
    decreases 0x1_0000_0000 - n,
    via enc_loop_decreases
{
    if h >= x.len() {
        Some(out)
    } else {
        match min_ge(x, 0, n) {
            None => None,
            Some(m) => {
                let d = delta + (m - n) * (h + 1);
                if d > (u32::MAX as int) || n > m {
                    None
                } else {
                    match enc_pass(x, 0, m as int, d, bias, h, b, out) {
                        None => None,
                        Some((d2, bias2, h2, out2)) => if d2 + 1 > (u32::MAX as int) {
                            None
                        } else {
                            enc_loop(x, m + 1, d2 + 1, bias2, h2, b, out2)
                        },
                    }
                }
            },
        }
    }
}

#[via_fn]
proof fn enc_loop_decreases(x: Seq<u32>, n: int, delta: int, bias: int, h: int, b: int, out: Seq<u8>) {
}

/// The basic code points of `x`, as bytes.
pub open spec fn basics(x: Seq<u32>) -> Seq<u8>
    decreases x.len(),
{
    if x.len() == 0 {
        seq![]
    } else if x.last() < 0x80 {
        basics(x.drop_last()).push(x.last() as u8)
    } else {
        basics(x.drop_last())
    }
}

/// Punycode encoding of `x` (6.3).
pub open spec fn encode(x: Seq<u32>) -> Option<Seq<u8>> {
    let bs = basics(x);
    let out = if bs.len() > 0 { bs.push(0x2D) } else { bs };
    if x.len() > (u32::MAX as int) {
        None
    } else {
        enc_loop(x, INITIAL_N as int, 0, INITIAL_BIAS as int, bs.len() as int, bs.len() as int, out)
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Implementation
// ---------------------------------------------------------------------------

proof fn lemma_vli_ge(x: Seq<u8>, p: int, i: int, w: int, k: int, bias: int)
    requires
        w >= 1,
    ensures
        vli(x, p, i, w, k, bias) matches Some((i2, _)) ==> i2 >= i,
    decreases x.len() - p,
{
    if 0 <= p < x.len() {
        if let Some(d) = digit_val(x[p]) {
            let t = threshold(k, bias);
            assert(d * w >= 0) by (nonlinear_arith)
                requires
                    d >= 0,
                    w >= 1,
            ;
            assert(w * (BASE as int - t) >= 1) by (nonlinear_arith)
                requires
                    w >= 1,
                    BASE - t >= 10,
            ;
            lemma_vli_ge(x, p + 1, i + d * w, w * (BASE as int - t), k + 36, bias);
        }
    }
}

#[inline(always)]
fn digit_val_exec(b: u8) -> (r: Option<u64>)
    ensures
        r matches Some(d) ==> digit_val(b) == Some(d as int) && d < 36,
        r is None ==> digit_val(b) is None,
{
    if 0x30 <= b && b <= 0x39 {
        Some((b - 0x30 + 26) as u64)
    } else if 0x41 <= b && b <= 0x5A {
        Some((b - 0x41) as u64)
    } else if 0x61 <= b && b <= 0x7A {
        Some((b - 0x61) as u64)
    } else {
        None
    }
}

#[inline(always)]
fn digit_char_exec(d: u64) -> (r: u8)
    requires
        d < 36,
    ensures
        r == digit_char(d as int),
{
    if d < 26 {
        (0x61 + d) as u8
    } else {
        (0x30 + d - 26) as u8
    }
}

#[inline(always)]
fn threshold_exec(k: u64, bias: u64) -> (r: u64)
    ensures
        r == threshold(k as int, bias as int),
        1 <= r <= 26,
{
    if k <= bias {
        1
    } else if k >= 26 && k - 26 >= bias {
        26
    } else {
        k - bias
    }
}

/// `adapt(delta, numpoints, firsttime)`.
fn adapt_exec(delta: u64, numpoints: u64, firsttime: bool) -> (r: u64)
    requires
        delta <= u32::MAX,
        1 <= numpoints,
    ensures
        r == adapt(delta as int, numpoints as int, firsttime),
{
    let d0 = if firsttime { delta / 700 } else { delta / 2 };
    let mut d = d0 + d0 / numpoints;
    let mut k: u64 = 0;
    let ghost dd = d;
    while d > 455
        invariant
            adapt_loop(d as int, k as int) == adapt(delta as int, numpoints as int, firsttime),
            k / 36 + d <= dd,
            k % 36 == 0,
            dd <= 2 * u32::MAX,
        decreases d,
    {
        d = d / 35;
        k = k + 36;
    }
    k + (36 * d) / (d + 38)
}

/// One generalized variable-length integer from `x[p..]`, starting at `i`.
fn vli_exec(x: &[u8], p: usize, i: u64, bias: u64) -> (r: Option<(u64, usize)>)
    requires
        i <= u32::MAX,
        p <= x@.len() < u32::MAX,
    ensures
        r matches Some((i2, p2)) ==> vli(x@, p as int, i as int, 1, 36, bias as int) == Some((i2 as int, p2 as int))
            && i <= i2 <= u32::MAX && p < p2 <= x@.len(),
        r is None ==> vli(x@, p as int, i as int, 1, 36, bias as int) is None,
{
    let n_in = x.len();
    let mut q = p;
    let mut w: u64 = 1;
    let mut k: u64 = 36;
    let mut ii: u64 = i;
    proof {
        lemma_vli_ge(x@, p as int, i as int, 1, 36, bias as int);
        lemma_vli_advances(x@, p as int, i as int, 1, 36, bias as int);
    }
    loop
        invariant
            n_in == x@.len() < u32::MAX,
            p <= q,
            vli(x@, p as int, i as int, 1, 36, bias as int) == vli(x@, q as int, ii as int, w as int, k as int, bias as int),
            vli(x@, p as int, i as int, 1, 36, bias as int) matches Some((i2, p2)) ==> i <= i2 && p < p2 <= x@.len(),
            ii <= u32::MAX,
            1 <= w <= u32::MAX,
            k <= 36 * (q - p + 1),
            q <= n_in,
        decreases n_in - q,
    {
        if q >= n_in {
            return None;
        }
        let dg = match digit_val_exec(get(x, q)) {
            Some(dg) => dg,
            None => return None,
        };
        assert(dg * w <= 35 * u32::MAX) by (nonlinear_arith)
            requires
                dg < 36,
                w <= u32::MAX,
        ;
        let i2 = ii + dg * w;
        let t = threshold_exec(k, bias);
        if i2 > u32::MAX as u64 {
            return None;
        }
        if dg < t {
            return Some((i2, q + 1));
        }
        assert(w * (36 - t) <= 35 * u32::MAX) by (nonlinear_arith)
            requires
                1 <= t,
                w <= u32::MAX,
        ;
        let w2 = w * (36 - t);
        if w2 > u32::MAX as u64 {
            return None;
        }
        assert(w2 >= 1) by (nonlinear_arith)
            requires
                w >= 1,
                t <= 26,
                w2 == w * (36 - t),
        ;
        ii = i2;
        w = w2;
        k = k + 36;
        q = q + 1;
    }
}

/// Punycode decoding. Fails (returns `false`) exactly when `decode` does,
/// and otherwise leaves the result in `out`, which must start empty.
pub fn decode_into(x: &[u8], out: &mut Vec<u32>) -> (r: bool)
    requires
        old(out)@.len() == 0,
        x@.len() < u32::MAX,
    ensures
        r == decode(x@) is Some,
        r ==> final(out)@ == decode(x@)->0,
{
    let n_in = x.len();
    // The last delimiter.
    let mut e = n_in;
    while e > 0 && get(x, e - 1) != 0x2D
        invariant
            e <= n_in == x@.len(),
            last_delim(x@, n_in as int) == last_delim(x@, e as int),
        decreases e,
    {
        e -= 1;
    }
    let ghost d = last_delim(x@, n_in as int);
    assert(d == e as int - 1);
    let b = if e > 0 { e - 1 } else { 0 };
    let start = if e > 1 { e } else { 0 };
    // The basic code points.
    let mut j = 0;
    while j < b
        invariant
            j <= b <= n_in == x@.len() < u32::MAX,
            d == e - 1,
            d == last_delim(x@, x@.len() as int),
            b == (if e > 0 { e - 1 } else { 0 }),
            out@ == widen(x@.take(j as int)),
            forall|q: int| 0 <= q < j ==> x@[q] < 0x80,
        decreases b - j,
    {
        let c = get(x, j);
        if c >= 0x80 {
            assert(x@[j as int] >= 0x80);
            assert(decode(x@) is None);
            return false;
        }
        out.push(c as u32);
        proof {
            assert(out@ =~= widen(x@.take(j + 1)));
        }
        j += 1;
    }
    assert(!exists|q: int| 0 <= q < b && x@[q] >= 0x80);
    let ghost dv = decode(x@);
    assert(dv == dec_loop(x@, start as int, INITIAL_N as int, 0, INITIAL_BIAS as int, out@));
    let mut p: usize = start;
    let mut n: u64 = INITIAL_N as u64;
    let mut i: u64 = 0;
    let mut bias: u64 = INITIAL_BIAS as u64;
    while p < n_in
        invariant
            n_in == x@.len() < u32::MAX,
            dv == decode(x@),
            dec_loop(x@, p as int, n as int, i as int, bias as int, out@) == dv,
            n <= u32::MAX,
            i <= u32::MAX,
            out@.len() <= p <= n_in,
        decreases n_in - p,
    {
        let (i2, p2) = match vli_exec(x, p, i, bias) {
            Some(r) => r,
            None => return false,
        };
        let len1 = out.len() as u64 + 1;
        let n2 = n + i2 / len1;
        if n2 > 0x10FFFF || (0xD800 <= n2 && n2 <= 0xDFFF) {
            return false;
        }
        let pos = i2 % len1;
        bias = adapt_exec(i2 - i, len1, i == 0);
        out.insert(pos as usize, n2 as u32);
        n = n2;
        i = pos + 1;
        p = p2;
    }
    true
}

proof fn lemma_basics_len(x: Seq<u32>)
    ensures
        basics(x).len() <= x.len(),
    decreases x.len(),
{
    if x.len() > 0 {
        lemma_basics_len(x.drop_last());
    }
}

/// Appends `vli_enc(q, 36, bias)`.
fn push_vli(out: &mut Vec<u8>, q0: u64, bias: u64)
    requires
        q0 <= u32::MAX,
    ensures
        final(out)@ == old(out)@ + vli_enc(q0 as int, 36, bias as int),
{
    let mut q = q0;
    let mut k: u64 = 36;
    loop
        invariant
            old(out)@ + vli_enc(q0 as int, 36, bias as int) == out@ + vli_enc(q as int, k as int, bias as int),
            q <= q0 <= u32::MAX,
            36 <= k <= 36 * (q0 - q + 1),
        decreases q,
    {
        let t = threshold_exec(k, bias);
        if q < t {
            assert(vli_enc(q as int, k as int, bias as int) == seq![digit_char(q as int)]);
            out.push(digit_char_exec(q));
            assert(out@ =~= old(out)@ + vli_enc(q0 as int, 36, bias as int));
            return;
        }
        let ghost before = out@;
        out.push(digit_char_exec(t + (q - t) % (36 - t)));
        let q2 = (q - t) / (36 - t);
        assert(q2 <= q - t) by (nonlinear_arith)
            requires
                q2 == (q - t) / (36 - t),
                q >= t,
                36 - t >= 1,
        ;
        assert(vli_enc(q as int, k as int, bias as int) == seq![digit_char(t + (q - t) % (36 - t))] + vli_enc(
            q2 as int,
            k + 36,
            bias as int,
        ));
        assert(before + vli_enc(q as int, k as int, bias as int) =~= out@ + vli_enc(q2 as int, k + 36, bias as int));
        q = q2;
        k = k + 36;
    }
}

/// `min_ge(x, 0, n)`.
fn min_ge_exec(x: &[u32], n: u64) -> (r: Option<u32>)
    ensures
        r == min_ge(x@, 0, n as int),
{
    let mut j = x.len();
    let mut cur: Option<u32> = None;
    while j > 0
        invariant
            j <= x@.len(),
            cur == min_ge(x@, j as int, n as int),
        decreases j,
    {
        j -= 1;
        let c = x[j];
        if c as u64 >= n && (cur.is_none() || c <= cur.unwrap()) {
            cur = Some(c);
        }
    }
    cur
}

/// One pass of the inner loop of 6.3 over all of `x`, for code point `m`.
fn enc_pass_exec(x: &[u32], m: u64, delta0: u64, bias0: u64, h0: u64, b: u64, out: &mut Vec<u8>) -> (r: Option<
    (u64, u64, u64),
>)
    requires
        delta0 <= u32::MAX,
        h0 <= u32::MAX,
    ensures
        r matches Some((d2, bias2, h2)) ==> enc_pass(x@, 0, m as int, delta0 as int, bias0 as int, h0 as int, b as int, old(out)@)
            == Some((d2 as int, bias2 as int, h2 as int, final(out)@)) && d2 <= u32::MAX && h2 <= u32::MAX,
        r is None ==> enc_pass(x@, 0, m as int, delta0 as int, bias0 as int, h0 as int, b as int, old(out)@) is None,
{
    let ghost target = enc_pass(x@, 0, m as int, delta0 as int, bias0 as int, h0 as int, b as int, old(out)@);
    let mut j = 0;
    let mut delta = delta0;
    let mut bias = bias0;
    let mut h = h0;
    while j < x.len()
        invariant
            j <= x@.len(),
            delta <= u32::MAX,
            h <= u32::MAX,
            target == enc_pass(x@, 0, m as int, delta0 as int, bias0 as int, h0 as int, b as int, old(out)@),
            enc_pass(x@, j as int, m as int, delta as int, bias as int, h as int, b as int, out@) == target,
        decreases x@.len() - j,
    {
        let c = x[j] as u64;
        if c < m {
            if delta + 1 > u32::MAX as u64 {
                assert(enc_pass(x@, j as int, m as int, delta as int, bias as int, h as int, b as int, out@) is None);
                return None;
            }
            delta = delta + 1;
        } else if c == m {
            if h + 1 > u32::MAX as u64 {
                assert(enc_pass(x@, j as int, m as int, delta as int, bias as int, h as int, b as int, out@) is None);
                return None;
            }
            push_vli(out, delta, bias);
            bias = adapt_exec(delta, h + 1, h == b);
            delta = 0;
            h = h + 1;
        }
        j += 1;
    }
    Some((delta, bias, h))
}

/// The basic code points of `x`, appended to `out`.
fn basics_exec(x: &[u32], out: &mut Vec<u8>)
    requires
        old(out)@.len() == 0,
    ensures
        final(out)@ == basics(x@),
{
    let mut j = 0;
    while j < x.len()
        invariant
            j <= x@.len(),
            out@ == basics(x@.take(j as int)),
        decreases x@.len() - j,
    {
        let c = x[j];
        assert(x@.take(j + 1).drop_last() =~= x@.take(j as int));
        if c < 0x80 {
            out.push(c as u8);
        }
        j += 1;
    }
    assert(x@.take(x@.len() as int) =~= x@);
}

/// Punycode encoding. Fails (returns `false`) exactly when `encode` does,
/// and otherwise leaves the result in `out`, which must start empty.
pub fn encode_into(x: &[u32], out: &mut Vec<u8>) -> (r: bool)
    requires
        old(out)@.len() == 0,
    ensures
        r == encode(x@) is Some,
        r ==> final(out)@ == encode(x@)->0,
{
    if x.len() > u32::MAX as usize {
        return false;
    }
    basics_exec(x, out);
    proof {
        lemma_basics_len(x@);
    }
    let b = out.len() as u64;
    if b > 0 {
        out.push(0x2D);
    }
    let ghost ev = encode(x@);
    let mut n: u64 = INITIAL_N as u64;
    let mut delta: u64 = 0;
    let mut bias: u64 = INITIAL_BIAS as u64;
    let mut h: u64 = b;
    let len = x.len() as u64;
    loop
        invariant
            len == x@.len() <= u32::MAX,
            ev == encode(x@),
            enc_loop(x@, n as int, delta as int, bias as int, h as int, b as int, out@) == ev,
            n <= 0x1_0000_0000,
            delta <= u32::MAX,
            h <= u32::MAX,
        decreases 0x1_0000_0000 - n,
    {
        if h >= len {
            return true;
        }
        let m = match min_ge_exec(x, n) {
            Some(m) => m as u64,
            None => return false,
        };
        if n > m {
            return false;
        }
        let mn = (m - n) as u128;
        let h1 = (h + 1) as u128;
        assert(mn * h1 <= 0x1_0000_0000 * 0x1_0000_0000) by (nonlinear_arith)
            requires
                mn <= 0x1_0000_0000,
                h1 <= 0x1_0000_0000,
        ;
        let d = delta as u128 + mn * h1;
        if d > u32::MAX as u128 {
            return false;
        }
        let (d2, bias2, h2) = match enc_pass_exec(x, m, d as u64, bias, h, b, out) {
            Some(r) => r,
            None => return false,
        };
        if d2 + 1 > u32::MAX as u64 {
            return false;
        }
        n = m + 1;
        delta = d2 + 1;
        bias = bias2;
        h = h2;
    }
}

/// `enc_pass` with `pre` in front of the output.
proof fn lemma_enc_pass_prefix(x: Seq<u32>, j: int, n: int, delta: int, bias: int, h: int, b: int, pre: Seq<u8>, out: Seq<u8>)
    ensures
        enc_pass(x, j, n, delta, bias, h, b, pre + out) == match enc_pass(x, j, n, delta, bias, h, b, out) {
            None => None,
            Some((d2, b2, h2, o2)) => Some((d2, b2, h2, pre + o2)),
        },
    decreases x.len() - j,
{
    if j < 0 || j >= x.len() {
    } else if x[j] < n {
        if delta + 1 <= (u32::MAX as int) {
            lemma_enc_pass_prefix(x, j + 1, n, delta + 1, bias, h, b, pre, out);
        }
    } else if x[j] == n {
        if h + 1 <= (u32::MAX as int) {
            let v = vli_enc(delta, BASE as int, bias);
            assert((pre + out) + v =~= pre + (out + v));
            lemma_enc_pass_prefix(x, j + 1, n, 0, adapt(delta, h + 1, h == b), h + 1, b, pre, out + v);
        }
    } else {
        lemma_enc_pass_prefix(x, j + 1, n, delta, bias, h, b, pre, out);
    }
}

/// Appends `basics(x)`.
fn basics_append(x: &[u32], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + basics(x@),
{
    let mut j = 0;
    while j < x.len()
        invariant
            j <= x@.len(),
            out@ == old(out)@ + basics(x@.take(j as int)),
        decreases x@.len() - j,
    {
        let c = x[j];
        assert(x@.take(j + 1).drop_last() =~= x@.take(j as int));
        if c < 0x80 {
            out.push(c as u8);
            assert(out@ =~= old(out)@ + basics(x@.take(j + 1)));
        }
        j += 1;
    }
    assert(x@.take(x@.len() as int) =~= x@);
}

/// [`encode_into`], appending to what `out` holds.
pub fn encode_append(x: &[u32], out: &mut Vec<u8>) -> (r: bool)
    ensures
        r == encode(x@) is Some,
        r ==> final(out)@ == old(out)@ + encode(x@)->0,
{
    let ghost pre = out@;
    if x.len() > u32::MAX as usize {
        return false;
    }
    let start = out.len();
    basics_append(x, out);
    proof {
        lemma_basics_len(x@);
    }
    let b = (out.len() - start) as u64;
    if b > 0 {
        out.push(0x2D);
    }
    let ghost mut o: Seq<u8> = out@.subrange(pre.len() as int, out@.len() as int);
    proof {
        assert(out@ =~= pre + o);
        let bs = basics(x@);
        assert(o =~= if bs.len() > 0 { bs.push(0x2D) } else { bs });
    }
    let ghost ev = encode(x@);
    let mut n: u64 = INITIAL_N as u64;
    let mut delta: u64 = 0;
    let mut bias: u64 = INITIAL_BIAS as u64;
    let mut h: u64 = b;
    let len = x.len() as u64;
    loop
        invariant
            len == x@.len() <= u32::MAX,
            ev == encode(x@),
            pre == old(out)@,
            out@ == pre + o,
            enc_loop(x@, n as int, delta as int, bias as int, h as int, b as int, o) == ev,
            n <= 0x1_0000_0000,
            delta <= u32::MAX,
            h <= u32::MAX,
        decreases 0x1_0000_0000 - n,
    {
        if h >= len {
            proof {
                assert(enc_loop(x@, n as int, delta as int, bias as int, h as int, b as int, o) == Some(o));
            }
            return true;
        }
        let m = match min_ge_exec(x, n) {
            Some(m) => m as u64,
            None => return false,
        };
        if n > m {
            return false;
        }
        let mn = (m - n) as u128;
        let h1 = (h + 1) as u128;
        assert(mn * h1 <= 0x1_0000_0000 * 0x1_0000_0000) by (nonlinear_arith)
            requires
                mn <= 0x1_0000_0000,
                h1 <= 0x1_0000_0000,
        ;
        let d = delta as u128 + mn * h1;
        if d > u32::MAX as u128 {
            return false;
        }
        proof {
            lemma_enc_pass_prefix(x@, 0, m as int, d as int, bias as int, h as int, b as int, pre, o);
        }
        let (d2, bias2, h2) = match enc_pass_exec(x, m, d as u64, bias, h, b, out) {
            Some(r) => r,
            None => return false,
        };
        let ghost o0 = o;
        proof {
            let o2 = out@.subrange(pre.len() as int, out@.len() as int);
            let e = enc_pass(x@, 0, m as int, d as int, bias as int, h as int, b as int, o0);
            assert(e is Some);
            let (ed, eb, eh, eo) = e->0;
            assert(pre + eo == out@);
            assert(eo =~= o2);
            assert(e == Some((d2 as int, bias2 as int, h2 as int, o2)));
            assert(out@ =~= pre + o2);
            o = o2;
        }
        if d2 + 1 > u32::MAX as u64 {
            return false;
        }
        n = m + 1;
        delta = d2 + 1;
        bias = bias2;
        h = h2;
    }
}

} // verus!

/// Decodes a Punycode label (without the `xn--` prefix).
pub fn decode_str(s: &str) -> Option<String> {
    let mut out = Vec::new();
    if s.len() >= u32::MAX as usize || !decode_into(s.as_bytes(), &mut out) {
        return None;
    }
    // `decode` only produces scalar values.
    Some(out.into_iter().map(|c| char::from_u32(c).unwrap()).collect())
}

/// Encodes `s` as a Punycode label (without the `xn--` prefix).
pub fn encode_str(s: &str) -> Option<String> {
    let cs: Vec<u32> = s.chars().map(|c| c as u32).collect();
    let mut out = Vec::new();
    if !encode_into(&cs, &mut out) {
        return None;
    }
    // The output is ASCII digits, letters, `-` and the basic input.
    Some(String::from_utf8(out).unwrap())
}
