//! Kernel (Lanczos) resampling of RGBA images, proven to compute exactly
//! `spec_lanczos::kresize` and `spec_lanczos::thumb` for every kernel
//! table, with no overflow or out-of-bounds access.
#[cfg(verus_only)]
use crate::resize::lemma_idx;
use crate::spec::*;
use crate::spec_lanczos::*;
use vstd::prelude::*;

verus! {

/// What the code needs of a table: at most 4 units of support, and every
/// weight at most 2.0 in size.
pub open spec fn kt_ok(kt: Seq<i32>) -> bool {
    1 <= kt.len() <= 1024 && forall|j: int| 0 <= j < kt.len() ==> -32768 <= #[trigger] kt[j] <= 32768
}

/// The table as integers, as the specification takes it.
pub open spec fn kseq(kt: Seq<i32>) -> Seq<int> {
    Seq::new(kt.len(), |j: int| kt[j] as int)
}

/// The weights `taps` lays out: entry `k` is output `k / n`'s weight for
/// its `k % n`-th source sample.
pub open spec fn wval(kt: Seq<int>, s: int, d: int, n: int, k: int) -> int {
    kw(kt, k / n, klo(kt, k / n, s, d) + k % n, s, d)
}

/// The weights of each output sample, worked out once for every row (or
/// column).
pub struct Taps {
    /// `klo` of each output sample.
    pub lo: Vec<i64>,
    /// `n` weights per output sample.
    pub w: Vec<i32>,
    /// Their sums (`kwsum`).
    pub ws: Vec<i64>,
    /// `ktaps`.
    pub n: usize,
}

impl Taps {
    pub open spec fn ok(&self, kt: Seq<int>, s: int, d: int) -> bool {
        &&& self.n == ktaps(kt, s, d)
        &&& self.lo@.len() == d
        &&& self.ws@.len() == d
        &&& self.w@.len() == d * self.n
        &&& forall|x: int| 0 <= x < d ==> #[trigger] self.lo@[x] == klo(kt, x, s, d)
        &&& forall|x: int| 0 <= x < d ==> #[trigger] self.ws@[x] == kwsum(kt, x, s, d)
        &&& forall|k: int| 0 <= k < d * self.n ==> #[trigger] self.w@[k] == wval(kt, s, d, self.n as int, k)
    }
}

// ---------------------------------------------------------------------------
// Arithmetic facts
// ---------------------------------------------------------------------------

/// Sizes: the support, the taps and where they start.
pub proof fn lemma_kbounds(kt: Seq<int>, x: int, s: int, d: int)
    requires
        1 <= kt.len() <= 1024,
        1 <= s <= MAX_DIM,
        1 <= d <= MAX_DIM,
        0 <= x < d,
    ensures
        1 <= ka(kt) <= 4,
        2 <= kd(s, d) <= 131070,
        3 <= ktaps(kt, s, d) <= 524282,
        d * ktaps(kt, s, d) <= 655350,
        -524281 <= klo(kt, x, s, d) < s,
        klo(kt, x, s, d) + ktaps(kt, s, d) <= 589817,
{
    let a = ka(kt);
    let dd = kd(s, d);
    let n = ktaps(kt, s, d);
    assert(1 <= a <= 4);
    assert(a * dd <= 524280) by (nonlinear_arith)
        requires
            1 <= a <= 4,
            dd <= 131070,
    ;
    assert(a * dd >= d) by (nonlinear_arith)
        requires
            1 <= a,
            dd >= 2 * d,
            d >= 1,
    ;
    let q = a * dd / d;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a * dd, d);
    vstd::arithmetic::div_mod::lemma_mod_bound(a * dd, d);
    assert(d * q <= a * dd);
    assert(q >= 1) by (nonlinear_arith)
        requires
            d * q + (a * dd) % d == a * dd,
            (a * dd) % d < d,
            a * dd >= d,
            d >= 1,
    ;
    assert(q <= a * dd) by (nonlinear_arith)
        requires
            d * q <= a * dd,
            d >= 1,
            q >= 1,
    ;
    assert(d * n == d * q + 2 * d) by (nonlinear_arith)
        requires
            n == q + 2,
    ;
    let num = (2 * x + 1) * s - a * dd;
    let den = 2 * d;
    assert((2 * x + 1) * s < den * s) by (nonlinear_arith)
        requires
            0 <= x < d,
            s >= 1,
            den == 2 * d,
    ;
    assert((2 * x + 1) * s >= 0) by (nonlinear_arith)
        requires
            0 <= x,
            s >= 1,
    ;
    let l = num / den;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(num, den);
    vstd::arithmetic::div_mod::lemma_mod_bound(num, den);
    assert(l < s) by (nonlinear_arith)
        requires
            den * l + num % den == num,
            0 <= num % den,
            num < den * s,
            den >= 1,
    ;
    assert(l >= -524281) by (nonlinear_arith)
        requires
            den * l + num % den == num,
            num % den < den,
            num >= -524280,
            den >= 2,
    ;
}

/// A table weight's size.
pub proof fn lemma_kw_bound(kt: Seq<i32>, x: int, i: int, s: int, d: int)
    requires
        kt_ok(kt),
        1 <= s,
        1 <= d,
    ensures
        -32768 <= kw(kseq(kt), x, i, s, d) <= 32768,
{
    let n = knum(x, i, s, d);
    let a = if n < 0 { -n } else { n };
    let dd = kd(s, d);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(a * KSTEP + dd / 2, dd);
}

/// Output `x` weighs no source sample outside its `ktaps` samples from
/// `klo`: `ksum` over them is the sum over the whole line.
pub proof fn lemma_kw_outside(kt: Seq<int>, x: int, i: int, s: int, d: int)
    requires
        1 <= kt.len(),
        1 <= s,
        1 <= d,
        i < klo(kt, x, s, d) || i >= klo(kt, x, s, d) + ktaps(kt, s, d),
    ensures
        kw(kt, x, i, s, d) == 0,
{
    let a = ka(kt);
    let dd = kd(s, d);
    let p = (2 * x + 1) * s;
    let num = p - a * dd;
    let den = 2 * d;
    let l = klo(kt, x, s, d);
    let q = a * dd / d;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(num, den);
    vstd::arithmetic::div_mod::lemma_mod_bound(num, den);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a * dd, d);
    vstd::arithmetic::div_mod::lemma_mod_bound(a * dd, d);
    assert(a * KSTEP >= kt.len());
    assert(dd >= 2);
    let n = knum(x, i, s, d);
    // |n| > a * dd: the rounded distance is at least the table's length.
    if i < l {
        assert(n <= -(a * dd) - d) by (nonlinear_arith)
            requires
                n == (2 * i + 1) * d - p,
                i <= l - 1,
                den * l + num % den == num,
                num % den >= 0,
                num == p - a * dd,
                den == 2 * d,
                d >= 1,
        ;
    } else {
        assert(n >= a * dd + d) by (nonlinear_arith)
            requires
                n == (2 * i + 1) * d - p,
                i >= l + q + 2,
                den * l + num % den == num,
                num % den < den,
                num == p - a * dd,
                den == 2 * d,
                d * q + (a * dd) % d == a * dd,
                (a * dd) % d < d,
                d >= 1,
        ;
    }
    let m = if n < 0 { -n } else { n };
    assert(m * KSTEP + dd / 2 >= (a * KSTEP) * dd) by (nonlinear_arith)
        requires
            m >= a * dd,
            dd >= 0,
    ;
    assert((m * KSTEP + dd / 2) / dd >= a * KSTEP) by {
        vstd::arithmetic::div_mod::lemma_div_is_ordered((a * KSTEP) * dd, m * KSTEP + dd / 2, dd);
        vstd::arithmetic::div_mod::lemma_div_by_multiple(a * KSTEP, dd);
    }
}

/// `ksum` of values in `[0, m]` is at most `t * 32768 * m` in size.
pub proof fn lemma_ksum_bound(v: spec_fn(int) -> int, kt: Seq<i32>, x: int, s: int, d: int, t: int, m: int)
    requires
        kt_ok(kt),
        1 <= s,
        1 <= d,
        0 <= t,
        0 <= m,
        forall|i: int| 0 <= i < s ==> 0 <= #[trigger] v(i) <= m,
    ensures
        -(t * 32768 * m) <= ksum(v, kseq(kt), x, s, d, t) <= t * 32768 * m,
    decreases t,
{
    if t > 0 {
        let i = klo(kseq(kt), x, s, d) + t - 1;
        lemma_ksum_bound(v, kt, x, s, d, t - 1, m);
        lemma_kw_bound(kt, x, i, s, d);
        let w = kw(kseq(kt), x, i, s, d);
        let vi = v(kc(i, s));
        assert(0 <= vi <= m);
        assert(-(32768 * m) <= w * vi <= 32768 * m) by (nonlinear_arith)
            requires
                -32768 <= w <= 32768,
                0 <= vi <= m,
        ;
        assert(t * 32768 * m == (t - 1) * 32768 * m + 32768 * m) by (nonlinear_arith);
    }
}

// ---------------------------------------------------------------------------
// Scalar code
// ---------------------------------------------------------------------------

/// `num / q`, rounded down (Verus's `/` on `int`).
pub fn floor_div(num: i64, q: i64) -> (r: i64)
    requires
        1 <= q <= 0x10_0000,
        -0x100_0000_0000 <= num <= 0x100_0000_0000,
    ensures
        r == num as int / q as int,
{
    let big: i64 = 0x100_0000_0000;
    proof {
        assert(q * big <= 0x10_0000 * 0x100_0000_0000) by (nonlinear_arith)
            requires
                1 <= q <= 0x10_0000,
                big == 0x100_0000_0000,
        ;
        assert(q * big >= big) by (nonlinear_arith)
            requires
                1 <= q,
                big >= 0,
        ;
    }
    let u = num + q * big;
    let k = u / q;
    let r0 = u % q;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u as int, q as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(u as int, q as int);
        assert(num == q * (k - big) + r0) by (nonlinear_arith)
            requires
                u == q * k + r0,
                u == num + q * big,
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(num as int, q as int, k - big, r0 as int);
        assert(k <= u);
        assert(k >= 0);
    }
    k - big
}

/// `kw`, for a source sample within 2^20 of the line.
fn kw_x(kt: &[i32], x: usize, i: i64, s: usize, d: usize) -> (r: i32)
    requires
        kt_ok(kt@),
        1 <= s <= MAX_DIM,
        1 <= d <= MAX_DIM,
        x < d,
        -0x10_0000 <= i <= 0x10_0000,
    ensures
        r as int == kw(kseq(kt@), x as int, i as int, s as int, d as int),
        -32768 <= r <= 32768,
{
    let dd: i64 = 2 * if s > d { s as i64 } else { d as i64 };
    proof {
        assert((2 * i + 1) * d <= 0x20_0001 * 65535 && (2 * i + 1) * d >= -0x20_0001 * 65535) by (nonlinear_arith)
            requires
                -0x10_0000 <= i <= 0x10_0000,
                1 <= d <= 65535,
        ;
        assert((2 * x + 1) * s <= 131071 * 65535) by (nonlinear_arith)
            requires
                x < 65535,
                s <= 65535,
        ;
        assert((2 * x + 1) * s >= 0) by (nonlinear_arith)
            requires
                x >= 0,
                s >= 0,
        ;
    }
    let n: i64 = (2 * i + 1) * (d as i64) - (2 * (x as i64) + 1) * (s as i64);
    let a: i64 = if n < 0 { -n } else { n };
    let j: i64 = (a * 256 + dd / 2) / dd;
    proof {
        lemma_kw_bound(kt@, x as int, i as int, s as int, d as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos((a * 256 + dd / 2) as int, dd as int);
    }
    if j < kt.len() as i64 {
        kt[j as usize]
    } else {
        0
    }
}

/// `kdiv` for the sizes the passes reach.
fn kdiv_x(n: i64, w: i64, scale: i64) -> (r: i64)
    requires
        -0x8_0000_0000_0000 <= n <= 0x8_0000_0000_0000,
        -0x8_0000_0000_0000 <= w <= 0x8_0000_0000_0000,
        1 <= scale <= 256,
    ensures
        r == kdiv(n as int, w as int, scale as int),
        0 <= r <= 255 * scale,
{
    if w <= 0 {
        0
    } else if n <= 0 {
        proof {
            let num = 2 * scale * n + w;
            let q = num / (2 * w);
            assert(2 * scale * n <= 0) by (nonlinear_arith)
                requires
                    n <= 0,
                    scale >= 1,
            ;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(num, 2 * w);
            vstd::arithmetic::div_mod::lemma_mod_bound(num, 2 * w);
            assert(q <= 0) by (nonlinear_arith)
                requires
                    (2 * w) * q + num % (2 * w) == num,
                    num % (2 * w) >= 0,
                    num < 2 * w,
                    w >= 1,
            ;
        }
        0
    } else {
        proof {
            assert(2 * scale * n <= 2 * 256 * 0x8_0000_0000_0000) by (nonlinear_arith)
                requires
                    1 <= scale <= 256,
                    1 <= n <= 0x8_0000_0000_0000,
            ;
            assert(2 * scale * n >= 0) by (nonlinear_arith)
                requires
                    1 <= scale,
                    1 <= n,
            ;
        }
        let q = (2 * scale * n + w) / (2 * w);
        if q > 255 * scale {
            255 * scale
        } else {
            q
        }
    }
}

/// `klo`.
fn klo_x(kt: &[i32], x: usize, s: usize, d: usize) -> (r: i64)
    requires
        1 <= kt@.len() <= 1024,
        1 <= s <= MAX_DIM,
        1 <= d <= MAX_DIM,
        x < d,
    ensures
        r == klo(kseq(kt@), x as int, s as int, d as int),
{
    proof {
        lemma_kbounds(kseq(kt@), x as int, s as int, d as int);
        assert((2 * x + 1) * s <= 131071 * 65535) by (nonlinear_arith)
            requires
                x < 65535,
                s <= 65535,
        ;
        assert((2 * x + 1) * s >= 0) by (nonlinear_arith)
            requires
                x >= 0,
                s >= 0,
        ;
    }
    let a = ((kt.len() + 255) / 256) as i64;
    assert(a == ka(kseq(kt@)));
    let dd: i64 = 2 * if s > d { s as i64 } else { d as i64 };
    proof {
        assert(1 <= a <= 4 && 2 <= dd <= 131070);
        assert(0 <= a * dd <= 524280) by (nonlinear_arith)
            requires
                1 <= a <= 4,
                2 <= dd <= 131070,
        ;
    }
    floor_div((2 * (x as i64) + 1) * (s as i64) - a * dd, 2 * (d as i64))
}

/// The weights for resampling `s` samples to `d`.
pub fn taps(kt: &[i32], s: usize, d: usize) -> (r: Taps)
    requires
        kt_ok(kt@),
        1 <= s <= MAX_DIM,
        1 <= d <= MAX_DIM,
    ensures
        r.ok(kseq(kt@), s as int, d as int),
{
    let ghost k = kseq(kt@);
    proof {
        lemma_kbounds(k, 0, s as int, d as int);
    }
    let a = (kt.len() + 255) / 256;
    assert(a == ka(k));
    let dd = 2 * if s > d { s } else { d };
    proof {
        assert(1 <= a <= 4 && 2 <= dd <= 131070);
        assert(a * dd <= 524280) by (nonlinear_arith)
            requires
                1 <= a <= 4,
                2 <= dd <= 131070,
        ;
    }
    let n = a * dd / d + 2;
    assert(n == ktaps(k, s as int, d as int));
    let mut lo: Vec<i64> = Vec::with_capacity(d);
    let mut ws: Vec<i64> = Vec::with_capacity(d);
    let mut w: Vec<i32> = Vec::with_capacity(d * n);
    let mut x: usize = 0;
    while x < d
        invariant
            kt_ok(kt@),
            k == kseq(kt@),
            1 <= s <= MAX_DIM,
            1 <= d <= MAX_DIM,
            n == ktaps(k, s as int, d as int),
            3 <= n <= 524282,
            d * n <= 655350,
            x <= d,
            lo@.len() == x,
            ws@.len() == x,
            w@.len() == x * n,
            forall|x2: int| 0 <= x2 < x ==> #[trigger] lo@[x2] == klo(k, x2, s as int, d as int),
            forall|x2: int| 0 <= x2 < x ==> #[trigger] ws@[x2] == kwsum(k, x2, s as int, d as int),
            forall|j: int| 0 <= j < w@.len() ==> #[trigger] w@[j] == wval(k, s as int, d as int, n as int, j),
        decreases d - x,
    {
        proof {
            lemma_kbounds(k, x as int, s as int, d as int);
            assert(x * n + n <= d * n) by (nonlinear_arith)
                requires
                    x < d,
                    n >= 0,
            ;
        }
        let l = klo_x(kt, x, s, d);
        let mut sum: i64 = 0;
        let mut t: usize = 0;
        while t < n
            invariant
                kt_ok(kt@),
                k == kseq(kt@),
                1 <= s <= MAX_DIM,
                1 <= d <= MAX_DIM,
                n == ktaps(k, s as int, d as int),
                3 <= n <= 524282,
                x < d,
                x * n + n <= d * n,
                d * n <= 655350,
                l == klo(k, x as int, s as int, d as int),
                -524281 <= l,
                l + n <= 589817,
                t <= n,
                w@.len() == x * n + t,
                sum == ksum(kunit(), k, x as int, s as int, d as int, t as int),
                -(t * 32768) <= sum <= t * 32768,
                forall|j: int| 0 <= j < w@.len() ==> #[trigger] w@[j] == wval(k, s as int, d as int, n as int, j),
            decreases n - t,
        {
            let wt = kw_x(kt, x, l + t as i64, s, d);
            let ghost before = w@;
            w.push(wt);
            proof {
                let j = x * n + t;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, n as int, x as int, t as int);
                assert forall|j2: int| 0 <= j2 < w@.len() implies #[trigger] w@[j2] == wval(
                    k,
                    s as int,
                    d as int,
                    n as int,
                    j2,
                ) by {
                    if j2 < before.len() {
                        assert(w@[j2] == before[j2]);
                    }
                }
                assert(kunit()(kc(l + t, s as int)) == 1);
            }
            sum = sum + wt as i64;
            t = t + 1;
        }
        lo.push(l);
        ws.push(sum);
        proof {
            assert(x * n + n == (x + 1) * n) by (nonlinear_arith);
        }
        x = x + 1;
    }
    Taps { lo, w, ws, n }
}

// ---------------------------------------------------------------------------
// The passes
// ---------------------------------------------------------------------------

/// The row pass's value at index `k` of its output.
pub open spec fn khval(kt: Seq<int>, src: Seq<u8>, sw: int, dw: int, k: int) -> int {
    khpx(kt, src, sw, dw, (k / NC) / dw, (k / NC) % dw, k % NC)
}

/// Source sample `i` of a line `s` long, edges repeated.
#[inline(always)]
fn kc_x(i: i64, s: usize) -> (r: usize)
    requires
        1 <= s <= MAX_DIM,
    ensures
        r == kc(i as int, s as int),
        r < s,
{
    if i < 0 {
        0
    } else if i >= s as i64 {
        s - 1
    } else {
        i as usize
    }
}

/// The row pass: `dw * sh * 4` values, `khpx` of each pixel and channel,
/// row by row.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn krows(kt: &[i32], src: &[u8], sw: usize, sh: usize, dw: usize, tp: &Taps) -> (r: Vec<u16>)
    requires
        kt_ok(kt@),
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        1 <= dw <= MAX_DIM,
        src@.len() == sw * sh * NC,
        dw * sh * NC <= usize::MAX,
        sw * sh * NC <= 65535 * 65535 * 4,
        tp.ok(kseq(kt@), sw as int, dw as int),
    ensures
        r@.len() == dw * sh * NC,
        forall|y: int, x: int, c: int|
            0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] r@[(y * dw + x) * NC + c] == khpx(
                kseq(kt@),
                src@,
                sw as int,
                dw as int,
                y,
                x,
                c,
            ),
{
    let ghost s = src@;
    let ghost k = kseq(kt@);
    let n = tp.n;
    proof {
        lemma_kbounds(k, 0, sw as int, dw as int);
    }
    let mut out: Vec<u16> = Vec::with_capacity(dw * sh * 4);
    let mut y: usize = 0;
    while y < sh
        invariant
            kt_ok(kt@),
            k == kseq(kt@),
            1 <= sw <= MAX_DIM,
            1 <= sh <= MAX_DIM,
            1 <= dw <= MAX_DIM,
            s == src@,
            src@.len() == sw * sh * NC,
            dw * sh * NC <= usize::MAX,
            sw * sh * NC <= 65535 * 65535 * 4,
            tp.ok(k, sw as int, dw as int),
            n == tp.n,
            3 <= n <= 524282,
            dw * n <= 655350,
            y <= sh,
            out@.len() == y * dw * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == khval(k, s, sw as int, dw as int, j),
        decreases sh - y,
    {
        let mut x: usize = 0;
        while x < dw
            invariant
                kt_ok(kt@),
                k == kseq(kt@),
                1 <= sw <= MAX_DIM,
                1 <= sh <= MAX_DIM,
                1 <= dw <= MAX_DIM,
                s == src@,
                src@.len() == sw * sh * NC,
                dw * sh * NC <= usize::MAX,
                sw * sh * NC <= 65535 * 65535 * 4,
                tp.ok(k, sw as int, dw as int),
                n == tp.n,
                3 <= n <= 524282,
                dw * n <= 655350,
                y < sh,
                x <= dw,
                out@.len() == (y * dw + x) * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == khval(k, s, sw as int, dw as int, j),
            decreases dw - x,
        {
            proof {
                lemma_kbounds(k, x as int, sw as int, dw as int);
                assert(x * n + n <= dw * n) by (nonlinear_arith)
                    requires
                        x < dw,
                        n >= 0,
                ;
            }
            let l = tp.lo[x];
            let base = x * n;
            let mut a0: i64 = 0;
            let mut a1: i64 = 0;
            let mut a2: i64 = 0;
            let mut a3: i64 = 0;
            let mut t: usize = 0;
            while t < n
                invariant
                    kt_ok(kt@),
                    k == kseq(kt@),
                    1 <= sw <= MAX_DIM,
                    1 <= sh <= MAX_DIM,
                    1 <= dw <= MAX_DIM,
                    s == src@,
                    src@.len() == sw * sh * NC,
                    tp.ok(k, sw as int, dw as int),
                    n == tp.n,
                    3 <= n <= 524282,
                    y < sh,
                    x < dw,
                    base == x * n,
                    x * n + n <= dw * n,
                    dw * n <= 655350,
                    sw * sh * NC <= 65535 * 65535 * 4,
                    l == klo(k, x as int, sw as int, dw as int),
                    -524281 <= l,
                    l + n <= 589817,
                    t <= n,
                    a0 == ksum(src_line(s, sw as int, y as int, 0), k, x as int, sw as int, dw as int, t as int),
                    a1 == ksum(src_line(s, sw as int, y as int, 1), k, x as int, sw as int, dw as int, t as int),
                    a2 == ksum(src_line(s, sw as int, y as int, 2), k, x as int, sw as int, dw as int, t as int),
                    a3 == ksum(src_line(s, sw as int, y as int, 3), k, x as int, sw as int, dw as int, t as int),
                    -(t * 8355840) <= a0 <= t * 8355840,
                    -(t * 8355840) <= a1 <= t * 8355840,
                    -(t * 8355840) <= a2 <= t * 8355840,
                    -(t * 8355840) <= a3 <= t * 8355840,
                decreases n - t,
            {
                let i = l + t as i64;
                let ci = kc_x(i, sw);
                let wt = tp.w[base + t] as i64;
                proof {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        (x * n + t) as int,
                        n as int,
                        x as int,
                        t as int,
                    );
                    assert(tp.w@[base + t] == wval(k, sw as int, dw as int, n as int, (x * n + t) as int));
                    lemma_kw_bound(kt@, x as int, i as int, sw as int, dw as int);
                    lemma_idx(y as int, ci as int, 3, sw as int, sh as int);
                    lemma_idx(y as int, ci as int, 0, sw as int, sh as int);
                }
                let p = (y * sw + ci) * 4;
                let v0 = src[p] as i64;
                let v1 = src[p + 1] as i64;
                let v2 = src[p + 2] as i64;
                let v3 = src[p + 3] as i64;
                proof {
                    assert(-8355840 <= wt * v0 <= 8355840 && -8355840 <= wt * v1 <= 8355840 && -8355840 <= wt * v2
                        <= 8355840 && -8355840 <= wt * v3 <= 8355840) by (nonlinear_arith)
                        requires
                            -32768 <= wt <= 32768,
                            0 <= v0 <= 255,
                            0 <= v1 <= 255,
                            0 <= v2 <= 255,
                            0 <= v3 <= 255,
                    ;
                    assert((t + 1) * 8355840 == t * 8355840 + 8355840) by (nonlinear_arith);
                    assert(src_line(s, sw as int, y as int, 0)(ci as int) == v0);
                    assert(src_line(s, sw as int, y as int, 1)(ci as int) == v1);
                    assert(src_line(s, sw as int, y as int, 2)(ci as int) == v2);
                    assert(src_line(s, sw as int, y as int, 3)(ci as int) == v3);
                }
                a0 = a0 + wt * v0;
                a1 = a1 + wt * v1;
                a2 = a2 + wt * v2;
                a3 = a3 + wt * v3;
                t = t + 1;
            }
            let wsum = tp.ws[x];
            proof {
                lemma_ksum_bound(kunit(), kt@, x as int, sw as int, dw as int, n as int, 1);
                assert(n * 32768 * 1 <= 524282 * 32768);
                assert(t * 8355840 <= 524282 * 8355840) by (nonlinear_arith)
                    requires
                        t <= 524282,
                ;
                lemma_idx(y as int, x as int, 3, dw as int, sh as int);
            }
            let q0 = kdiv_x(a0, wsum, 256) as u16;
            let q1 = kdiv_x(a1, wsum, 256) as u16;
            let q2 = kdiv_x(a2, wsum, 256) as u16;
            let q3 = kdiv_x(a3, wsum, 256) as u16;
            let ghost before = out@;
            out.push(q0);
            out.push(q1);
            out.push(q2);
            out.push(q3);
            proof {
                assert((y * dw + x + 1) * NC == (y * dw + x) * NC + 4) by (nonlinear_arith);
                assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == khval(
                    k,
                    s,
                    sw as int,
                    dw as int,
                    j,
                ) by {
                    if j >= before.len() {
                        let b = (y * dw + x) * NC;
                        lemma_idx(y as int, x as int, j - b, dw as int, sh as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            x = x + 1;
        }
        proof {
            assert((y * dw + dw) * NC == (y + 1) * dw * NC) by (nonlinear_arith);
        }
        y = y + 1;
    }
    proof {
        assert(out@.len() == dw * sh * NC) by (nonlinear_arith)
            requires
                out@.len() == sh * dw * NC,
        ;
        assert forall|y: int, x: int, c: int|
            0 <= y < sh && 0 <= x < dw && 0 <= c < NC implies #[trigger] out@[(y * dw + x) * NC + c] == khpx(
                k,
                src@,
                sw as int,
                dw as int,
                y,
                x,
                c,
            ) by {
            lemma_idx(y, x, c, dw as int, sh as int);
        }
    }
    out
}

/// The column pass's value at index `k` of its output.
pub open spec fn koval(kt: Seq<int>, src: Seq<u8>, sw: int, sh: int, dw: int, dh: int, k: int) -> u8 {
    kopx(kt, src, sw, sh, dw, dh, (k / NC) / dw, (k / NC) % dw, k % NC)
}

/// Column `x`, channel `c` of the row pass, for entry `j` of a row of it.
pub open spec fn kline(kt: Seq<int>, src: Seq<u8>, sw: int, dw: int, j: int) -> spec_fn(int) -> int {
    kmid_line(kt, src, sw, dw, j / NC, j % NC)
}

/// The column pass, over the row pass's values `mid`: the resampled image.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn kcols(
    kt: &[i32],
    mid: &[u16],
    sw: usize,
    sh: usize,
    dw: usize,
    dh: usize,
    tp: &Taps,
    Ghost(src): Ghost<Seq<u8>>,
) -> (r: Vec<u8>)
    requires
        kt_ok(kt@),
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        1 <= dw <= MAX_DIM,
        1 <= dh <= MAX_DIM,
        mid@.len() == dw * sh * NC,
        dw * sh * NC <= usize::MAX,
        dw * dh * NC <= usize::MAX,
        tp.ok(kseq(kt@), sh as int, dh as int),
        forall|y: int, x: int, c: int|
            0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] mid@[(y * dw + x) * NC + c] == khpx(
                kseq(kt@),
                src,
                sw as int,
                dw as int,
                y,
                x,
                c,
            ),
    ensures
        r@ == kresize(kseq(kt@), src, sw as int, sh as int, dw as int, dh as int),
{
    let ghost k = kseq(kt@);
    let n = tp.n;
    let row = dw * 4;
    proof {
        lemma_kbounds(k, 0, sh as int, dh as int);
        // Every entry of mid is a row-pass value, at most 255 * 256.
        assert forall|j: int, i: int| 0 <= j < row && 0 <= i < sh implies 0 <= #[trigger] kline(
            k,
            src,
            sw as int,
            dw as int,
            j,
        )(i) <= 65280 by {
            let x = j / NC;
            let c = j % NC;
            assert(khpx(k, src, sw as int, dw as int, i, x, c) == kdiv(
                ksum(src_line(src, sw as int, i, c), k, x, sw as int, dw as int, ktaps(k, sw as int, dw as int)),
                kwsum(k, x, sw as int, dw as int),
                256,
            ));
        }
    }
    let mut out: Vec<u8> = Vec::with_capacity(dw * dh * 4);
    let mut y: usize = 0;
    while y < dh
        invariant
            kt_ok(kt@),
            k == kseq(kt@),
            1 <= sw <= MAX_DIM,
            1 <= sh <= MAX_DIM,
            1 <= dw <= MAX_DIM,
            1 <= dh <= MAX_DIM,
            row == dw * NC,
            mid@.len() == dw * sh * NC,
            dw * sh * NC <= usize::MAX,
            dw * dh * NC <= usize::MAX,
            tp.ok(k, sh as int, dh as int),
            n == tp.n,
            3 <= n <= 524282,
            dh * n <= 655350,
            forall|y: int, x: int, c: int|
                0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] mid@[(y * dw + x) * NC + c] == khpx(
                    k,
                    src,
                    sw as int,
                    dw as int,
                    y,
                    x,
                    c,
                ),
            forall|j: int, i: int|
                0 <= j < row && 0 <= i < sh ==> 0 <= #[trigger] kline(k, src, sw as int, dw as int, j)(i) <= 65280,
            y <= dh,
            out@.len() == y * row,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == koval(
                k,
                src,
                sw as int,
                sh as int,
                dw as int,
                dh as int,
                j,
            ),
        decreases dh - y,
    {
        proof {
            lemma_kbounds(k, y as int, sh as int, dh as int);
            assert(y * n + n <= dh * n) by (nonlinear_arith)
                requires
                    y < dh,
                    n >= 0,
            ;
        }
        let l = tp.lo[y];
        let base = y * n;
        let mut acc: Vec<i64> = Vec::with_capacity(row);
        let mut j: usize = 0;
        while j < row
            invariant
                acc@.len() == j,
                j <= row,
                forall|j2: int| 0 <= j2 < j ==> #[trigger] acc@[j2] == 0,
            decreases row - j,
        {
            acc.push(0);
            j = j + 1;
        }
        let mut t: usize = 0;
        while t < n
            invariant
                kt_ok(kt@),
                k == kseq(kt@),
                1 <= sw <= MAX_DIM,
                1 <= sh <= MAX_DIM,
                1 <= dw <= MAX_DIM,
                1 <= dh <= MAX_DIM,
                row == dw * NC,
                mid@.len() == dw * sh * NC,
                dw * sh * NC <= usize::MAX,
                tp.ok(k, sh as int, dh as int),
                n == tp.n,
                3 <= n <= 524282,
                y < dh,
                base == y * n,
                y * n + n <= dh * n,
                dh * n <= 655350,
                l == klo(k, y as int, sh as int, dh as int),
                -524281 <= l,
                l + n <= 589817,
                forall|y: int, x: int, c: int|
                    0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] mid@[(y * dw + x) * NC + c] == khpx(
                        k,
                        src,
                        sw as int,
                        dw as int,
                        y,
                        x,
                        c,
                    ),
                forall|j: int, i: int|
                    0 <= j < row && 0 <= i < sh ==> 0 <= #[trigger] kline(k, src, sw as int, dw as int, j)(i)
                        <= 65280,
                t <= n,
                acc@.len() == row,
                forall|j: int|
                    0 <= j < row ==> #[trigger] acc@[j] == ksum(
                        kline(k, src, sw as int, dw as int, j),
                        k,
                        y as int,
                        sh as int,
                        dh as int,
                        t as int,
                    ),
                forall|j: int| 0 <= j < row ==> -(t * 2139095040) <= #[trigger] acc@[j] <= t * 2139095040,
            decreases n - t,
        {
            let i = l + t as i64;
            let ci = kc_x(i, sh);
            let wt = tp.w[base + t] as i64;
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                    (y * n + t) as int,
                    n as int,
                    y as int,
                    t as int,
                );
                assert(tp.w@[base + t] == wval(k, sh as int, dh as int, n as int, (y * n + t) as int));
                lemma_kw_bound(kt@, y as int, i as int, sh as int, dh as int);
                assert(ci * row + row <= sh * row) by (nonlinear_arith)
                    requires
                        ci < sh,
                        row >= 0,
                ;
                assert(sh * row == dw * sh * NC) by (nonlinear_arith)
                    requires
                        row == dw * NC,
                ;
                assert((t + 1) * 2139095040 == t * 2139095040 + 2139095040) by (nonlinear_arith);
            }
            let rb = ci * row;
            let ghost prev = acc@;
            let mut j: usize = 0;
            while j < row
                invariant
                    row == dw * NC,
                    1 <= dw <= MAX_DIM,
                    1 <= sh <= MAX_DIM,
                    mid@.len() == dw * sh * NC,
                    rb == ci * row,
                    rb + row <= mid@.len(),
                    dw * sh * NC <= usize::MAX,
                    ci < sh,
                    -32768 <= wt <= 32768,
                    t < n,
                    acc@.len() == row,
                    prev.len() == row,
                    j <= row,
                    forall|j2: int| j <= j2 < row ==> #[trigger] acc@[j2] == prev[j2],
                    forall|j2: int|
                        0 <= j2 < j ==> #[trigger] acc@[j2] == prev[j2] + wt * mid@[rb + j2] as int,
                    forall|j2: int| 0 <= j2 < row ==> -(t * 2139095040) <= #[trigger] prev[j2] <= t * 2139095040,
                    t * 2139095040 <= 524282 * 2139095040,
                decreases row - j,
            {
                let v = mid[rb + j] as i64;
                proof {
                    assert(-2147483648 <= wt * v <= 2147483648) by (nonlinear_arith)
                        requires
                            -32768 <= wt <= 32768,
                            0 <= v <= 65535,
                    ;
                }
                let nv = acc[j] + wt * v;
                acc.set(j, nv);
                j = j + 1;
            }
            proof {
                assert forall|j: int| 0 <= j < row implies #[trigger] acc@[j] == ksum(
                    kline(k, src, sw as int, dw as int, j),
                    k,
                    y as int,
                    sh as int,
                    dh as int,
                    (t + 1) as int,
                ) && -((t + 1) * 2139095040) <= acc@[j] <= (t + 1) * 2139095040 by {
                    let x = j / NC;
                    let c = j % NC;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, NC);
                    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, NC);
                    assert(x < dw) by (nonlinear_arith)
                        requires
                            j < row,
                            row == dw * NC,
                            j == NC * x + c,
                            0 <= c,
                    ;
                    assert(rb + j == (ci * dw + x) * NC + c) by (nonlinear_arith)
                        requires
                            rb == ci * row,
                            row == dw * NC,
                            j == NC * x + c,
                    ;
                    let mv = mid@[(ci * dw + x) * NC + c];
                    assert(mv == khpx(k, src, sw as int, dw as int, ci as int, x, c));
                    assert(kline(k, src, sw as int, dw as int, j)(kc(i as int, sh as int)) == mv);
                    assert(0 <= mv <= 65280);
                    assert(-2139095040 <= wt * mv <= 2139095040) by (nonlinear_arith)
                        requires
                            -32768 <= wt <= 32768,
                            0 <= mv <= 65280,
                    ;
                }
            }
            t = t + 1;
        }
        proof {
            lemma_ksum_bound(kunit(), kt@, y as int, sh as int, dh as int, n as int, 1);
            assert(t * 2139095040 <= 524282 * 2139095040) by (nonlinear_arith)
                requires
                    t <= 524282,
            ;
        }
        let w256 = 256 * tp.ws[y];
        let ghost before = out@;
        let mut j: usize = 0;
        while j < row
            invariant
                kt_ok(kt@),
                k == kseq(kt@),
                1 <= sw <= MAX_DIM,
                1 <= sh <= MAX_DIM,
                1 <= dw <= MAX_DIM,
                1 <= dh <= MAX_DIM,
                row == dw * NC,
                dw * dh * NC <= usize::MAX,
                y < dh,
                n == ktaps(k, sh as int, dh as int),
                w256 == 256 * kwsum(k, y as int, sh as int, dh as int),
                -0x8_0000_0000_0000 <= w256 <= 0x8_0000_0000_0000,
                acc@.len() == row,
                forall|j: int|
                    0 <= j < row ==> #[trigger] acc@[j] == ksum(
                        kline(k, src, sw as int, dw as int, j),
                        k,
                        y as int,
                        sh as int,
                        dh as int,
                        n as int,
                    ),
                forall|j: int| 0 <= j < row ==> -(524282 * 2139095040) <= #[trigger] acc@[j] <= 524282 * 2139095040,
                before.len() == y * row,
                j <= row,
                out@.len() == y * row + j,
                forall|j2: int| 0 <= j2 < before.len() ==> #[trigger] out@[j2] == before[j2],
                forall|j2: int| 0 <= j2 < before.len() ==> #[trigger] before[j2] == koval(
                    k,
                    src,
                    sw as int,
                    sh as int,
                    dw as int,
                    dh as int,
                    j2,
                ),
                forall|j2: int|
                    0 <= j2 < j ==> #[trigger] out@[y * row + j2] == kdiv(acc@[j2] as int, w256 as int, 1),
            decreases row - j,
        {
            let q = kdiv_x(acc[j], w256, 1) as u8;
            out.push(q);
            j = j + 1;
        }
        proof {
            assert forall|j2: int| 0 <= j2 < out@.len() implies #[trigger] out@[j2] == koval(
                k,
                src,
                sw as int,
                sh as int,
                dw as int,
                dh as int,
                j2,
            ) by {
                if j2 >= before.len() {
                    let jj = j2 - y * row;
                    let x = jj / NC;
                    let c = jj % NC;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(jj, NC);
                    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(jj, NC);
                    assert(x < dw) by (nonlinear_arith)
                        requires
                            jj < row,
                            row == dw * NC,
                            jj == NC * x + c,
                            0 <= c,
                    ;
                    assert(j2 == (y * dw + x) * NC + c) by (nonlinear_arith)
                        requires
                            j2 == y * row + jj,
                            row == dw * NC,
                            jj == NC * x + c,
                    ;
                    lemma_idx(y as int, x, c, dw as int, dh as int);
                    assert(out@[y * row + jj] == kdiv(acc@[jj] as int, w256 as int, 1));
                }
            }
            assert(y * row + row == (y + 1) * row) by (nonlinear_arith);
        }
        y = y + 1;
    }
    proof {
        let want = kresize(k, src, sw as int, sh as int, dw as int, dh as int);
        assert(out@.len() == dw * dh * NC) by (nonlinear_arith)
            requires
                out@.len() == dh * row,
                row == dw * NC,
        ;
        assert forall|j: int| 0 <= j < out@.len() implies out@[j] == #[trigger] want[j] by {
            assert(out@[j] == koval(k, src, sw as int, sh as int, dw as int, dh as int, j));
        }
        assert(out@ =~= want);
    }
    out
}

/// `src` (`sw` by `sh` RGBA pixels) resampled with the kernel `kt` to `dw`
/// by `dh`: exactly `spec_lanczos::kresize`.
pub fn kresize_rgba(kt: &[i32], src: &[u8], sw: usize, sh: usize, dw: usize, dh: usize) -> (r: Vec<u8>)
    requires
        kt_ok(kt@),
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        1 <= dw <= MAX_DIM,
        1 <= dh <= MAX_DIM,
        src@.len() == sw * sh * NC,
    ensures
        r@ == kresize(kseq(kt@), src@, sw as int, sh as int, dw as int, dh as int),
{
    proof {
        assert(dw * sh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                dw <= 65535,
                sh <= 65535,
        ;
        assert(dw * dh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                dw <= 65535,
                dh <= 65535,
        ;
    }
    proof {
        assert(sw * sh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                sw <= 65535,
                sh <= 65535,
        ;
    }
    let tx = taps(kt, sw, dw);
    let ty = taps(kt, sh, dh);
    let mid = krows(kt, src, sw, sh, dw, &tx);
    kcols(kt, &mid, sw, sh, dw, dh, &ty, Ghost(src@))
}

/// `kpre`.
fn kpre_x(s: usize, d: usize) -> (r: usize)
    requires
        1 <= s <= MAX_DIM,
        1 <= d <= MAX_DIM,
    ensures
        r == kpre(s as int, d as int),
        1 <= r <= s,
{
    let k = if s >= 4 * d { s / (2 * d) } else { 1 };
    proof {
        let si = s as int;
        let di = d as int;
        let ki = k as int;
        if s >= 4 * d {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(4 * di, si, 2 * di);
            vstd::arithmetic::div_mod::lemma_div_by_multiple(2, 2 * di);
            assert(4 * di == 2 * (2 * di));
            assert(ki >= 2);
        }
        assert(ki >= 1);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(ki, si + ki - 1, ki);
        vstd::arithmetic::div_mod::lemma_div_by_multiple(1, ki);
        assert(si + ki - 1 <= si * ki) by (nonlinear_arith)
            requires
                si >= 1,
                ki >= 1,
        ;
        vstd::arithmetic::div_mod::lemma_div_is_ordered(si + ki - 1, si * ki, ki);
        vstd::arithmetic::div_mod::lemma_div_by_multiple(si, ki);
        assert(si * ki == ki * si) by (nonlinear_arith);
    }
    (s + k - 1) / k
}

/// `src` (`sw` by `sh` RGBA pixels) thumbnailed to `dw` by `dh`: exactly
/// `spec_lanczos::thumb` (a box shrink by a whole factor, then the kernel).
pub fn thumb_rgba(kt: &[i32], src: &[u8], sw: usize, sh: usize, dw: usize, dh: usize) -> (r: Vec<u8>)
    requires
        kt_ok(kt@),
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        1 <= dw <= MAX_DIM,
        1 <= dh <= MAX_DIM,
        src@.len() == sw * sh * NC,
    ensures
        r@ == thumb(kseq(kt@), src@, sw as int, sh as int, dw as int, dh as int),
{
    let mw = kpre_x(sw, dw);
    let mh = kpre_x(sh, dh);
    if mw == sw && mh == sh {
        kresize_rgba(kt, src, sw, sh, dw, dh)
    } else {
        proof {
            assert(mw * sh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
                requires
                    mw <= 65535,
                    sh <= 65535,
            ;
            assert(mw * mh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
                requires
                    mw <= 65535,
                    mh <= 65535,
            ;
            assert(sw * sh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
                requires
                    sw <= 65535,
                    sh <= 65535,
            ;
        }
        let mid = crate::resize::resize_rgba(src, sw, sh, mw, mh);
        proof {
            assert(mid@.len() == mw * mh * NC);
        }
        kresize_rgba(kt, &mid, mw, mh, dw, dh)
    }
}

} // verus!
