//! Area-average resizing of RGBA images, proven to compute exactly
//! `spec::resize`, with no overflow or out-of-bounds access.
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Arithmetic facts
// ---------------------------------------------------------------------------

/// `(y * w + x) * 4 + c` splits back into `y`, `x` and `c`, and lies below
/// `h * w * 4` when `y < h`.
pub proof fn lemma_idx(y: int, x: int, c: int, w: int, h: int)
    requires
        0 <= y < h,
        0 <= x < w,
        0 <= c < NC,
    ensures
        ((y * w + x) * NC + c) / NC == y * w + x,
        ((y * w + x) * NC + c) % NC == c,
        (((y * w + x) * NC + c) / NC) / w == y,
        (((y * w + x) * NC + c) / NC) % w == x,
        0 <= y * w + x < h * w,
        0 <= (y * w + x) * NC + c < h * w * NC,
        (y * w + x) * NC + c < w * h * NC,
{
    assert(0 <= y * w) by (nonlinear_arith)
        requires
            0 <= y,
            0 <= w,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((y * w + x) * NC + c, NC, y * w + x, c);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(y * w + x, w, y, x);
    assert(y * w + x < h * w) by (nonlinear_arith)
        requires
            0 <= y < h,
            0 <= x < w,
    ;
    assert((y * w + x) * NC + c < h * w * NC) by (nonlinear_arith)
        requires
            y * w + x < h * w,
            0 <= c < NC,
            NC == 4,
    ;
    assert(h * w * NC == w * h * NC) by (nonlinear_arith);
}

/// Every index below `w * h * 4` is `(y * w + x) * 4 + c` for a pixel
/// `(x, y)` and a channel `c`.
pub proof fn lemma_split(k: int, w: int, h: int)
    requires
        0 <= k < w * h * NC,
        1 <= w,
    ensures
        0 <= (k / NC) / w < h,
        0 <= (k / NC) % w < w,
        0 <= k % NC < NC,
        k == (((k / NC) / w) * w + (k / NC) % w) * NC + k % NC,
{
    let q = k / NC;
    let c = k % NC;
    let y = q / w;
    let x = q % w;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k, NC);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q, w);
    vstd::arithmetic::div_mod::lemma_mod_bound(k, NC);
    vstd::arithmetic::div_mod::lemma_mod_bound(q, w);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(k, NC);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(q, w);
    assert(k == (y * w + x) * NC + c) by (nonlinear_arith)
        requires
            k == NC * q + c,
            q == w * y + x,
    ;
    assert(y < h) by (nonlinear_arith)
        requires
            k == (y * w + x) * NC + c,
            k < w * h * NC,
            0 <= x,
            0 <= c,
            w >= 1,
    ;
}

/// Where output cell `x` starts and ends among the source samples.
pub proof fn lemma_span(x: int, s: int, d: int)
    requires
        0 <= x < d,
        1 <= s,
        1 <= d,
    ensures
        0 <= lo(x, s, d) < hi(x, s, d) <= s,
        lo(x, s, d) * d <= x * s < (lo(x, s, d) + 1) * d,
        (hi(x, s, d) - 1) * d < (x + 1) * s <= hi(x, s, d) * d,
{
    let a = x * s;
    let b = (x + 1) * s;
    let l = lo(x, s, d);
    let h = hi(x, s, d);
    assert(0 <= a) by (nonlinear_arith)
        requires
            a == x * s,
            0 <= x,
            1 <= s,
    ;
    assert(b == a + s) by (nonlinear_arith)
        requires
            a == x * s,
            b == (x + 1) * s,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, d);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b + d - 1, d);
    vstd::arithmetic::div_mod::lemma_mod_bound(a, d);
    vstd::arithmetic::div_mod::lemma_mod_bound(b + d - 1, d);
    assert(l == a / d);
    assert(h == (b + d - 1) / d);
    assert(l * d == d * (a / d)) by (nonlinear_arith)
        requires
            l == a / d,
    ;
    assert(h * d == d * ((b + d - 1) / d)) by (nonlinear_arith)
        requires
            h == (b + d - 1) / d,
    ;
    assert(0 <= l) by {
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(a, d);
    }
    assert((l + 1) * d == l * d + d) by (nonlinear_arith);
    assert((h - 1) * d == h * d - d) by (nonlinear_arith);
    // l < h: h * d >= b > a >= l * d.
    assert(l < h) by (nonlinear_arith)
        requires
            h * d >= b,
            b > a,
            a >= l * d,
            d >= 1,
    ;
    // h <= s: (h - 1) * d < b <= d * s.
    assert(b <= d * s) by (nonlinear_arith)
        requires
            b == (x + 1) * s,
            x + 1 <= d,
            1 <= s,
    ;
    assert(h <= s) by (nonlinear_arith)
        requires
            (h - 1) * d < b,
            b <= d * s,
            d >= 1,
    ;
    assert(b == (x + 1) * s);
}

/// `ov` is never negative and never more than `s` or `d`.
pub proof fn lemma_ov_bounds(x: int, i: int, s: int, d: int)
    requires
        1 <= s,
        1 <= d,
    ensures
        0 <= ov(x, i, s, d) <= s,
        ov(x, i, s, d) <= d,
{
    assert((x + 1) * s == x * s + s) by (nonlinear_arith);
    assert((i + 1) * d == i * d + d) by (nonlinear_arith);
}

/// The weight of one sample, everywhere.
pub open spec fn one() -> spec_fn(int) -> int {
    |i: int| 1int
}

/// The weights up to `k` add up to the length of the part of the cell
/// before `k * d`; over the whole span, to `s`.
pub proof fn lemma_osum(x: int, s: int, d: int, k: int)
    requires
        0 <= x < d,
        1 <= s,
        1 <= d,
        lo(x, s, d) < k <= hi(x, s, d),
    ensures
        acc(one(), x, s, d, k) == (if (x + 1) * s < k * d { (x + 1) * s } else { k * d }) - x * s,
        k == hi(x, s, d) ==> acc(one(), x, s, d, k) == s,
    decreases k - lo(x, s, d),
{
    lemma_span(x, s, d);
    let l = lo(x, s, d);
    assert((x + 1) * s == x * s + s) by (nonlinear_arith);
    assert(k * d == (k - 1) * d + d) by (nonlinear_arith);
    if k == l + 1 {
        assert(acc(one(), x, s, d, k - 1) == 0);
    } else {
        lemma_osum(x, s, d, k - 1);
        // (k - 1) * d > x * s: k - 1 >= l + 1.
        assert((k - 1) * d >= (l + 1) * d) by (nonlinear_arith)
            requires
                k - 1 >= l + 1,
                d >= 1,
        ;
        // (k - 1) * d < (x + 1) * s: k - 1 <= hi - 1.
        assert((k - 1) * d <= (hi(x, s, d) - 1) * d) by (nonlinear_arith)
            requires
                k - 1 <= hi(x, s, d) - 1,
                d >= 1,
        ;
    }
}

/// A weighted sum of values in `[0, m]` is at most `m` times the weights.
pub proof fn lemma_acc_bound(v: spec_fn(int) -> int, x: int, s: int, d: int, k: int, m: int)
    requires
        1 <= s,
        1 <= d,
        0 <= m,
        forall|i: int| lo(x, s, d) <= i < k ==> 0 <= #[trigger] v(i) <= m,
    ensures
        0 <= acc(v, x, s, d, k) <= m * acc(one(), x, s, d, k),
    decreases k - lo(x, s, d),
{
    if k > lo(x, s, d) {
        lemma_acc_bound(v, x, s, d, k - 1, m);
        lemma_ov_bounds(x, k - 1, s, d);
        let w = ov(x, k - 1, s, d);
        let a = acc(v, x, s, d, k - 1);
        let o = acc(one(), x, s, d, k - 1);
        assert(0 <= w * v(k - 1) <= m * w) by (nonlinear_arith)
            requires
                0 <= w,
                0 <= v(k - 1) <= m,
        ;
        assert(m * (o + w * 1) == m * o + m * w) by (nonlinear_arith);
    }
}

/// The row pass's values are at most 255 * 256.
pub proof fn lemma_hpx_bound(src: Seq<u8>, sw: int, dw: int, y: int, x: int, c: int)
    requires
        1 <= sw,
        1 <= dw,
        0 <= x < dw,
    ensures
        0 <= hpx(src, sw, dw, y, x, c) <= 65280,
{
    let v = src_line(src, sw, y, c);
    let h = hi(x, sw, dw);
    lemma_span(x, sw, dw);
    lemma_osum(x, sw, dw, h);
    lemma_acc_bound(v, x, sw, dw, h, 255);
    let a = acc(v, x, sw, dw, h);
    assert(0 <= a * 256 + sw / 2 <= 65280 * sw + sw / 2) by (nonlinear_arith)
        requires
            0 <= a <= 255 * sw,
            1 <= sw,
    ;
    assert(sw / 2 < sw);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(a * 256 + sw / 2, sw);
    assert((a * 256 + sw / 2) / sw <= 65280) by {
        let n = a * 256 + sw / 2;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, sw);
        vstd::arithmetic::div_mod::lemma_mod_bound(n, sw);
        assert(sw * (n / sw) <= n);
        if n / sw > 65280 {
            assert(sw * (n / sw) >= sw * 65281) by (nonlinear_arith)
                requires
                    n / sw >= 65281,
                    sw >= 1,
            ;
        }
    }
}

/// The column pass's values are at most 255 before the cast.
pub proof fn lemma_opx_bound(src: Seq<u8>, sw: int, sh: int, dw: int, dh: int, y: int, x: int, c: int)
    requires
        1 <= sw,
        1 <= dw,
        1 <= sh,
        1 <= dh,
        0 <= x < dw,
        0 <= y < dh,
    ensures
        0 <= (acc(mid_line(src, sw, dw, x, c), y, sh, dh, hi(y, sh, dh)) + 128 * sh) / (256 * sh) <= 255,
{
    let v = mid_line(src, sw, dw, x, c);
    let h = hi(y, sh, dh);
    lemma_span(y, sh, dh);
    lemma_osum(y, sh, dh, h);
    assert forall|j: int| lo(y, sh, dh) <= j < h implies 0 <= #[trigger] v(j) <= 65280 by {
        lemma_hpx_bound(src, sw, dw, j, x, c);
    }
    lemma_acc_bound(v, y, sh, dh, h, 65280);
    let a = acc(v, y, sh, dh, h);
    let n = a + 128 * sh;
    let q = 256 * sh;
    assert(0 <= n <= 65408 * sh) by (nonlinear_arith)
        requires
            0 <= a <= 65280 * sh,
            n == a + 128 * sh,
            1 <= sh,
    ;
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(n, q);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, q);
    vstd::arithmetic::div_mod::lemma_mod_bound(n, q);
    if n / q > 255 {
        assert(q * (n / q) >= q * 256) by (nonlinear_arith)
            requires
                n / q >= 256,
                q >= 1,
        ;
        assert(q * 256 == 65536 * sh);
    }
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

/// `spec::lo` and `spec::hi`.
fn span(x: usize, s: usize, d: usize) -> (r: (usize, usize))
    requires
        x < d <= MAX_DIM,
        1 <= s <= MAX_DIM,
    ensures
        r.0 == lo(x as int, s as int, d as int),
        r.1 == hi(x as int, s as int, d as int),
{
    proof {
        assert(x * s <= (x + 1) * s <= 65535 * 65535) by (nonlinear_arith)
            requires
                x + 1 <= 65535,
                s <= 65535,
        ;
    }
    (x * s / d, ((x + 1) * s + d - 1) / d)
}

/// `spec::ov`.
#[inline(always)]
fn ov_x(x: usize, i: usize, s: usize, d: usize) -> (r: usize)
    requires
        x < d <= MAX_DIM,
        i < s <= MAX_DIM,
    ensures
        r == ov(x as int, i as int, s as int, d as int),
        r <= MAX_DIM,
{
    proof {
        assert(x * s + s <= 65535 * 65535) by (nonlinear_arith)
            requires
                x + 1 <= 65535,
                s <= 65535,
        ;
        assert(i * d + d <= 65535 * 65535) by (nonlinear_arith)
            requires
                i + 1 <= 65535,
                d <= 65535,
        ;
        assert((x + 1) * s == x * s + s) by (nonlinear_arith);
        assert((i + 1) * d == i * d + d) by (nonlinear_arith);
        lemma_ov_bounds(x as int, i as int, s as int, d as int);
    }
    let xs = x * s;
    let id = i * d;
    let a = if xs > id { xs } else { id };
    let xs1 = xs + s;
    let id1 = id + d;
    let b = if xs1 < id1 { xs1 } else { id1 };
    if b > a { b - a } else { 0 }
}

/// The row pass's value at index `k` of its output.
pub open spec fn hval(src: Seq<u8>, sw: int, dw: int, k: int) -> int {
    hpx(src, sw, dw, (k / NC) / dw, (k / NC) % dw, k % NC)
}

/// The row pass: `dw * sh * 4` values, `hpx` of each pixel and channel,
/// row by row.
#[verifier::spinoff_prover]
pub fn rows(src: &[u8], sw: usize, sh: usize, dw: usize) -> (r: Vec<u16>)
    requires
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        1 <= dw <= MAX_DIM,
        src@.len() == sw * sh * NC,
            sw * sh * NC <= 65535 * 65535 * 4,
        dw * sh * NC <= usize::MAX,
    ensures
        r@.len() == dw * sh * NC,
        forall|y: int, x: int, c: int|
            0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] r@[(y * dw + x) * NC + c] == hpx(
                src@,
                sw as int,
                dw as int,
                y,
                x,
                c,
            ),
{
    let ghost s = src@;
    let mut out: Vec<u16> = Vec::with_capacity(dw * sh * 4);
    let mut y: usize = 0;
    while y < sh
        invariant
            1 <= sw <= MAX_DIM,
            1 <= sh <= MAX_DIM,
            1 <= dw <= MAX_DIM,
            s == src@,
            src@.len() == sw * sh * NC,
            sw * sh * NC <= 65535 * 65535 * 4,
            dw * sh * NC <= usize::MAX,
            y <= sh,
            out@.len() == y * dw * NC,
            forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == hval(s, sw as int, dw as int, k),
        decreases sh - y,
    {
        let mut x: usize = 0;
        while x < dw
            invariant
                1 <= sw <= MAX_DIM,
                1 <= sh <= MAX_DIM,
                1 <= dw <= MAX_DIM,
                s == src@,
                src@.len() == sw * sh * NC,
            sw * sh * NC <= 65535 * 65535 * 4,
                dw * sh * NC <= usize::MAX,
                y < sh,
                x <= dw,
                out@.len() == (y * dw + x) * NC,
                forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == hval(s, sw as int, dw as int, k),
            decreases dw - x,
        {
            let (l, h) = span(x, sw, dw);
            proof {
                lemma_span(x as int, sw as int, dw as int);
            }
            let mut a0: u64 = 0;
            let mut a1: u64 = 0;
            let mut a2: u64 = 0;
            let mut a3: u64 = 0;
            let mut i = l;
            while i < h
                invariant
                    1 <= sw <= MAX_DIM,
                    1 <= sh <= MAX_DIM,
                    1 <= dw <= MAX_DIM,
                    s == src@,
                    src@.len() == sw * sh * NC,
            sw * sh * NC <= 65535 * 65535 * 4,
                    y < sh,
                    x < dw,
                    l == lo(x as int, sw as int, dw as int),
                    h == hi(x as int, sw as int, dw as int),
                    0 <= l <= i <= h <= sw,
                    a0 == acc(src_line(s, sw as int, y as int, 0), x as int, sw as int, dw as int, i as int),
                    a1 == acc(src_line(s, sw as int, y as int, 1), x as int, sw as int, dw as int, i as int),
                    a2 == acc(src_line(s, sw as int, y as int, 2), x as int, sw as int, dw as int, i as int),
                    a3 == acc(src_line(s, sw as int, y as int, 3), x as int, sw as int, dw as int, i as int),
                    a0 <= (i - l) * (65535 * 255),
                    a1 <= (i - l) * (65535 * 255),
                    a2 <= (i - l) * (65535 * 255),
                    a3 <= (i - l) * (65535 * 255),
                decreases h - i,
            {
                let w = ov_x(x, i, sw, dw) as u64;
                proof {
                    lemma_idx(y as int, i as int, 3, sw as int, sh as int);
                    assert(w * 255 <= 65535 * 255);
                }
                let p = (y * sw + i) * 4;
                let v0 = verilith_core::prims::get(src, p) as u64;
                let v1 = verilith_core::prims::get(src, p + 1) as u64;
                let v2 = verilith_core::prims::get(src, p + 2) as u64;
                let v3 = verilith_core::prims::get(src, p + 3) as u64;
                proof {
                    assert(w * v0 <= 65535 * 255 && w * v1 <= 65535 * 255 && w * v2 <= 65535 * 255 && w * v3
                        <= 65535 * 255) by (nonlinear_arith)
                        requires
                            w <= 65535,
                            v0 <= 255,
                            v1 <= 255,
                            v2 <= 255,
                            v3 <= 255,
                    ;
                    assert((i + 1 - l) * (65535 * 255) == (i - l) * (65535 * 255) + 65535 * 255) by (nonlinear_arith);
                    assert(i - l <= 65535);
                    assert((i - l) * (65535 * 255) <= 65535 * (65535 * 255)) by (nonlinear_arith)
                        requires
                            0 <= i - l <= 65535,
                    ;
                }
                a0 = a0 + w * v0;
                a1 = a1 + w * v1;
                a2 = a2 + w * v2;
                a3 = a3 + w * v3;
                i = i + 1;
            }
            let half = (sw / 2) as u64;
            let swu = sw as u64;
            proof {
                lemma_hpx_bound(s, sw as int, dw as int, y as int, x as int, 0);
                lemma_hpx_bound(s, sw as int, dw as int, y as int, x as int, 1);
                lemma_hpx_bound(s, sw as int, dw as int, y as int, x as int, 2);
                lemma_hpx_bound(s, sw as int, dw as int, y as int, x as int, 3);
                assert((h - l) * (65535 * 255) <= 65535 * (65535 * 255)) by (nonlinear_arith)
                    requires
                        0 <= h - l <= 65535,
                ;
                lemma_idx(y as int, x as int, 3, dw as int, sh as int);
            }
            let ghost before = out@;
            out.push(((a0 * 256 + half) / swu) as u16);
            out.push(((a1 * 256 + half) / swu) as u16);
            out.push(((a2 * 256 + half) / swu) as u16);
            out.push(((a3 * 256 + half) / swu) as u16);
            proof {
                assert((y * dw + x + 1) * NC == (y * dw + x) * NC + 4) by (nonlinear_arith);
                assert forall|k: int| 0 <= k < out@.len() implies #[trigger] out@[k] == hval(s, sw as int, dw as int, k) by {
                    if k >= before.len() {
                        let base = (y * dw + x) * NC;
                        lemma_idx(y as int, x as int, k - base, dw as int, sh as int);
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
            0 <= y < sh && 0 <= x < dw && 0 <= c < NC implies #[trigger] out@[(y * dw + x) * NC + c] == hpx(
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
pub open spec fn oval(src: Seq<u8>, sw: int, sh: int, dw: int, dh: int, k: int) -> u8 {
    opx(src, sw, sh, dw, dh, (k / NC) / dw, (k / NC) % dw, k % NC)
}

/// The column pass, over the row pass's values `mid`: the resized image.
#[verifier::spinoff_prover]
pub fn cols(mid: &[u16], sw: usize, sh: usize, dw: usize, dh: usize, Ghost(src): Ghost<Seq<u8>>) -> (r: Vec<u8>)
    requires
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        1 <= dw <= MAX_DIM,
        1 <= dh <= MAX_DIM,
        mid@.len() == dw * sh * NC,
            dw * sh * NC <= 65535 * 65535 * 4,
        dw * dh * NC <= usize::MAX,
        forall|y: int, x: int, c: int|
            0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] mid@[(y * dw + x) * NC + c] == hpx(
                src,
                sw as int,
                dw as int,
                y,
                x,
                c,
            ),
    ensures
        r@ == resize(src, sw as int, sh as int, dw as int, dh as int),
{
    let mut out: Vec<u8> = Vec::with_capacity(dw * dh * 4);
    let shu = sh as u64;
    let mut y: usize = 0;
    while y < dh
        invariant
            1 <= sw <= MAX_DIM,
            1 <= sh <= MAX_DIM,
            1 <= dw <= MAX_DIM,
            1 <= dh <= MAX_DIM,
            shu == sh,
            mid@.len() == dw * sh * NC,
            dw * sh * NC <= 65535 * 65535 * 4,
            dw * dh * NC <= usize::MAX,
            forall|y: int, x: int, c: int|
                0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] mid@[(y * dw + x) * NC + c] == hpx(
                    src,
                    sw as int,
                    dw as int,
                    y,
                    x,
                    c,
                ),
            y <= dh,
            out@.len() == y * dw * NC,
            forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == oval(src, sw as int, sh as int, dw as int, dh as int, k),
        decreases dh - y,
    {
        let (l, h) = span(y, sh, dh);
        proof {
            lemma_span(y as int, sh as int, dh as int);
        }
        let mut x: usize = 0;
        while x < dw
            invariant
                1 <= sw <= MAX_DIM,
                1 <= sh <= MAX_DIM,
                1 <= dw <= MAX_DIM,
                1 <= dh <= MAX_DIM,
                shu == sh,
                mid@.len() == dw * sh * NC,
            dw * sh * NC <= 65535 * 65535 * 4,
                dw * dh * NC <= usize::MAX,
                forall|y: int, x: int, c: int|
                    0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] mid@[(y * dw + x) * NC + c] == hpx(
                        src,
                        sw as int,
                        dw as int,
                        y,
                        x,
                        c,
                    ),
                y < dh,
                x <= dw,
                l == lo(y as int, sh as int, dh as int),
                h == hi(y as int, sh as int, dh as int),
                0 <= l < h <= sh,
                out@.len() == (y * dw + x) * NC,
                forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == oval(src, sw as int, sh as int, dw as int, dh as int, k),
            decreases dw - x,
        {
            let mut a0: u64 = 0;
            let mut a1: u64 = 0;
            let mut a2: u64 = 0;
            let mut a3: u64 = 0;
            let mut j = l;
            while j < h
                invariant
                    1 <= sw <= MAX_DIM,
                    1 <= sh <= MAX_DIM,
                    1 <= dw <= MAX_DIM,
                    1 <= dh <= MAX_DIM,
                    mid@.len() == dw * sh * NC,
            dw * sh * NC <= 65535 * 65535 * 4,
                    forall|y: int, x: int, c: int|
                        0 <= y < sh && 0 <= x < dw && 0 <= c < NC ==> #[trigger] mid@[(y * dw + x) * NC + c] == hpx(
                            src,
                            sw as int,
                            dw as int,
                            y,
                            x,
                            c,
                        ),
                    y < dh,
                    x < dw,
                    l == lo(y as int, sh as int, dh as int),
                    h == hi(y as int, sh as int, dh as int),
                    0 <= l <= j <= h <= sh,
                    a0 == acc(mid_line(src, sw as int, dw as int, x as int, 0), y as int, sh as int, dh as int, j as int),
                    a1 == acc(mid_line(src, sw as int, dw as int, x as int, 1), y as int, sh as int, dh as int, j as int),
                    a2 == acc(mid_line(src, sw as int, dw as int, x as int, 2), y as int, sh as int, dh as int, j as int),
                    a3 == acc(mid_line(src, sw as int, dw as int, x as int, 3), y as int, sh as int, dh as int, j as int),
                    a0 <= (j - l) * (65535 * 65535),
                    a1 <= (j - l) * (65535 * 65535),
                    a2 <= (j - l) * (65535 * 65535),
                    a3 <= (j - l) * (65535 * 65535),
                decreases h - j,
            {
                let w = ov_x(y, j, sh, dh) as u64;
                proof {
                    lemma_idx(j as int, x as int, 3, dw as int, sh as int);
                }
                let p = (j * dw + x) * 4;
                proof {
                    assert((j * dw + x) * NC + 1 == p + 1);
                    assert((j * dw + x) * NC + 2 == p + 2);
                    assert((j * dw + x) * NC + 3 == p + 3);
                    assert(mid@[(j * dw + x) * NC + 0] == hpx(src, sw as int, dw as int, j as int, x as int, 0));
                    assert(mid@[(j * dw + x) * NC + 1] == hpx(src, sw as int, dw as int, j as int, x as int, 1));
                    assert(mid@[(j * dw + x) * NC + 2] == hpx(src, sw as int, dw as int, j as int, x as int, 2));
                    assert(mid@[(j * dw + x) * NC + 3] == hpx(src, sw as int, dw as int, j as int, x as int, 3));
                }
                let v0 = verilith_core::prims::get_u16(mid, p) as u64;
                let v1 = verilith_core::prims::get_u16(mid, p + 1) as u64;
                let v2 = verilith_core::prims::get_u16(mid, p + 2) as u64;
                let v3 = verilith_core::prims::get_u16(mid, p + 3) as u64;
                proof {
                    assert(w * v0 <= 65535 * 65535 && w * v1 <= 65535 * 65535 && w * v2 <= 65535 * 65535 && w
                        * v3 <= 65535 * 65535) by (nonlinear_arith)
                        requires
                            w <= 65535,
                            v0 <= 65535,
                            v1 <= 65535,
                            v2 <= 65535,
                            v3 <= 65535,
                    ;
                    assert((j + 1 - l) * (65535 * 65535) == (j - l) * (65535 * 65535) + 65535 * 65535) by (nonlinear_arith);
                    assert(j - l <= 65535);
                    assert((j - l) * (65535 * 65535) <= 65535 * (65535 * 65535)) by (nonlinear_arith)
                        requires
                            0 <= j - l <= 65535,
                    ;
                }
                a0 = a0 + w * v0;
                a1 = a1 + w * v1;
                a2 = a2 + w * v2;
                a3 = a3 + w * v3;
                j = j + 1;
            }
            proof {
                lemma_opx_bound(src, sw as int, sh as int, dw as int, dh as int, y as int, x as int, 0);
                lemma_opx_bound(src, sw as int, sh as int, dw as int, dh as int, y as int, x as int, 1);
                lemma_opx_bound(src, sw as int, sh as int, dw as int, dh as int, y as int, x as int, 2);
                lemma_opx_bound(src, sw as int, sh as int, dw as int, dh as int, y as int, x as int, 3);
                assert((h - l) * (65535 * 65535) <= 65535 * (65535 * 65535)) by (nonlinear_arith)
                    requires
                        0 <= h - l <= 65535,
                ;
                lemma_idx(y as int, x as int, 3, dw as int, dh as int);
            }
            let rnd = 128 * shu;
            let q = 256 * shu;
            let ghost before = out@;
            out.push(((a0 + rnd) / q) as u8);
            out.push(((a1 + rnd) / q) as u8);
            out.push(((a2 + rnd) / q) as u8);
            out.push(((a3 + rnd) / q) as u8);
            proof {
                assert((y * dw + x + 1) * NC == (y * dw + x) * NC + 4) by (nonlinear_arith);
                assert forall|k: int| 0 <= k < out@.len() implies #[trigger] out@[k] == oval(src, sw as int, sh as int, dw as int, dh as int, k) by {
                    if k >= before.len() {
                        let base = (y * dw + x) * NC;
                        lemma_idx(y as int, x as int, k - base, dw as int, dh as int);
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
        let want = resize(src, sw as int, sh as int, dw as int, dh as int);
        assert(out@.len() == dw * dh * NC) by (nonlinear_arith)
            requires
                out@.len() == dh * dw * NC,
        ;
        assert(out@ =~= want);
    }
    out
}

/// `src` (`sw` by `sh` RGBA pixels) resized to `dw` by `dh`: exactly
/// `spec::resize`.
pub fn resize_rgba(src: &[u8], sw: usize, sh: usize, dw: usize, dh: usize) -> (r: Vec<u8>)
    requires
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        1 <= dw <= MAX_DIM,
        1 <= dh <= MAX_DIM,
        src@.len() == sw * sh * NC,
            sw * sh * NC <= 65535 * 65535 * 4,
        dw * sh * NC <= usize::MAX,
        dw * dh * NC <= usize::MAX,
    ensures
        r@ == resize(src@, sw as int, sh as int, dw as int, dh as int),
{
    proof {
        assert(sw * sh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                sw <= 65535,
                sh <= 65535,
        ;
        assert(dw * sh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                dw <= 65535,
                sh <= 65535,
        ;
    }
    let mid = rows(src, sw, sh, dw);
    cols(&mid, sw, sh, dw, dh, Ghost(src@))
}

/// The value `crop` gives at index `k`.
pub open spec fn cval(src: Seq<u8>, sw: int, x0: int, y0: int, cw: int, k: int) -> u8 {
    src[((y0 + (k / NC) / cw) * sw + x0 + (k / NC) % cw) * NC + k % NC]
}

/// The `cw` by `ch` rectangle at `(x0, y0)` of `src` (`sw` by `sh`):
/// exactly `spec::crop`.
pub fn crop_rgba(src: &[u8], sw: usize, sh: usize, x0: usize, y0: usize, cw: usize, ch: usize) -> (r: Vec<u8>)
    requires
        1 <= sw <= MAX_DIM,
        1 <= sh <= MAX_DIM,
        1 <= cw,
        1 <= ch,
        x0 + cw <= sw,
        y0 + ch <= sh,
        src@.len() == sw * sh * NC,
    ensures
        r@ == crop(src@, sw as int, x0 as int, y0 as int, cw as int, ch as int),
{
    proof {
        assert(cw * ch * NC <= sw * sh * NC) by (nonlinear_arith)
            requires
                cw <= sw,
                ch <= sh,
        ;
        assert(sw * sh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                sw <= 65535,
                sh <= 65535,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(cw * ch * 4);
    let mut y: usize = 0;
    while y < ch
        invariant
            1 <= sw <= MAX_DIM,
            1 <= sh <= MAX_DIM,
            1 <= cw,
            x0 + cw <= sw,
            y0 + ch <= sh,
            src@.len() == sw * sh * NC,
            cw * ch * NC <= sw * sh * NC,
            sw * sh * NC <= 65535 * 65535 * 4,
            y <= ch,
            out@.len() == y * cw * NC,
            forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == cval(src@, sw as int, x0 as int, y0 as int, cw as int, k),
        decreases ch - y,
    {
        proof {
            lemma_idx((y0 + y) as int, x0 as int, 0, sw as int, sh as int);
            assert(((y0 + y) * sw + x0 + cw) * NC <= sw * sh * NC) by (nonlinear_arith)
                requires
                    x0 + cw <= sw,
                    y0 + y < sh,
            ;
            assert(y * cw * NC + cw * NC <= cw * ch * NC) by (nonlinear_arith)
                requires
                    y < ch,
            ;
        }
        let row = ((y0 + y) * sw + x0) * 4;
        let mut k: usize = 0;
        while k < cw * 4
            invariant
                1 <= sw <= MAX_DIM,
                1 <= cw,
                src@.len() == sw * sh * NC,
                y < ch,
                y0 + ch <= sh,
                x0 + cw <= sw,
                row == ((y0 + y) * sw + x0) * NC,
                ((y0 + y) * sw + x0 + cw) * NC <= sw * sh * NC,
                y * cw * NC + cw * NC <= cw * ch * NC,
                cw * ch * NC <= sw * sh * NC,
                sw * sh * NC <= 65535 * 65535 * 4,
                k <= cw * NC,
                out@.len() == y * cw * NC + k,
                forall|kk: int| 0 <= kk < out@.len() ==> #[trigger] out@[kk] == cval(src@, sw as int, x0 as int, y0 as int, cw as int, kk),
            decreases cw * NC - k,
        {
            proof {
                assert(((y0 + y) * sw + x0 + cw) * NC == ((y0 + y) * sw + x0) * NC + cw * NC) by (nonlinear_arith);
            }
            let ghost before = out@;
            out.push(src[row + k]);
            proof {
                let q = (k as int) / NC;
                let c = (k as int) % NC;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k as int, NC);
                vstd::arithmetic::div_mod::lemma_mod_bound(k as int, NC);
                vstd::arithmetic::div_mod::lemma_div_pos_is_pos(k as int, NC);
                assert(q < cw) by (nonlinear_arith)
                    requires
                        k == NC * q + c,
                        k < cw * NC,
                        0 <= c,
                ;
                lemma_idx(y as int, q, c, cw as int, ch as int);
                let kk = before.len() as int;
                assert(kk == (y * cw + q) * NC + c) by (nonlinear_arith)
                    requires
                        kk == y * cw * NC + k,
                        k == NC * q + c,
                ;
                assert(row + k == ((y0 + y) * sw + x0 + q) * NC + c) by (nonlinear_arith)
                    requires
                        row == ((y0 + y) * sw + x0) * NC,
                        k == NC * q + c,
                ;
            }
            k = k + 1;
        }
        proof {
            assert(y * cw * NC + cw * NC == (y + 1) * cw * NC) by (nonlinear_arith);
        }
        y = y + 1;
    }
    proof {
        let want = crop(src@, sw as int, x0 as int, y0 as int, cw as int, ch as int);
        assert(out@.len() == cw * ch * NC) by (nonlinear_arith)
            requires
                out@.len() == ch * cw * NC,
        ;
        assert(out@ =~= want);
    }
    out
}

} // verus!
