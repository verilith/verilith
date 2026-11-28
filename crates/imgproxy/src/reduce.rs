//! `vips_resize`'s passes on 8-bit RGBA, proven to compute `spec_reduce`'s
//! for every image up to 65535 by 65535, every set of masks of up to 1000
//! taps, and every choice of where output samples start: no overflow, no
//! out-of-bounds access. Which masks and positions libvips takes is
//! `reduce_plan`'s (trusted) business.
use crate::filter::fixavg_x;
use crate::lanczos::kc_x;
#[cfg(verus_only)]
use crate::resize::lemma_idx;
use crate::spec::*;
use crate::spec_lanczos::*;
use crate::spec_reduce::*;
use vstd::prelude::*;

verus! {

/// The masks and positions the proofs cover: `n` taps, 65 masks, each
/// output sample's mask index at most 64 and its start within 2^32.
pub open spec fn plan_ok(n: int, m: Seq<i16>, st: Seq<i64>, t: Seq<u8>, o: int) -> bool {
    &&& 1 <= n <= 1000
    &&& m.len() == 65 * n
    &&& st.len() == o
    &&& t.len() == o
    &&& forall|j: int| 0 <= j < o ==> #[trigger] t[j] <= 64
    &&& forall|j: int| 0 <= j < o ==> -0x1_0000_0000 <= #[trigger] st[j] <= 0x1_0000_0000
}

/// The largest product of a mask entry and an 8-bit value.
pub open spec fn tmax() -> int {
    8355840int
}

pub proof fn lemma_tsum_bound(v: spec_fn(int) -> int, m: Seq<i16>, b: int, st: int, s: int, n: int)
    requires
        0 <= n,
        0 <= b,
        b + n <= m.len(),
        forall|i: int| 0 <= #[trigger] v(i) <= 255,
    ensures
        -n * tmax() <= tsum(v, m, b, st, s, n) <= n * tmax(),
    decreases n,
{
    if n > 0 {
        lemma_tsum_bound(v, m, b, st, s, n - 1);
        let a = m[b + n - 1] as int;
        let c = v(kc(st + n - 1, s));
        assert(-tmax() <= a * c <= tmax()) by (nonlinear_arith)
            requires
                -32768 <= a <= 32767,
                0 <= c <= 255,
        ;
        assert((n - 1) * tmax() + tmax() == n * tmax()) by (nonlinear_arith);
    }
}

/// `fround`, for sums within the bound above.
pub fn fround_x(sum: i64) -> (r: u8)
    requires
        -0x10_0000_0000 <= sum <= 0x10_0000_0000,
    ensures
        r as int == fround(sum as int),
{
    let a = sum + 2048;
    if a < 0 {
        proof {
            assert((a as int) / 4096 < 0) by (nonlinear_arith)
                requires
                    a < 0,
            ;
        }
        0
    } else {
        let q = a / 4096;
        if q > 255 {
            255
        } else {
            q as u8
        }
    }
}

pub proof fn lemma_rows(o: int, w: int, x: int)
    requires
        0 <= x <= w,
    ensures
        (o * w + x) * NC == o * w * NC + x * NC,
        (o * w + w) * NC == (o + 1) * w * NC,
{
    assert((o * w + x) * NC == o * w * NC + x * NC) by (nonlinear_arith);
    assert((o * w + w) * NC == (o + 1) * w * NC) by (nonlinear_arith);
}

/// The reduction's value at index `k` of its output.
pub open spec fn rvval(src: Seq<u8>, w: int, h: int, n: int, m: Seq<i16>, st: Seq<i64>, t: Seq<u8>, oh: int, k: int) -> u8 {
    reducev(src, w, h, n, m, st, t, oh)[k]
}

/// `reducev`.
#[verifier::rlimit(60)]
pub fn reducev_x(src: &[u8], w: usize, h: usize, n: usize, m: &[i16], st: &[i64], t: &[u8], oh: usize) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        1 <= oh <= MAX_DIM,
        src@.len() == w * h * NC,
        plan_ok(n as int, m@, st@, t@, oh as int),
    ensures
        r@ == reducev(src@, w as int, h as int, n as int, m@, st@, t@, oh as int),
{
    let ghost s = src@;
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4 && w * oh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                1 <= oh <= MAX_DIM,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(w * oh * 4);
    let mut o: usize = 0;
    while o < oh
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            1 <= oh <= MAX_DIM,
            s == src@,
            src@.len() == w * h * NC,
            plan_ok(n as int, m@, st@, t@, oh as int),
            o <= oh,
            out@.len() == o * w * NC,
            forall|j: int|
                0 <= j < out@.len() ==> #[trigger] out@[j] == rvval(s, w as int, h as int, n as int, m@, st@, t@, oh as int, j),
        decreases oh - o,
    {
        let s0 = st[o];
        let to = t[o] as usize;
        proof {
            assert(t@[o as int] <= 64);
            assert(to * n <= 64000) by (nonlinear_arith)
                requires
                    to <= 64,
                    n <= 1000,
            ;
        }
        let b = to * n;
        proof {
            assert(t@[o as int] <= 64);
            assert(b + n <= 65 * n) by (nonlinear_arith)
                requires
                    b == t@[o as int] as int * n,
                    t@[o as int] <= 64,
            ;
        }
        let mut x: usize = 0;
        while x < w
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                1 <= oh <= MAX_DIM,
                s == src@,
                src@.len() == w * h * NC,
                plan_ok(n as int, m@, st@, t@, oh as int),
                o < oh,
                s0 == st@[o as int],
                b == t@[o as int] as int * n,
                b + n <= m@.len(),
                x <= w,
                out@.len() == o * w * NC + x * NC,
                forall|j: int|
                    0 <= j < out@.len() ==> #[trigger] out@[j] == rvval(s, w as int, h as int, n as int, m@, st@, t@, oh as int, j),
            decreases w - x,
        {
            let mut a0: i64 = 0;
            let mut a1: i64 = 0;
            let mut a2: i64 = 0;
            let mut a3: i64 = 0;
            let mut i: usize = 0;
            while i < n
                invariant
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    s == src@,
                    src@.len() == w * h * NC,
                    plan_ok(n as int, m@, st@, t@, oh as int),
                    o < oh,
                    s0 == st@[o as int],
                    b + n <= m@.len(),
                    x < w,
                    i <= n,
                    a0 == tsum(col_line(s, w as int, x as int, 0), m@, b as int, s0 as int, h as int, i as int),
                    a1 == tsum(col_line(s, w as int, x as int, 1), m@, b as int, s0 as int, h as int, i as int),
                    a2 == tsum(col_line(s, w as int, x as int, 2), m@, b as int, s0 as int, h as int, i as int),
                    a3 == tsum(col_line(s, w as int, x as int, 3), m@, b as int, s0 as int, h as int, i as int),
                    -i * tmax() <= a0 <= i * tmax(),
                    -i * tmax() <= a1 <= i * tmax(),
                    -i * tmax() <= a2 <= i * tmax(),
                    -i * tmax() <= a3 <= i * tmax(),
                decreases n - i,
            {
                let yy = kc_x(s0 + i as i64, h);
                let c = m[b + i] as i64;
                proof {
                    lemma_idx(yy as int, x as int, 3, w as int, h as int);
                    lemma_idx(yy as int, x as int, 0, w as int, h as int);
                    assert((yy * w + x) * NC + 3 < w * h * NC && h * w <= 65535 * 65535) by (nonlinear_arith)
                        requires
                            0 <= yy * w + x < h * w,
                            1 <= w <= MAX_DIM,
                            1 <= h <= MAX_DIM,
                    ;
                }
                let p = (yy * w + x) * 4;
                let v0 = src[p] as i64;
                let v1 = src[p + 1] as i64;
                let v2 = src[p + 2] as i64;
                let v3 = src[p + 3] as i64;
                proof {
                    assert(-tmax() <= c * v0 <= tmax() && -tmax() <= c * v1 <= tmax() && -tmax() <= c * v2 <= tmax()
                        && -tmax() <= c * v3 <= tmax()) by (nonlinear_arith)
                        requires
                            -32768 <= c <= 32767,
                            0 <= v0 <= 255,
                            0 <= v1 <= 255,
                            0 <= v2 <= 255,
                            0 <= v3 <= 255,
                    ;
                    assert((i + 1) * tmax() == i * tmax() + tmax()) by (nonlinear_arith);
                    assert(col_line(s, w as int, x as int, 0)(yy as int) == v0);
                    assert(col_line(s, w as int, x as int, 1)(yy as int) == v1);
                    assert(col_line(s, w as int, x as int, 2)(yy as int) == v2);
                    assert(col_line(s, w as int, x as int, 3)(yy as int) == v3);
                    assert(m@[b + i] as int == c);
                }
                a0 = a0 + c * v0;
                a1 = a1 + c * v1;
                a2 = a2 + c * v2;
                a3 = a3 + c * v3;
                i = i + 1;
            }
            proof {
                assert(i * tmax() <= 1000 * tmax()) by (nonlinear_arith)
                    requires
                        i <= 1000,
                ;
                lemma_rows(o as int, w as int, x as int);
                lemma_rows(o as int, w as int, x as int + 1);
            }
            let ghost before = out@;
            out.push(fround_x(a0));
            out.push(fround_x(a1));
            out.push(fround_x(a2));
            out.push(fround_x(a3));
            proof {
                assert forall|j: int|
                    0 <= j < out@.len() implies #[trigger] out@[j] == rvval(s, w as int, h as int, n as int, m@, st@, t@, oh as int, j) by {
                    if j >= before.len() {
                        let bb = (o * w + x) * NC;
                        lemma_idx(o as int, x as int, j - bb, w as int, oh as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            x = x + 1;
        }
        proof {
            lemma_rows(o as int, w as int, w as int);
        }
        o = o + 1;
    }
    proof {
        assert(out@.len() == w * oh * NC) by (nonlinear_arith)
            requires
                out@.len() == oh * w * NC,
        ;
        assert(out@ =~= reducev(s, w as int, h as int, n as int, m@, st@, t@, oh as int));
    }
    out
}

/// The row reduction's value at index `k` of its output.
pub open spec fn rhval(src: Seq<u8>, w: int, h: int, n: int, m: Seq<i16>, st: Seq<i64>, t: Seq<u8>, ow: int, k: int) -> u8 {
    reduceh(src, w, h, n, m, st, t, ow)[k]
}

/// `reduceh`.
#[verifier::rlimit(60)]
pub fn reduceh_x(src: &[u8], w: usize, h: usize, n: usize, m: &[i16], st: &[i64], t: &[u8], ow: usize) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        1 <= ow <= MAX_DIM,
        src@.len() == w * h * NC,
        plan_ok(n as int, m@, st@, t@, ow as int),
    ensures
        r@ == reduceh(src@, w as int, h as int, n as int, m@, st@, t@, ow as int),
{
    let ghost s = src@;
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4 && ow * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                1 <= ow <= MAX_DIM,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(ow * h * 4);
    let mut y: usize = 0;
    while y < h
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            1 <= ow <= MAX_DIM,
            s == src@,
            src@.len() == w * h * NC,
            plan_ok(n as int, m@, st@, t@, ow as int),
            y <= h,
            out@.len() == y * ow * NC,
            forall|j: int|
                0 <= j < out@.len() ==> #[trigger] out@[j] == rhval(s, w as int, h as int, n as int, m@, st@, t@, ow as int, j),
        decreases h - y,
    {
        let mut o: usize = 0;
        while o < ow
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                1 <= ow <= MAX_DIM,
                s == src@,
                src@.len() == w * h * NC,
                plan_ok(n as int, m@, st@, t@, ow as int),
                y < h,
                o <= ow,
                out@.len() == y * ow * NC + o * NC,
                forall|j: int|
                    0 <= j < out@.len() ==> #[trigger] out@[j] == rhval(s, w as int, h as int, n as int, m@, st@, t@, ow as int, j),
            decreases ow - o,
        {
        let s0 = st[o];
        let to = t[o] as usize;
        proof {
            assert(t@[o as int] <= 64);
            assert(to * n <= 64000) by (nonlinear_arith)
                requires
                    to <= 64,
                    n <= 1000,
            ;
        }
        let b = to * n;
        proof {
            assert(t@[o as int] <= 64);
            assert(b + n <= 65 * n) by (nonlinear_arith)
                requires
                    b == t@[o as int] as int * n,
                    t@[o as int] <= 64,
            ;
        }
            let mut a0: i64 = 0;
            let mut a1: i64 = 0;
            let mut a2: i64 = 0;
            let mut a3: i64 = 0;
            let mut i: usize = 0;
            while i < n
                invariant
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    s == src@,
                    src@.len() == w * h * NC,
                    plan_ok(n as int, m@, st@, t@, ow as int),
                    o < ow,
                    y < h,
                    s0 == st@[o as int],
                    b + n <= m@.len(),
                    i <= n,
                    a0 == tsum(src_line(s, w as int, y as int, 0), m@, b as int, s0 as int, w as int, i as int),
                    a1 == tsum(src_line(s, w as int, y as int, 1), m@, b as int, s0 as int, w as int, i as int),
                    a2 == tsum(src_line(s, w as int, y as int, 2), m@, b as int, s0 as int, w as int, i as int),
                    a3 == tsum(src_line(s, w as int, y as int, 3), m@, b as int, s0 as int, w as int, i as int),
                    -i * tmax() <= a0 <= i * tmax(),
                    -i * tmax() <= a1 <= i * tmax(),
                    -i * tmax() <= a2 <= i * tmax(),
                    -i * tmax() <= a3 <= i * tmax(),
                decreases n - i,
            {
                let xx = kc_x(s0 + i as i64, w);
                let c = m[b + i] as i64;
                proof {
                    lemma_idx(y as int, xx as int, 3, w as int, h as int);
                    lemma_idx(y as int, xx as int, 0, w as int, h as int);
                    assert((y * w + xx) * NC + 3 < w * h * NC && h * w <= 65535 * 65535) by (nonlinear_arith)
                        requires
                            0 <= y * w + xx < h * w,
                            1 <= w <= MAX_DIM,
                            1 <= h <= MAX_DIM,
                    ;
                }
                let p = (y * w + xx) * 4;
                let v0 = src[p] as i64;
                let v1 = src[p + 1] as i64;
                let v2 = src[p + 2] as i64;
                let v3 = src[p + 3] as i64;
                proof {
                    assert(-tmax() <= c * v0 <= tmax() && -tmax() <= c * v1 <= tmax() && -tmax() <= c * v2 <= tmax()
                        && -tmax() <= c * v3 <= tmax()) by (nonlinear_arith)
                        requires
                            -32768 <= c <= 32767,
                            0 <= v0 <= 255,
                            0 <= v1 <= 255,
                            0 <= v2 <= 255,
                            0 <= v3 <= 255,
                    ;
                    assert((i + 1) * tmax() == i * tmax() + tmax()) by (nonlinear_arith);
                    assert(src_line(s, w as int, y as int, 0)(xx as int) == v0);
                    assert(src_line(s, w as int, y as int, 1)(xx as int) == v1);
                    assert(src_line(s, w as int, y as int, 2)(xx as int) == v2);
                    assert(src_line(s, w as int, y as int, 3)(xx as int) == v3);
                    assert(m@[b + i] as int == c);
                }
                a0 = a0 + c * v0;
                a1 = a1 + c * v1;
                a2 = a2 + c * v2;
                a3 = a3 + c * v3;
                i = i + 1;
            }
            proof {
                assert(i * tmax() <= 1000 * tmax()) by (nonlinear_arith)
                    requires
                        i <= 1000,
                ;
                lemma_rows(y as int, ow as int, o as int);
                lemma_rows(y as int, ow as int, o as int + 1);
            }
            let ghost before = out@;
            out.push(fround_x(a0));
            out.push(fround_x(a1));
            out.push(fround_x(a2));
            out.push(fround_x(a3));
            proof {
                assert forall|j: int|
                    0 <= j < out@.len() implies #[trigger] out@[j] == rhval(s, w as int, h as int, n as int, m@, st@, t@, ow as int, j) by {
                    if j >= before.len() {
                        let bb = (y * ow + o) * NC;
                        lemma_idx(y as int, o as int, j - bb, ow as int, h as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            o = o + 1;
        }
        proof {
            lemma_rows(y as int, ow as int, ow as int);
        }
        y = y + 1;
    }
    proof {
        assert(out@.len() == ow * h * NC) by (nonlinear_arith)
            requires
                out@.len() == h * ow * NC,
        ;
        assert(out@ =~= reduceh(s, w as int, h as int, n as int, m@, st@, t@, ow as int));
    }
    out
}


pub proof fn lemma_bsum_bound(v: spec_fn(int) -> int, st: int, s: int, n: int)
    requires
        0 <= n,
        forall|i: int| 0 <= #[trigger] v(i) <= 255,
    ensures
        0 <= bsum(v, st, s, n) <= 255 * n,
    decreases n,
{
    if n > 0 {
        lemma_bsum_bound(v, st, s, n - 1);
    }
}

/// `bavg`, for `k` values of at most 255.
pub fn bavg_x(sum: u64, k: u64, exact: bool) -> (r: u8)
    requires
        1 <= k <= MAX_DIM,
        sum <= 255 * k,
    ensures
        r == bavg(sum as int, k as int, exact) as u8,
{
    if exact {
        ((sum + k / 2) / k) as u8
    } else {
        fixavg_x(sum, k)
    }
}

pub proof fn lemma_cdiv(s: int, k: int)
    requires
        1 <= s <= MAX_DIM,
        1 <= k <= MAX_DIM,
    ensures
        1 <= cdiv(s, k) <= s,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(s + k - 1, k);
    assert(1 <= cdiv(s, k)) by (nonlinear_arith)
        requires
            1 <= k,
            1 <= s,
            k * cdiv(s, k) + (s + k - 1) % k == s + k - 1,
            0 <= (s + k - 1) % k < k,
    ;
    assert(cdiv(s, k) <= s) by (nonlinear_arith)
        requires
            1 <= k,
            1 <= s,
            k * cdiv(s, k) + (s + k - 1) % k == s + k - 1,
            0 <= (s + k - 1) % k,
    ;
}

/// The column shrink's value at index `j` of its output.
pub open spec fn svval(src: Seq<u8>, w: int, h: int, k: int, exact: bool, j: int) -> u8 {
    shrinkv(src, w, h, k, exact)[j]
}

/// `shrinkv`.
#[verifier::rlimit(60)]
pub fn shrinkv_x(src: &[u8], w: usize, h: usize, k: usize, exact: bool) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        1 <= k <= MAX_DIM,
        src@.len() == w * h * NC,
    ensures
        r@ == shrinkv(src@, w as int, h as int, k as int, exact),
        r@.len() == w * cdiv(h as int, k as int) * NC,
{
    let ghost s = src@;
    proof {
        lemma_cdiv(h as int, k as int);
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
        ;
    }
    let oh = (h + k - 1) / k;
    proof {
        assert(w * oh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= oh <= h <= MAX_DIM,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(w * oh * 4);
    let mut o: usize = 0;
    while o < oh
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            1 <= k <= MAX_DIM,
            oh == cdiv(h as int, k as int),
            1 <= oh <= h,
            s == src@,
            src@.len() == w * h * NC,
            o <= oh,
            out@.len() == o * w * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == svval(s, w as int, h as int, k as int, exact, j),
        decreases oh - o,
    {
        proof {
            assert(o * k <= 65535 * 65535) by (nonlinear_arith)
                requires
                    o < oh <= h <= MAX_DIM,
                    k <= MAX_DIM,
            ;
        }
        let s0 = (o * k) as i64;
        let mut x: usize = 0;
        while x < w
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                1 <= k <= MAX_DIM,
                oh == cdiv(h as int, k as int),
                1 <= oh <= h,
                s == src@,
                src@.len() == w * h * NC,
                o < oh,
                s0 == o * k,
                0 <= s0 <= 65535 * 65535,
                x <= w,
                out@.len() == o * w * NC + x * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == svval(s, w as int, h as int, k as int, exact, j),
            decreases w - x,
        {
            let mut a0: u64 = 0;
            let mut a1: u64 = 0;
            let mut a2: u64 = 0;
            let mut a3: u64 = 0;
            let mut i: usize = 0;
            while i < k
                invariant
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    1 <= k <= MAX_DIM,
                    s == src@,
                    src@.len() == w * h * NC,
                    0 <= s0 <= 65535 * 65535,
                    x < w,
                    i <= k,
                    a0 == bsum(col_line(s, w as int, x as int, 0), s0 as int, h as int, i as int),
                    a1 == bsum(col_line(s, w as int, x as int, 1), s0 as int, h as int, i as int),
                    a2 == bsum(col_line(s, w as int, x as int, 2), s0 as int, h as int, i as int),
                    a3 == bsum(col_line(s, w as int, x as int, 3), s0 as int, h as int, i as int),
                    a0 <= 255 * i && a1 <= 255 * i && a2 <= 255 * i && a3 <= 255 * i,
                decreases k - i,
            {
                let yy = kc_x(s0 + i as i64, h);
                proof {
                    lemma_idx(yy as int, x as int, 3, w as int, h as int);
                    lemma_idx(yy as int, x as int, 0, w as int, h as int);
                    assert((yy * w + x) * NC + 3 < w * h * NC && h * w <= 65535 * 65535) by (nonlinear_arith)
                        requires
                            0 <= yy * w + x < h * w,
                            1 <= w <= MAX_DIM,
                            1 <= h <= MAX_DIM,
                    ;
                }
                let p = (yy * w + x) * 4;
                proof {
                    assert(col_line(s, w as int, x as int, 0)(yy as int) == src@[p as int]);
                    assert(col_line(s, w as int, x as int, 1)(yy as int) == src@[p + 1]);
                    assert(col_line(s, w as int, x as int, 2)(yy as int) == src@[p + 2]);
                    assert(col_line(s, w as int, x as int, 3)(yy as int) == src@[p + 3]);
                }
                a0 = a0 + src[p] as u64;
                a1 = a1 + src[p + 1] as u64;
                a2 = a2 + src[p + 2] as u64;
                a3 = a3 + src[p + 3] as u64;
                i = i + 1;
            }
            proof {
                lemma_rows(o as int, w as int, x as int);
                lemma_rows(o as int, w as int, x as int + 1);
            }
            let ghost before = out@;
            out.push(bavg_x(a0, k as u64, exact));
            out.push(bavg_x(a1, k as u64, exact));
            out.push(bavg_x(a2, k as u64, exact));
            out.push(bavg_x(a3, k as u64, exact));
            proof {
                assert forall|j: int|
                    0 <= j < out@.len() implies #[trigger] out@[j] == svval(s, w as int, h as int, k as int, exact, j) by {
                    if j >= before.len() {
                        let bb = (o * w + x) * NC;
                        lemma_idx(o as int, x as int, j - bb, w as int, oh as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            x = x + 1;
        }
        proof {
            lemma_rows(o as int, w as int, w as int);
        }
        o = o + 1;
    }
    proof {
        assert(out@.len() == w * oh * NC) by (nonlinear_arith)
            requires
                out@.len() == oh * w * NC,
        ;
        assert(out@ =~= shrinkv(s, w as int, h as int, k as int, exact));
    }
    out
}

/// The row shrink's value at index `j` of its output.
pub open spec fn shval(src: Seq<u8>, w: int, h: int, k: int, exact: bool, j: int) -> u8 {
    shrinkh(src, w, h, k, exact)[j]
}

/// `shrinkh`.
#[verifier::rlimit(60)]
pub fn shrinkh_x(src: &[u8], w: usize, h: usize, k: usize, exact: bool) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        1 <= k <= MAX_DIM,
        src@.len() == w * h * NC,
    ensures
        r@ == shrinkh(src@, w as int, h as int, k as int, exact),
        r@.len() == cdiv(w as int, k as int) * h * NC,
{
    let ghost s = src@;
    proof {
        lemma_cdiv(w as int, k as int);
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
        ;
    }
    let ow = (w + k - 1) / k;
    proof {
        assert(ow * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= h <= MAX_DIM,
                1 <= ow <= w <= MAX_DIM,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(ow * h * 4);
    let mut y: usize = 0;
    while y < h
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            1 <= k <= MAX_DIM,
            ow == cdiv(w as int, k as int),
            1 <= ow <= w,
            s == src@,
            src@.len() == w * h * NC,
            y <= h,
            out@.len() == y * ow * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == shval(s, w as int, h as int, k as int, exact, j),
        decreases h - y,
    {
        let mut o: usize = 0;
        while o < ow
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                1 <= k <= MAX_DIM,
                ow == cdiv(w as int, k as int),
                1 <= ow <= w,
                s == src@,
                src@.len() == w * h * NC,
                y < h,
                o <= ow,
                out@.len() == y * ow * NC + o * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == shval(s, w as int, h as int, k as int, exact, j),
            decreases ow - o,
        {
            proof {
                assert(o * k <= 65535 * 65535) by (nonlinear_arith)
                    requires
                        o < ow <= w <= MAX_DIM,
                        k <= MAX_DIM,
                ;
            }
            let s0 = (o * k) as i64;
            let mut a0: u64 = 0;
            let mut a1: u64 = 0;
            let mut a2: u64 = 0;
            let mut a3: u64 = 0;
            let mut i: usize = 0;
            while i < k
                invariant
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    1 <= k <= MAX_DIM,
                    s == src@,
                    src@.len() == w * h * NC,
                    0 <= s0 <= 65535 * 65535,
                    s0 == o * k,
                    y < h,
                    i <= k,
                    a0 == bsum(src_line(s, w as int, y as int, 0), s0 as int, w as int, i as int),
                    a1 == bsum(src_line(s, w as int, y as int, 1), s0 as int, w as int, i as int),
                    a2 == bsum(src_line(s, w as int, y as int, 2), s0 as int, w as int, i as int),
                    a3 == bsum(src_line(s, w as int, y as int, 3), s0 as int, w as int, i as int),
                    a0 <= 255 * i && a1 <= 255 * i && a2 <= 255 * i && a3 <= 255 * i,
                decreases k - i,
            {
                let xx = kc_x(s0 + i as i64, w);
                proof {
                    lemma_idx(y as int, xx as int, 3, w as int, h as int);
                    lemma_idx(y as int, xx as int, 0, w as int, h as int);
                    assert((y * w + xx) * NC + 3 < w * h * NC && h * w <= 65535 * 65535) by (nonlinear_arith)
                        requires
                            0 <= y * w + xx < h * w,
                            1 <= w <= MAX_DIM,
                            1 <= h <= MAX_DIM,
                    ;
                }
                let p = (y * w + xx) * 4;
                proof {
                    assert(src_line(s, w as int, y as int, 0)(xx as int) == src@[p as int]);
                    assert(src_line(s, w as int, y as int, 1)(xx as int) == src@[p + 1]);
                    assert(src_line(s, w as int, y as int, 2)(xx as int) == src@[p + 2]);
                    assert(src_line(s, w as int, y as int, 3)(xx as int) == src@[p + 3]);
                }
                a0 = a0 + src[p] as u64;
                a1 = a1 + src[p + 1] as u64;
                a2 = a2 + src[p + 2] as u64;
                a3 = a3 + src[p + 3] as u64;
                i = i + 1;
            }
            proof {
                lemma_rows(y as int, ow as int, o as int);
                lemma_rows(y as int, ow as int, o as int + 1);
            }
            let ghost before = out@;
            out.push(bavg_x(a0, k as u64, exact));
            out.push(bavg_x(a1, k as u64, exact));
            out.push(bavg_x(a2, k as u64, exact));
            out.push(bavg_x(a3, k as u64, exact));
            proof {
                assert forall|j: int|
                    0 <= j < out@.len() implies #[trigger] out@[j] == shval(s, w as int, h as int, k as int, exact, j) by {
                    if j >= before.len() {
                        let bb = (y * ow + o) * NC;
                        lemma_idx(y as int, o as int, j - bb, ow as int, h as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            o = o + 1;
        }
        proof {
            lemma_rows(y as int, ow as int, ow as int);
        }
        y = y + 1;
    }
    proof {
        assert(out@.len() == ow * h * NC) by (nonlinear_arith)
            requires
                out@.len() == h * ow * NC,
        ;
        assert(out@ =~= shrinkh(s, w as int, h as int, k as int, exact));
    }
    out
}

/// The subsample's value at index `j` of its output.
pub open spec fn ssval(src: Seq<u8>, w: int, h: int, kx: int, ky: int, j: int) -> u8 {
    subsample(src, w, h, kx, ky)[j]
}

/// `subsample`.
#[verifier::rlimit(40)]
pub fn subsample_x(src: &[u8], w: usize, h: usize, kx: usize, ky: usize) -> (r: Vec<u8>)
    requires
        1 <= kx <= w <= MAX_DIM,
        1 <= ky <= h <= MAX_DIM,
        src@.len() == w * h * NC,
    ensures
        r@ == subsample(src@, w as int, h as int, kx as int, ky as int),
        r@.len() == (w as int / kx as int) * (h as int / ky as int) * NC,
{
    let ghost s = src@;
    let ow = w / kx;
    let oh = h / ky;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(w as int, kx as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(h as int, ky as int);
        assert(1 <= ow <= w && 1 <= oh <= h && ow * kx <= w && oh * ky <= h) by (nonlinear_arith)
            requires
                1 <= kx <= w,
                1 <= ky <= h,
                kx * ow + w % kx == w,
                ky * oh + h % ky == h,
                0 <= w % kx < kx,
                0 <= h % ky < ky,
        ;
        assert(ow * oh * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= ow <= w <= MAX_DIM,
                1 <= oh <= h <= MAX_DIM,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(ow * oh * 4);
    let mut y: usize = 0;
    while y < oh
        invariant
            1 <= kx <= w <= MAX_DIM,
            1 <= ky <= h <= MAX_DIM,
            ow == w / kx,
            oh == h / ky,
            1 <= ow <= w,
            1 <= oh <= h,
            ow * kx <= w,
            oh * ky <= h,
            s == src@,
            src@.len() == w * h * NC,
            y <= oh,
            out@.len() == y * ow * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == ssval(s, w as int, h as int, kx as int, ky as int, j),
        decreases oh - y,
    {
        let mut x: usize = 0;
        while x < ow
            invariant
                1 <= kx <= w <= MAX_DIM,
                1 <= ky <= h <= MAX_DIM,
                ow == w / kx,
                oh == h / ky,
                1 <= ow <= w,
                1 <= oh <= h,
                ow * kx <= w,
                oh * ky <= h,
                s == src@,
                src@.len() == w * h * NC,
                y < oh,
                x <= ow,
                out@.len() == y * ow * NC + x * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == ssval(s, w as int, h as int, kx as int, ky as int, j),
            decreases ow - x,
        {
            proof {
                assert(y * ky < h && x * kx < w) by (nonlinear_arith)
                    requires
                        y < oh,
                        x < ow,
                        ow * kx <= w,
                        oh * ky <= h,
                        1 <= kx,
                        1 <= ky,
                ;
            }
            let sy = y * ky;
            let sx = x * kx;
            proof {
                lemma_idx(sy as int, sx as int, 3, w as int, h as int);
                lemma_idx(sy as int, sx as int, 0, w as int, h as int);
                assert((sy * w + sx) * NC + 3 < w * h * NC && h * w <= 65535 * 65535) by (nonlinear_arith)
                    requires
                        0 <= sy * w + sx < h * w,
                        1 <= w <= MAX_DIM,
                        1 <= h <= MAX_DIM,
                ;
                lemma_rows(y as int, ow as int, x as int);
                lemma_rows(y as int, ow as int, x as int + 1);
            }
            let p = (sy * w + sx) * 4;
            let ghost before = out@;
            out.push(src[p]);
            out.push(src[p + 1]);
            out.push(src[p + 2]);
            out.push(src[p + 3]);
            proof {
                assert forall|j: int|
                    0 <= j < out@.len() implies #[trigger] out@[j] == ssval(s, w as int, h as int, kx as int, ky as int, j) by {
                    if j >= before.len() {
                        let bb = (y * ow + x) * NC;
                        lemma_idx(y as int, x as int, j - bb, ow as int, oh as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            x = x + 1;
        }
        proof {
            lemma_rows(y as int, ow as int, ow as int);
        }
        y = y + 1;
    }
    proof {
        assert(out@.len() == ow * oh * NC) by (nonlinear_arith)
            requires
                out@.len() == oh * ow * NC,
        ;
        assert(out@ =~= subsample(s, w as int, h as int, kx as int, ky as int));
    }
    out
}
} // verus!
