//! `blur`, `sharpen`'s step on the lightness, premultiplied alpha and pixelate, proven to compute
//! `spec_filter`'s for every table of weights up to 10001 entries of at
//! most 65536, every divisor up to 2^31, and every image up to 65535 by
//! 65535: no overflow, no out-of-bounds access.
use crate::lanczos::{kc_x, kdiv_x};
#[cfg(verus_only)]
use crate::resize::lemma_idx;
use crate::spec::*;
use crate::spec_filter::*;
use crate::spec_lanczos::*;
use vstd::prelude::*;

verus! {

/// The tables the proofs cover.
pub open spec fn gk_ok(g: Seq<u32>) -> bool {
    &&& 1 <= g.len() <= 10001
    &&& g.len() % 2 == 1
    &&& forall|j: int| 0 <= j < g.len() ==> #[trigger] g[j] <= 65536
}

/// The table as integers, as the specification takes it.
pub open spec fn gseq(g: Seq<u32>) -> Seq<int> {
    Seq::new(g.len(), |j: int| g[j] as int)
}

pub proof fn lemma_gsum_bound(v: spec_fn(int) -> int, g: Seq<int>, x: int, s: int, t: int, m: int)
    requires
        0 <= t <= g.len(),
        m >= 0,
        forall|j: int| 0 <= j < g.len() ==> 0 <= #[trigger] g[j] <= 65536,
        forall|i: int| 0 <= #[trigger] v(i) <= m,
    ensures
        0 <= gsum(v, g, x, s, t) <= t * 65536 * m,
    decreases t,
{
    if t > 0 {
        lemma_gsum_bound(v, g, x, s, t - 1, m);
        let a = g[t - 1];
        let b = v(kc(x + (t - 1) - gr(g), s));
        assert(0 <= a * b <= 65536 * m) by (nonlinear_arith)
            requires
                0 <= a <= 65536,
                0 <= b <= m,
        ;
        assert((t - 1) * 65536 * m + 65536 * m == t * 65536 * m) by (nonlinear_arith);
    }
}

/// The row pass's value at index `k` of its output.
pub open spec fn ghval(g: Seq<int>, d: int, src: Seq<u8>, w: int, k: int) -> int {
    ghpx(g, d, src, w, (k / NC) / w, (k / NC) % w, k % NC)
}

/// The row pass: `w * h * 4` values, `ghpx` of each pixel and channel.
pub fn grows(g: &[u32], d: i64, src: &[u8], w: usize, h: usize) -> (r: Vec<u8>)
    requires
        gk_ok(g@),
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        w * h * NC <= 65535 * 65535 * 4,
        src@.len() == w * h * NC,
        1 <= d <= 0x8000_0000,
    ensures
        r@.len() == w * h * NC,
        forall|y: int, x: int, c: int|
            0 <= y < h && 0 <= x < w && 0 <= c < NC ==> #[trigger] r@[(y * w + x) * NC + c] == ghpx(
                gseq(g@),
                d as int,
                src@,
                w as int,
                y,
                x,
                c,
            ),
{
    let ghost s = src@;
    let ghost k = gseq(g@);
    let n = g.len();
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                w * h * NC <= 65535 * 65535 * 4,
        ;
    }
    let rad = ((n - 1) / 2) as i64;
    let mut out: Vec<u8> = Vec::with_capacity(w * h * 4);
    let mut y: usize = 0;
    while y < h
        invariant
            gk_ok(g@),
            k == gseq(g@),
            n == g@.len(),
            rad == gr(k),
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            w * h * NC <= 65535 * 65535 * 4,
            s == src@,
            src@.len() == w * h * NC,
            1 <= d <= 0x8000_0000,
            y <= h,
            out@.len() == y * w * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == ghval(k, d as int, s, w as int, j),
        decreases h - y,
    {
        let mut x: usize = 0;
        while x < w
            invariant
                gk_ok(g@),
                k == gseq(g@),
                n == g@.len(),
                rad == gr(k),
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                w * h * NC <= 65535 * 65535 * 4,
                s == src@,
                src@.len() == w * h * NC,
                1 <= d <= 0x8000_0000,
                y < h,
                x <= w,
                out@.len() == (y * w + x) * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == ghval(k, d as int, s, w as int, j),
            decreases w - x,
        {
            let mut a0: i64 = 0;
            let mut a1: i64 = 0;
            let mut a2: i64 = 0;
            let mut a3: i64 = 0;
            let mut t: usize = 0;
            while t < n
                invariant
                    gk_ok(g@),
                    k == gseq(g@),
                    n == g@.len(),
                    rad == gr(k),
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    w * h * NC <= 65535 * 65535 * 4,
                    s == src@,
                    src@.len() == w * h * NC,
                    y < h,
                    x < w,
                    t <= n,
                    a0 == gsum(src_line(s, w as int, y as int, 0), k, x as int, w as int, t as int),
                    a1 == gsum(src_line(s, w as int, y as int, 1), k, x as int, w as int, t as int),
                    a2 == gsum(src_line(s, w as int, y as int, 2), k, x as int, w as int, t as int),
                    a3 == gsum(src_line(s, w as int, y as int, 3), k, x as int, w as int, t as int),
                    0 <= a0 <= t * 16711680,
                    0 <= a1 <= t * 16711680,
                    0 <= a2 <= t * 16711680,
                    0 <= a3 <= t * 16711680,
                decreases n - t,
            {
                let i = x as i64 + t as i64 - rad;
                let ci = kc_x(i, w);
                let wt = g[t] as i64;
                proof {
                    lemma_idx(y as int, ci as int, 3, w as int, h as int);
                    lemma_idx(y as int, ci as int, 0, w as int, h as int);
                }
                let p = (y * w + ci) * 4;
                let v0 = src[p] as i64;
                let v1 = src[p + 1] as i64;
                let v2 = src[p + 2] as i64;
                let v3 = src[p + 3] as i64;
                proof {
                    assert(0 <= wt * v0 <= 16711680 && 0 <= wt * v1 <= 16711680 && 0 <= wt * v2 <= 16711680 && 0
                        <= wt * v3 <= 16711680) by (nonlinear_arith)
                        requires
                            0 <= wt <= 65536,
                            0 <= v0 <= 255,
                            0 <= v1 <= 255,
                            0 <= v2 <= 255,
                            0 <= v3 <= 255,
                    ;
                    assert((t + 1) * 16711680 == t * 16711680 + 16711680) by (nonlinear_arith);
                    assert(src_line(s, w as int, y as int, 0)(ci as int) == v0);
                    assert(src_line(s, w as int, y as int, 1)(ci as int) == v1);
                    assert(src_line(s, w as int, y as int, 2)(ci as int) == v2);
                    assert(src_line(s, w as int, y as int, 3)(ci as int) == v3);
                    assert(k[t as int] == wt);
                }
                a0 = a0 + wt * v0;
                a1 = a1 + wt * v1;
                a2 = a2 + wt * v2;
                a3 = a3 + wt * v3;
                t = t + 1;
            }
            proof {
                assert(t * 16711680 <= 10001 * 16711680) by (nonlinear_arith)
                    requires
                        t <= 10001,
                ;
                lemma_idx(y as int, x as int, 3, w as int, h as int);
            }
            let q0 = kdiv_x(a0, d, 1) as u8;
            let q1 = kdiv_x(a1, d, 1) as u8;
            let q2 = kdiv_x(a2, d, 1) as u8;
            let q3 = kdiv_x(a3, d, 1) as u8;
            let ghost before = out@;
            out.push(q0);
            out.push(q1);
            out.push(q2);
            out.push(q3);
            proof {
                assert((y * w + x + 1) * NC == (y * w + x) * NC + 4) by (nonlinear_arith);
                assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == ghval(k, d as int, s, w as int, j) by {
                    if j >= before.len() {
                        let b = (y * w + x) * NC;
                        lemma_idx(y as int, x as int, j - b, w as int, h as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            x = x + 1;
        }
        proof {
            assert((y * w + w) * NC == (y + 1) * w * NC) by (nonlinear_arith);
        }
        y = y + 1;
    }
    proof {
        assert(out@.len() == w * h * NC) by (nonlinear_arith)
            requires
                out@.len() == h * w * NC,
        ;
        assert forall|y: int, x: int, c: int|
            0 <= y < h && 0 <= x < w && 0 <= c < NC implies #[trigger] out@[(y * w + x) * NC + c] == ghpx(
                k,
                d as int,
                src@,
                w as int,
                y,
                x,
                c,
            ) by {
            lemma_idx(y, x, c, w as int, h as int);
        }
    }
    out
}

/// The blurred value at index `k`.
pub open spec fn goval(g: Seq<int>, d: int, src: Seq<u8>, w: int, h: int, k: int) -> u8 {
    gopx(g, d, src, w, h, (k / NC) / w, (k / NC) % w, k % NC)
}

/// The column pass over the row pass's values `mid`: the blurred image.
#[verifier::rlimit(40)]
pub fn gcols(g: &[u32], d: i64, mid: &[u8], Ghost(src): Ghost<Seq<u8>>, w: usize, h: usize) -> (r: Vec<u8>)
    requires
        gk_ok(g@),
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        w * h * NC <= 65535 * 65535 * 4,
        src.len() == w * h * NC,
        mid@.len() == w * h * NC,
        forall|y: int, x: int, c: int|
            0 <= y < h && 0 <= x < w && 0 <= c < NC ==> #[trigger] mid@[(y * w + x) * NC + c] == ghpx(
                gseq(g@),
                d as int,
                src,
                w as int,
                y,
                x,
                c,
            ),
        1 <= d <= 0x8000_0000,
    ensures
        r@ == blur(gseq(g@), d as int, src, w as int, h as int),
{
    let ghost k = gseq(g@);
    let n = g.len();
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                w * h * NC <= 65535 * 65535 * 4,
        ;
    }
    let rad = ((n - 1) / 2) as i64;
    let mut out: Vec<u8> = Vec::with_capacity(w * h * 4);
    let mut y: usize = 0;
    while y < h
        invariant
            gk_ok(g@),
            k == gseq(g@),
            n == g@.len(),
            rad == gr(k),
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            w * h * NC <= 65535 * 65535 * 4,
            src.len() == w * h * NC,
            mid@.len() == w * h * NC,
            forall|y: int, x: int, c: int|
                0 <= y < h && 0 <= x < w && 0 <= c < NC ==> #[trigger] mid@[(y * w + x) * NC + c] == ghpx(
                    k,
                    d as int,
                    src,
                    w as int,
                    y,
                    x,
                    c,
                ),
            1 <= d <= 0x8000_0000,
            y <= h,
            out@.len() == y * w * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == goval(k, d as int, src, w as int, h as int, j),
        decreases h - y,
    {
        let mut x: usize = 0;
        while x < w
            invariant
                gk_ok(g@),
                k == gseq(g@),
                n == g@.len(),
                rad == gr(k),
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                w * h * NC <= 65535 * 65535 * 4,
                src.len() == w * h * NC,
                mid@.len() == w * h * NC,
                forall|y: int, x: int, c: int|
                    0 <= y < h && 0 <= x < w && 0 <= c < NC ==> #[trigger] mid@[(y * w + x) * NC + c] == ghpx(
                        k,
                        d as int,
                        src,
                        w as int,
                        y,
                        x,
                        c,
                    ),
                1 <= d <= 0x8000_0000,
                y < h,
                x <= w,
                out@.len() == (y * w + x) * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == goval(k, d as int, src, w as int, h as int, j),
            decreases w - x,
        {
            let mut a0: i64 = 0;
            let mut a1: i64 = 0;
            let mut a2: i64 = 0;
            let mut a3: i64 = 0;
            let mut t: usize = 0;
            while t < n
                invariant
                    gk_ok(g@),
                    k == gseq(g@),
                    n == g@.len(),
                    rad == gr(k),
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    w * h * NC <= 65535 * 65535 * 4,
                    src.len() == w * h * NC,
                    mid@.len() == w * h * NC,
                    forall|y: int, x: int, c: int|
                        0 <= y < h && 0 <= x < w && 0 <= c < NC ==> #[trigger] mid@[(y * w + x) * NC + c] == ghpx(
                            k,
                            d as int,
                            src,
                            w as int,
                            y,
                            x,
                            c,
                        ),
                    y < h,
                    x < w,
                    t <= n,
                    a0 == gsum(gmid_line(k, d as int, src, w as int, x as int, 0), k, y as int, h as int, t as int),
                    a1 == gsum(gmid_line(k, d as int, src, w as int, x as int, 1), k, y as int, h as int, t as int),
                    a2 == gsum(gmid_line(k, d as int, src, w as int, x as int, 2), k, y as int, h as int, t as int),
                    a3 == gsum(gmid_line(k, d as int, src, w as int, x as int, 3), k, y as int, h as int, t as int),
                    0 <= a0 <= t * 16711680,
                    0 <= a1 <= t * 16711680,
                    0 <= a2 <= t * 16711680,
                    0 <= a3 <= t * 16711680,
                decreases n - t,
            {
                let i = y as i64 + t as i64 - rad;
                let cj = kc_x(i, h);
                let wt = g[t] as i64;
                proof {
                    lemma_idx(cj as int, x as int, 3, w as int, h as int);
                    lemma_idx(cj as int, x as int, 0, w as int, h as int);
                    lemma_idx(cj as int, x as int, 1, w as int, h as int);
                    lemma_idx(cj as int, x as int, 2, w as int, h as int);
                }
                let p = (cj * w + x) * 4;
                let v0 = mid[p] as i64;
                let v1 = mid[p + 1] as i64;
                let v2 = mid[p + 2] as i64;
                let v3 = mid[p + 3] as i64;
                proof {
                    assert(mid@[(cj * w + x) * NC + 0] == ghpx(k, d as int, src, w as int, cj as int, x as int, 0));
                    assert(mid@[(cj * w + x) * NC + 1] == ghpx(k, d as int, src, w as int, cj as int, x as int, 1));
                    assert(mid@[(cj * w + x) * NC + 2] == ghpx(k, d as int, src, w as int, cj as int, x as int, 2));
                    assert(mid@[(cj * w + x) * NC + 3] == ghpx(k, d as int, src, w as int, cj as int, x as int, 3));
                    assert(gmid_line(k, d as int, src, w as int, x as int, 0)(cj as int) == v0);
                    assert(gmid_line(k, d as int, src, w as int, x as int, 1)(cj as int) == v1);
                    assert(gmid_line(k, d as int, src, w as int, x as int, 2)(cj as int) == v2);
                    assert(gmid_line(k, d as int, src, w as int, x as int, 3)(cj as int) == v3);
                    assert(0 <= wt * v0 <= 16711680 && 0 <= wt * v1 <= 16711680 && 0 <= wt * v2 <= 16711680
                        && 0 <= wt * v3 <= 16711680) by (nonlinear_arith)
                        requires
                            0 <= wt <= 65536,
                            0 <= v0 <= 255,
                            0 <= v1 <= 255,
                            0 <= v2 <= 255,
                            0 <= v3 <= 255,
                    ;
                    assert((t + 1) * 16711680 == t * 16711680 + 16711680) by (nonlinear_arith);
                    assert(k[t as int] == wt);
                }
                a0 = a0 + wt * v0;
                a1 = a1 + wt * v1;
                a2 = a2 + wt * v2;
                a3 = a3 + wt * v3;
                t = t + 1;
            }
            proof {
                assert(t * 16711680 <= 10001 * 16711680) by (nonlinear_arith)
                    requires
                        t <= 10001,
                ;
                lemma_idx(y as int, x as int, 3, w as int, h as int);
            }
            let q0 = kdiv_x(a0, d, 1) as u8;
            let q1 = kdiv_x(a1, d, 1) as u8;
            let q2 = kdiv_x(a2, d, 1) as u8;
            let q3 = kdiv_x(a3, d, 1) as u8;
            let ghost before = out@;
            out.push(q0);
            out.push(q1);
            out.push(q2);
            out.push(q3);
            proof {
                assert((y * w + x + 1) * NC == (y * w + x) * NC + 4) by (nonlinear_arith);
                assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == goval(
                    k,
                    d as int,
                    src,
                    w as int,
                    h as int,
                    j,
                ) by {
                    if j >= before.len() {
                        let b = (y * w + x) * NC;
                        lemma_idx(y as int, x as int, j - b, w as int, h as int);
                    } else {
                        assert(out@[j] == before[j]);
                    }
                }
            }
            x = x + 1;
        }
        proof {
            assert((y * w + w) * NC == (y + 1) * w * NC) by (nonlinear_arith);
        }
        y = y + 1;
    }
    proof {
        assert(out@.len() == w * h * NC) by (nonlinear_arith)
            requires
                out@.len() == h * w * NC,
        ;
        assert(out@ =~= blur(k, d as int, src, w as int, h as int));
    }
    out
}

/// `blur`: `src` (`w` by `h` RGBA) blurred with the table `g`.
pub fn blur_rgba(g: &[u32], d: i64, src: &[u8], w: usize, h: usize) -> (r: Vec<u8>)
    requires
        gk_ok(g@),
        1 <= d <= 0x8000_0000,
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        src@.len() == w * h * NC,
    ensures
        r@ == blur(gseq(g@), d as int, src@, w as int, h as int),
{
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
        ;
    }
    let mid = grows(g, d, src, w, h);
    gcols(g, d, mid.as_slice(), Ghost(src@), w, h)
}

/// `sdiv`, for a non-negative sum.
pub fn sdiv_x(n: i64, d: i64) -> (r: u16)
    requires
        0 <= n <= 0x10_0000_0000_0000,
        1 <= d <= 0x8000_0000,
    ensures
        r as int == sdiv(n as int, d as int),
{
    let q = (n + d / 2) / d;
    if q > 32767 {
        32767
    } else {
        q as u16
    }
}

/// The row pass of the blur of the one-channel `l`.
#[verifier::rlimit(30)]
pub fn lrows(g: &[u32], d: i64, l: &[u16], w: usize, h: usize) -> (r: Vec<u16>)
    requires
        gk_ok(g@),
        1 <= d <= 0x8000_0000,
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        l@.len() == w * h,
    ensures
        r@.len() == w * h,
        forall|y: int, x: int|
            0 <= y < h && 0 <= x < w ==> #[trigger] r@[y * w + x] == lhpx(gseq(g@), d as int, l@, w as int, y, x),
{
    let ghost k = gseq(g@);
    let n = g.len();
    let rad = ((n - 1) / 2) as i64;
    proof {
        assert(w * h <= 65535 * 65535) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
        ;
    }
    let mut out: Vec<u16> = Vec::with_capacity(w * h);
    let mut y: usize = 0;
    while y < h
        invariant
            gk_ok(g@),
            k == gseq(g@),
            n == g@.len(),
            rad == gr(k),
            1 <= d <= 0x8000_0000,
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            l@.len() == w * h,
            w * h <= 65535 * 65535,
            y <= h,
            out@.len() == y * w,
            forall|yy: int, xx: int|
                0 <= yy < h && 0 <= xx < w && yy * w + xx < out@.len() ==> #[trigger] out@[yy * w + xx] == lhpx(
                    k,
                    d as int,
                    l@,
                    w as int,
                    yy,
                    xx,
                ),
        decreases h - y,
    {
        let mut x: usize = 0;
        while x < w
            invariant
                gk_ok(g@),
                k == gseq(g@),
                n == g@.len(),
                rad == gr(k),
                1 <= d <= 0x8000_0000,
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                l@.len() == w * h,
                w * h <= 65535 * 65535,
                y < h,
                x <= w,
                out@.len() == y * w + x,
                forall|yy: int, xx: int|
                    0 <= yy < h && 0 <= xx < w && yy * w + xx < out@.len() ==> #[trigger] out@[yy * w + xx] == lhpx(
                        k,
                        d as int,
                        l@,
                        w as int,
                        yy,
                        xx,
                    ),
            decreases w - x,
        {
            let mut a: i64 = 0;
            let mut t: usize = 0;
            while t < n
                invariant
                    gk_ok(g@),
                    k == gseq(g@),
                    n == g@.len(),
                    rad == gr(k),
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    l@.len() == w * h,
                    w * h <= 65535 * 65535,
                    y < h,
                    x < w,
                    t <= n,
                    a == gsum(l_line(l@, w as int, y as int), k, x as int, w as int, t as int),
                    0 <= a <= t * 0xFFFF_0000,
                decreases n - t,
            {
                let i = x as i64 + t as i64 - rad;
                let ci = kc_x(i, w);
                let wt = g[t] as i64;
                proof {
                    assert(y * w + ci < w * h) by (nonlinear_arith)
                        requires
                            y < h,
                            ci < w,
                    ;
                }
                let v = l[y * w + ci] as i64;
                proof {
                    assert(0 <= wt * v <= 0xFFFF_0000) by (nonlinear_arith)
                        requires
                            0 <= wt <= 65536,
                            0 <= v <= 65535,
                    ;
                    assert((t + 1) * 0xFFFF_0000 == t * 0xFFFF_0000 + 0xFFFF_0000) by (nonlinear_arith);
                    assert(l_line(l@, w as int, y as int)(ci as int) == v);
                    assert(k[t as int] == wt);
                }
                a = a + wt * v;
                t = t + 1;
            }
            proof {
                assert(t * 0xFFFF_0000 <= 10001 * 0xFFFF_0000) by (nonlinear_arith)
                    requires
                        t <= 10001,
                ;
            }
            let q = sdiv_x(a, d);
            let ghost before = out@;
            out.push(q);
            proof {
                assert forall|yy: int, xx: int|
                    0 <= yy < h && 0 <= xx < w && yy * w + xx < out@.len() implies #[trigger] out@[yy * w + xx] == lhpx(
                        k,
                        d as int,
                        l@,
                        w as int,
                        yy,
                        xx,
                    ) by {
                    if yy * w + xx == y * w + x {
                        lemma_same_pixel(yy, xx, y as int, x as int, w as int);
                    } else {
                        assert(out@[yy * w + xx] == before[yy * w + xx]);
                    }
                }
            }
            x = x + 1;
        }
        proof {
            assert(y * w + w == (y + 1) * w) by (nonlinear_arith);
        }
        y = y + 1;
    }
    proof {
        assert(out@.len() == w * h) by (nonlinear_arith)
            requires
                out@.len() == h * w,
        ;
        assert forall|y: int, x: int| 0 <= y < h && 0 <= x < w implies #[trigger] out@[y * w + x] == lhpx(
            k,
            d as int,
            l@,
            w as int,
            y,
            x,
        ) by {
            assert(y * w + x < w * h) by (nonlinear_arith)
                requires
                    y < h,
                    x < w,
            ;
        }
    }
    out
}

/// One pixel index names one pixel.
pub proof fn lemma_same_pixel(y1: int, x1: int, y2: int, x2: int, w: int)
    requires
        0 <= x1 < w,
        0 <= x2 < w,
        0 <= y1,
        0 <= y2,
        y1 * w + x1 == y2 * w + x2,
    ensures
        y1 == y2,
        x1 == x2,
{
    assert(y1 == y2 && x1 == x2) by (nonlinear_arith)
        requires
            0 <= x1 < w,
            0 <= x2 < w,
            0 <= y1,
            0 <= y2,
            y1 * w + x1 == y2 * w + x2,
    ;
}

/// The column pass over `mid`, `lrows`'s output.
#[verifier::rlimit(30)]
pub fn lcols(g: &[u32], d: i64, mid: &[u16], Ghost(l): Ghost<Seq<u16>>, w: usize, h: usize) -> (r: Vec<u16>)
    requires
        gk_ok(g@),
        1 <= d <= 0x8000_0000,
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        l.len() == w * h,
        mid@.len() == w * h,
        forall|y: int, x: int|
            0 <= y < h && 0 <= x < w ==> #[trigger] mid@[y * w + x] == lhpx(gseq(g@), d as int, l, w as int, y, x),
    ensures
        r@.len() == w * h,
        forall|y: int, x: int|
            0 <= y < h && 0 <= x < w ==> #[trigger] r@[y * w + x] == lopx(gseq(g@), d as int, l, w as int, h as int, y, x),
{
    let ghost k = gseq(g@);
    let n = g.len();
    let rad = ((n - 1) / 2) as i64;
    proof {
        assert(w * h <= 65535 * 65535) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
        ;
    }
    let mut out: Vec<u16> = Vec::with_capacity(w * h);
    let mut y: usize = 0;
    while y < h
        invariant
            gk_ok(g@),
            k == gseq(g@),
            n == g@.len(),
            rad == gr(k),
            1 <= d <= 0x8000_0000,
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            l.len() == w * h,
            mid@.len() == w * h,
            w * h <= 65535 * 65535,
            forall|y: int, x: int|
                0 <= y < h && 0 <= x < w ==> #[trigger] mid@[y * w + x] == lhpx(k, d as int, l, w as int, y, x),
            y <= h,
            out@.len() == y * w,
            forall|yy: int, x: int|
                0 <= yy < h && 0 <= x < w && yy * w + x < out@.len() ==> #[trigger] out@[yy * w + x] == lopx(
                    k,
                    d as int,
                    l,
                    w as int,
                    h as int,
                    yy,
                    x,
                ),
        decreases h - y,
    {
        let mut x: usize = 0;
        while x < w
            invariant
                gk_ok(g@),
                k == gseq(g@),
                n == g@.len(),
                rad == gr(k),
                1 <= d <= 0x8000_0000,
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                l.len() == w * h,
                mid@.len() == w * h,
                w * h <= 65535 * 65535,
                forall|y: int, x: int|
                    0 <= y < h && 0 <= x < w ==> #[trigger] mid@[y * w + x] == lhpx(k, d as int, l, w as int, y, x),
                y < h,
                x <= w,
                out@.len() == y * w + x,
                forall|yy: int, xx: int|
                    0 <= yy < h && 0 <= xx < w && yy * w + xx < out@.len() ==> #[trigger] out@[yy * w + xx] == lopx(
                        k,
                        d as int,
                        l,
                        w as int,
                        h as int,
                        yy,
                        xx,
                    ),
            decreases w - x,
        {
            let mut a: i64 = 0;
            let mut t: usize = 0;
            while t < n
                invariant
                    gk_ok(g@),
                    k == gseq(g@),
                    n == g@.len(),
                    rad == gr(k),
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    mid@.len() == w * h,
                    w * h <= 65535 * 65535,
                    forall|y: int, x: int|
                        0 <= y < h && 0 <= x < w ==> #[trigger] mid@[y * w + x] == lhpx(k, d as int, l, w as int, y, x),
                    y < h,
                    x < w,
                    t <= n,
                    a == gsum(lmid_line(k, d as int, l, w as int, x as int), k, y as int, h as int, t as int),
                    0 <= a <= t * 0xFFFF_0000,
                decreases n - t,
            {
                let i = y as i64 + t as i64 - rad;
                let cj = kc_x(i, h);
                let wt = g[t] as i64;
                proof {
                    assert(cj * w + x < w * h) by (nonlinear_arith)
                        requires
                            cj < h,
                            x < w,
                    ;
                }
                let v = mid[cj * w + x] as i64;
                proof {
                    assert(mid@[cj * w + x] == lhpx(k, d as int, l, w as int, cj as int, x as int));
                    assert(lmid_line(k, d as int, l, w as int, x as int)(cj as int) == v);
                    assert(0 <= wt * v <= 0xFFFF_0000) by (nonlinear_arith)
                        requires
                            0 <= wt <= 65536,
                            0 <= v <= 65535,
                    ;
                    assert((t + 1) * 0xFFFF_0000 == t * 0xFFFF_0000 + 0xFFFF_0000) by (nonlinear_arith);
                    assert(k[t as int] == wt);
                }
                a = a + wt * v;
                t = t + 1;
            }
            proof {
                assert(t * 0xFFFF_0000 <= 10001 * 0xFFFF_0000) by (nonlinear_arith)
                    requires
                        t <= 10001,
                ;
            }
            let q = sdiv_x(a, d);
            let ghost before = out@;
            out.push(q);
            proof {
                assert forall|yy: int, xx: int|
                    0 <= yy < h && 0 <= xx < w && yy * w + xx < out@.len() implies #[trigger] out@[yy * w + xx] == lopx(
                        k,
                        d as int,
                        l,
                        w as int,
                        h as int,
                        yy,
                        xx,
                    ) by {
                    if yy * w + xx == y * w + x {
                        lemma_same_pixel(yy, xx, y as int, x as int, w as int);
                    } else {
                        assert(out@[yy * w + xx] == before[yy * w + xx]);
                    }
                }
            }
            x = x + 1;
        }
        proof {
            assert(y * w + w == (y + 1) * w) by (nonlinear_arith);
        }
        y = y + 1;
    }
    proof {
        assert(out@.len() == w * h) by (nonlinear_arith)
            requires
                out@.len() == h * w,
        ;
        assert forall|y: int, x: int| 0 <= y < h && 0 <= x < w implies #[trigger] out@[y * w + x] == lopx(
            k,
            d as int,
            l,
            w as int,
            h as int,
            y,
            x,
        ) by {
            assert(y * w + x < w * h) by (nonlinear_arith)
                requires
                    y < h,
                    x < w,
            ;
        }
    }
    out
}

/// `sharpen_l`: `vips_sharpen`'s step on the lightness `l`.
pub fn sharpen_l_x(g: &[u32], d: i64, lut: &[i16], l: &[u16], w: usize, h: usize) -> (r: Vec<u16>)
    requires
        gk_ok(g@),
        1 <= d <= 0x8000_0000,
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        l@.len() == w * h,
        lut@.len() == 65536,
        forall|i: int| 0 <= i < l@.len() ==> #[trigger] l@[i] <= 32767,
    ensures
        r@ == sharpen_l(gseq(g@), d as int, Seq::new(65536, |i: int| lut@[i] as int), l@, w as int, h as int),
{
    let ghost lt = Seq::new(65536, |i: int| lut@[i] as int);
    let mid = lrows(g, d, l, w, h);
    let b = lcols(g, d, &mid, Ghost(l@), w, h);
    proof {
        assert(w * h <= 65535 * 65535) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
        ;
    }
    let n = w * h;
    let mut out: Vec<u16> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == w * h,
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            l@.len() == n,
            b@.len() == n,
            lut@.len() == 65536,
            lt == Seq::new(65536, |i: int| lut@[i] as int),
            forall|i: int| 0 <= i < l@.len() ==> #[trigger] l@[i] <= 32767,
            forall|y: int, x: int|
                0 <= y < h && 0 <= x < w ==> #[trigger] b@[y * w + x] == lopx(gseq(g@), d as int, l@, w as int, h as int, y, x),
            i <= n,
            out@.len() == i,
            forall|j: int|
                0 <= j < i ==> #[trigger] out@[j] == sharpen_l(gseq(g@), d as int, lt, l@, w as int, h as int)[j],
        decreases n - i,
    {
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, w as int);
            assert((i as int) / (w as int) < h) by (nonlinear_arith)
                requires
                    i < w * h,
                    i == w * (i / w) + i % w,
                    0 <= i % w,
                    w >= 1,
            ;
            assert((i / w) * w + i % w == i) by (nonlinear_arith)
                requires
                    i == w * (i / w) + i % w,
            ;
            assert(b@[(i / w) * w + i % w] == lopx(gseq(g@), d as int, l@, w as int, h as int, (i as int) / (w as int), (i as int) % (w as int)));
        }
        let v1 = l[i] as i32;
        let v2 = b[i] as i32;
        let o = v1 + lut[(v1 - v2 + 32768) as usize] as i32;
        let v = if o < 0 {
            0
        } else if o > 32767 {
            32767
        } else {
            o as u16
        };
        out.push(v);
        i = i + 1;
    }
    proof {
        assert(out@ =~= sharpen_l(gseq(g@), d as int, lt, l@, w as int, h as int));
    }
    out
}

// ---------------------------------------------------------------------------
// premultiplied alpha
// ---------------------------------------------------------------------------

/// `premultiply`: colour channels scaled by alpha.
pub fn premul_rgba(src: &[u8]) -> (r: Vec<u8>)
    requires
        src@.len() % 4 == 0,
    ensures
        r@ == premultiply(src@),
{
    let n = src.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == src@.len(),
            n % 4 == 0,
            i <= n,
            i % 4 == 0,
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == premultiply(src@)[j],
        decreases n - i,
    {
        let a = src[i + 3] as u32;
        proof {
            assert(src[i as int] as u32 * a / 255 <= 255) by (nonlinear_arith)
                requires
                    src[i as int] <= 255,
                    a <= 255,
            ;
            assert(src[i as int + 1] as u32 * a / 255 <= 255) by (nonlinear_arith)
                requires
                    src[i as int + 1] <= 255,
                    a <= 255,
            ;
            assert(src[i as int + 2] as u32 * a / 255 <= 255) by (nonlinear_arith)
                requires
                    src[i as int + 2] <= 255,
                    a <= 255,
            ;
        }
        let ghost before = out@;
        out.push((src[i] as u32 * a / 255) as u8);
        out.push((src[i + 1] as u32 * a / 255) as u8);
        out.push((src[i + 2] as u32 * a / 255) as u8);
        out.push(src[i + 3]);
        proof {
            assert forall|j: int| 0 <= j < i + 4 implies #[trigger] out@[j] == premultiply(src@)[j] by {
                if j >= i {
                    assert(j % 4 == j - i && j - j % 4 + 3 == i + 3);
                } else {
                    assert(out@[j] == before[j]);
                }
            }
        }
        i = i + 4;
    }
    proof {
        assert(out@ =~= premultiply(src@));
    }
    out
}

/// `up_low`.
pub fn up_low_x(v: u8, a: u8) -> (r: bool)
    ensures
        r == up_low(v as int, a as int),
{
    (v == a && (a == 7 || a == 14 || a == 28 || a == 41 || a == 56 || a == 63 || a == 82 || a == 91 || a == 101 || a == 112 || a == 113 || a == 119 || a == 123 || a == 126 || a == 163 || a == 164 || a == 182 || a == 191 || a == 197 || a == 202 || a == 207 || a == 209 || a == 223 || a == 224 || a == 226 || a == 229 || a == 233 || a == 237 || a == 238 || a == 239 || a == 246 || a == 252)) || (a == 237 && (v == 79 || v == 158))
}

/// `up`.
pub fn up_x(v: u8, a: u8) -> (r: u8)
    ensures
        r as int == up(v as int, a as int),
{
    if a == 0 {
        return 0;
    }
    let q = v as u32 * 255 / a as u32;
    let low = up_low_x(v, a);
    proof {
        if low {
            if v == a {
                assert((v as int) * 255 / (a as int) >= 1) by (nonlinear_arith)
                    requires
                        v == a,
                        a >= 1,
                ;
            } else {
                assert(79u32 * 255 / 237 == 85) by (compute);
                assert(158u32 * 255 / 237 == 170) by (compute);
            }
        }
    }
    let e = if low { q - 1 } else { q };
    if e > 255 {
        255
    } else {
        e as u8
    }
}

/// `unpremultiply`.
pub fn unpremul_rgba(src: &[u8]) -> (r: Vec<u8>)
    requires
        src@.len() % 4 == 0,
    ensures
        r@ == unpremultiply(src@),
{
    let n = src.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == src@.len(),
            n % 4 == 0,
            i <= n,
            i % 4 == 0,
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == unpremultiply(src@)[j],
        decreases n - i,
    {
        let a = src[i + 3];
        let ghost before = out@;
        out.push(up_x(src[i], a));
        out.push(up_x(src[i + 1], a));
        out.push(up_x(src[i + 2], a));
        out.push(a);
        proof {
            assert forall|j: int| 0 <= j < i + 4 implies #[trigger] out@[j] == unpremultiply(src@)[j] by {
                if j >= i {
                    assert(j % 4 == j - i && j - j % 4 + 3 == i + 3);
                } else {
                    assert(out@[j] == before[j]);
                }
            }
        }
        i = i + 4;
    }
    proof {
        assert(out@ =~= unpremultiply(src@));
    }
    out
}

// ---------------------------------------------------------------------------
// pixelate
// ---------------------------------------------------------------------------

/// `mir`.
pub fn mir_x(i: usize, s: usize) -> (r: usize)
    requires
        1 <= s <= MAX_DIM,
    ensures
        r == mir(i as int, s as int),
        r < s,
{
    let m = i % (2 * s);
    if m < s {
        m
    } else {
        2 * s - 1 - m
    }
}

/// `fixavg`, for `n` values of at most 255.
pub fn fixavg_x(sum: u64, n: u64) -> (r: u8)
    requires
        1 <= n <= MAX_DIM,
        sum <= 255 * n,
    ensures
        r as int == fixavg(sum as int, n as int),
{
    let m = 0x100_0000u64 / n;
    proof {
        let ni = n as int;
        let mi = m as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(0x100_0000int, ni);
        assert(ni * mi <= 0x100_0000);
        assert((sum as int + ni / 2) * mi <= 255 * 0x100_0000 + 0x80_0000) by (nonlinear_arith)
            requires
                ni >= 1,
                mi >= 0,
                ni * mi <= 0x100_0000,
                sum <= 255 * ni,
        ;
    }
    (((sum + n / 2) * m) / 0x100_0000) as u8
}

/// `y / p` for `y` in block `b`.
pub proof fn lemma_in_block(y: int, p: int, b: int)
    requires
        p >= 1,
        b >= 0,
        b * p <= y < (b + 1) * p,
    ensures
        y / p == b,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y, p);
    let q = y / p;
    let r = y % p;
    assert(q == b) by (nonlinear_arith)
        requires
            p >= 1,
            y == p * q + r,
            0 <= r < p,
            b * p <= y < (b + 1) * p,
    ;
}

/// Pixel `j` of `pixelate` with the block size `p`.
pub open spec fn pxval(src: Seq<u8>, w: int, h: int, p: int, j: int) -> u8 {
    pval(src, w, h, p, j % NC, ((j / NC) % w) / p, ((j / NC) / w) / p) as u8
}

/// Block row `by`'s `vips_shrinkv` values, columns `0..tw`.
#[verifier::rlimit(40)]
pub fn vrow_x(src: &[u8], w: usize, h: usize, p: usize, by: usize, tw: usize) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        2 <= p <= MAX_DIM,
        src@.len() == w * h * NC,
        tw <= 2 * MAX_DIM,
        by * p <= 2 * MAX_DIM,
        w * h * NC <= 65535 * 65535 * 4,
    ensures
        r@.len() == tw * NC,
        forall|q: int, c: int|
            0 <= q < tw && 0 <= c < NC ==> #[trigger] r@[q * NC + c] == vshr(src@, w as int, h as int, p as int, c, q, by as int),
{
    let ghost s = src@;
    let mut out: Vec<u8> = Vec::with_capacity(tw * 4);
    let mut xx: usize = 0;
    while xx < tw
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            2 <= p <= MAX_DIM,
            s == src@,
            src@.len() == w * h * NC,
            tw <= 2 * MAX_DIM,
            by * p <= 2 * MAX_DIM,
            w * h * NC <= 65535 * 65535 * 4,
            xx <= tw,
            out@.len() == xx * NC,
            forall|q: int, c: int|
                0 <= q < xx && 0 <= c < NC ==> #[trigger] out@[q * NC + c] == vshr(s, w as int, h as int, p as int, c, q, by as int),
        decreases tw - xx,
    {
        let mx = mir_x(xx, w);
        let mut s0: u64 = 0;
        let mut s1: u64 = 0;
        let mut s2: u64 = 0;
        let mut s3: u64 = 0;
        let mut j: usize = 0;
        while j < p
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                2 <= p <= MAX_DIM,
                s == src@,
                src@.len() == w * h * NC,
                by * p <= 2 * MAX_DIM,
                w * h * NC <= 65535 * 65535 * 4,
                mx == mir(xx as int, w as int),
                mx < w,
                j <= p,
                s0 == vsum(s, w as int, h as int, 0, xx as int, (by * p) as int, j as int),
                s1 == vsum(s, w as int, h as int, 1, xx as int, (by * p) as int, j as int),
                s2 == vsum(s, w as int, h as int, 2, xx as int, (by * p) as int, j as int),
                s3 == vsum(s, w as int, h as int, 3, xx as int, (by * p) as int, j as int),
                s0 <= 255 * j,
                s1 <= 255 * j,
                s2 <= 255 * j,
                s3 <= 255 * j,
            decreases p - j,
        {
            let my = mir_x(by * p + j, h);
            proof {
                lemma_idx(my as int, mx as int, 0, w as int, h as int);
                lemma_idx(my as int, mx as int, 3, w as int, h as int);
            }
            let b = (my * w + mx) * 4;
            s0 = s0 + src[b] as u64;
            s1 = s1 + src[b + 1] as u64;
            s2 = s2 + src[b + 2] as u64;
            s3 = s3 + src[b + 3] as u64;
            proof {
                assert(my * w + mx == mir((by * p + j) as int, h as int) * w + mir(xx as int, w as int));
            }
            j = j + 1;
        }
        let ghost before = out@;
        out.push(fixavg_x(s0, p as u64));
        out.push(fixavg_x(s1, p as u64));
        out.push(fixavg_x(s2, p as u64));
        out.push(fixavg_x(s3, p as u64));
        proof {
            assert forall|q: int, c: int| 0 <= q < xx + 1 && 0 <= c < NC implies #[trigger] out@[q * NC + c] == vshr(
                s,
                w as int,
                h as int,
                p as int,
                c,
                q,
                by as int,
            ) by {
                if q < xx {
                    assert(q * NC + c < xx * NC);
                    assert(out@[q * NC + c] == before[q * NC + c]);
                }
            }
        }
        xx = xx + 1;
    }
    out
}

/// Block row `by`'s values, blocks `0..nbx`, from its `vrow_x`.
#[verifier::rlimit(40)]
pub fn brow_x(vr: &[u8], Ghost(src): Ghost<Seq<u8>>, w: usize, h: usize, p: usize, by: usize, nbx: usize) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        2 <= p <= MAX_DIM,
        nbx * p <= 2 * MAX_DIM,
        vr@.len() == nbx * p * NC,
        forall|q: int, c: int|
            0 <= q < nbx * p && 0 <= c < NC ==> #[trigger] vr@[q * NC + c] == vshr(src, w as int, h as int, p as int, c, q, by as int),
    ensures
        r@.len() == nbx * NC,
        forall|b: int, c: int|
            0 <= b < nbx && 0 <= c < NC ==> #[trigger] r@[b * NC + c] == pval(src, w as int, h as int, p as int, c, b, by as int),
{
    proof {
        assert(nbx <= nbx * p) by (nonlinear_arith)
            requires
                p >= 1,
                nbx >= 0,
        ;
    }
    let mut out: Vec<u8> = Vec::with_capacity(nbx * 4);
    let mut bx: usize = 0;
    while bx < nbx
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            2 <= p <= MAX_DIM,
            nbx * p <= 2 * MAX_DIM,
            vr@.len() == nbx * p * NC,
            forall|q: int, c: int|
                0 <= q < nbx * p && 0 <= c < NC ==> #[trigger] vr@[q * NC + c] == vshr(src, w as int, h as int, p as int, c, q, by as int),
            bx <= nbx,
            out@.len() == bx * NC,
            forall|b: int, c: int|
                0 <= b < bx && 0 <= c < NC ==> #[trigger] out@[b * NC + c] == pval(src, w as int, h as int, p as int, c, b, by as int),
        decreases nbx - bx,
    {
        proof {
            assert((bx + 1) * p <= nbx * p) by (nonlinear_arith)
                requires
                    bx + 1 <= nbx,
                    p >= 0,
            ;
        }
        let mut s0: u64 = 0;
        let mut s1: u64 = 0;
        let mut s2: u64 = 0;
        let mut s3: u64 = 0;
        let mut i: usize = 0;
        while i < p
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                2 <= p <= MAX_DIM,
                nbx * p <= 2 * MAX_DIM,
                (bx + 1) * p <= nbx * p,
                vr@.len() == nbx * p * NC,
                forall|q: int, c: int|
                    0 <= q < nbx * p && 0 <= c < NC ==> #[trigger] vr@[q * NC + c] == vshr(src, w as int, h as int, p as int, c, q, by as int),
                i <= p,
                s0 == hsum(src, w as int, h as int, p as int, 0, bx as int, by as int, i as int),
                s1 == hsum(src, w as int, h as int, p as int, 1, bx as int, by as int, i as int),
                s2 == hsum(src, w as int, h as int, p as int, 2, bx as int, by as int, i as int),
                s3 == hsum(src, w as int, h as int, p as int, 3, bx as int, by as int, i as int),
                s0 <= 255 * i,
                s1 <= 255 * i,
                s2 <= 255 * i,
                s3 <= 255 * i,
            decreases p - i,
        {
            proof {
                assert(bx * p + i < nbx * p) by (nonlinear_arith)
                    requires
                        (bx + 1) * p <= nbx * p,
                        i < p,
                ;
            }
            let q = bx * p + i;
            proof {
                assert(q * NC + 3 < nbx * p * NC) by (nonlinear_arith)
                    requires
                        q < nbx * p,
                ;
            }
            proof {
                assert(vr@[q * NC + 0] == vshr(src, w as int, h as int, p as int, 0, q as int, by as int));
                assert(vr@[q * NC + 1] == vshr(src, w as int, h as int, p as int, 1, q as int, by as int));
                assert(vr@[q * NC + 2] == vshr(src, w as int, h as int, p as int, 2, q as int, by as int));
                assert(vr@[q * NC + 3] == vshr(src, w as int, h as int, p as int, 3, q as int, by as int));
                assert(bx * p + (i + 1) - 1 == q);
            }
            s0 = s0 + vr[q * 4] as u64;
            s1 = s1 + vr[q * 4 + 1] as u64;
            s2 = s2 + vr[q * 4 + 2] as u64;
            s3 = s3 + vr[q * 4 + 3] as u64;
            i = i + 1;
        }
        let ghost before = out@;
        out.push(fixavg_x(s0, p as u64));
        out.push(fixavg_x(s1, p as u64));
        out.push(fixavg_x(s2, p as u64));
        out.push(fixavg_x(s3, p as u64));
        proof {
            assert forall|b: int, c: int| 0 <= b < bx + 1 && 0 <= c < NC implies #[trigger] out@[b * NC + c] == pval(
                src,
                w as int,
                h as int,
                p as int,
                c,
                b,
                by as int,
            ) by {
                if b < bx {
                    assert(b * NC + c < bx * NC);
                    assert(out@[b * NC + c] == before[b * NC + c]);
                }
            }
        }
        bx = bx + 1;
    }
    out
}

/// `pixelate`: `src` (`w` by `h` RGBA) pixelated with blocks of `p0`.
#[verifier::rlimit(60)]
pub fn pixelate_rgba(src: Vec<u8>, w: usize, h: usize, p0: usize) -> (r: Vec<u8>)
    requires
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        src@.len() == w * h * NC,
    ensures
        r@ == pixelate(src@, w as int, h as int, p0 as int),
{
    let m = if w > h { w } else { h };
    let p = if p0 > m { m } else { p0 };
    if p <= 1 {
        return src;
    }
    let ghost s = src@;
    let nbx = (w + p - 1) / p;
    let nby = (h + p - 1) / p;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((w + p - 1) as int, p as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((h + p - 1) as int, p as int);
        assert(w <= nbx * p <= 2 * MAX_DIM && nbx * p <= w + p - 1) by (nonlinear_arith)
            requires
                w + p - 1 == p * nbx + ((w + p - 1) as int % (p as int)),
                0 <= ((w + p - 1) as int % (p as int)) < p,
                1 <= w <= MAX_DIM,
                2 <= p <= MAX_DIM,
        ;
        assert(h <= nby * p <= 2 * MAX_DIM && nby * p <= h + p - 1) by (nonlinear_arith)
            requires
                h + p - 1 == p * nby + ((h + p - 1) as int % (p as int)),
                0 <= ((h + p - 1) as int % (p as int)) < p,
                1 <= h <= MAX_DIM,
                2 <= p <= MAX_DIM,
        ;
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
        ;
    }
    let tw = nbx * p;
    let mut out: Vec<u8> = Vec::with_capacity(w * h * 4);
    let mut y: usize = 0;
    let mut by: usize = 0;
    while by < nby
        invariant
            1 <= w <= MAX_DIM,
            1 <= h <= MAX_DIM,
            2 <= p <= MAX_DIM,
            p == pclamp(p0 as int, w as int, h as int),
            s == src@,
            src@.len() == w * h * NC,
            w * h * NC <= 65535 * 65535 * 4,
            tw == nbx * p,
            w <= nbx * p <= 2 * MAX_DIM,
            h <= nby * p <= 2 * MAX_DIM,
            nby * p <= h + p - 1,
            by <= nby,
            y == (if by * p < h { by * p } else { h as int }),
            out@.len() == y * w * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == pxval(s, w as int, h as int, p as int, j),
        decreases nby - by,
    {
        proof {
            assert(by * p <= nby * p) by (nonlinear_arith)
                requires
                    by <= nby,
                    p >= 0,
            ;
            assert((by + 1) * p == by * p + p) by (nonlinear_arith);
            assert(by * p < h) by (nonlinear_arith)
                requires
                    by + 1 <= nby,
                    nby * p <= h + p - 1,
                    p >= 0,
            ;
        }
        let vr = vrow_x(&src, w, h, p, by, tw);
        proof {
            assert(tw * NC == nbx * p * NC);
        }
        let br = brow_x(&vr, Ghost(s), w, h, p, by, nbx);
        let y1 = if by * p + p < h { by * p + p } else { h };
        while y < y1
            invariant
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
                2 <= p <= MAX_DIM,
                s == src@,
                w * h * NC <= 65535 * 65535 * 4,
                w <= nbx * p,
                by * p <= y <= y1,
                y1 <= h,
                y1 <= (by + 1) * p,
                br@.len() == nbx * NC,
                forall|b: int, c: int|
                    0 <= b < nbx && 0 <= c < NC ==> #[trigger] br@[b * NC + c] == pval(s, w as int, h as int, p as int, c, b, by as int),
                out@.len() == y * w * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == pxval(s, w as int, h as int, p as int, j),
            decreases y1 - y,
        {
            proof {
                lemma_in_block(y as int, p as int, by as int);
            }
            let mut x: usize = 0;
            while x < w
                invariant
                    1 <= w <= MAX_DIM,
                    1 <= h <= MAX_DIM,
                    2 <= p <= MAX_DIM,
                    w * h * NC <= 65535 * 65535 * 4,
                    w <= nbx * p,
                    y < h,
                    y / p == by,
                    br@.len() == nbx * NC,
                    forall|b: int, c: int|
                        0 <= b < nbx && 0 <= c < NC ==> #[trigger] br@[b * NC + c] == pval(s, w as int, h as int, p as int, c, b, by as int),
                    x <= w,
                    out@.len() == (y * w + x) * NC,
                    forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == pxval(s, w as int, h as int, p as int, j),
                decreases w - x,
            {
                let b = x / p;
                proof {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, p as int);
                    assert(b < nbx) by (nonlinear_arith)
                        requires
                            x == p * b + x % p,
                            0 <= x % p,
                            x < w,
                            w <= nbx * p,
                            p >= 1,
                    ;
                    assert(b * NC + 3 < nbx * NC);
                }
                let ghost before = out@;
                out.push(br[b * 4]);
                out.push(br[b * 4 + 1]);
                out.push(br[b * 4 + 2]);
                out.push(br[b * 4 + 3]);
                proof {
                    assert((y * w + x + 1) * NC == (y * w + x) * NC + 4) by (nonlinear_arith);
                    assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == pxval(
                        s,
                        w as int,
                        h as int,
                        p as int,
                        j,
                    ) by {
                        if j >= before.len() {
                            let k = (y * w + x) * NC;
                            lemma_idx(y as int, x as int, j - k, w as int, h as int);
                            assert(out@[j] == br@[b * NC + (j - k)]);
                        } else {
                            assert(out@[j] == before[j]);
                        }
                    }
                }
                x = x + 1;
            }
            proof {
                assert((y * w + w) * NC == (y + 1) * w * NC) by (nonlinear_arith);
            }
            y = y + 1;
        }
        by = by + 1;
    }
    proof {
        assert(y == h) by (nonlinear_arith)
            requires
                y == (if by * p < h { by * p } else { h as int }),
                by == nby,
                h <= nby * p,
        ;
        assert(out@.len() == w * h * NC) by (nonlinear_arith)
            requires
                out@.len() == h * w * NC,
        ;
        assert(out@ =~= pixelate(s, w as int, h as int, p0 as int));
    }
    out
}

} // verus!
