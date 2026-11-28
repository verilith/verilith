//! `blur` and `sharpen`, proven to compute `spec_filter::blur` and
//! `spec_filter::sharpen` for every table of weights up to 2049 entries
//! of at most 65536, and every image up to 65535 by 65535: no overflow,
//! no out-of-bounds access.
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
    &&& 1 <= g.len() <= 2049
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

/// `gtot`.
pub fn gtot_x(g: &[u32]) -> (r: i64)
    requires
        gk_ok(g@),
    ensures
        r == gtot(gseq(g@)),
        0 <= r <= 2049 * 65536,
{
    let ghost k = gseq(g@);
    let mut a: i64 = 0;
    let mut t: usize = 0;
    while t < g.len()
        invariant
            gk_ok(g@),
            k == gseq(g@),
            t <= g@.len(),
            a == gsum(kunit(), k, 0, 1, t as int),
            0 <= a <= t * 65536,
        decreases g.len() - t,
    {
        proof {
            assert(k[t as int] == g@[t as int] as int);
            assert(kunit()(kc(0 + ((t + 1) - 1) - gr(k), 1)) == 1);
            assert(gsum(kunit(), k, 0, 1, (t + 1) as int) == gsum(kunit(), k, 0, 1, t as int) + k[t as int]);
        }
        a = a + g[t] as i64;
        t = t + 1;
    }
    a
}

/// The row pass's value at index `k` of its output.
pub open spec fn ghval(g: Seq<int>, src: Seq<u8>, w: int, k: int) -> int {
    ghpx(g, src, w, (k / NC) / w, (k / NC) % w, k % NC)
}

/// The row pass: `w * h * 4` values, `ghpx` of each pixel and channel.
pub fn grows(g: &[u32], src: &[u8], w: usize, h: usize, tot: i64) -> (r: Vec<u16>)
    requires
        gk_ok(g@),
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        w * h * NC <= 65535 * 65535 * 4,
        src@.len() == w * h * NC,
        tot == gtot(gseq(g@)),
        0 <= tot <= 2049 * 65536,
    ensures
        r@.len() == w * h * NC,
        forall|y: int, x: int, c: int|
            0 <= y < h && 0 <= x < w && 0 <= c < NC ==> #[trigger] r@[(y * w + x) * NC + c] == ghpx(
                gseq(g@),
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
    let mut out: Vec<u16> = Vec::with_capacity(w * h * 4);
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
            tot == gtot(k),
            0 <= tot <= 2049 * 65536,
            y <= h,
            out@.len() == y * w * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == ghval(k, s, w as int, j),
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
                tot == gtot(k),
                0 <= tot <= 2049 * 65536,
                y < h,
                x <= w,
                out@.len() == (y * w + x) * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == ghval(k, s, w as int, j),
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
                assert(t * 16711680 <= 2049 * 16711680) by (nonlinear_arith)
                    requires
                        t <= 2049,
                ;
                lemma_idx(y as int, x as int, 3, w as int, h as int);
            }
            let q0 = kdiv_x(a0, tot, 256) as u16;
            let q1 = kdiv_x(a1, tot, 256) as u16;
            let q2 = kdiv_x(a2, tot, 256) as u16;
            let q3 = kdiv_x(a3, tot, 256) as u16;
            let ghost before = out@;
            out.push(q0);
            out.push(q1);
            out.push(q2);
            out.push(q3);
            proof {
                assert((y * w + x + 1) * NC == (y * w + x) * NC + 4) by (nonlinear_arith);
                assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == ghval(k, s, w as int, j) by {
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
pub open spec fn goval(g: Seq<int>, src: Seq<u8>, w: int, h: int, k: int) -> u8 {
    gopx(g, src, w, h, (k / NC) / w, (k / NC) % w, k % NC)
}

/// The column pass over the row pass's values `mid`: the blurred image.
#[verifier::rlimit(40)]
pub fn gcols(g: &[u32], mid: &[u16], Ghost(src): Ghost<Seq<u8>>, w: usize, h: usize, tot: i64) -> (r: Vec<u8>)
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
                src,
                w as int,
                y,
                x,
                c,
            ),
        tot == gtot(gseq(g@)),
        0 <= tot <= 2049 * 65536,
    ensures
        r@ == blur(gseq(g@), src, w as int, h as int),
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
                    src,
                    w as int,
                    y,
                    x,
                    c,
                ),
            tot == gtot(k),
            0 <= tot <= 2049 * 65536,
            y <= h,
            out@.len() == y * w * NC,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == goval(k, src, w as int, h as int, j),
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
                        src,
                        w as int,
                        y,
                        x,
                        c,
                    ),
                tot == gtot(k),
                0 <= tot <= 2049 * 65536,
                y < h,
                x <= w,
                out@.len() == (y * w + x) * NC,
                forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == goval(k, src, w as int, h as int, j),
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
                            src,
                            w as int,
                            y,
                            x,
                            c,
                        ),
                    y < h,
                    x < w,
                    t <= n,
                    a0 == gsum(gmid_line(k, src, w as int, x as int, 0), k, y as int, h as int, t as int),
                    a1 == gsum(gmid_line(k, src, w as int, x as int, 1), k, y as int, h as int, t as int),
                    a2 == gsum(gmid_line(k, src, w as int, x as int, 2), k, y as int, h as int, t as int),
                    a3 == gsum(gmid_line(k, src, w as int, x as int, 3), k, y as int, h as int, t as int),
                    0 <= a0 <= t * 4278190080,
                    0 <= a1 <= t * 4278190080,
                    0 <= a2 <= t * 4278190080,
                    0 <= a3 <= t * 4278190080,
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
                    assert(mid@[(cj * w + x) * NC + 0] == ghpx(k, src, w as int, cj as int, x as int, 0));
                    assert(mid@[(cj * w + x) * NC + 1] == ghpx(k, src, w as int, cj as int, x as int, 1));
                    assert(mid@[(cj * w + x) * NC + 2] == ghpx(k, src, w as int, cj as int, x as int, 2));
                    assert(mid@[(cj * w + x) * NC + 3] == ghpx(k, src, w as int, cj as int, x as int, 3));
                    assert(gmid_line(k, src, w as int, x as int, 0)(cj as int) == v0);
                    assert(gmid_line(k, src, w as int, x as int, 1)(cj as int) == v1);
                    assert(gmid_line(k, src, w as int, x as int, 2)(cj as int) == v2);
                    assert(gmid_line(k, src, w as int, x as int, 3)(cj as int) == v3);
                    assert(0 <= wt * v0 <= 4278190080 && 0 <= wt * v1 <= 4278190080 && 0 <= wt * v2 <= 4278190080
                        && 0 <= wt * v3 <= 4278190080) by (nonlinear_arith)
                        requires
                            0 <= wt <= 65536,
                            0 <= v0 <= 65280,
                            0 <= v1 <= 65280,
                            0 <= v2 <= 65280,
                            0 <= v3 <= 65280,
                    ;
                    assert((t + 1) * 4278190080 == t * 4278190080 + 4278190080) by (nonlinear_arith);
                    assert(k[t as int] == wt);
                }
                a0 = a0 + wt * v0;
                a1 = a1 + wt * v1;
                a2 = a2 + wt * v2;
                a3 = a3 + wt * v3;
                t = t + 1;
            }
            proof {
                assert(t * 4278190080 <= 2049 * 4278190080) by (nonlinear_arith)
                    requires
                        t <= 2049,
                ;
                lemma_idx(y as int, x as int, 3, w as int, h as int);
            }
            let q0 = kdiv_x(a0, 256 * tot, 1) as u8;
            let q1 = kdiv_x(a1, 256 * tot, 1) as u8;
            let q2 = kdiv_x(a2, 256 * tot, 1) as u8;
            let q3 = kdiv_x(a3, 256 * tot, 1) as u8;
            let ghost before = out@;
            out.push(q0);
            out.push(q1);
            out.push(q2);
            out.push(q3);
            proof {
                assert((y * w + x + 1) * NC == (y * w + x) * NC + 4) by (nonlinear_arith);
                assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == goval(
                    k,
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
        assert(out@ =~= blur(k, src, w as int, h as int));
    }
    out
}

/// `blur`: `src` (`w` by `h` RGBA) blurred with the table `g`.
pub fn blur_rgba(g: &[u32], src: &[u8], w: usize, h: usize) -> (r: Vec<u8>)
    requires
        gk_ok(g@),
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        src@.len() == w * h * NC,
    ensures
        r@ == blur(gseq(g@), src@, w as int, h as int),
{
    proof {
        assert(w * h * NC <= 65535 * 65535 * 4) by (nonlinear_arith)
            requires
                1 <= w <= MAX_DIM,
                1 <= h <= MAX_DIM,
        ;
    }
    let tot = gtot_x(g);
    let mid = grows(g, src, w, h, tot);
    gcols(g, mid.as_slice(), Ghost(src@), w, h, tot)
}

/// `sharpen`: an unsharp mask of `src` with the table `g`.
pub fn sharpen_rgba(g: &[u32], src: &[u8], w: usize, h: usize) -> (r: Vec<u8>)
    requires
        gk_ok(g@),
        1 <= w <= MAX_DIM,
        1 <= h <= MAX_DIM,
        src@.len() == w * h * NC,
    ensures
        r@ == sharpen(gseq(g@), src@, w as int, h as int),
{
    let b = blur_rgba(g, src, w, h);
    let n = src.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == src@.len(),
            b@.len() == n,
            b@ == blur(gseq(g@), src@, w as int, h as int),
            n == w * h * NC,
            i <= n,
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == sharpen(gseq(g@), src@, w as int, h as int)[j],
        decreases n - i,
    {
        let v = if i % 4 == 3 {
            src[i]
        } else {
            let d = 2 * src[i] as i32 - b[i] as i32;
            if d < 0 {
                0
            } else if d > 255 {
                255
            } else {
                d as u8
            }
        };
        out.push(v);
        i = i + 1;
    }
    proof {
        assert(out@ =~= sharpen(gseq(g@), src@, w as int, h as int));
    }
    out
}

} // verus!
