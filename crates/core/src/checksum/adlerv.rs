//! Adler-32 with byte dot products (`vpdpbusd` on AVX-512 VNNI,
//! `vpmaddubsw`/`vpmaddwd` on AVX2), proven to compute `adler_from`.
//!
//! The input is taken in rows of `W` bytes (64 or 32), each split into
//! `W / 4` lanes of four bytes. Three vectors of 32-bit lanes are kept:
//! `s1`, the sums of the bytes so far; `s10`, the sum over rows of `s1` as
//! it was before the row; and `s2`, the sums of each byte weighted by
//! `W - k`, its distance from the end of its row. One row is three
//! instructions: `s10 += s1`, `s1 += dot(row, 1)`, `s2 += dot(row, W - k)`.
//! Then over the rows `X` so far, `sum(s1) == sum(X)` and
//! `W * sum(s10) + sum(s2) == wsum(X)` (`lemma_row`), and at the end of a
//! block the sums go through the closed form `lemma_adler_closed`.
//!
//! Blocks are at most 1024 rows, which keeps every lane below 2^32
//! (`s10`, the largest, below `1020 * 1024^2`). The kernels at the end
//! (x86-64 only) are verified; what they trust is `vdot.rs`.
#[cfg(verus_only)]
use super::{
    adler_from, jsum, lemma_adler_append, lemma_adler_closed, lemma_lanes_bound, lemma_lanes_sum,
    lemma_sum_append, lemma_wsum_jsum, lsum, spec, sum, wsum,
};
use vstd::prelude::*;

verus! {

/// The dot product of lane `j`'s four bytes of `x` and `w`.
pub open spec fn dot4(x: Seq<u8>, w: Seq<u8>, j: int) -> nat {
    (x[4 * j] as nat) * (w[4 * j] as nat) + (x[4 * j + 1] as nat) * (w[4 * j + 1] as nat) + (x[4 * j
        + 2] as nat) * (w[4 * j + 2] as nat) + (x[4 * j + 3] as nat) * (w[4 * j + 3] as nat)
}

/// The dot product of the first `m` bytes of `x` and `w`.
pub open spec fn dotn(x: Seq<u8>, w: Seq<u8>, m: nat) -> nat
    decreases m,
{
    if m == 0 {
        0
    } else {
        dotn(x, w, (m - 1) as nat) + (x[m - 1] as nat) * (w[m - 1] as nat)
    }
}

/// Lanes `v` are lanes `u` plus each lane's dot product.
pub proof fn lemma_dot_lanes(u: Seq<u32>, v: Seq<u32>, x: Seq<u8>, w: Seq<u8>, l: nat)
    requires
        l <= u.len(),
        l <= v.len(),
        4 * l <= x.len(),
        4 * l <= w.len(),
        forall|j: int| 0 <= j < l ==> #[trigger] v[j] as nat == u[j] as nat + dot4(x, w, j),
    ensures
        lsum(v, l) == lsum(u, l) + dotn(x, w, 4 * l),
    decreases l,
{
    if l > 0 {
        let k = (l - 1) as nat;
        lemma_dot_lanes(u, v, x, w, k);
        let q = 4 * k as int;
        assert(4 * l == 4 * k + 4);
        assert(dotn(x, w, (q + 4) as nat) == dotn(x, w, (q + 3) as nat) + (x[q + 3] as nat) * (w[q + 3] as nat));
        assert(dotn(x, w, (q + 3) as nat) == dotn(x, w, (q + 2) as nat) + (x[q + 2] as nat) * (w[q + 2] as nat));
        assert(dotn(x, w, (q + 2) as nat) == dotn(x, w, (q + 1) as nat) + (x[q + 1] as nat) * (w[q + 1] as nat));
        assert(dotn(x, w, (q + 1) as nat) == dotn(x, w, q as nat) + (x[q] as nat) * (w[q] as nat));
    }
}

/// With all weights 1, the dot product is the sum.
pub proof fn lemma_dot_ones(x: Seq<u8>, w: Seq<u8>, m: nat)
    requires
        m <= x.len(),
        m <= w.len(),
        forall|k: int| 0 <= k < m ==> #[trigger] w[k] == 1,
    ensures
        dotn(x, w, m) == sum(x.subrange(0, m as int)),
    decreases m,
{
    if m > 0 {
        lemma_dot_ones(x, w, (m - 1) as nat);
        assert(x.subrange(0, m as int).drop_last() =~= x.subrange(0, m - 1));
    } else {
        assert(x.subrange(0, 0) =~= Seq::<u8>::empty());
    }
}

/// With weights `c - k`, the dot product is `c * sum - jsum`.
pub proof fn lemma_dot_desc(x: Seq<u8>, w: Seq<u8>, m: nat, c: nat)
    requires
        m <= x.len(),
        m <= w.len(),
        m <= c,
        forall|k: int| 0 <= k < m ==> #[trigger] w[k] as int == c - k,
    ensures
        dotn(x, w, m) + jsum(x.subrange(0, m as int)) == c * sum(x.subrange(0, m as int)),
    decreases m,
{
    if m > 0 {
        let k = (m - 1) as nat;
        lemma_dot_desc(x, w, k, c);
        let p = x.subrange(0, m as int);
        assert(p.drop_last() =~= x.subrange(0, k as int));
        assert(p.last() == x[k as int]);
        let xv = x[k as int] as int;
        let wk = w[k as int] as int;
        assert(wk == c - k);
        assert(dotn(x, w, m) == dotn(x, w, k) + xv * wk);
        assert(jsum(p) == jsum(p.drop_last()) + k * xv);
        assert(sum(p) == sum(p.drop_last()) + xv);
        assert(xv * wk + k * xv == c * xv) by (nonlinear_arith) requires wk == c - k;
        let s0 = sum(x.subrange(0, k as int)) as int;
        assert(c * (s0 + xv) == c * s0 + c * xv) by (nonlinear_arith);
        assert(sum(p) == s0 + xv);
        assert(jsum(p) == jsum(x.subrange(0, k as int)) + k * xv);
        let d0 = dotn(x, w, k) as int;
        let j0 = jsum(x.subrange(0, k as int)) as int;
        assert(d0 + j0 == c * s0);
        assert(dotn(x, w, m) + jsum(p) == (d0 + xv * wk) + (j0 + k * xv));
    } else {
        assert(x.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(c * 0 == 0) by (nonlinear_arith);
    }
}

/// Rows of `w` bytes: `s1`, `s10`, `s2` as the module describes, after
/// the bytes `x`, `r` rows of them.
pub open spec fn row_inv(s1: Seq<u32>, s10: Seq<u32>, s2: Seq<u32>, x: Seq<u8>, w: nat, r: nat) -> bool {
    let l = w / 4;
    &&& s1.len() == l
    &&& s10.len() == l
    &&& s2.len() == l
    &&& x.len() == w * r
    &&& lsum(s1, l) == sum(x)
    &&& w * lsum(s10, l) + lsum(s2, l) == wsum(x)
    &&& forall|j: int| 0 <= j < l ==> #[trigger] s1[j] as nat <= 1020 * r
    &&& forall|j: int| 0 <= j < l ==> #[trigger] s10[j] as nat <= 1020 * r * r
    &&& forall|j: int| 0 <= j < l ==> #[trigger] s2[j] as nat <= 1020 * w * r
}

/// The lane's four bytes are each at most 255, so a dot product with
/// weights at most `c` is at most `1020 * c`.
pub proof fn lemma_dot4_bound(x: Seq<u8>, w: Seq<u8>, j: int, c: nat)
    requires
        0 <= j,
        4 * j + 4 <= x.len(),
        4 * j + 4 <= w.len(),
        forall|k: int| 4 * j <= k < 4 * j + 4 ==> #[trigger] w[k] as nat <= c,
    ensures
        dot4(x, w, j) <= 1020 * c,
{
    let (x0, x1, x2, x3) = (x[4 * j] as nat, x[4 * j + 1] as nat, x[4 * j + 2] as nat, x[4 * j + 3] as nat);
    let (w0, w1, w2, w3) = (w[4 * j] as nat, w[4 * j + 1] as nat, w[4 * j + 2] as nat, w[4 * j + 3] as nat);
    assert(w0 <= c && w1 <= c && w2 <= c && w3 <= c);
    assert(x0 * w0 <= 255 * c) by (nonlinear_arith) requires x0 <= 255, w0 <= c;
    assert(x1 * w1 <= 255 * c) by (nonlinear_arith) requires x1 <= 255, w1 <= c;
    assert(x2 * w2 <= 255 * c) by (nonlinear_arith) requires x2 <= 255, w2 <= c;
    assert(x3 * w3 <= 255 * c) by (nonlinear_arith) requires x3 <= 255, w3 <= c;
}

/// One row `y`: `s10 += s1`, `s1 += dot(y, ones)`, `s2 += dot(y, desc)`.
pub proof fn lemma_row(
    s1: Seq<u32>,
    s10: Seq<u32>,
    s2: Seq<u32>,
    t1: Seq<u32>,
    t10: Seq<u32>,
    t2: Seq<u32>,
    x: Seq<u8>,
    y: Seq<u8>,
    ones: Seq<u8>,
    desc: Seq<u8>,
    w: nat,
    r: nat,
)
    requires
        w == 32 || w == 64,
        r < 1024,
        row_inv(s1, s10, s2, x, w, r),
        y.len() == w,
        ones.len() == w,
        desc.len() == w,
        forall|k: int| 0 <= k < w ==> #[trigger] ones[k] == 1,
        forall|k: int| 0 <= k < w ==> #[trigger] desc[k] as int == w - k,
        t10.len() == w / 4,
        t1.len() == w / 4,
        t2.len() == w / 4,
        forall|j: int| 0 <= j < w / 4 ==> #[trigger] t10[j] == super::vdot_add32(s10[j] as int, s1[j] as int),
        forall|j: int| 0 <= j < w / 4 ==> #[trigger] t1[j] == super::vdot_add32(s1[j] as int, dot4(y, ones, j) as int),
        forall|j: int| 0 <= j < w / 4 ==> #[trigger] t2[j] == super::vdot_add32(s2[j] as int, dot4(y, desc, j) as int),
    ensures
        row_inv(t1, t10, t2, x + y, w, r + 1),
{
    let l = w / 4;
    assert(4 * l == w);
    let r1 = (r + 1) as nat;
    assert(1020 * r * r + 1020 * r <= 1020 * r1 * r1) by (nonlinear_arith) requires r1 == r + 1;
    assert(1020 * r1 * r1 < 0x1_0000_0000) by (nonlinear_arith) requires r1 <= 1024;
    assert(1020 * w * r + 1020 * w == 1020 * w * r1) by (nonlinear_arith) requires r1 == r + 1;
    assert(1020 * w * r1 < 0x1_0000_0000) by (nonlinear_arith) requires r1 <= 1024, w <= 64;
    assert forall|j: int| 0 <= j < l implies #[trigger] t10[j] as nat == s10[j] as nat + s1[j] as nat
        && t10[j] as nat <= 1020 * r1 * r1 by {
        assert(s1[j] as nat <= 1020 * r);
        assert(s10[j] as nat <= 1020 * r * r);
        assert(1020 * r <= 1020 * r1 * r1) by (nonlinear_arith) requires r1 == r + 1;
        let a10 = s10[j] as int + s1[j] as int;
        vstd::arithmetic::div_mod::lemma_small_mod(a10 as nat, 0x1_0000_0000);
    }
    assert forall|j: int| 0 <= j < l implies #[trigger] t1[j] as nat == s1[j] as nat + dot4(y, ones, j)
        && t1[j] as nat <= 1020 * r1 by {
        lemma_dot4_bound(y, ones, j, 1);
        assert(s1[j] as nat <= 1020 * r);
        let a1 = s1[j] as int + dot4(y, ones, j) as int;
        vstd::arithmetic::div_mod::lemma_small_mod(a1 as nat, 0x1_0000_0000);
    }
    assert forall|j: int| 0 <= j < l implies #[trigger] t2[j] as nat == s2[j] as nat + dot4(y, desc, j)
        && t2[j] as nat <= 1020 * w * r1 by {
        lemma_dot4_bound(y, desc, j, w);
        assert(s2[j] as nat <= 1020 * w * r);
        let a2 = s2[j] as int + dot4(y, desc, j) as int;
        vstd::arithmetic::div_mod::lemma_small_mod(a2 as nat, 0x1_0000_0000);
    }
    lemma_lanes_sum(s10, t10, s1, l);
    lemma_dot_lanes(s1, t1, y, ones, l);
    lemma_dot_lanes(s2, t2, y, desc, l);
    lemma_dot_ones(y, ones, w);
    lemma_dot_desc(y, desc, w, w);
    assert(y.subrange(0, w as int) =~= y);
    lemma_wsum_jsum(y);
    lemma_sum_append(x, y);
    assert((x + y).len() == w * r1) by (nonlinear_arith) requires x.len() == w * r, y.len() == w, r1 == r + 1;
    assert(w * lsum(t10, l) == w * lsum(s10, l) + w * lsum(s1, l)) by (nonlinear_arith)
        requires lsum(t10, l) == lsum(s10, l) + lsum(s1, l);
}

/// The weights: ones, and `w - k`.
pub open spec fn ones_ok(a: Seq<u8>, w: nat) -> bool {
    a.len() == w && forall|k: int| 0 <= k < w ==> #[trigger] a[k] == 1
}

pub open spec fn desc_ok(a: Seq<u8>, w: nat) -> bool {
    a.len() == w && forall|k: int| 0 <= k < w ==> #[trigger] a[k] as int == w - k
}

pub exec const ONES64: [u8; 64]
    ensures
        ones_ok(ONES64@, 64),
{
    let a = [1u8; 64];
    assert(a@ =~= Seq::new(64, |k: int| 1u8));
    a
}

pub exec const DESC64: [u8; 64]
    ensures
        desc_ok(DESC64@, 64),
{
    let a: [u8; 64] = [
        64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42,
        41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19,
        18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
    ];
    assert(a@ =~= Seq::new(64, |k: int| (64 - k) as u8));
    a
}

pub exec const ONES32: [u8; 32]
    ensures
        ones_ok(ONES32@, 32),
{
    let a = [1u8; 32];
    assert(a@ =~= Seq::new(32, |k: int| 1u8));
    a
}

pub exec const DESC32: [u8; 32]
    ensures
        desc_ok(DESC32@, 32),
{
    let a: [u8; 32] = [
        32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10,
        9, 8, 7, 6, 5, 4, 3, 2, 1,
    ];
    assert(a@ =~= Seq::new(32, |k: int| (32 - k) as u8));
    a
}

/// The sum of the lanes, in 64 bits.
pub fn lane_sum(v: &[u32]) -> (r: u64)
    requires
        v@.len() <= 16,
    ensures
        r as nat == lsum(v@, v@.len() as nat),
{
    let mut r: u64 = 0;
    let mut j: usize = 0;
    while j < v.len()
        invariant
            j <= v@.len() <= 16,
            r as nat == lsum(v@, j as nat),
            r as nat <= j * 0xffff_ffff,
        decreases v@.len() - j,
    {
        assert((j + 1) * 0xffff_ffff == j * 0xffff_ffff + 0xffff_ffff) by (nonlinear_arith);
        r = r + v[j] as u64;
        j = j + 1;
    }
    r
}

/// The block's sums from the lanes, reduced: the closed form.
pub fn block_sums(a: u32, b: u32, s1: &[u32], s10: &[u32], s2: &[u32], Ghost(x): Ghost<Seq<u8>>, w: u64, rows: u64) -> (r: (u32, u32))
    requires
        a < super::ADLER_MOD,
        b < super::ADLER_MOD,
        w == 32 || w == 64,
        rows <= 1024,
        row_inv(s1@, s10@, s2@, x, w as nat, rows as nat),
    ensures
        r.0 < super::ADLER_MOD,
        r.1 < super::ADLER_MOD,
        (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, x),
{
    let ghost l = (w / 4) as nat;
    let p1 = lane_sum(s1);
    let p10 = lane_sum(s10);
    let p2 = lane_sum(s2);
    proof {
        let rr = rows as nat;
        lemma_lanes_bound(s1@, l, 1020 * rr);
        lemma_lanes_bound(s10@, l, 1020 * rr * rr);
        lemma_lanes_bound(s2@, l, 1020 * (w as nat) * rr);
        assert(l * (1020 * rr) <= 16 * 1020 * 1024) by (nonlinear_arith) requires l <= 16, rr <= 1024;
        assert(l * (1020 * rr * rr) <= 16 * 1020 * 1024 * 1024) by (nonlinear_arith) requires l <= 16, rr <= 1024;
        assert(l * (1020 * (w as nat) * rr) <= 16 * 1020 * 64 * 1024) by (nonlinear_arith) requires l <= 16, rr <= 1024, w <= 64;
        assert((w * rows) as nat * (a as nat) <= 65536 * 65521) by (nonlinear_arith) requires w <= 64, rows <= 1024, a < 65521;
        assert((w as nat) * (p10 as nat) <= 64 * 16 * 1020 * 1024 * 1024) by (nonlinear_arith) requires w <= 64, p10 <= 16 * 1020 * 1024 * 1024;
    }
    assert(w * rows <= 65536) by (nonlinear_arith) requires w <= 64, rows <= 1024;
    let ra = (a as u64 + p1) % 65521;
    let rb = (b as u64 + (w * rows) * a as u64 + w * p10 + p2) % 65521;
    proof {
        lemma_adler_closed(a as nat, b as nat, x);
        assert(x.len() == (w * rows) as nat);
    }
    (ra as u32, rb as u32)
}

} // verus!

#[cfg(target_arch = "x86_64")]
verus! {

use super::vdot::*;

broadcast use group_vdot;

/// One block of `rows` rows of 64 bytes from `i`, with AVX-512 VNNI.
#[inline(always)]
fn block_vnni(a: u32, b: u32, d: &[u8], i: usize, rows: usize) -> (r: (u32, u32))
    requires
        vnni512(),
        a < super::ADLER_MOD,
        b < super::ADLER_MOD,
        1 <= rows <= 1024,
        i + 64 * rows <= d@.len() <= usize::MAX,
    ensures
        r.0 < super::ADLER_MOD,
        r.1 < super::ADLER_MOD,
        (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, d@.subrange(i as int, i + 64 * rows)),
{
    let oa = ONES64;
    let da = DESC64;
    let ones = zb_load(&oa, 0);
    let desc = zb_load(&da, 0);
    proof {
        assert(oa@.subrange(0, 64) =~= oa@);
        assert(da@.subrange(0, 64) =~= da@);
    }
    let zero = zd_zero();
    let mut s1 = zd_zero();
    let mut s10 = zd_zero();
    let mut s2 = zd_zero();
    let mut r: usize = 0;
    proof {
        assert(d@.subrange(i as int, i as int) =~= Seq::<u8>::empty());
        assert(lsum(zd(s1), 16) == 0) by { lemma_lanes_bound(zd(s1), 16, 0); }
        assert(lsum(zd(s10), 16) == 0) by { lemma_lanes_bound(zd(s10), 16, 0); }
        assert(lsum(zd(s2), 16) == 0) by { lemma_lanes_bound(zd(s2), 16, 0); }
    }
    while r < rows
        invariant
            vnni512(),
            1 <= rows <= 1024,
            r <= rows,
            i + 64 * rows <= d@.len() <= usize::MAX,
            ones_ok(zb(ones), 64),
            desc_ok(zb(desc), 64),
            zd(zero) == Seq::new(16, |j: int| 0u32),
            row_inv(zd(s1), zd(s10), zd(s2), d@.subrange(i as int, i + 64 * r), 64, r as nat),
        decreases rows - r,
    {
        assert(64 * r < 64 * rows) by (nonlinear_arith) requires r < rows;
        let j = i + 64 * r;
        let y = zb_load(d, j);
        let t10 = zd_add(&s10, &s1);
        // Dot products into zero, then added: `vpdpbusd` has a latency of
        // several cycles, an add one, so the rows no longer wait on it.
        let u1 = zd_dot(&zero, &y, &ones);
        let u2 = zd_dot(&zero, &y, &desc);
        let t1 = zd_add(&s1, &u1);
        let t2 = zd_add(&s2, &u2);
        proof {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] zd(t1)[j] == super::vdot_add32(zd(s1)[j] as int, dot4(zb(y), zb(ones), j) as int)
                && zd(t2)[j] == super::vdot_add32(zd(s2)[j] as int, dot4(zb(y), zb(desc), j) as int) by {
                lemma_dot4_bound(zb(y), zb(ones), j, 1);
                lemma_dot4_bound(zb(y), zb(desc), j, 64);
                assert(zd(u1)[j] == dot4(zb(y), zb(ones), j));
                assert(zd(u2)[j] == dot4(zb(y), zb(desc), j));
            }
            lemma_row(zd(s1), zd(s10), zd(s2), zd(t1), zd(t10), zd(t2), d@.subrange(i as int, j as int),
                zb(y), zb(ones), zb(desc), 64, r as nat);
            assert(d@.subrange(i as int, j as int) + zb(y) =~= d@.subrange(i as int, i + 64 * (r + 1)));
        }
        s1 = t1;
        s10 = t10;
        s2 = t2;
        r = r + 1;
    }
    let v1 = zd_store(&s1);
    let v10 = zd_store(&s10);
    let v2 = zd_store(&s2);
    block_sums(a, b, &v1, &v10, &v2, Ghost(d@.subrange(i as int, i + 64 * rows)), 64, rows as u64)
}

/// One block of `rows` rows of 32 bytes from `i`, with AVX2.
#[inline(always)]
fn block_avx2(a: u32, b: u32, d: &[u8], i: usize, rows: usize) -> (r: (u32, u32))
    requires
        avx2(),
        a < super::ADLER_MOD,
        b < super::ADLER_MOD,
        1 <= rows <= 1024,
        i + 32 * rows <= d@.len() <= usize::MAX,
    ensures
        r.0 < super::ADLER_MOD,
        r.1 < super::ADLER_MOD,
        (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, d@.subrange(i as int, i + 32 * rows)),
{
    let oa = ONES32;
    let da = DESC32;
    let ones = yb_load(&oa, 0);
    let desc = yb_load(&da, 0);
    proof {
        assert(oa@.subrange(0, 32) =~= oa@);
        assert(da@.subrange(0, 32) =~= da@);
    }
    let mut s1 = yd_zero();
    let mut s10 = yd_zero();
    let mut s2 = yd_zero();
    let mut r: usize = 0;
    proof {
        assert(d@.subrange(i as int, i as int) =~= Seq::<u8>::empty());
        assert(lsum(yd(s1), 8) == 0) by { lemma_lanes_bound(yd(s1), 8, 0); }
        assert(lsum(yd(s10), 8) == 0) by { lemma_lanes_bound(yd(s10), 8, 0); }
        assert(lsum(yd(s2), 8) == 0) by { lemma_lanes_bound(yd(s2), 8, 0); }
    }
    while r < rows
        invariant
            avx2(),
            1 <= rows <= 1024,
            r <= rows,
            i + 32 * rows <= d@.len() <= usize::MAX,
            ones_ok(yb(ones), 32),
            desc_ok(yb(desc), 32),
            row_inv(yd(s1), yd(s10), yd(s2), d@.subrange(i as int, i + 32 * r), 32, r as nat),
        decreases rows - r,
    {
        assert(32 * r < 32 * rows) by (nonlinear_arith) requires r < rows;
        let j = i + 32 * r;
        let y = yb_load(d, j);
        let t10 = yd_add(&s10, &s1);
        let t1 = yd_dot(&s1, &y, &ones);
        let t2 = yd_dot(&s2, &y, &desc);
        proof {
            lemma_row(yd(s1), yd(s10), yd(s2), yd(t1), yd(t10), yd(t2), d@.subrange(i as int, j as int),
                yb(y), yb(ones), yb(desc), 32, r as nat);
            assert(d@.subrange(i as int, j as int) + yb(y) =~= d@.subrange(i as int, i + 32 * (r + 1)));
        }
        s1 = t1;
        s10 = t10;
        s2 = t2;
        r = r + 1;
    }
    let v1 = yd_store(&s1);
    let v10 = yd_store(&s10);
    let v2 = yd_store(&s2);
    block_sums(a, b, &v1, &v10, &v2, Ghost(d@.subrange(i as int, i + 32 * rows)), 32, rows as u64)
}

/// **Adler-32 with AVX-512 VNNI**: blocks of up to 1024 rows of 64 bytes,
/// then the portable code for the last 63 bytes or fewer.
#[inline(always)]
pub fn adler32_vnni(a0: u32, b0: u32, d: &[u8]) -> (r: (u32, u32))
    requires
        vnni512(),
        a0 < super::ADLER_MOD,
        b0 < super::ADLER_MOD,
    ensures
        (r.0 as nat, r.1 as nat) == adler_from(a0 as nat, b0 as nat, d@),
{
    let n = d.len();
    let mut a = a0;
    let mut b = b0;
    let mut i: usize = 0;
    proof {
        assert(d@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while n - i >= 64
        invariant
            vnni512(),
            n == d@.len(),
            i <= n,
            a < super::ADLER_MOD,
            b < super::ADLER_MOD,
            (a as nat, b as nat) == adler_from(a0 as nat, b0 as nat, d@.subrange(0, i as int)),
        decreases n - i,
    {
        let rows = if (n - i) / 64 >= 1024 { 1024 } else { (n - i) / 64 };
        let (x, y) = block_vnni(a, b, d, i, rows);
        proof {
            lemma_adler_append(a0 as nat, b0 as nat, d@.subrange(0, i as int), d@.subrange(i as int, i + 64 * rows));
            assert(d@.subrange(0, i as int) + d@.subrange(i as int, i + 64 * rows) =~= d@.subrange(0, i + 64 * rows));
        }
        a = x;
        b = y;
        i = i + 64 * rows;
    }
    let tail = vstd::slice::slice_subrange(d, i, n);
    let (x, y) = super::adler32_update(a, b, tail);
    proof {
        lemma_adler_append(a0 as nat, b0 as nat, d@.subrange(0, i as int), tail@);
        assert(d@.subrange(0, i as int) + tail@ =~= d@);
    }
    (x, y)
}

/// **Adler-32 with AVX2**: blocks of up to 1024 rows of 32 bytes, then
/// the portable code for the last 31 bytes or fewer.
#[inline(always)]
pub fn adler32_avx2(a0: u32, b0: u32, d: &[u8]) -> (r: (u32, u32))
    requires
        avx2(),
        a0 < super::ADLER_MOD,
        b0 < super::ADLER_MOD,
    ensures
        (r.0 as nat, r.1 as nat) == adler_from(a0 as nat, b0 as nat, d@),
{
    let n = d.len();
    let mut a = a0;
    let mut b = b0;
    let mut i: usize = 0;
    proof {
        assert(d@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while n - i >= 32
        invariant
            avx2(),
            n == d@.len(),
            i <= n,
            a < super::ADLER_MOD,
            b < super::ADLER_MOD,
            (a as nat, b as nat) == adler_from(a0 as nat, b0 as nat, d@.subrange(0, i as int)),
        decreases n - i,
    {
        let rows = if (n - i) / 32 >= 1024 { 1024 } else { (n - i) / 32 };
        let (x, y) = block_avx2(a, b, d, i, rows);
        proof {
            lemma_adler_append(a0 as nat, b0 as nat, d@.subrange(0, i as int), d@.subrange(i as int, i + 32 * rows));
            assert(d@.subrange(0, i as int) + d@.subrange(i as int, i + 32 * rows) =~= d@.subrange(0, i + 32 * rows));
        }
        a = x;
        b = y;
        i = i + 32 * rows;
    }
    let tail = vstd::slice::slice_subrange(d, i, n);
    let (x, y) = super::adler32_update(a, b, tail);
    proof {
        lemma_adler_append(a0 as nat, b0 as nat, d@.subrange(0, i as int), tail@);
        assert(d@.subrange(0, i as int) + tail@ =~= d@);
    }
    (x, y)
}

} // verus!

/// The AArch64 kernel, on 64-byte rows of four NEON registers.
pub mod udot {

#[cfg(verus_only)]
use super::super::{adler_from, lemma_adler_append, lemma_lanes_bound, lsum};
#[cfg(verus_only)]
use super::{desc_ok, dot4, lemma_dot4_bound, lemma_row, ones_ok, row_inv};
use super::{block_sums, DESC64, ONES64};
use super::super::vudot::*;
use vstd::prelude::*;

verus! {

broadcast use group_vudot;

/// One block of `rows` rows of 64 bytes from `i`, with the dot-product extension (`udot`).
#[inline(always)]
fn block_udot(a: u32, b: u32, d: &[u8], i: usize, rows: usize) -> (r: (u32, u32))
    requires
        dotprod(),
        a < super::super::ADLER_MOD,
        b < super::super::ADLER_MOD,
        1 <= rows <= 1024,
        i + 64 * rows <= d@.len() <= usize::MAX,
    ensures
        r.0 < super::super::ADLER_MOD,
        r.1 < super::super::ADLER_MOD,
        (r.0 as nat, r.1 as nat) == adler_from(a as nat, b as nat, d@.subrange(i as int, i + 64 * rows)),
{
    let oa = ONES64;
    let da = DESC64;
    let ones = nb_load(&oa, 0);
    let desc = nb_load(&da, 0);
    proof {
        assert(oa@.subrange(0, 64) =~= oa@);
        assert(da@.subrange(0, 64) =~= da@);
    }
    let mut s1 = nd_zero();
    let mut s10 = nd_zero();
    let mut s2 = nd_zero();
    let mut r: usize = 0;
    proof {
        assert(d@.subrange(i as int, i as int) =~= Seq::<u8>::empty());
        assert(lsum(nd(s1), 16) == 0) by { lemma_lanes_bound(nd(s1), 16, 0); }
        assert(lsum(nd(s10), 16) == 0) by { lemma_lanes_bound(nd(s10), 16, 0); }
        assert(lsum(nd(s2), 16) == 0) by { lemma_lanes_bound(nd(s2), 16, 0); }
    }
    while r < rows
        invariant
            dotprod(),
            1 <= rows <= 1024,
            r <= rows,
            i + 64 * rows <= d@.len() <= usize::MAX,
            ones_ok(nb(ones), 64),
            desc_ok(nb(desc), 64),
            row_inv(nd(s1), nd(s10), nd(s2), d@.subrange(i as int, i + 64 * r), 64, r as nat),
        decreases rows - r,
    {
        assert(64 * r < 64 * rows) by (nonlinear_arith) requires r < rows;
        let j = i + 64 * r;
        let y = nb_load(d, j);
        let t10 = nd_add(&s10, &s1);
        // `udot` accumulates in place: four registers each, so the chain
        // through a register is one row apart.
        let t1 = nd_dot(&s1, &y, &ones);
        let t2 = nd_dot(&s2, &y, &desc);
        proof {
            lemma_row(nd(s1), nd(s10), nd(s2), nd(t1), nd(t10), nd(t2), d@.subrange(i as int, j as int),
                nb(y), nb(ones), nb(desc), 64, r as nat);
            assert(d@.subrange(i as int, j as int) + nb(y) =~= d@.subrange(i as int, i + 64 * (r + 1)));
        }
        s1 = t1;
        s10 = t10;
        s2 = t2;
        r = r + 1;
    }
    let v1 = nd_store(&s1);
    let v10 = nd_store(&s10);
    let v2 = nd_store(&s2);
    block_sums(a, b, &v1, &v10, &v2, Ghost(d@.subrange(i as int, i + 64 * rows)), 64, rows as u64)
}

/// **Adler-32 with the dot-product extension (`udot`)**: blocks of up to 1024 rows of 64 bytes,
/// then the portable code for the last 63 bytes or fewer.
#[inline(always)]
pub fn adler32_udot(a0: u32, b0: u32, d: &[u8]) -> (r: (u32, u32))
    requires
        dotprod(),
        a0 < super::super::ADLER_MOD,
        b0 < super::super::ADLER_MOD,
    ensures
        (r.0 as nat, r.1 as nat) == adler_from(a0 as nat, b0 as nat, d@),
{
    let n = d.len();
    let mut a = a0;
    let mut b = b0;
    let mut i: usize = 0;
    proof {
        assert(d@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while n - i >= 64
        invariant
            dotprod(),
            n == d@.len(),
            i <= n,
            a < super::super::ADLER_MOD,
            b < super::super::ADLER_MOD,
            (a as nat, b as nat) == adler_from(a0 as nat, b0 as nat, d@.subrange(0, i as int)),
        decreases n - i,
    {
        let rows = if (n - i) / 64 >= 1024 { 1024 } else { (n - i) / 64 };
        let (x, y) = block_udot(a, b, d, i, rows);
        proof {
            lemma_adler_append(a0 as nat, b0 as nat, d@.subrange(0, i as int), d@.subrange(i as int, i + 64 * rows));
            assert(d@.subrange(0, i as int) + d@.subrange(i as int, i + 64 * rows) =~= d@.subrange(0, i + 64 * rows));
        }
        a = x;
        b = y;
        i = i + 64 * rows;
    }
    let tail = vstd::slice::slice_subrange(d, i, n);
    let (x, y) = super::super::adler32_update(a, b, tail);
    proof {
        lemma_adler_append(a0 as nat, b0 as nat, d@.subrange(0, i as int), tail@);
        assert(d@.subrange(0, i as int) + tail@ =~= d@);
    }
    (x, y)
}

} // verus!

} // mod udot
