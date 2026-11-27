//! Samples to pixels: upsampling and color conversion.
use crate::idct::*;
use crate::num::*;
use crate::parse::*;
use crate::scan::*;
use crate::spec::*;
use crate::types::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use crate::prims::*;
use crate::work::Meter;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// `pl` holds the samples of component `c`: `rows` rows of `stride`.
pub open spec fn plane_is(pl: Seq<u8>, stride: int, rows: int, k: Coded, c: int) -> bool {
    &&& pl.len() == stride * rows
    &&& forall|r: int, x: int|
        0 <= r < rows && 0 <= x < stride ==> #[trigger] pat(pl, stride, r, x) as int == sample(k, c, r, x)
}

/// Row `r` of a plane starts at `r * stride`, and is inside the plane.
pub proof fn lemma_rowbase(r: int, rows: int, stride: int)
    requires
        0 <= r < rows,
        stride >= 0,
    ensures
        0 <= r * stride,
        r * stride + stride <= stride * rows,
{
    assert(0 <= r * stride && r * stride + stride <= stride * rows) by (nonlinear_arith)
        requires
            0 <= r < rows,
            stride >= 0,
    ;
}

pub proof fn lemma_div_lt(x: int, d: int, n: int)
    requires
        0 <= x < n * d,
        d > 0,
    ensures
        0 <= x / d < n,
{
    lemma_fundamental_div_mod(x, d);
    lemma_mod_bound(x, d);
    let q = x / d;
    assert(0 <= q < n) by (nonlinear_arith)
        requires
            0 <= x < n * d,
            d > 0,
            x == d * q + x % d,
            0 <= x % d < d,
    ;
}

/// What libjpeg's `h2v1_fancy_upsample` gives at output column `x` of a
/// row of samples.
pub open spec fn h2v1_at(row: Seq<u8>, x: int) -> int {
    let i = x / 2;
    let s = row[i] as int;
    if x % 2 == 0 {
        if i == 0 {
            s
        } else {
            (3 * s + row[i - 1] as int + 1) / 4
        }
    } else if i == row.len() - 1 {
        s
    } else {
        (3 * s + row[i + 1] as int + 2) / 4
    }
}

/// `3 * near + far` at column `i` of two rows.
pub open spec fn csum(nr: Seq<u8>, fr: Seq<u8>, i: int) -> int {
    3 * nr[i] as int + fr[i] as int
}

/// What `h2v2_fancy_upsample` gives at output column `x`, from the nearer
/// and the farther row of samples.
pub open spec fn h2v2_at(nr: Seq<u8>, fr: Seq<u8>, x: int) -> int {
    let i = x / 2;
    let s = csum(nr, fr, i);
    if x % 2 == 0 {
        if i == 0 {
            (4 * s + 8) / 16
        } else {
            (3 * s + csum(nr, fr, i - 1) + 8) / 16
        }
    } else if i == nr.len() - 1 {
        (4 * s + 7) / 16
    } else {
        (3 * s + csum(nr, fr, i + 1) + 7) / 16
    }
}

/// One output of the horizontal 2:1 filter.
fn h2v1_px(row: &[u8], x: usize) -> (r: u8)
    requires
        x / 2 < row@.len(),
    ensures
        r as int == h2v1_at(row@, x as int),
{
    let i = x / 2;
    let s = sget(row, i) as u32;
    let v = if x % 2 == 0 {
        if i == 0 {
            s
        } else {
            (3 * s + sget(row, i - 1) as u32 + 1) / 4
        }
    } else if i == row.len() - 1 {
        s
    } else {
        (3 * s + sget(row, i + 1) as u32 + 2) / 4
    };
    v as u8
}

/// Outputs `2 * i0 + 1` to `2 * (i0 + cnt)` of the horizontal 2:1 filter:
/// the two between each sample and the next. The loop has no branches
/// and its slices do not overlap, so compilers vectorize it.
#[inline(always)]
fn h2v1_run(row: &[u8], i0: usize, cnt: usize, out: &mut [u8], Tracked(mt): Tracked<&mut Meter>)
    requires
        i0 + cnt < row@.len(),
        2 * (i0 + cnt) < old(out)@.len(),
    ensures
        final(mt).n == old(mt).n + cnt,
        final(out)@.len() == old(out)@.len(),
        forall|j: int| 2 * i0 + 1 <= j <= 2 * (i0 + cnt) ==> (#[trigger] final(out)@[j]) as int == h2v1_at(row@, j),
        forall|j: int|
            0 <= j < final(out)@.len() && (j <= 2 * i0 || j > 2 * (i0 + cnt)) ==> (#[trigger] final(out)@[j]) == old(out)@[j],
{
    let n = out.len();
    let mut k: usize = 0;
    while k < cnt
        invariant
            mt.n == old(mt).n + k,
            k <= cnt,
            i0 + cnt < row@.len(),
            2 * (i0 + cnt) < out@.len(),
            out@.len() == n,
            out@.len() == old(out)@.len(),
            forall|j: int| 2 * i0 + 1 <= j <= 2 * (i0 + k) ==> (#[trigger] out@[j]) as int == h2v1_at(row@, j),
            forall|j: int|
                0 <= j < out@.len() && (j <= 2 * i0 || j > 2 * (i0 + k)) ==> (#[trigger] out@[j]) == old(out)@[j],
        decreases cnt - k,
    {
        let i = i0 + k;
        let a = sget(row, i) as u16;
        let b = sget(row, i + 1) as u16;
        assert((2 * i + 1) / 2 == i && (2 * i + 1) % 2 == 1 && (2 * i + 2) / 2 == i + 1 && (2 * i + 2) % 2 == 0);
        sset(out, 2 * i + 1, ((3 * a + b + 2) / 4) as u8);
        sset(out, 2 * i + 2, ((3 * b + a + 1) / 4) as u8);
        k += 1;
        proof {
            mt.n = mt.n + 1;
        }
    }
}

/// Outputs 1 to `2 * m` of the horizontal 2:1 filter, sixteen inputs at a
/// time; the last sixteen are done again from `m - 16` when `m` is not a
/// multiple of sixteen, so that no row ends one sample at a time.
#[inline(never)]
fn h2v1_mid(row: &[u8], m: usize, out: &mut [u8], Tracked(mt): Tracked<&mut Meter>)
    requires
        m < row@.len(),
        2 * m < old(out)@.len(),
    ensures
        final(mt).n <= old(mt).n + m + 16,
        final(out)@.len() == old(out)@.len(),
        forall|j: int| 1 <= j <= 2 * m ==> (#[trigger] final(out)@[j]) as int == h2v1_at(row@, j),
        forall|j: int|
            0 <= j < final(out)@.len() && (j == 0 || j > 2 * m) ==> (#[trigger] final(out)@[j]) == old(out)@[j],
{
    // `h2v1_mid_avx2` enables AVX2, which makes it unsafe to call, on x86-64;
    // `has_avx2` checked that the CPU has it.
    if verilith_simd::cpu::has_avx2() {
        #[cfg_attr(any(verus_only, not(target_arch = "x86_64")), allow(unused_unsafe))]
        unsafe { h2v1_mid_avx2(row, m, out, Tracked(mt)) };
        return ;
    }
    if m < 16 {
        h2v1_run(row, 0, m, out, Tracked(mt));
        return ;
    }
    let whole = m - m % 16;
    h2v1_run(row, 0, whole, out, Tracked(mt));
    if whole < m {
        h2v1_run(row, m - 16, 16, out, Tracked(mt));
    }
}

/// `h2v1_mid` compiled for AVX2, which vectorizes its loop twice as wide.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
#[cfg_attr(not(target_arch = "x86_64"), inline(always))]
fn h2v1_mid_avx2(row: &[u8], m: usize, out: &mut [u8], Tracked(mt): Tracked<&mut Meter>)
    requires
        m < row@.len(),
        2 * m < old(out)@.len(),
    ensures
        final(mt).n <= old(mt).n + m + 16,
        final(out)@.len() == old(out)@.len(),
        forall|j: int| 1 <= j <= 2 * m ==> (#[trigger] final(out)@[j]) as int == h2v1_at(row@, j),
        forall|j: int|
            0 <= j < final(out)@.len() && (j == 0 || j > 2 * m) ==> (#[trigger] final(out)@[j]) == old(out)@[j],
{
    if m < 16 {
        h2v1_run(row, 0, m, out, Tracked(mt));
        return ;
    }
    let whole = m - m % 16;
    h2v1_run(row, 0, whole, out, Tracked(mt));
    if whole < m {
        h2v1_run(row, m - 16, 16, out, Tracked(mt));
    }
}

/// One output of the 2:1 filter in both directions.
fn h2v2_px(nr: &[u8], fr: &[u8], x: usize) -> (r: u8)
    requires
        nr@.len() == fr@.len(),
        x / 2 < nr@.len(),
    ensures
        r as int == h2v2_at(nr@, fr@, x as int),
{
    let i = x / 2;
    let s = 3 * sget(nr, i) as u32 + sget(fr, i) as u32;
    let v = if x % 2 == 0 {
        if i == 0 {
            (4 * s + 8) / 16
        } else {
            (3 * s + 3 * sget(nr, i - 1) as u32 + sget(fr, i - 1) as u32 + 8) / 16
        }
    } else if i == nr.len() - 1 {
        (4 * s + 7) / 16
    } else {
        (3 * s + 3 * sget(nr, i + 1) as u32 + sget(fr, i + 1) as u32 + 7) / 16
    };
    v as u8
}

/// Outputs `2 * i0 + 1` to `2 * (i0 + cnt)` of the 2:1 filter in both
/// directions.
#[inline(always)]
fn h2v2_run(nr: &[u8], fr: &[u8], i0: usize, cnt: usize, out: &mut [u8], Tracked(mt): Tracked<&mut Meter>)
    requires
        nr@.len() == fr@.len(),
        i0 + cnt < nr@.len(),
        2 * (i0 + cnt) < old(out)@.len(),
    ensures
        final(mt).n == old(mt).n + cnt,
        final(out)@.len() == old(out)@.len(),
        forall|j: int| 2 * i0 + 1 <= j <= 2 * (i0 + cnt) ==> (#[trigger] final(out)@[j]) as int == h2v2_at(nr@, fr@, j),
        forall|j: int|
            0 <= j < final(out)@.len() && (j <= 2 * i0 || j > 2 * (i0 + cnt)) ==> (#[trigger] final(out)@[j]) == old(out)@[j],
{
    let n = out.len();
    let mut k: usize = 0;
    while k < cnt
        invariant
            mt.n == old(mt).n + k,
            k <= cnt,
            nr@.len() == fr@.len(),
            i0 + cnt < nr@.len(),
            2 * (i0 + cnt) < out@.len(),
            out@.len() == n,
            out@.len() == old(out)@.len(),
            forall|j: int| 2 * i0 + 1 <= j <= 2 * (i0 + k) ==> (#[trigger] out@[j]) as int == h2v2_at(nr@, fr@, j),
            forall|j: int|
                0 <= j < out@.len() && (j <= 2 * i0 || j > 2 * (i0 + k)) ==> (#[trigger] out@[j]) == old(out)@[j],
        decreases cnt - k,
    {
        let i = i0 + k;
        let a = 3 * sget(nr, i) as u32 + sget(fr, i) as u32;
        let b = 3 * sget(nr, i + 1) as u32 + sget(fr, i + 1) as u32;
        assert((2 * i + 1) / 2 == i && (2 * i + 1) % 2 == 1 && (2 * i + 2) / 2 == i + 1 && (2 * i + 2) % 2 == 0);
        assert(a == csum(nr@, fr@, i as int) && b == csum(nr@, fr@, i + 1));
        sset(out, 2 * i + 1, ((3 * a + b + 7) / 16) as u8);
        sset(out, 2 * i + 2, ((3 * b + a + 8) / 16) as u8);
        k += 1;
        proof {
            mt.n = mt.n + 1;
        }
    }
}

/// Outputs 1 to `2 * m` of the 2:1 filter in both directions, sixteen
/// inputs at a time; the last sixteen are done again from `m - 16` when
/// `m` is not a multiple of sixteen, so that no row ends one sample at a
/// time.
#[inline(never)]
fn h2v2_mid(nr: &[u8], fr: &[u8], m: usize, out: &mut [u8], Tracked(mt): Tracked<&mut Meter>)
    requires
        nr@.len() == fr@.len(),
        m < nr@.len(),
        2 * m < old(out)@.len(),
    ensures
        final(mt).n <= old(mt).n + m + 16,
        final(out)@.len() == old(out)@.len(),
        forall|j: int| 1 <= j <= 2 * m ==> (#[trigger] final(out)@[j]) as int == h2v2_at(nr@, fr@, j),
        forall|j: int|
            0 <= j < final(out)@.len() && (j == 0 || j > 2 * m) ==> (#[trigger] final(out)@[j]) == old(out)@[j],
{
    // `h2v2_mid_avx2` enables AVX2, which makes it unsafe to call, on x86-64;
    // `has_avx2` checked that the CPU has it.
    if verilith_simd::cpu::has_avx2() {
        #[cfg_attr(any(verus_only, not(target_arch = "x86_64")), allow(unused_unsafe))]
        unsafe { h2v2_mid_avx2(nr, fr, m, out, Tracked(mt)) };
        return ;
    }
    if m < 16 {
        h2v2_run(nr, fr, 0, m, out, Tracked(mt));
        return ;
    }
    let whole = m - m % 16;
    h2v2_run(nr, fr, 0, whole, out, Tracked(mt));
    if whole < m {
        h2v2_run(nr, fr, m - 16, 16, out, Tracked(mt));
    }
}

/// `h2v2_mid` compiled for AVX2, which vectorizes its loop twice as wide.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
#[cfg_attr(not(target_arch = "x86_64"), inline(always))]
fn h2v2_mid_avx2(nr: &[u8], fr: &[u8], m: usize, out: &mut [u8], Tracked(mt): Tracked<&mut Meter>)
    requires
        nr@.len() == fr@.len(),
        m < nr@.len(),
        2 * m < old(out)@.len(),
    ensures
        final(mt).n <= old(mt).n + m + 16,
        final(out)@.len() == old(out)@.len(),
        forall|j: int| 1 <= j <= 2 * m ==> (#[trigger] final(out)@[j]) as int == h2v2_at(nr@, fr@, j),
        forall|j: int|
            0 <= j < final(out)@.len() && (j == 0 || j > 2 * m) ==> (#[trigger] final(out)@[j]) == old(out)@[j],
{
    if m < 16 {
        h2v2_run(nr, fr, 0, m, out, Tracked(mt));
        return ;
    }
    let whole = m - m % 16;
    h2v2_run(nr, fr, 0, whole, out, Tracked(mt));
    if whole < m {
        h2v2_run(nr, fr, m - 16, 16, out, Tracked(mt));
    }
}

/// The vertical 2:1 filter along a row: `(3 * near + far + bias) / 4`.
#[inline(never)]
fn v_mid(nr: &[u8], fr: &[u8], w: usize, bias: u32, out: &mut [u8], Tracked(mt): Tracked<&mut Meter>)
    requires
        w <= nr@.len(),
        w <= fr@.len(),
        w <= old(out)@.len(),
        bias <= 2,
    ensures
        final(mt).n == old(mt).n + w,
        final(out)@.len() == old(out)@.len(),
        forall|j: int| 0 <= j < w ==> (#[trigger] final(out)@[j]) as int == (csum(nr@, fr@, j) + bias) / 4,
        forall|j: int| w <= j < final(out)@.len() ==> (#[trigger] final(out)@[j]) == old(out)@[j],
{
    let n = out.len();
    let mut x: usize = 0;
    while x < w
        invariant
            mt.n == old(mt).n + x,
            x <= w,
            w <= nr@.len(),
            w <= fr@.len(),
            w <= out@.len(),
            bias <= 2,
            out@.len() == n,
            out@.len() == old(out)@.len(),
            forall|j: int| 0 <= j < x ==> (#[trigger] out@[j]) as int == (csum(nr@, fr@, j) + bias) / 4,
            forall|j: int| x <= j < out@.len() ==> (#[trigger] out@[j]) == old(out)@[j],
        decreases w - x,
    {
        sset(out, x, ((3 * sget(nr, x) as u32 + sget(fr, x) as u32 + bias) / 4) as u8);
        x += 1;
        proof {
            mt.n = mt.n + 1;
        }
    }
}

/// What `up_row` needs of its arguments.
pub open spec fn up_pre(
    pl: Seq<u8>,
    stride: usize,
    pw: usize,
    ph: usize,
    hs: usize,
    vs: usize,
    y: usize,
    w: usize,
    rows: int,
    k: Coded,
    c: int,
) -> bool {
    &&& plane_is(pl, stride as int, rows, k, c)
    &&& pw == dw(k.f, c)
    &&& ph == dh(k.f, c)
    &&& hs == maxh(k.f) / k.f.comps[c].h as int
    &&& vs == maxv(k.f) / k.f.comps[c].v as int
    &&& 1 <= hs <= 4
    &&& 1 <= vs <= 4
    &&& 1 <= pw <= stride
    &&& 1 <= ph <= rows
    &&& w <= pw * hs
    &&& y < ph * vs
}

fn up_same(
    pl: &Vec<u8>,
    stride: usize,
    pw: usize,
    ph: usize,
    hs: usize,
    vs: usize,
    y: usize,
    w: usize,
    out: &mut Vec<u8>,
    Ghost(rows): Ghost<int>,
    Ghost(k): Ghost<Coded>,
    Ghost(c): Ghost<int>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        up_pre(pl@, stride, pw, ph, hs, vs, y, w, rows, k, c),
        old(out).len() == w,
        hs == 1 && vs == 1,
    ensures
        final(mt).n <= old(mt).n + 2 * w + 32,
        final(out).len() == w,
        forall|x: int| 0 <= x < w ==> (#[trigger] final(out)[x]) as int == upsampled(k, c, y as int, x),
{
    hide(sample);
    let ghost st = stride as int;
    let ghost yi = y as int;
    proof {
        lemma_div_lt(yi, vs as int, ph as int);
        assert(pl.len() == st * rows);
    }
    proof {
        lemma_rowbase(yi, rows, st);
    }
    let r = y * stride;
    let row = slice_subrange(pl.as_slice(), r, r + w);
    out.as_mut_slice().copy_from_slice(row);
    proof {
        mt.n = mt.n + w as nat;
    }
    proof {
        assert forall|x: int| 0 <= x < w implies (#[trigger] out[x]) as int == upsampled(k, c, yi, x) by {
            assert(out[x] == pl[r + x]);
            assert(pat(pl@, st, yi, x) == pl[r + x]);
            assert(sample(k, c, yi, x) == pl[r + x] as int);
            assert(yi / 1 == yi && x / 1 == x);
        }
    }
}

fn up_h2v1(
    pl: &Vec<u8>,
    stride: usize,
    pw: usize,
    ph: usize,
    hs: usize,
    vs: usize,
    y: usize,
    w: usize,
    out: &mut Vec<u8>,
    Ghost(rows): Ghost<int>,
    Ghost(k): Ghost<Coded>,
    Ghost(c): Ghost<int>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        up_pre(pl@, stride, pw, ph, hs, vs, y, w, rows, k, c),
        old(out).len() == w,
        hs == 2 && vs == 1 && pw > 2,
    ensures
        final(mt).n <= old(mt).n + 2 * w + 32,
        final(out).len() == w,
        forall|x: int| 0 <= x < w ==> (#[trigger] final(out)[x]) as int == upsampled(k, c, y as int, x),
{
    hide(sample);
    let ghost st = stride as int;
    let ghost yi = y as int;
    proof {
        lemma_div_lt(yi, vs as int, ph as int);
        assert(pl.len() == st * rows);
    }
    proof {
        lemma_rowbase(yi, rows, st);
    }
    let r = y * stride;
    let row = slice_subrange(pl.as_slice(), r, r + pw);
    proof {
        assert forall|i: int| 0 <= i < pw implies (#[trigger] row@[i]) as int == sample(k, c, yi, i) by {
            assert(row@[i] == pl[r + i]);
            assert(pat(pl@, st, yi, i) == pl[r + i]);
        }
        assert forall|x: int| 0 <= x < w implies h2v1_at(row@, x) == upsampled(k, c, yi, x) by {
            let i = x / 2;
            assert(0 <= i < pw);
            assert(row@[i] as int == sample(k, c, yi, i));
            if i > 0 {
                assert(row@[i - 1] as int == sample(k, c, yi, i - 1));
            }
            if i + 1 < pw {
                assert(row@[i + 1] as int == sample(k, c, yi, i + 1));
            }
        }
    }
    if w > 0 {
        vset(out, 0, h2v1_px(row, 0));
        let m = if (w - 1) / 2 < pw - 1 {
            (w - 1) / 2
        } else {
            pw - 1
        };
        h2v1_mid(row, m, out.as_mut_slice(), Tracked(mt));
        let mut x: usize = 2 * m + 1;
        while x < w
            invariant
                x <= w,
                mt.n <= old(mt).n + m + 16 + x - (2 * m + 1),
                2 * m + 1 <= x,
                out.len() == w,
                w <= pw * 2,
                row@.len() == pw,
                forall|j: int| 0 <= j < x ==> (#[trigger] out[j]) as int == h2v1_at(row@, j),
            decreases w - x,
        {
            vset(out, x, h2v1_px(row, x));
            x += 1;
            proof {
                mt.n = mt.n + 1;
            }
        }
    }
}

fn up_v2(
    pl: &Vec<u8>,
    stride: usize,
    pw: usize,
    ph: usize,
    hs: usize,
    vs: usize,
    y: usize,
    w: usize,
    out: &mut Vec<u8>,
    Ghost(rows): Ghost<int>,
    Ghost(k): Ghost<Coded>,
    Ghost(c): Ghost<int>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        up_pre(pl@, stride, pw, ph, hs, vs, y, w, rows, k, c),
        old(out).len() == w,
        (hs == 1 && vs == 2) || (hs == 2 && vs == 2 && pw > 2),
    ensures
        final(mt).n <= old(mt).n + 2 * w + 32,
        final(out).len() == w,
        forall|x: int| 0 <= x < w ==> (#[trigger] final(out)[x]) as int == upsampled(k, c, y as int, x),
{
    hide(sample);
    let ghost st = stride as int;
    let ghost yi = y as int;
    proof {
        lemma_div_lt(yi, vs as int, ph as int);
        assert(pl.len() == st * rows);
    }
    let ny = y / 2;
    let fy = if y % 2 == 0 {
        if y / 2 >= 1 {
            y / 2 - 1
        } else {
            0
        }
    } else if y / 2 + 1 <= ph - 1 {
        y / 2 + 1
    } else {
        ph - 1
    };
    let ghost ni = ny as int;
    let ghost fi = fy as int;
    proof {
        lemma_rowbase(ni, rows, st);
        lemma_rowbase(fi, rows, st);
        assert(fi == far_row(k, c, yi));
    }
    let near = ny * stride;
    let far = fy * stride;
    let nr = slice_subrange(pl.as_slice(), near, near + pw);
    let fr = slice_subrange(pl.as_slice(), far, far + pw);
    proof {
        assert forall|i: int| 0 <= i < pw implies csum(nr@, fr@, i) == colsum(k, c, yi, i) by {
            assert(nr@[i] == pl[near + i]);
            assert(fr@[i] == pl[far + i]);
            assert(pat(pl@, st, ni, i) == pl[near + i]);
            assert(pat(pl@, st, fi, i) == pl[far + i]);
        }
    }
    if hs == 1 {
        let bias = 1 + (y % 2) as u32;
        assert(w <= pw) by (nonlinear_arith)
            requires
                w <= pw * hs,
                hs == 1,
        ;
        v_mid(nr, fr, w, bias, out.as_mut_slice(), Tracked(mt));
        proof {
            assert forall|x: int| 0 <= x < w implies (#[trigger] out[x]) as int == upsampled(k, c, yi, x) by {
                assert(csum(nr@, fr@, x) == colsum(k, c, yi, x));
            }
        }
    } else {
        proof {
            assert forall|x: int| 0 <= x < w implies h2v2_at(nr@, fr@, x) == upsampled(k, c, yi, x) by {
                let i = x / 2;
                assert(0 <= i < pw);
                assert(csum(nr@, fr@, i) == colsum(k, c, yi, i));
                if i > 0 {
                    assert(csum(nr@, fr@, i - 1) == colsum(k, c, yi, i - 1));
                }
                if i + 1 < pw {
                    assert(csum(nr@, fr@, i + 1) == colsum(k, c, yi, i + 1));
                }
            }
        }
        if w > 0 {
            vset(out, 0, h2v2_px(nr, fr, 0));
            let m = if (w - 1) / 2 < pw - 1 {
                (w - 1) / 2
            } else {
                pw - 1
            };
            h2v2_mid(nr, fr, m, out.as_mut_slice(), Tracked(mt));
            let mut x: usize = 2 * m + 1;
            while x < w
                invariant
                    x <= w,
                    mt.n <= old(mt).n + m + 16 + x - (2 * m + 1),
                    2 * m + 1 <= x,
                    out.len() == w,
                    w <= pw * 2,
                    nr@.len() == pw,
                    fr@.len() == pw,
                    forall|j: int| 0 <= j < x ==> (#[trigger] out[j]) as int == h2v2_at(nr@, fr@, j),
                decreases w - x,
            {
                vset(out, x, h2v2_px(nr, fr, x));
                x += 1;
                proof {
                    mt.n = mt.n + 1;
                }
            }
        }
    }
}

fn up_rep(
    pl: &Vec<u8>,
    stride: usize,
    pw: usize,
    ph: usize,
    hs: usize,
    vs: usize,
    y: usize,
    w: usize,
    out: &mut Vec<u8>,
    Ghost(rows): Ghost<int>,
    Ghost(k): Ghost<Coded>,
    Ghost(c): Ghost<int>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        up_pre(pl@, stride, pw, ph, hs, vs, y, w, rows, k, c),
        old(out).len() == w,
        !(hs == 1 && vs == 1) && !(hs == 2 && vs == 1 && pw > 2) && !((hs == 1 && vs == 2) || (hs == 2 && vs == 2 && pw > 2)),
    ensures
        final(mt).n <= old(mt).n + 2 * w + 32,
        final(out).len() == w,
        forall|x: int| 0 <= x < w ==> (#[trigger] final(out)[x]) as int == upsampled(k, c, y as int, x),
{
    hide(sample);
    let ghost st = stride as int;
    let ghost yi = y as int;
    proof {
        lemma_div_lt(yi, vs as int, ph as int);
        assert(pl.len() == st * rows);
    }
    let ry = y / vs;
    let ghost ri = ry as int;
    proof {
        assert(0 <= ri < ph);
        assert(ri < rows);
        lemma_rowbase(ri, rows, st);
        assert(st * rows == pl.len());
    }
    let r = ry * stride;
    let mut x: usize = 0;
    while x < w
        invariant
            x <= w,
            mt.n == old(mt).n + x,
            out.len() == w,
            w <= pw * hs,
            1 <= hs <= 4,
            1 <= pw <= stride,
            pw == dw(k.f, c),
            r == ri * st,
            r + st <= pl.len(),
            0 <= ri < rows,
            ri == yi / (vs as int),
            yi == y,
            !(hs == 2 && vs == 1 && pw > 2),
            !(hs == 1 && vs == 2),
            !(hs == 2 && vs == 2 && pw > 2),
            st == stride,
            plane_is(pl@, st, rows, k, c),
            hs == maxh(k.f) / k.f.comps[c].h as int,
            vs == maxv(k.f) / k.f.comps[c].v as int,
            forall|j: int| 0 <= j < x ==> (#[trigger] out[j]) as int == upsampled(k, c, yi, j),
        decreases w - x,
    {
        proof {
            lemma_div_lt(x as int, hs as int, pw as int);
        }
        let i = x / hs;
        assert(pat(pl@, st, ri, i as int) == pl[r + i]);
        vset(out, x, vget(pl, r + i));
        x += 1;
        proof {
            mt.n = mt.n + 1;
        }
    }
}

/// Row `y` of a component brought up to the frame's resolution: `w`
/// values in `out`. `pl` is the component's plane, `stride` wide, of which
/// `dw` by `dh` samples are image; `hs` and `vs` are the ratios to undo.
pub fn up_row(
    pl: &Vec<u8>,
    stride: usize,
    pw: usize,
    ph: usize,
    hs: usize,
    vs: usize,
    y: usize,
    w: usize,
    out: &mut Vec<u8>,
    Ghost(rows): Ghost<int>,
    Ghost(k): Ghost<Coded>,
    Ghost(c): Ghost<int>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        up_pre(pl@, stride, pw, ph, hs, vs, y, w, rows, k, c),
        old(out).len() == w,
    ensures
        final(mt).n <= old(mt).n + 2 * w + 32,
        final(out).len() == w,
        forall|x: int| 0 <= x < w ==> (#[trigger] final(out)[x]) as int == upsampled(k, c, y as int, x),
{
    if hs == 1 && vs == 1 {
        up_same(pl, stride, pw, ph, hs, vs, y, w, out, Ghost(rows), Ghost(k), Ghost(c), Tracked(mt));
    } else if hs == 2 && vs == 1 && pw > 2 {
        up_h2v1(pl, stride, pw, ph, hs, vs, y, w, out, Ghost(rows), Ghost(k), Ghost(c), Tracked(mt));
    } else if (hs == 1 && vs == 2) || (hs == 2 && vs == 2 && pw > 2) {
        up_v2(pl, stride, pw, ph, hs, vs, y, w, out, Ghost(rows), Ghost(k), Ghost(c), Tracked(mt));
    } else {
        up_rep(pl, stride, pw, ph, hs, vs, y, w, out, Ghost(rows), Ghost(k), Ghost(c), Tracked(mt));
    }
}

#[inline(always)]
pub fn clamp8(x: i32) -> (r: u8)
    ensures
        r as int == clamp(x as int, 0, 255),
{
    if x < 0 {
        0
    } else if x > 255 {
        255
    } else {
        x as u8
    }
}

/// Channel `ch` of the pixel made from one sample of each component.
pub open spec fn chan(color: Color, l: int, cb: int, cr: int, ch: int) -> int {
    match color {
        Color::Gray => l,
        Color::Rgb => if ch == 0 {
            l
        } else if ch == 1 {
            cb
        } else {
            cr
        },
        Color::YCbCr => if ch == 0 {
            ycc_r(l, cr)
        } else if ch == 1 {
            ycc_g(l, cb, cr)
        } else {
            ycc_b(l, cb)
        },
    }
}

/// `ycc_row`'s first pixels, sixteen at a time with NEON (on x86-64, with
/// the SSE implementation of the NEON wrappers, for which this function
/// enables SSE4.1 and SSSE3): returns how many it converted, all but the
/// last `w % 16`.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "sse4.1,ssse3"))]
#[cfg_attr(not(target_arch = "x86_64"), inline(always))]
fn ycc_run(yr: &[u8], cbr: &[u8], crr: &[u8], w: usize, out: &mut [u8], o: usize, Tracked(mt): Tracked<&mut Meter>) -> (x: usize)
    requires
        verilith_simd::neon::neon(),
        yr@.len() == w,
        cbr@.len() == w,
        crr@.len() == w,
        o + 3 * w <= old(out)@.len(),
    ensures
        x <= w,
        final(mt).n <= old(mt).n + x,
        final(out)@.len() == old(out)@.len(),
        forall|i: int|
            o <= i < o + 3 * x ==> (#[trigger] final(out)@[i]) as int == chan(
                Color::YCbCr,
                yr@[(i - o) / 3] as int,
                cbr@[(i - o) / 3] as int,
                crr@[(i - o) / 3] as int,
                (i - o) % 3,
            ),
        forall|i: int| 0 <= i < o || o + 3 * x <= i < final(out)@.len() ==> (#[trigger] final(out)@[i]) == old(out)@[i],
{
    let n = out.len();
    let mut x: usize = 0;
    while w - x >= 16
        invariant
            x <= w,
            mt.n <= old(mt).n + x,
            verilith_simd::neon::neon(),
            yr@.len() == w,
            cbr@.len() == w,
            crr@.len() == w,
            o + 3 * w <= out@.len(),
            out@.len() == n,
            out@.len() == old(out)@.len(),
            forall|i: int|
                o <= i < o + 3 * x ==> (#[trigger] out@[i]) as int == chan(
                    Color::YCbCr,
                    yr@[(i - o) / 3] as int,
                    cbr@[(i - o) / 3] as int,
                    crr@[(i - o) / 3] as int,
                    (i - o) % 3,
                ),
            forall|i: int| 0 <= i < o || o + 3 * x <= i < out@.len() ==> (#[trigger] out@[i]) == old(out)@[i],
        decreases w - x,
    {
        let ghost out0 = out@;
        let p = o + 3 * x;
        crate::color_neon::ycc16(yr, cbr, crr, x, out, p);
        proof {
            assert forall|i: int| o <= i < o + 3 * (x + 16) implies (#[trigger] out@[i]) as int == chan(
                Color::YCbCr,
                yr@[(i - o) / 3] as int,
                cbr@[(i - o) / 3] as int,
                crr@[(i - o) / 3] as int,
                (i - o) % 3,
            ) by {
                if i < p {
                    assert(out@[i] == out0[i]);
                } else {
                    let j = i - p;
                    assert(i - o == 3 * x + j);
                    assert((i - o) / 3 == x + j / 3 && (i - o) % 3 == j % 3);
                }
            }
        }
        x += 16;
        proof {
            mt.n = mt.n + 1;
        }
    }
    x
}

/// A row of YCbCr to red, green, blue at `out[o..]`. The slices do not
/// overlap, so compilers vectorize the loop.
#[inline(never)]
pub fn ycc_row(yr: &[u8], cbr: &[u8], crr: &[u8], w: usize, out: &mut [u8], o: usize, Tracked(mt): Tracked<&mut Meter>)
    requires
        yr@.len() == w,
        cbr@.len() == w,
        crr@.len() == w,
        o + 3 * w <= old(out)@.len(),
    ensures
        final(mt).n <= old(mt).n + w,
        final(out)@.len() == old(out)@.len(),
        forall|i: int|
            o <= i < o + 3 * w ==> (#[trigger] final(out)@[i]) as int == chan(
                Color::YCbCr,
                yr@[(i - o) / 3] as int,
                cbr@[(i - o) / 3] as int,
                crr@[(i - o) / 3] as int,
                (i - o) % 3,
            ),
        forall|i: int|
            0 <= i < o || o + 3 * w <= i < final(out)@.len() ==> (#[trigger] final(out)@[i]) == old(out)@[i],
{
    // With AVX2 the compiler's vectorized loop beats the 16-pixel kernel.
    // `ycc_row_avx2` enables AVX2, which makes it unsafe to call, on
    // x86-64; `has_avx2` checked that the CPU has it.
    if verilith_simd::cpu::has_avx2() {
        #[cfg_attr(any(verus_only, not(target_arch = "x86_64")), allow(unused_unsafe))]
        unsafe { ycc_row_avx2(yr, cbr, crr, w, out, o, Tracked(mt)) };
        return ;
    }
    let mut x: usize = 0;
    // `ycc_run` enables SSE4.1 and SSSE3, which makes it unsafe to call, on
    // x86-64; `has_neon_sse` checked that the CPU has them.
    if verilith_simd::neon::has_neon_sse() {
        #[cfg_attr(any(verus_only, not(target_arch = "x86_64")), allow(unused_unsafe))]
        let k = unsafe { ycc_run(yr, cbr, crr, w, out, o, Tracked(mt)) };
        x = k;
    }
    ycc_from(yr, cbr, crr, w, out, o, x, Tracked(mt));
}

/// `ycc_from` from the start of the row, compiled for AVX2.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
#[cfg_attr(not(target_arch = "x86_64"), inline(always))]
fn ycc_row_avx2(yr: &[u8], cbr: &[u8], crr: &[u8], w: usize, out: &mut [u8], o: usize, Tracked(mt): Tracked<&mut Meter>)
    requires
        yr@.len() == w,
        cbr@.len() == w,
        crr@.len() == w,
        o + 3 * w <= old(out)@.len(),
    ensures
        final(mt).n <= old(mt).n + w,
        final(out)@.len() == old(out)@.len(),
        forall|i: int|
            o <= i < o + 3 * w ==> (#[trigger] final(out)@[i]) as int == chan(
                Color::YCbCr,
                yr@[(i - o) / 3] as int,
                cbr@[(i - o) / 3] as int,
                crr@[(i - o) / 3] as int,
                (i - o) % 3,
            ),
        forall|i: int|
            0 <= i < o || o + 3 * w <= i < final(out)@.len() ==> (#[trigger] final(out)@[i]) == old(out)@[i],
{
    ycc_from(yr, cbr, crr, w, out, o, 0, Tracked(mt));
}

/// The rest of `ycc_row`, from pixel `x0` on, the pixels before it done.
#[inline(always)]
fn ycc_from(yr: &[u8], cbr: &[u8], crr: &[u8], w: usize, out: &mut [u8], o: usize, x0: usize, Tracked(mt): Tracked<&mut Meter>)
    requires
        yr@.len() == w,
        cbr@.len() == w,
        crr@.len() == w,
        o + 3 * w <= old(out)@.len(),
        x0 <= w,
        forall|i: int|
            o <= i < o + 3 * x0 ==> (#[trigger] old(out)@[i]) as int == chan(
                Color::YCbCr,
                yr@[(i - o) / 3] as int,
                cbr@[(i - o) / 3] as int,
                crr@[(i - o) / 3] as int,
                (i - o) % 3,
            ),
    ensures
        final(mt).n <= old(mt).n + (w - x0),
        final(out)@.len() == old(out)@.len(),
        forall|i: int|
            o <= i < o + 3 * w ==> (#[trigger] final(out)@[i]) as int == chan(
                Color::YCbCr,
                yr@[(i - o) / 3] as int,
                cbr@[(i - o) / 3] as int,
                crr@[(i - o) / 3] as int,
                (i - o) % 3,
            ),
        forall|i: int|
            0 <= i < o || o + 3 * w <= i < final(out)@.len() ==> (#[trigger] final(out)@[i]) == old(out)@[i],
{
    let n = out.len();
    let mut x = x0;
    while x < w
        invariant
            x <= w,
            x0 <= x,
            mt.n <= old(mt).n + (x - x0),
            yr@.len() == w,
            cbr@.len() == w,
            crr@.len() == w,
            o + 3 * w <= out@.len(),
            out@.len() == n,
            out@.len() == old(out)@.len(),
            forall|i: int|
                o <= i < o + 3 * x ==> (#[trigger] out@[i]) as int == chan(
                    Color::YCbCr,
                    yr@[(i - o) / 3] as int,
                    cbr@[(i - o) / 3] as int,
                    crr@[(i - o) / 3] as int,
                    (i - o) % 3,
                ),
            forall|i: int| 0 <= i < o || o + 3 * x <= i < out@.len() ==> (#[trigger] out@[i]) == old(out)@[i],
        decreases w - x,
    {
        let l = sget(yr, x) as i32;
        let cb = sget(cbr, x) as i32 - 128;
        let cr = sget(crr, x) as i32 - 128;
        proof {
            lemma_shr16((91881 * cr + 32768) as i32);
            lemma_shr16((-22554 * cb - 46802 * cr + 32768) as i32);
            lemma_shr16((116130 * cb + 32768) as i32);
        }
        sset(out, o + 3 * x, clamp8(l + ((91881 * cr + 32768) >> 16)));
        sset(out, o + 3 * x + 1, clamp8(l + ((-22554 * cb - 46802 * cr + 32768) >> 16)));
        sset(out, o + 3 * x + 2, clamp8(l + ((116130 * cb + 32768) >> 16)));
        x += 1;
        proof {
            mt.n = mt.n + 1;
        }
    }
}

/// A row of three components, interleaved, at `out[o..]`.
pub fn rgb_row(r0: &Vec<u8>, r1: &Vec<u8>, r2: &Vec<u8>, w: usize, out: &mut [u8], o: usize, Tracked(mt): Tracked<&mut Meter>)
    requires
        r0.len() == w,
        r1.len() == w,
        r2.len() == w,
        o + 3 * w <= old(out)@.len(),
    ensures
        final(mt).n == old(mt).n + w,
        final(out)@.len() == old(out)@.len(),
        forall|i: int|
            o <= i < o + 3 * w ==> (#[trigger] final(out)@[i]) as int == chan(
                Color::Rgb,
                r0[(i - o) / 3] as int,
                r1[(i - o) / 3] as int,
                r2[(i - o) / 3] as int,
                (i - o) % 3,
            ),
        forall|i: int| 0 <= i < o || o + 3 * w <= i < final(out)@.len() ==> (#[trigger] final(out)@[i]) == old(out)@[i],
{
    let n = out.len();
    let mut x: usize = 0;
    while x < w
        invariant
            x <= w,
            mt.n == old(mt).n + x,
            r0.len() == w,
            r1.len() == w,
            r2.len() == w,
            o + 3 * w <= out@.len(),
            out@.len() == old(out)@.len(),
            out@.len() == n,
            forall|i: int|
                o <= i < o + 3 * x ==> (#[trigger] out@[i]) as int == chan(
                    Color::Rgb,
                    r0[(i - o) / 3] as int,
                    r1[(i - o) / 3] as int,
                    r2[(i - o) / 3] as int,
                    (i - o) % 3,
                ),
            forall|i: int| 0 <= i < o || o + 3 * x <= i < out@.len() ==> (#[trigger] out@[i]) == old(out)@[i],
        decreases w - x,
    {
        sset(out, o + 3 * x, vget(r0, x));
        sset(out, o + 3 * x + 1, vget(r1, x));
        sset(out, o + 3 * x + 2, vget(r2, x));
        x += 1;
        proof {
            mt.n = mt.n + 1;
        }
    }
}

/// A row of one component at `out[o..]`.
pub fn gray_row(r0: &Vec<u8>, w: usize, out: &mut [u8], o: usize, Tracked(mt): Tracked<&mut Meter>)
    requires
        r0.len() == w,
        o + w <= old(out)@.len(),
    ensures
        final(mt).n == old(mt).n + w,
        final(out)@.len() == old(out)@.len(),
        forall|i: int| o <= i < o + w ==> (#[trigger] final(out)@[i]) == r0[i - o],
        forall|i: int| 0 <= i < o || o + w <= i < final(out)@.len() ==> (#[trigger] final(out)@[i]) == old(out)@[i],
{
    let n = out.len();
    let mut x: usize = 0;
    while x < w
        invariant
            x <= w,
            mt.n == old(mt).n + x,
            r0.len() == w,
            o + w <= out@.len(),
            out@.len() == old(out)@.len(),
            out@.len() == n,
            forall|i: int| o <= i < o + x ==> (#[trigger] out@[i]) == r0[i - o],
            forall|i: int| 0 <= i < o || o + x <= i < out@.len() ==> (#[trigger] out@[i]) == old(out)@[i],
        decreases w - x,
    {
        sset(out, o + x, vget(r0, x));
        x += 1;
        proof {
            mt.n = mt.n + 1;
        }
    }
}

} // verus!


