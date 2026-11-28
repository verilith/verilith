//! The lossy encoder's choices for one macroblock: the source in the
//! scratch block's layout, the 16x16 luma and chroma modes with the least
//! squared error, the forward transforms, and quantization. Nothing here
//! needs to be right for the file to decode as the encoder says; these are
//! the encoder's decisions, and only their ranges are proven.
use crate::vp8dsp::{pred_block, BPS};
use crate::vp8frame::*;
use vstd::prelude::*;

verus! {

proof fn lemma_sar(x: i32)
    ensures
        (x >> 1u32) as int == (x as int) / 2,
        (x >> 4u32) as int == (x as int) / 16,
        (x >> 9u32) as int == (x as int) / 512,
        (x >> 16u32) as int == (x as int) / 0x1_0000,
{
    assert(mul(x >> 1u32, 2) <= x && x <= add(mul(x >> 1u32, 2), 1)) by (bit_vector);
    assert(mul(x >> 4u32, 16) <= x && x <= add(mul(x >> 4u32, 16), 15)) by (bit_vector);
    assert(mul(x >> 9u32, 512) <= x && x <= add(mul(x >> 9u32, 512), 511)) by (bit_vector);
    assert(mul(x >> 16u32, 0x1_0000) <= x && x <= add(mul(x >> 16u32, 0x1_0000), 0xffff)) by (bit_vector);
    assert(-0x4000_0000 <= x >> 1u32 <= 0x3fff_ffff) by (bit_vector);
    assert(-0x0800_0000 <= x >> 4u32 <= 0x07ff_ffff) by (bit_vector);
    assert(-0x40_0000 <= x >> 9u32 <= 0x3f_ffff) by (bit_vector);
    assert(-0x8000 <= x >> 16u32 <= 0x7fff) by (bit_vector);
    let (a, b, c, d) = (x >> 1u32, x >> 4u32, x >> 9u32, x >> 16u32);
    assert(mul(a, 2) == a * 2 && add(mul(a, 2), 1) == a * 2 + 1);
    assert(mul(b, 16) == b * 16 && add(mul(b, 16), 15) == b * 16 + 15);
    assert(mul(c, 512) == c * 512 && add(mul(c, 512), 511) == c * 512 + 511);
    assert(mul(d, 0x1_0000) == d * 0x1_0000 && add(mul(d, 0x1_0000), 0xffff) == d * 0x1_0000 + 0xffff);
}

/// Sum of squared differences of a `size` by `size` block at `d` in two
/// scratch blocks.
pub fn sse(a: &[u8], b: &[u8], d: usize, size: usize) -> (r: u32)
    requires
        a@.len() == YUV_SIZE,
        b@.len() == YUV_SIZE,
        size == 8 || size == 16,
        d + (size - 1) * BPS + size <= YUV_SIZE,
    ensures
        r <= 256 * 65025,
{
    let mut s: u32 = 0;
    let mut j: usize = 0;
    while j < size
        invariant
            a@.len() == YUV_SIZE,
            b@.len() == YUV_SIZE,
            size == 8 || size == 16,
            d + (size - 1) * BPS + size <= YUV_SIZE,
            j <= size,
            s <= 65025 * (16 * j),
        decreases size - j,
    {
        let mut i: usize = 0;
        while i < size
            invariant
                a@.len() == YUV_SIZE,
                b@.len() == YUV_SIZE,
                size == 8 || size == 16,
                d + (size - 1) * BPS + size <= YUV_SIZE,
                j < size,
                i <= size,
                s <= 65025 * (16 * j + i),
            decreases size - i,
        {
            let k = d + j * BPS + i;
            let x = a[k] as i32 - b[k] as i32;
            assert(-255 <= x <= 255);
            assert(0 <= x * x <= 65025) by (nonlinear_arith)
                requires
                    -255 <= x <= 255,
            ;
            let xx = x * x;
            assert(65025 * (16 * j + i) + 65025 <= 65025 * 256);
            s = s + xx as u32;
            i = i + 1;
        }
        j = j + 1;
    }
    s
}

/// One pass of `FTransform` on four differences.
fn fdct_a(d0: i32, d1: i32, d2: i32, d3: i32) -> (r: (i32, i32, i32, i32))
    requires
        -255 <= d0 <= 255,
        -255 <= d1 <= 255,
        -255 <= d2 <= 255,
        -255 <= d3 <= 255,
    ensures
        -8160 <= r.0 <= 8160,
        -8160 <= r.1 <= 8160,
        -8160 <= r.2 <= 8160,
        -8160 <= r.3 <= 8160,
{
    let a0 = d0 + d3;
    let a1 = d1 + d2;
    let a2 = d1 - d2;
    let a3 = d0 - d3;
    let x1 = a2 * 2217 + a3 * 5352 + 1812;
    let x3 = a3 * 2217 - a2 * 5352 + 937;
    proof {
        lemma_sar(x1);
        lemma_sar(x3);
    }
    ((a0 + a1) * 8, x1 >> 9u32, (a0 - a1) * 8, x3 >> 9u32)
}

/// The second pass of `FTransform`.
fn fdct_b(t0: i32, t1: i32, t2: i32, t3: i32) -> (r: (i32, i32, i32, i32))
    requires
        -8160 <= t0 <= 8160,
        -8160 <= t1 <= 8160,
        -8160 <= t2 <= 8160,
        -8160 <= t3 <= 8160,
    ensures
        -4096 <= r.0 <= 4096,
        -4096 <= r.1 <= 4096,
        -4096 <= r.2 <= 4096,
        -4096 <= r.3 <= 4096,
{
    let a0 = t0 + t3;
    let a1 = t1 + t2;
    let a2 = t1 - t2;
    let a3 = t0 - t3;
    let x0 = a0 + a1 + 7;
    let x2 = a0 - a1 + 7;
    let x1 = a2 * 2217 + a3 * 5352 + 12000;
    let x3 = a3 * 2217 - a2 * 5352 + 51000;
    proof {
        lemma_sar(x0);
        lemma_sar(x1);
        lemma_sar(x2);
        lemma_sar(x3);
    }
    (x0 >> 4u32, (x1 >> 16u32) + (a3 != 0) as i32, x2 >> 4u32, x3 >> 16u32)
}

/// `FTransform`: the forward DCT of the 4x4 difference between `src` and
/// `pred` at `d`, into `out[o..o + 16]` in raster order.
pub fn fdct(src: &[u8], pred: &[u8], d: usize, out: &mut [i32], o: usize)
    requires
        src@.len() == YUV_SIZE,
        pred@.len() == YUV_SIZE,
        d + 3 * BPS + 4 <= YUV_SIZE,
        o + 16 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < final(out)@.len() && !(o <= i < o + 16) ==> final(out)@[i] == old(out)@[i],
        forall|i: int| o <= i < o + 16 ==> -4096 <= #[trigger] final(out)@[i] <= 4096,
{
    let mut t = [0i32; 16];
    let mut i: usize = 0;
    while i < 4
        invariant
            src@.len() == YUV_SIZE,
            pred@.len() == YUV_SIZE,
            d + 3 * BPS + 4 <= YUV_SIZE,
            i <= 4,
            forall|k: int| 0 <= k < 16 ==> -8160 <= #[trigger] t@[k] <= 8160,
        decreases 4 - i,
    {
        let r = d + i * BPS;
        let (a, b, c, e) = fdct_a(
            src[r] as i32 - pred[r] as i32,
            src[r + 1] as i32 - pred[r + 1] as i32,
            src[r + 2] as i32 - pred[r + 2] as i32,
            src[r + 3] as i32 - pred[r + 3] as i32,
        );
        t[4 * i] = a;
        t[4 * i + 1] = b;
        t[4 * i + 2] = c;
        t[4 * i + 3] = e;
        i = i + 1;
    }
    let ghost o0 = out@;
    proof {
        assert(out@.len() == out.len());
    }
    let mut i: usize = 0;
    while i < 4
        invariant
            i <= 4,
            o + 16 <= out@.len(),
            out@.len() <= usize::MAX,
            out@.len() == o0.len(),
            forall|k: int| 0 <= k < 16 ==> -8160 <= #[trigger] t@[k] <= 8160,
            forall|k: int| 0 <= k < out@.len() && !(o <= k < o + 16) ==> #[trigger] out@[k] == o0[k],
            forall|k: int| o <= k < o + 16 && (k - o) % 4 < i ==> -4096 <= #[trigger] out@[k] <= 4096,
        decreases 4 - i,
    {
        let (a, b, c, e) = fdct_b(t[i], t[4 + i], t[8 + i], t[12 + i]);
        out[o + i] = a;
        out[o + 4 + i] = b;
        out[o + 8 + i] = c;
        out[o + 12 + i] = e;
        i = i + 1;
    }
}

/// `FTransformWHT` of the sixteen luma DCs (`dc[k]` for block `k` in
/// raster order), in raster order.
pub fn fwht(dc: &[i32; 16]) -> (r: [i32; 16])
    requires
        forall|k: int| 0 <= k < 16 ==> -4096 <= #[trigger] dc@[k] <= 4096,
    ensures
        forall|k: int| 0 <= k < 16 ==> -32768 <= #[trigger] r@[k] <= 32768,
{
    let mut t = [0i32; 16];
    let mut i: usize = 0;
    while i < 4
        invariant
            i <= 4,
            forall|k: int| 0 <= k < 16 ==> -4096 <= #[trigger] dc@[k] <= 4096,
            forall|k: int| 0 <= k < 16 ==> -16384 <= #[trigger] t@[k] <= 16384,
        decreases 4 - i,
    {
        let a0 = dc[4 * i] + dc[4 * i + 2];
        let a1 = dc[4 * i + 1] + dc[4 * i + 3];
        let a2 = dc[4 * i + 1] - dc[4 * i + 3];
        let a3 = dc[4 * i] - dc[4 * i + 2];
        t[4 * i] = a0 + a1;
        t[4 * i + 1] = a3 + a2;
        t[4 * i + 2] = a3 - a2;
        t[4 * i + 3] = a0 - a1;
        i = i + 1;
    }
    let mut r = [0i32; 16];
    let mut i: usize = 0;
    while i < 4
        invariant
            i <= 4,
            forall|k: int| 0 <= k < 16 ==> -16384 <= #[trigger] t@[k] <= 16384,
            forall|k: int| 0 <= k < 16 ==> -32768 <= #[trigger] r@[k] <= 32768,
        decreases 4 - i,
    {
        let a0 = t[i] + t[8 + i];
        let a1 = t[4 + i] + t[12 + i];
        let a2 = t[4 + i] - t[12 + i];
        let a3 = t[i] - t[8 + i];
        let (b0, b1, b2, b3) = (a0 + a1, a3 + a2, a3 - a2, a0 - a1);
        proof {
            lemma_sar(b0);
            lemma_sar(b1);
            lemma_sar(b2);
            lemma_sar(b3);
        }
        r[i] = b0 >> 1u32;
        r[4 + i] = b1 >> 1u32;
        r[8 + i] = b2 >> 1u32;
        r[12 + i] = b3 >> 1u32;
        i = i + 1;
    }
    r
}

/// The quantizer of one kind of coefficient: step `q`, rounding `bias`
/// (in 1/256), and the largest level, which keeps `level * q` within
/// `cap`.
#[derive(Clone, Copy)]
pub struct Qz {
    pub q: u32,
    pub bias: u32,
    pub lim: u32,
}

pub open spec fn qz_ok(z: Qz, cap: int) -> bool {
    &&& 4 <= z.q <= 1024
    &&& z.bias < 256
    &&& z.lim * z.q <= cap
    &&& z.lim <= 2047
}

pub fn qz(q: u32, bias: u32, cap: u32) -> (r: Qz)
    requires
        4 <= q <= 1024,
        bias < 256,
        cap <= 32767,
    ensures
        qz_ok(r, cap as int),
        r.q == q,
{
    let l0 = cap / q;
    proof {
        assert(l0 * q <= cap) by (nonlinear_arith)
            requires
                l0 == cap / q,
                q > 0,
        ;
    }
    let lim = if l0 > 2047 {
        2047
    } else {
        l0
    };
    proof {
        assert(lim * q <= l0 * q) by (nonlinear_arith)
            requires
                lim <= l0,
        ;
    }
    Qz { q, bias, lim }
}

/// Quantizes `c`: the level, and the coefficient it dequantizes to.
pub fn quant(c: i32, z: Qz, Ghost(cap): Ghost<int>) -> (r: (i16, i16))
    requires
        qz_ok(z, cap),
        cap <= 32767,
        -32768 <= c <= 32768,
    ensures
        -2047 <= r.0 <= 2047,
        r.1 as int == r.0 as int * z.q as int,
        -cap <= r.1 <= cap,
{
    let a: u32 = if c < 0 {
        (-c) as u32
    } else {
        c as u32
    };
    proof {
        assert(z.q * z.bias <= 1024 * 256) by (nonlinear_arith)
            requires
                z.q <= 1024,
                z.bias < 256,
        ;
    }
    let mut lev = (a * 256 + z.q * z.bias) / (z.q * 256);
    if lev > z.lim {
        lev = z.lim;
    }
    proof {
        assert(lev * z.q <= z.lim * z.q) by (nonlinear_arith)
            requires
                lev <= z.lim,
        ;
        assert(lev * z.q <= 32767);
    }
    let l = lev as i16;
    let d = (lev * z.q) as i16;
    proof {
        assert((-(lev as int)) * (z.q as int) == -((lev * z.q) as int)) by (nonlinear_arith);
    }
    if c < 0 {
        (-l, -d)
    } else {
        (l, d)
    }
}

} // verus!
