//! Vector (AVX2) kernels for the inverse transforms, verified against the
//! same specs as the scalar code in `undo.rs`.
//!
//! Every intrinsic is called through `vsimd`'s specifications; each kernel
//! requires `avx2()`, so verified code reaches it only after run-time
//! detection (`verilith_simd::cpu::has_avx2`).
use crate::pxops::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use crate::vlemmas::*;
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
use verilith_core::prims::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;
#[cfg(verus_only)]
use verilith_simd::patterns::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

// ---------------------------------------------------------------------------
// Subtract green
// ---------------------------------------------------------------------------

/// `pshufb` mask copying each pixel's green byte onto its blue and red
/// bytes, zeroing green and alpha.
pub open spec fn sg_mask() -> Seq<u8> {
    Seq::new(32, |i: int| if i % 2 == 0 { (i % 16 - i % 4 + 1) as u8 } else { 128u8 })
}

proof fn lemma_sg(a: Seq<u8>, m: Seq<u8>)
    requires
        a.len() == 32,
        m == sg_mask(),
    ensures
        forall|k: int|
            0 <= k < 8 ==> #[trigger] u32s(add8(a, shuffle8_lanes(a, m)))[k] == add_green(u32s(a)[k]),
{
    let s = shuffle8_lanes(a, m);
    assert forall|i: int| 0 <= i < 32 implies #[trigger] s[i] == (if i % 2 == 0 { a[i - i % 4 + 1] } else { 0u8 }) by {
        assert((i / 16) * 16 + (i % 16 - i % 4 + 1) == i - i % 4 + 1);
    }
    let c = add8(a, s);
    assert forall|k: int| 0 <= k < 8 implies #[trigger] u32s(c)[k] == add_green(u32s(a)[k]) by {
        assert((4 * k) % 2 == 0 && (4 * k) % 4 == 0 && (4 * k + 2) % 2 == 0 && (4 * k + 2) % 4 == 2);
        assert((4 * k + 1) % 2 == 1 && (4 * k + 3) % 2 == 1);
        lemma_lane_px(a, k);
        lemma_lane_px(c, k);
        let p = u32s(a)[k];
        lemma_argb_le32(
            alpha(p) as u8,
            ((red(p) + green(p)) % 256) as u8,
            green(p) as u8,
            ((blue(p) + green(p)) % 256) as u8,
        );
    }
}

/// Undoes subtract green, eight pixels at a time.
#[inline(always)]
pub fn undo_sg_avx2_body(px: &mut Vec<u32>)
    requires
        avx2(),
    ensures
        final(px)@ == Seq::new(old(px)@.len(), |j: int| add_green(old(px)@[j])),
{
    let ghost src = px@;
    let n = px.len();
    let m = _mm256_setr_epi8(
        1, -128, 1, -128, 5, -128, 5, -128, 9, -128, 9, -128, 13, -128, 13, -128,
        1, -128, 1, -128, 5, -128, 5, -128, 9, -128, 9, -128, 13, -128, 13, -128,
    );
    assert(b256(m) =~= sg_mask());
    let mut i: usize = 0;
    while n - i >= 8
        invariant
            avx2(),
            n == px@.len(),
            src.len() == n,
            i <= n,
            b256(m) == sg_mask(),
            forall|j: int| 0 <= j < i ==> #[trigger] px@[j] == add_green(src[j]),
            forall|j: int| i <= j < n ==> #[trigger] px@[j] == src[j],
        decreases n - i,
    {
        let a = load256_u32(px.as_slice(), i);
        let r = _mm256_add_epi8(a, _mm256_shuffle_epi8(a, m));
        proof {
            lemma_sg(b256(a), b256(m));
        }
        store256_u32(px.as_mut_slice(), i, r);
        assert forall|j: int| i <= j < i + 8 implies #[trigger] px@[j] == add_green(src[j]) by {
            assert(u32x8(a)[j - i] == src[j]);
        }
        i = i + 8;
    }
    while i < n
        invariant
            n == px@.len(),
            src.len() == n,
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] px@[j] == add_green(src[j]),
            forall|j: int| i <= j < n ==> #[trigger] px@[j] == src[j],
        decreases n - i,
    {
        let c = add_green_exec(px[i]);
        px.set(i, c);
        i = i + 1;
    }
    assert(px@ =~= Seq::new(src.len(), |j: int| add_green(src[j])));
}

/// Trusted: `undo_sg_avx2_body` compiled with `avx2` enabled, through
/// `tf::undo_sg_avx2`; the contract is `undo_sg_avx2_body`'s, which is verified.
#[verifier::external_body]
pub fn undo_sg_avx2(px: &mut Vec<u32>)
    requires
        avx2(),
    ensures
        final(px)@ == Seq::new(old(px)@.len(), |j: int| add_green(old(px)@[j])),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::undo_sg_avx2(px) };
    #[cfg(not(target_arch = "x86_64"))]
    return undo_sg_avx2_body(px);
}

// ---------------------------------------------------------------------------
// Color transform
// ---------------------------------------------------------------------------
//
// libwebp's trick: with green in the high byte of a 16-bit lane, that lane
// is `256 * sbyte(green)`; multiplying by `8 * sbyte(m)` and keeping the high
// half (`mulhi_epi16`) gives `(sbyte(green) * sbyte(m)) >> 5`, which is
// `delta(m, green)`. Its low byte, added bytewise, adjusts red and blue.

/// `8 * sbyte(m)` as a 16-bit lane.
pub open spec fn cst16(m: u32) -> u16 {
    ((sbyte(m) * 8 + 0x10000) % 0x10000) as u16
}

#[inline(always)]
fn cst16_exec(m: u32) -> (r: u32)
    requires
        m < 256,
    ensures
        r == cst16(m) as u32,
        r < 0x10000,
{
    if m < 128 {
        m * 8
    } else {
        0x10000 - (256 - m) * 8
    }
}

/// Two 16-bit lanes as one 32-bit lane.
pub open spec fn pack16(hi: u16, lo: u16) -> u32 {
    ((hi as u32) << 16u32) | (lo as u32)
}

/// The value of `mulhi_epi16` on one lane.
pub open spec fn mulhi1(x: u16, y: u16) -> u16 {
    (((s16(x) * s16(y)) / 0x10000) % 0x10000) as u16
}

proof fn lemma_mulhi_delta(g: u8, m: u32)
    requires
        m < 256,
    ensures
        byte16(mulhi1(le16(0u8, g), cst16(m)), 0) as int == delta(m, g as u32) % 256,
{
    lemma_le16_value(0u8, g);
    let x = le16(0u8, g);
    let y = cst16(m);
    assert(s16(x) == 256 * sbyte(g as u32));
    assert(s16(y) == 8 * sbyte(m));
    let k = sbyte(m) * sbyte(g as u32);
    assert(s16(x) * s16(y) == 2048 * k) by (nonlinear_arith)
        requires
            s16(x) == 256 * sbyte(g as u32),
            s16(y) == 8 * sbyte(m),
            k == sbyte(m) * sbyte(g as u32),
    ;
    lemma_fundamental_div_mod(k, 32);
    lemma_mod_bound(k, 32);
    assert(2048 * k == 65536 * (k / 32) + 2048 * (k % 32)) by (nonlinear_arith)
        requires
            k == 32 * (k / 32) + k % 32,
    ;
    lemma_fundamental_div_mod_converse(2048 * k, 65536, k / 32, 2048 * (k % 32));
    let d = k / 32;
    assert(d == delta(m, g as u32));
    let r = mulhi1(x, y);
    assert(r as int == d % 0x10000);
    lemma_byte16_lo(r);
    lemma_mod_mod(d, 256, 256);
}

proof fn lemma_mulhi_zero()
    ensures
        byte16(mulhi1(le16(0u8, 0u8), 0u16), 0) == 0,
{
    lemma_le16_value(0u8, 0u8);
    assert(s16(le16(0u8, 0u8)) == 0);
    assert(s16(0u16) == 0);
    assert(s16(le16(0u8, 0u8)) * s16(0u16) == 0);
    assert(0int / 0x10000 == 0);
    assert(mulhi1(le16(0u8, 0u8), 0u16) == 0);
    lemma_byte16_lo(0u16);
}

/// Pixel `k` through the vector color transform (byte sequences of the
/// intermediate vectors, related as the intrinsics' specs relate them).
#[verifier::rlimit(40)]
proof fn lemma_color_px(
    k: int,
    e: u32,
    a: Seq<u8>,
    p1: Seq<u8>,
    p2: Seq<u8>,
    m1: Seq<u8>,
    m2: Seq<u8>,
    mag: Seq<u8>,
    b: Seq<u8>,
    c: Seq<u8>,
    d: Seq<u8>,
    ee: Seq<u8>,
    f: Seq<u8>,
    g: Seq<u8>,
    o: Seq<u8>,
)
    requires
        a.len() == 32 && c.len() == 32 && f.len() == 32 && m1.len() == 32 && m2.len() == 32 && mag.len() == 32,
        p1 == group4_mask(-1, 1, -1, 1, 32),
        p2 == group4_mask(-1, 2, -1, -1, 32),
        u32s(m1) == splat32(pack16(cst16(e & 0xff), cst16((e >> 8u32) & 0xff)), 8),
        u32s(m2) == splat32(cst16((e >> 16u32) & 0xff) as u32, 8),
        u32s(mag) == splat32(0xff00ff00u32, 8),
        b == shuffle8_lanes(a, p1),
        u16s(c) == mulhi_s16(u16s(b), u16s(m1)),
        d == add8(a, c),
        ee == shuffle8_lanes(d, p2),
        u16s(f) == mulhi_s16(u16s(ee), u16s(m2)),
        g == add8(d, f),
        o == blendv8(g, a, mag),
        0 <= k < 8,
    ensures
        u32s(o)[k] == uncolor(u32s(a)[k], e),
{
    let g2r = e & 0xff;
    let g2b = (e >> 8u32) & 0xff;
    let r2b = (e >> 16u32) & 0xff;
    assert(e & 0xffu32 < 256 && (e >> 8u32) & 0xffu32 < 256 && (e >> 16u32) & 0xffu32 < 256) by (bit_vector);
    lemma_group4_shuffle(a, -1, 1, -1, 1);
    lemma_group4_shuffle(d, -1, 2, -1, -1);
    lemma_u16s_of_u32s(m1);
    lemma_u16s_of_u32s(m2);
    lemma_u32s_bytes(mag);
    let w1 = pack16(cst16(g2r), cst16(g2b));
    assert((w1 & 0xffff) as u16 == cst16(g2b) && (w1 >> 16u32) as u16 == cst16(g2r)) by {
        let (hi, lo) = (cst16(g2r), cst16(g2b));
        assert(((((hi as u32) << 16u32) | (lo as u32)) & 0xffff) as u16 == lo) by (bit_vector);
        assert(((((hi as u32) << 16u32) | (lo as u32)) >> 16u32) as u16 == hi) by (bit_vector);
    }
    let w2 = cst16(r2b) as u32;
    assert((w2 & 0xffff) as u16 == cst16(r2b) && (w2 >> 16u32) as u16 == 0u16) by {
        let lo = cst16(r2b);
        assert((lo as u32) & 0xffff == lo as u32) by (bit_vector);
        assert((lo as u32) >> 16u32 == 0) by (bit_vector);
    }
    assert(byte32(0xff00ff00u32, 0) == 0 && byte32(0xff00ff00u32, 1) == 0xff && byte32(0xff00ff00u32, 2) == 0
        && byte32(0xff00ff00u32, 3) == 0xff) by (compute);
    {
        let p = u32s(a)[k];
        lemma_lane_px(a, k);
        lemma_lane_px(o, k);
        let (bl, gr, rd, al) = (a[4 * k], a[4 * k + 1], a[4 * k + 2], a[4 * k + 3]);
        assert((4 * k) % 4 == 0 && (4 * k + 1) % 4 == 1 && (4 * k + 2) % 4 == 2 && (4 * k + 3) % 4 == 3);
        // b: green in the high byte of both 16-bit lanes.
        assert(b[4 * k] == 0 && b[4 * k + 1] == gr && b[4 * k + 2] == 0 && b[4 * k + 3] == gr);
        assert(u16s(b)[2 * k] == le16(0u8, gr) && u16s(b)[2 * k + 1] == le16(0u8, gr));
        assert(u32s(m1)[k] == w1);
        assert(u16s(m1)[2 * k] == (u32s(m1)[k] & 0xffff) as u16);
        assert(u16s(m1)[2 * k + 1] == (u32s(m1)[k] >> 16u32) as u16);
        assert(u16s(m1)[2 * k] == cst16(g2b) && u16s(m1)[2 * k + 1] == cst16(g2r));
        // c: the deltas, in the low bytes.
        lemma_u16_lane_bytes(c, 2 * k);
        lemma_u16_lane_bytes(c, 2 * k + 1);
        lemma_mulhi_delta(gr, g2b);
        lemma_mulhi_delta(gr, g2r);
        assert(c[4 * k] as int == delta(g2b, gr as u32) % 256);
        assert(c[4 * k + 2] as int == delta(g2r, gr as u32) % 256);
        // d: red is final.
        let nr = (rd + delta(g2r, gr as u32)) % 256;
        lemma_add_mod_noop(rd as int, delta(g2r, gr as u32), 256);
        lemma_mod_twice(delta(g2r, gr as u32), 256);
        lemma_mod_bound(rd as int, 256);
        assert(d[4 * k + 2] as int == nr) by {
            lemma_small_mod(rd as nat, 256);
        }
        // e, f: red's delta to blue.
        assert(ee[4 * k] == 0 && ee[4 * k + 1] == d[4 * k + 2] && ee[4 * k + 2] == 0 && ee[4 * k + 3] == 0);
        assert(u16s(ee)[2 * k] == le16(0u8, d[4 * k + 2]) && u16s(ee)[2 * k + 1] == le16(0u8, 0u8));
        assert(u32s(m2)[k] == w2);
        assert(u16s(m2)[2 * k] == (u32s(m2)[k] & 0xffff) as u16);
        assert(u16s(m2)[2 * k + 1] == (u32s(m2)[k] >> 16u32) as u16);
        assert(u16s(m2)[2 * k] == cst16(r2b) && u16s(m2)[2 * k + 1] == 0u16);
        lemma_u16_lane_bytes(f, 2 * k);
        lemma_u16_lane_bytes(f, 2 * k + 1);
        lemma_mulhi_delta(d[4 * k + 2], r2b);
        lemma_mulhi_zero();
        assert(f[4 * k] as int == delta(r2b, nr as u32) % 256);
        assert(f[4 * k + 2] == 0);
        // g: blue is final.
        let nb = (bl + delta(g2b, gr as u32) + delta(r2b, nr as u32)) % 256;
        assert(g[4 * k] as int == nb) by {
            let (d1, d2) = (delta(g2b, gr as u32), delta(r2b, nr as u32));
            lemma_add_mod_noop(bl as int, d1, 256);
            lemma_mod_twice(d1, 256);
            lemma_small_mod(bl as nat, 256);
            assert(d[4 * k] as int == (bl + d1) % 256);
            lemma_add_mod_noop(bl + d1, d2, 256);
            lemma_mod_twice(d2, 256);
            lemma_mod_twice(bl + d1, 256);
        }
        assert(g[4 * k + 2] as int == nr) by {
            lemma_small_mod(d[4 * k + 2] as nat, 256);
        }
        // o: alpha and green from the input.
        assert(u32s(mag)[k] == 0xff00ff00u32);
        assert(byte32(u32s(mag)[k], 0) == mag[4 * k + 0]);
        assert(byte32(u32s(mag)[k], 1) == mag[4 * k + 1]);
        assert(byte32(u32s(mag)[k], 2) == mag[4 * k + 2]);
        assert(byte32(u32s(mag)[k], 3) == mag[4 * k + 3]);
        assert(o[4 * k] == g[4 * k] && o[4 * k + 1] == gr && o[4 * k + 2] == g[4 * k + 2] && o[4 * k + 3] == al);
        lemma_argb_le32(al, nr as u8, gr, nb as u8);
    }
}

/// Eight pixels through the vector color transform.
proof fn lemma_color8(
    e: u32,
    a: Seq<u8>,
    p1: Seq<u8>,
    p2: Seq<u8>,
    m1: Seq<u8>,
    m2: Seq<u8>,
    mag: Seq<u8>,
    b: Seq<u8>,
    c: Seq<u8>,
    d: Seq<u8>,
    ee: Seq<u8>,
    f: Seq<u8>,
    g: Seq<u8>,
    o: Seq<u8>,
)
    requires
        a.len() == 32 && c.len() == 32 && f.len() == 32 && m1.len() == 32 && m2.len() == 32 && mag.len() == 32,
        p1 == group4_mask(-1, 1, -1, 1, 32),
        p2 == group4_mask(-1, 2, -1, -1, 32),
        u32s(m1) == splat32(pack16(cst16(e & 0xff), cst16((e >> 8u32) & 0xff)), 8),
        u32s(m2) == splat32(cst16((e >> 16u32) & 0xff) as u32, 8),
        u32s(mag) == splat32(0xff00ff00u32, 8),
        b == shuffle8_lanes(a, p1),
        u16s(c) == mulhi_s16(u16s(b), u16s(m1)),
        d == add8(a, c),
        ee == shuffle8_lanes(d, p2),
        u16s(f) == mulhi_s16(u16s(ee), u16s(m2)),
        g == add8(d, f),
        o == blendv8(g, a, mag),
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] u32s(o)[k] == uncolor(u32s(a)[k], e),
{
    assert forall|k: int| 0 <= k < 8 implies #[trigger] u32s(o)[k] == uncolor(u32s(a)[k], e) by {
        lemma_color_px(k, e, a, p1, p2, m1, m2, mag, b, c, d, ee, f, g, o);
    }
}

/// Undoes the color transform with element `e` on pixels `i0..i1`.
#[inline(always)]
pub fn uncolor_run_avx2_body(px: &mut Vec<u32>, i0: usize, i1: usize, e: u32)
    requires
        avx2(),
        i0 <= i1 <= old(px)@.len(),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] final(px)@[j] == uncolor(old(px)@[j], e),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    let ghost src = px@;
    let p1 = _mm256_setr_epi8(
        -128, 1, -128, 1, -128, 5, -128, 5, -128, 9, -128, 9, -128, 13, -128, 13,
        -128, 1, -128, 1, -128, 5, -128, 5, -128, 9, -128, 9, -128, 13, -128, 13,
    );
    let p2 = _mm256_setr_epi8(
        -128, 2, -128, -128, -128, 6, -128, -128, -128, 10, -128, -128, -128, 14, -128, -128,
        -128, 2, -128, -128, -128, 6, -128, -128, -128, 10, -128, -128, -128, 14, -128, -128,
    );
    assert(b256(p1) =~= group4_mask(-1, 1, -1, 1, 32));
    assert(b256(p2) =~= group4_mask(-1, 2, -1, -1, 32));
    proof {
        assert(e & 0xffu32 < 256 && (e >> 8u32) & 0xffu32 < 256 && (e >> 16u32) & 0xffu32 < 256) by (bit_vector);
    }
    let g2r = cst16_exec(e & 0xff);
    let g2b = cst16_exec((e >> 8) & 0xff);
    let r2b = cst16_exec((e >> 16) & 0xff);
    let w1 = (g2r << 16) | g2b;
    proof {
        assert(w1 == pack16(g2r as u16, g2b as u16)) by {
            assert(g2r < 0x10000 && g2b < 0x10000 ==> (g2r << 16u32) | g2b == ((((g2r as u16) as u32) << 16u32) | ((g2b as u16) as u32))) by (bit_vector);
        }
    }
    let m1 = _mm256_set1_epi32(i32_of_u32(w1));
    let m2 = _mm256_set1_epi32(r2b as i32);
    let mag = _mm256_set1_epi32(i32_of_u32(0xff00ff00));
    let mut i = i0;
    while i1 - i >= 8
        invariant
            avx2(),
            i0 <= i <= i1 <= px@.len(),
            px@.len() == src.len(),
            b256(p1) == group4_mask(-1, 1, -1, 1, 32),
            b256(p2) == group4_mask(-1, 2, -1, -1, 32),
            u32x8(m1) == splat32(pack16(cst16(e & 0xff), cst16((e >> 8u32) & 0xff)), 8),
            u32x8(m2) == splat32(cst16((e >> 16u32) & 0xff) as u32, 8),
            u32x8(mag) == splat32(0xff00ff00u32, 8),
            forall|j: int| i0 <= j < i ==> #[trigger] px@[j] == uncolor(src[j], e),
            forall|j: int| 0 <= j < i0 || i <= j < src.len() ==> #[trigger] px@[j] == src[j],
        decreases i1 - i,
    {
        let a = load256_u32(px.as_slice(), i);
        let b = _mm256_shuffle_epi8(a, p1);
        let c = _mm256_mulhi_epi16(b, m1);
        let d = _mm256_add_epi8(a, c);
        let ee = _mm256_shuffle_epi8(d, p2);
        let f = _mm256_mulhi_epi16(ee, m2);
        let g = _mm256_add_epi8(d, f);
        let o = _mm256_blendv_epi8(g, a, mag);
        proof {
            lemma_color8(e, b256(a), b256(p1), b256(p2), b256(m1), b256(m2), b256(mag), b256(b), b256(c), b256(d),
                b256(ee), b256(f), b256(g), b256(o));
        }
        store256_u32(px.as_mut_slice(), i, o);
        assert forall|j: int| i <= j < i + 8 implies #[trigger] px@[j] == uncolor(src[j], e) by {
            assert(u32x8(a)[j - i] == src[j]);
        }
        i = i + 8;
    }
    while i < i1
        invariant
            i0 <= i <= i1 <= px@.len(),
            px@.len() == src.len(),
            forall|j: int| i0 <= j < i ==> #[trigger] px@[j] == uncolor(src[j], e),
            forall|j: int| 0 <= j < i0 || i <= j < src.len() ==> #[trigger] px@[j] == src[j],
        decreases i1 - i,
    {
        let c = uncolor_exec(get32(px.as_slice(), i), e);
        set32(px.as_mut_slice(), i, c);
        i = i + 1;
    }
}

/// Trusted: `uncolor_run_avx2_body` compiled with `avx2` enabled, through
/// `tf::uncolor_run_avx2`; the contract is `uncolor_run_avx2_body`'s, which is verified.
#[verifier::external_body]
pub fn uncolor_run_avx2(px: &mut Vec<u32>, i0: usize, i1: usize, e: u32)
    requires
        avx2(),
        i0 <= i1 <= old(px)@.len(),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] final(px)@[j] == uncolor(old(px)@[j], e),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::uncolor_run_avx2(px, i0, i1, e) };
    #[cfg(not(target_arch = "x86_64"))]
    return uncolor_run_avx2_body(px, i0, i1, e);
}

/// The `i32` with the bits of `x`.
#[inline(always)]
pub fn i32_of_u32(x: u32) -> (r: i32)
    ensures
        u32_of_i32(r) == x,
{
    if x < 0x8000_0000 {
        x as i32
    } else {
        ((x - 0x8000_0000) as i32) - 0x7fff_ffff - 1
    }
}

} // verus!

/// Trampolines that compile a verified `*_body` function with the target
/// features its kernel needs. Each is one call; `#[target_feature]` only
/// changes code generation. Verus rejects the attribute on verified code
/// (verus-lang/verus#3362), so it lives outside `verus!`.
#[cfg(target_arch = "x86_64")]
mod tf {
    #[allow(unused_imports)]
    use super::*;

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn undo_sg_avx2(px: &mut Vec<u32>) {
        undo_sg_avx2_body(px)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn uncolor_run_avx2(px: &mut Vec<u32>, i0: usize, i1: usize, e: u32) {
        uncolor_run_avx2_body(px, i0, i1, e)
    }
}
