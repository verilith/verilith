//! AVX2 base64 kernels (after Muła and Lemire, "Faster Base64 Encoding and
//! Decoding using AVX2 Instructions", 2018), proven with vsimd's
//! specifications of the intrinsics.
//!
//! Encoding takes 24 bytes to 32 characters per step: two overlapping
//! 16-byte loads put 12 input bytes in each 128-bit lane, a byte shuffle
//! spreads every 3 bytes `a b c` over a 32-bit lane as `b a c b`, four
//! masked shifts cut the lane into its four 6-bit values, and a 16-entry
//! table lookup adds the offset that turns each value into its character.
//!
//! The kernels stop where fewer than a full step (plus the bytes the loads
//! read past it) remain, and return how far they got; the scalar loops in
//! `scalar` continue from there.
use super::spec::*;
use crate::simd::*;
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
use verilith_simd::ops::*;
#[cfg(verus_only)]
use verilith_simd::patterns::pick4;
#[cfg(verus_only)]
use vstd::compute::RangeAll;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

/// Spreads each 3 input bytes `a b c` of a 128-bit lane over a 32-bit lane
/// as `b a c b`.
pub const ENC_SHUF: [u8; 32] = [
    1, 0, 2, 1, 4, 3, 5, 4, 7, 6, 8, 7, 10, 9, 11, 10,
    1, 0, 2, 1, 4, 3, 5, 4, 7, 6, 8, 7, 10, 9, 11, 10,
];

/// Offsets from a 6-bit value to its character, indexed by `xr(value)`:
/// 0 for `a..z`, 1..=10 for digits, 11 and 12 for the two symbols, 13 for
/// `A..Z`. Standard alphabet.
pub const ENC_LUT_STD: [u8; 32] = [
    71, 252, 252, 252, 252, 252, 252, 252, 252, 252, 252, 237, 240, 65, 0, 0,
    71, 252, 252, 252, 252, 252, 252, 252, 252, 252, 252, 237, 240, 65, 0, 0,
];

/// As `ENC_LUT_STD`, for the URL-safe alphabet.
pub const ENC_LUT_URL: [u8; 32] = [
    71, 252, 252, 252, 252, 252, 252, 252, 252, 252, 252, 239, 32, 65, 0, 0,
    71, 252, 252, 252, 252, 252, 252, 252, 252, 252, 252, 239, 32, 65, 0, 0,
];

/// The table index the kernel computes for a value `v`: `subs(v, 51)`, or
/// 13 where `v < 26` (a signed compare).
pub open spec fn xr(v: u8) -> u8 {
    (if v < 51 {
        0u8
    } else {
        (v - 51) as u8
    }) | ((if s8(26) > s8(v) {
        0xffu8
    } else {
        0u8
    }) & 13u8)
}

/// What the translation step makes of a value.
pub open spec fn xl(lut: Seq<u8>, v: u8) -> u8 {
    ((lut[(xr(v) % 16) as int] + v) % 256) as u8
}

pub proof fn lemma_enc_consts()
    ensures
        forall|j: int| 0 <= j < 32 ==> #[trigger] ENC_SHUF@[j] == 3 * ((j % 16) / 4) + pick4(1, 0, 2, 1, j % 4),
        forall|v: u8| v < 64 ==> #[trigger] xl(ENC_LUT_STD@, v) == sym(false, v),
        forall|v: u8| v < 64 ==> #[trigger] xl(ENC_LUT_URL@, v) == sym(true, v),
        forall|v: u8| v < 64 ==> #[trigger] xr(v) < 16,
        forall|k: int| 0 <= k < 16 ==> #[trigger] ENC_LUT_STD@[k + 16] == ENC_LUT_STD@[k],
        forall|k: int| 0 <= k < 16 ==> #[trigger] ENC_LUT_URL@[k + 16] == ENC_LUT_URL@[k],
{
    let p0 = |j: int| ENC_SHUF@[j] == 3 * ((j % 16) / 4) + pick4(1, 0, 2, 1, j % 4);
    assert((0..32int).all_spec(|j: int| ENC_SHUF@[j] == 3 * ((j % 16) / 4) + pick4(1, 0, 2, 1, j % 4))) by (compute_only);
    vstd::compute::all_spec_ensures(0..32int, p0);
    let p1 = |i: int| xl(ENC_LUT_STD@, i as u8) == sym(false, i as u8) && xr(i as u8) < 16;
    assert((0..64int).all_spec(|i: int| xl(ENC_LUT_STD@, i as u8) == sym(false, i as u8) && xr(i as u8) < 16)) by (compute_only);
    vstd::compute::all_spec_ensures(0..64int, p1);
    let p2 = |i: int| xl(ENC_LUT_URL@, i as u8) == sym(true, i as u8);
    assert((0..64int).all_spec(|i: int| xl(ENC_LUT_URL@, i as u8) == sym(true, i as u8))) by (compute_only);
    vstd::compute::all_spec_ensures(0..64int, p2);
    let p3 = |k: int| ENC_LUT_STD@[k + 16] == ENC_LUT_STD@[k] && ENC_LUT_URL@[k + 16] == ENC_LUT_URL@[k];
    assert((0..16int).all_spec(|k: int| ENC_LUT_STD@[k + 16] == ENC_LUT_STD@[k] && ENC_LUT_URL@[k + 16] == ENC_LUT_URL@[k])) by (compute_only);
    vstd::compute::all_spec_ensures(0..16int, p3);
    assert forall|j: int| 0 <= j < 32 implies #[trigger] ENC_SHUF@[j] == 3 * ((j % 16) / 4) + pick4(1, 0, 2, 1, j % 4) by {
        assert(p0(j));
    }
    assert forall|v: u8| v < 64 implies #[trigger] xl(ENC_LUT_STD@, v) == sym(false, v) by {
        assert(p1(v as int));
    }
    assert forall|v: u8| v < 64 implies #[trigger] xr(v) < 16 by {
        assert(p1(v as int));
    }
    assert forall|v: u8| v < 64 implies #[trigger] xl(ENC_LUT_URL@, v) == sym(true, v) by {
        assert(p2(v as int));
    }
    assert forall|k: int| 0 <= k < 16 implies #[trigger] ENC_LUT_STD@[k + 16] == ENC_LUT_STD@[k] && ENC_LUT_URL@[k + 16] == ENC_LUT_URL@[k] by {
        assert(p3(k));
    }
}

/// The lane arithmetic: the four masked shifts of `b a c b` give the four
/// 6-bit values of `a b c`, one per byte.
pub open spec fn idx_lane(w: u32) -> u32 {
    ((w >> 10u32) & 0x3f) | ((w & 0x3f0) << 4u32) | ((w >> 6u32) & 0x3f0000) | ((w & 0x3f0000) << 8u32)
}

proof fn lemma_idx_lane(a: u8, b: u8, c: u8)
    ensures
        byte32(idx_lane(le32(b, a, c, b)), 0) == sext(a, b, c, 0),
        byte32(idx_lane(le32(b, a, c, b)), 1) == sext(a, b, c, 1),
        byte32(idx_lane(le32(b, a, c, b)), 2) == sext(a, b, c, 2),
        byte32(idx_lane(le32(b, a, c, b)), 3) == sext(a, b, c, 3),
{
    let w = le32(b, a, c, b);
    assert(w == (b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32));
    assert((((((((b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) >> 10u32) & 0x3f)
        | ((((b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) & 0x3f0) << 4u32) | ((((
    b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) >> 6u32) & 0x3f0000) | ((((
    b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) & 0x3f0000) << 8u32)) & 0xff)
        as u8) == a >> 2) by (bit_vector);
    assert(((((((((b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) >> 10u32) & 0x3f)
        | ((((b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) & 0x3f0) << 4u32) | ((((
    b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) >> 6u32) & 0x3f0000) | ((((
    b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) & 0x3f0000) << 8u32)) >> 8u32)
        & 0xff) as u8) == ((a & 3) << 4) | (b >> 4)) by (bit_vector);
    assert(((((((((b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) >> 10u32) & 0x3f)
        | ((((b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) & 0x3f0) << 4u32) | ((((
    b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) >> 6u32) & 0x3f0000) | ((((
    b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) & 0x3f0000) << 8u32)) >> 16u32)
        & 0xff) as u8) == ((b & 15) << 2) | (c >> 6)) by (bit_vector);
    assert(((((((((b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) >> 10u32) & 0x3f)
        | ((((b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) & 0x3f0) << 4u32) | ((((
    b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) >> 6u32) & 0x3f0000) | ((((
    b as u32) | ((a as u32) << 8u32) | ((c as u32) << 16u32) | ((b as u32) << 24u32)) & 0x3f0000) << 8u32)) >> 24u32)
        & 0xff) as u8) == c & 63) by (bit_vector);
}

proof fn lemma_shuffle_index(g: int, t: int)
    requires
        0 <= g < 8,
        0 <= t < 4,
    ensures
        (4 * g + t) / 16 == g / 4,
        (4 * g + t) % 16 == 4 * (g % 4) + t,
        ((4 * g + t) % 16) / 4 == g % 4,
        (4 * g + t) % 4 == t,
        16 * (g / 4) + 3 * (g % 4) == 3 * g + 4 * (g / 4),
{
}

/// Byte `4g + t` of the shuffled vector is input byte
/// `3g + pick4(1, 0, 2, 1, t)`.
proof fn lemma_enc_shuffle(xs: Seq<u8>, i: int, lo: Seq<u8>, hi: Seq<u8>, sb: Seq<u8>)
    requires
        0 <= i,
        i + 28 <= xs.len(),
        lo == xs.subrange(i, i + 16),
        hi == xs.subrange(i + 12, i + 28),
        sb == shuffle8_lanes(lo + hi, ENC_SHUF@),
    ensures
        sb.len() == 32,
        forall|g: int, t: int| 0 <= g < 8 && 0 <= t < 4 ==> #[trigger] sb[4 * g + t] == xs[i + 3 * g + pick4(1, 0, 2, 1, t)],
{
    lemma_enc_consts();
    assert forall|g: int, t: int| 0 <= g < 8 && 0 <= t < 4 implies #[trigger] sb[4 * g + t] == xs[i + 3 * g + pick4(1, 0, 2, 1, t)] by {
        lemma_shuffle_index(g, t);
        let j = 4 * g + t;
        assert(ENC_SHUF@[j] == 3 * (g % 4) + pick4(1, 0, 2, 1, t));
    }
}

/// The masked shifts compute `idx_lane` on every 32-bit lane.
proof fn lemma_enc_lanes(
    sb: Seq<u8>,
    s10: Seq<u8>,
    s6: Seq<u8>,
    k0: Seq<u8>,
    k1: Seq<u8>,
    k2: Seq<u8>,
    t0: Seq<u8>,
    m1: Seq<u8>,
    t1: Seq<u8>,
    t2: Seq<u8>,
    m3: Seq<u8>,
    t3: Seq<u8>,
    t01: Seq<u8>,
    t23: Seq<u8>,
    ib: Seq<u8>,
)
    requires
        sb.len() == 32 && s10.len() == 32 && s6.len() == 32 && k0.len() == 32 && k1.len() == 32 && k2.len() == 32,
        t1.len() == 32 && t3.len() == 32,
        u32s(s10) == srli32(u32s(sb), 10),
        u32s(s6) == srli32(u32s(sb), 6),
        u32s(k0) == splat32(0x3f, 8),
        u32s(k1) == splat32(0x3f0, 8),
        u32s(k2) == splat32(0x3f0000, 8),
        t0 == and8(s10, k0),
        m1 == and8(sb, k1),
        u32s(t1) == slli32(u32s(m1), 4),
        t2 == and8(s6, k2),
        m3 == and8(sb, k2),
        u32s(t3) == slli32(u32s(m3), 8),
        t01 == or8(t0, t1),
        t23 == or8(t2, t3),
        ib == or8(t01, t23),
    ensures
        forall|g: int| 0 <= g < 8 ==> #[trigger] u32s(ib)[g] == idx_lane(u32s(sb)[g]),
{
    lemma_and8_u32s(s10, k0);
    lemma_and8_u32s(sb, k1);
    lemma_and8_u32s(s6, k2);
    lemma_and8_u32s(sb, k2);
    lemma_or8_u32s(t0, t1);
    lemma_or8_u32s(t2, t3);
    lemma_or8_u32s(t01, t23);
    assert forall|g: int| 0 <= g < 8 implies #[trigger] u32s(ib)[g] == idx_lane(u32s(sb)[g]) by {
        let w = u32s(sb)[g];
        lemma_srli32_lane(w, 10);
        lemma_srli32_lane(w, 6);
        assert(w & 0x3f0 <= 0x3f0) by (bit_vector);
        assert(w & 0x3f0000 <= 0x3f0000) by (bit_vector);
        lemma_slli32_lane(w & 0x3f0, 4);
        lemma_slli32_lane(w & 0x3f0000, 8);
        assert(u32s(t0)[g] == (w >> 10u32) & 0x3f);
        assert(u32s(m1)[g] == w & 0x3f0);
        assert(u32s(t1)[g] == (w & 0x3f0) << 4u32);
        assert(u32s(t2)[g] == (w >> 6u32) & 0x3f0000);
        assert(u32s(m3)[g] == w & 0x3f0000);
        assert(u32s(t3)[g] == (w & 0x3f0000) << 8u32);
        let (p0, p1, p2, p3) = (u32s(t0)[g], u32s(t1)[g], u32s(t2)[g], u32s(t3)[g]);
        assert((p0 | p1) | (p2 | p3) == ((p0 | p1) | p2) | p3) by (bit_vector);
    }
}

/// Each byte of `idx` is the 6-bit value of its input group.
proof fn lemma_enc_values(xs: Seq<u8>, i: int, sb: Seq<u8>, ib: Seq<u8>)
    requires
        0 <= i,
        i + 28 <= xs.len(),
        sb.len() == 32,
        ib.len() == 32,
        forall|g: int, t: int| 0 <= g < 8 && 0 <= t < 4 ==> #[trigger] sb[4 * g + t] == xs[i + 3 * g + pick4(1, 0, 2, 1, t)],
        forall|g: int| 0 <= g < 8 ==> #[trigger] u32s(ib)[g] == idx_lane(u32s(sb)[g]),
    ensures
        forall|g: int, t: int| 0 <= g < 8 && 0 <= t < 4 ==> #[trigger] ib[4 * g + t] == sext(xs[i + 3 * g], xs[i + 3 * g + 1], xs[i + 3 * g + 2], t),
{
    assert forall|g: int, t: int| 0 <= g < 8 && 0 <= t < 4 implies #[trigger] ib[4 * g + t] == sext(
        xs[i + 3 * g],
        xs[i + 3 * g + 1],
        xs[i + 3 * g + 2],
        t,
    ) by {
        let a = xs[i + 3 * g];
        let b = xs[i + 3 * g + 1];
        let c = xs[i + 3 * g + 2];
        assert(sb[4 * g + 0] == xs[i + 3 * g + pick4(1, 0, 2, 1, 0)]);
        assert(sb[4 * g + 1] == xs[i + 3 * g + pick4(1, 0, 2, 1, 1)]);
        assert(sb[4 * g + 2] == xs[i + 3 * g + pick4(1, 0, 2, 1, 2)]);
        assert(sb[4 * g + 3] == xs[i + 3 * g + pick4(1, 0, 2, 1, 3)]);
        assert(u32s(sb)[g] == le32(b, a, c, b));
        lemma_idx_lane(a, b, c);
        lemma_byte_of_lane(ib, 4 * g + t);
        lemma_shuffle_index(g, t);
    }
}

/// The translation step maps each value through `xl`.
proof fn lemma_enc_xlat(
    lb: Seq<u8>,
    ib: Seq<u8>,
    k51: Seq<u8>,
    k26: Seq<u8>,
    k13: Seq<u8>,
    sub: Seq<u8>,
    less: Seq<u8>,
    lm: Seq<u8>,
    key: Seq<u8>,
    off: Seq<u8>,
    rb: Seq<u8>,
)
    requires
        lb.len() == 32 && ib.len() == 32,
        forall|k: int| 0 <= k < 16 ==> #[trigger] lb[k + 16] == lb[k],
        forall|j: int| 0 <= j < 32 ==> #[trigger] ib[j] < 64,
        k51 == splat8(51, 32),
        k26 == splat8(26, 32),
        k13 == splat8(13, 32),
        sub == subs_u8(ib, k51),
        less == cmpgt_s8(k26, ib),
        lm == and8(less, k13),
        key == or8(sub, lm),
        off == shuffle8_lanes(lb, key),
        rb == add8(off, ib),
    ensures
        rb.len() == 32,
        forall|j: int| 0 <= j < 32 ==> #[trigger] rb[j] == xl(lb, ib[j]),
{
    lemma_enc_consts();
    assert forall|j: int| 0 <= j < 32 implies #[trigger] rb[j] == xl(lb, ib[j]) by {
        let vv = ib[j];
        assert(key[j] == xr(vv));
        assert(xr(vv) < 16);
        let k = (xr(vv) % 16) as int;
        if j >= 16 {
            assert(lb[k + 16] == lb[k]);
        }
        assert(off[j] == lb[k]);
    }
}

/// The translated bytes are the encoding's characters.
proof fn lemma_enc_assemble(url: bool, xs: Seq<u8>, i: int, ib: Seq<u8>, rb: Seq<u8>)
    requires
        0 <= i,
        i % 3 == 0,
        i + 28 <= xs.len(),
        ib.len() == 32,
        rb.len() == 32,
        forall|g: int, t: int| 0 <= g < 8 && 0 <= t < 4 ==> #[trigger] ib[4 * g + t] == sext(xs[i + 3 * g], xs[i + 3 * g + 1], xs[i + 3 * g + 2], t),
        forall|j: int| 0 <= j < 32 ==> #[trigger] rb[j] == xl(if url { ENC_LUT_URL@ } else { ENC_LUT_STD@ }, ib[j]),
    ensures
        forall|j: int| 0 <= j < 32 ==> #[trigger] rb[j] == enc_char(url, xs, 4 * (i / 3) + j),
{
    lemma_enc_consts();
    assert forall|j: int| 0 <= j < 32 implies #[trigger] rb[j] == enc_char(url, xs, 4 * (i / 3) + j) by {
        let g = j / 4;
        let t = j % 4;
        assert(j == 4 * g + t);
        let a = xs[i + 3 * g];
        let b = xs[i + 3 * g + 1];
        let c = xs[i + 3 * g + 2];
        assert(ib[4 * g + t] == sext(a, b, c, t));
        lemma_sext_small(a, b, c);
        let q = i / 3;
        assert(i == 3 * q);
        lemma_group_index(q + g, t);
        assert(4 * q + j == 4 * (q + g) + t);
        assert(at(xs, 3 * (q + g)) == a);
        assert(at(xs, 3 * (q + g) + 1) == b);
        assert(at(xs, 3 * (q + g) + 2) == c);
    }
}

/// The 32 characters for the 24 input bytes at `x[i..]`, where `i` is a
/// multiple of 3 and the loads may read 4 bytes further.
#[inline(always)]
fn enc_block(url: bool, x: &[u8], i: usize, shuf: __m256i, lut: __m256i) -> (r: __m256i)
    requires
        avx2(),
        i + 28 <= x.len(),
        i % 3 == 0,
        b256(shuf) == ENC_SHUF@,
        b256(lut) == if url { ENC_LUT_URL@ } else { ENC_LUT_STD@ },
    ensures
        forall|j: int| 0 <= j < 32 ==> #[trigger] b256(r)[j] == enc_char(url, x@, 4 * (i / 3) + j),
{
    let lo = load128_u8(x, i);
    let hi = load128_u8(x, i + 12);
    let v = _mm256_set_m128i(hi, lo);
    let s = _mm256_shuffle_epi8(v, shuf);
    let s10 = _mm256_srli_epi32::<10>(s);
    let s6 = _mm256_srli_epi32::<6>(s);
    let k0 = _mm256_set1_epi32(0x3f);
    let k1 = _mm256_set1_epi32(0x3f0);
    let k2 = _mm256_set1_epi32(0x3f0000);
    let t0 = _mm256_and_si256(s10, k0);
    let m1 = _mm256_and_si256(s, k1);
    let t1 = _mm256_slli_epi32::<4>(m1);
    let t2 = _mm256_and_si256(s6, k2);
    let m3 = _mm256_and_si256(s, k2);
    let t3 = _mm256_slli_epi32::<8>(m3);
    let t01 = _mm256_or_si256(t0, t1);
    let t23 = _mm256_or_si256(t2, t3);
    let idx = _mm256_or_si256(t01, t23);
    let k51 = _mm256_set1_epi8(51);
    let k26 = _mm256_set1_epi8(26);
    let k13 = _mm256_set1_epi8(13);
    let sub = _mm256_subs_epu8(idx, k51);
    let less = _mm256_cmpgt_epi8(k26, idx);
    let lm = _mm256_and_si256(less, k13);
    let key = _mm256_or_si256(sub, lm);
    let off = _mm256_shuffle_epi8(lut, key);
    let r = _mm256_add_epi8(off, idx);
    proof {
        assert(u32_of_i32(0x3f) == 0x3f);
        assert(u32_of_i32(0x3f0) == 0x3f0);
        assert(u32_of_i32(0x3f0000) == 0x3f0000);
        assert(u8_of_i8(51) == 51 && u8_of_i8(26) == 26 && u8_of_i8(13) == 13);
        lemma_enc_consts();
        lemma_enc_shuffle(x@, i as int, b128(lo), b128(hi), b256(s));
        lemma_enc_lanes(
            b256(s), b256(s10), b256(s6), b256(k0), b256(k1), b256(k2), b256(t0), b256(m1), b256(t1),
            b256(t2), b256(m3), b256(t3), b256(t01), b256(t23), b256(idx),
        );
        lemma_enc_values(x@, i as int, b256(s), b256(idx));
        assert forall|j: int| 0 <= j < 32 implies #[trigger] b256(idx)[j] < 64 by {
            let g = j / 4;
            let t = j % 4;
            assert(j == 4 * g + t);
            lemma_sext_small(x@[i + 3 * g], x@[i + 3 * g + 1], x@[i + 3 * g + 2]);
            assert(b256(idx)[4 * g + t] == sext(x@[i + 3 * g], x@[i + 3 * g + 1], x@[i + 3 * g + 2], t));
        }
        let lb = if url { ENC_LUT_URL@ } else { ENC_LUT_STD@ };
        lemma_enc_xlat(lb, b256(idx), b256(k51), b256(k26), b256(k13), b256(sub), b256(less), b256(lm), b256(key), b256(off), b256(r));
        lemma_enc_assemble(url, x@, i as int, b256(idx), b256(r));
    }
    r
}

/// Encodes full groups of `x` 24 bytes at a time while the loads stay in
/// bounds; returns the number of groups written to `out`.
#[inline(always)]
pub fn encode_bulk_body(url: bool, x: &[u8], out: &mut [u8]) -> (g: usize)
    requires
        avx2(),
        x.len() <= usize::MAX / 2,
        old(out).len() >= 4 * (x.len() / 3),
    ensures
        final(out).len() == old(out).len(),
        g <= x.len() / 3,
        forall|i: int| 0 <= i < 4 * g ==> #[trigger] final(out)@[i] == enc_char(url, x@, i),
        forall|i: int| 4 * (x.len() / 3) <= i < final(out).len() ==> #[trigger] final(out)@[i] == old(out)@[i],
{
    let shuf = load256_u8(ENC_SHUF.as_slice(), 0);
    let lut = if url {
        load256_u8(ENC_LUT_URL.as_slice(), 0)
    } else {
        load256_u8(ENC_LUT_STD.as_slice(), 0)
    };
    proof {
        assert(ENC_SHUF@.subrange(0, 32) =~= ENC_SHUF@);
        assert(ENC_LUT_URL@.subrange(0, 32) =~= ENC_LUT_URL@);
        assert(ENC_LUT_STD@.subrange(0, 32) =~= ENC_LUT_STD@);
    }
    let n = x.len();
    let mut i: usize = 0;
    while i < n && n - i >= 28
        invariant
            avx2(),
            n == x.len(),
            n <= usize::MAX / 2,
            i % 3 == 0,
            i <= n,
            b256(shuf) == ENC_SHUF@,
            b256(lut) == if url { ENC_LUT_URL@ } else { ENC_LUT_STD@ },
            out.len() == old(out).len(),
            old(out).len() >= 4 * (n / 3),
            forall|k: int| 0 <= k < 4 * (i / 3) ==> #[trigger] out@[k] == enc_char(url, x@, k),
            forall|k: int| 4 * (n / 3) <= k < out.len() ==> #[trigger] out@[k] == old(out)@[k],
        decreases n - i,
    {
        let r = enc_block(url, x, i, shuf, lut);
        let o = i / 3 * 4;
        proof {
            assert(o + 32 == 4 * ((i + 24) / 3));
            assert((i + 24) / 3 <= n / 3);
        }
        let ghost before = out@;
        store256_u8(out, o, r);
        proof {
            assert forall|k: int| 0 <= k < 4 * ((i + 24) / 3) implies #[trigger] out@[k] == enc_char(url, x@, k) by {
                if k >= o {
                    assert(out@[k] == b256(r)[k - o]);
                    assert(b256(r)[(k - o)] == enc_char(url, x@, 4 * (i / 3) + (k - o)));
                } else {
                    assert(out@[k] == before[k]);
                }
            }
        }
        i = i + 24;
    }
    i / 3
}

/// Trusted: `encode_bulk_body` compiled with `avx2` enabled, through
/// `tf::encode_bulk`; the contract is `encode_bulk_body`'s, which is verified.
#[verifier::external_body]
pub fn encode_bulk(url: bool, x: &[u8], out: &mut [u8]) -> (g: usize)
    requires
        avx2(),
        x.len() <= usize::MAX / 2,
        old(out).len() >= 4 * (x.len() / 3),
    ensures
        final(out).len() == old(out).len(),
        g <= x.len() / 3,
        forall|i: int| 0 <= i < 4 * g ==> #[trigger] final(out)@[i] == enc_char(url, x@, i),
        forall|i: int| 4 * (x.len() / 3) <= i < final(out).len() ==> #[trigger] final(out)@[i] == old(out)@[i],
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::encode_bulk(url, x, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return encode_bulk_body(url, x, out);
}

/// Validation, by low nibble: a character is in the standard alphabet iff
/// its two nibbles' entries share no bit.
pub const DEC_LO_STD: [u8; 32] = [
    11, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 21, 23, 23, 23, 21,
    11, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 21, 23, 23, 23, 21,
];

/// Validation, by high nibble (standard alphabet).
pub const DEC_HI_STD: [u8; 32] = [
    1, 1, 2, 4, 8, 16, 8, 16, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 2, 4, 8, 16, 8, 16, 1, 1, 1, 1, 1, 1, 1, 1,
];

/// The offset from character to value, by `dkey` (standard alphabet).
pub const DEC_ROLL_STD: [u8; 32] = [
    0, 16, 19, 4, 191, 191, 185, 185, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 16, 19, 4, 191, 191, 185, 185, 0, 0, 0, 0, 0, 0, 0, 0,
];

/// As `DEC_LO_STD`, for the URL-safe alphabet.
pub const DEC_LO_URL: [u8; 32] = [
    11, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 55, 55, 53, 55, 39,
    11, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 55, 55, 53, 55, 39,
];

/// As `DEC_HI_STD`, for the URL-safe alphabet.
pub const DEC_HI_URL: [u8; 32] = [
    1, 1, 2, 4, 8, 16, 8, 32, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 2, 4, 8, 16, 8, 32, 1, 1, 1, 1, 1, 1, 1, 1,
];

/// As `DEC_ROLL_STD`, for the URL-safe alphabet.
pub const DEC_ROLL_URL: [u8; 32] = [
    0, 0, 17, 4, 191, 191, 185, 185, 0, 0, 0, 0, 0, 0, 0, 224,
    0, 0, 17, 4, 191, 191, 185, 185, 0, 0, 0, 0, 0, 0, 0, 224,
];

/// Packs the three low bytes of each 32-bit lane, most significant first.
pub const DEC_PACK: [u8; 32] = [
    2, 1, 0, 6, 5, 4, 10, 9, 8, 14, 13, 12, 128, 128, 128, 128,
    2, 1, 0, 6, 5, 4, 10, 9, 8, 14, 13, 12, 128, 128, 128, 128,
];

/// The character the roll key singles out (`/` or `_`), and what it adds to
/// the key.
pub open spec fn dec_c(url: bool) -> u8 {
    if url { 0x5F } else { 0x2F }
}

pub open spec fn dec_k(url: bool) -> u8 {
    if url { 0x0A } else { 0xFF }
}

pub open spec fn dec_lo(url: bool) -> Seq<u8> {
    if url { DEC_LO_URL@ } else { DEC_LO_STD@ }
}

pub open spec fn dec_hi(url: bool) -> Seq<u8> {
    if url { DEC_HI_URL@ } else { DEC_HI_STD@ }
}

pub open spec fn dec_roll(url: bool) -> Seq<u8> {
    if url { DEC_ROLL_URL@ } else { DEC_ROLL_STD@ }
}

/// The validation byte for `c`: zero iff `c` is in the alphabet.
pub open spec fn derr(url: bool, c: u8) -> u8 {
    dec_lo(url)[(c & 15) as int] & dec_hi(url)[(c >> 4) as int]
}

/// The roll-table index for `c`.
pub open spec fn dkey(url: bool, c: u8) -> u8 {
    (((c >> 4) + (if c == dec_c(url) { dec_k(url) } else { 0u8 })) % 256) as u8
}

/// The value the kernel computes for `c`.
pub open spec fn dval(url: bool, c: u8) -> u8 {
    ((c + (if dkey(url, c) >= 128 { 0u8 } else { dec_roll(url)[(dkey(url, c) % 16) as int] })) % 256) as u8
}

pub open spec fn dec_ok(url: bool, c: u8) -> bool {
    &&& (derr(url, c) == 0) == (val(url, c) is Some)
    &&& val(url, c) is Some ==> dval(url, c) == val(url, c)->0
}

pub proof fn lemma_dec_consts()
    ensures
        forall|c: u8| #[trigger] dec_ok(false, c),
        forall|c: u8| #[trigger] dec_ok(true, c),
        forall|k: int| 0 <= k < 16 ==> #[trigger] DEC_LO_STD@[k + 16] == DEC_LO_STD@[k] && DEC_HI_STD@[k + 16] == DEC_HI_STD@[k]
            && DEC_ROLL_STD@[k + 16] == DEC_ROLL_STD@[k] && DEC_LO_URL@[k + 16] == DEC_LO_URL@[k] && DEC_HI_URL@[k + 16]
            == DEC_HI_URL@[k] && DEC_ROLL_URL@[k + 16] == DEC_ROLL_URL@[k],
        forall|k: int| 0 <= k < 32 ==> #[trigger] DEC_PACK@[k] == if k % 16 < 12 { 4 * ((k % 16) / 3) + 2 - (k % 16) % 3 } else { 128 },
{
    let p0 = |i: int| dec_ok(false, i as u8);
    assert((0..256int).all_spec(|i: int| dec_ok(false, i as u8))) by (compute_only);
    vstd::compute::all_spec_ensures(0..256int, p0);
    let p1 = |i: int| dec_ok(true, i as u8);
    assert((0..256int).all_spec(|i: int| dec_ok(true, i as u8))) by (compute_only);
    vstd::compute::all_spec_ensures(0..256int, p1);
    assert forall|c: u8| #[trigger] dec_ok(false, c) by {
        assert(p0(c as int));
    }
    assert forall|c: u8| #[trigger] dec_ok(true, c) by {
        assert(p1(c as int));
    }
    let p2 = |k: int| DEC_LO_STD@[k + 16] == DEC_LO_STD@[k] && DEC_HI_STD@[k + 16] == DEC_HI_STD@[k]
            && DEC_ROLL_STD@[k + 16] == DEC_ROLL_STD@[k] && DEC_LO_URL@[k + 16] == DEC_LO_URL@[k] && DEC_HI_URL@[k + 16]
            == DEC_HI_URL@[k] && DEC_ROLL_URL@[k + 16] == DEC_ROLL_URL@[k];
    assert((0..16int).all_spec(|k: int| DEC_LO_STD@[k + 16] == DEC_LO_STD@[k] && DEC_HI_STD@[k + 16] == DEC_HI_STD@[k]
            && DEC_ROLL_STD@[k + 16] == DEC_ROLL_STD@[k] && DEC_LO_URL@[k + 16] == DEC_LO_URL@[k] && DEC_HI_URL@[k + 16]
            == DEC_HI_URL@[k] && DEC_ROLL_URL@[k + 16] == DEC_ROLL_URL@[k])) by (compute_only);
    vstd::compute::all_spec_ensures(0..16int, p2);
    assert forall|k: int| 0 <= k < 16 implies #[trigger] DEC_LO_STD@[k + 16] == DEC_LO_STD@[k] && DEC_HI_STD@[k + 16] == DEC_HI_STD@[k]
            && DEC_ROLL_STD@[k + 16] == DEC_ROLL_STD@[k] && DEC_LO_URL@[k + 16] == DEC_LO_URL@[k] && DEC_HI_URL@[k + 16]
            == DEC_HI_URL@[k] && DEC_ROLL_URL@[k + 16] == DEC_ROLL_URL@[k] by {
        assert(p2(k));
    }
    let p3 = |k: int| DEC_PACK@[k] == if k % 16 < 12 { 4 * ((k % 16) / 3) + 2 - (k % 16) % 3 } else { 128 };
    assert((0..32int).all_spec(|k: int| DEC_PACK@[k] == if k % 16 < 12 { 4 * ((k % 16) / 3) + 2 - (k % 16) % 3 } else { 128 })) by (compute_only);
    vstd::compute::all_spec_ensures(0..32int, p3);
    assert forall|k: int| 0 <= k < 32 implies #[trigger] DEC_PACK@[k] == if k % 16 < 12 { 4 * ((k % 16) / 3) + 2 - (k % 16) % 3 } else { 128 } by {
        assert(p3(k));
    }
}

/// The per-byte steps at byte `j`.
proof fn lemma_dec_byte_at(
    url: bool,
    ib: Seq<u8>,
    hb: Seq<u8>,
    k0f: Seq<u8>,
    lob: Seq<u8>,
    lt: Seq<u8>,
    ht: Seq<u8>,
    l: Seq<u8>,
    h: Seq<u8>,
    e: Seq<u8>,
    kc: Seq<u8>,
    kk: Seq<u8>,
    eq: Seq<u8>,
    ek: Seq<u8>,
    key: Seq<u8>,
    rt: Seq<u8>,
    roll: Seq<u8>,
    vb: Seq<u8>,
    j: int,
)
    requires
        0 <= j < 32,
        ib.len() == 32,
        forall|i: int| 0 <= i < 32 ==> #[trigger] hb[i] == ib[i] >> 4,
        hb.len() == 32,
        k0f == splat8(0x0f, 32),
        lob == and8(ib, k0f),
        lt == dec_lo(url),
        ht == dec_hi(url),
        rt == dec_roll(url),
        l == shuffle8_lanes(lt, lob),
        h == shuffle8_lanes(ht, hb),
        e == and8(l, h),
        kc == splat8(dec_c(url), 32),
        kk == splat8(dec_k(url), 32),
        eq == cmpeq8(ib, kc),
        ek == and8(eq, kk),
        key == add8(hb, ek),
        roll == shuffle8_lanes(rt, key),
        vb == add8(ib, roll),
    ensures
        e[j] == derr(url, ib[j]),
        vb[j] == dval(url, ib[j]),
{
    lemma_dec_consts();
    let c = ib[j];
    assert(c & 0x0f < 16) by (bit_vector);
    assert(c >> 4 < 16) by (bit_vector);
    assert(c & 0x0f == c & 15) by (bit_vector);
    let lo = (c & 15) as int;
    let hi = (c >> 4) as int;
    if j >= 16 {
        assert(lt[lo + 16] == lt[lo]);
        assert(ht[hi + 16] == ht[hi]);
    }
    assert(l[j] == lt[lo]);
    assert(h[j] == ht[hi]);
    assert(ek[j] == if c == dec_c(url) { dec_k(url) } else { 0u8 }) by {
        let x = if c == dec_c(url) { 0xffu8 } else { 0u8 };
        assert(eq[j] == x);
        let kv = dec_k(url);
        assert(0xffu8 & kv == kv) by (bit_vector);
        assert(0u8 & kv == 0) by (bit_vector);
    }
    assert(key[j] == dkey(url, c));
    let kj = dkey(url, c);
    if kj < 128 {
        let r = (kj % 16) as int;
        if j >= 16 {
            assert(rt[r + 16] == rt[r]);
        }
        assert(roll[j] == rt[r]);
    } else {
        assert(roll[j] == 0);
    }
    assert(roll[j] == (if kj >= 128 { 0u8 } else { rt[(kj % 16) as int] }));
    assert(vb[j] == ((c + roll[j]) % 256) as u8);
}

/// The per-byte steps: validation bytes and values.
proof fn lemma_dec_bytes(
    url: bool,
    ib: Seq<u8>,
    hb: Seq<u8>,
    k0f: Seq<u8>,
    lob: Seq<u8>,
    lt: Seq<u8>,
    ht: Seq<u8>,
    l: Seq<u8>,
    h: Seq<u8>,
    e: Seq<u8>,
    kc: Seq<u8>,
    kk: Seq<u8>,
    eq: Seq<u8>,
    ek: Seq<u8>,
    key: Seq<u8>,
    rt: Seq<u8>,
    roll: Seq<u8>,
    vb: Seq<u8>,
)
    requires
        ib.len() == 32,
        forall|i: int| 0 <= i < 32 ==> #[trigger] hb[i] == ib[i] >> 4,
        hb.len() == 32,
        k0f == splat8(0x0f, 32),
        lob == and8(ib, k0f),
        lt == dec_lo(url),
        ht == dec_hi(url),
        rt == dec_roll(url),
        l == shuffle8_lanes(lt, lob),
        h == shuffle8_lanes(ht, hb),
        e == and8(l, h),
        kc == splat8(dec_c(url), 32),
        kk == splat8(dec_k(url), 32),
        eq == cmpeq8(ib, kc),
        ek == and8(eq, kk),
        key == add8(hb, ek),
        roll == shuffle8_lanes(rt, key),
        vb == add8(ib, roll),
    ensures
        e.len() == 32,
        vb.len() == 32,
        forall|j: int| 0 <= j < 32 ==> #[trigger] e[j] == derr(url, ib[j]),
        forall|j: int| 0 <= j < 32 ==> #[trigger] vb[j] == dval(url, ib[j]),
{
    assert forall|j: int| 0 <= j < 32 implies #[trigger] e[j] == derr(url, ib[j]) by {
        lemma_dec_byte_at(url, ib, hb, k0f, lob, lt, ht, l, h, e, kc, kk, eq, ek, key, rt, roll, vb, j);
    }
    assert forall|j: int| 0 <= j < 32 implies #[trigger] vb[j] == dval(url, ib[j]) by {
        lemma_dec_byte_at(url, ib, hb, k0f, lob, lt, ht, l, h, e, kc, kk, eq, ek, key, rt, roll, vb, j);
    }
}

/// The packing arithmetic of one 32-bit lane: four 6-bit values make three
/// bytes, most significant first.
proof fn lemma_pack_lane(p: u8, q: u8, r: u8, w: u8)
    requires
        p < 64,
        q < 64,
        r < 64,
        w < 64,
    ensures
        ({
            let n = ((p as int * 64 + q as int) * 4096 + (r as int * 64 + w as int)) as u32;
            byte32(n, 2) == dbyte(p, q, r, w, 0) && byte32(n, 1) == dbyte(p, q, r, w, 1) && byte32(n, 0) == dbyte(p, q, r, w, 2)
        }),
{
    let n32 = ((p as u32) << 18u32) | ((q as u32) << 12u32) | ((r as u32) << 6u32) | (w as u32);
    assert(p < 64 && q < 64 && r < 64 && w < 64 ==> ((p as u32) << 18u32) | ((q as u32) << 12u32) | ((r as u32) << 6u32) | (w as u32)
        == (p as u32) * 262144 + (q as u32) * 4096 + (r as u32) * 64 + (w as u32)) by (bit_vector);
    assert(n32 as int == p as int * 262144 + q as int * 4096 + r as int * 64 + w as int);
    assert(p < 64 && q < 64 && r < 64 && w < 64 ==> ((((((p as u32) << 18u32) | ((q as u32) << 12u32) | ((r as u32) << 6u32) | (w as u32)) >> 16u32) & 0xff) as u8) == (p << 2) | (q >> 4)) by (bit_vector);
    assert(p < 64 && q < 64 && r < 64 && w < 64 ==> ((((((p as u32) << 18u32) | ((q as u32) << 12u32) | ((r as u32) << 6u32) | (w as u32)) >> 8u32) & 0xff) as u8) == (q << 4) | (r >> 2)) by (bit_vector);
    assert(p < 64 && q < 64 && r < 64 && w < 64 ==> (((((p as u32) << 18u32) | ((q as u32) << 12u32) | ((r as u32) << 6u32) | (w as u32)) & 0xff) as u8) == (r << 6) | w) by (bit_vector);
}

/// The multiply-adds put the 24-bit value of group `g` in 32-bit lane `g`.
proof fn lemma_dec_madd(vb: Seq<u8>, k1: Seq<u8>, mb: Seq<u8>, k2: Seq<u8>, nb: Seq<u8>)
    requires
        vb.len() == 32 && k1.len() == 32 && mb.len() == 32 && k2.len() == 32 && nb.len() == 32,
        forall|j: int| 0 <= j < 32 ==> #[trigger] vb[j] < 64,
        u32s(k1) == splat32(0x01400140, 8),
        u16s(mb) == maddubs(vb, k1),
        u32s(k2) == splat32(0x00011000, 8),
        u32s(nb) == madd16(u16s(mb), u16s(k2)),
    ensures
        forall|g: int| 0 <= g < 8 ==> #[trigger] u32s(nb)[g] == ((vb[4 * g] as int * 64 + vb[4 * g + 1] as int) * 4096 + (vb[4 * g + 2] as int * 64 + vb[4 * g + 3] as int)) as u32,
{
    lemma_u32s_bytes(k1);
    lemma_u16s_of_u32s(k2);
    assert forall|g: int| 0 <= g < 8 implies #[trigger] u32s(nb)[g] == ((vb[4 * g] as int * 64 + vb[4 * g + 1] as int) * 4096 + (vb[4 * g + 2] as int * 64 + vb[4 * g + 3] as int)) as u32 by {
        assert(byte32(0x01400140u32, 0) == 0x40 && byte32(0x01400140u32, 1) == 1 && byte32(0x01400140u32, 2) == 0x40 && byte32(0x01400140u32, 3) == 1) by (compute_only);
        assert(k1[4 * g] == byte32(u32s(k1)[g], 0));
        assert(k1[4 * g + 1] == byte32(u32s(k1)[g], 1));
        assert(k1[4 * g + 2] == byte32(u32s(k1)[g], 2));
        assert(k1[4 * g + 3] == byte32(u32s(k1)[g], 3));
        let m0 = u16s(mb)[2 * g];
        let m1 = u16s(mb)[2 * g + 1];
        assert(k1[4 * g] == 0x40 && k1[4 * g + 1] == 1 && k1[4 * g + 2] == 0x40 && k1[4 * g + 3] == 1);
        assert(s8(0x40) == 64 && s8(1) == 1);
        let (a0, a1, a2, a3) = (vb[4 * g], vb[4 * g + 1], vb[4 * g + 2], vb[4 * g + 3]);
        assert(a0 * 64 <= 63 * 64 && a2 * 64 <= 63 * 64) by (nonlinear_arith)
            requires
                a0 < 64,
                a2 < 64,
        ;
        assert(2 * (2 * g) == 4 * g && 2 * (2 * g) + 1 == 4 * g + 1);
        assert(2 * (2 * g + 1) == 4 * g + 2 && 2 * (2 * g + 1) + 1 == 4 * g + 3);
        assert(maddubs(vb, k1)[2 * g] == (sat_s16(a0 * s8(k1[4 * g]) + a1 * s8(k1[4 * g + 1])) % 0x10000) as u16);
        assert(maddubs(vb, k1)[2 * g + 1] == (sat_s16(a2 * s8(k1[4 * g + 2]) + a3 * s8(k1[4 * g + 3])) % 0x10000) as u16);
        assert(m0 as int == a0 as int * 64 + a1 as int);
        assert(m1 as int == a2 as int * 64 + a3 as int);
        assert((0x00011000u32 & 0xffff) as u16 == 0x1000 && (0x00011000u32 >> 16u32) as u16 == 1) by (compute_only);
        assert(u16s(k2)[2 * g] == 0x1000);
        assert(u16s(k2)[2 * g + 1] == 1);
        assert(s16(m0) == m0 as int && s16(m1) == m1 as int);
        assert(s16(0x1000u16) == 4096 && s16(1u16) == 1);
        let x = s16(m0) * s16(0x1000u16) + s16(m1) * s16(1u16);
        assert(x == m0 as int * 4096 + m1 as int);
        assert(0 <= m0 as int * 4096 <= 4095 * 4096) by (nonlinear_arith)
            requires
                0 <= m0 as int <= 4095,
        ;
        assert(madd16(u16s(mb), u16s(k2))[g] == (x % 0x1_0000_0000) as u32);
        assert(x % 0x1_0000_0000 == x);
    }
}

/// From the per-byte facts to the kernel's postcondition.
proof fn lemma_dec_block_out(
    url: bool,
    ss: Seq<u8>,
    j: int,
    ib: Seq<u8>,
    eb: Seq<u8>,
    vb: Seq<u8>,
    k1: Seq<u8>,
    mb: Seq<u8>,
    k2: Seq<u8>,
    nb: Seq<u8>,
    pb: Seq<u8>,
    perm: Seq<u32>,
    ob: Seq<u8>,
)
    requires
        0 <= j,
        j + 32 <= ss.len(),
        ib == ss.subrange(j, j + 32),
        eb.len() == 32 && vb.len() == 32 && k1.len() == 32 && mb.len() == 32 && k2.len() == 32 && nb.len() == 32,
        pb.len() == 32 && ob.len() == 32,
        forall|k: int| 0 <= k < 32 ==> #[trigger] eb[k] == derr(url, ib[k]),
        forall|k: int| 0 <= k < 32 ==> #[trigger] vb[k] == dval(url, ib[k]),
        u32s(k1) == splat32(0x01400140, 8),
        u16s(mb) == maddubs(vb, k1),
        u32s(k2) == splat32(0x00011000, 8),
        u32s(nb) == madd16(u16s(mb), u16s(k2)),
        pb == shuffle8_lanes(nb, DEC_PACK@),
        perm == seq![0u32, 1, 2, 4, 5, 6, 3, 7],
        u32s(ob) == permvar32(u32s(pb), perm),
    ensures
        forall|k: int| 0 <= k < 32 ==> (#[trigger] eb[k] == 0) == (val(url, ss[j + k]) is Some),
        (forall|k: int| 0 <= k < 32 ==> val(url, #[trigger] ss[j + k]) is Some) ==> forall|t: int| 0 <= t < 24 ==> #[trigger] ob[t] == dbyte(
            v(url, ss, j + 4 * (t / 3)),
            v(url, ss, j + 4 * (t / 3) + 1),
            v(url, ss, j + 4 * (t / 3) + 2),
            v(url, ss, j + 4 * (t / 3) + 3),
            t % 3,
        ),
{
    lemma_dec_consts();
    assert forall|k: int| 0 <= k < 32 implies (#[trigger] eb[k] == 0) == (val(url, ss[j + k]) is Some) by {
        assert(ib[k] == ss[j + k]);
        assert(dec_ok(url, ib[k]));
    }
    if forall|k: int| 0 <= k < 32 ==> val(url, #[trigger] ss[j + k]) is Some {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] vb[k] < 64 && vb[k] == v(url, ss, j + k) by {
            assert(ib[k] == ss[j + k]);
            assert(val(url, ss[j + k]) is Some);
            assert(dec_ok(url, ib[k]));
            lemma_sym_val(url, ib[k]);
        }
        lemma_dec_madd(vb, k1, mb, k2, nb);
        assert forall|t: int| 0 <= t < 24 implies #[trigger] ob[t] == dbyte(
            v(url, ss, j + 4 * (t / 3)),
            v(url, ss, j + 4 * (t / 3) + 1),
            v(url, ss, j + 4 * (t / 3) + 2),
            v(url, ss, j + 4 * (t / 3) + 3),
            t % 3,
        ) by {
            lemma_dec_pack_byte(url, ss, j, vb, nb, pb, perm, ob, t);
        }
    }
}

/// The index arithmetic of the packing, for output byte `t`: it comes
/// from byte `pt` of the shuffled vector (through the permutation), which
/// comes from byte `ns` of the multiply-add result.
pub open spec fn pack_src(t: int) -> int {
    if t < 12 { t / 4 } else { t / 4 + 1 }
}

pub open spec fn pack_pt(t: int) -> int {
    4 * pack_src(t) + t % 4
}

pub open spec fn pack_ns(t: int) -> int {
    (pack_pt(t) / 16) * 16 + DEC_PACK@[pack_pt(t)] as int
}

pub open spec fn pack_facts(t: int) -> bool {
    &&& seq![0u32, 1, 2, 4, 5, 6, 3, 7][t / 4] as int == pack_src(t)
    &&& 0 <= pack_pt(t) < 32
    &&& pack_pt(t) / 4 == pack_src(t)
    &&& pack_pt(t) % 4 == t % 4
    &&& DEC_PACK@[pack_pt(t)] < 16
    &&& pack_ns(t) == 4 * (t / 3) + 2 - t % 3
    &&& pack_ns(t) / 4 == t / 3
    &&& pack_ns(t) % 4 == 2 - t % 3
}

proof fn lemma_pack_facts()
    ensures
        forall|t: int| 0 <= t < 24 ==> #[trigger] pack_facts(t),
{
    let p = |t: int| pack_facts(t);
    assert((0..24int).all_spec(|t: int| pack_facts(t))) by (compute_only);
    vstd::compute::all_spec_ensures(0..24int, p);
}

/// One output byte, through the byte shuffle and the lane permutation.
#[verifier::spinoff_prover]
proof fn lemma_dec_pack_byte(url: bool, ss: Seq<u8>, j: int, vb: Seq<u8>, nb: Seq<u8>, pb: Seq<u8>, perm: Seq<u32>, ob: Seq<u8>, t: int)
    requires
        0 <= t < 24,
        0 <= j,
        j + 32 <= ss.len(),
        vb.len() == 32 && nb.len() == 32 && pb.len() == 32 && ob.len() == 32,
        forall|k: int| 0 <= k < 32 ==> #[trigger] vb[k] < 64 && vb[k] == v(url, ss, j + k),
        forall|g: int| 0 <= g < 8 ==> #[trigger] u32s(nb)[g] == ((vb[4 * g] as int * 64 + vb[4 * g + 1] as int) * 4096 + (vb[4 * g + 2] as int * 64 + vb[4 * g + 3] as int)) as u32,
        pb == shuffle8_lanes(nb, DEC_PACK@),
        perm == seq![0u32, 1, 2, 4, 5, 6, 3, 7],
        u32s(ob) == permvar32(u32s(pb), perm),
    ensures
        ob[t] == dbyte(
            v(url, ss, j + 4 * (t / 3)),
            v(url, ss, j + 4 * (t / 3) + 1),
            v(url, ss, j + 4 * (t / 3) + 2),
            v(url, ss, j + 4 * (t / 3) + 3),
            t % 3,
        ),
{
    lemma_dec_consts();
    let g = t / 3;
    let p = vb[4 * g];
    let q = vb[4 * g + 1];
    let r = vb[4 * g + 2];
    let w = vb[4 * g + 3];
    assert(p == v(url, ss, j + 4 * g));
    assert(q == v(url, ss, j + 4 * g + 1));
    assert(r == v(url, ss, j + 4 * g + 2));
    assert(w == v(url, ss, j + 4 * g + 3));
    lemma_pack_lane(p, q, r, w);
    lemma_pack_facts();
    assert(pack_facts(t));
    lemma_pack_perm(pb, perm, ob, t);
    lemma_pack_shuf(nb, pb, t);
    let n = u32s(nb)[g];
    assert(ob[t] == byte32(n, 2 - t % 3));
    if t % 3 == 0 {
        assert(byte32(n, 2) == dbyte(p, q, r, w, 0));
    } else if t % 3 == 1 {
        assert(byte32(n, 1) == dbyte(p, q, r, w, 1));
    } else {
        assert(byte32(n, 0) == dbyte(p, q, r, w, 2));
    }
}

proof fn lemma_pack_perm(pb: Seq<u8>, perm: Seq<u32>, ob: Seq<u8>, t: int)
    requires
        0 <= t < 24,
        pb.len() == 32 && ob.len() == 32,
        pack_facts(t),
        perm == seq![0u32, 1, 2, 4, 5, 6, 3, 7],
        u32s(ob) == permvar32(u32s(pb), perm),
    ensures
        ob[t] == pb[pack_pt(t)],
{
    let src = pack_src(t);
    let pt = pack_pt(t);
    lemma_byte_of_lane(ob, t);
    lemma_byte_of_lane(pb, pt);
    assert(perm[t / 4] % 8 == src);
    assert(u32s(ob)[t / 4] == u32s(pb)[src]);
}

proof fn lemma_pack_shuf(nb: Seq<u8>, pb: Seq<u8>, t: int)
    requires
        0 <= t < 24,
        nb.len() == 32 && pb.len() == 32,
        pack_facts(t),
        pb == shuffle8_lanes(nb, DEC_PACK@),
    ensures
        pb[pack_pt(t)] == byte32(u32s(nb)[t / 3], 2 - t % 3),
{
    let pt = pack_pt(t);
    let ns = pack_ns(t);
    assert(DEC_PACK@[pt] % 16 == DEC_PACK@[pt]);
    assert(pb[pt] == nb[ns]);
    lemma_byte_of_lane(nb, ns);
}

/// The 24 bytes decoded from the 32 characters at `s[j..]`, and whether
/// all of them are in the alphabet (`err` is all zero).
#[inline(always)]
fn dec_block(url: bool, s: &[u8], j: usize, lo_t: __m256i, hi_t: __m256i, roll_t: __m256i, pack: __m256i, perm: __m256i) -> (r: (__m256i, __m256i))
    requires
        avx2(),
        j + 32 <= s.len(),
        b256(lo_t) == dec_lo(url),
        b256(hi_t) == dec_hi(url),
        b256(roll_t) == dec_roll(url),
        b256(pack) == DEC_PACK@,
        u32x8(perm) == seq![0u32, 1, 2, 4, 5, 6, 3, 7],
    ensures
        forall|k: int| 0 <= k < 32 ==> (#[trigger] b256(r.1)[k] == 0) == (val(url, s@[j + k]) is Some),
        (forall|k: int| 0 <= k < 32 ==> val(url, #[trigger] s@[j + k]) is Some) ==> forall|t: int| 0 <= t < 24 ==> #[trigger] b256(r.0)[t] == dbyte(
            v(url, s@, j + 4 * (t / 3)),
            v(url, s@, j + 4 * (t / 3) + 1),
            v(url, s@, j + 4 * (t / 3) + 2),
            v(url, s@, j + 4 * (t / 3) + 3),
            t % 3,
        ),
{
    let inp = load256_u8(s, j);
    let sh = _mm256_srli_epi32::<4>(inp);
    let k0f = _mm256_set1_epi8(0x0f);
    let hb = _mm256_and_si256(sh, k0f);
    let lob = _mm256_and_si256(inp, k0f);
    let l = _mm256_shuffle_epi8(lo_t, lob);
    let h = _mm256_shuffle_epi8(hi_t, hb);
    let e = _mm256_and_si256(l, h);
    let kc = _mm256_set1_epi8(if url { 0x5Fi8 } else { 0x2Fi8 });
    let kk = _mm256_set1_epi8(if url { 0x0Ai8 } else { -1i8 });
    let eq = _mm256_cmpeq_epi8(inp, kc);
    let ek = _mm256_and_si256(eq, kk);
    let key = _mm256_add_epi8(hb, ek);
    let roll = _mm256_shuffle_epi8(roll_t, key);
    let vals = _mm256_add_epi8(inp, roll);
    let k1 = _mm256_set1_epi32(0x01400140);
    let m = _mm256_maddubs_epi16(vals, k1);
    let k2 = _mm256_set1_epi32(0x00011000);
    let nv = _mm256_madd_epi16(m, k2);
    let pk = _mm256_shuffle_epi8(nv, pack);
    let out = _mm256_permutevar8x32_epi32(pk, perm);
    proof {
        let ib = b256(inp);
        assert(ib == s@.subrange(j as int, j + 32));
        assert(u8_of_i8(0x0f) == 0x0f);
        assert(u8_of_i8(if url { 0x5Fi8 } else { 0x2Fi8 }) == dec_c(url));
        assert(u8_of_i8(if url { 0x0Ai8 } else { -1i8 }) == dec_k(url));
        assert(u32_of_i32(0x01400140) == 0x01400140);
        assert(u32_of_i32(0x00011000) == 0x00011000);
        lemma_hi_nibbles(ib, b256(sh), b256(k0f), b256(hb));
        lemma_dec_bytes(url, ib, b256(hb), b256(k0f), b256(lob), b256(lo_t), b256(hi_t), b256(l), b256(h), b256(e),
            b256(kc), b256(kk), b256(eq), b256(ek), b256(key), b256(roll_t), b256(roll), b256(vals));
        lemma_dec_block_out(url, s@, j as int, ib, b256(e), b256(vals), b256(k1), b256(m), b256(k2), b256(nv), b256(pk), u32x8(perm), b256(out));
    }
    (out, e)
}

/// Decodes full groups of the body `s[..m]` 32 characters at a time while
/// the 32-byte stores stay inside `out`. Returns the number of groups done
/// and whether all their characters are in the alphabet; if so, their bytes
/// are in `out`.
#[inline(always)]
pub fn decode_bulk_body(url: bool, s: &[u8], m: usize, out: &mut [u8]) -> (r: (usize, bool))
    requires
        avx2(),
        m <= s.len(),
        old(out).len() >= 3 * (m / 4),
    ensures
        final(out).len() == old(out).len(),
        r.0 <= m / 4,
        r.1 <==> forall|k: int| 0 <= k < 4 * r.0 ==> (#[trigger] val(url, s@[k])) is Some,
        r.1 ==> forall|i: int| 0 <= i < 3 * r.0 ==> #[trigger] final(out)@[i] == dec_byte(url, s@, m as int, i),
{
    let lo_t = if url { load256_u8(DEC_LO_URL.as_slice(), 0) } else { load256_u8(DEC_LO_STD.as_slice(), 0) };
    let hi_t = if url { load256_u8(DEC_HI_URL.as_slice(), 0) } else { load256_u8(DEC_HI_STD.as_slice(), 0) };
    let roll_t = if url { load256_u8(DEC_ROLL_URL.as_slice(), 0) } else { load256_u8(DEC_ROLL_STD.as_slice(), 0) };
    let pack = load256_u8(DEC_PACK.as_slice(), 0);
    let perm = _mm256_setr_epi32(0, 1, 2, 4, 5, 6, 3, 7);
    let zero = _mm256_setzero_si256();
    proof {
        assert(DEC_LO_URL@.subrange(0, 32) =~= DEC_LO_URL@);
        assert(DEC_LO_STD@.subrange(0, 32) =~= DEC_LO_STD@);
        assert(DEC_HI_URL@.subrange(0, 32) =~= DEC_HI_URL@);
        assert(DEC_HI_STD@.subrange(0, 32) =~= DEC_HI_STD@);
        assert(DEC_ROLL_URL@.subrange(0, 32) =~= DEC_ROLL_URL@);
        assert(DEC_ROLL_STD@.subrange(0, 32) =~= DEC_ROLL_STD@);
        assert(DEC_PACK@.subrange(0, 32) =~= DEC_PACK@);
        assert(u32x8(perm) =~= seq![0u32, 1, 2, 4, 5, 6, 3, 7]);
    }
    let mut err = zero;
    let mut j: usize = 0;
    while j < m && m - j >= 32 && j / 4 * 3 < out.len() && out.len() - j / 4 * 3 >= 32
        invariant
            avx2(),
            m <= s.len(),
            j <= m,
            j % 4 == 0,
            out.len() == old(out).len(),
            old(out).len() >= 3 * (m / 4),
            b256(lo_t) == dec_lo(url),
            b256(hi_t) == dec_hi(url),
            b256(roll_t) == dec_roll(url),
            b256(pack) == DEC_PACK@,
            u32x8(perm) == seq![0u32, 1, 2, 4, 5, 6, 3, 7],
            b256(zero) == splat8(0u8, 32),
            (forall|k: int| 0 <= k < 32 ==> #[trigger] b256(err)[k] == 0) <==> forall|k: int| 0 <= k < j ==> (#[trigger] val(url, s@[k])) is Some,
            (forall|k: int| 0 <= k < 32 ==> #[trigger] b256(err)[k] == 0) ==> forall|i: int| 0 <= i < 3 * (j / 4) ==> #[trigger] out@[i] == dec_byte(url, s@, m as int, i),
        decreases m - j,
    {
        let (o, e) = dec_block(url, s, j, lo_t, hi_t, roll_t, pack, perm);
        let ghost err0 = err;
        err = _mm256_or_si256(err, e);
        let oi = j / 4 * 3;
        let ghost before = out@;
        store256_u8(out, oi, o);
        proof {
            assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(err)[k] == b256(err0)[k] | b256(e)[k] by {}
            assert forall|x: u8, y: u8| (x | y == 0) == (x == 0 && y == 0) by {
                assert((x | y == 0) == (x == 0 && y == 0)) by (bit_vector);
            }
            let allz = forall|k: int| 0 <= k < 32 ==> #[trigger] b256(err)[k] == 0;
            let allz0 = forall|k: int| 0 <= k < 32 ==> #[trigger] b256(err0)[k] == 0;
            let alle = forall|k: int| 0 <= k < 32 ==> #[trigger] b256(e)[k] == 0;
            assert(allz == (allz0 && alle)) by {
                if allz {
                    assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(err0)[k] == 0 by {
                        assert(b256(err)[k] == 0);
                    }
                    assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(e)[k] == 0 by {
                        assert(b256(err)[k] == 0);
                    }
                }
                if allz0 && alle {
                    assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(err)[k] == 0 by {
                        assert(b256(err0)[k] == 0 && b256(e)[k] == 0);
                    }
                }
            }
            let valid_new = forall|k: int| 0 <= k < 32 ==> val(url, #[trigger] s@[j + k]) is Some;
            assert(alle == valid_new) by {
                if alle {
                    assert forall|k: int| 0 <= k < 32 implies val(url, #[trigger] s@[j + k]) is Some by {
                        assert(b256(e)[k] == 0);
                    }
                }
                if valid_new {
                    assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(e)[k] == 0 by {
                        assert(val(url, s@[j + k]) is Some);
                    }
                }
            }
            assert(allz == forall|k: int| 0 <= k < j + 32 ==> (#[trigger] val(url, s@[k])) is Some) by {
                if allz {
                    assert forall|k: int| 0 <= k < j + 32 implies (#[trigger] val(url, s@[k])) is Some by {
                        if k >= j {
                            assert(val(url, s@[j + (k - j)]) is Some);
                        }
                    }
                }
                if forall|k: int| 0 <= k < j + 32 ==> (#[trigger] val(url, s@[k])) is Some {
                    assert forall|k: int| 0 <= k < 32 implies val(url, #[trigger] s@[j + k]) is Some by {
                        assert(val(url, s@[j + k]) is Some);
                    }
                }
            }
            if allz {
                assert forall|i: int| 0 <= i < 3 * ((j + 32) / 4) implies #[trigger] out@[i] == dec_byte(url, s@, m as int, i) by {
                    if i >= oi {
                        let t = i - oi;
                        assert(out@[i] == b256(o)[t]);
                        let g = j / 4 + t / 3;
                        assert(i / 3 == g && i % 3 == t % 3) by {
                            assert(i == 3 * g + t % 3);
                            lemma_byte_index(g, t % 3);
                        }
                        assert(4 * g + 3 < m);
                        assert(j + 4 * (t / 3) == 4 * g);
                    } else {
                        assert(out@[i] == before[i]);
                    }
                }
            }
        }
        j = j + 32;
    }
    let c = _mm256_cmpeq_epi8(err, zero);
    let mm = _mm256_movemask_epi8(c);
    proof {
        lemma_all_zero(b256(err), b256(zero), b256(c), mm);
    }
    (j / 4, mm == -1)
}

/// Trusted: `decode_bulk_body` compiled with `avx2` enabled, through
/// `tf::decode_bulk`; the contract is `decode_bulk_body`'s, which is verified.
#[verifier::external_body]
pub fn decode_bulk(url: bool, s: &[u8], m: usize, out: &mut [u8]) -> (r: (usize, bool))
    requires
        avx2(),
        m <= s.len(),
        old(out).len() >= 3 * (m / 4),
    ensures
        final(out).len() == old(out).len(),
        r.0 <= m / 4,
        r.1 <==> forall|k: int| 0 <= k < 4 * r.0 ==> (#[trigger] val(url, s@[k])) is Some,
        r.1 ==> forall|i: int| 0 <= i < 3 * r.0 ==> #[trigger] final(out)@[i] == dec_byte(url, s@, m as int, i),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::decode_bulk(url, s, m, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return decode_bulk_body(url, s, m, out);
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
    pub(super) unsafe fn encode_bulk(url: bool, x: &[u8], out: &mut [u8]) -> usize {
        encode_bulk_body(url, x, out)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn decode_bulk(url: bool, s: &[u8], m: usize, out: &mut [u8]) -> (usize, bool) {
        decode_bulk_body(url, s, m, out)
    }
}
