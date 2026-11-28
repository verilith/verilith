//! The encoder's 4:2:0 chroma downsampling on AVX2, sixteen samples at a
//! time, proven equal to the scalar `down_plane` (`enc_spec::samp`): the
//! four samples summed in 16-bit lanes, the alternating bias added, and
//! the sum shifted down by two, as libjpeg-turbo's `h2v2_downsample` does.
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

/// A 4:2:0 chroma sample (`enc_spec::samp`), from its four samples.
pub open spec fn down4(ra: Seq<u8>, rb: Seq<u8>, x: int) -> int {
    (ra[2 * x] + ra[2 * x + 1] + rb[2 * x] + rb[2 * x + 1] + 1 + x % 2) / 4
}

/// The sums of adjacent bytes, as 16-bit lanes.
#[inline(always)]
fn pairsum(a: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] u16x16(r)[i] as int == b256(a)[2 * i] + b256(a)[2 * i + 1],
{
    let ones = _mm256_set1_epi8(1);
    let r = _mm256_maddubs_epi16(a, ones);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] u16x16(r)[i] as int == b256(a)[2 * i] + b256(a)[2 * i + 1] by {
            assert(b256(ones)[2 * i] == 1u8 && b256(ones)[2 * i + 1] == 1u8);
            assert(s8(1u8) == 1);
            let u = b256(a)[2 * i] + b256(a)[2 * i + 1];
            assert(s8(b256(ones)[2 * i]) == 1 && s8(b256(ones)[2 * i + 1]) == 1);
            assert(b256(a)[2 * i] * s8(b256(ones)[2 * i]) == b256(a)[2 * i] as int) by (nonlinear_arith)
                requires
                    s8(b256(ones)[2 * i]) == 1,
            ;
            assert(b256(a)[2 * i + 1] * s8(b256(ones)[2 * i + 1]) == b256(a)[2 * i + 1] as int) by (nonlinear_arith)
                requires
                    s8(b256(ones)[2 * i + 1]) == 1,
            ;
            assert(b256(a)[2 * i] * s8(b256(ones)[2 * i]) + b256(a)[2 * i + 1] * s8(b256(ones)[2 * i + 1]) == u);
            lemma_small_mod(u as nat, 0x10000);
        }
    }
    r
}

/// `(a + b + 1 + i % 2) / 4` in lane `i`.
#[inline(always)]
fn avg4(sa: __m256i, sb: __m256i) -> (v: __m256i)
    requires
        avx2(),
        forall|i: int| 0 <= i < 16 ==> #[trigger] u16x16(sa)[i] <= 510 && u16x16(sb)[i] <= 510,
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] u16x16(v)[i] as int == (u16x16(sa)[i] + u16x16(sb)[i] + 1 + i % 2) / 4,
{
    let s = _mm256_add_epi16(sa, sb);
    let bias = _mm256_set1_epi32(0x0002_0001);
    let t = _mm256_add_epi16(s, bias);
    let v = _mm256_srli_epi16::<2>(t);
    proof {
        reveal_with_fuel(pow2_spec, 3);
        lemma_u16s_of_u32s(b256(bias));
        assert((0x0002_0001u32 & 0xffff) as u16 == 1u16 && (0x0002_0001u32 >> 16u32) as u16 == 2u16) by (bit_vector);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] u16x16(v)[i] as int == (u16x16(sa)[i] + u16x16(sb)[i] + 1 + i % 2) / 4 by {
            let l = i / 2;
            assert(u16x16(bias)[2 * l] == (u32x8(bias)[l] & 0xffff) as u16);
            assert(u16x16(bias)[2 * l + 1] == (u32x8(bias)[l] >> 16u32) as u16);
            assert(u16x16(bias)[i] as int == 1 + i % 2);
            let u = u16x16(sa)[i] + u16x16(sb)[i];
            assert(u16x16(sa)[i] <= 510 && u16x16(sb)[i] <= 510);
            lemma_small_mod(u as nat, 0x10000);
            lemma_small_mod((u + 1 + i % 2) as nat, 0x10000);
        }
    }
    v
}

/// The sixteen 16-bit lanes of `v`, each below 256, as bytes.
#[inline(always)]
fn narrow(v: __m256i, out: &mut [u8; 16])
    requires
        avx2(),
        forall|i: int| 0 <= i < 16 ==> #[trigger] u16x16(v)[i] <= 255,
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] final(out)[i] == u16x16(v)[i],
{
    let pk = _mm256_packus_epi16(v, v);
    let lo = _mm256_castsi256_si128(pk);
    let hi = _mm256_extracti128_si256::<1>(pk);
    storel64_u8(out, 0, lo);
    storel64_u8(out, 8, hi);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] out[i] == u16x16(v)[i] by {
            let k = if i < 8 { i } else { i + 8 };
            assert(out[i] == b256(pk)[k]);
            assert(b256(pk)[k] == sat_u8(s16(u16x16(v)[(k / 16) * 8 + k % 16])));
            assert((k / 16) * 8 + k % 16 == i);
        }
    }
}

/// Sixteen 4:2:0 chroma samples, `x..x + 16`, from rows `ra` and `rb`, as
/// libjpeg-turbo's `h2v2_downsample` computes them.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
pub fn down16(ra: &[u8], rb: &[u8], x: usize, out: &mut [u8; 16])
    requires
        avx2(),
        x % 2 == 0,
        x < 0x4000_0000,
        2 * x + 32 <= ra@.len(),
        2 * x + 32 <= rb@.len(),
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] final(out)[i] as int == down4(ra@, rb@, x + i),
{
    let a = load256_u8(ra, 2 * x);
    let b = load256_u8(rb, 2 * x);
    let sa = pairsum(a);
    let sb = pairsum(b);
    let v = avg4(sa, sb);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] u16x16(v)[i] as int == down4(ra@, rb@, x + i) && u16x16(v)[i] <= 255 by {
            assert(b256(a)[2 * i] == ra@[2 * x + 2 * i] && b256(a)[2 * i + 1] == ra@[2 * x + 2 * i + 1]);
            assert(b256(b)[2 * i] == rb@[2 * x + 2 * i] && b256(b)[2 * i + 1] == rb@[2 * x + 2 * i + 1]);
            assert(u16x16(sa)[i] as int == b256(a)[2 * i] + b256(a)[2 * i + 1]);
            assert(u16x16(sb)[i] as int == b256(b)[2 * i] + b256(b)[2 * i + 1]);
            assert((x + i) % 2 == i % 2);
            assert(2 * (x + i) == 2 * x + 2 * i);
        }
    }
    narrow(v, out);
}


} // verus!
