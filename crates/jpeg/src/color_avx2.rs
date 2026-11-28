//! The encoder's colour conversion on AVX2, eight 4-byte pixels at a time,
//! proven equal to `enc_spec::ycc`: the same unsigned 32-bit arithmetic as
//! `enc_front::ycc_x`, one pixel per 32-bit lane. Nothing wraps (every
//! numerator is below 2^24), so each lane computes exactly `ycc`.
use crate::enc_spec::*;
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

/// 32-bit lane `m` of `v`, unsigned.
pub open spec fn uv(v: __m256i, m: int) -> int {
    u32x8(v)[m] as int
}

/// Every lane of `v` is at most `b`.
pub open spec fn ub(v: __m256i, b: int) -> bool {
    forall|m: int| 0 <= m < 8 ==> #[trigger] uv(v, m) <= b
}

#[inline(always)]
fn uadd(a: __m256i, b: __m256i, Ghost(ba): Ghost<int>, Ghost(bb): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        ub(a, ba),
        ub(b, bb),
        ba + bb < 0x1_0000_0000,
    ensures
        ub(r, ba + bb),
        forall|m: int| 0 <= m < 8 ==> #[trigger] uv(r, m) == uv(a, m) + uv(b, m),
{
    let r = _mm256_add_epi32(a, b);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] uv(r, m) == uv(a, m) + uv(b, m) by {
            assert(uv(a, m) <= ba && uv(b, m) <= bb);
            lemma_small_mod((uv(a, m) + uv(b, m)) as nat, 0x1_0000_0000);
        }
    }
    r
}

/// `a - b`, for lanes where `b <= a`.
#[inline(always)]
fn usub(a: __m256i, b: __m256i, Ghost(ba): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        ub(a, ba),
        forall|m: int| 0 <= m < 8 ==> #[trigger] uv(b, m) <= uv(a, m),
    ensures
        ub(r, ba),
        forall|m: int| 0 <= m < 8 ==> #[trigger] uv(r, m) == uv(a, m) - uv(b, m),
{
    let r = _mm256_sub_epi32(a, b);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] uv(r, m) == uv(a, m) - uv(b, m) by {
            assert(uv(b, m) <= uv(a, m) <= ba);
            lemma_mod_multiples_vanish(1, uv(a, m) - uv(b, m), 0x1_0000_0000);
            lemma_small_mod((uv(a, m) - uv(b, m)) as nat, 0x1_0000_0000);
        }
    }
    r
}

/// Times the constant `c`.
#[inline(always)]
fn umul(a: __m256i, c: u32, Ghost(ba): Ghost<int>, Ghost(bc): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        ub(a, ba),
        0 <= ba,
        c < 0x8000_0000,
        bc == c * ba,
        bc < 0x1_0000_0000,
    ensures
        ub(r, bc),
        forall|m: int| 0 <= m < 8 ==> #[trigger] uv(r, m) == uv(a, m) * c,
{
    let k = _mm256_set1_epi32(c as i32);
    let r = _mm256_mullo_epi32(a, k);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] uv(r, m) == uv(a, m) * c && uv(r, m) <= bc by {
            let x = uv(a, m);
            assert(0 <= x <= ba);
            assert(u32x8(k)[m] == c);
            assert(0 <= x * c <= bc) by (nonlinear_arith)
                requires
                    0 <= x <= ba,
                    bc == c * ba,
                    0 <= c,
            ;
            lemma_small_mod((x * c) as nat, 0x1_0000_0000);
        }
    }
    r
}

/// The constant `c` in every lane.
#[inline(always)]
fn uconst(c: u32) -> (r: __m256i)
    requires
        avx2(),
        c < 0x8000_0000,
    ensures
        ub(r, c as int),
        forall|m: int| 0 <= m < 8 ==> #[trigger] uv(r, m) == c,
{
    _mm256_set1_epi32(c as i32)
}

/// Byte `k` of each pixel: shifted to the top, then down.
#[inline(always)]
fn byte_of<const UP: i32>(v: __m256i) -> (r: __m256i)
    requires
        avx2(),
        UP == 24 || UP == 16 || UP == 8,
    ensures
        ub(r, 255),
        forall|m: int| 0 <= m < 8 ==> #[trigger] uv(r, m) == (uv(v, m) / vstd::arithmetic::power2::pow2((24 - UP) as nat) as int) % 256,
{
    let a = _mm256_slli_epi32::<UP>(v);
    let r = _mm256_srli_epi32::<24>(a);
    proof {
        reveal_with_fuel(pow2_spec, 25);
        vstd::arithmetic::power2::lemma2_to64();
        assert forall|m: int| 0 <= m < 8 implies #[trigger] uv(r, m) == (uv(v, m) / vstd::arithmetic::power2::pow2(
            (24 - UP) as nat,
        ) as int) % 256 && uv(r, m) <= 255 by {
            let x = uv(v, m);
            let d = vstd::arithmetic::power2::pow2((24 - UP) as nat) as int;
            let s = pow2_spec(UP as nat) as int;
            if UP == 24 {
                assert(s == 0x100_0000 && d == 1);
            } else if UP == 16 {
                assert(s == 0x1_0000 && d == 256);
            } else {
                assert(s == 256 && d == 0x1_0000);
            }
            assert(s * d == 0x100_0000);
            assert(uv(a, m) == (x * s) % 0x1_0000_0000);
            assert(uv(r, m) == uv(a, m) / 0x100_0000);
            // x = q * d * 256 + t * d + e with t the byte and e < d.
            let q = x / (d * 256);
            let y = x % (d * 256);
            lemma_fundamental_div_mod(x, d * 256);
            lemma_mod_bound(x, d * 256);
            let t = y / d;
            let e = y % d;
            lemma_fundamental_div_mod(y, d);
            lemma_mod_bound(y, d);
            assert(x * s == q * 0x1_0000_0000 + (t * 0x100_0000 + e * s)) by (nonlinear_arith)
                requires
                    x == d * 256 * q + y,
                    y == d * t + e,
                    s * d == 0x100_0000,
            ;
            assert(0 <= t < 256) by (nonlinear_arith)
                requires
                    0 <= y < d * 256,
                    t == y / d,
                    d > 0,
            ;
            assert(0 <= e * s < s * d) by (nonlinear_arith)
                requires
                    0 <= e < d,
                    s > 0,
            ;
            lemma_mod_multiples_vanish(q, t * 0x100_0000 + e * s, 0x1_0000_0000);
            assert(q * 0x1_0000_0000 + (t * 0x100_0000 + e * s) == 0x1_0000_0000 * q + (t * 0x100_0000 + e * s));
            lemma_small_mod((t * 0x100_0000 + e * s) as nat, 0x1_0000_0000);
            lemma_fundamental_div_mod_converse(t * 0x100_0000 + e * s, 0x100_0000, t, e * s);
            // x / d % 256 == t.
            assert(x / d == q * 256 + t) by {
                lemma_fundamental_div_mod_converse(x, d, q * 256 + t, e);
                assert(x == d * (q * 256 + t) + e) by (nonlinear_arith)
                    requires
                        x == d * 256 * q + y,
                        y == d * t + e,
                ;
            }
            lemma_fundamental_div_mod_converse(q * 256 + t, 256, q, t);
        }
    }
    r
}

/// Y, Cb and Cr of the eight pixels whose bytes `v` holds (`pix_ok`).
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn ycc_v(v: __m256i, Ghost(px): Ghost<Seq<u8>>, Ghost(i): Ghost<int>, Ghost(st): Ghost<int>) -> (r: (__m256i, __m256i, __m256i))
    requires
        avx2(),
        pix_ok(v, px, i, st),
    ensures
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.0, p) == ycc(px[i + st * p] as int, px[i + st * p + 1] as int, px[i + st * p + 2] as int, 0),
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.1, p) == ycc(px[i + st * p] as int, px[i + st * p + 1] as int, px[i + st * p + 2] as int, 1),
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.2, p) == ycc(px[i + st * p] as int, px[i + st * p + 1] as int, px[i + st * p + 2] as int, 2),
        ub(r.0, 255) && ub(r.1, 255) && ub(r.2, 255),
{
    let r = byte_of::<24>(v);
    let g = byte_of::<16>(v);
    let b = byte_of::<8>(v);
    let bc = Ghost(255int);
    // Y.
    let y1 = umul(r, 19595, bc, Ghost(19595int * 255));
    let y2 = umul(g, 38470, bc, Ghost(38470int * 255));
    let y3 = umul(b, 7471, bc, Ghost(7471int * 255));
    let y12 = uadd(y1, y2, Ghost(19595int * 255), Ghost(38470int * 255));
    let y123 = uadd(y12, y3, Ghost(58065int * 255), Ghost(7471int * 255));
    let ny = uadd(y123, uconst(32768), Ghost(65536int * 255), Ghost(32768int));
    let yv = _mm256_srli_epi32::<16>(ny);
    // Cb.
    let b1 = umul(b, 32768, bc, Ghost(32768int * 255));
    let b2 = uadd(b1, uconst(8421375), Ghost(32768int * 255), Ghost(8421375int));
    let b3 = umul(r, 11059, bc, Ghost(11059int * 255));
    let b4 = umul(g, 21709, bc, Ghost(21709int * 255));
    let b5 = uadd(b3, b4, Ghost(11059int * 255), Ghost(21709int * 255));
    let nb = usub(b2, b5, Ghost(32768int * 255 + 8421375));
    let cbv = _mm256_srli_epi32::<16>(nb);
    // Cr.
    let r1 = umul(r, 32768, bc, Ghost(32768int * 255));
    let r2 = uadd(r1, uconst(8421375), Ghost(32768int * 255), Ghost(8421375int));
    let r3 = umul(g, 27439, bc, Ghost(27439int * 255));
    let r4 = umul(b, 5329, bc, Ghost(5329int * 255));
    let r5 = uadd(r3, r4, Ghost(27439int * 255), Ghost(5329int * 255));
    let nr = usub(r2, r5, Ghost(32768int * 255 + 8421375));
    let crv = _mm256_srli_epi32::<16>(nr);
    proof {
        reveal_with_fuel(pow2_spec, 17);
        vstd::arithmetic::power2::lemma2_to64();
        assert forall|p: int| #![trigger uv(yv, p)] #![trigger uv(cbv, p)] #![trigger uv(crv, p)] 0 <= p < 8 implies {
            &&& uv(yv, p) == ycc(px[i + st * p] as int, px[i + st * p + 1] as int, px[i + st * p + 2] as int, 0)
            &&& uv(cbv, p) == ycc(px[i + st * p] as int, px[i + st * p + 1] as int, px[i + st * p + 2] as int, 1)
            &&& uv(crv, p) == ycc(px[i + st * p] as int, px[i + st * p + 1] as int, px[i + st * p + 2] as int, 2)
            &&& uv(yv, p) <= 255 && uv(cbv, p) <= 255 && uv(crv, p) <= 255
        } by {
            lemma_pixel_bytes(px, i, st, v, p);
            let (rr, gg, bb) = (uv(r, p), uv(g, p), uv(b, p));
            assert(rr == px[i + st * p] as int && gg == px[i + st * p + 1] as int && bb == px[i + st * p + 2] as int);
            assert(uv(ny, p) == 19595 * rr + 38470 * gg + 7471 * bb + 32768);
            assert(uv(nb, p) == 32768 * bb + 8421375 - (11059 * rr + 21709 * gg));
            assert(uv(nr, p) == 32768 * rr + 8421375 - (27439 * gg + 5329 * bb));
            lemma_div_is_ordered(uv(ny, p), 16777215, 65536);
            lemma_div_is_ordered(uv(nb, p), 16777215, 65536);
            lemma_div_is_ordered(uv(nr, p), 16777215, 65536);
        }
    }
    (yv, cbv, crv)
}

/// Bytes 0 to 2 of lane `p` of `v` are pixel `p`'s R, G and B, pixel `p`
/// at `s[i + st * p..]`.
pub open spec fn pix_ok(v: __m256i, s: Seq<u8>, i: int, st: int) -> bool {
    forall|p: int|
        0 <= p < 8 ==> #[trigger] pix3(v, p) == (s[i + st * p], s[i + st * p + 1], s[i + st * p + 2])
}

pub open spec fn pix3(v: __m256i, p: int) -> (u8, u8, u8) {
    (b256(v)[4 * p], b256(v)[4 * p + 1], b256(v)[4 * p + 2])
}

/// Lane `p`'s low three bytes.
proof fn lemma_pixel_bytes(s: Seq<u8>, i: int, st: int, v: __m256i, p: int)
    requires
        pix_ok(v, s, i, st),
        0 <= p < 8,
    ensures
        uv(v, p) % 256 == s[i + st * p] as int,
        (uv(v, p) / 256) % 256 == s[i + st * p + 1] as int,
        (uv(v, p) / 65536) % 256 == s[i + st * p + 2] as int,
        vstd::arithmetic::power2::pow2(0) == 1,
        vstd::arithmetic::power2::pow2(8) == 256,
        vstd::arithmetic::power2::pow2(16) == 65536,
{
    vstd::arithmetic::power2::lemma2_to64();
    let b = b256(v);
    let (b0, b1, b2, b3) = (b[4 * p], b[4 * p + 1], b[4 * p + 2], b[4 * p + 3]);
    assert(u32x8(v)[p] == le32(b0, b1, b2, b3));
    let x = le32(b0, b1, b2, b3);
    assert(x % 256 == b0 as u32 && (x / 256) % 256 == b1 as u32 && (x / 65536) % 256 == b2 as u32) by (bit_vector)
        requires
            x == (b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32),
    ;
    assert(pix3(v, p) == (s[i + st * p], s[i + st * p + 1], s[i + st * p + 2]));
}

/// Y, Cb and Cr of the eight 4-byte pixels at `px[i..i + 32]`.
#[inline(always)]
pub fn ycc8(px: &[u8], i: usize) -> (r: (__m256i, __m256i, __m256i))
    requires
        avx2(),
        i + 32 <= px@.len(),
    ensures
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.0, p) == ycc(px@[i + 4 * p] as int, px@[i + 4 * p + 1] as int, px@[i + 4 * p + 2] as int, 0),
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.1, p) == ycc(px@[i + 4 * p] as int, px@[i + 4 * p + 1] as int, px@[i + 4 * p + 2] as int, 1),
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.2, p) == ycc(px@[i + 4 * p] as int, px@[i + 4 * p + 1] as int, px@[i + 4 * p + 2] as int, 2),
        ub(r.0, 255) && ub(r.1, 255) && ub(r.2, 255),
{
    let v = load256_u8(px, i);
    proof {
        assert forall|p: int| 0 <= p < 8 implies #[trigger] pix3(v, p) == (px@[i + 4 * p], px@[i + 4 * p + 1], px@[i + 4 * p + 2]) by {
            assert(b256(v) == px@.subrange(i as int, i + 32));
        }
    }
    ycc_v(v, Ghost(px@), Ghost(i as int), Ghost(4))
}

/// Y, Cb and Cr of the eight 3-byte pixels at `px[i..i + 24]`, reading
/// `px[i..i + 28]`: two 16-byte loads, at `i` and `i + 12`, each spread to
/// four 32-bit lanes by a byte shuffle.
#[inline(always)]
#[verifier::spinoff_prover]
pub fn ycc8_rgb(px: &[u8], i: usize) -> (r: (__m256i, __m256i, __m256i))
    requires
        avx2(),
        i + 28 <= px@.len(),
    ensures
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.0, p) == ycc(px@[i + 3 * p] as int, px@[i + 3 * p + 1] as int, px@[i + 3 * p + 2] as int, 0),
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.1, p) == ycc(px@[i + 3 * p] as int, px@[i + 3 * p + 1] as int, px@[i + 3 * p + 2] as int, 1),
        forall|p: int| 0 <= p < 8 ==> #[trigger] uv(r.2, p) == ycc(px@[i + 3 * p] as int, px@[i + 3 * p + 1] as int, px@[i + 3 * p + 2] as int, 2),
        ub(r.0, 255) && ub(r.1, 255) && ub(r.2, 255),
{
    proof {
        assert(px@.len() == px.len());
    }
    let lo = load128_u8(px, i);
    let hi = load128_u8(px, i + 12);
    let v = _mm256_set_m128i(hi, lo);
    let m = _mm256_setr_epi8(
        0, 1, 2, -128, 3, 4, 5, -128, 6, 7, 8, -128, 9, 10, 11, -128,
        0, 1, 2, -128, 3, 4, 5, -128, 6, 7, 8, -128, 9, 10, 11, -128,
    );
    let w = _mm256_shuffle_epi8(v, m);
    proof {
        let bv = b256(v);
        let bm = b256(m);
        let bw = b256(w);
        assert(bv == px@.subrange(i as int, i + 16) + px@.subrange(i + 12, i + 28));
        assert(bw == shuffle8_lanes(bv, bm));
        assert forall|p: int| 0 <= p < 8 implies #[trigger] pix3(w, p) == (px@[i + 3 * p], px@[i + 3 * p + 1], px@[i + 3 * p + 2]) by {
            let h = p / 4;
            let q = p % 4;
            assert(bm[4 * p] == 3 * q && bm[4 * p + 1] == 3 * q + 1 && bm[4 * p + 2] == 3 * q + 2);
            assert((4 * p) / 16 == h && (4 * p + 1) / 16 == h && (4 * p + 2) / 16 == h);
            assert(bw[4 * p] == bv[16 * h + 3 * q]);
            assert(bw[4 * p + 1] == bv[16 * h + 3 * q + 1]);
            assert(bw[4 * p + 2] == bv[16 * h + 3 * q + 2]);
            if h == 0 {
                assert(bv[3 * q] == px@[i + 3 * q]);
                assert(bv[3 * q + 1] == px@[i + 3 * q + 1]);
                assert(bv[3 * q + 2] == px@[i + 3 * q + 2]);
            } else {
                assert(bv[16 + 3 * q] == px@[i + 12 + 3 * q]);
                assert(bv[16 + 3 * q + 1] == px@[i + 12 + 3 * q + 1]);
                assert(bv[16 + 3 * q + 2] == px@[i + 12 + 3 * q + 2]);
            }
        }
    }
    ycc_v(w, Ghost(px@), Ghost(i as int), Ghost(3))
}

/// Appends eight lanes of at most 255 to `row` as bytes.
#[inline(always)]
pub fn push8(row: &mut Vec<u8>, v: __m256i)
    requires
        avx2(),
        ub(v, 255),
    ensures
        final(row)@.len() == old(row)@.len() + 8,
        forall|p: int| 0 <= p < 8 ==> #[trigger] final(row)@[old(row)@.len() + p] as int == uv(v, p),
        forall|j: int| 0 <= j < old(row)@.len() ==> #[trigger] final(row)@[j] == old(row)@[j],
{
    let mut b = [0u32; 8];
    store256_u32(&mut b, 0, v);
    proof {
        assert(b@ =~= u32x8(v));
        assert(uv(v, 0) <= 255 && uv(v, 1) <= 255 && uv(v, 2) <= 255 && uv(v, 3) <= 255);
        assert(uv(v, 4) <= 255 && uv(v, 5) <= 255 && uv(v, 6) <= 255 && uv(v, 7) <= 255);
        assert(b[0] <= 255 && b[1] <= 255 && b[2] <= 255 && b[3] <= 255);
        assert(b[4] <= 255 && b[5] <= 255 && b[6] <= 255 && b[7] <= 255);
    }
    let a: [u8; 8] = [b[0] as u8, b[1] as u8, b[2] as u8, b[3] as u8, b[4] as u8, b[5] as u8, b[6] as u8, b[7] as u8];
    verilith_core::prims::extend(row, a.as_slice());
    proof {
        assert forall|p: int| 0 <= p < 8 implies #[trigger] row@[old(row)@.len() + p] as int == uv(v, p) by {
            assert(row@[old(row)@.len() + p] == a@[p]);
            assert(uv(v, p) <= 255);
        }
    }
}

/// Appends Y, Cb and Cr of the `8 * n` pixels of `st` (3 or 4) bytes
/// from `px[i..]` to `r0`, `r1` and `r2`; reads 4 bytes past them.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
pub fn ycc_run(px: &[u8], i: usize, n: usize, st: usize, r0: &mut Vec<u8>, r1: &mut Vec<u8>, r2: &mut Vec<u8>)
    requires
        avx2(),
        st == 3 || st == 4,
        i + st * (8 * n) + 4 <= px@.len(),
    ensures
        final(r0)@.len() == old(r0)@.len() + 8 * n,
        final(r1)@.len() == old(r1)@.len() + 8 * n,
        final(r2)@.len() == old(r2)@.len() + 8 * n,
        forall|j: int| 0 <= j < old(r0)@.len() ==> #[trigger] final(r0)@[j] == old(r0)@[j],
        forall|j: int| 0 <= j < old(r1)@.len() ==> #[trigger] final(r1)@[j] == old(r1)@[j],
        forall|j: int| 0 <= j < old(r2)@.len() ==> #[trigger] final(r2)@[j] == old(r2)@[j],
        forall|q: int| 0 <= q < 8 * n ==> #[trigger] final(r0)@[old(r0)@.len() + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 0),
        forall|q: int| 0 <= q < 8 * n ==> #[trigger] final(r1)@[old(r1)@.len() + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 1),
        forall|q: int| 0 <= q < 8 * n ==> #[trigger] final(r2)@[old(r2)@.len() + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 2),
{
    let ghost n0 = r0@.len();
    let ghost n1 = r1@.len();
    let ghost n2 = r2@.len();
    let mut k: usize = 0;
    while k < n
        invariant
            avx2(),
            st == 3 || st == 4,
            i + st * (8 * n) + 4 <= px@.len(),
            k <= n,
            n0 == old(r0)@.len() && n1 == old(r1)@.len() && n2 == old(r2)@.len(),
            r0@.len() == n0 + 8 * k && r1@.len() == n1 + 8 * k && r2@.len() == n2 + 8 * k,
            forall|j: int| 0 <= j < n0 ==> #[trigger] r0@[j] == old(r0)@[j],
            forall|j: int| 0 <= j < n1 ==> #[trigger] r1@[j] == old(r1)@[j],
            forall|j: int| 0 <= j < n2 ==> #[trigger] r2@[j] == old(r2)@[j],
            forall|q: int| 0 <= q < 8 * k ==> #[trigger] r0@[n0 + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 0),
            forall|q: int| 0 <= q < 8 * k ==> #[trigger] r1@[n1 + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 1),
            forall|q: int| 0 <= q < 8 * k ==> #[trigger] r2@[n2 + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 2),
        decreases n - k,
    {
        proof {
            assert(st * (8 * k) + st * 8 <= st * (8 * n)) by (nonlinear_arith)
                requires
                    k < n,
                    st >= 0,
            ;
            assert(8 * k <= 8 * n);
            assert(px@.len() == px.len());
            assert(st * (8 * k) <= st * (8 * n)) by (nonlinear_arith)
                requires
                    k < n,
                    st >= 0,
            ;
        }
        let at = i + st * (8 * k);
        let (yv, cb, cr) = if st == 4 {
            ycc8(px, at)
        } else {
            ycc8_rgb(px, at)
        };
        let ghost o0 = r0@;
        let ghost o1 = r1@;
        let ghost o2 = r2@;
        push8(r0, yv);
        push8(r1, cb);
        push8(r2, cr);
        proof {
            assert forall|q: int| #![trigger r0@[n0 + q]] #![trigger r1@[n1 + q]] #![trigger r2@[n2 + q]] 0 <= q < 8 * (k + 1) implies {
                &&& r0@[n0 + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 0)
                &&& r1@[n1 + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 1)
                &&& r2@[n2 + q] as int == ycc(px@[i + st * q] as int, px@[i + st * q + 1] as int, px@[i + st * q + 2] as int, 2)
            } by {
                if q < 8 * k {
                    assert(r0@[n0 + q] == o0[n0 + q]);
                    assert(r1@[n1 + q] == o1[n1 + q]);
                    assert(r2@[n2 + q] == o2[n2 + q]);
                } else {
                    let p = q - 8 * k;
                    assert(at + st * p == i + st * q) by (nonlinear_arith)
                        requires
                            at == i + st * (8 * k),
                            p == q - 8 * k,
                    ;
                    assert(r0@[o0.len() + p] as int == uv(yv, p));
                    assert(r1@[o1.len() + p] as int == uv(cb, p));
                    assert(r2@[o2.len() + p] as int == uv(cr, p));
                }
            }
        }
        k = k + 1;
    }
}

} // verus!
