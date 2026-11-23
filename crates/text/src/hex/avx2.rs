//! AVX2 hex kernels, proven with vsimd's specifications of the intrinsics.
//!
//! Encoding takes 32 bytes to 64 digits per step: the two nibbles of every
//! byte index a 16-entry digit table, and byte interleaves put each pair of
//! digits in order. Decoding takes 32 digits to 16 bytes per step: a
//! nibble-table check (as in the base64 decoder) finds non-digits, a
//! second table maps each digit to its value, and a multiply-add joins the
//! pairs.
use super::codec::*;
use crate::simd::*;
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
use verilith_simd::ops::*;
#[cfg(verus_only)]
use verilith_simd::x86::perm2x128;
#[cfg(verus_only)]
use vstd::compute::RangeAll;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

/// The digit table, once per 128-bit lane.
pub const HEX_LO32: [u8; 32] = [
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102,
];

/// The uppercase digit table, once per 128-bit lane.
pub const HEX_UP32: [u8; 32] = [
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 65, 66, 67, 68, 69, 70,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 65, 66, 67, 68, 69, 70,
];

/// Validation by low and high nibble: a byte is a hex digit iff the two
/// entries share no bit.
pub const HV_LO: [u8; 32] = [
    3, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7, 7, 7, 7, 7, 7,
    3, 1, 1, 1, 1, 1, 1, 3, 3, 3, 7, 7, 7, 7, 7, 7,
];

/// The high-nibble half of the validation table (see `HV_LO`).
pub const HV_HI: [u8; 32] = [
    1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1,
];

/// The offset from a digit to its value, by high nibble.
pub const HV_ROLL: [u8; 32] = [
    0, 0, 0, 208, 201, 0, 169, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 208, 201, 0, 169, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

/// Picks the low byte of each 16-bit lane.
pub const HV_PACK: [u8; 32] = [
    0, 2, 4, 6, 8, 10, 12, 14, 128, 128, 128, 128, 128, 128, 128, 128,
    0, 2, 4, 6, 8, 10, 12, 14, 128, 128, 128, 128, 128, 128, 128, 128,
];

pub open spec fn hex_tab(upper: bool) -> Seq<u8> {
    if upper { HEX_UP32@ } else { HEX_LO32@ }
}

pub open spec fn herr(c: u8) -> u8 {
    HV_LO@[(c & 15) as int] & HV_HI@[(c >> 4) as int]
}

pub open spec fn hval(c: u8) -> u8 {
    ((c + HV_ROLL@[(c >> 4) as int]) % 256) as u8
}

pub open spec fn hex_ok(c: u8) -> bool {
    &&& (herr(c) == 0) == (dval(c) is Some)
    &&& dval(c) is Some ==> hval(c) == dval(c)->0
}

pub proof fn lemma_hex_consts()
    ensures
        forall|c: u8| #[trigger] hex_ok(c),
        forall|v: int| 0 <= v < 16 ==> #[trigger] HEX_LO32@[v] == digit(false, v as u8) && HEX_UP32@[v] == digit(true, v as u8),
        forall|k: int| 0 <= k < 16 ==> #[trigger] HEX_LO32@[k + 16] == HEX_LO32@[k] && HEX_UP32@[k + 16] == HEX_UP32@[k]
            && HV_LO@[k + 16] == HV_LO@[k] && HV_HI@[k + 16] == HV_HI@[k] && HV_ROLL@[k + 16] == HV_ROLL@[k],
        forall|k: int| 0 <= k < 32 ==> #[trigger] HV_PACK@[k] == if k % 16 < 8 { 2 * (k % 16) } else { 128 },
{
    let p0 = |i: int| hex_ok(i as u8);
    assert((0..256int).all_spec(|i: int| hex_ok(i as u8))) by (compute_only);
    vstd::compute::all_spec_ensures(0..256int, p0);
    assert forall|c: u8| #[trigger] hex_ok(c) by {
        assert(p0(c as int));
    }
    let p1 = |v: int| HEX_LO32@[v] == digit(false, v as u8) && HEX_UP32@[v] == digit(true, v as u8);
    assert((0..16int).all_spec(|v: int| HEX_LO32@[v] == digit(false, v as u8) && HEX_UP32@[v] == digit(true, v as u8))) by (compute_only);
    vstd::compute::all_spec_ensures(0..16int, p1);
    let p2 = |k: int| HEX_LO32@[k + 16] == HEX_LO32@[k] && HEX_UP32@[k + 16] == HEX_UP32@[k]
            && HV_LO@[k + 16] == HV_LO@[k] && HV_HI@[k + 16] == HV_HI@[k] && HV_ROLL@[k + 16] == HV_ROLL@[k];
    assert((0..16int).all_spec(|k: int| HEX_LO32@[k + 16] == HEX_LO32@[k] && HEX_UP32@[k + 16] == HEX_UP32@[k]
            && HV_LO@[k + 16] == HV_LO@[k] && HV_HI@[k + 16] == HV_HI@[k] && HV_ROLL@[k + 16] == HV_ROLL@[k])) by (compute_only);
    vstd::compute::all_spec_ensures(0..16int, p2);
    let p3 = |k: int| HV_PACK@[k] == if k % 16 < 8 { 2 * (k % 16) } else { 128 };
    assert((0..32int).all_spec(|k: int| HV_PACK@[k] == if k % 16 < 8 { 2 * (k % 16) } else { 128 })) by (compute_only);
    vstd::compute::all_spec_ensures(0..32int, p3);
    assert forall|v: int| 0 <= v < 16 implies #[trigger] HEX_LO32@[v] == digit(false, v as u8) && HEX_UP32@[v] == digit(true, v as u8) by {
        assert(p1(v));
    }
    assert forall|k: int| 0 <= k < 16 implies #[trigger] HEX_LO32@[k + 16] == HEX_LO32@[k] && HEX_UP32@[k + 16] == HEX_UP32@[k]
            && HV_LO@[k + 16] == HV_LO@[k] && HV_HI@[k + 16] == HV_HI@[k] && HV_ROLL@[k + 16] == HV_ROLL@[k] by {
        assert(p2(k));
    }
    assert forall|k: int| 0 <= k < 32 implies #[trigger] HV_PACK@[k] == if k % 16 < 8 { 2 * (k % 16) } else { 128 } by {
        assert(p3(k));
    }
}

/// The digits of one nibble vector, looked up in `tab`.
proof fn lemma_digits(upper: bool, nb: Seq<u8>, d: Seq<u8>)
    requires
        nb.len() == 32,
        forall|j: int| 0 <= j < 32 ==> #[trigger] nb[j] < 16,
        d == shuffle8_lanes(hex_tab(upper), nb),
    ensures
        d.len() == 32,
        forall|j: int| 0 <= j < 32 ==> #[trigger] d[j] == digit(upper, nb[j]),
{
    lemma_hex_consts();
    assert forall|j: int| 0 <= j < 32 implies #[trigger] d[j] == digit(upper, nb[j]) by {
        let k = nb[j] as int;
        if j >= 16 {
            assert(hex_tab(upper)[k + 16] == hex_tab(upper)[k]);
        }
        assert(d[j] == hex_tab(upper)[k]);
    }
}

/// Output digit `i` of a 32-byte step, as the interleaves and lane
/// permutes produce it.
proof fn lemma_enc_order(xb: Seq<u8>, hd: Seq<u8>, ld: Seq<u8>, ul: Seq<u8>, uh: Seq<u8>, o0: Seq<u8>, o1: Seq<u8>, upper: bool)
    requires
        xb.len() == 32 && hd.len() == 32 && ld.len() == 32,
        forall|j: int| 0 <= j < 32 ==> #[trigger] hd[j] == digit(upper, xb[j] >> 4),
        forall|j: int| 0 <= j < 32 ==> #[trigger] ld[j] == digit(upper, xb[j] & 15),
        ul == unpacklo8_lanes(hd, ld),
        uh == unpackhi8_lanes(hd, ld),
        o0 == perm2x128(ul, uh, 0x20),
        o1 == perm2x128(ul, uh, 0x31),
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] (o0 + o1)[i] == digit(upper, if i % 2 == 0 { xb[i / 2] >> 4 } else { xb[i / 2] & 15 }),
{
    assert forall|i: int| 0 <= i < 64 implies #[trigger] (o0 + o1)[i] == digit(upper, if i % 2 == 0 { xb[i / 2] >> 4 } else { xb[i / 2] & 15 }) by {
        // Byte i of the output is byte i % 32 of o0 or o1; each 16-byte
        // quarter q of the output comes from lane q % 2 of ul (q even) or
        // uh (q odd), and covers input bytes 8q .. 8q + 8.
        let q = i / 16;
        let p = i % 16;
        assert(i == 16 * q + p);
        if q == 0 {
            assert((o0 + o1)[i] == ul[p]);
        } else if q == 1 {
            assert((o0 + o1)[i] == uh[p]);
        } else if q == 2 {
            assert((o0 + o1)[i] == ul[16 + p]);
        } else {
            assert((o0 + o1)[i] == uh[16 + p]);
        }
    }
}

/// The 64 digits of the 32 bytes at `x[i..]`, as two vectors.
#[inline(always)]
fn enc_block(upper: bool, x: &[u8], i: usize, tab: __m256i) -> (r: (__m256i, __m256i))
    requires
        avx2(),
        i + 32 <= x.len(),
        b256(tab) == hex_tab(upper),
    ensures
        forall|k: int| 0 <= k < 64 ==> #[trigger] (b256(r.0) + b256(r.1))[k] == encode(upper, x@)[2 * i + k],
{
    let v = load256_u8(x, i);
    let sh = _mm256_srli_epi32::<4>(v);
    let k0f = _mm256_set1_epi8(0x0f);
    let hn = _mm256_and_si256(sh, k0f);
    let ln = _mm256_and_si256(v, k0f);
    let hd = _mm256_shuffle_epi8(tab, hn);
    let ld = _mm256_shuffle_epi8(tab, ln);
    let ul = _mm256_unpacklo_epi8(hd, ld);
    let uh = _mm256_unpackhi_epi8(hd, ld);
    let o0 = _mm256_permute2x128_si256::<0x20>(ul, uh);
    let o1 = _mm256_permute2x128_si256::<0x31>(ul, uh);
    proof {
        let xb = b256(v);
        assert(xb == x@.subrange(i as int, i + 32));
        assert(u8_of_i8(0x0f) == 0x0f);
        lemma_hi_nibbles(xb, b256(sh), b256(k0f), b256(hn));
        assert forall|j: int| 0 <= j < 32 implies #[trigger] b256(hn)[j] < 16 && b256(ln)[j] < 16 && b256(ln)[j] == xb[j] & 15 by {
            let c = xb[j];
            assert(c >> 4 < 16) by (bit_vector);
            assert(c & 0x0f < 16 && c & 0x0f == c & 15) by (bit_vector);
        }
        assert forall|j: int| 0 <= j < 32 implies #[trigger] b256(ln)[j] < 16 by {
            assert(b256(hn)[j] < 16);
        }
        lemma_digits(upper, b256(hn), b256(hd));
        lemma_digits(upper, b256(ln), b256(ld));
        assert forall|j: int| 0 <= j < 32 implies #[trigger] b256(ld)[j] == digit(upper, xb[j] & 15) by {
            assert(b256(hn)[j] < 16);
        }
        lemma_enc_order(xb, b256(hd), b256(ld), b256(ul), b256(uh), b256(o0), b256(o1), upper);
        assert forall|k: int| 0 <= k < 64 implies #[trigger] (b256(o0) + b256(o1))[k] == encode(upper, x@)[2 * i + k] by {
            assert((2 * i + k) / 2 == i + k / 2 && (2 * i + k) % 2 == k % 2);
        }
    }
    (o0, o1)
}

/// Encodes 32 bytes at a time while they last; returns how many bytes
/// were done (their digits are in `out`).
#[inline(always)]
pub fn encode_bulk_body(upper: bool, x: &[u8], out: &mut [u8]) -> (n: usize)
    requires
        avx2(),
        old(out).len() == 2 * x.len(),
    ensures
        final(out).len() == old(out).len(),
        n <= x.len(),
        forall|k: int| 0 <= k < 2 * n ==> #[trigger] final(out)@[k] == encode(upper, x@)[k],
{
    let tab = if upper { load256_u8(HEX_UP32.as_slice(), 0) } else { load256_u8(HEX_LO32.as_slice(), 0) };
    proof {
        assert(HEX_UP32@.subrange(0, 32) =~= HEX_UP32@);
        assert(HEX_LO32@.subrange(0, 32) =~= HEX_LO32@);
    }
    let len = x.len();
    let mut i: usize = 0;
    while i < len && len - i >= 32
        invariant
            avx2(),
            len == x.len(),
            i <= len,
            out.len() == 2 * len,
            b256(tab) == hex_tab(upper),
            forall|k: int| 0 <= k < 2 * i ==> #[trigger] out@[k] == encode(upper, x@)[k],
        decreases len - i,
    {
        let (o0, o1) = enc_block(upper, x, i, tab);
        let ghost before = out@;
        store256_u8(out, 2 * i, o0);
        let ghost mid = out@;
        store256_u8(out, 2 * i + 32, o1);
        proof {
            assert forall|k: int| 0 <= k < 2 * (i + 32) implies #[trigger] out@[k] == encode(upper, x@)[k] by {
                if k >= 2 * i + 32 {
                    assert(out@[k] == b256(o1)[k - 2 * i - 32]);
                    assert((b256(o0) + b256(o1))[k - 2 * i] == b256(o1)[k - 2 * i - 32]);
                } else if k >= 2 * i {
                    assert(out@[k] == mid[k]);
                    assert(mid[k] == b256(o0)[k - 2 * i]);
                    assert((b256(o0) + b256(o1))[k - 2 * i] == b256(o0)[k - 2 * i]);
                } else {
                    assert(out@[k] == before[k]);
                }
            }
        }
        i = i + 32;
    }
    i
}

/// Trusted: `encode_bulk_body` compiled with `avx2` enabled, through
/// `tf::encode_bulk`; the contract is `encode_bulk_body`'s, which is verified.
#[verifier::external_body]
pub fn encode_bulk(upper: bool, x: &[u8], out: &mut [u8]) -> (n: usize)
    requires
        avx2(),
        old(out).len() == 2 * x.len(),
    ensures
        final(out).len() == old(out).len(),
        n <= x.len(),
        forall|k: int| 0 <= k < 2 * n ==> #[trigger] final(out)@[k] == encode(upper, x@)[k],
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::encode_bulk(upper, x, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return encode_bulk_body(upper, x, out);
}

/// The 16 bytes from the 32 digits at `s[j..]` (in the low half of the
/// result), and the validation vector (all zero iff all are digits).
#[inline(always)]
fn dec_block(s: &[u8], j: usize, lo_t: __m256i, hi_t: __m256i, roll_t: __m256i, pack: __m256i, perm: __m256i) -> (r: (__m256i, __m256i))
    requires
        avx2(),
        j + 32 <= s.len(),
        b256(lo_t) == HV_LO@,
        b256(hi_t) == HV_HI@,
        b256(roll_t) == HV_ROLL@,
        b256(pack) == HV_PACK@,
        u32x8(perm) == seq![0u32, 1, 4, 5, 2, 3, 6, 7],
    ensures
        forall|k: int| 0 <= k < 32 ==> (#[trigger] b256(r.1)[k] == 0) == (dval(s@[j + k]) is Some),
        (forall|k: int| 0 <= k < 32 ==> dval(#[trigger] s@[j + k]) is Some) ==> forall|t: int| 0 <= t < 16 ==> #[trigger] b256(r.0)[t] == ((dv(s@, j + 2 * t) << 4) | dv(s@, j + 2 * t + 1)) as u8,
{
    let v = load256_u8(s, j);
    let sh = _mm256_srli_epi32::<4>(v);
    let k0f = _mm256_set1_epi8(0x0f);
    let hn = _mm256_and_si256(sh, k0f);
    let ln = _mm256_and_si256(v, k0f);
    let l = _mm256_shuffle_epi8(lo_t, ln);
    let h = _mm256_shuffle_epi8(hi_t, hn);
    let e = _mm256_and_si256(l, h);
    let roll = _mm256_shuffle_epi8(roll_t, hn);
    let vals = _mm256_add_epi8(v, roll);
    let k1 = _mm256_set1_epi16(0x0110);
    let m = _mm256_maddubs_epi16(vals, k1);
    let p = _mm256_shuffle_epi8(m, pack);
    let o = _mm256_permutevar8x32_epi32(p, perm);
    proof {
        assert(u8_of_i8(0x0f) == 0x0f);
        assert(u16_of_i16(0x0110) == 0x0110);
        lemma_hex_dec_block(s@, j as int, b256(v), b256(sh), b256(k0f), b256(hn), b256(ln), b256(l), b256(h), b256(e), b256(roll),
            b256(vals), b256(k1), b256(m), b256(p), u32x8(perm), b256(o));
    }
    (o, e)
}

proof fn lemma_hex_dec_block(
    ss: Seq<u8>,
    j: int,
    ib: Seq<u8>,
    sh: Seq<u8>,
    k0f: Seq<u8>,
    hn: Seq<u8>,
    ln: Seq<u8>,
    l: Seq<u8>,
    h: Seq<u8>,
    e: Seq<u8>,
    roll: Seq<u8>,
    vb: Seq<u8>,
    k1: Seq<u8>,
    mb: Seq<u8>,
    pb: Seq<u8>,
    perm: Seq<u32>,
    ob: Seq<u8>,
)
    requires
        0 <= j,
        j + 32 <= ss.len(),
        ib == ss.subrange(j, j + 32),
        sh.len() == 32 && k1.len() == 32 && mb.len() == 32 && ob.len() == 32,
        u32s(sh) == srli32(u32s(ib), 4),
        k0f == splat8(0x0f, 32),
        hn == and8(sh, k0f),
        ln == and8(ib, k0f),
        l == shuffle8_lanes(HV_LO@, ln),
        h == shuffle8_lanes(HV_HI@, hn),
        e == and8(l, h),
        roll == shuffle8_lanes(HV_ROLL@, hn),
        vb == add8(ib, roll),
        u16s(k1) == splat16(0x0110, 16),
        u16s(mb) == maddubs(vb, k1),
        pb == shuffle8_lanes(mb, HV_PACK@),
        perm == seq![0u32, 1, 4, 5, 2, 3, 6, 7],
        u32s(ob) == permvar32(u32s(pb), perm),
    ensures
        forall|k: int| 0 <= k < 32 ==> (#[trigger] e[k] == 0) == (dval(ss[j + k]) is Some),
        (forall|k: int| 0 <= k < 32 ==> dval(#[trigger] ss[j + k]) is Some) ==> forall|t: int| 0 <= t < 16 ==> #[trigger] ob[t] == ((dv(ss, j + 2 * t) << 4) | dv(ss, j + 2 * t + 1)) as u8,
{
    lemma_hex_consts();
    lemma_hi_nibbles(ib, sh, k0f, hn);
    assert forall|k: int| #![trigger e[k]] #![trigger vb[k]] 0 <= k < 32 implies e[k] == herr(ib[k]) && vb[k] == hval(ib[k]) by {
        let c = ib[k];
        assert(c & 0x0f < 16 && c & 0x0f == c & 15) by (bit_vector);
        assert(c >> 4 < 16) by (bit_vector);
        let lo = (c & 15) as int;
        let hi = (c >> 4) as int;
        if k >= 16 {
            assert(HV_LO@[lo + 16] == HV_LO@[lo]);
            assert(HV_HI@[hi + 16] == HV_HI@[hi]);
            assert(HV_ROLL@[hi + 16] == HV_ROLL@[hi]);
        }
        assert(l[k] == HV_LO@[lo]);
        assert(h[k] == HV_HI@[hi]);
        assert(roll[k] == HV_ROLL@[hi]);
    }
    assert forall|k: int| 0 <= k < 32 implies (#[trigger] e[k] == 0) == (dval(ss[j + k]) is Some) by {
        assert(ib[k] == ss[j + k]);
        assert(hex_ok(ib[k]));
        assert(e[k] == herr(ib[k]));
    }
    if forall|k: int| 0 <= k < 32 ==> dval(#[trigger] ss[j + k]) is Some {
        assert forall|t: int| 0 <= t < 16 implies #[trigger] ob[t] == ((dv(ss, j + 2 * t) << 4) | dv(ss, j + 2 * t + 1)) as u8 by {
            lemma_hex_pack_byte(ss, j, ib, vb, k1, mb, pb, perm, ob, t);
        }
    }
}

proof fn lemma_hex_pack_byte(ss: Seq<u8>, j: int, ib: Seq<u8>, vb: Seq<u8>, k1: Seq<u8>, mb: Seq<u8>, pb: Seq<u8>, perm: Seq<u32>, ob: Seq<u8>, t: int)
    requires
        0 <= t < 16,
        0 <= j,
        j + 32 <= ss.len(),
        ib == ss.subrange(j, j + 32),
        vb.len() == 32 && k1.len() == 32 && mb.len() == 32 && pb.len() == 32 && ob.len() == 32,
        forall|k: int| 0 <= k < 32 ==> dval(#[trigger] ss[j + k]) is Some,
        forall|k: int| 0 <= k < 32 ==> #[trigger] vb[k] == hval(ib[k]),
        u16s(k1) == splat16(0x0110, 16),
        u16s(mb) == maddubs(vb, k1),
        pb == shuffle8_lanes(mb, HV_PACK@),
        perm == seq![0u32, 1, 4, 5, 2, 3, 6, 7],
        u32s(ob) == permvar32(u32s(pb), perm),
    ensures
        ob[t] == ((dv(ss, j + 2 * t) << 4) | dv(ss, j + 2 * t + 1)) as u8,
{
    lemma_hex_consts();
    let a = j + 2 * t;
    assert(hex_ok(ib[2 * t]) && hex_ok(ib[2 * t + 1]));
    assert(ib[2 * t] == ss[a] && ib[2 * t + 1] == ss[a + 1]);
    assert(dval(ss[j + 2 * t]) is Some && dval(ss[j + (2 * t + 1)]) is Some);
    let p = dv(ss, a);
    let q = dv(ss, a + 1);
    assert(vb[2 * t] == p && vb[2 * t + 1] == q);
    assert(p < 16 && q < 16);
    // maddubs with (16, 1): lane t = 16 p + q.
    lemma_u16s_bytes(k1);
    assert(byte16(0x0110u16, 0) == 0x10 && byte16(0x0110u16, 1) == 1) by (compute_only);
    assert(k1[2 * t] == byte16(u16s(k1)[t], 0));
    assert(k1[2 * t + 1] == byte16(u16s(k1)[t], 1));
    assert(s8(0x10) == 16 && s8(1) == 1);
    assert(p * 16 <= 15 * 16) by (nonlinear_arith)
        requires
            p < 16,
    ;
    let mt = u16s(mb)[t];
    assert(mt as int == p as int * 16 + q as int);
    assert(p < 16 && q < 16 ==> ((p << 4) | q) as int == p as int * 16 + q as int) by (bit_vector);
    // Through the byte shuffle and lane permutation: output byte t is the
    // low byte of 16-bit lane t.
    let src = if t < 8 { t / 4 } else { t / 4 + 2 };
    assert(perm[t / 4] as int == src);
    lemma_byte_of_lane(ob, t);
    let pt = 4 * src + t % 4;
    lemma_byte_of_lane(pb, pt);
    assert(pt / 4 == src && pt % 4 == t % 4);
    assert(u32s(ob)[t / 4] == u32s(pb)[src]);
    assert(ob[t] == pb[pt]);
    assert(pt % 16 < 8);
    assert(HV_PACK@[pt] == 2 * (pt % 16));
    let ms = (pt / 16) * 16 + 2 * (pt % 16);
    assert(ms == 2 * t);
    assert(pb[pt] == mb[2 * t]);
    lemma_u16s_bytes(mb);
    assert(mb[2 * t] == byte16(mt, 0));
    lemma_byte16_lo(mt);
}

/// Decodes 32 digits at a time while they last. Returns how many bytes
/// were done and whether all digits read so far were valid (if so, their
/// bytes are in `out`).
#[inline(always)]
pub fn decode_bulk_body(s: &[u8], out: &mut [u8]) -> (r: (usize, bool))
    requires
        avx2(),
        s.len() % 2 == 0,
        old(out).len() == s.len() / 2,
    ensures
        final(out).len() == old(out).len(),
        r.0 <= s.len() / 2,
        r.1 <==> forall|k: int| 0 <= k < 2 * r.0 ==> (#[trigger] dval(s@[k])) is Some,
        r.1 ==> forall|k: int| 0 <= k < r.0 ==> #[trigger] final(out)@[k] == ((dv(s@, 2 * k) << 4) | dv(s@, 2 * k + 1)) as u8,
{
    let lo_t = load256_u8(HV_LO.as_slice(), 0);
    let hi_t = load256_u8(HV_HI.as_slice(), 0);
    let roll_t = load256_u8(HV_ROLL.as_slice(), 0);
    let pack = load256_u8(HV_PACK.as_slice(), 0);
    let perm = _mm256_setr_epi32(0, 1, 4, 5, 2, 3, 6, 7);
    let zero = _mm256_setzero_si256();
    proof {
        assert(HV_LO@.subrange(0, 32) =~= HV_LO@);
        assert(HV_HI@.subrange(0, 32) =~= HV_HI@);
        assert(HV_ROLL@.subrange(0, 32) =~= HV_ROLL@);
        assert(HV_PACK@.subrange(0, 32) =~= HV_PACK@);
        assert(u32x8(perm) =~= seq![0u32, 1, 4, 5, 2, 3, 6, 7]);
    }
    let n = s.len();
    let mut err = zero;
    let mut j: usize = 0;
    while j < n && n - j >= 32
        invariant
            avx2(),
            n == s.len(),
            n % 2 == 0,
            j <= n,
            j % 2 == 0,
            out.len() == n / 2,
            b256(lo_t) == HV_LO@,
            b256(hi_t) == HV_HI@,
            b256(roll_t) == HV_ROLL@,
            b256(pack) == HV_PACK@,
            u32x8(perm) == seq![0u32, 1, 4, 5, 2, 3, 6, 7],
            b256(zero) == splat8(0u8, 32),
            (forall|k: int| 0 <= k < 32 ==> #[trigger] b256(err)[k] == 0) <==> forall|k: int| 0 <= k < j ==> (#[trigger] dval(s@[k])) is Some,
            (forall|k: int| 0 <= k < 32 ==> #[trigger] b256(err)[k] == 0) ==> forall|k: int| 0 <= k < j / 2 ==> #[trigger] out@[k] == ((dv(s@, 2 * k) << 4) | dv(s@, 2 * k + 1)) as u8,
        decreases n - j,
    {
        let (o, e) = dec_block(s, j, lo_t, hi_t, roll_t, pack, perm);
        let ghost err0 = err;
        err = _mm256_or_si256(err, e);
        let lo = _mm256_castsi256_si128(o);
        let ghost before = out@;
        store128_u8(out, j / 2, lo);
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
            let valid_new = forall|k: int| 0 <= k < 32 ==> dval(#[trigger] s@[j + k]) is Some;
            assert(alle == valid_new) by {
                if alle {
                    assert forall|k: int| 0 <= k < 32 implies dval(#[trigger] s@[j + k]) is Some by {
                        assert(b256(e)[k] == 0);
                    }
                }
                if valid_new {
                    assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(e)[k] == 0 by {
                        assert(dval(s@[j + k]) is Some);
                    }
                }
            }
            assert(allz == forall|k: int| 0 <= k < j + 32 ==> (#[trigger] dval(s@[k])) is Some) by {
                if allz {
                    assert forall|k: int| 0 <= k < j + 32 implies (#[trigger] dval(s@[k])) is Some by {
                        if k >= j {
                            assert(dval(s@[j + (k - j)]) is Some);
                        }
                    }
                }
                if forall|k: int| 0 <= k < j + 32 ==> (#[trigger] dval(s@[k])) is Some {
                    assert forall|k: int| 0 <= k < 32 implies dval(#[trigger] s@[j + k]) is Some by {
                        assert(dval(s@[j + k]) is Some);
                    }
                }
            }
            if allz {
                assert forall|k: int| 0 <= k < (j + 32) / 2 implies #[trigger] out@[k] == ((dv(s@, 2 * k) << 4) | dv(s@, 2 * k + 1)) as u8 by {
                    if k >= j / 2 {
                        let t = k - j / 2;
                        assert(out@[k] == b128(lo)[t]);
                        assert(b128(lo)[t] == b256(o)[t]);
                        assert(j + 2 * t == 2 * k);
                    } else {
                        assert(out@[k] == before[k]);
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
    (j / 2, mm == -1)
}

/// Trusted: `decode_bulk_body` compiled with `avx2` enabled, through
/// `tf::decode_bulk`; the contract is `decode_bulk_body`'s, which is verified.
#[verifier::external_body]
pub fn decode_bulk(s: &[u8], out: &mut [u8]) -> (r: (usize, bool))
    requires
        avx2(),
        s.len() % 2 == 0,
        old(out).len() == s.len() / 2,
    ensures
        final(out).len() == old(out).len(),
        r.0 <= s.len() / 2,
        r.1 <==> forall|k: int| 0 <= k < 2 * r.0 ==> (#[trigger] dval(s@[k])) is Some,
        r.1 ==> forall|k: int| 0 <= k < r.0 ==> #[trigger] final(out)@[k] == ((dv(s@, 2 * k) << 4) | dv(s@, 2 * k + 1)) as u8,
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::decode_bulk(s, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return decode_bulk_body(s, out);
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
    pub(super) unsafe fn encode_bulk(upper: bool, x: &[u8], out: &mut [u8]) -> usize {
        encode_bulk_body(upper, x, out)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn decode_bulk(s: &[u8], out: &mut [u8]) -> (usize, bool) {
        decode_bulk_body(s, out)
    }
}
