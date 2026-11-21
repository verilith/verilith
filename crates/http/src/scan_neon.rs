//! The NEON forms of the scanners' 16-byte class masks, for AArch64, with
//! the same contracts as the SSE2 ones in `crate::scan`. They are built
//! from the trusted NEON specifications in `verilith_simd::neon` and vsimd's
//! verified `movemask16`. Off AArch64 the wrappers run an emulation, so
//! these are verified and tested on x86-64 as well.
#[allow(unused_imports)]
use crate::spec::*;
use verilith_simd::neon::*;
use verilith_simd::neon_mask::*;
#[allow(unused_imports)]
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use verilith_simd::neon::group_neon;

/// `x <= k` as a 0x00/0xFF lane: saturating `x - k` is zero.
#[inline(always)]
fn le_mask(x: uint8x16_t, k: u8) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        is_mask(n8(r)),
        forall|j: int| 0 <= j < 16 ==> #[trigger] n8(r)[j] == if n8(x)[j] <= k { 0xFFu8 } else { 0u8 },
{
    vceqq_u8(vqsubq_u8(x, vdupq_n_u8(k)), vdupq_n_u8(0))
}

#[inline(always)]
fn eq_mask(x: uint8x16_t, k: u8) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        is_mask(n8(r)),
        forall|j: int| 0 <= j < 16 ==> #[trigger] n8(r)[j] == if n8(x)[j] == k { 0xFFu8 } else { 0u8 },
{
    vceqq_u8(x, vdupq_n_u8(k))
}

#[verifier::bit_vector]
proof fn lemma_mask_ops(x: u8, y: u8)
    requires
        x == 0xFF || x == 0,
        y == 0xFF || y == 0,
    ensures
        (x | y == 0xFF || x | y == 0) && ((x | y == 0xFF) == (x == 0xFF || y == 0xFF)),
        (x ^ y == 0xFF || x ^ y == 0) && ((x ^ y == 0xFF) == ((x == 0xFF) != (y == 0xFF))),
{
}

/// Lane `j` is 0xFF iff `b[p + j]` is not a field-value byte, else 0.
#[inline(always)]
pub fn value_badv(b: &[u8], p: usize) -> (v: uint8x16_t)
    requires
        neon(),
        p + 16 <= b@.len(),
    ensures
        is_mask(n8(v)),
        forall|j: int| 0 <= j < 16 ==> (#[trigger] n8(v)[j] == 0xFF) == !is_value_char(b@[p + j]),
{
    let x = vld1q_u8_at(b, p);
    let lo = le_mask(x, 0x1F);
    let tab = eq_mask(x, HTAB);
    let del = eq_mask(x, 0x7F);
    // HTAB is one of the bytes below 0x20, so `lo ^ tab` drops it from `lo`.
    let e = veorq_u8(lo, tab);
    let bad = vorrq_u8(e, del);
    proof {
        assert forall|j: int| 0 <= j < 16 implies (#[trigger] n8(bad)[j] == 0 || n8(bad)[j] == 0xFF) && (n8(bad)[j]
            == 0xFF) == !is_value_char(b@[p + j]) by {
            assert(n8(x)[j] == b@[p + j]);
            lemma_mask_ops(n8(lo)[j], n8(tab)[j]);
            lemma_mask_ops(n8(e)[j], n8(del)[j]);
        }
    }
    bad
}

/// Lane `j` is 0xFF iff `b[p + j]` is not a request-target byte, else 0.
#[inline(always)]
pub fn target_badv(b: &[u8], p: usize) -> (v: uint8x16_t)
    requires
        neon(),
        p + 16 <= b@.len(),
    ensures
        is_mask(n8(v)),
        forall|j: int| 0 <= j < 16 ==> (#[trigger] n8(v)[j] == 0xFF) == !is_target_char(b@[p + j]),
{
    let x = vld1q_u8_at(b, p);
    let lo = le_mask(x, 0x20);
    let del = eq_mask(x, 0x7F);
    let bad = vorrq_u8(lo, del);
    proof {
        assert forall|j: int| 0 <= j < 16 implies (#[trigger] n8(bad)[j] == 0 || n8(bad)[j] == 0xFF) && (n8(bad)[j]
            == 0xFF) == !is_target_char(b@[p + j]) by {
            assert(n8(x)[j] == b@[p + j]);
            lemma_mask_ops(n8(lo)[j], n8(del)[j]);
        }
    }
    bad
}

/// Letters (after case folding), digits and `-` are tchars.
proof fn lemma_alnum_dash(c: u8)
    requires
        ((c | 0x20u8) <= 0x7A && !((c | 0x20u8) <= 0x60)) || (c <= 0x39 && !(c <= 0x2F)) || c == 0x2D,
    ensures
        is_tchar(c),
{
    assert(((c | 0x20u8) <= 0x7A && !((c | 0x20u8) <= 0x60)) ==> ((0x41 <= c && c <= 0x5A) || (0x61 <= c && c
        <= 0x7A))) by (bit_vector);
}

/// Lane `j` is 0 when `b[p + j]` is a letter, a digit or `-`, and 0xFF
/// otherwise; 0xFF lanes are only candidates.
#[inline(always)]
pub fn token_badv(b: &[u8], p: usize) -> (v: uint8x16_t)
    requires
        neon(),
        p + 16 <= b@.len(),
    ensures
        is_mask(n8(v)),
        forall|j: int| 0 <= j < 16 && #[trigger] n8(v)[j] != 0xFF ==> is_tchar(b@[p + j]),
{
    let x = vld1q_u8_at(b, p);
    let y = vorrq_u8(x, vdupq_n_u8(0x20));
    // `a1 ^ a2` is `0x60 < y <= 0x7A`, since `a2` implies `a1`; likewise
    // for the digits.
    let a1 = le_mask(y, 0x7A);
    let a2 = le_mask(y, 0x60);
    let d1 = le_mask(x, 0x39);
    let d2 = le_mask(x, 0x2F);
    let ds = eq_mask(x, 0x2D);
    let al = veorq_u8(a1, a2);
    let dg = veorq_u8(d1, d2);
    let g1 = vorrq_u8(al, dg);
    let good = vorrq_u8(g1, ds);
    let bad = veorq_u8(good, vdupq_n_u8(0xFF));
    proof {
        assert forall|j: int| 0 <= j < 16 implies (#[trigger] n8(bad)[j] == 0 || n8(bad)[j] == 0xFF) && (n8(bad)[j]
            != 0xFF ==> is_tchar(b@[p + j])) by {
            let c = b@[p + j];
            assert(n8(x)[j] == c);
            assert(n8(y)[j] == c | 0x20);
            lemma_mask_ops(n8(a1)[j], n8(a2)[j]);
            lemma_mask_ops(n8(d1)[j], n8(d2)[j]);
            lemma_mask_ops(n8(al)[j], n8(dg)[j]);
            lemma_mask_ops(n8(g1)[j], n8(ds)[j]);
            lemma_mask_ops(n8(good)[j], 0xFF);
            if n8(good)[j] == 0xFF {
                lemma_alnum_dash(c);
            }
        }
    }
    bad
}

/// Bit `j` of the nibble mask shifted right by `4 sh` is set exactly when
/// lane `j / 4 + sh` is 0xFF, for the lanes that are left.
proof fn lemma_nib_shift(n: u64, a: Seq<u8>, sh: u64, j: u64)
    requires
        a.len() == 16,
        sh < 16,
        j < 64,
        forall|k: u64| k < 16 ==> #[trigger] ((n >> (4 * k)) & 15) == if a[k as int] == 0xFF { 15u64 } else { 0u64 },
    ensures
        (((n >> (4 * sh)) >> j) & 1 == 1) == (j + 4 * sh < 64 && a[(j / 4 + sh) as int] == 0xFF),
{
    let s: u64 = (4 * sh) as u64;
    assert(n >> (4 * sh) == n >> s);
    if j + s < 64 {
        let js: u64 = (j + s) as u64;
        assert(s < 64 && j < 64 && js == j + s ==> ((n >> s) >> j) == n >> js) by (bit_vector);
        lemma_nibmask_bit(n, a, js);
        assert(js / 4 == j / 4 + sh) by (nonlinear_arith)
            requires
                js == j + 4 * sh,
        ;
        assert(((n >> js) & 1 == 1) == (a[(js / 4) as int] == 0xFF));
        assert((((n >> s) >> j) & 1 == 1) == (a[(js / 4) as int] == 0xFF));
        assert((((n >> (4 * sh)) >> j) & 1 == 1) == (a[(js / 4) as int] == 0xFF));
    } else {
        assert(j + 4 * sh >= 64);
        assert(s < 64 && j < 64 && j >= 64 - s ==> ((n >> s) >> j) == 0) by (bit_vector);
        let z: u64 = (n >> s) >> j;
        assert(z == 0);
        assert(z & 1 == 0) by (bit_vector)
            requires
                z == 0,
        ;
    }
}

/// The first 0xFF lane of `v` at or after `sh`, counted from `sh`, or
/// `16 - sh` if there is none: two instructions for the mask (`shrn`,
/// `fmov`), then a shift, `rbit`/`clz` and a `min`.
#[inline(always)]
pub fn nib_first(v: uint8x16_t, sh: u32) -> (d: u32)
    requires
        neon(),
        is_mask(n8(v)),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|k: u32| k < d ==> #[trigger] n8(v)[(k + sh) as int] != 0xFF,
        d < 16 - sh ==> n8(v)[(d + sh) as int] == 0xFF,
{
    let n = nibmask16(v);
    let s = n >> (4 * sh as u64);
    let t = s.trailing_zeros();
    let e = t / 4;
    let d = if e > 16 - sh { 16 - sh } else { e };
    proof {
        vstd::std_specs::bits::axiom_u64_trailing_zeros(s);
        let a = n8(v);
        assert forall|k: u32| k < d implies #[trigger] n8(v)[(k + sh) as int] != 0xFF by {
            let j = (4 * k) as u64;
            assert(j < t);
            lemma_nib_shift(n, a, sh as u64, j);
            assert(j / 4 == k as u64);
        }
        if d < 16 - sh {
            assert(t < 64);
            lemma_nib_shift(n, a, sh as u64, t as u64);
            assert(t as u64 / 4 == e as u64);
        }
    }
    d
}

} // verus!
