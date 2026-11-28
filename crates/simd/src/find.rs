//! Finding the next occurrence of one byte, 16 bytes at a time: SSE2 on
//! x86-64, NEON on AArch64 (and wasm32's SIMD through the same generic
//! scanner), proven against the plain definition, `first_at`. Nothing
//! here is trusted: it is built on this crate's verified `sse2` and
//! `neon` wrappers.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
#[allow(unused_imports)]
use crate::sse2::{eq16, load16, movemask16, splat16};
#[cfg(all(verus_only, any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
use crate::sse2::{b16, bit};
use vstd::prelude::*;

verus! {

/// `q` is where the first `c` at or after `p` is, or the end of `s`.
pub open spec fn first_at(s: Seq<u8>, p: int, c: u8, q: int) -> bool {
    &&& p <= q <= s.len()
    &&& forall|j: int| p <= j < q ==> #[trigger] s[j] != c
    &&& q < s.len() ==> s[q] == c
}

/// One byte at a time. The second result counts loop iterations.
#[doc(hidden)]
pub fn find_scalar(s: &[u8], p: usize, c: u8) -> (r: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_at(s@, p as int, c, r.0 as int),
        0 <= r.1@ <= r.0 - p,
{
    let mut q = p;
    while q < s.len() && s[q] != c
        invariant
            p <= q <= s@.len(),
            forall|j: int| p <= j < q ==> #[trigger] s@[j] != c,
        decreases s@.len() - q,
    {
        q += 1;
    }
    (q, Ghost(q - p))
}

} // verus!

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
verus! {

broadcast use crate::neon::group_neon;

/// Shifting a 16-bit mask right by `s` moves bit `k + s` to bit `k` and
/// clears the top `s` bits.
#[doc(hidden)]
pub proof fn lemma_shr(m: u32, s: u32, k: u32)
    requires
        m < 0x10000,
        s < 16,
        k < 32,
    ensures
        m >> s < 0x10000,
        k + s < 16 ==> bit(m >> s, k) == bit(m, (k + s) as u32),
        k + s >= 16 ==> !bit(m >> s, k),
{
    assert(m < 0x10000 && s < 16 ==> m >> s < 0x10000) by (bit_vector);
    assert(m < 0x10000 && s < 16 && k < 32 ==> (k + s < 16 ==> (((m >> s) >> k) & 1u32 == 1u32) == ((m >> (k + s))
        & 1u32 == 1u32))) by (bit_vector);
    assert(m < 0x10000 && s < 16 && k < 32 ==> (k + s >= 16 ==> !(((m >> s) >> k) & 1u32 == 1u32))) by (bit_vector);
}

/// The lowest set bit of `m` at or after bit `sh`, counted from `sh`, or
/// `16 - sh` if there is none.
#[inline(always)]
#[doc(hidden)]
pub fn mask_first(m: u32, sh: u32) -> (d: u32)
    requires
        m < 0x10000,
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|k: u32| k < d ==> !#[trigger] bit(m, (k + sh) as u32),
        d < 16 - sh ==> bit(m, (d + sh) as u32),
{
    let s = m >> sh;
    let t = s.trailing_zeros();
    let d = if t > 16 - sh {
        16 - sh
    } else {
        t
    };
    proof {
        vstd::std_specs::bits::axiom_u32_trailing_zeros(s);
        assert forall|k: u32| k < d implies !#[trigger] bit(m, (k + sh) as u32) by {
            lemma_shr(m, sh, k);
            assert((s >> k) & 1u32 == 0u32);
        }
        if d < 16 - sh {
            lemma_shr(m, sh, t);
        }
    }
    d
}

/// Bit `j` of the nibble mask shifted right by `4 sh` is set exactly when
/// lane `j / 4 + sh` is 0xFF, for the lanes that are left.
#[doc(hidden)]
pub proof fn lemma_nib_shift(n: u64, a: Seq<u8>, sh: u64, j: u64)
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
        crate::neon_mask::lemma_nibmask_bit(n, a, js);
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
/// `16 - sh` if there is none.
#[inline(always)]
#[doc(hidden)]
pub fn nib_first(v: crate::neon::uint8x16_t, sh: u32) -> (d: u32)
    requires
        crate::neon::neon(),
        crate::neon_mask::is_mask(crate::neon::n8(v)),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|k: u32| k < d ==> #[trigger] crate::neon::n8(v)[(k + sh) as int] != 0xFF,
        d < 16 - sh ==> crate::neon::n8(v)[(d + sh) as int] == 0xFF,
{
    let n = crate::neon_mask::nibmask16(v);
    let s = n >> (4 * sh as u64);
    let t = s.trailing_zeros();
    let e = t / 4;
    let d = if e > 16 - sh {
        16 - sh
    } else {
        e
    };
    proof {
        vstd::std_specs::bits::axiom_u64_trailing_zeros(s);
        let a = crate::neon::n8(v);
        assert forall|k: u32| k < d implies #[trigger] crate::neon::n8(v)[(k + sh) as int] != 0xFF by {
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

/// The first `c` from `q + sh` on in `s[q..q + 16]`, counted from
/// `q + sh`, or `16 - sh` if there is none.
#[inline(always)]
#[doc(hidden)]
pub fn eq_from<const NEON: bool>(s: &[u8], q: usize, sh: u32, c: u8) -> (d: u32)
    requires
        NEON ==> crate::neon::neon(),
        q + 16 <= s@.len(),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|j: int| q + sh <= j < q + sh + d ==> #[trigger] s@[j] != c,
        d < 16 - sh ==> s@[q + sh + d] == c,
{
    if NEON {
        let x = crate::neon::vld1q_u8_at(s, q);
        let v = crate::neon::vceqq_u8(x, crate::neon::vdupq_n_u8(c));
        proof {
            assert forall|j: int| 0 <= j < 16 implies (#[trigger] crate::neon::n8(v)[j] == 0xFF) == (s@[q + j] == c)
                && (crate::neon::n8(v)[j] == 0xFF || crate::neon::n8(v)[j] == 0) by {
                assert(crate::neon::n8(x)[j] == s@[q + j]);
            }
        }
        let d = nib_first(v, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies #[trigger] s@[j] != c by {
                assert(crate::neon::n8(v)[(((j - q - sh) as u32) + sh) as int] != 0xFF);
            }
        }
        d
    } else {
        let x = load16(s, q);
        let e = eq16(x, splat16(c));
        let m = movemask16(e);
        proof {
            assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == (s@[q + k] == c) by {
                assert(b16(x)[k as int] == s@.subrange(q as int, q + 16)[k as int]);
            }
        }
        let d = mask_first(m, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies #[trigger] s@[j] != c by {
                assert(!bit(m, (((j - q - sh) as u32) + sh) as u32));
            }
            if d < 16 - sh {
                assert(bit(m, (d + sh) as u32));
            }
        }
        d
    }
}

/// Whether `c` is absent from `s[p..p + 64]`. (False may also mean
/// present.)
#[inline(always)]
#[doc(hidden)]
pub fn none64<const NEON: bool>(s: &[u8], p: usize, c: u8) -> (r: bool)
    requires
        NEON ==> crate::neon::neon(),
        p + 64 <= s@.len(),
    ensures
        r ==> forall|j: int| p <= j < p + 64 ==> #[trigger] s@[j] != c,
{
    let n = s.len();
    assert(p + 64 <= n);
    if NEON {
        let cc = crate::neon::vdupq_n_u8(c);
        let x0 = crate::neon::vld1q_u8_at(s, p);
        let x1 = crate::neon::vld1q_u8_at(s, p + 16);
        let x2 = crate::neon::vld1q_u8_at(s, p + 32);
        let x3 = crate::neon::vld1q_u8_at(s, p + 48);
        let e0 = crate::neon::vceqq_u8(x0, cc);
        let e1 = crate::neon::vceqq_u8(x1, cc);
        let e2 = crate::neon::vceqq_u8(x2, cc);
        let e3 = crate::neon::vceqq_u8(x3, cc);
        let f = crate::neon::vorrq_u8(e0, e1);
        let g = crate::neon::vorrq_u8(e2, e3);
        let o = crate::neon::vorrq_u8(f, g);
        proof {
            assert forall|k: int| 0 <= k < 16 implies (#[trigger] crate::neon::n8(o)[k] == 0xFF) == (s@[p + k] == c || s@[p
                + 16 + k] == c || s@[p + 32 + k] == c || s@[p + 48 + k] == c) && (crate::neon::n8(o)[k] == 0xFF
                || crate::neon::n8(o)[k] == 0) by {
                assert(crate::neon::n8(x0)[k] == s@[p + k]);
                assert(crate::neon::n8(x1)[k] == s@[p + 16 + k]);
                assert(crate::neon::n8(x2)[k] == s@[p + 32 + k]);
                assert(crate::neon::n8(x3)[k] == s@[p + 48 + k]);
                let a0 = crate::neon::n8(e0)[k];
                let a1 = crate::neon::n8(e1)[k];
                let a2 = crate::neon::n8(e2)[k];
                let a3 = crate::neon::n8(e3)[k];
                lemma_mask_ops(a0, a1);
                lemma_mask_ops(a2, a3);
                assert(crate::neon::n8(f)[k] == a0 | a1);
                assert(crate::neon::n8(g)[k] == a2 | a3);
                lemma_mask_ops(a0 | a1, a2 | a3);
                assert(crate::neon::n8(o)[k] == (a0 | a1) | (a2 | a3));
            }
        }
        let m = crate::neon_mask::nibmask16(o);
        proof {
            if m == 0 {
                assert forall|j: int| p <= j < p + 64 implies #[trigger] s@[j] != c by {
                    let k = (j - p) % 16;
                    let bitj = (4 * k) as u64;
                    crate::neon_mask::lemma_nibmask_bit(m, crate::neon::n8(o), bitj);
                    assert(bitj < 64 ==> (0u64 >> bitj) & 1 == 0) by (bit_vector);
                    assert(bitj / 4 == k as u64);
                    assert(crate::neon::n8(o)[k] != 0xFF);
                }
            }
        }
        m == 0
    } else {
        let cc = splat16(c);
        let x0 = load16(s, p);
        let x1 = load16(s, p + 16);
        let x2 = load16(s, p + 32);
        let x3 = load16(s, p + 48);
        let m0 = movemask16(eq16(x0, cc));
        let m1 = movemask16(eq16(x1, cc));
        let m2 = movemask16(eq16(x2, cc));
        let m3 = movemask16(eq16(x3, cc));
        let m = (m0 | m1) | (m2 | m3);
        proof {
            if m == 0 {
                assert((m0 | m1) | (m2 | m3) == 0 ==> m0 == 0 && m1 == 0 && m2 == 0 && m3 == 0) by (bit_vector);
                assert forall|j: int| p <= j < p + 64 implies #[trigger] s@[j] != c by {
                    let k = ((j - p) % 16) as u32;
                    assert(k < 32 ==> !((0u32 >> k) & 1u32 == 1u32)) by (bit_vector);
                    assert(!bit(0, k));
                    assert(b16(x0)[k as int] == s@.subrange(p as int, p + 16)[k as int]);
                    assert(b16(x1)[k as int] == s@.subrange(p + 16, p + 32)[k as int]);
                    assert(b16(x2)[k as int] == s@.subrange(p + 32, p + 48)[k as int]);
                    assert(b16(x3)[k as int] == s@.subrange(p + 48, p + 64)[k as int]);
                    assert(bit(m0, k) == (s@[p + k] == c));
                    assert(bit(m1, k) == (s@[p + 16 + k] == c));
                    assert(bit(m2, k) == (s@[p + 32 + k] == c));
                    assert(bit(m3, k) == (s@[p + 48 + k] == c));
                }
            }
        }
        m == 0
    }
}

#[doc(hidden)]
pub fn find_impl<const NEON: bool>(s: &[u8], p0: usize, c: u8) -> (r: (usize, Ghost<int>))
    requires
        NEON ==> crate::neon::neon(),
        p0 <= s@.len(),
    ensures
        first_at(s@, p0 as int, c, r.0 as int),
        0 <= r.1@ <= r.0 - p0 + 1,
        r.0 > p0 ==> r.1@ <= r.0 - p0,
{
    let mut p = p0;
    let ghost mut steps: int = 0;
    // 64 bytes at a time while the byte is absent.
    while s.len() - p >= 64
        invariant
            NEON ==> crate::neon::neon(),
            p0 <= p <= s@.len(),
            forall|j: int| p0 <= j < p ==> #[trigger] s@[j] != c,
            0 <= steps,
            16 * steps <= p - p0,
        decreases s@.len() - p,
    {
        if !none64::<NEON>(s, p, c) {
            break;
        }
        proof {
            steps = steps + 1;
        }
        p += 64;
    }
    while s.len() - p >= 16
        invariant
            NEON ==> crate::neon::neon(),
            p0 <= p <= s@.len(),
            forall|j: int| p0 <= j < p ==> #[trigger] s@[j] != c,
            0 <= steps,
            16 * steps <= p - p0,
        decreases s@.len() - p,
    {
        let d = eq_from::<NEON>(s, p, 0, c);
        if d < 16 {
            return (p + d as usize, Ghost(steps + 1));
        }
        proof {
            steps = steps + 1;
        }
        p += 16;
    }
    // The last bytes: one block ending at the end of the text, with the
    // lanes before `p` skipped.
    if s.len() >= 16 && p < s.len() {
        let q = s.len() - 16;
        let sh = (p - q) as u32;
        let d = eq_from::<NEON>(s, q, sh, c);
        return (p + d as usize, Ghost(steps + 1));
    }
    let (e, g) = find_scalar(s, p, c);
    (e, Ghost(steps + g@))
}

/// Two masks of 0x00 and 0xFF lanes, combined.
#[doc(hidden)]
pub proof fn lemma_mask_ops(x: u8, y: u8)
    requires
        x == 0 || x == 0xFF,
        y == 0 || y == 0xFF,
    ensures
        (x | y) == 0 || (x | y) == 0xFF,
        (x & y) == 0 || (x & y) == 0xFF,
        ((x | y) == 0xFF) == (x == 0xFF || y == 0xFF),
        ((x & y) == 0xFF) == (x == 0xFF && y == 0xFF),
{
    assert((x == 0 || x == 0xFF) && (y == 0 || y == 0xFF) ==> ((x | y) == 0 || (x | y) == 0xFF) && ((x & y) == 0 || (x
        & y) == 0xFF) && (((x | y) == 0xFF) == (x == 0xFF || y == 0xFF)) && (((x & y) == 0xFF) == (x == 0xFF && y
        == 0xFF))) by (bit_vector);
}

/// Bits of two 16-bit masks, combined.
#[doc(hidden)]
pub proof fn lemma_bit_ops(x: u32, y: u32, k: u32)
    requires
        x < 0x10000,
        y < 0x10000,
        k < 32,
    ensures
        (x | y) < 0x10000,
        (x & y) < 0x10000,
        bit(x | y, k) == (bit(x, k) || bit(y, k)),
        bit(x & y, k) == (bit(x, k) && bit(y, k)),
{
    assert(x < 0x10000 && y < 0x10000 ==> (x | y) < 0x10000 && (x & y) < 0x10000) by (bit_vector);
    assert(k < 32 ==> ((((x | y) >> k) & 1u32 == 1u32) == (((x >> k) & 1u32 == 1u32) || ((y >> k) & 1u32 == 1u32))))
        by (bit_vector);
    assert(k < 32 ==> ((((x & y) >> k) & 1u32 == 1u32) == (((x >> k) & 1u32 == 1u32) && ((y >> k) & 1u32 == 1u32))))
        by (bit_vector);
}

/// Where the first `c` at or after `p` is, or the end of `s`. The second
/// result counts loop iterations.
pub fn find_byte(s: &[u8], p: usize, c: u8) -> (r: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_at(s@, p as int, c, r.0 as int),
        0 <= r.1@ <= r.0 - p + 1,
        r.0 > p ==> r.1@ <= r.0 - p,
{
    if crate::neon::has_neon() {
        find_impl::<true>(s, p, c)
    } else {
        find_impl::<false>(s, p, c)
    }
}

} // verus!

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
verus! {

/// Where the first `c` at or after `p` is, or the end of `s`. The second
/// result counts loop iterations.
pub fn find_byte(s: &[u8], p: usize, c: u8) -> (r: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_at(s@, p as int, c, r.0 as int),
        0 <= r.1@ <= r.0 - p + 1,
        r.0 > p ==> r.1@ <= r.0 - p,
{
    find_scalar(s, p, c)
}

} // verus!
