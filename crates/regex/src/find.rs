//! Finding the next occurrence of one byte, 16 bytes at a time: SSE2 on
//! x86-64 and NEON on AArch64, proven against the plain definition.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
use crate::lanes::*;
use vstd::prelude::*;

verus! {

/// `q` is where the first `c` at or after `p` is, or the end of `s`.
pub open spec fn first_at(s: Seq<u8>, p: int, c: u8, q: int) -> bool {
    &&& p <= q <= s.len()
    &&& forall|j: int| p <= j < q ==> #[trigger] s[j] != c
    &&& q < s.len() ==> s[q] == c
}

/// One byte at a time. The second result counts loop iterations.
fn find_scalar(s: &[u8], p: usize, c: u8) -> (r: (usize, Ghost<int>))
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

/// `b` is in one of the three ranges `r.0..=r.1`, `r.2..=r.3`,
/// `r.4..=r.5`.
pub open spec fn inr(b: u8, r: (u8, u8, u8, u8, u8, u8)) -> bool {
    (r.0 <= b && b <= r.1) || (r.2 <= b && b <= r.3) || (r.4 <= b && b <= r.5)
}

#[inline(always)]
pub fn in_rng(b: u8, r: (u8, u8, u8, u8, u8, u8)) -> (x: bool)
    ensures
        x == inr(b, r),
{
    (r.0 <= b && b <= r.1) || (r.2 <= b && b <= r.3) || (r.4 <= b && b <= r.5)
}

/// `q` is where the first byte in the ranges at or after `p` is, or the
/// end of `s`.
pub open spec fn first_rng(s: Seq<u8>, p: int, r: (u8, u8, u8, u8, u8, u8), q: int) -> bool {
    &&& p <= q <= s.len()
    &&& forall|j: int| p <= j < q ==> !inr(#[trigger] s[j], r)
    &&& q < s.len() ==> inr(s[q], r)
}

/// One byte at a time. The second result counts loop iterations.
fn rng_scalar(s: &[u8], p: usize, r: (u8, u8, u8, u8, u8, u8)) -> (x: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_rng(s@, p as int, r, x.0 as int),
        0 <= x.1@ <= x.0 - p,
{
    let mut q = p;
    while q < s.len() && !in_rng(s[q], r)
        invariant
            p <= q <= s@.len(),
            forall|j: int| p <= j < q ==> !inr(#[trigger] s@[j], r),
        decreases s@.len() - q,
    {
        q += 1;
    }
    (q, Ghost(q - p))
}

/// Byte `j` is one of `q.0`, `q.1` and the byte after it is one of
/// `q.2`, `q.3`.
pub open spec fn cand(s: Seq<u8>, j: int, q: (u8, u8, u8, u8)) -> bool {
    0 <= j && j + 1 < s.len() && (s[j] == q.0 || s[j] == q.1) && (s[j + 1] == q.2 || s[j + 1] == q.3)
}

/// `r` is where the first such pair at or after `p` is, or the end of `s`.
pub open spec fn first_pair(s: Seq<u8>, p: int, q: (u8, u8, u8, u8), r: int) -> bool {
    &&& p <= r <= s.len()
    &&& forall|j: int| p <= j < r ==> !#[trigger] cand(s, j, q)
    &&& r < s.len() ==> cand(s, r, q)
}

/// One byte at a time. The second result counts loop iterations.
fn pair_scalar(s: &[u8], p: usize, q4: (u8, u8, u8, u8)) -> (r: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_pair(s@, p as int, q4, r.0 as int),
        0 <= r.1@ <= r.0 - p,
{
    let n = s.len();
    let mut q = p;
    while q < n
        invariant
            n == s@.len(),
            p <= q <= n,
            forall|j: int| p <= j < q ==> !#[trigger] cand(s@, j, q4),
        decreases n - q,
    {
        if q + 1 < n && (s[q] == q4.0 || s[q] == q4.1) && (s[q + 1] == q4.2 || s[q + 1] == q4.3) {
            return (q, Ghost(q - p));
        }
        q += 1;
    }
    (n, Ghost(n - p))
}

} // verus!

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
verus! {

broadcast use verilith_simd::neon::group_neon;

/// Shifting a 16-bit mask right by `s` moves bit `k + s` to bit `k` and
/// clears the top `s` bits.
proof fn lemma_shr(m: u32, s: u32, k: u32)
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
fn mask_first(m: u32, sh: u32) -> (d: u32)
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
        verilith_simd::neon_mask::lemma_nibmask_bit(n, a, js);
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
fn nib_first(v: verilith_simd::neon::uint8x16_t, sh: u32) -> (d: u32)
    requires
        verilith_simd::neon::neon(),
        verilith_simd::neon_mask::is_mask(verilith_simd::neon::n8(v)),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|k: u32| k < d ==> #[trigger] verilith_simd::neon::n8(v)[(k + sh) as int] != 0xFF,
        d < 16 - sh ==> verilith_simd::neon::n8(v)[(d + sh) as int] == 0xFF,
{
    let n = verilith_simd::neon_mask::nibmask16(v);
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
        let a = verilith_simd::neon::n8(v);
        assert forall|k: u32| k < d implies #[trigger] verilith_simd::neon::n8(v)[(k + sh) as int] != 0xFF by {
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
fn eq_from<const NEON: bool>(s: &[u8], q: usize, sh: u32, c: u8) -> (d: u32)
    requires
        NEON ==> verilith_simd::neon::neon(),
        q + 16 <= s@.len(),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|j: int| q + sh <= j < q + sh + d ==> #[trigger] s@[j] != c,
        d < 16 - sh ==> s@[q + sh + d] == c,
{
    if NEON {
        let x = verilith_simd::neon::vld1q_u8_at(s, q);
        let v = verilith_simd::neon::vceqq_u8(x, verilith_simd::neon::vdupq_n_u8(c));
        proof {
            assert forall|j: int| 0 <= j < 16 implies (#[trigger] verilith_simd::neon::n8(v)[j] == 0xFF) == (s@[q + j] == c)
                && (verilith_simd::neon::n8(v)[j] == 0xFF || verilith_simd::neon::n8(v)[j] == 0) by {
                assert(verilith_simd::neon::n8(x)[j] == s@[q + j]);
            }
        }
        let d = nib_first(v, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies #[trigger] s@[j] != c by {
                assert(verilith_simd::neon::n8(v)[(((j - q - sh) as u32) + sh) as int] != 0xFF);
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
fn none64<const NEON: bool>(s: &[u8], p: usize, c: u8) -> (r: bool)
    requires
        NEON ==> verilith_simd::neon::neon(),
        p + 64 <= s@.len(),
    ensures
        r ==> forall|j: int| p <= j < p + 64 ==> #[trigger] s@[j] != c,
{
    let n = s.len();
    assert(p + 64 <= n);
    if NEON {
        let cc = verilith_simd::neon::vdupq_n_u8(c);
        let x0 = verilith_simd::neon::vld1q_u8_at(s, p);
        let x1 = verilith_simd::neon::vld1q_u8_at(s, p + 16);
        let x2 = verilith_simd::neon::vld1q_u8_at(s, p + 32);
        let x3 = verilith_simd::neon::vld1q_u8_at(s, p + 48);
        let e0 = verilith_simd::neon::vceqq_u8(x0, cc);
        let e1 = verilith_simd::neon::vceqq_u8(x1, cc);
        let e2 = verilith_simd::neon::vceqq_u8(x2, cc);
        let e3 = verilith_simd::neon::vceqq_u8(x3, cc);
        let f = verilith_simd::neon::vorrq_u8(e0, e1);
        let g = verilith_simd::neon::vorrq_u8(e2, e3);
        let o = verilith_simd::neon::vorrq_u8(f, g);
        proof {
            assert forall|k: int| 0 <= k < 16 implies (#[trigger] verilith_simd::neon::n8(o)[k] == 0xFF) == (s@[p + k] == c || s@[p
                + 16 + k] == c || s@[p + 32 + k] == c || s@[p + 48 + k] == c) && (verilith_simd::neon::n8(o)[k] == 0xFF
                || verilith_simd::neon::n8(o)[k] == 0) by {
                assert(verilith_simd::neon::n8(x0)[k] == s@[p + k]);
                assert(verilith_simd::neon::n8(x1)[k] == s@[p + 16 + k]);
                assert(verilith_simd::neon::n8(x2)[k] == s@[p + 32 + k]);
                assert(verilith_simd::neon::n8(x3)[k] == s@[p + 48 + k]);
                let a0 = verilith_simd::neon::n8(e0)[k];
                let a1 = verilith_simd::neon::n8(e1)[k];
                let a2 = verilith_simd::neon::n8(e2)[k];
                let a3 = verilith_simd::neon::n8(e3)[k];
                lemma_mask_ops(a0, a1);
                lemma_mask_ops(a2, a3);
                assert(verilith_simd::neon::n8(f)[k] == a0 | a1);
                assert(verilith_simd::neon::n8(g)[k] == a2 | a3);
                lemma_mask_ops(a0 | a1, a2 | a3);
                assert(verilith_simd::neon::n8(o)[k] == (a0 | a1) | (a2 | a3));
            }
        }
        let m = verilith_simd::neon_mask::nibmask16(o);
        proof {
            if m == 0 {
                assert forall|j: int| p <= j < p + 64 implies #[trigger] s@[j] != c by {
                    let k = (j - p) % 16;
                    let bitj = (4 * k) as u64;
                    verilith_simd::neon_mask::lemma_nibmask_bit(m, verilith_simd::neon::n8(o), bitj);
                    assert(bitj < 64 ==> (0u64 >> bitj) & 1 == 0) by (bit_vector);
                    assert(bitj / 4 == k as u64);
                    assert(verilith_simd::neon::n8(o)[k] != 0xFF);
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

fn find_impl<const NEON: bool>(s: &[u8], p0: usize, c: u8) -> (r: (usize, Ghost<int>))
    requires
        NEON ==> verilith_simd::neon::neon(),
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
            NEON ==> verilith_simd::neon::neon(),
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
            NEON ==> verilith_simd::neon::neon(),
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
proof fn lemma_mask_ops(x: u8, y: u8)
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
proof fn lemma_bit_ops(x: u32, y: u32, k: u32)
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

/// The first pair from `q + sh` on that starts in `s[q..q + 16]`,
/// counted from `q + sh`, or `16 - sh` if there is none.
#[inline(always)]
fn pair_from<const NEON: bool>(s: &[u8], q: usize, sh: u32, q4: (u8, u8, u8, u8)) -> (d: u32)
    requires
        NEON ==> verilith_simd::neon::neon(),
        q + 17 <= s@.len(),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|j: int| q + sh <= j < q + sh + d ==> !#[trigger] cand(s@, j, q4),
        d < 16 - sh ==> cand(s@, q + sh + d, q4),
{
    let n = s.len();
    assert(q + 17 <= n);
    if NEON {
        let x0 = verilith_simd::neon::vld1q_u8_at(s, q);
        let x1 = verilith_simd::neon::vld1q_u8_at(s, q + 1);
        let ea = verilith_simd::neon::vceqq_u8(x0, verilith_simd::neon::vdupq_n_u8(q4.0));
        let eb = verilith_simd::neon::vceqq_u8(x0, verilith_simd::neon::vdupq_n_u8(q4.1));
        let ec = verilith_simd::neon::vceqq_u8(x1, verilith_simd::neon::vdupq_n_u8(q4.2));
        let ed = verilith_simd::neon::vceqq_u8(x1, verilith_simd::neon::vdupq_n_u8(q4.3));
        let f = verilith_simd::neon::vorrq_u8(ea, eb);
        let g = verilith_simd::neon::vorrq_u8(ec, ed);
        let v = verilith_simd::neon::vandq_u8(f, g);
        proof {
            assert forall|j: int| 0 <= j < 16 implies (#[trigger] verilith_simd::neon::n8(v)[j] == 0xFF) == cand(s@, q + j, q4)
                && (verilith_simd::neon::n8(v)[j] == 0xFF || verilith_simd::neon::n8(v)[j] == 0) by {
                assert(verilith_simd::neon::n8(x0)[j] == s@[q + j]);
                assert(verilith_simd::neon::n8(x1)[j] == s@[q + 1 + j]);
                let a = verilith_simd::neon::n8(ea)[j];
                let b = verilith_simd::neon::n8(eb)[j];
                let c = verilith_simd::neon::n8(ec)[j];
                let e = verilith_simd::neon::n8(ed)[j];
                lemma_mask_ops(a, b);
                lemma_mask_ops(c, e);
                assert(verilith_simd::neon::n8(f)[j] == a | b);
                assert(verilith_simd::neon::n8(g)[j] == c | e);
                lemma_mask_ops(a | b, c | e);
                assert(verilith_simd::neon::n8(v)[j] == (a | b) & (c | e));
            }
        }
        let d = nib_first(v, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies !#[trigger] cand(s@, j, q4) by {
                assert(verilith_simd::neon::n8(v)[(((j - q - sh) as u32) + sh) as int] != 0xFF);
            }
        }
        d
    } else {
        let x0 = load16(s, q);
        let x1 = load16(s, q + 1);
        let ma = movemask16(eq16(x0, splat16(q4.0)));
        let mb = movemask16(eq16(x0, splat16(q4.1)));
        let mc = movemask16(eq16(x1, splat16(q4.2)));
        let md = movemask16(eq16(x1, splat16(q4.3)));
        let m = (ma | mb) & (mc | md);
        proof {
            lemma_bit_ops(ma, mb, 0);
            lemma_bit_ops(mc, md, 0);
            lemma_bit_ops(ma | mb, mc | md, 0);
            assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == cand(s@, q + k, q4) by {
                assert(b16(x0)[k as int] == s@.subrange(q as int, q + 16)[k as int]);
                assert(b16(x1)[k as int] == s@.subrange(q + 1, q + 17)[k as int]);
                assert(bit(ma, k) == (s@[q + k] == q4.0));
                assert(bit(mb, k) == (s@[q + k] == q4.1));
                assert(bit(mc, k) == (s@[q + k + 1] == q4.2));
                assert(bit(md, k) == (s@[q + k + 1] == q4.3));
                lemma_bit_ops(ma, mb, k);
                lemma_bit_ops(mc, md, k);
                lemma_bit_ops(ma | mb, mc | md, k);
            }
        }
        let d = mask_first(m, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies !#[trigger] cand(s@, j, q4) by {
                assert(!bit(m, (((j - q - sh) as u32) + sh) as u32));
            }
            if d < 16 - sh {
                assert(bit(m, (d + sh) as u32));
            }
        }
        d
    }
}

fn pair_impl<const NEON: bool>(s: &[u8], p0: usize, q4: (u8, u8, u8, u8)) -> (r: (usize, Ghost<int>))
    requires
        NEON ==> verilith_simd::neon::neon(),
        p0 <= s@.len(),
    ensures
        first_pair(s@, p0 as int, q4, r.0 as int),
        0 <= r.1@ <= r.0 - p0 + 1,
        r.0 > p0 ==> r.1@ <= r.0 - p0,
{
    let n = s.len();
    let mut p = p0;
    let ghost mut steps: int = 0;
    while n - p >= 17
        invariant
            NEON ==> verilith_simd::neon::neon(),
            n == s@.len(),
            p0 <= p <= n,
            forall|j: int| p0 <= j < p ==> !#[trigger] cand(s@, j, q4),
            0 <= steps,
            16 * steps <= p - p0,
        decreases n - p,
    {
        let d = pair_from::<NEON>(s, p, 0, q4);
        if d < 16 {
            return (p + d as usize, Ghost(steps + 1));
        }
        proof {
            steps = steps + 1;
        }
        p += 16;
    }
    // The last bytes: one block that ends a byte before the end of the
    // text, with the lanes before `p` skipped. The last byte starts no
    // pair.
    if p < n && n >= 17 && p + 1 < n {
        let q = n - 17;
        let sh = (p - q) as u32;
        let d = pair_from::<NEON>(s, q, sh, q4);
        if d < 16 - sh {
            return (p + d as usize, Ghost(steps + 1));
        }
        return (n, Ghost(steps + 1));
    }
    let (e, g) = pair_scalar(s, p, q4);
    (e, Ghost(steps + g@))
}

/// Where the first pair of bytes `(q4.0 or q4.1, q4.2 or q4.3)` at or
/// after `p` starts, or the end of `s`. The second result counts loop
/// iterations.
/// What the range test computes in a lane: zero exactly when `x` is in
/// `lo..=hi`.
pub open spec fn rdist(x: u8, lo: u8, hi: u8) -> u8 {
    (if x < hi {
        0u8
    } else {
        (x - hi) as u8
    }) | (if lo < x {
        0u8
    } else {
        (lo - x) as u8
    })
}

proof fn lemma_rdist(x: u8, lo: u8, hi: u8)
    ensures
        (rdist(x, lo, hi) == 0) == (lo <= x && x <= hi),
{
    let a = if x < hi {
        0u8
    } else {
        (x - hi) as u8
    };
    let b = if lo < x {
        0u8
    } else {
        (lo - x) as u8
    };
    assert(((a | b) == 0) == (a == 0 && b == 0)) by (bit_vector);
}

/// The first byte in the ranges from `q + sh` on in `s[q..q + 16]`,
/// counted from `q + sh`, or `16 - sh` if there is none. The second and
/// third ranges are tested only if `two` and `three` say they differ
/// from the first.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
#[inline(always)]
fn rng_from<const NEON: bool>(s: &[u8], q: usize, sh: u32, r: (u8, u8, u8, u8, u8, u8), two: bool, three: bool) -> (d:
    u32)
    requires
        NEON ==> verilith_simd::neon::neon(),
        q + 16 <= s@.len(),
        sh < 16,
        !two ==> r.2 == r.0 && r.3 == r.1,
        !three ==> r.4 == r.0 && r.5 == r.1,
    ensures
        d <= 16 - sh,
        forall|j: int| q + sh <= j < q + sh + d ==> !inr(#[trigger] s@[j], r),
        d < 16 - sh ==> inr(s@[q + sh + d], r),
{
    if NEON {
        let x = verilith_simd::neon::vld1q_u8_at(s, q);
        let z = verilith_simd::neon::vdupq_n_u8(0);
        let d0 = verilith_simd::neon::vorrq_u8(
            verilith_simd::neon::vqsubq_u8(x, verilith_simd::neon::vdupq_n_u8(r.1)),
            verilith_simd::neon::vqsubq_u8(verilith_simd::neon::vdupq_n_u8(r.0), x),
        );
        let mut v = verilith_simd::neon::vceqq_u8(d0, z);
        proof {
            assert forall|j: int| 0 <= j < 16 implies (#[trigger] verilith_simd::neon::n8(v)[j] == 0xFF) == (r.0 <= s@[q + j]
                && s@[q + j] <= r.1) && (verilith_simd::neon::n8(v)[j] == 0xFF || verilith_simd::neon::n8(v)[j] == 0) by {
                let b = s@[q + j];
                assert(verilith_simd::neon::n8(x)[j] == b);
                assert(verilith_simd::neon::n8(d0)[j] == rdist(b, r.0, r.1));
                lemma_rdist(b, r.0, r.1);
            }
        }
        if two {
            let d1 = verilith_simd::neon::vorrq_u8(
                verilith_simd::neon::vqsubq_u8(x, verilith_simd::neon::vdupq_n_u8(r.3)),
                verilith_simd::neon::vqsubq_u8(verilith_simd::neon::vdupq_n_u8(r.2), x),
            );
            let e1 = verilith_simd::neon::vceqq_u8(d1, z);
            let ghost v0 = v;
            v = verilith_simd::neon::vorrq_u8(v, e1);
            proof {
                assert forall|j: int| 0 <= j < 16 implies (#[trigger] verilith_simd::neon::n8(v)[j] == 0xFF) == ((r.0 <= s@[q
                    + j] && s@[q + j] <= r.1) || (r.2 <= s@[q + j] && s@[q + j] <= r.3)) && (verilith_simd::neon::n8(v)[j] == 0xFF
                    || verilith_simd::neon::n8(v)[j] == 0) by {
                    let b = s@[q + j];
                    assert(verilith_simd::neon::n8(x)[j] == b);
                    assert(verilith_simd::neon::n8(d1)[j] == rdist(b, r.2, r.3));
                    lemma_rdist(b, r.2, r.3);
                    let a0 = verilith_simd::neon::n8(v0)[j];
                    let a1 = verilith_simd::neon::n8(e1)[j];
                    lemma_mask_ops(a0, a1);
                    assert(verilith_simd::neon::n8(v)[j] == a0 | a1);
                }
            }
        }
        if three {
            let d2 = verilith_simd::neon::vorrq_u8(
                verilith_simd::neon::vqsubq_u8(x, verilith_simd::neon::vdupq_n_u8(r.5)),
                verilith_simd::neon::vqsubq_u8(verilith_simd::neon::vdupq_n_u8(r.4), x),
            );
            let e2 = verilith_simd::neon::vceqq_u8(d2, z);
            let ghost v0 = v;
            v = verilith_simd::neon::vorrq_u8(v, e2);
            proof {
                assert forall|j: int| 0 <= j < 16 implies (#[trigger] verilith_simd::neon::n8(v)[j] == 0xFF) == inr(s@[q + j], r)
                    && (verilith_simd::neon::n8(v)[j] == 0xFF || verilith_simd::neon::n8(v)[j] == 0) by {
                    let b = s@[q + j];
                    assert(verilith_simd::neon::n8(x)[j] == b);
                    assert(verilith_simd::neon::n8(d2)[j] == rdist(b, r.4, r.5));
                    lemma_rdist(b, r.4, r.5);
                    let a0 = verilith_simd::neon::n8(v0)[j];
                    let a2 = verilith_simd::neon::n8(e2)[j];
                    lemma_mask_ops(a0, a2);
                    assert(verilith_simd::neon::n8(v)[j] == a0 | a2);
                }
            }
        }
        proof {
            assert forall|j: int| 0 <= j < 16 implies (#[trigger] verilith_simd::neon::n8(v)[j] == 0xFF) == inr(s@[q + j], r) by {}
        }
        let d = nib_first(v, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies !inr(#[trigger] s@[j], r) by {
                assert(verilith_simd::neon::n8(v)[(((j - q - sh) as u32) + sh) as int] != 0xFF);
            }
        }
        d
    } else {
        let x = load16(s, q);
        let z = splat16(0);
        let d0 = or16(subs16(x, splat16(r.1)), subs16(splat16(r.0), x));
        let mut m = movemask16(eq16(d0, z));
        proof {
            assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == (r.0 <= s@[q + k] && s@[q + k] <= r.1) by {
                let b = s@[q + k];
                assert(b16(x)[k as int] == s@.subrange(q as int, q + 16)[k as int]);
                assert(b16(d0)[k as int] == rdist(b, r.0, r.1));
                lemma_rdist(b, r.0, r.1);
            }
        }
        if two {
            let d1 = or16(subs16(x, splat16(r.3)), subs16(splat16(r.2), x));
            let m1 = movemask16(eq16(d1, z));
            let ghost m0 = m;
            m = m | m1;
            proof {
                lemma_bit_ops(m0, m1, 0);
                assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == ((r.0 <= s@[q + k] && s@[q + k] <= r.1) || (
                r.2 <= s@[q + k] && s@[q + k] <= r.3)) by {
                    let b = s@[q + k];
                    assert(b16(x)[k as int] == s@.subrange(q as int, q + 16)[k as int]);
                    assert(b16(d1)[k as int] == rdist(b, r.2, r.3));
                    lemma_rdist(b, r.2, r.3);
                    lemma_bit_ops(m0, m1, k);
                }
            }
        }
        if three {
            let d2 = or16(subs16(x, splat16(r.5)), subs16(splat16(r.4), x));
            let m2 = movemask16(eq16(d2, z));
            let ghost m0 = m;
            m = m | m2;
            proof {
                lemma_bit_ops(m0, m2, 0);
                assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == inr(s@[q + k], r) by {
                    let b = s@[q + k];
                    assert(b16(x)[k as int] == s@.subrange(q as int, q + 16)[k as int]);
                    assert(b16(d2)[k as int] == rdist(b, r.4, r.5));
                    lemma_rdist(b, r.4, r.5);
                    lemma_bit_ops(m0, m2, k);
                }
            }
        }
        proof {
            assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == inr(s@[q + k], r) by {}
        }
        let d = mask_first(m, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies !inr(#[trigger] s@[j], r) by {
                assert(!bit(m, (((j - q - sh) as u32) + sh) as u32));
            }
            if d < 16 - sh {
                assert(bit(m, (d + sh) as u32));
            }
        }
        d
    }
}

fn rng_impl<const NEON: bool>(s: &[u8], p0: usize, r: (u8, u8, u8, u8, u8, u8)) -> (x: (usize, Ghost<int>))
    requires
        NEON ==> verilith_simd::neon::neon(),
        p0 <= s@.len(),
    ensures
        first_rng(s@, p0 as int, r, x.0 as int),
        0 <= x.1@ <= x.0 - p0 + 1,
        x.0 > p0 ==> x.1@ <= x.0 - p0,
{
    let mut p = p0;
    let ghost mut steps: int = 0;
    let two = r.2 != r.0 || r.3 != r.1;
    let three = r.4 != r.0 || r.5 != r.1;
    while s.len() - p >= 16
        invariant
            NEON ==> verilith_simd::neon::neon(),
            p0 <= p <= s@.len(),
            two == (r.2 != r.0 || r.3 != r.1),
            three == (r.4 != r.0 || r.5 != r.1),
            forall|j: int| p0 <= j < p ==> !inr(#[trigger] s@[j], r),
            0 <= steps,
            16 * steps <= p - p0,
        decreases s@.len() - p,
    {
        let d = rng_from::<NEON>(s, p, 0, r, two, three);
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
        let d = rng_from::<NEON>(s, q, sh, r, two, three);
        return (p + d as usize, Ghost(steps + 1));
    }
    let (e, g) = rng_scalar(s, p, r);
    (e, Ghost(steps + g@))
}

/// Where the first byte in the three ranges `r` at or after `p` is, or
/// the end of `s`. The second result counts loop iterations.
pub fn find_rng(s: &[u8], p: usize, r: (u8, u8, u8, u8, u8, u8)) -> (x: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_rng(s@, p as int, r, x.0 as int),
        0 <= x.1@ <= x.0 - p + 1,
        x.0 > p ==> x.1@ <= x.0 - p,
{
    if verilith_simd::neon::has_neon() {
        rng_impl::<true>(s, p, r)
    } else {
        rng_impl::<false>(s, p, r)
    }
}

pub fn find_pair(s: &[u8], p: usize, q4: (u8, u8, u8, u8)) -> (r: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_pair(s@, p as int, q4, r.0 as int),
        0 <= r.1@ <= r.0 - p + 1,
        r.0 > p ==> r.1@ <= r.0 - p,
{
    if verilith_simd::neon::has_neon() {
        pair_impl::<true>(s, p, q4)
    } else {
        pair_impl::<false>(s, p, q4)
    }
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
    if verilith_simd::neon::has_neon() {
        find_impl::<true>(s, p, c)
    } else {
        find_impl::<false>(s, p, c)
    }
}

} // verus!

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
verus! {

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

pub fn find_pair(s: &[u8], p: usize, q4: (u8, u8, u8, u8)) -> (r: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_pair(s@, p as int, q4, r.0 as int),
        0 <= r.1@ <= r.0 - p + 1,
        r.0 > p ==> r.1@ <= r.0 - p,
{
    pair_scalar(s, p, q4)
}

pub fn find_rng(s: &[u8], p: usize, r: (u8, u8, u8, u8, u8, u8)) -> (x: (usize, Ghost<int>))
    requires
        p <= s@.len(),
    ensures
        first_rng(s@, p as int, r, x.0 as int),
        0 <= x.1@ <= x.0 - p + 1,
        x.0 > p ==> x.1@ <= x.0 - p,
{
    rng_scalar(s, p, r)
}

} // verus!

#[cfg(all(test, any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
mod tests {
    use super::*;

    /// The NEON and SSE2 searches agree with the scalar one from every
    /// start, with the byte at every place or absent. Off AArch64 the
    /// NEON path runs on vsimd's emulation.
    #[test]
    fn neon_and_sse2_agree_with_scalar() {
        for len in (0..70usize).chain([128, 150, 200]) {
            for pos in 0..=len {
                for second in [None, Some(pos + 3), Some(pos + 20)] {
                    let mut d = vec![b'a'; len];
                    if pos < len {
                        d[pos] = b'Z';
                    }
                    if let Some(q) = second {
                        if q < len {
                            d[q] = b'Z';
                        }
                    }
                    for i in 0..=len {
                        let want = find_scalar(&d, i, b'Z').0;
                        assert_eq!(find_impl::<true>(&d, i, b'Z').0, want);
                        assert_eq!(find_impl::<false>(&d, i, b'Z').0, want);
                    }
                    // Ranges: one, two and three of them.
                    let mut g = d.clone();
                    if pos + 5 < len {
                        g[pos + 5] = b'7';
                    }
                    if pos + 9 < len {
                        g[pos + 9] = 0xC3;
                    }
                    for r in [
                        (b'Z', b'Z', b'Z', b'Z', b'Z', b'Z'),
                        (b'0', b'9', b'X', b'Z', b'0', b'9'),
                        (b'0', b'9', b'X', b'Z', 0xC2, 0xF4),
                        (0, 0, 0xFF, 0xFF, b'5', b'8'),
                    ] {
                        for i in 0..=len {
                            let want = rng_scalar(&g, i, r).0;
                            assert_eq!(rng_impl::<true>(&g, i, r).0, want);
                            assert_eq!(rng_impl::<false>(&g, i, r).0, want);
                        }
                    }
                    // Pairs: `Z` or `Y`, then `q` or `r`.
                    let q4 = (b'Z', b'Y', b'q', b'r');
                    for (k, tail) in [b'q', b'r', b'x'].into_iter().enumerate() {
                        let mut e = d.clone();
                        if pos + 1 < len {
                            e[pos + 1] = tail;
                        }
                        if k == 1 && pos < len {
                            e[pos] = b'Y';
                        }
                        for i in 0..=len {
                            let want = pair_scalar(&e, i, q4).0;
                            assert_eq!(pair_impl::<true>(&e, i, q4).0, want);
                            assert_eq!(pair_impl::<false>(&e, i, q4).0, want);
                        }
                    }
                }
            }
        }
    }
}
