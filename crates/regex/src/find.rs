//! Finding the next occurrence of one byte, 16 bytes at a time: SSE2 on
//! x86-64 and NEON on AArch64, proven against the plain definition.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
use crate::lanes::*;
#[cfg(verus_only)]
pub use verilith_simd::find::first_at;
pub use verilith_simd::find::find_byte;
#[cfg(test)]
use verilith_simd::find::{find_impl, find_scalar};
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
use verilith_simd::find::{mask_first, nib_first};
#[cfg(all(verus_only, any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
use verilith_simd::find::{lemma_bit_ops, lemma_mask_ops, lemma_shr};
use vstd::prelude::*;

verus! {

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

} // verus!

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
verus! {

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
