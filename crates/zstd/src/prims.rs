//! Primitives. The trusted ones (with the CPU-feature wrappers in `cpu.rs`, the only `external_body` functions in this crate)
//! are the wild copies `put4`, `put_pairs4` and `extend_from`:
//! each `ensures` is the spec of the code under it. They copy 16 bytes at a
//! time where there is room, which may write past the new end of the vector
//! into its spare capacity and read up to 15 bytes past the end of the
//! source range (still inside the source buffer); neither is visible in the
//! vector's contents. To audit: check the bounds in each `if`.
use vstd::prelude::*;

verus! {

/// `v[i]` without the bounds check, which the `requires` replaces
/// (verified against vstd's spec of `get_unchecked`).
#[inline(always)]
pub fn row<T: Copy>(v: &[T], i: usize) -> (r: T)
    requires
        i < v@.len(),
    ensures
        r == v@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *v.get_unchecked(i) }
}

/// `a[i]` for an array, without the bounds check, which the `requires`
/// replaces (verified against vstd's spec of `get_unchecked`).
#[inline(always)]
pub fn at<T: Copy, const N: usize>(a: &[T; N], i: usize) -> (r: T)
    requires
        i < N,
    ensures
        r == a@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *a.get_unchecked(i) }
}

/// The symbols of a two-symbol table entry: `a`, then `b` if `n` is 2.
pub open spec fn pair(a: u8, b: u8, n: u8) -> Seq<u8> {
    if n == 1 {
        seq![a]
    } else {
        seq![a, b]
    }
}

/// `b` is `a` outside `[lo, hi)`.
#[verifier::opaque]
pub open spec fn kept(a: Seq<u8>, b: Seq<u8>, lo: int, hi: int) -> bool {
    &&& b.len() == a.len()
    &&& forall|j: int| 0 <= j < a.len() && !(lo <= j < hi) ==> #[trigger] b[j] == a[j]
}

/// Writing nothing keeps everything.
pub proof fn lemma_kept_refl(a: Seq<u8>, lo: int, hi: int)
    ensures
        kept(a, a, lo, hi),
{
    reveal(kept);
}

/// Grows `v` by `n` bytes (zeros; the spec leaves them unknown).
#[inline(always)]
pub fn grow(v: &mut Vec<u8>, n: usize)
    requires
        old(v)@.len() + n <= usize::MAX,
    ensures
        final(v)@.len() == old(v)@.len() + n,
        final(v)@.subrange(0, old(v)@.len() as int) == old(v)@,
{
    v.resize(v.len() + n, 0u8);
    proof {
        assert(v@.subrange(0, old(v)@.len() as int) =~= old(v)@);
    }
}

/// Writes `src[from..from + n]` at `v[at..at + n]`.
#[inline(always)]
pub fn put(v: &mut Vec<u8>, at: usize, src: &[u8], from: usize, n: usize)
    requires
        at + n <= old(v)@.len(),
        from + n <= src@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        kept(old(v)@, final(v)@, at as int, at + n),
        final(v)@.subrange(at as int, at + n) == src@.subrange(from as int, from + n),
{
    let vl = v.len();
    let sl = src.len();
    assert(at + n <= vl && from + n <= sl);
    v.as_mut_slice()[at..at + n].copy_from_slice(&src[from..from + n]);
    proof {
        reveal(kept);
        assert(v@.subrange(at as int, at + n) =~= src@.subrange(from as int, from + n));
    }
}

/// Writes four bytes at `at` with one store.
#[verifier::external_body]
#[inline(always)]
pub fn put4(v: &mut Vec<u8>, at: usize, a: [u8; 4])
    requires
        at + 4 <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        kept(old(v)@, final(v)@, at as int, at + 4),
        final(v)@.subrange(at as int, at + 4) == a@,
{
    // SAFETY: `at + 4 <= len`.
    unsafe {
        core::ptr::copy_nonoverlapping(a.as_ptr(), v.as_mut_ptr().add(at), 4);
    }
}

/// The symbols of four two-symbol entries.
pub open spec fn pairs4(e: [(u8, u8, u8); 4]) -> Seq<u8> {
    pair(e[0].0, e[0].1, e[0].2) + pair(e[1].0, e[1].1, e[1].2) + pair(e[2].0, e[2].1, e[2].2) + pair(
        e[3].0,
        e[3].1,
        e[3].2,
    )
}

/// Writes the symbols of four two-symbol entries at `at`, without
/// branches: every entry's two bytes are written, and the next entry goes
/// after its count. Any of the eight bytes from `at` may change.
#[verifier::external_body]
#[inline(always)]
pub fn put_pairs4(v: &mut Vec<u8>, at: usize, e: [(u8, u8, u8); 4])
    requires
        at + 8 <= old(v)@.len(),
        forall|k: int| 0 <= k < 4 ==> 1 <= #[trigger] e[k].2 <= 2,
    ensures
        final(v)@.len() == old(v)@.len(),
        kept(old(v)@, final(v)@, at as int, at + 8),
        final(v)@.subrange(at as int, at + pairs4(e).len()) == pairs4(e),
{
    // SAFETY: `at + 8 <= len`, and the writes stay below `at + 8`.
    unsafe {
        let p = v.as_mut_ptr().add(at);
        let mut k = 0usize;
        for j in 0..4 {
            *p.add(k) = e[j].0;
            *p.add(k + 1) = e[j].1;
            k += e[j].2 as usize;
        }
    }
}

/// Drops the first `cut` bytes of `v`, keeping its buffer (what
/// `drain(..cut)` does: a move down, then a shorter length).
#[inline(always)]
pub fn drop_front(v: &mut Vec<u8>, cut: usize)
    requires
        cut <= old(v)@.len(),
    ensures
        final(v)@ == old(v)@.subrange(cut as int, old(v)@.len() as int),
{
    let len = v.len();
    v.as_mut_slice().copy_within(cut..len, 0);
    v.truncate(len - cut);
    proof {
        assert(v@ =~= old(v)@.subrange(cut as int, old(v)@.len() as int));
    }
}

/// Appends `s[i..i + n]` to `v`.
#[verifier::external_body]
#[inline(always)]
pub fn extend_from(v: &mut Vec<u8>, s: &[u8], i: usize, n: usize)
    requires
        i + n <= s@.len(),
    ensures
        final(v)@ == old(v)@ + s@.subrange(i as int, i + n),
{
    let len = v.len();
    // Wild copy when the source has 16 bytes of slack after the range.
    if n <= 32 && s.len() - i >= 32 {
        v.reserve(32);
        unsafe {
            let p = v.as_mut_ptr();
            let q = s.as_ptr();
            core::ptr::copy_nonoverlapping(q.add(i), p.add(len), 16);
            core::ptr::copy_nonoverlapping(q.add(i + 16), p.add(len + 16), 16);
            v.set_len(len + n);
        }
    } else if n <= 64 && s.len() - i >= n + 16 {
        v.reserve(n + 16);
        unsafe {
            let p = v.as_mut_ptr();
            let q = s.as_ptr();
            let mut k = 0;
            while k < n {
                core::ptr::copy_nonoverlapping(q.add(i + k), p.add(len + k), 16);
                k += 16;
            }
            v.set_len(len + n);
        }
    } else {
        v.extend_from_slice(&s[i..i + n]);
    }
}

} // verus!
