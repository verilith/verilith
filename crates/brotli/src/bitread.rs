//! Reading bits of the input. The decoder sees the stream `b` through a
//! window `src`, the bytes `b[base..base + src.len()]`, and reads at
//! absolute bit positions. Every read is proven to return `spec::bits` of
//! the whole stream, or to report that the window ends first.
use crate::huffman::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
use verilith_core::prims::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;
#[cfg(verus_only)]
pub use verilith_core::bits::{lowmask, lemma_mask, lemma_and_mask, lemma_shr_bits, lemma_or_byte};

verus! {

/// Inputs larger than this are not supported (positions are counted in
/// bits in a `u64`).
pub const MAX_INPUT: u64 = 0x1000_0000_0000_0000;

/// `src` is the window of `b` starting at byte `base`.
pub open spec fn src_ok(src: Seq<u8>, base: int, b: Seq<u8>) -> bool {
    &&& 0 <= base
    &&& base + src.len() <= b.len()
    &&& b.len() <= MAX_INPUT
    &&& src == b.subrange(base, base + src.len())
}

/// The bit position where the window ends.
pub open spec fn lim(src: Seq<u8>, base: int) -> int {
    8 * (base + src.len())
}

/// The window reaches the end of the stream.
pub open spec fn full(src: Seq<u8>, base: int, b: Seq<u8>) -> bool {
    base + src.len() == b.len()
}

/// The bits of the window are the bits of the stream.
pub proof fn lemma_window_bits(src: Seq<u8>, base: int, b: Seq<u8>, p: int, n: nat)
    requires
        src_ok(src, base, b),
        8 * base <= p,
        p + n <= lim(src, base),
    ensures
        bits(src, p - 8 * base, n) == bits(b, p, n),
    decreases n,
{
    if n > 0 {
        lemma_window_bits(src, base, b, p + 1, (n - 1) as nat);
        let q = p - 8 * base;
        assert(q / 8 + base == p / 8 && q % 8 == p % 8) by {
            lemma_fundamental_div_mod(q, 8);
            lemma_mod_bound(q, 8);
            lemma_fundamental_div_mod_converse(p, 8, base + q / 8, q % 8);
        }
        assert(src[q / 8] == b[p / 8]);
        assert(bit(src, q) == bit(b, p));
        assert(q + 1 == (p + 1) - 8 * base);
    }
}

/// Up to 56 bits at `pos`: returns them and how many there are (56, or
/// all that is left of the window).
pub fn peek(src: &[u8], base: u64, pos: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: (u64, u64))
    requires
        src_ok(src@, base as int, b),
        8 * base <= pos <= lim(src@, base as int),
    ensures
        r.1 <= 56,
        r.1 == 56 || pos + r.1 == lim(src@, base as int),
        pos + r.1 <= lim(src@, base as int),
        r.0 as nat == bits(b, pos as int, r.1 as nat),
        r.0 < pow2(r.1 as nat),
{
    let ghost sv = src@;
    let rel = pos - 8 * base;
    assert(rel / 8 <= src@.len()) by {
        lemma_div_is_ordered(rel as int, 8 * src@.len() as int, 8);
        lemma_div_multiples_vanish(src@.len() as int, 8);
    }
    let i = (rel / 8) as usize;
    let sh = rel % 8;
    proof {
        lemma_fundamental_div_mod(rel as int, 8);
        lemma2_to64();
    }
    if src.len() - i >= 8 {
        let w = load_u64_le(src, i);
        proof {
            lemma_le_bytes_bits(sv, i as int, 8);
            lemma_shr_bits(sv, 8 * i, 64, w, sh);
            assert(8 * i + sh == rel);
            lemma_bits_divmod(sv, rel as int, 56, (64 - sh) as nat);
        }
        let x = (w >> sh) & 0x00ff_ffff_ffff_ffff;
        proof {
            assert(0x00ff_ffff_ffff_ffffu64 == lowmask(56)) by (compute);
            lemma_and_mask(w >> sh, 56);
            lemma_window_bits(sv, base as int, b, pos as int, 56);
            lemma_bits_bound(b, pos as int, 56);
        }
        (x, 56)
    } else {
        let mut w: u64 = 0;
        let mut k: usize = 0;
        let n = src.len() - i;
        assert(i + n == sv.len());
        while k < n
            invariant
                sv == src@,
                n == sv.len() - i,
                i + n == sv.len(),
                sv.len() <= usize::MAX,
                n < 8,
                k <= n,
                w as nat == le_bytes(sv, i as int, k as nat),
                (w as nat) < pow2((8 * k) as nat),
            decreases n - k,
        {
            let byte = get(src, i + k) as u64;
            proof {
                lemma_le_bytes_split(sv, i as int, k as nat);
                lemma_or_byte(w, byte, (8 * k) as u64);
            }
            w = w | (byte << ((8 * k) as u64));
            k = k + 1;
        }
        proof {
            lemma_le_bytes_bits(sv, i as int, n as nat);
            lemma_shr_bits(sv, 8 * i, (8 * n) as nat, w, sh);
            assert(8 * i + sh == rel);
            lemma_window_bits(sv, base as int, b, pos as int, (8 * n - sh) as nat);
            lemma_bits_bound(b, pos as int, (8 * n - sh) as nat);
        }
        (w >> sh, (8 * n) as u64 - sh)
    }
}

/// `le_bytes` with one more byte on top.
pub proof fn lemma_le_bytes_split(b: Seq<u8>, i: int, k: nat)
    ensures
        le_bytes(b, i, k + 1) == le_bytes(b, i, k) + pow2(8 * k) * b[i + k] as nat,
    decreases k,
{
    lemma2_to64();
    assert(le_bytes(b, i, k + 1) == b[i] as nat + 256 * le_bytes(b, i + 1, k));
    if k == 0 {
        assert(le_bytes(b, i + 1, 0) == 0);
        assert(le_bytes(b, i, 0) == 0);
        assert(pow2(8 * k) == 1);
        assert(b[i + k] == b[i]);
        assert(pow2(8 * k) * (b[i + k] as nat) == b[i] as nat) by (nonlinear_arith)
            requires
                pow2(8 * k) == 1,
                b[i + k] == b[i],
        ;
    } else {
        lemma_le_bytes_split(b, i + 1, (k - 1) as nat);
        assert((k - 1) as nat + 1 == k);
        assert(i + 1 + (k - 1) == i + k);
        assert(le_bytes(b, i, k) == b[i] as nat + 256 * le_bytes(b, i + 1, (k - 1) as nat));
        lemma_pow2_adds(8, (8 * (k - 1)) as nat);
        assert(8 + 8 * (k - 1) == 8 * k);
        let t = le_bytes(b, i + 1, (k - 1) as nat);
        let c = b[i + k] as nat;
        let p = pow2((8 * (k - 1)) as nat);
        assert(pow2(8 * k) == 256 * p);
        assert(le_bytes(b, i + 1, k) == t + p * c);
        assert(256 * (t + p * c) == 256 * t + (256 * p) * c) by (nonlinear_arith);
        assert(le_bytes(b, i, k + 1) == b[i] as nat + 256 * t + pow2(8 * k) * c);
        assert(le_bytes(b, i, k + 1) == le_bytes(b, i, k) + pow2(8 * k) * b[i + k] as nat);
    }
}

/// `spec::rd`: `n <= 32` bits at `pos`, or `None` if the window ends first.
pub fn read_bits(src: &[u8], base: u64, pos: u64, n: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<u64>)
    requires
        src_ok(src@, base as int, b),
        8 * base <= pos <= lim(src@, base as int),
        n <= 32,
    ensures
        r matches Some(v) ==> rd(b, pos as int, n as nat) == Some(v as int) && v < pow2(n as nat)
            && pos + n <= lim(src@, base as int),
        r is None ==> pos + n > lim(src@, base as int),
        r is None && full(src@, base as int, b) ==> rd(b, pos as int, n as nat) is None,
{
    let (x, c) = peek(src, base, pos, Ghost(b));
    if n > c {
        return None;
    }
    proof {
        lemma_mask(n);
        lemma_shr_bits(b, pos as int, c as nat, x, n);
        lemma_bits_bound(b, pos as int, n as nat);
    }
    Some(x & ((1u64 << n) - 1))
}

/// Two reads in a row, `n1` then `n2` bits, from one `peek`.
#[inline(always)]
pub fn read_two(src: &[u8], base: u64, pos: u64, n1: u64, n2: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Option<(u64, u64)>)
    requires
        src_ok(src@, base as int, b),
        8 * base <= pos <= lim(src@, base as int),
        n1 <= 24,
        n2 <= 24,
    ensures
        r matches Some((v1, v2)) ==> rd(b, pos as int, n1 as nat) == Some(v1 as int) && v1 < pow2(n1 as nat)
            && rd(b, pos + n1, n2 as nat) == Some(v2 as int) && v2 < pow2(n2 as nat)
            && pos + n1 + n2 <= lim(src@, base as int),
        r is None ==> pos + n1 + n2 > lim(src@, base as int),
        r is None && full(src@, base as int, b) ==> rd(b, pos as int, n1 as nat) is None || rd(b, pos + n1, n2 as nat) is None,
{
    let (x, c) = peek(src, base, pos, Ghost(b));
    if n1 + n2 > c {
        return None;
    }
    let y = x >> n1;
    proof {
        lemma_mask(n1);
        lemma_mask(n2);
        lemma_shr_bits(b, pos as int, c as nat, x, n1);
        lemma_shr_bits(b, pos + n1, (c - n1) as nat, y, n2);
        lemma_bits_bound(b, pos as int, n1 as nat);
        lemma_bits_bound(b, pos + n1, n2 as nat);
    }
    Some((x & ((1u64 << n1) - 1), y & ((1u64 << n2) - 1)))
}

} // verus!
