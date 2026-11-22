//! Reading backward bitstreams, and the arithmetic about bits the decoder
//! needs.
#[allow(unused_imports)]
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[allow(unused_imports)]
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
pub use verilith_core::bits::{lowmask, lemma_mask, lemma_and_mask};

verus! {

pub proof fn lemma_pow2_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
{
    if a < b {
        lemma_pow2_strictly_increases(a, b);
    }
}

/// `2^highbit(x) <= x < 2^(highbit(x) + 1)` for `x >= 1`.
pub proof fn lemma_highbit(x: nat)
    requires
        x >= 1,
    ensures
        pow2(highbit(x)) <= x < pow2(highbit(x) + 1),
    decreases x,
{
    if x <= 1 {
        lemma2_to64();
    } else {
        lemma_highbit(x / 2);
        lemma_pow2_unfold(highbit(x / 2) + 1);
        lemma_pow2_unfold(highbit(x / 2) + 2);
    }
}

/// `highbit` is the unique `h` with `2^h <= x < 2^(h+1)`.
pub proof fn lemma_highbit_unique(x: nat, h: nat)
    requires
        pow2(h) <= x < pow2(h + 1),
    ensures
        highbit(x) == h,
    decreases h,
{
    lemma_pow2_pos(h);
    if h == 0 {
        lemma2_to64();
    } else {
        lemma_pow2_unfold(h);
        lemma_pow2_unfold(h + 1);
        lemma_highbit_unique(x / 2, (h - 1) as nat);
    }
}

pub proof fn lemma_highbit_mono(x: nat, y: nat)
    requires
        1 <= x <= y,
    ensures
        highbit(x) <= highbit(y),
{
    lemma_highbit(x);
    lemma_highbit(y);
    if highbit(x) > highbit(y) {
        lemma_pow2_strictly_increases(highbit(y) + 1, highbit(x) + 0);
        if highbit(y) + 1 < highbit(x) {
            lemma_pow2_strictly_increases(highbit(y) + 1, highbit(x));
        }
    }
}

/// `highbit` of a number below `2^16`.
#[inline(always)]
pub fn highbit_u32(x: u32) -> (r: u32)
    requires
        x < 65536,
    ensures
        r as nat == highbit(x as nat),
        r < 16,
{
    let r = highbit32(x);
    proof {
        if r >= 16 {
            lemma_pow2_le(16, r as nat);
            assert(pow2(16) == 65536) by {
                lemma2_to64();
            }
        }
    }
    r
}

/// `highbit` of any `u32`, from its leading zeros.
#[inline(always)]
pub fn highbit32(x: u32) -> (r: u32)
    ensures
        r as nat == highbit(x as nat),
        r < 32,
        x >= 1 ==> pow2(r as nat) <= x < pow2(r as nat + 1),
{
    if x <= 1 {
        proof {
            lemma2_to64();
        }
        return 0;
    }
    let z = x.leading_zeros();
    proof {
        vstd::std_specs::bits::axiom_u32_leading_zeros(x);
    }
    let r = 31 - z;
    proof {
        assert(x >> r != 0u32) by {
            assert((x >> r) & 1u32 != 0u32);
            let y = x >> r;
            assert(y == 0u32 ==> y & 1u32 == 0u32) by (bit_vector);
        }
        lemma_u32_shr_is_div(x, r);
        lemma_pow2_pos(r as nat);
        if r + 1 < 32 {
            assert(x >> (r + 1) as u32 == 0);
            lemma_u32_shr_is_div(x, (r + 1) as u32);
            lemma_pow2_pos(r as nat + 1);
            if x as nat >= pow2(r as nat + 1) {
                vstd::arithmetic::div_mod::lemma_div_is_ordered(pow2(r as nat + 1) as int, x as int, pow2(r as nat + 1) as int);
                vstd::arithmetic::div_mod::lemma_div_by_self(pow2(r as nat + 1) as int);
            }
        } else {
            assert(pow2(32) == 0x1_0000_0000) by {
                lemma2_to64();
            }
        }
        if (x as nat) < pow2(r as nat) {
            vstd::arithmetic::div_mod::lemma_basic_div(x as int, pow2(r as nat) as int);
        }
        lemma_highbit_unique(x as nat, r as nat);
    }
    r
}

/// A backward stream's start: the number of useful bits.
pub fn bstart_exec(s: &[u8]) -> (r: Option<usize>)
    requires
        s@.len() < 0x1000_0000_0000_0000,
    ensures
        r is Some <==> bstart(s@) is Some,
        r is Some ==> r.unwrap() as int == bstart(s@).unwrap(),
        r is Some ==> r.unwrap() <= 8 * s@.len(),
{
    if s.len() == 0 {
        return None;
    }
    let last = s[s.len() - 1];
    if last == 0 {
        return None;
    }
    let h = highbit_u32(last as u32);
    proof {
        lemma_highbit(last as nat);
        if h >= 8 {
            lemma_pow2_le(8, h as nat);
            lemma2_to64();
        }
    }
    Some(8 * (s.len() - 1) + h as usize)
}

/// The `n` bits at `pos`, from the little-endian word at byte `i`.
pub proof fn lemma_word_bits(b: Seq<u8>, i: int, w: u64, sh: u64, n: u64)
    requires
        0 <= i,
        i + 8 <= b.len(),
        w as nat == le_word(b, i),
        sh < 8,
        n <= 56,
    ensures
        ((w >> sh) & lowmask(n)) as nat == bits(b, 8 * i + sh, n as nat),
{
    lemma_le_bytes_bits(b, i, 8);
    lemma_u64_shr_is_div(w, sh);
    lemma_bits_divmod(b, 8 * i, sh as nat, 64);
    assert(64 - sh as nat == (64 - sh) as nat);
    let x = w >> sh;
    lemma_and_mask(x, n);
    lemma_bits_divmod(b, 8 * i + sh, n as nat, (64 - sh) as nat);
}

/// `bits` reads the same from a sequence and its prefix.
pub proof fn lemma_bits_prefix(b: Seq<u8>, c: Seq<u8>, p: int, n: nat)
    requires
        0 <= p,
        p + n <= 8 * c.len(),
        c.len() <= b.len(),
        c == b.subrange(0, c.len() as int),
    ensures
        bits(b, p, n) == bits(c, p, n),
    decreases n,
{
    if n > 0 {
        assert(b[p / 8] == c[p / 8]);
        lemma_bits_prefix(b, c, p + 1, (n - 1) as nat);
    }
}

/// The little-endian value of the bytes `i..` of a short tail.
#[inline(always)]
pub fn load_tail(s: &[u8], i: usize) -> (r: u64)
    requires
        i < s@.len(),
        s@.len() - i <= 8,
    ensures
        r as nat == le_bytes(s@, i as int, (s@.len() - i) as nat),
{
    let n = s.len() - i;
    let mut r: u64 = 0;
    let mut k = n;
    proof {
        lemma2_to64();
    }
    // Horner's rule from the last byte down.
    while k > 0
        invariant
            k <= n,
            n == s@.len() - i,
            n <= 8,
            i + n == s@.len(),
            s@.len() <= usize::MAX,
            r as nat == le_bytes(s@, i + k, (n - k) as nat),
            (r as nat) < pow2((8 * (n - k)) as nat),
        decreases k,
    {
        let c = s[i + (k - 1)];
        proof {
            assert(le_bytes(s@, i + k - 1, (n - k + 1) as nat) == c as nat + 256 * le_bytes(
                s@,
                i + k,
                (n - k) as nat,
            ));
            lemma_pow2_adds(8, (8 * (n - k)) as nat);
            assert(pow2(8) == 256) by {
                lemma2_to64();
            }
            assert((8 * (n - k + 1)) as nat == 8 + (8 * (n - k)) as nat);
            assert(pow2((8 * (n - k)) as nat) <= pow2(56)) by {
                if 8 * (n - k) < 56 {
                    lemma_pow2_le((8 * (n - k)) as nat, 56);
                }
            }
            assert(pow2(56) == 0x100000000000000) by {
                lemma2_to64_rest();
            }
            lemma_u64_shl_is_mul(r, 8);
            assert(r * 256 + c < 0x10000000000000000);
            assert((r << 8u64) | (c as u64) == (r << 8u64) + c as u64) by (bit_vector)
                requires
                    c < 256,
            ;
        }
        r = (r << 8u64) | (c as u64);
        k = k - 1;
    }
    r
}

/// Reads the `n` bits at position `lo`.
#[inline(always)]
pub fn bits_at(s: &[u8], lo: usize, n: u32) -> (r: u64)
    requires
        lo + n <= 8 * s@.len(),
        n <= 56,
    ensures
        r as nat == bits(s@, lo as int, n as nat),
        r as nat <= pow2(n as nat) - 1,
{
    let i = lo / 8;
    let sh = (lo % 8) as u64;
    proof {
        lemma_bits_bound(s@, lo as int, n as nat);
    }
    if i + 8 <= s.len() {
        let w = load_u64_le(s, i);
        proof {
            lemma_word_bits(s@, i as int, w, sh, n as u64);
            lemma_mask(n as u64);
        }
        (w >> sh) & ((1u64 << n as u64) - 1)
    } else if n == 0 {
        proof {
            lemma2_to64();
        }
        0
    } else {
        // Fewer than 8 bytes from `i` on: pad them with zeros to a word.
        let w = load_tail(s, i);
        let ghost m = (s@.len() - i) as nat;
        let ghost t = s@ + Seq::new((8 - m) as nat, |k: int| 0u8);
        proof {
            assert(le_bytes(t, i as int, 8) == le_bytes(s@, i as int, m)) by {
                lemma_le_bytes_pad(s@, t, i as int, m, 8);
            }
            lemma_word_bits(t, i as int, w, sh, n as u64);
            assert(s@ =~= t.subrange(0, s@.len() as int));
            lemma_bits_prefix(t, s@, lo as int, n as nat);
            lemma_mask(n as u64);
        }
        (w >> sh) & ((1u64 << n as u64) - 1)
    }
}

/// The `k` bits at offset `a` of a field `w` holding the `n` bits at `lo`.
#[inline(always)]
pub fn field(w: u64, a: u32, k: u32, Ghost(s): Ghost<Seq<u8>>, Ghost(lo): Ghost<int>, Ghost(n): Ghost<nat>) -> (r: u64)
    requires
        w as nat == bits(s, lo, n),
        a + k <= n,
        n <= 56,
    ensures
        r as nat == bits(s, lo + a, k as nat),
        r as nat <= pow2(k as nat) - 1,
{
    proof {
        lemma_bits_divmod(s, lo, a as nat, n);
        lemma_bits_divmod(s, lo + a, k as nat, (n - a) as nat);
        lemma_u64_shr_is_div(w, a as u64);
        lemma_bits_bound(s, lo + a, k as nat);
    }
    let x = w >> a as u64;
    proof {
        lemma_and_mask(x, k as u64);
        lemma_mask(k as u64);
    }
    x & ((1u64 << k as u64) - 1)
}

/// The top `n - a` bits of a field `w` holding the `n` bits at `lo`: a
/// shift, with no mask.
#[inline(always)]
pub fn field_top(w: u64, a: u32, Ghost(s): Ghost<Seq<u8>>, Ghost(lo): Ghost<int>, Ghost(n): Ghost<nat>) -> (r: u64)
    requires
        w as nat == bits(s, lo, n),
        a <= n,
        n <= 56,
    ensures
        r as nat == bits(s, lo + a, (n - a) as nat),
        r as nat <= pow2((n - a) as nat) - 1,
{
    proof {
        lemma_bits_divmod(s, lo, a as nat, n);
        lemma_u64_shr_is_div(w, a as u64);
        lemma_bits_bound(s, lo + a, (n - a) as nat);
    }
    w >> a as u64
}

/// Reads the `n` bits just below position `p` of a backward stream.
#[inline(always)]
pub fn rd(s: &[u8], p: usize, n: u32) -> (r: u64)
    requires
        n <= p <= 8 * s@.len(),
        n <= 56,
    ensures
        r as nat == bits(s@, p - n, n as nat),
        r as nat <= pow2(n as nat) - 1,
{
    bits_at(s, p - n as usize, n)
}

/// A word whose low 56 bits are the 56 bits below `p`: one load, no mask
/// and no test for the end of the stream.
#[inline(always)]
pub fn word56(s: &[u8], p: usize) -> (w: u64)
    requires
        56 <= p < 8 * s@.len(),
    ensures
        (w & lowmask(56)) as nat == bits(s@, p - 56, 56),
{
    let lo = p - 56;
    let i = lo / 8;
    let sh = (lo % 8) as u64;
    let x = load_u64_le(s, i);
    proof {
        lemma_word_bits(s@, i as int, x, sh, 56);
    }
    x >> sh
}

/// The `k` bits at offset `a` of a word whose low 56 bits are the bits at
/// `lo` (`word56`).
#[inline(always)]
pub fn fld(w: u64, a: u32, k: u32, Ghost(s): Ghost<Seq<u8>>, Ghost(lo): Ghost<int>) -> (r: u64)
    requires
        (w & lowmask(56)) as nat == bits(s, lo, 56),
        a + k <= 56,
    ensures
        r as nat == bits(s, lo + a, k as nat),
        r as nat <= pow2(k as nat) - 1,
{
    let ghost w2 = w & lowmask(56);
    proof {
        lemma_bits_divmod(s, lo, a as nat, 56);
        lemma_bits_divmod(s, lo + a, k as nat, (56 - a) as nat);
        lemma_u64_shr_is_div(w2, a as u64);
        lemma_bits_bound(s, lo + a, k as nat);
    }
    let x = w >> a as u64;
    proof {
        let x2 = w2 >> a as u64;
        lemma_and_mask(x2, k as u64);
        lemma_mask(k as u64);
        let a64 = a as u64;
        let k64 = k as u64;
        assert(lowmask(56) == 0x00FF_FFFF_FFFF_FFFFu64) by (compute);
        assert((w >> a64) & (((1u64 << k64) - 1) as u64) == ((w & 0x00FF_FFFF_FFFF_FFFFu64) >> a64) & (((1u64 << k64) - 1) as u64))
            by (bit_vector)
            requires
                a64 + k64 <= 56,
        ;
    }
    x & ((1u64 << k as u64) - 1)
}

/// Zero bytes after the end add nothing to a little-endian number.
pub proof fn lemma_le_bytes_pad(s: Seq<u8>, t: Seq<u8>, i: int, m: nat, n: nat)
    requires
        0 <= i,
        i + m == s.len(),
        m <= n,
        i + n <= t.len(),
        forall|k: int| 0 <= k < s.len() ==> t[k] == s[k],
        forall|k: int| s.len() <= k < t.len() ==> t[k] == 0,
    ensures
        le_bytes(t, i, n) == le_bytes(s, i, m),
    decreases n,
{
    if n > 0 {
        if m > 0 {
            lemma_le_bytes_pad(s, t, i + 1, (m - 1) as nat, (n - 1) as nat);
        } else {
            lemma_le_bytes_zero(t, i, n);
        }
    }
}

pub proof fn lemma_le_bytes_zero(t: Seq<u8>, i: int, n: nat)
    requires
        0 <= i,
        i + n <= t.len(),
        forall|k: int| i <= k < i + n ==> t[k] == 0,
    ensures
        le_bytes(t, i, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_le_bytes_zero(t, i + 1, (n - 1) as nat);
    }
}

/// Peeks at the `n` bits below `p`, with zeros below bit 0.
#[inline(always)]
pub fn peek(s: &[u8], p: usize, n: u32) -> (r: u64)
    requires
        p <= 8 * s@.len(),
        n <= 56,
    ensures
        r as nat == bpeek(s@, p as int, n as nat),
        r as nat <= pow2(n as nat) - 1,
{
    if p >= n as usize {
        rd(s, p, n)
    } else if p == 0 {
        proof {
            lemma_pow2_pos(n as nat);
        }
        0
    } else {
        let v = rd(s, p, p as u32);
        let k = n - p as u32;
        proof {
            lemma_pow2_adds(p as nat, k as nat);
            lemma_mul_inequality(v as int, pow2(p as nat) - 1, pow2(k as nat) as int);
            lemma_pow2_pos(k as nat);
            assert((pow2(p as nat) - 1) * pow2(k as nat) == pow2(n as nat) - pow2(k as nat)) by {
                lemma_mul_is_distributive_sub_other_way(pow2(k as nat) as int, pow2(p as nat) as int, 1);
            }
            lemma_u64_pow2_no_overflow(n as nat);
            lemma_u64_shl_is_mul(v, k as u64);
        }
        v << k as u64
    }
}

} // verus!
