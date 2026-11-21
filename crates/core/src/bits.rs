//! Bit strings packed least significant bit first, the order DEFLATE,
//! WebP lossless and PNG use: the spec of a bit reader, and the arithmetic
//! that proofs about one need.
#[cfg(verus_only)]
use crate::prims::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/// Number of bits in the input.
pub open spec fn nbits(b: Seq<u8>) -> int {
    (8 * b.len()) as int
}

/// Bit `k` of the input: bits are numbered from the least significant bit
/// of byte 0.
pub open spec fn bit(b: Seq<u8>, k: int) -> nat {
    ((b[k / 8] as nat) / pow2((k % 8) as nat)) % 2
}

/// The `n` bits at `pos` as a number, first bit least significant. This is
/// how every DEFLATE field is packed except Huffman codes.
pub open spec fn bits(b: Seq<u8>, pos: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        bit(b, pos) + 2 * bits(b, pos + 1, (n - 1) as nat)
    }
}

/// The `n` bits at `pos` as a number, first bit most significant. This is
/// how Huffman codes are packed.
pub open spec fn code_bits(b: Seq<u8>, pos: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        2 * code_bits(b, pos, (n - 1) as nat) + bit(b, pos + n - 1)
    }
}



pub proof fn lemma_bits_bound(b: Seq<u8>, p: int, n: nat)
    ensures
        bits(b, p, n) < pow2(n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_bits_bound(b, p + 1, (n - 1) as nat);
        lemma_pow2_unfold(n);
        assert(bit(b, p) <= 1);
    }
}

/// Splitting a field: the first `m` bits, then the next `n`.
pub proof fn lemma_bits_split(b: Seq<u8>, p: int, m: nat, n: nat)
    ensures
        bits(b, p, m + n) == bits(b, p, m) + pow2(m) * bits(b, p + m, n),
    decreases m,
{
    if m == 0 {
        lemma2_to64();
        assert(m + n == n);
    } else {
        lemma_bits_split(b, p + 1, (m - 1) as nat, n);
        assert((m - 1) as nat + n == (m + n - 1) as nat);
        assert(p + 1 + (m - 1) as nat == p + m);
        let x = bits(b, p + 1, (m - 1) as nat);
        let y = bits(b, p + m, n);
        let q = pow2((m - 1) as nat);
        lemma_pow2_unfold(m);
        assert(bits(b, p, m + n) == bit(b, p) + 2 * (x + q * y));
        assert(bits(b, p, m) == bit(b, p) + 2 * x);
        assert(2 * (x + q * y) == 2 * x + (2 * q) * y) by (nonlinear_arith);
    }
}

/// The first `m` of `n` bits, and the rest, by arithmetic.
pub proof fn lemma_bits_divmod(b: Seq<u8>, p: int, m: nat, n: nat)
    requires
        m <= n,
    ensures
        bits(b, p, n) % pow2(m) == bits(b, p, m),
        bits(b, p, n) / pow2(m) == bits(b, p + m, (n - m) as nat),
{
    lemma_bits_split(b, p, m, (n - m) as nat);
    assert(m + (n - m) as nat == n);
    lemma_bits_bound(b, p, m);
    lemma_pow2_pos(m);
    let lo = bits(b, p, m);
    let hi = bits(b, p + m, (n - m) as nat);
    assert(bits(b, p, n) == hi * pow2(m) + lo) by {
        lemma_mul_is_commutative(hi as int, pow2(m) as int);
    }
    lemma_fundamental_div_mod_converse(
        bits(b, p, n) as int,
        pow2(m) as int,
        hi as int,
        lo as int,
    );
}

/// The `n` bits at bit `j` of byte `i`, for `j + n <= 8`.
pub proof fn lemma_bits_in_byte(b: Seq<u8>, i: int, j: nat, n: nat)
    requires
        0 <= i < b.len(),
        j + n <= 8,
    ensures
        bits(b, 8 * i + j, n) == (b[i] as nat / pow2(j)) % pow2(n),
    decreases n,
{
    lemma_pow2_pos(j);
    lemma_pow2_pos(n);
    let y = b[i] as nat / pow2(j);
    if n == 0 {
        lemma2_to64();
    } else {
        let k = 8 * i + j;
        assert(k / 8 == i && k % 8 == j as int) by {
            lemma_fundamental_div_mod_converse(k, 8, i, j as int);
        }
        assert(bit(b, k) == y % 2);
        lemma_bits_in_byte(b, i, j + 1, (n - 1) as nat);
        assert(8 * i + (j + 1) == k + 1);
        assert(b[i] as nat / pow2(j + 1) == y / 2) by {
            lemma_pow2_unfold(j + 1);
            lemma_div_denominator(b[i] as int, pow2(j) as int, 2);
        }
        lemma_pow2_unfold(n);
        lemma_pow2_pos((n - 1) as nat);
        // y % (2 * 2^(n-1)) == 2 * ((y / 2) % 2^(n-1)) + y % 2
        lemma_breakdown(y as int, 2, pow2((n - 1) as nat) as int);
    }
}

pub proof fn lemma_bits_byte(b: Seq<u8>, i: int)
    requires
        0 <= i < b.len(),
    ensures
        bits(b, 8 * i, 8) == b[i] as nat,
{
    lemma_bits_in_byte(b, i, 0, 8);
    lemma2_to64();
    assert(8 * i + 0 == 8 * i);
}

/// Little-endian bytes are the same bits.
pub proof fn lemma_le_bytes_bits(b: Seq<u8>, i: int, n: nat)
    requires
        0 <= i,
        i + n <= b.len(),
    ensures
        le_bytes(b, i, n) == bits(b, 8 * i, 8 * n),
    decreases n,
{
    if n > 0 {
        lemma_le_bytes_bits(b, i + 1, (n - 1) as nat);
        lemma_bits_split(b, 8 * i, 8, (8 * (n - 1)) as nat);
        assert(8 + (8 * (n - 1)) as nat == 8 * n);
        assert(8 * i + 8 == 8 * (i + 1));
        lemma_bits_byte(b, i);
        lemma2_to64();
    }
}

// Masks and shifts on `u64` words, as bit readers use them: `lowmask(n)`
// is the low `n` bits, and the lemmas connect `&`, `>>` and `|` on words to
// `%`, `/` and `+` on their values and to `bits`. These were copied in
// vbrotli, vwebp, vzlib and vzstd; they live here once.

/// The low `n` bits set, as the decoder computes it.
pub open spec fn lowmask(n: u64) -> u64 {
    ((1u64 << n) - 1) as u64
}

/// `(1 << n) - 1` is the mask of the low `n` bits.
pub proof fn lemma_mask(n: u64)
    requires
        n < 64,
    ensures
        lowmask(n) as nat == pow2(n as nat) - 1,
        (1u64 << n) as nat == pow2(n as nat),
{
    lemma_u64_pow2_no_overflow(n as nat);
    lemma_u64_shl_is_mul(1, n);
    lemma_pow2_pos(n as nat);
}

/// Masking with the low `n` bits is `% 2^n`.
pub proof fn lemma_and_mask(x: u64, n: u64)
    requires
        n < 64,
    ensures
        (x & lowmask(n)) as nat == x as nat % pow2(n as nat),
{
    lemma_mask(n);
    lemma_u64_low_bits_mask_is_mod(x, n as nat);
    lemma_u64_pow2_no_overflow(n as nat);
    assert(lowmask(n) == low_bits_mask(n as nat) as u64);
}

/// Shifting the buffer right by `n` drops the first `n` bits.
pub proof fn lemma_shr_bits(b: Seq<u8>, p: int, k: nat, x: u64, n: u64)
    requires
        x as nat == bits(b, p, k),
        n <= k,
        n < 64,
    ensures
        (x >> n) as nat == bits(b, p + n, (k - n) as nat),
        (x & lowmask(n)) as nat == bits(b, p, n as nat),
{
    lemma_u64_shr_is_div(x, n);
    lemma_bits_divmod(b, p, n as nat, k);
    lemma_and_mask(x, n);
}

/// Adding a byte above the buffered bits.
pub proof fn lemma_or_byte(x: u64, y: u64, c: u64)
    requires
        c <= 56,
        x < pow2(c as nat),
        y < 256,
    ensures
        (x | (y << c)) as nat == x as nat + pow2(c as nat) * y as nat,
        ((x | (y << c)) as nat) < pow2((c + 8) as nat),
{
    lemma_pow2_adds(c as nat, 8);
    lemma2_to64();
    lemma_pow2_pos(c as nat);
    lemma_mul_inequality(y as int, 255, pow2(c as nat) as int);
    if c + 8 < 64 {
        lemma_pow2_strictly_increases((c + 8) as nat, 64);
    }
    lemma_mul_is_commutative(y as int, pow2(c as nat) as int);
    lemma_u64_shl_is_mul(y, c);
    lemma_mask(c);
    assert(x < (1u64 << c));
    assert((x | (y << c)) == x + (y << c)) by (bit_vector)
        requires
            x < (1u64 << c),
            c <= 56,
            y < 256,
    ;
}

} // verus!
