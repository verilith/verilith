//! Lemmas for the encoders: what a stream that starts with the written bits
//! reads, and canonical codes (from verilith-brotli's `elemmas` and
//! verilith-zlib's `dlemmas`).
#[cfg(verus_only)]
use crate::enc_bw::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// The first bits of `b` are `w`.
pub open spec fn ext(b: Seq<u8>, w: Seq<nat>) -> bool {
    &&& w.len() <= nbits(b)
    &&& forall|k: int| 0 <= k < w.len() ==> #[trigger] bit(b, k) == w[k]
}

/// A stream that starts with `w + u` starts with `w`.
pub proof fn lemma_ext_prefix(b: Seq<u8>, w: Seq<nat>, u: Seq<nat>)
    requires
        ext(b, w + u),
    ensures
        ext(b, w),
{
    assert forall|k: int| 0 <= k < w.len() implies #[trigger] bit(b, k) == w[k] by {
        assert((w + u)[k] == w[k]);
    }
}

/// Bits of `b` inside `w` are bits of `w`.
pub proof fn lemma_ext_bits(b: Seq<u8>, w: Seq<nat>, p: int, n: nat)
    requires
        ext(b, w),
        0 <= p,
        p + n <= w.len(),
    ensures
        bits(b, p, n) == wbits(w, p, n),
    decreases n,
{
    if n > 0 {
        lemma_ext_bits(b, w, p + 1, (n - 1) as nat);
    }
}

/// A field written as the `n` bits of `v` reads back as `v`.
pub proof fn lemma_field(b: Seq<u8>, w: Seq<nat>, v: nat, n: nat)
    requires
        ext(b, w + bits_of(v, n)),
        v < pow2(n),
    ensures
        rd(b, w.len() as int, n) == Some(v),
        bits_of(v, n).len() == n,
{
    let u = bits_of(v, n);
    lemma_bits_of(v, n);
    lemma_ext_bits(b, w + u, w.len() as int, n);
    lemma_wbits_suffix(w, u, 0, n);
    assert(w.len() + 0 == w.len());
    lemma_small_mod(v, pow2(n));
}

/// The finished output starts with its bits.
pub proof fn lemma_hold_ext(b: Seq<u8>, w: Seq<nat>)
    requires
        bytes_hold(b, w),
    ensures
        ext(b, w),
{
    assert forall|k: int| 0 <= k < w.len() implies #[trigger] bit(b, k) == w[k] by {
        lemma_written(b, w, k, 1);
        reveal_with_fuel(bits, 2);
        reveal_with_fuel(wbits, 2);
    }
}

/// Fields written one after another: `ext` of the whole gives `ext` of
/// each prefix.
pub proof fn lemma_ext2(b: Seq<u8>, w: Seq<nat>, x: Seq<nat>, y: Seq<nat>)
    requires
        ext(b, w + (x + y)),
    ensures
        ext(b, w + x),
        ext(b, (w + x) + y),
{
    assert(w + (x + y) =~= (w + x) + y);
    lemma_ext_prefix(b, w + x, y);
}

/// The bits of `v` in `n` bits, with `v` below `2^n`.
pub open spec fn fld(v: nat, n: nat) -> Seq<nat> {
    bits_of(v, n)
}

/// Reading a field at position `p` of `w + fld(v, n) + rest`.
pub proof fn lemma_rd(b: Seq<u8>, w: Seq<nat>, v: nat, n: nat, rest: Seq<nat>)
    requires
        ext(b, w + (fld(v, n) + rest)),
        v < pow2(n),
    ensures
        rd(b, w.len() as int, n) == Some(v),
        fld(v, n).len() == n,
{
    lemma_ext2(b, w, fld(v, n), rest);
    lemma_field(b, w, v, n);
}

pub proof fn lemma_pow2_small()
    ensures
        pow2(0) == 1,
        pow2(1) == 2,
        pow2(2) == 4,
        pow2(3) == 8,
        pow2(4) == 16,
        pow2(5) == 32,
        pow2(6) == 64,
        pow2(7) == 128,
        pow2(8) == 256,
        pow2(16) == 0x10000,
        pow2(20) == 0x100000,
        pow2(24) == 0x1000000,
{
    lemma2_to64();
}

/// The canonical code of symbol `s` (§3.2.2 step 3): the codes of length
/// `lens[s]` are handed out in symbol order from `first_code`.
pub open spec fn canon(lens: Seq<u8>, s: int) -> nat {
    first_code(lens, lens[s] as nat) + count_below(lens, lens[s] as nat, s)
}

/// The first `j` bits of a code are its top `j` bits.
pub proof fn lemma_rev_prefix(x: nat, j: nat, m: nat)
    requires
        j <= m,
    ensures
        rev(x, j) == rev(x, m) / pow2((m - j) as nat),
    decreases m - j,
{
    if j == m {
        lemma2_to64();
        assert((m - j) as nat == 0);
    } else {
        lemma_rev_prefix(x, j, (m - 1) as nat);
        lemma_rev_unfold(x, m);
        let r = rev(x, (m - 1) as nat);
        let b = (x / pow2((m - 1) as nat)) % 2;
        lemma_fundamental_div_mod_converse((2 * r + b) as int, 2, r as int, b as int);
        let k = (m - 1 - j) as nat;
        lemma_pow2_pos(k);
        lemma_div_denominator(rev(x, m) as int, 2, pow2(k) as int);
        lemma_pow2_unfold((m - j) as nat);
        assert((m - j) as nat - 1 == k);
    }
}

/// Codes of length `m` start above every code of a shorter length `j`,
/// extended to `m` bits: canonical codes are prefix-free.
pub proof fn lemma_first_code_grows(lens: Seq<u8>, j: nat, m: nat)
    requires
        1 <= j < m,
    ensures
        first_code(lens, m) >= pow2((m - j) as nat) * (first_code(lens, j) + count(lens, j)),
    decreases m - j,
{
    let k = (m - 1) as nat;
    assert(first_code(lens, m) == 2 * (first_code(lens, k) + count(lens, k)));
    lemma_pow2_unfold((m - j) as nat);
    if j == k {
        lemma_pow2_unfold(1);
        lemma2_to64();
        assert((m - j) as nat == 1);
    } else {
        lemma_first_code_grows(lens, j, k);
        let q = pow2((k - j) as nat);
        let v = first_code(lens, j) + count(lens, j);
        assert((m - j) as nat - 1 == (k - j) as nat);
        assert(first_code(lens, k) >= q * v);
        assert(2 * (first_code(lens, k) + count(lens, k)) >= (2 * q) * v) by (nonlinear_arith)
            requires
                first_code(lens, k) >= q * v,
        ;
    }
}

/// The bits of a symbol's canonical code decode, under `spec::decode`, to
/// that symbol. Only the lengths up to the symbol's need to fit the code
/// space.
pub proof fn lemma_encode(lens: Seq<u8>, s: int, b: Seq<u8>, pos: int)
    requires
        0 <= s < lens.len(),
        1 <= lens[s] <= MAX_BITS,
        forall|l: nat| 1 <= l <= MAX_BITS ==> #[trigger] left(lens, l) >= 0,
        0 <= pos,
        pos + lens[s] <= nbits(b),
        bits(b, pos, lens[s] as nat) == rev(canon(lens, s), lens[s] as nat),
    ensures
        decode(lens, b, pos) == Some((s as nat, lens[s] as nat)),
{
    let m = lens[s] as nat;
    let c = canon(lens, s);
    let f = first_code(lens, m);
    let x = bits(b, pos, m);
    // The code is in range for length m, and is s's.
    lemma_count_below_mono(lens, m, s + 1, lens.len() as int);
    assert(count_below(lens, m, s + 1) == count_below(lens, m, s) + 1);
    assert(c < f + count(lens, m));
    lemma_codes_fit(lens, m);
    lemma_rev_bound(c, m);
    lemma_bits_bound(b, pos, m);
    lemma_small_mod(x, pow2(m));
    lemma_rev_iff(x, c, m);
    assert(rev(x, m) == c);
    assert(matches_at(lens, x, m));
    lemma_nth_rank(lens, m, s, 0);
    assert(count_below(lens, m, 0) == 0);
    // No shorter code is a prefix of it.
    assert forall|j: nat| 1 <= j < m implies !#[trigger] matches_at(lens, x, j) by {
        lemma_rev_prefix(x, j, m);
        lemma_first_code_grows(lens, j, m);
        let q = pow2((m - j) as nat);
        let v = first_code(lens, j) + count(lens, j);
        lemma_pow2_pos((m - j) as nat);
        lemma_div_is_ordered((q * v) as int, c as int, q as int);
        lemma_mul_is_commutative(q as int, v as int);
        lemma_div_multiples_vanish(v as int, q as int);
    }
    lemma_decode_num_first(lens, x, m, 1, m);
    lemma_decode_num_some(lens, b, pos, m, m, 1);
}

} // verus!
