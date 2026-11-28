//! Canonical Huffman codes (RFC 1951 §3.2.2, which WebP lossless and PNG
//! use too): the spec of decoding one symbol from code lengths, the proofs
//! that make lookup tables exact, and the exec pieces table builders share.
#[cfg(verus_only)]
use crate::bits::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// Longest code length DEFLATE allows.
pub spec const MAX_BITS: nat = 15;

/// Number of symbols among the first `n` whose code length is `l`.
pub open spec fn count_below(lens: Seq<u8>, l: nat, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_below(lens, l, n - 1) + if lens[n - 1] as nat == l {
            1nat
        } else {
            0nat
        }
    }
}

/// `bl_count[l]`: the number of symbols whose code length is `l`.
pub open spec fn count(lens: Seq<u8>, l: nat) -> nat {
    count_below(lens, l, lens.len() as int)
}

/// `next_code[l]` from step 2 of §3.2.2: the code of the first symbol (in
/// symbol order) whose code length is `l`. `bl_count[0]` is taken as 0.
pub open spec fn first_code(lens: Seq<u8>, l: nat) -> nat
    decreases l,
{
    if l <= 1 {
        0
    } else {
        2 * (first_code(lens, (l - 1) as nat) + count(lens, (l - 1) as nat))
    }
}

/// The symbol with the `r`-th smallest value (from 0) among symbols `from..`
/// whose code length is `l`, or -1 if there is none.
pub open spec fn nth_with_len(lens: Seq<u8>, l: nat, r: nat, from: int) -> int
    decreases lens.len() - from,
{
    if from < 0 || from >= lens.len() {
        -1
    } else if lens[from] as nat == l {
        if r == 0 {
            from
        } else {
            nth_with_len(lens, l, (r - 1) as nat, from + 1)
        }
    } else {
        nth_with_len(lens, l, r, from + 1)
    }
}

/// Step 3 of §3.2.2 assigns the symbols of length `l`, in symbol order, the
/// consecutive codes `first_code(l)`, `first_code(l) + 1`, ... So the code
/// `v` of length `l` belongs to a symbol iff it is in that range, and
/// decoding reads code bits until it is. Returns the symbol and the number of
/// bits its code takes, or `None` if no code matches within `MAX_BITS` bits
/// or the input ends first.
///
/// The codes of a valid set of lengths (`valid_lens`) are prefix-free, so
/// the shortest match is the only one.
pub open spec fn decode_from(lens: Seq<u8>, b: Seq<u8>, pos: int, l: nat) -> Option<(nat, nat)>
    decreases MAX_BITS + 1 - l,
{
    if l > MAX_BITS || pos + l > nbits(b) {
        None
    } else {
        let v = code_bits(b, pos, l);
        let f = first_code(lens, l);
        if f <= v && v < f + count(lens, l) {
            Some((nth_with_len(lens, l, (v - f) as nat, 0) as nat, l))
        } else {
            decode_from(lens, b, pos, l + 1)
        }
    }
}

/// Decodes one Huffman-coded symbol at bit `pos`.
pub open spec fn decode(lens: Seq<u8>, b: Seq<u8>, pos: int) -> Option<(nat, nat)> {
    decode_from(lens, b, pos, 1)
}

/// Codes of length `l` still unassigned once every length up to `l` is
/// assigned (Kraft's inequality): negative iff the lengths over-subscribe
/// the code space.
pub open spec fn left(lens: Seq<u8>, l: nat) -> int
    decreases l,
{
    if l == 0 {
        1
    } else {
        2 * left(lens, (l - 1) as nat) - count(lens, l)
    }
}

/// No symbol has a code.
pub open spec fn no_codes(lens: Seq<u8>) -> bool {
    forall|l: nat| 1 <= l <= MAX_BITS ==> #[trigger] count(lens, l) == 0
}

/// Exactly one symbol has a code, and it is one bit long.
pub open spec fn single_code(lens: Seq<u8>) -> bool {
    &&& count(lens, 1) == 1
    &&& forall|l: nat| 2 <= l <= MAX_BITS ==> #[trigger] count(lens, l) == 0
}

/// The number of symbols with a code (a nonzero code length).
pub open spec fn used(lens: Seq<u8>) -> nat {
    (lens.len() - count(lens, 0)) as nat
}

// ---------------------------------------------------------------------------
// Decoding from a number, and exact tables
// ---------------------------------------------------------------------------


/// The first `l` bits of `x` (first bit least significant), read as a code
/// (first bit most significant).
pub open spec fn rev(x: nat, l: nat) -> nat
    decreases l,
{
    if l == 0 {
        0
    } else {
        2 * rev(x, (l - 1) as nat) + (x / pow2((l - 1) as nat)) % 2
    }
}

/// `spec::decode_from`, reading the code bits from the number `x` of which
/// `avail` bits are known.
pub open spec fn decode_num(lens: Seq<u8>, x: nat, avail: nat, l: nat) -> Option<(nat, nat)>
    decreases MAX_BITS + 1 - l,
{
    if l > MAX_BITS || l > avail {
        None
    } else {
        let v = rev(x, l);
        let f = first_code(lens, l);
        if f <= v && v < f + count(lens, l) {
            Some((nth_with_len(lens, l, (v - f) as nat, 0) as nat, l))
        } else {
            decode_num(lens, x, avail, l + 1)
        }
    }
}

/// Some code of length `l` matches the first `l` bits of `x`.
pub open spec fn matches_at(lens: Seq<u8>, x: nat, l: nat) -> bool {
    let v = rev(x, l);
    first_code(lens, l) <= v && v < first_code(lens, l) + count(lens, l)
}

// ---------------------------------------------------------------------------
// rev
// ---------------------------------------------------------------------------

pub proof fn lemma_rev_bound(x: nat, l: nat)
    ensures
        rev(x, l) < pow2(l),
    decreases l,
{
    if l == 0 {
        lemma2_to64();
    } else {
        lemma_rev_bound(x, (l - 1) as nat);
        lemma_pow2_unfold(l);
    }
}

pub proof fn lemma_rev_unfold(y: nat, l: nat)
    requires
        l > 0,
    ensures
        rev(y, l) == 2 * rev(y, (l - 1) as nat) + (y / pow2((l - 1) as nat)) % 2,
{
}

/// Bit `j` of `x`, for `j < t`, is bit `j` of `x % 2^t`.
pub proof fn lemma_bit_of_mod(x: nat, j: nat, t: nat)
    requires
        j < t,
    ensures
        ((x % pow2(t)) / pow2(j)) % 2 == (x / pow2(j)) % 2,
{
    lemma_pow2_pos(j);
    lemma_pow2_pos(t);
    lemma_pow2_adds(j, (t - j) as nat);
    assert(j + (t - j) as nat == t);
    let a = pow2(j);
    let c = pow2((t - j) as nat);
    // x % (a * c) == a * ((x / a) % c) + x % a, so dividing by a leaves
    // (x / a) % c.
    lemma_breakdown(x as int, a as int, c as int);
    lemma_mod_bound(x as int, a as int);
    lemma_mod_bound((x / a) as int, c as int);
    lemma_mul_is_commutative(a as int, ((x / a) % c) as int);
    lemma_fundamental_div_mod_converse(
        (x % (a * c)) as int,
        a as int,
        ((x / a) % c) as int,
        (x % a) as int,
    );
    // (y % c) % 2 == y % 2 when 2 divides c
    lemma_pow2_unfold((t - j) as nat);
    let y = x / a;
    lemma_mod_mod(y as int, 2, pow2((t - j - 1) as nat) as int);
    lemma_mul_is_commutative(2, pow2((t - j - 1) as nat) as int);
}

/// `rev` reads only the low `l` bits.
pub proof fn lemma_rev_mod(x: nat, l: nat, t: nat)
    requires
        l <= t,
    ensures
        rev(x % pow2(t), l) == rev(x, l),
    decreases l,
{
    if l > 0 {
        let j = (l - 1) as nat;
        lemma_rev_mod(x, j, t);
        lemma_bit_of_mod(x, j, t);
        lemma_pow2_pos(t);
        let y: nat = x % pow2(t);
        lemma_rev_unfold(y, l);
        lemma_rev_unfold(x, l);
        assert(rev(y, j) == rev(x, j));
        assert((y / pow2(j)) % 2 == (x / pow2(j)) % 2);
        assert(rev(y, l) == rev(x, l));
        assert(rev(x % pow2(t), l) == rev(y, l));
    } else {
        lemma_pow2_pos(t);
    }
}

/// Bit `j` of `bits(b, p, k)` is bit `p + j` of the input.
pub proof fn lemma_bit_of_bits(b: Seq<u8>, p: int, k: nat, j: nat)
    requires
        j < k,
    ensures
        (bits(b, p, k) / pow2(j)) % 2 == bit(b, p + j),
{
    lemma_bits_divmod(b, p, j, k);
    let r = (k - j) as nat;
    assert(r >= 1);
    // bits(p + j, r) % 2 == bit(p + j)
    let rest = bits(b, p + j + 1, (r - 1) as nat);
    assert(bits(b, p + j, r) == bit(b, p + j) + 2 * rest);
    assert(bit(b, p + j) < 2);
    lemma_mod_multiples_vanish(rest as int, bit(b, p + j) as int, 2);
    lemma_small_mod(bit(b, p + j), 2);
}

/// Code bits from the input are code bits from the bit buffer.
pub proof fn lemma_code_bits_rev(b: Seq<u8>, p: int, k: nat, l: nat)
    requires
        l <= k,
    ensures
        code_bits(b, p, l) == rev(bits(b, p, k), l),
    decreases l,
{
    if l > 0 {
        lemma_code_bits_rev(b, p, k, (l - 1) as nat);
        lemma_bit_of_bits(b, p, k, (l - 1) as nat);
    }
}

// ---------------------------------------------------------------------------
// decode_num
// ---------------------------------------------------------------------------

/// Decoding from the input is decoding from the bit buffer, when the
/// buffer holds at least 15 bits or all that is left of the input.
pub proof fn lemma_decode_num(lens: Seq<u8>, b: Seq<u8>, pos: int, k: nat, avail: nat, l: nat)
    requires
        pos + k <= nbits(b),
        avail <= k,
        avail >= MAX_BITS || pos + avail == nbits(b),
        l >= 1,
    ensures
        decode_from(lens, b, pos, l) == decode_num(lens, bits(b, pos, k), avail, l),
    decreases MAX_BITS + 1 - l,
{
    if l <= MAX_BITS && l <= avail {
        lemma_code_bits_rev(b, pos, k, l);
        lemma_decode_num(lens, b, pos, k, avail, l + 1);
    }
}

/// A code found within the first `avail` bits is the code at `pos`,
/// however the stream continues.
pub proof fn lemma_decode_num_some(lens: Seq<u8>, b: Seq<u8>, pos: int, k: nat, avail: nat, l: nat)
    requires
        pos + k <= nbits(b),
        avail <= k,
        l >= 1,
        decode_num(lens, bits(b, pos, k), avail, l) is Some,
    ensures
        decode_from(lens, b, pos, l) == decode_num(lens, bits(b, pos, k), avail, l),
    decreases MAX_BITS + 1 - l,
{
    if l <= MAX_BITS && l <= avail {
        lemma_code_bits_rev(b, pos, k, l);
        let v = rev(bits(b, pos, k), l);
        let f = first_code(lens, l);
        if !(f <= v && v < f + count(lens, l)) {
            lemma_decode_num_some(lens, b, pos, k, avail, l + 1);
        }
    }
}

/// A decoded code is at least `l` bits long.
pub proof fn lemma_decode_num_len(lens: Seq<u8>, x: nat, avail: nat, l: nat)
    ensures
        decode_num(lens, x, avail, l) matches Some((s, k)) ==> l <= k <= avail && k <= MAX_BITS,
    decreases MAX_BITS + 1 - l,
{
    if l <= MAX_BITS && l <= avail {
        lemma_decode_num_len(lens, x, avail, l + 1);
    }
}

/// Decoding `x` and decoding its low `t` bits agree on every length up to
/// both `t` and `avail`.
pub proof fn lemma_decode_num_trunc(lens: Seq<u8>, x: nat, avail: nat, t: nat, l: nat)
    requires
        l >= 1,
    ensures
        decode_num(lens, x % pow2(t), t, l) matches Some((s, k)) ==> (if k <= avail {
            decode_num(lens, x, avail, l) == Some((s, k))
        } else {
            decode_num(lens, x, avail, l) is None
        }),
    decreases MAX_BITS + 1 - l,
{
    lemma_pow2_pos(t);
    if l <= MAX_BITS && l <= t {
        lemma_rev_mod(x, l, t);
        lemma_decode_num_trunc(lens, x, avail, t, l + 1);
        lemma_decode_num_len(lens, x % pow2(t), t, l + 1);
    }
}

// ---------------------------------------------------------------------------
// Code space arithmetic
// ---------------------------------------------------------------------------

/// The codes of length `l` start at `first_code(l)`, `count(l)` of them are
/// used, and `left(l)` remain.
pub proof fn lemma_code_space(lens: Seq<u8>, l: nat)
    requires
        l >= 1,
    ensures
        first_code(lens, l) + count(lens, l) + left(lens, l) == pow2(l),
    decreases l,
{
    lemma_pow2_unfold(l);
    if l == 1 {
        lemma2_to64();
        assert(left(lens, 0) == 1);
    } else {
        lemma_code_space(lens, (l - 1) as nat);
    }
}

/// When every length up to `l` leaves the code space non-negative, the
/// codes of length `l` fit in `l` bits.
pub proof fn lemma_codes_fit(lens: Seq<u8>, l: nat)
    requires
        l >= 1,
        left(lens, l) >= 0,
    ensures
        first_code(lens, l) + count(lens, l) <= pow2(l),
{
    lemma_code_space(lens, l);
}

/// No code shorter than `l` matches `x`, so its first `l` bits read as a
/// code are at least `first_code(l)`.
pub proof fn lemma_no_match_above(lens: Seq<u8>, x: nat, l: nat)
    requires
        l >= 1,
        forall|j: nat| 1 <= j < l ==> !#[trigger] matches_at(lens, x, j),
    ensures
        rev(x, l) >= first_code(lens, l),
    decreases l,
{
    if l > 1 {
        let j = (l - 1) as nat;
        lemma_no_match_above(lens, x, j);
        assert(!matches_at(lens, x, j));
    }
}

/// No code of at most `t` bits is a prefix of `x % 2^t`: decoding `x`
/// from length `l <= t + 1` is decoding it from length `t + 1`.
pub proof fn lemma_decode_num_skip(lens: Seq<u8>, x: nat, avail: nat, t: nat, l: nat)
    requires
        1 <= l <= t + 1,
        t <= avail,
        t <= MAX_BITS,
        decode_num(lens, x % pow2(t), t, l) is None,
    ensures
        decode_num(lens, x, avail, l) == decode_num(lens, x, avail, t + 1),
    decreases t + 1 - l,
{
    if l <= t {
        lemma_rev_mod(x, l, t);
        lemma_decode_num_step(lens, x % pow2(t), t, l);
        assert(!matches_at(lens, x % pow2(t), l));
        lemma_decode_num_skip(lens, x, avail, t, l + 1);
        assert(!matches_at(lens, x, l));
    }
}

/// One step of `decode_num`: a length that does not match is skipped.
pub proof fn lemma_decode_num_step(lens: Seq<u8>, y: nat, t: nat, l: nat)
    requires
        1 <= l <= t,
        t <= 15,
    ensures
        !matches_at(lens, y, l) ==> decode_num(lens, y, t, l) == decode_num(lens, y, t, l + 1),
        matches_at(lens, y, l) ==> decode_num(lens, y, t, l) is Some,
{
}

/// `decode_num` finds the first length that matches.
pub proof fn lemma_decode_num_first(lens: Seq<u8>, x: nat, avail: nat, l: nat, m: nat)
    requires
        1 <= l <= m,
        m <= MAX_BITS,
        m <= avail,
        forall|j: nat| l <= j < m ==> !#[trigger] matches_at(lens, x, j),
        matches_at(lens, x, m),
    ensures
        decode_num(lens, x, avail, l) == Some(
            (nth_with_len(lens, m, (rev(x, m) - first_code(lens, m)) as nat, 0) as nat, m),
        ),
    decreases m - l,
{
    if l < m {
        assert(!matches_at(lens, x, l));
        lemma_decode_num_first(lens, x, avail, l + 1, m);
    }
}

/// A complete code (no codes left at length `t`) decodes every `t`-bit
/// string: the codes of each length continue where the previous length's
/// end, and together they cover the whole code space.
pub proof fn lemma_complete_decodes(lens: Seq<u8>, x: nat, t: nat)
    requires
        1 <= t <= MAX_BITS,
        left(lens, t) == 0,
    ensures
        decode_num(lens, x, t, 1) is Some,
{
    if forall|j: nat| 1 <= j <= t ==> !#[trigger] matches_at(lens, x, j) {
        lemma_no_match_above(lens, x, t);
        assert(!matches_at(lens, x, t));
        lemma_code_space(lens, t);
        lemma_rev_bound(x, t);
        assert(false);
    } else {
        let m = choose|j: nat| 1 <= j <= t && #[trigger] matches_at(lens, x, j);
        lemma_first_match(lens, x, t, m);
    }
}

/// If some length up to `t` matches, the first one does, and `decode_num`
/// returns it.
proof fn lemma_first_match(lens: Seq<u8>, x: nat, t: nat, m: nat)
    requires
        1 <= m <= t <= MAX_BITS,
        matches_at(lens, x, m),
    ensures
        decode_num(lens, x, t, 1) is Some,
    decreases m,
{
    if exists|j: nat| 1 <= j < m && #[trigger] matches_at(lens, x, j) {
        let j = choose|j: nat| 1 <= j < m && #[trigger] matches_at(lens, x, j);
        lemma_first_match(lens, x, t, j);
    } else {
        lemma_decode_num_first(lens, x, t, 1, m);
    }
}


// ---------------------------------------------------------------------------
// rev is its own inverse on l-bit numbers
// ---------------------------------------------------------------------------

/// Bit `j` of `rev(x, l)` is bit `l - 1 - j` of `x`.
pub proof fn lemma_rev_bit(x: nat, l: nat, j: nat)
    requires
        j < l,
    ensures
        (rev(x, l) / pow2(j)) % 2 == (x / pow2((l - 1 - j) as nat)) % 2,
    decreases l,
{
    let k = (l - 1) as nat;
    lemma_rev_unfold(x, l);
    lemma_pow2_pos(k);
    let b = (x / pow2(k)) % 2;
    let r = rev(x, k);
    if j == 0 {
        lemma2_to64();
        lemma_mod_multiples_vanish(r as int, b as int, 2);
        lemma_small_mod(b, 2);
        assert(rev(x, l) == 2 * r + b);
        assert(pow2(0) == 1);
        assert(rev(x, l) / 1 == rev(x, l));
        assert(rev(x, l) / pow2(j) == rev(x, l));
        assert((l - 1 - j) as nat == k);
    } else {
        lemma_rev_bit(x, k, (j - 1) as nat);
        // (2r + b) / 2^j == r / 2^(j-1)
        lemma_pow2_unfold(j);
        lemma_pow2_pos((j - 1) as nat);
        lemma_fundamental_div_mod_converse((2 * r + b) as int, 2, r as int, b as int);
        lemma_div_denominator((2 * r + b) as int, 2, pow2((j - 1) as nat) as int);
        assert((k - 1 - (j - 1)) as nat == (l - 1 - j) as nat);
    }
}

/// Numbers below `2^l` with the same low `l` bits are equal.
pub proof fn lemma_bits_eq(a: nat, b: nat, l: nat)
    requires
        a < pow2(l),
        b < pow2(l),
        forall|j: nat| j < l ==> (#[trigger] (a / pow2(j)) % 2) == (b / pow2(j)) % 2,
    ensures
        a == b,
    decreases l,
{
    if l == 0 {
        lemma2_to64();
    } else {
        let k = (l - 1) as nat;
        lemma_pow2_unfold(l);
        lemma2_to64();
        assert((a / pow2(0)) % 2 == (b / pow2(0)) % 2);
        assert forall|j: nat| j < k implies (#[trigger] ((a / 2) / pow2(j)) % 2) == ((b / 2) / pow2(
            j,
        )) % 2 by {
            lemma_pow2_unfold(j + 1);
            lemma_pow2_pos(j);
            lemma_div_denominator(a as int, 2, pow2(j) as int);
            lemma_div_denominator(b as int, 2, pow2(j) as int);
            lemma_mul_is_commutative(2, pow2(j) as int);
            assert((a / pow2(j + 1)) % 2 == (b / pow2(j + 1)) % 2);
        }
        lemma_pow2_pos(k);
        lemma_div_by_multiple_is_strongly_ordered_helper(a, k);
        lemma_div_by_multiple_is_strongly_ordered_helper(b, k);
        lemma_bits_eq(a / 2, b / 2, k);
        lemma_fundamental_div_mod(a as int, 2);
        lemma_fundamental_div_mod(b as int, 2);
    }
}

proof fn lemma_div_by_multiple_is_strongly_ordered_helper(a: nat, k: nat)
    requires
        a < 2 * pow2(k),
    ensures
        a / 2 < pow2(k),
{
    lemma_pow2_pos(k);
    lemma_fundamental_div_mod(a as int, 2);
}

pub proof fn lemma_rev_rev(c: nat, l: nat)
    requires
        c < pow2(l),
    ensures
        rev(rev(c, l), l) == c,
{
    lemma_rev_bound(c, l);
    lemma_rev_bound(rev(c, l), l);
    assert forall|j: nat| j < l implies (#[trigger] (rev(rev(c, l), l) / pow2(j)) % 2) == (c / pow2(
        j,
    )) % 2 by {
        lemma_rev_bit(rev(c, l), l, j);
        lemma_rev_bit(c, l, (l - 1 - j) as nat);
        assert((l - 1 - (l - 1 - j) as nat) as nat == j);
    }
    lemma_bits_eq(rev(rev(c, l), l), c, l);
}

/// The numbers whose first `l` bits read as code `c` are those congruent
/// to `rev(c, l)` modulo `2^l`.
pub proof fn lemma_rev_iff(x: nat, c: nat, l: nat)
    requires
        c < pow2(l),
    ensures
        (rev(x, l) == c) == (x % pow2(l) == rev(c, l)),
{
    lemma_pow2_pos(l);
    lemma_rev_mod(x, l, l);
    let y = x % pow2(l);
    lemma_mod_bound(x as int, pow2(l) as int);
    lemma_rev_rev(c, l);
    if rev(x, l) == c {
        lemma_rev_rev(y, l);
    }
}

// ---------------------------------------------------------------------------
// Counting
// ---------------------------------------------------------------------------

pub proof fn lemma_count_below_mono(lens: Seq<u8>, l: nat, a: int, b: int)
    requires
        a <= b,
    ensures
        count_below(lens, l, a) <= count_below(lens, l, b),
    decreases b - a,
{
    if a < b {
        lemma_count_below_mono(lens, l, a, b - 1);
    }
}

/// The symbols of length `l` in order: `s` is the one with rank
/// `count_below(l, s)`.
pub proof fn lemma_nth_rank(lens: Seq<u8>, l: nat, s: int, from: int)
    requires
        0 <= from <= s < lens.len(),
        lens[s] as nat == l,
    ensures
        nth_with_len(lens, l, (count_below(lens, l, s) - count_below(lens, l, from)) as nat, from)
            == s,
    decreases s - from,
{
    lemma_count_below_mono(lens, l, from, s);
    if from < s {
        lemma_count_below_mono(lens, l, from + 1, s);
        lemma_nth_rank(lens, l, s, from + 1);
        assert(count_below(lens, l, from + 1) == count_below(lens, l, from) + if lens[from] as nat
            == l {
            1nat
        } else {
            0nat
        });
    }
}

/// Sum of `count_below(k, m)` over `k < l`.
pub open spec fn csum(lens: Seq<u8>, l: nat, m: int) -> nat
    decreases l,
{
    if l == 0 {
        0
    } else {
        csum(lens, (l - 1) as nat, m) + count_below(lens, (l - 1) as nat, m)
    }
}

proof fn lemma_csum_step(lens: Seq<u8>, l: nat, m: int)
    requires
        0 <= m < lens.len(),
    ensures
        csum(lens, l, m + 1) == csum(lens, l, m) + if (lens[m] as nat) < l {
            1nat
        } else {
            0nat
        },
    decreases l,
{
    if l > 0 {
        lemma_csum_step(lens, (l - 1) as nat, m);
    }
}

/// Every symbol has exactly one length.
pub proof fn lemma_csum_all(lens: Seq<u8>, m: int)
    requires
        0 <= m <= lens.len(),
        forall|i: int| 0 <= i < m ==> #[trigger] lens[i] as nat <= MAX_BITS,
    ensures
        csum(lens, MAX_BITS + 1, m) == m,
    decreases m,
{
    if m > 0 {
        lemma_csum_all(lens, m - 1);
        lemma_csum_step(lens, MAX_BITS + 1, m - 1);
    } else {
        lemma_csum_zero(lens, MAX_BITS + 1);
    }
}

proof fn lemma_csum_zero(lens: Seq<u8>, l: nat)
    ensures
        csum(lens, l, 0) == 0,
    decreases l,
{
    if l > 0 {
        lemma_csum_zero(lens, (l - 1) as nat);
    }
}

/// A complete code with no code longer than `t` is complete at `t`.
pub proof fn lemma_left_tail(lens: Seq<u8>, t: nat, l: nat)
    requires
        t <= l,
        forall|k: nat| t < k <= l ==> #[trigger] count(lens, k) == 0,
    ensures
        left(lens, l) == pow2((l - t) as nat) * left(lens, t),
    decreases l,
{
    if l == t {
        lemma2_to64();
        assert(pow2((l - t) as nat) == 1);
        assert(1 * left(lens, t) == left(lens, t));
    } else {
        lemma_left_tail(lens, t, (l - 1) as nat);
        lemma_pow2_unfold((l - t) as nat);
        assert(((l - 1) as nat - t) as nat == ((l - t) as nat - 1) as nat);
        let q = pow2(((l - t) as nat - 1) as nat) as int;
        assert(count(lens, l) == 0);
        assert(left(lens, l) == 2 * left(lens, (l - 1) as nat));
        assert(left(lens, (l - 1) as nat) == q * left(lens, t));
        assert(pow2((l - t) as nat) == 2 * q);
        lemma_mul_is_associative(2, q, left(lens, t));
        assert(left(lens, l) == (2 * q) * left(lens, t));
    }
}


pub proof fn lemma_count_below_le(lens: Seq<u8>, l: nat, m: int)
    requires
        0 <= m,
    ensures
        count_below(lens, l, m) <= m,
    decreases m,
{
    if m > 0 {
        lemma_count_below_le(lens, l, m - 1);
    }
}

pub proof fn lemma_csum_mono(lens: Seq<u8>, a: nat, b: nat, m: int)
    requires
        a <= b,
    ensures
        csum(lens, a, m) <= csum(lens, b, m),
    decreases b - a,
{
    if a < b {
        lemma_csum_mono(lens, a, (b - 1) as nat, m);
    }
}

/// How many symbols have a code, by the counts.
pub proof fn lemma_used(lens: Seq<u8>)
    requires
        forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] as nat <= MAX_BITS,
    ensures
        (lens.len() - count(lens, 0) == 0) == no_codes(lens),
        (lens.len() - count(lens, 0) == 1 && count(lens, 1) == 1) == single_code(lens),
{
    let n = lens.len() as int;
    lemma_csum_all(lens, n);
    reveal_with_fuel(csum, 17);
    assert(n == count(lens, 0) + count(lens, 1) + count(lens, 2) + count(lens, 3) + count(lens, 4)
        + count(lens, 5) + count(lens, 6) + count(lens, 7) + count(lens, 8) + count(lens, 9)
        + count(lens, 10) + count(lens, 11) + count(lens, 12) + count(lens, 13) + count(lens, 14)
        + count(lens, 15));
    if n - count(lens, 0) == 0 {
        assert forall|l: nat| 1 <= l <= MAX_BITS implies #[trigger] count(lens, l) == 0 by {
            assert(l == 1 || l == 2 || l == 3 || l == 4 || l == 5 || l == 6 || l == 7 || l == 8
                || l == 9 || l == 10 || l == 11 || l == 12 || l == 13 || l == 14 || l == 15);
        }
    }
    if no_codes(lens) {
        assert(count(lens, 1) == 0 && count(lens, 2) == 0 && count(lens, 3) == 0 && count(lens, 4)
            == 0 && count(lens, 5) == 0 && count(lens, 6) == 0 && count(lens, 7) == 0 && count(
            lens,
            8,
        ) == 0 && count(lens, 9) == 0 && count(lens, 10) == 0 && count(lens, 11) == 0 && count(
            lens,
            12,
        ) == 0 && count(lens, 13) == 0 && count(lens, 14) == 0 && count(lens, 15) == 0);
    }
    if n - count(lens, 0) == 1 && count(lens, 1) == 1 {
        assert forall|l: nat| 2 <= l <= MAX_BITS implies #[trigger] count(lens, l) == 0 by {
            assert(l == 2 || l == 3 || l == 4 || l == 5 || l == 6 || l == 7 || l == 8 || l == 9
                || l == 10 || l == 11 || l == 12 || l == 13 || l == 14 || l == 15);
        }
    }
    if single_code(lens) {
        assert(count(lens, 2) == 0 && count(lens, 3) == 0 && count(lens, 4) == 0 && count(lens, 5)
            == 0 && count(lens, 6) == 0 && count(lens, 7) == 0 && count(lens, 8) == 0 && count(
            lens,
            9,
        ) == 0 && count(lens, 10) == 0 && count(lens, 11) == 0 && count(lens, 12) == 0 && count(
            lens,
            13,
        ) == 0 && count(lens, 14) == 0 && count(lens, 15) == 0);
    }
}

/// Two numbers with the same residue less than `m` apart are equal.
pub proof fn lemma_same_residue(a: int, b: int, m: int)
    requires
        m > 0,
        a % m == b % m,
        a <= b < a + m,
    ensures
        a == b,
{
    lemma_fundamental_div_mod(a, m);
    lemma_fundamental_div_mod(b, m);
    let qa = a / m;
    let qb = b / m;
    assert(m * (qb - qa) == b - a) by (nonlinear_arith)
        requires
            a == m * qa + a % m,
            b == m * qb + b % m,
            a % m == b % m,
    ;
    if qb - qa >= 1 {
        lemma_mul_inequality(1, qb - qa, m);
        lemma_mul_is_commutative(m, qb - qa);
    }
    if qb - qa <= -1 {
        lemma_mul_inequality(qb - qa, -1, m);
        lemma_mul_is_commutative(m, qb - qa);
    }
}

/// Table entries filled for the codes of lengths `l + 1` to `t` in a
/// table of `2^t` entries: each code of length `k` fills `2^(t - k)`.
pub open spec fn fill_cost(lens: Seq<u8>, t: nat, l: nat) -> nat
    decreases t - l,
{
    if l >= t {
        0
    } else {
        fill_cost(lens, t, l + 1) + count(lens, l + 1) * pow2((t - (l + 1)) as nat)
    }
}

/// Kraft's equality, partially summed: the codes of lengths `l + 1` to `t`
/// and the unused codes at length `t` together fill the `2^(t - l)`
/// extensions of each code still unused at length `l`.
pub proof fn lemma_fill_cost(lens: Seq<u8>, t: nat, l: nat)
    requires
        l <= t,
    ensures
        fill_cost(lens, t, l) + left(lens, t) == pow2((t - l) as nat) * left(lens, l),
    decreases t - l,
{
    if l == t {
        lemma2_to64();
        assert(pow2(0) == 1);
        assert(1 * left(lens, l) == left(lens, l));
    } else {
        lemma_fill_cost(lens, t, l + 1);
        let q = pow2((t - (l + 1)) as nat) as int;
        lemma_pow2_unfold((t - l) as nat);
        assert(((t - l) as nat - 1) as nat == (t - (l + 1)) as nat);
        assert(pow2((t - l) as nat) == 2 * q);
        let c = count(lens, l + 1) as int;
        let a = left(lens, l);
        assert(left(lens, l + 1) == 2 * a - c);
        assert(q * (2 * a - c) + c * q == 2 * q * a) by (nonlinear_arith);
    }
}

/// The table entries filled for all codes of length at most `t` number at
/// most `2^t`.
pub proof fn lemma_fill_bound(lens: Seq<u8>, t: nat)
    requires
        left(lens, t) >= 0,
    ensures
        fill_cost(lens, t, 0) <= pow2(t),
{
    lemma_fill_cost(lens, t, 0);
    assert(pow2(t) * 1 == pow2(t));
}

// ---------------------------------------------------------------------------
// Exec
// ---------------------------------------------------------------------------

/// The low `l` bits of `c`, reversed.
pub fn reverse(c: u32, l: u32) -> (r: (u32, Ghost<nat>))
    requires
        l <= 15,
    ensures
        r.0 as nat == rev(c as nat, l as nat),
        r.1@ <= 15,
{
    let mut r: u32 = 0;
    let mut x = c;
    let mut i: u32 = 0;
    proof {
        lemma2_to64();
    }
    while i < l
        invariant
            i <= l <= 15,
            r as nat == rev(c as nat, i as nat),
            r < pow2(i as nat),
            x as nat == c as nat / pow2(i as nat),
        decreases l - i,
    {
        proof {
            lemma_pow2_pos(i as nat);
            lemma_pow2_unfold((i + 1) as nat);
            lemma_rev_unfold(c as nat, (i + 1) as nat);
            lemma_pow2_strictly_increases(i as nat, 31);
            lemma2_to64();
            assert(((r << 1u32) | (x & 1u32)) == 2 * r + x % 2) by (bit_vector)
                requires
                    r < 0x8000_0000u32,
            ;
            assert(x >> 1u32 == x / 2) by (bit_vector);
            lemma_div_denominator(c as int, pow2(i as nat) as int, 2);
        }
        r = (r << 1) | (x & 1);
        x = x >> 1;
        i = i + 1;
    }
    (r, Ghost(i as nat))
}





// --- fast reverse: begin
/// Every byte with its bits reversed.
pub const REV8: [u8; 256] = [
    0, 128, 64, 192, 32, 160, 96, 224, 16, 144, 80, 208, 48, 176, 112, 240,
    8, 136, 72, 200, 40, 168, 104, 232, 24, 152, 88, 216, 56, 184, 120, 248,
    4, 132, 68, 196, 36, 164, 100, 228, 20, 148, 84, 212, 52, 180, 116, 244,
    12, 140, 76, 204, 44, 172, 108, 236, 28, 156, 92, 220, 60, 188, 124, 252,
    2, 130, 66, 194, 34, 162, 98, 226, 18, 146, 82, 210, 50, 178, 114, 242,
    10, 138, 74, 202, 42, 170, 106, 234, 26, 154, 90, 218, 58, 186, 122, 250,
    6, 134, 70, 198, 38, 166, 102, 230, 22, 150, 86, 214, 54, 182, 118, 246,
    14, 142, 78, 206, 46, 174, 110, 238, 30, 158, 94, 222, 62, 190, 126, 254,
    1, 129, 65, 193, 33, 161, 97, 225, 17, 145, 81, 209, 49, 177, 113, 241,
    9, 137, 73, 201, 41, 169, 105, 233, 25, 153, 89, 217, 57, 185, 121, 249,
    5, 133, 69, 197, 37, 165, 101, 229, 21, 149, 85, 213, 53, 181, 117, 245,
    13, 141, 77, 205, 45, 173, 109, 237, 29, 157, 93, 221, 61, 189, 125, 253,
    3, 131, 67, 195, 35, 163, 99, 227, 19, 147, 83, 211, 51, 179, 115, 243,
    11, 139, 75, 203, 43, 171, 107, 235, 27, 155, 91, 219, 59, 187, 123, 251,
    7, 135, 71, 199, 39, 167, 103, 231, 23, 151, 87, 215, 55, 183, 119, 247,
    15, 143, 79, 207, 47, 175, 111, 239, 31, 159, 95, 223, 63, 191, 127, 255,
];

/// The bits of a byte reversed, written out.
pub open spec fn rev8c(x: int) -> int {
    (x % 2) * 128 + (x / 2 % 2) * 64 + (x / 4 % 2) * 32 + (x / 8 % 2) * 16 + (x / 16 % 2) * 8 + (x / 32 % 2) * 4 + (x
        / 64 % 2) * 2 + (x / 128 % 2)
}

/// `REV8` is right from entry `i` on, checked by evaluation.
pub open spec fn rev8_all(i: int) -> bool
    decreases 256 - i,
{
    if i >= 256 || i < 0 {
        true
    } else {
        REV8[i] as int == rev8c(i) && rev8_all(i + 1)
    }
}

proof fn lemma_rev8_all(k: int, i: int)
    requires
        0 <= k <= i < 256,
        rev8_all(k),
    ensures
        REV8[i] as int == rev8c(i),
    decreases i - k,
{
    if k < i {
        lemma_rev8_all(k + 1, i);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_rev8(i: int)
    requires
        0 <= i < 256,
    ensures
        REV8[i] as nat == rev(i as nat, 8),
{
    assert(rev8_all(0)) by (compute_only);
    lemma_rev8_all(0, i);
    lemma2_to64();
    reveal_with_fuel(rev, 9);
    let x = i as nat;
    assert(rev(x, 8) == rev8c(i));
}

/// Reversing `a + b` bits: the first `a` reversed, then the next `b`.
pub proof fn lemma_rev_split(x: nat, a: nat, b: nat)
    ensures
        rev(x, a + b) == rev(x, a) * pow2(b) + rev(x / pow2(a), b),
    decreases b,
{
    lemma_pow2_pos(a);
    if b == 0 {
        lemma2_to64();
        assert(pow2(0) == 1);
        assert(rev(x / pow2(a), 0) == 0);
        assert(a + b == a);
        assert(rev(x, a) * 1 == rev(x, a));
        assert(rev(x, a + b) == rev(x, a) * pow2(b) + rev(x / pow2(a), b));
    } else {
        let b1 = (b - 1) as nat;
        lemma_rev_split(x, a, b1);
        lemma_rev_unfold(x, a + b);
        lemma_rev_unfold(x / pow2(a), b);
        lemma_pow2_pos(b1);
        lemma_pow2_adds(a, b1);
        lemma_div_denominator(x as int, pow2(a) as int, pow2(b1) as int);
        lemma_pow2_unfold(b);
        assert((a + b - 1) as nat == a + b1);
        assert(2 * (rev(x, a) * pow2(b1)) == rev(x, a) * (2 * pow2(b1))) by (nonlinear_arith);
        let y = x / pow2(a);
        assert(y / pow2(b1) == x / pow2((a + b1) as nat));
        assert(rev(x, a + b) == 2 * rev(x, a + b1) + (x / pow2((a + b1) as nat)) % 2);
        assert(rev(y, b) == 2 * rev(y, b1) + (y / pow2(b1)) % 2);
        assert(rev(x, a + b1) == rev(x, a) * pow2(b1) + rev(y, b1));
        assert(pow2(b) == 2 * pow2(b1));
        assert(rev(x, a) * pow2(b) == 2 * (rev(x, a) * pow2(b1)));
        assert(rev(x, a + b) == rev(x, a) * pow2(b) + rev(x / pow2(a), b));
    }
}

/// No bits set, none in the reverse.
pub proof fn lemma_rev_zero(l: nat)
    ensures
        rev(0, l) == 0,
    decreases l,
{
    if l > 0 {
        lemma_rev_zero((l - 1) as nat);
        lemma_pow2_pos((l - 1) as nat);
    }
}

/// The low `l` bits of `c`, reversed, by table: `reverse` without the loop.
pub fn reverse_fast(c: u32, l: u32) -> (r: u32)
    requires
        1 <= l <= 15,
        c < pow2(l as nat),
    ensures
        r as nat == rev(c as nat, l as nat),
{
    let lo = (c & 0xff) as usize;
    let hi = ((c >> 8) & 0xff) as usize;
    assert(lo < 256 && hi < 256) by (bit_vector)
        requires
            lo == (c & 0xff),
            hi == ((c >> 8u32) & 0xff),
    ;
    let a = REV8[lo] as u32;
    let b = REV8[hi] as u32;
    proof {
        lemma2_to64();
        lemma_pow2_strictly_increases(l as nat, 16);
        assert(lo == c % 256 && hi == c / 256 && hi < 256) by (bit_vector)
            requires
                lo == (c & 0xff),
                hi == ((c >> 8u32) & 0xff),
                c < 0x10000,
        ;
        lemma_rev8(lo as int);
        lemma_rev8(hi as int);
        // rev(c, 16) from its two bytes.
        lemma_rev_split(c as nat, 8, 8);
        lemma_rev_mod(c as nat, 8, 8);
        assert(rev(c as nat, 16) == a * 256 + b);
        // rev(c, 16) is rev(c, l) followed by zeros.
        lemma_rev_split(c as nat, l as nat, (16 - l) as nat);
        lemma_pow2_pos(l as nat);
        lemma_basic_div(c as int, pow2(l as nat) as int);
        lemma_rev_zero((16 - l) as nat);
        lemma_rev_bound(c as nat, l as nat);
        let k = (16 - l) as u32;
        let v = rev(c as nat, l as nat);
        lemma_pow2_strictly_increases((16 - l) as nat, 16);
        assert(a * 256 + b == v * pow2((16 - l) as nat));
        assert(((a << 8u32) | b) == a * 256 + b) by (bit_vector)
            requires
                a < 256,
                b < 256,
        ;
        vstd::bits::lemma_u32_shr_is_div((a << 8u32) | b, k);
        lemma_div_multiples_vanish(v as int, pow2((16 - l) as nat) as int);
        assert((v * pow2((16 - l) as nat)) / pow2((16 - l) as nat) == v) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(v as int, pow2((16 - l) as nat) as int);
        }
    }
    ((a << 8) | b) >> (16 - l)
}
// --- fast reverse: end

/// The first symbol from `from` on with a code, or -1.
pub open spec fn first_used(lens: Seq<u8>, from: int) -> int
    decreases lens.len() - from,
{
    if from < 0 || from >= lens.len() {
        -1
    } else if lens[from] != 0 {
        from
    } else {
        first_used(lens, from + 1)
    }
}

/// Which code length sets are accepted. RFC 9649 §3.7.2.1 asks for a valid
/// prefix code and says a code with a single symbol takes zero bits.
/// libwebp (`BuildHuffmanTable`): at most 15 bits; exactly one symbol with
/// a code (of any length), or at least two forming a complete code (not
/// over-subscribed, and Kraft's sum exactly 1).
pub open spec fn valid_code(lens: Seq<u8>) -> bool {
    &&& forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] as nat <= MAX_BITS
    &&& (used(lens) == 1 || (used(lens) >= 2 && (forall|l: nat|
        1 <= l <= MAX_BITS ==> #[trigger] left(lens, l) >= 0) && left(lens, MAX_BITS) == 0))
}

} // verus!
