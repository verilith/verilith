//! Proofs the decoder builds on: the bit buffer as a window on the input,
//! the fields of table entries, and facts about the spec's block decoding.
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use crate::huffman::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use crate::spec::*;
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

// ---------------------------------------------------------------------------
// The bit buffer
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Symbol tables
// ---------------------------------------------------------------------------

pub proof fn lemma_tables()
    ensures
        forall|i: int| 0 <= i < 29 ==> #[trigger] LEN_EXTRA@[i] as nat == len_extra()[i] && LEN_EXTRA@[i] <= 5,
        forall|i: int| 0 <= i < 29 ==> #[trigger] LEN_BASE@[i] as nat == len_base()[i] && LEN_BASE@[i] <= 258,
        forall|i: int| 0 <= i < 30 ==> #[trigger] DIST_EXTRA@[i] as nat == dist_extra()[i] && DIST_EXTRA@[i] <= 13,
        forall|i: int| 0 <= i < 30 ==> #[trigger] DIST_BASE@[i] as nat == dist_base()[i] && DIST_BASE@[i] <= 24577,
        forall|i: int| 0 <= i < 30 ==> #[trigger] dist_base()[i] >= 1,
        forall|i: int| 0 <= i < 29 ==> #[trigger] len_base()[i] >= 3,
        len_extra().len() == 29,
        len_base().len() == 29,
        dist_extra().len() == 30,
        dist_base().len() == 30,
{
    assert(forall|i: int| 0 <= i < 29 ==> #[trigger] LEN_EXTRA@[i] as nat == len_extra()[i] && LEN_EXTRA@[i] <= 5) by (compute);
    assert(forall|i: int| 0 <= i < 29 ==> #[trigger] LEN_BASE@[i] as nat == len_base()[i] && LEN_BASE@[i] <= 258) by (compute);
    assert(forall|i: int| 0 <= i < 30 ==> #[trigger] DIST_EXTRA@[i] as nat == dist_extra()[i] && DIST_EXTRA@[i] <= 13) by (compute);
    assert(forall|i: int| 0 <= i < 30 ==> #[trigger] DIST_BASE@[i] as nat == dist_base()[i] && DIST_BASE@[i] <= 24577) by (compute);
    assert(forall|i: int| 0 <= i < 30 ==> #[trigger] dist_base()[i] >= 1) by (compute);
    assert(forall|i: int| 0 <= i < 29 ==> #[trigger] len_base()[i] >= 3) by (compute);
}

// ---------------------------------------------------------------------------
// Table entries
// ---------------------------------------------------------------------------

/// The flags of symbol `s`'s entry.
pub open spec fn exc_of(alpha: u8, s: nat) -> bool {
    if alpha == ALPHA_LIT {
        s == 256 || s > 285
    } else if alpha == ALPHA_DIST {
        s >= 30
    } else {
        false
    }
}

/// The extra bits that follow symbol `s`'s code.
pub open spec fn extra_of(alpha: u8, s: nat) -> nat {
    if alpha == ALPHA_LIT && 257 <= s <= 285 {
        len_extra()[s - 257]
    } else if alpha == ALPHA_DIST && s < 30 {
        dist_extra()[s as int]
    } else {
        0
    }
}

/// The value field of symbol `s`'s entry: the literal, base length or
/// distance, or code length symbol.
pub open spec fn val_of(alpha: u8, s: nat) -> nat {
    if alpha == ALPHA_LIT {
        if s < 256 {
            s
        } else if 257 <= s <= 285 {
            len_base()[s - 257]
        } else {
            0
        }
    } else if alpha == ALPHA_DIST {
        if s < 30 {
            dist_base()[s as int]
        } else {
            0
        }
    } else {
        s
    }
}

proof fn lemma_mk_bv(flags: u32, len: u32, extra: u32, value: u32)
    requires
        len <= 15,
        extra <= 13,
        value < 0x8000,
        flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ensures
        (flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0xff == len + extra,
        ((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) >> 8u32) & 0x1f == len,
        ((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) >> 16u32) & 0x7fff
            == value,
        ((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0x8000_0000 != 0)
            == (flags == 0x8000_0000),
        ((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0x8000 != 0) == (
        flags == 0x8000 || flags == 0xC000),
        ((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0x4000 != 0) == (
        flags == 0xC000),
        (flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0x2000 == 0,
        (((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) >> 16u32) as u8)
            == value as u8,
        flags == 0 ==> (flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) >> 16u32
            == value,
{
    assert((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0xff == len + extra)
        by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ;
    assert(((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) >> 8u32) & 0x1f
        == len) by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ;
    assert(((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) >> 16u32) & 0x7fff
        == value) by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            value < 0x8000,
            flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ;
    assert(((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0x8000_0000 != 0)
        == (flags == 0x8000_0000)) by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            value < 0x8000,
            flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ;
    assert(((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0x8000 != 0) == (
    flags == 0x8000 || flags == 0xC000)) by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ;
    assert(((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0x4000 != 0) == (
    flags == 0xC000)) by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ;
    assert((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) & 0x2000 == 0)
        by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ;
    assert((((flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)) >> 16u32) as u8)
        == value as u8) by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            flags == 0 || flags == 0x8000_0000 || flags == 0x8000 || flags == 0xC000,
    ;
    assert(flags == 0 ==> (flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32))
        >> 16u32 == value) by (bit_vector)
        requires
            len <= 15,
            extra <= 13,
            value < 0x8000,
    ;
}

/// The fields of a table entry.
pub proof fn lemma_ent(alpha: u8, s: nat, l: nat)
    requires
        l <= 15,
        alpha == ALPHA_LIT || alpha == ALPHA_DIST || alpha == ALPHA_CL,
        alpha == ALPHA_CL ==> s < 0x8000,
    ensures
        ent(alpha, s, l) & 0xff == l + extra_of(alpha, s),
        (ent(alpha, s, l) >> 8u32) & 0x1f == l,
        (ent(alpha, s, l) >> 16u32) & 0x7fff == val_of(alpha, s),
        (ent(alpha, s, l) & F_LIT != 0) == (alpha == ALPHA_LIT && s < 256),
        (ent(alpha, s, l) & F_EXC != 0) == exc_of(alpha, s),
        (ent(alpha, s, l) & F_EOB != 0) == (alpha == ALPHA_LIT && s == 256),
        ent(alpha, s, l) & F_LONG == 0,
        alpha == ALPHA_LIT && s < 256 ==> ((ent(alpha, s, l) >> 16u32) as u8) == s as u8,
        alpha == ALPHA_CL ==> ent(alpha, s, l) >> 16u32 == s,
        extra_of(alpha, s) <= 13,
        val_of(alpha, s) < 0x8000,
{
    lemma_tables();
    lemma_flags();
    let lu = l as u32;
    if alpha == ALPHA_LIT {
        if s < 256 {
            lemma_mk_bv(F_LIT, lu, 0, s as u32);
            assert((s as u32) as u8 == s as u8);
        } else if s == 256 {
            lemma_mk_bv(F_EXC | F_EOB, lu, 0, 0);
        } else if s <= 285 {
            let i = s - 257;
            assert(LEN_EXTRA@[i] as nat == len_extra()[i]);
            assert(LEN_BASE@[i] as nat == len_base()[i]);
            lemma_mk_bv(0, lu, LEN_EXTRA@[i] as u32, LEN_BASE@[i] as u32);
        } else {
            lemma_mk_bv(F_EXC, lu, 0, 0);
        }
    } else if alpha == ALPHA_DIST {
        if s < 30 {
            assert(DIST_EXTRA@[s as int] as nat == dist_extra()[s as int]);
            assert(DIST_BASE@[s as int] as nat == dist_base()[s as int]);
            lemma_mk_bv(0, lu, DIST_EXTRA@[s as int] as u32, DIST_BASE@[s as int] as u32);
        } else {
            lemma_mk_bv(F_EXC, lu, 0, 0);
        }
    } else {
        lemma_mk_bv(0, lu, 0, s as u32);
    }
}

pub proof fn lemma_flags()
    ensures
        F_LIT == 0x8000_0000,
        F_EXC == 0x8000,
        F_EOB == 0x4000,
        F_LONG == 0x2000,
        F_EXC | F_EOB == 0xC000,
        LONG == 0xA000,
{
    assert(F_LIT == 0x8000_0000) by (compute);
    assert(F_EXC == 0x8000) by (compute);
    assert(F_EOB == 0x4000) by (compute);
    assert(F_LONG == 0x2000) by (compute);
    assert(F_EXC | F_EOB == 0xC000) by (compute);
    assert(LONG == 0xA000) by (compute);
}

pub proof fn lemma_long()
    ensures
        LONG & F_LONG != 0,
        LONG & F_LIT == 0,
        LONG & F_EXC != 0,
        LONG & F_EOB == 0,
{
    assert(LONG & F_LONG != 0) by (compute);
    assert(LONG & F_LIT == 0) by (compute);
    assert(LONG & F_EXC != 0) by (compute);
    assert(LONG & F_EOB == 0) by (compute);
}

pub proof fn lemma_div_pow2_bound(a: nat, t: nat, c: nat)
    requires
        a < pow2(t),
        c <= t,
    ensures
        a / pow2(c) < pow2((t - c) as nat),
{
    lemma_pow2_pos(c);
    lemma_pow2_adds(c, (t - c) as nat);
    assert(c + (t - c) as nat == t);
    let p = pow2(c) as int;
    let m = pow2((t - c) as nat) as int;
    let q = (a / pow2(c)) as int;
    lemma_fundamental_div_mod(a as int, p);
    lemma_mod_bound(a as int, p);
    if q >= m {
        lemma_mul_inequality(m, q, p);
        lemma_mul_is_commutative(m, p);
        lemma_mul_is_commutative(q, p);
    }
}

/// The extra bits of an entry, from the bits saved before its code.
pub proof fn lemma_value_bits(b: Seq<u8>, p: int, a: nat, saved: nat, tot: nat, cl: nat)
    requires
        saved == bits(b, p, a),
        cl <= tot <= a,
    ensures
        (saved % pow2(tot)) / pow2(cl) == bits(b, p + cl, (tot - cl) as nat),
{
    lemma_bits_divmod(b, p, tot, a);
    lemma_bits_divmod(b, p, cl, tot);
}

/// Where the `r`-th symbol of length `l` is.
pub proof fn lemma_nth_bound(lens: Seq<u8>, l: nat, r: nat, from: int)
    requires
        0 <= from <= lens.len(),
        r + count_below(lens, l, from) < count_below(lens, l, lens.len() as int),
    ensures
        from <= nth_with_len(lens, l, r, from) < lens.len(),
    decreases lens.len() - from,
{
    verilith_core::huffman::lemma_count_below_mono(lens, l, from, lens.len() as int);
    if from < lens.len() {
        assert(count_below(lens, l, from + 1) == count_below(lens, l, from) + if lens[from] as nat
            == l {
            1nat
        } else {
            0nat
        });
        if lens[from] as nat == l && r == 0 {
        } else if lens[from] as nat == l {
            lemma_nth_bound(lens, l, (r - 1) as nat, from + 1);
        } else {
            lemma_nth_bound(lens, l, r, from + 1);
        }
    }
}

/// A decoded symbol is one of the alphabet's.
pub proof fn lemma_decode_num_sym(lens: Seq<u8>, x: nat, avail: nat, l: nat)
    ensures
        decode_num(lens, x, avail, l) matches Some((s, k)) ==> s < lens.len() && l <= k <= avail
            && k <= 15,
    decreases 16 - l,
{
    verilith_core::huffman::lemma_decode_num_len(lens, x, avail, l);
    if l <= 15 && l <= avail {
        let v = rev(x, l);
        let f = first_code(lens, l);
        if f <= v && v < f + count(lens, l) {
            assert(count_below(lens, l, 0) == 0);
            lemma_nth_bound(lens, l, (v - f) as nat, 0);
        } else {
            lemma_decode_num_sym(lens, x, avail, l + 1);
        }
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// The fixed code
// ---------------------------------------------------------------------------

/// Counting over a run of equal lengths.
pub proof fn lemma_count_run(lens: Seq<u8>, l: nat, c: u8, a: int, n: int)
    requires
        0 <= a <= n <= lens.len(),
        forall|i: int| a <= i < n ==> #[trigger] lens[i] == c,
    ensures
        count_below(lens, l, n) == count_below(lens, l, a) + if c as nat == l {
            (n - a) as nat
        } else {
            0nat
        },
    decreases n - a,
{
    if n > a {
        lemma_count_run(lens, l, c, a, n - 1);
    }
}

pub proof fn lemma_fixed_counts(l: nat)
    ensures
        count(fixed_lit_lens(), l) == if l == 7 {
            24nat
        } else if l == 8 {
            152nat
        } else if l == 9 {
            112nat
        } else {
            0nat
        },
        count(fixed_dist_lens(), l) == if l == 5 {
            32nat
        } else {
            0nat
        },
{
    let fl = fixed_lit_lens();
    let fd = fixed_dist_lens();
    assert(count_below(fl, l, 0) == 0);
    lemma_count_run(fl, l, 8, 0, 144);
    lemma_count_run(fl, l, 9, 144, 256);
    lemma_count_run(fl, l, 7, 256, 280);
    lemma_count_run(fl, l, 8, 280, 288);
    assert(count_below(fd, l, 0) == 0);
    lemma_count_run(fd, l, 5, 0, 32);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn lemma_fixed_valid()
    ensures
        valid_lens(fixed_lit_lens(), true),
        valid_lens(fixed_dist_lens(), true),
        fixed_lit_lens().len() == 288,
        fixed_dist_lens().len() == 32,
{
    let fl = fixed_lit_lens();
    let fd = fixed_dist_lens();
    assert forall|l: nat| 1 <= l <= 15 implies #[trigger] left(fl, l) >= 0 && left(fd, l) >= 0
        && (l == 15 ==> left(fl, l) == 0 && left(fd, l) == 0) by {
        lemma_fixed_counts(1);
        lemma_fixed_counts(2);
        lemma_fixed_counts(3);
        lemma_fixed_counts(4);
        lemma_fixed_counts(5);
        lemma_fixed_counts(6);
        lemma_fixed_counts(7);
        lemma_fixed_counts(8);
        lemma_fixed_counts(9);
        lemma_fixed_counts(10);
        lemma_fixed_counts(11);
        lemma_fixed_counts(12);
        lemma_fixed_counts(13);
        lemma_fixed_counts(14);
        lemma_fixed_counts(15);
        reveal_with_fuel(left, 16);
    }
    assert(left(fl, 15) == 0);
    assert(left(fd, 15) == 0);
    assert forall|l: nat| 1 <= l <= 15 implies #[trigger] left(fd, l) >= 0 by {
        assert(left(fl, l) >= 0 && left(fd, l) >= 0);
    }
    assert forall|i: int| 0 <= i < fd.len() implies #[trigger] fd[i] as nat <= MAX_BITS by {}
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

/// Decoding a symbol stays within the input.
pub proof fn lemma_decode_from_end(lens: Seq<u8>, b: Seq<u8>, pos: int, l: nat)
    ensures
        decode_from(lens, b, pos, l) matches Some((s, k)) ==> pos + k <= nbits(b) && l <= k <= 15,
    decreases 16 - l,
{
    if !(l > 15 || pos + l > nbits(b)) {
        lemma_decode_from_end(lens, b, pos, l + 1);
    }
}

/// A compressed block ends after it starts, within the input, and adds
/// at most 129 bytes of output per bit.
pub proof fn lemma_codes_end(b: Seq<u8>, pos: int, out: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>)
    ensures
        inflate_codes(b, pos, out, lit, dist) matches Some((p, o)) ==> pos < p <= nbits(b) && out.len()
            <= o.len() <= out.len() + 129 * (p - pos),
    decreases nbits(b) - pos,
{
    match decode(lit, b, pos) {
        None => {},
        Some((sym, l)) => {
            let p1 = pos + l;
            if !advances(b, pos, p1) {
            } else if sym < 256 {
                lemma_codes_end(b, p1, out.push(sym as u8), lit, dist);
            } else if sym == 256 {
            } else if sym > 285 {
            } else {
                let le = len_extra()[sym - 257];
                let len = len_base()[sym - 257] + bits(b, p1, le);
                let p2 = p1 + le;
                if p2 <= nbits(b) {
                    lemma_decode_from_end(dist, b, p2, 1);
                    match decode(dist, b, p2) {
                        None => {},
                        Some((ds, dl)) => {
                            let p3 = p2 + dl;
                            if ds < 30 {
                                let de = dist_extra()[ds as int];
                                let d = dist_base()[ds as int] + bits(b, p3, de);
                                let p4 = p3 + de;
                                if advances(b, pos, p4) && d <= out.len() {
                                    lemma_tables();
                                    lemma_bits_bound(b, p1, le);
                                    lemma2_to64();
                                    assert(len <= 258) by {
                                        assert(sym - 257 < 29);
                                        assert(le == len_extra()[sym - 257]);
                                        if le == 0 {
                                        } else if le == 1 {
                                        } else if le == 2 {
                                        } else if le == 3 {
                                        } else if le == 4 {
                                        } else {
                                            assert(le == 5);
                                        }
                                        assert(len_base()[sym - 257] + pow2(le) - 1 <= 258) by {
                                            reveal_with_fuel(len_base, 1);
                                            assert(forall|i: int|
                                                0 <= i < 29 ==> #[trigger] len_base()[i] + pow2(
                                                    len_extra()[i],
                                                ) - 1 <= 258) by (compute);
                                        }
                                    }
                                    lemma_decode_from_end(lit, b, pos, 1);
                                    lemma_copy_match_len(out, d, len);
                                    lemma_codes_end(b, p4, copy_match(out, d, len), lit, dist);
                                }
                            }
                        },
                    }
                }
            }
        },
    }
}

pub proof fn lemma_copy_match_len(out: Seq<u8>, d: nat, len: nat)
    ensures
        copy_match(out, d, len).len() == out.len() + len,
    decreases len,
{
    if len > 0 {
        lemma_copy_match_len(out.push(out[out.len() - d]), d, (len - 1) as nat);
    }
}

// ---------------------------------------------------------------------------
// Decoding in steps
// ---------------------------------------------------------------------------

/// What follows a block that ended at `p` with output `o` (`r`): nothing
/// if it was the final block, the next block otherwise.
#[verifier::opaque]
pub open spec fn after(b: Seq<u8>, last: bool, r: Option<(int, Seq<u8>)>) -> Option<(int, Seq<u8>)> {
    match r {
        None => None,
        Some((p, o)) => if last {
            Some((p, o))
        } else {
            inflate_blocks(b, p, o)
        },
    }
}

/// The block whose 3 header bits are at `pos`, as `inflate_blocks` decodes
/// it.
#[verifier::opaque]
pub open spec fn block(b: Seq<u8>, pos: int, out: Seq<u8>) -> Option<(int, Seq<u8>)> {
    let btype = bits(b, pos + 1, 2);
    let p = pos + 3;
    if btype == 0 {
        inflate_stored(b, p, out)
    } else if btype == 1 {
        inflate_codes(b, p, out, fixed_lit_lens(), fixed_dist_lens())
    } else if btype == 2 {
        match read_dynamic(b, p) {
            None => None,
            Some((p2, lit, dist)) => inflate_codes(b, p2, out, lit, dist),
        }
    } else {
        None
    }
}

pub proof fn lemma_block_cases(b: Seq<u8>, pos: int, out: Seq<u8>)
    ensures
        bits(b, pos + 1, 2) == 0 ==> block(b, pos, out) == inflate_stored(b, pos + 3, out),
        bits(b, pos + 1, 2) == 1 ==> block(b, pos, out) == inflate_codes(
            b,
            pos + 3,
            out,
            fixed_lit_lens(),
            fixed_dist_lens(),
        ),
        bits(b, pos + 1, 2) == 2 ==> block(b, pos, out) == match read_dynamic(b, pos + 3) {
            None => None,
            Some((p2, lit, dist)) => inflate_codes(b, p2, out, lit, dist),
        },
        bits(b, pos + 1, 2) == 3 ==> block(b, pos, out) is None,
{
    reveal(block);
}

pub proof fn lemma_after_none(b: Seq<u8>, last: bool)
    ensures
        after(b, last, None) is None,
{
    reveal(after);
}

/// The rest of a stored block: `n` bytes from the byte at `pos`.
pub open spec fn stored_rest(b: Seq<u8>, pos: int, n: nat, out: Seq<u8>) -> Option<(int, Seq<u8>)> {
    let i = pos / 8;
    if i + n > b.len() {
        None
    } else {
        Some((8 * (i + n), out + b.subrange(i, i + n)))
    }
}

pub proof fn lemma_read_lens_end(cl: Seq<u8>, b: Seq<u8>, pos: int, lens: Seq<u8>, total: nat)
    requires
        lens.len() <= total,
    ensures
        read_lens(cl, b, pos, lens, total) matches Some((p, l)) ==> p >= pos && l.len() == total
            && l.subrange(0, lens.len() as int) == lens,
    decreases total - lens.len(),
{
    if lens.len() < total {
        lemma_decode_from_end(cl, b, pos, 1);
        match decode(cl, b, pos) {
            None => {},
            Some((sym, l)) => {
                let p1 = pos + l;
                if sym < 16 {
                    let l2 = lens.push(sym as u8);
                    lemma_read_lens_end(cl, b, p1, l2, total);
                    if let Some((p, lf)) = read_lens(cl, b, pos, lens, total) {
                        assert(lf.subrange(0, l2.len() as int) == l2);
                        assert(lf.subrange(0, lens.len() as int) =~= l2.subrange(0, lens.len() as int));
                        assert(l2.subrange(0, lens.len() as int) =~= lens);
                    }
                } else if sym == 16 && lens.len() == 0 {
                } else {
                    let e: nat = if sym == 16 {
                        2
                    } else if sym == 17 {
                        3
                    } else {
                        7
                    };
                    let base: nat = if sym == 16 {
                        3
                    } else if sym == 17 {
                        3
                    } else {
                        11
                    };
                    let v: u8 = if sym == 16 {
                        lens.last()
                    } else {
                        0
                    };
                    let rep = base + bits(b, p1, e);
                    if !(p1 + e > nbits(b) || lens.len() + rep > total) {
                        let l2 = lens + Seq::new(rep, |i: int| v);
                        lemma_read_lens_end(cl, b, p1 + e, l2, total);
                        if let Some((p, lf)) = read_lens(cl, b, pos, lens, total) {
                            assert(lf.subrange(0, l2.len() as int) == l2);
                            assert(lf.subrange(0, lens.len() as int) =~= l2.subrange(
                                0,
                                lens.len() as int,
                            ));
                            assert(l2.subrange(0, lens.len() as int) =~= lens);
                        }
                    }
                }
            },
        }
    }
}

/// A block ends after it starts and within the input.
pub proof fn lemma_block_end(b: Seq<u8>, pos: int, out: Seq<u8>)
    requires
        0 <= pos,
    ensures
        block(b, pos, out) matches Some((p, o)) ==> pos < p <= nbits(b),
{
    reveal(block);
    let btype = bits(b, pos + 1, 2);
    let p = pos + 3;
    if btype == 0 {
        let i = (p + 7) / 8;
        assert(8 * i >= p);
    } else if btype == 1 {
        lemma_codes_end(b, p, out, fixed_lit_lens(), fixed_dist_lens());
    } else if btype == 2 {
        if p + 14 <= nbits(b) {
            let hlit = bits(b, p, 5) + 257;
            let hdist = bits(b, p + 5, 5) + 1;
            let hclen = bits(b, p + 10, 4) + 4;
            let q = p + 14 + 3 * hclen;
            lemma_read_lens_end(clen_lens(b, p + 14, hclen), b, q, Seq::empty(), hlit + hdist);
        }
        match read_dynamic(b, p) {
            None => {},
            Some((p2, lit, dist)) => {
                lemma_codes_end(b, p2, out, lit, dist);
            },
        }
    }
}

/// `inflate_blocks` decodes a block, then what follows it.
pub proof fn lemma_blocks_unfold(b: Seq<u8>, pos: int, out: Seq<u8>)
    requires
        0 <= pos,
        pos + 3 <= nbits(b),
    ensures
        inflate_blocks(b, pos, out) == after(b, bits(b, pos, 1) == 1, block(b, pos, out)),
{
    lemma_block_end(b, pos, out);
    reveal(block);
    reveal(after);
}

/// Copying a stored block `k` bytes at a time.
pub proof fn lemma_stored_step(b: Seq<u8>, pos: int, n: nat, k: nat, out: Seq<u8>)
    requires
        pos >= 0,
        pos % 8 == 0,
        k <= n,
        pos / 8 + k <= b.len(),
    ensures
        stored_rest(b, pos, n, out) == stored_rest(
            b,
            pos + 8 * k,
            (n - k) as nat,
            out + b.subrange(pos / 8, pos / 8 + k),
        ),
{
    let i = pos / 8;
    assert((pos + 8 * k) / 8 == i + k) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(pos + 8 * k, 8, i + k, 0);
    }
    if i + n <= b.len() {
        assert(out + b.subrange(i, i + n) =~= out + b.subrange(i, i + k) + b.subrange(i + k, i + n));
    }
}

/// A match copied in two parts.
pub proof fn lemma_copy_match_split(out: Seq<u8>, d: nat, a: nat, c: nat)
    ensures
        copy_match(out, d, a + c) == copy_match(copy_match(out, d, a), d, c),
    decreases a,
{
    if a > 0 {
        lemma_copy_match_split(out.push(out[out.len() - d]), d, (a - 1) as nat, c);
        assert((a + c - 1) as nat == (a - 1) as nat + c);
    }
}

/// One more byte of a match: the byte `d` back.
pub proof fn lemma_copy_match_push(out: Seq<u8>, d: nat, n: nat)
    ensures
        copy_match(out, d, n + 1) == copy_match(out, d, n).push(
            copy_match(out, d, n)[copy_match(out, d, n).len() - d],
        ),
{
    lemma_copy_match_split(out, d, n, 1);
    let r = copy_match(out, d, n);
    assert(copy_match(r.push(r[r.len() - d]), d, 0) == r.push(r[r.len() - d]));
}

/// The bytes of a match: the old output, then each byte `d` back.
pub proof fn lemma_copy_match_index(out: Seq<u8>, d: nat, n: nat)
    requires
        1 <= d <= out.len(),
    ensures
        copy_match(out, d, n).len() == out.len() + n,
        copy_match(out, d, n).subrange(0, out.len() as int) == out,
        forall|i: int|
            out.len() <= i < out.len() + n ==> #[trigger] copy_match(out, d, n)[i] == copy_match(
                out,
                d,
                n,
            )[i - d],
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        lemma_copy_match_index(out, d, m);
        lemma_copy_match_push(out, d, m);
        let r = copy_match(out, d, m);
        let r2 = copy_match(out, d, n);
        assert(r2 == r.push(r[r.len() - d]));
        assert(r2.subrange(0, out.len() as int) =~= r.subrange(0, out.len() as int));
        assert forall|i: int| out.len() <= i < out.len() + n implies #[trigger] r2[i] == r2[i - d] by {
            if i < out.len() + m {
                assert(r[i] == r[i - d]);
            }
        }
    }
}

/// A shorter match is a prefix of a longer one.
pub proof fn lemma_copy_match_prefix(out: Seq<u8>, d: nat, a: nat, c: nat)
    requires
        1 <= d <= out.len(),
    ensures
        copy_match(out, d, a + c).subrange(0, (out.len() + a) as int) == copy_match(out, d, a),
{
    lemma_copy_match_split(out, d, a, c);
    lemma_copy_match_index(out, d, a);
    lemma_copy_match_index(copy_match(out, d, a), d, c);
}

/// `CLEN_ORDER` is the spec's order, and `clen_slot` its inverse.
pub proof fn lemma_clen_order()
    ensures
        forall|i: int| 0 <= i < 19 ==> #[trigger] crate::inflate::CLEN_ORDER@[i] as nat == clen_order()[i]
            && clen_slot()[clen_order()[i] as int] == i && clen_order()[i] < 19,
        forall|s: int| 0 <= s < 19 ==> #[trigger] clen_slot()[s] < 19 && clen_order()[clen_slot()[s] as int] == s,
        clen_slot().len() == 19,
        clen_order().len() == 19,
{
    assert(forall|i: int| 0 <= i < 19 ==> #[trigger] crate::inflate::CLEN_ORDER@[i] as nat == clen_order()[i]
            && clen_slot()[clen_order()[i] as int] == i && clen_order()[i] < 19) by (compute);
    assert(forall|s: int| 0 <= s < 19 ==> #[trigger] clen_slot()[s] < 19 && clen_order()[clen_slot()[s] as int] == s) by (compute);
}

// ---------------------------------------------------------------------------
// One symbol of a compressed block
// ---------------------------------------------------------------------------

/// The end of the length or distance whose code at `pos` decodes to `s`
/// and takes `l` bits.
pub open spec fn len_of(b: Seq<u8>, s: nat, p1: int) -> nat {
    len_base()[s - 257] + bits(b, p1, len_extra()[s - 257])
}

pub proof fn lemma_codes_lit(b: Seq<u8>, pos: int, out: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>, s: nat, l: nat)
    requires
        decode(lit, b, pos) == Some((s, l)),
        s < 256,
    ensures
        inflate_codes(b, pos, out, lit, dist) == inflate_codes(b, pos + l, out.push(s as u8), lit, dist),
{
    lemma_decode_from_end(lit, b, pos, 1);
}

pub proof fn lemma_codes_eob(b: Seq<u8>, pos: int, out: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>, l: nat)
    requires
        decode(lit, b, pos) == Some((256nat, l)),
    ensures
        inflate_codes(b, pos, out, lit, dist) == Some((pos + l, out)),
{
    lemma_decode_from_end(lit, b, pos, 1);
}

pub proof fn lemma_codes_bad(b: Seq<u8>, pos: int, out: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>, s: nat, l: nat)
    requires
        decode(lit, b, pos) == Some((s, l)),
        s > 285,
    ensures
        inflate_codes(b, pos, out, lit, dist) is None,
{
    lemma_decode_from_end(lit, b, pos, 1);
}

/// A length symbol `s` (code `l` bits), whose extra bits run past the
/// input or are followed by no valid distance.
pub proof fn lemma_codes_match_none(
    b: Seq<u8>,
    pos: int,
    out: Seq<u8>,
    lit: Seq<u8>,
    dist: Seq<u8>,
    s: nat,
    l: nat,
)
    requires
        decode(lit, b, pos) == Some((s, l)),
        257 <= s <= 285,
        ({
            let p2 = pos + l + len_extra()[s - 257];
            ||| p2 > nbits(b)
            ||| decode(dist, b, p2) is None
            ||| (decode(dist, b, p2) matches Some((ds, dl)) && (ds >= 30 || p2 + dl + dist_extra()[ds as int] > nbits(b)
                || dist_base()[ds as int] + bits(b, p2 + dl, dist_extra()[ds as int]) > out.len()))
        }),
    ensures
        inflate_codes(b, pos, out, lit, dist) is None,
{
    lemma_decode_from_end(lit, b, pos, 1);
}

/// A match.
/// No match reaches back further than 32768 bytes.
pub proof fn lemma_dist_max(b: Seq<u8>, ds: nat, p: int)
    requires
        ds < 30,
    ensures
        dist_base()[ds as int] + bits(b, p, dist_extra()[ds as int]) <= 32768,
{
    lemma_bits_bound(b, p, dist_extra()[ds as int]);
    lemma2_to64();
    assert(dist_base()[ds as int] + pow2(dist_extra()[ds as int]) <= 32769) by {
        assert(dist_base() =~= seq![
            1nat, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025,
            1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
        ]);
        assert(dist_extra() =~= seq![
            0nat, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12,
            12, 13, 13,
        ]);
    }
}

pub proof fn lemma_codes_match(
    b: Seq<u8>,
    pos: int,
    out: Seq<u8>,
    lit: Seq<u8>,
    dist: Seq<u8>,
    s: nat,
    l: nat,
    ds: nat,
    dl: nat,
)
    requires
        decode(lit, b, pos) == Some((s, l)),
        257 <= s <= 285,
        pos + l + len_extra()[s - 257] <= nbits(b),
        decode(dist, b, pos + l + len_extra()[s - 257]) == Some((ds, dl)),
        ds < 30,
        pos + l + len_extra()[s - 257] + dl + dist_extra()[ds as int] <= nbits(b),
        dist_base()[ds as int] + bits(b, pos + l + len_extra()[s - 257] + dl, dist_extra()[ds as int])
            <= out.len(),
    ensures
        inflate_codes(b, pos, out, lit, dist) == inflate_codes(
            b,
            pos + l + len_extra()[s - 257] + dl + dist_extra()[ds as int],
            copy_match(
                out,
                dist_base()[ds as int] + bits(
                    b,
                    pos + l + len_extra()[s - 257] + dl,
                    dist_extra()[ds as int],
                ),
                len_of(b, s, pos + l),
            ),
            lit,
            dist,
        ),
{
    lemma_decode_from_end(lit, b, pos, 1);
}

// ---------------------------------------------------------------------------
// The fast loop
// ---------------------------------------------------------------------------

/// The fast loop's bit buffer: `buf` holds the `a` input bits from the
/// position `8 * ip - cnt`, all within the input. The `a - cnt <= 8` bits
/// above `cnt` are the input's own (the refill loads whole words).
pub open spec fn fast_bits(b: Seq<u8>, buf: u64, cnt: u32, ip: int, a: nat) -> bool {
    &&& cnt <= 63
    &&& cnt <= a <= 64
    &&& a - cnt <= 8
    &&& cnt <= 8 * ip
    &&& ip <= b.len()
    &&& 8 * ip - cnt + a <= nbits(b)
    &&& buf as nat == bits(b, 8 * ip - cnt, a)
}

/// `e` is the entry of the symbol at `pos`.
pub open spec fn resolved(lens: Seq<u8>, which: u8, b: Seq<u8>, pos: int, e: u32) -> bool {
    &&& decode(lens, b, pos) matches Some((s, k))
    &&& e == ent(which, s, k)
    &&& s < lens.len()
    &&& 1 <= k <= 15
    &&& pos + k <= nbits(b)
}

/// Refilling with a whole word: OR it in above the `cnt` bits and advance
/// by the whole bytes that fit.
pub proof fn lemma_fast_refill(b: Seq<u8>, buf: u64, cnt: u32, ip: int, a: nat, w: u64)
    requires
        fast_bits(b, buf, cnt, ip, a),
        ip + 8 <= b.len(),
        w as nat == verilith_core::prims::le_word(b, ip),
    ensures
        fast_bits(
            b,
            buf | (w << (cnt as u64)),
            cnt | 56u32,
            ip + (((63 - cnt) as u32) >> 3u32) as int,
            64,
        ),
        8 * (ip + (((63 - cnt) as u32) >> 3u32) as int) - (cnt | 56u32) == 8 * ip - cnt,
        (cnt | 56u32) >= 56,
        (((63 - cnt) as u32) >> 3u32) <= 7,
{
    let pos = 8 * ip - cnt;
    let c = cnt as u64;
    let k = (a - cnt) as nat;
    let ku = k as u64;
    lemma_le_bytes_bits(b, ip, 8);
    assert(w as nat == bits(b, 8 * ip, 64));
    lemma_shr_bits(b, pos, a, buf, c);
    assert(pos + cnt == 8 * ip);
    lemma_and_mask(w, ku);
    lemma_bits_divmod(b, 8 * ip, k, 64);
    assert((buf >> c) == (w & lowmask(ku)));
    let lo = buf & lowmask(c);
    let r = buf | (w << c);
    assert(r == lo | (w << c)) by (bit_vector)
        requires
            c < 64,
            ku <= 8,
            (buf >> c) == (w & ((1u64 << ku) - 1) as u64),
            lo == buf & ((1u64 << c) - 1) as u64,
            r == buf | (w << c),
    ;
    assert(r & lowmask(c) == lo && (r >> c) == ((w << c) >> c)) by (bit_vector)
        requires
            c < 64,
            lo == buf & ((1u64 << c) - 1) as u64,
            r == lo | (w << c),
    ;
    lemma_and_mask(r, c);
    lemma_u64_shr_is_div(r, c);
    lemma_pow2_pos(c as nat);
    lemma_fundamental_div_mod(r as int, pow2(c as nat) as int);
    if c == 0 {
        assert(((w << c) >> c) == w) by (bit_vector)
            requires
                c == 0,
        ;
        lemma2_to64();
        assert(bits(b, 8 * ip, 64) % pow2(0) == 0);
    } else {
        assert(((w << c) >> c) == w & lowmask((64 - c) as u64)) by (bit_vector)
            requires
                0 < c < 64,
        ;
        lemma_and_mask(w, (64 - c) as u64);
        lemma_bits_divmod(b, 8 * ip, (64 - c) as nat, 64);
    }
    assert((r >> c) as nat == bits(b, 8 * ip, (64 - c) as nat));
    lemma_bits_split(b, pos, c as nat, (64 - c) as nat);
    assert(c as nat + (64 - c) as nat == 64);
    assert(r as nat == bits(b, pos, 64)) by {
        lemma_mul_is_commutative(pow2(c as nat) as int, (r >> c) as int);
    }
    let nc = cnt | 56u32;
    let adv = ((63 - cnt) as u32) >> 3u32;
    assert(nc == cnt + 8 * adv && nc >= 56 && nc <= 63 && adv <= 7) by (bit_vector)
        requires
            cnt <= 63,
            nc == cnt | 56u32,
            adv == ((63 - cnt) as u32) >> 3u32,
    ;
}

/// What the fast loop learns from a table entry: the symbol, or that the
/// code is longer than the table (`LONG`), in which case `decode_slow`
/// finds it.
pub proof fn lemma_fast_entry(
    table: Seq<u32>,
    lens: Seq<u8>,
    which: u8,
    t: nat,
    b: Seq<u8>,
    pos: int,
    a: nat,
    x: nat,
    c: nat,
    e: u32,
)
    requires
        table_ok(table, lens, t, which),
        e == table[bits(b, pos, t) as int],
        x == bits(b, pos, a),
        0 <= pos,
        pos + a <= nbits(b),
        MAX_BITS <= c <= a,
        1 <= t <= MAX_BITS,
        which == ALPHA_LIT || which == ALPHA_DIST,
    ensures
        slow_result(lens, which, x, c) == match decode(lens, b, pos) {
            Some((s, k)) => Some(ent(which, s, k)),
            None => None::<u32>,
        },
        e & F_LONG == 0 ==> resolved(lens, which, b, pos, e),
        e & F_LONG != 0 ==> e == LONG,
        decode(lens, b, pos) is Some ==> resolved(
            lens,
            which,
            b,
            pos,
            ent(which, decode(lens, b, pos)->Some_0.0, decode(lens, b, pos)->Some_0.1),
        ),
{
    lemma_bits_bound(b, pos, t);
    assert(e == tab_entry(lens, which, bits(b, pos, t), t));
    lemma_decode_num(lens, b, pos, a, c, 1);
    lemma_bits_divmod(b, pos, t, a);
    lemma_decode_num_trunc(lens, x, c, t, 1);
    lemma_decode_num_len(lens, x % pow2(t), t, 1);
    lemma_decode_num_sym(lens, x, c, 1);
    lemma_decode_from_end(lens, b, pos, 1);
    lemma_long();
    if let Some((s, k)) = decode_num(lens, x % pow2(t), t, 1) {
        lemma_ent(which, s, k);
    }
}

/// A length is 3 to 258.
pub proof fn lemma_len_bound(b: Seq<u8>, s: nat, p: int)
    requires
        257 <= s <= 285,
    ensures
        3 <= len_of(b, s, p) <= 258,
{
    let le = len_extra()[s - 257];
    lemma_tables();
    lemma_bits_bound(b, p, le);
    lemma2_to64();
    assert(le == len_extra()[s - 257]);
    if le == 0 {
    } else if le == 1 {
    } else if le == 2 {
    } else if le == 3 {
    } else if le == 4 {
    } else {
        assert(le == 5);
    }
    assert(len_base()[s - 257] + pow2(le) - 1 <= 258) by {
        reveal_with_fuel(len_base, 1);
        assert(forall|i: int|
            0 <= i < 29 ==> #[trigger] len_base()[i] + pow2(len_extra()[i]) - 1 <= 258) by (compute);
    }
}

/// In a run where each byte repeats the one before, all equal the first.
pub proof fn lemma_run(s: Seq<u8>, lo: int, i: int)
    requires
        1 <= lo <= i < s.len(),
        forall|j: int| lo <= j < s.len() ==> #[trigger] s[j] == s[j - 1],
    ensures
        s[i] == s[lo - 1],
    decreases i - lo,
{
    if i > lo {
        lemma_run(s, lo, i - 1);
    }
}

/// Where each byte repeats the one `d` back, it also repeats the one `m * d`
/// back.
pub proof fn lemma_period(s: Seq<u8>, d: int, lo: int, m: nat, i: int)
    requires
        1 <= d <= lo,
        forall|j: int| lo <= j < s.len() ==> #[trigger] s[j] == s[j - d],
        i < s.len(),
        0 <= i - m * d,
        m >= 1 ==> i - (m - 1) * d >= lo,
    ensures
        s[i] == s[i - m * d],
    decreases m,
{
    if m == 0 {
        assert(m * d == 0) by (nonlinear_arith)
            requires
                m == 0,
        ;
    } else {
        assert(s[i] == s[i - d]);
        if m > 1 {
            assert(i - d - (m - 2) * d == i - (m - 1) * d) by (nonlinear_arith);
            lemma_period(s, d, lo, (m - 1) as nat, i - d);
            assert(i - d - (m - 1) * d == i - m * d) by (nonlinear_arith);
        } else {
            assert(m * d == d) by (nonlinear_arith)
                requires
                    m == 1,
            ;
        }
    }
}

/// An 8-byte copy from `dst - s` back that extends a correct prefix.
pub proof fn lemma_copy8_ok(old: Seq<u8>, new: Seq<u8>, c: Seq<u8>, s: int, dst: int)
    requires
        old.len() == new.len(),
        0 <= s,
        s + 8 <= dst,
        dst + 8 <= old.len(),
        dst + 8 <= c.len(),
        forall|k: int|
            0 <= k < new.len() ==> #[trigger] new[k] == if dst <= k < dst + 8 {
                old[k - dst + s]
            } else {
                old[k]
            },
        forall|i: int| 0 <= i < dst ==> old[i] == #[trigger] c[i],
        forall|i: int| dst <= i < dst + 8 ==> #[trigger] c[i] == c[i - dst + s],
    ensures
        forall|i: int| 0 <= i < dst + 8 ==> new[i] == #[trigger] c[i],
{
    assert forall|i: int| 0 <= i < dst + 8 implies new[i] == #[trigger] c[i] by {
        if i >= dst {
            assert(new[i] == old[i - dst + s]);
            assert(old[i - dst + s] == c[i - dst + s]);
        } else {
            assert(new[i] == old[i]);
        }
    }
}

/// A block adds at most 129 bytes of output per bit it takes.
pub proof fn lemma_block_output(b: Seq<u8>, pos: int, out: Seq<u8>)
    requires
        0 <= pos,
    ensures
        block(b, pos, out) matches Some((p, o)) ==> pos < p <= nbits(b) && out.len() <= o.len()
            <= out.len() + 129 * (p - pos),
{
    lemma_block_end(b, pos, out);
    reveal(block);
    let btype = bits(b, pos + 1, 2);
    let p = pos + 3;
    if btype == 0 {
        let i = (p + 7) / 8;
        assert(8 * i >= p);
    } else if btype == 1 {
        lemma_codes_end(b, p, out, fixed_lit_lens(), fixed_dist_lens());
    } else if btype == 2 {
        if p + 14 <= nbits(b) {
            let hlit = bits(b, p, 5) + 257;
            let hdist = bits(b, p + 5, 5) + 1;
            let hclen = bits(b, p + 10, 4) + 4;
            let q = p + 14 + 3 * hclen;
            lemma_read_lens_end(clen_lens(b, p + 14, hclen), b, q, Seq::empty(), hlit + hdist);
        }
        match read_dynamic(b, p) {
            None => {},
            Some((p2, lit, dist)) => {
                lemma_codes_end(b, p2, out, lit, dist);
            },
        }
    }
}

/// Decoding blocks adds at most 129 bytes of output per bit.
pub proof fn lemma_blocks_output(b: Seq<u8>, pos: int, out: Seq<u8>)
    requires
        0 <= pos,
    ensures
        inflate_blocks(b, pos, out) matches Some((p, o)) ==> pos < p <= nbits(b) && out.len()
            <= o.len() <= out.len() + 129 * (p - pos),
    decreases nbits(b) - pos,
{
    if pos + 3 <= nbits(b) {
        lemma_blocks_unfold(b, pos, out);
        lemma_block_output(b, pos, out);
        reveal(after);
        if let Some((p, o)) = block(b, pos, out) {
            if bits(b, pos, 1) != 1 {
                lemma_blocks_output(b, p, o);
            }
        }
    }
}

/// The output bound `spec::max_output`: a stream of `n` input bytes
/// decompresses to at most `1032 * n` bytes, in every format.
pub proof fn theorem_output_bound(b: Seq<u8>)
    ensures
        inflate(b) matches Some((o, n)) ==> 0 < n <= b.len() && o.len() <= max_output(n as nat),
        zlib_decompress(b) matches Some((o, n)) ==> 0 < n <= b.len() && o.len() <= max_output(
            n as nat,
        ),
        gzip_decompress(b) matches Some((o, n)) ==> 0 < n <= b.len() && o.len() <= max_output(
            n as nat,
        ),
{
    lemma_blocks_output(b, 0, Seq::empty());
    lemma_blocks_output(b, 16, Seq::empty());
    if let Some((end, o)) = inflate_blocks(b, 0, Seq::empty()) {
        let n = (end + 7) / 8;
        assert(8 * n >= end);
    }
    if let Some((end, o)) = inflate_blocks(b, 16, Seq::empty()) {
        let n = (end + 7) / 8;
        assert(8 * n >= end);
    }
    if let Some(h) = gzip_header(b) {
        lemma_gzip_header_end(b);
        lemma_blocks_output(b, 8 * h, Seq::empty());
        if let Some((end, o)) = inflate_blocks(b, 8 * h, Seq::empty()) {
            let n = (end + 7) / 8;
            assert(8 * n >= end);
        }
    }
}

/// The skipped string ends after `p`, within the input.
pub proof fn lemma_skip_zstr_end(b: Seq<u8>, p: int)
    ensures
        skip_zstr(b, p) matches Some(q) ==> p < q <= b.len(),
    decreases b.len() - p,
{
    if 0 <= p < b.len() && b[p] != 0 {
        lemma_skip_zstr_end(b, p + 1);
    }
}

/// A gzip header ends within the input.
pub proof fn lemma_gzip_header_end(b: Seq<u8>)
    ensures
        gzip_header(b) matches Some(h) ==> 10 <= h <= b.len(),
{
    if b.len() >= 10 {
        let flg = b[3] as nat;
        let p1: int = if has(flg, GZ_FEXTRA) {
            12 + le16(b, 10) as int
        } else {
            10
        };
        lemma_skip_zstr_end(b, p1);
        if let Some(q) = skip_zstr(b, p1) {
            lemma_skip_zstr_end(b, q);
        }
        let p2: int = if has(flg, GZ_FNAME) { match skip_zstr(b, p1) { Some(q) => q, None => p1 } } else { p1 };
        lemma_skip_zstr_end(b, p2);
    }
}

pub proof fn lemma_after_done(b: Seq<u8>, last: bool, p: int, o: Seq<u8>)
    ensures
        after(b, last, Some((p, o))) == if last {
            Some((p, o))
        } else {
            inflate_blocks(b, p, o)
        },
{
    reveal(after);
}

} // verus!
