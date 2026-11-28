//! Huffman coding of one block (T.81 F.1.2; libjpeg's `jchuff.c`,
//! `encode_one_block`), proven to decode, under the specification's
//! `base_block`, to exactly the block coded.
use crate::enc_bits::*;
#[cfg(verus_only)]
use crate::huff::{lemma_hbase_mono, lemma_hbase_nonneg, lemma_hfirst_nonneg};
use crate::spec::*;
use crate::types::HuffTab;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The zigzag order, both ways
// ---------------------------------------------------------------------------
/// `ZZI[p]` is the place of row-major position `p` in the zigzag order.
pub const ZZI: [u8; 64] = [
    0, 1, 5, 6, 14, 15, 27, 28, 2, 4, 7, 13, 16, 26, 29, 42, 3, 8, 12, 17, 25, 30, 41, 43, 9, 11, 18, 24, 31, 40, 44,
    53, 10, 19, 23, 32, 39, 45, 52, 54, 20, 22, 33, 38, 46, 51, 55, 60, 21, 34, 37, 47, 50, 56, 59, 61, 35, 36, 48,
    49, 57, 58, 62, 63,
];

pub open spec fn zzi(p: int) -> int {
    ZZI[p] as int
}

pub open spec fn zz_ok(j: int) -> bool
    decreases 64 - j,
{
    if j >= 64 {
        true
    } else {
        ZZ[j] < 64 && ZZI[ZZ[j] as int] as int == j && ZZ[ZZI[j] as int] as int == j && zz_ok(j + 1)
    }
}

proof fn lemma_zz_ok(j: int)
    requires
        0 <= j,
        zz_ok(j),
    ensures
        forall|i: int| j <= i < 64 ==> zz(i) < 64 && #[trigger] zzi(zz(i)) == i,
        forall|p: int| j <= p < 64 ==> 0 <= zzi(p) < 64 && #[trigger] zz(zzi(p)) == p,
    decreases 64 - j,
{
    if j < 64 {
        lemma_zz_ok(j + 1);
    }
}

/// The zigzag order is a permutation of the 64 positions, and `zzi` is its
/// inverse.
pub proof fn lemma_zz_perm()
    ensures
        forall|i: int| 0 <= i < 64 ==> 0 <= zz(i) < 64 && #[trigger] zzi(zz(i)) == i,
        forall|p: int| 0 <= p < 64 ==> 0 <= zzi(p) < 64 && #[trigger] zz(zzi(p)) == p,
{
    assert(zz_ok(0)) by (compute_only);
    lemma_zz_ok(0);
}

// ---------------------------------------------------------------------------
// Code tables for encoding
// ---------------------------------------------------------------------------
/// `sym` has the code `co[sym]` of length `si[sym]` in table `t`: the
/// code of a symbol of that length, and the symbol it stands for is `sym`.
pub open spec fn code_ok(t: HuffTable, co: Seq<u16>, si: Seq<u8>, sym: int) -> bool {
    let l = si[sym] as int;
    let c = co[sym] as int;
    &&& 1 <= l <= 16
    &&& hfirst(t, l) <= c < hfirst(t, l) + hcount(t, l)
    &&& t.vals[hbase(t, l) + c - hfirst(t, l)] as int == sym
}

/// The DC symbols this encoder may write: sizes 0 to 11.
pub open spec fn dc_ready(t: HuffTable, co: Seq<u16>, si: Seq<u8>) -> bool {
    &&& huff_ok(t)
    &&& co.len() == 256 && si.len() == 256
    &&& forall|s: int| 0 <= s <= 11 ==> #[trigger] code_ok(t, co, si, s)
}

/// An AC symbol this encoder may write: end of block, a run of 16 zeros,
/// or a run of up to 15 zeros and a size from 1 to 10.
pub open spec fn ac_sym(sym: int) -> bool {
    0 <= sym < 256 && (sym == 0 || sym == 0xF0 || (1 <= sym % 16 <= 10))
}

pub open spec fn ac_ready(t: HuffTable, co: Seq<u16>, si: Seq<u8>) -> bool {
    &&& huff_ok(t)
    &&& co.len() == 256 && si.len() == 256
    &&& forall|s: int| ac_sym(s) ==> #[trigger] code_ok(t, co, si, s)
}

/// The code of `sym`.
pub open spec fn hc(co: Seq<u16>, si: Seq<u8>, sym: int) -> Seq<bool> {
    bits_of(co[sym] as nat, si[sym] as nat)
}

pub proof fn lemma_hfirst_div(t: HuffTable, a: int, b: int)
    requires
        1 <= a < b,
    ensures
        hfirst(t, b) / pow2((b - a) as nat) as int >= hfirst(t, a) + hcount(t, a),
    decreases b - a,
{
    lemma_hfirst_nonneg(t, a);
    lemma_pow2_unfold((b - a) as nat);
    lemma_pow2_pos((b - a - 1) as nat);
    let p = pow2((b - a - 1) as nat) as int;
    assert(hfirst(t, b) == 2 * (hfirst(t, b - 1) + hcount(t, b - 1)));
    assert(hfirst(t, b) / (2 * p) == (hfirst(t, b) / 2) / p) by {
        lemma_hfirst_nonneg(t, b);
        lemma_div_denominator(hfirst(t, b), 2, p);
    }
    assert(hfirst(t, b) / 2 == hfirst(t, b - 1) + hcount(t, b - 1));
    if b - 1 == a {
        assert(p == 1) by {
            lemma2_to64();
        }
    } else {
        lemma_hfirst_div(t, a, b - 1);
        lemma_hfirst_nonneg(t, b - 1);
        assert(hcount(t, b - 1) >= 0);
        lemma_div_is_ordered(hfirst(t, b - 1), hfirst(t, b - 1) + hcount(t, b - 1), p);
    }
}

/// The first `k` of the `n` bits of `v`.
pub proof fn lemma_bits_of_prefix(v: nat, n: nat, k: nat)
    requires
        k <= n,
    ensures
        bits_of(v, n).subrange(0, k as int) == bits_of(v / pow2((n - k) as nat), k),
    decreases n - k,
{
    lemma_bits_of_len(v, n);
    if k == n {
        lemma2_to64();
        assert((n - k) as nat == 0);
        assert(pow2((n - k) as nat) == 1);
        assert(v / 1 == v);
        assert(bits_of(v, n).subrange(0, k as int) =~= bits_of(v, n));
    } else {
        lemma_bits_of_prefix(v / 2, (n - 1) as nat, k);
        lemma_bits_of_len(v / 2, (n - 1) as nat);
        assert(bits_of(v, n).subrange(0, k as int) =~= bits_of(v / 2, (n - 1) as nat).subrange(0, k as int));
        lemma_pow2_unfold((n - k) as nat);
        lemma_pow2_pos((n - 1 - k) as nat);
        lemma_div_denominator(v as int, 2, pow2((n - 1 - k) as nat) as int);
    }
}

proof fn lemma_bits_at_prefix(e: Seq<u8>, n: int, b: Seq<bool>, k: int)
    requires
        bits_at(e, n, b),
        0 <= k <= b.len(),
    ensures
        bits_at(e, n, b.subrange(0, k)),
{
    assert forall|i: int| 0 <= i < k implies ebit(e, n + i) == b2i(#[trigger] b.subrange(0, k)[i]) as int by {
        assert(b.subrange(0, k)[i] == b[i]);
    }
}

/// The first `j` bits of a code are the code divided by `2^(l - j)`.
proof fn lemma_ebits_prefix(e: Seq<u8>, n: int, c: nat, l: nat, j: nat)
    requires
        c < pow2(l),
        j <= l,
        bits_at(e, n, bits_of(c, l)),
    ensures
        ebits(e, n, j) == c / pow2((l - j) as nat),
        c / pow2((l - j) as nat) < pow2(j),
{
    lemma_bits_of_len(c, l);
    lemma_bits_of_prefix(c, l, j);
    lemma_bits_at_prefix(e, n, bits_of(c, l), j as int);
    lemma_pow2_pos((l - j) as nat);
    let pre = c / pow2((l - j) as nat);
    lemma_pow2_adds(j, (l - j) as nat);
    assert(pow2((l - j) as nat) * pow2(j) == pow2(j) * pow2((l - j) as nat)) by (nonlinear_arith);
    assert(((j + (l - j)) as nat) == l);
    lemma_multiply_divide_lt(c as int, pow2((l - j) as nat) as int, pow2(j) as int);
    lemma_val_bits_of(pre, j);
    lemma_ebits_val(e, n, bits_of(pre, j));
}

proof fn lemma_hdec_walk(t: HuffTable, co: Seq<u16>, si: Seq<u8>, sym: int, e: Seq<u8>, n: int, j: int)
    requires
        huff_ok(t),
        co.len() == 256,
        si.len() == 256,
        0 <= sym < 256,
        code_ok(t, co, si, sym),
        bits_at(e, n, hc(co, si, sym)),
        1 <= j <= si[sym],
    ensures
        hdec(t, e, n, j, ebits(e, n, j as nat)) == (sym, n + si[sym]),
    decreases si[sym] - j,
{
    let l = si[sym] as int;
    let c = co[sym] as nat;
    assert(hfirst(t, l) + hcount(t, l) < pow2(l as nat));
    lemma_ebits_prefix(e, n, c, l as nat, j as nat);
    let pre = c / pow2((l - j) as nat);
    if j < l {
        lemma_hfirst_div(t, j, l);
        lemma_pow2_pos((l - j) as nat);
        lemma_div_is_ordered(hfirst(t, l), c as int, pow2((l - j) as nat) as int);
        assert(!(pre < hfirst(t, j) + hcount(t, j)));
        assert(ebits(e, n, (j + 1) as nat) == 2 * ebits(e, n, j as nat) + ebit(e, n + j));
        lemma_hdec_walk(t, co, si, sym, e, n, j + 1);
    } else {
        lemma2_to64();
        assert((l - j) as nat == 0);
        assert(pow2(0) == 1);
        assert(c / 1 == c);
        assert(pre == c);
    }
}

/// DECODE reads back the code of a symbol.
pub proof fn lemma_huff_enc(t: HuffTable, co: Seq<u16>, si: Seq<u8>, sym: int, e: Seq<u8>, n: int)
    requires
        huff_ok(t),
        co.len() == 256,
        si.len() == 256,
        0 <= sym < 256,
        code_ok(t, co, si, sym),
        bits_at(e, n, hc(co, si, sym)),
    ensures
        huff(t, e, n) == (sym, n + si[sym]),
        hc(co, si, sym).len() == si[sym],
{
    lemma_bits_of_len(co[sym] as nat, si[sym] as nat);
    lemma_hdec_walk(t, co, si, sym, e, n, 1);
    reveal_with_fuel(ebits, 2);
    assert(ebits(e, n, 1) == ebit(e, n));
}

// ---------------------------------------------------------------------------
// Values (T.81 F.1.2.1: SSSS and the additional bits)
// ---------------------------------------------------------------------------
/// The number of bits of `v`.
pub open spec fn nb(v: nat) -> nat
    decreases v,
{
    if v == 0 {
        0
    } else {
        1 + nb(v / 2)
    }
}

pub open spec fn iabs(v: int) -> nat {
    if v < 0 {
        (-v) as nat
    } else {
        v as nat
    }
}

/// The additional bits of `v` in `s` bits: `v`, or `v - 1` in two's
/// complement for a negative one.
pub open spec fn vbits(v: int, s: nat) -> nat {
    if v < 0 {
        (v - 1 + pow2(s)) as nat
    } else {
        v as nat
    }
}

/// The size and additional bits of `v`.
pub open spec fn val_bits(v: int) -> Seq<bool> {
    bits_of(vbits(v, nb(iabs(v))), nb(iabs(v)))
}

pub proof fn lemma_nb(v: nat)
    ensures
        v < pow2(nb(v)),
        v > 0 ==> pow2((nb(v) - 1) as nat) <= v && nb(v) >= 1,
        v == 0 ==> nb(v) == 0,
    decreases v,
{
    lemma2_to64();
    if v > 0 {
        lemma_nb(v / 2);
        lemma_pow2_unfold(nb(v));
        if v / 2 > 0 {
            lemma_pow2_unfold(nb(v / 2));
        }
    }
}

pub proof fn lemma_nb_unique(v: nat, s: nat)
    requires
        s >= 1,
        pow2((s - 1) as nat) <= v < pow2(s),
    ensures
        nb(v) == s,
    decreases s,
{
    lemma2_to64();
    lemma_pow2_unfold(s);
    if s > 1 {
        lemma_pow2_unfold((s - 1) as nat);
        lemma_nb_unique(v / 2, (s - 1) as nat);
    }
}

/// `nb` grows with its argument, and is at most `k` below `2^k`.
pub proof fn lemma_nb_le(v: nat, k: nat)
    requires
        v < pow2(k),
    ensures
        nb(v) <= k,
{
    lemma_nb(v);
    if nb(v) > k {
        lemma_pow2_strictly_increases(k, (nb(v) - 1) as nat);
        if k < (nb(v) - 1) as nat {
        } else {
            assert(k == (nb(v) - 1) as nat);
        }
    }
}

/// EXTEND reads back the additional bits.
pub proof fn lemma_extend(v: int, e: Seq<u8>, k: int)
    requires
        v != 0,
        bits_at(e, k, val_bits(v)),
    ensures
        extend(ebits(e, k, nb(iabs(v))), nb(iabs(v)) as int) == v,
        val_bits(v).len() == nb(iabs(v)),
{
    let s = nb(iabs(v));
    lemma_nb(iabs(v));
    lemma_pow2_unfold(s);
    let half = pow2((s - 1) as nat) as int;
    let u = vbits(v, s);
    assert(u < pow2(s)) by {
        if v < 0 {
        }
    }
    lemma_val_bits_of(u, s);
    lemma_ebits_val(e, k, val_bits(v));
    assert(ebits(e, k, s) == u);
    assert((s - 1) as nat == (s as int - 1) as nat);
}

// ---------------------------------------------------------------------------
// A block's bits
// ---------------------------------------------------------------------------
/// The DC difference `diff`: its size's code, then its bits.
pub open spec fn dc_bits(co: Seq<u16>, si: Seq<u8>, diff: int) -> Seq<bool> {
    hc(co, si, nb(iabs(diff)) as int) + val_bits(diff)
}

/// The AC coefficients of `b` (64, row-major) from zigzag place `k`, after
/// a run of `r` zeros (`encode_one_block`'s loop): a run of more than 15 is
/// written in pieces of 16 (ZRL), and the zeros left at the end as an
/// end of block.
#[verifier::opaque]
pub open spec fn ac_bits(co: Seq<u16>, si: Seq<u8>, b: Seq<i16>, k: int, r: int) -> Seq<bool>
    decreases 64 - k, r,
{
    if k >= 64 || r < 0 {
        if r > 0 {
            hc(co, si, 0)
        } else {
            Seq::empty()
        }
    } else if b[zz(k)] == 0 {
        ac_bits(co, si, b, k + 1, r + 1)
    } else if r > 15 {
        hc(co, si, 0xF0) + ac_bits(co, si, b, k, r - 16)
    } else {
        let v = b[zz(k)] as int;
        hc(co, si, r * 16 + nb(iabs(v)) as int) + val_bits(v) + ac_bits(co, si, b, k + 1, 0)
    }
}

pub proof fn lemma_ac_zero_step(co: Seq<u16>, si: Seq<u8>, b: Seq<i16>, k: int, r: int)
    requires
        0 <= k < 64,
        0 <= r,
        b[zz(k)] == 0,
    ensures
        ac_bits(co, si, b, k, r) == ac_bits(co, si, b, k + 1, r + 1),
{
    reveal_with_fuel(ac_bits, 1);
}

pub proof fn lemma_ac_zrl_step(co: Seq<u16>, si: Seq<u8>, b: Seq<i16>, k: int, r: int)
    requires
        0 <= k < 64,
        r > 15,
        b[zz(k)] != 0,
    ensures
        ac_bits(co, si, b, k, r) == hc(co, si, 0xF0) + ac_bits(co, si, b, k, r - 16),
{
    reveal_with_fuel(ac_bits, 1);
}

pub proof fn lemma_ac_coef_step(co: Seq<u16>, si: Seq<u8>, b: Seq<i16>, k: int, r: int)
    requires
        0 <= k < 64,
        0 <= r <= 15,
        b[zz(k)] != 0,
    ensures
        ac_bits(co, si, b, k, r) == hc(co, si, r * 16 + nb(iabs(b[zz(k)] as int)) as int) + val_bits(b[zz(k)] as int)
            + ac_bits(co, si, b, k + 1, 0),
{
    reveal_with_fuel(ac_bits, 1);
}

pub proof fn lemma_ac_end(co: Seq<u16>, si: Seq<u8>, b: Seq<i16>, r: int)
    requires
        0 <= r,
    ensures
        ac_bits(co, si, b, 64, r) == if r > 0 {
            hc(co, si, 0)
        } else {
            Seq::<bool>::empty()
        },
{
    reveal_with_fuel(ac_bits, 1);
}

/// A block, with the DC prediction `pred`.
pub open spec fn block_bits(
    dco: Seq<u16>,
    dsi: Seq<u8>,
    aco: Seq<u16>,
    asi: Seq<u8>,
    b: Seq<i16>,
    pred: int,
) -> Seq<bool> {
    dc_bits(dco, dsi, b[0] - pred) + ac_bits(aco, asi, b, 1, 0)
}

/// The coefficients a block may have: AC below 1024 in size, so that
/// their sizes are at most 10.
pub open spec fn block_ok(b: Seq<i16>) -> bool {
    &&& b.len() == 64
    &&& forall|i: int| 1 <= i < 64 ==> -1024 < #[trigger] b[i] < 1024
}

/// The block's coefficients written, in zigzag order from place `j`, over
/// `a` at `o`.
pub open spec fn fill(a: Seq<i16>, o: int, b: Seq<i16>, j: int) -> Seq<i16>
    decreases 64 - j,
{
    if j >= 64 {
        a
    } else {
        fill(a.update(o + zz(j), b[zz(j)]), o, b, j + 1)
    }
}

/// `a` with the block at `o` replaced by `b`.
pub open spec fn put_block(a: Seq<i16>, o: int, b: Seq<i16>) -> Seq<i16> {
    Seq::new(a.len(), |i: int| if o <= i < o + 64 { b[i - o] } else { a[i] })
}

proof fn lemma_fill(a: Seq<i16>, o: int, b: Seq<i16>, j: int)
    requires
        0 <= j <= 64,
        0 <= o,
        o + 64 <= a.len(),
        b.len() == 64,
    ensures
        fill(a, o, b, j).len() == a.len(),
        forall|i: int|
            0 <= i < a.len() ==> #[trigger] fill(a, o, b, j)[i] == if o <= i < o + 64 && zzi(i - o) >= j {
                b[i - o]
            } else {
                a[i]
            },
    decreases 64 - j,
{
    lemma_zz_perm();
    if j < 64 {
        let a2 = a.update(o + zz(j), b[zz(j)]);
        lemma_fill(a2, o, b, j + 1);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] fill(a, o, b, j)[i] == if o <= i < o + 64 && zzi(
            i - o,
        ) >= j {
            b[i - o]
        } else {
            a[i]
        } by {
            if o <= i < o + 64 {
                let p = i - o;
                if zzi(p) == j {
                    assert(zz(j) == p);
                } else if i == o + zz(j) {
                    assert(zzi(zz(j)) == j);
                }
            }
        }
    }
}

/// Writing a zero where there is a zero changes nothing.
proof fn lemma_fill_zero(a: Seq<i16>, o: int, b: Seq<i16>, j: int)
    requires
        0 <= j < 64,
        0 <= o,
        o + 64 <= a.len(),
        b.len() == 64,
        b[zz(j)] == 0,
        a[o + zz(j)] == 0,
    ensures
        fill(a, o, b, j) == fill(a, o, b, j + 1),
{
    lemma_zz_perm();
    assert(a.update(o + zz(j), b[zz(j)]) =~= a);
}

proof fn lemma_fill_zeros(a: Seq<i16>, o: int, b: Seq<i16>, j: int, k: int)
    requires
        0 <= j <= k <= 64,
        0 <= o,
        o + 64 <= a.len(),
        b.len() == 64,
        forall|i: int| j <= i < k ==> b[#[trigger] zz(i)] == 0 && a[o + zz(i)] == 0,
    ensures
        fill(a, o, b, j) == fill(a, o, b, k),
    decreases k - j,
{
    if j < k {
        assert(b[zz(j)] == 0 && a[o + zz(j)] == 0);
        lemma_fill_zero(a, o, b, j);
        lemma_fill_zeros(a, o, b, j + 1, k);
    }
}

/// One run of 16 zeros (ZRL).
proof fn lemma_ac_zrl(t: HuffTable, co: Seq<u16>, si: Seq<u8>, e: Seq<u8>, n: int, b: Seq<i16>, k: int, r: int, a: Seq<i16>, o: int)
    requires
        ac_ready(t, co, si),
        block_ok(b),
        16 <= r,
        1 <= k - r,
        k < 64,
        b[zz(k)] != 0,
        bits_at(e, n, ac_bits(co, si, b, k, r)),
    ensures
        bits_at(e, n + si[0xF0], ac_bits(co, si, b, k, r - 16)),
        base_ac(t, e, n, k - r, a, o) == base_ac(t, e, n + si[0xF0], k - r + 16, a, o),
        ac_bits(co, si, b, k, r).len() == si[0xF0] + ac_bits(co, si, b, k, r - 16).len(),
{
    let z = hc(co, si, 0xF0);
    let rest = ac_bits(co, si, b, k, r - 16);
    lemma_ac_zrl_step(co, si, b, k, r);
    lemma_bits_at_cat(e, n, z, rest);
    assert(ac_sym(0xF0));
    lemma_huff_enc(t, co, si, 0xF0, e, n);
    assert(0xF0int / 16 == 15 && 0xF0int % 16 == 0);
}

/// One nonzero coefficient, after fewer than 16 zeros.
#[verifier::rlimit(50)]
proof fn lemma_ac_coef(t: HuffTable, co: Seq<u16>, si: Seq<u8>, e: Seq<u8>, n: int, b: Seq<i16>, k: int, r: int, a: Seq<i16>, o: int)
    requires
        ac_ready(t, co, si),
        block_ok(b),
        0 <= r < 16,
        1 <= k - r,
        k < 64,
        b[zz(k)] != 0,
        bits_at(e, n, ac_bits(co, si, b, k, r)),
    ensures
        ({
            let n2 = n + ac_bits(co, si, b, k, r).len() - ac_bits(co, si, b, k + 1, 0).len();
            &&& bits_at(e, n2, ac_bits(co, si, b, k + 1, 0))
            &&& base_ac(t, e, n, k - r, a, o) == base_ac(t, e, n2, k + 1, a.update(o + zz(k), b[zz(k)]), o)
        }),
{
    lemma_zz_perm();
    let v = b[zz(k)] as int;
    let s = nb(iabs(v));
    let sym = r * 16 + s as int;
    lemma2_to64();
    lemma_nb_le(iabs(v), 10);
    lemma_nb(iabs(v));
    assert(1 <= s <= 10);
    assert(sym % 16 == s && sym / 16 == r);
    assert(ac_sym(sym));
    let c = hc(co, si, sym);
    let vb = val_bits(v);
    let rest = ac_bits(co, si, b, k + 1, 0);
    lemma_ac_coef_step(co, si, b, k, r);
    lemma_bits_at_cat(e, n, c + vb, rest);
    lemma_bits_at_cat(e, n, c, vb);
    lemma_huff_enc(t, co, si, sym, e, n);
    let n1 = n + si[sym];
    lemma_extend(v, e, n1);
    assert(v as i16 == b[zz(k)]);
}

/// The AC coefficients decode to the block's, from the start of the run.
#[verifier::spinoff_prover]
pub proof fn lemma_ac(
    t: HuffTable,
    co: Seq<u16>,
    si: Seq<u8>,
    e: Seq<u8>,
    n: int,
    b: Seq<i16>,
    k: int,
    r: int,
    a: Seq<i16>,
    o: int,
)
    requires
        ac_ready(t, co, si),
        block_ok(b),
        0 <= r,
        1 <= k - r,
        k <= 64,
        forall|j: int| k - r <= j < k ==> b[#[trigger] zz(j)] == 0,
        0 <= o,
        o + 64 <= a.len(),
        forall|j: int| k - r <= j < 64 ==> a[o + #[trigger] zz(j)] == 0,
        bits_at(e, n, ac_bits(co, si, b, k, r)),
    ensures
        base_ac(t, e, n, k - r, a, o) == (fill(a, o, b, k - r), n + ac_bits(co, si, b, k, r).len()),
    decreases 64 - k, r,
{
    lemma_zz_perm();
    if k >= 64 {
        lemma_ac_end(co, si, b, r);
        lemma_fill_zeros(a, o, b, k - r, 64);
        if r > 0 {
            assert(ac_sym(0));
            lemma_huff_enc(t, co, si, 0, e, n);
            assert(t.vals[hbase(t, si[0] as int) + co[0] - hfirst(t, si[0] as int)] == 0);
        }
    } else if b[zz(k)] == 0 {
        lemma_ac_zero_step(co, si, b, k, r);
        lemma_ac(t, co, si, e, n, b, k + 1, r + 1, a, o);
    } else if r > 15 {
        lemma_ac_zrl(t, co, si, e, n, b, k, r, a, o);
        lemma_ac(t, co, si, e, n + si[0xF0], b, k, r - 16, a, o);
        lemma_fill_zeros(a, o, b, k - r, k - r + 16);
    } else {
        lemma_ac_coef(t, co, si, e, n, b, k, r, a, o);
        let n2 = n + ac_bits(co, si, b, k, r).len() - ac_bits(co, si, b, k + 1, 0).len();
        let a2 = a.update(o + zz(k), b[zz(k)]);
        assert forall|j: int| k + 1 <= j < 64 implies a2[o + #[trigger] zz(j)] == 0 by {
            assert(zzi(zz(j)) == j);
            assert(zz(j) != zz(k));
        }
        lemma_ac(t, co, si, e, n2, b, k + 1, 0, a2, o);
        lemma_fill_zeros(a, o, b, k - r, k);
    }
}

/// The DC difference decodes to `diff`.
pub proof fn lemma_dc(t: HuffTable, co: Seq<u16>, si: Seq<u8>, e: Seq<u8>, n: int, diff: int)
    requires
        dc_ready(t, co, si),
        -2048 < diff < 2048,
        bits_at(e, n, dc_bits(co, si, diff)),
    ensures
        dc_diff(t, e, n) == (diff, n + dc_bits(co, si, diff).len()),
{
    let s = nb(iabs(diff));
    lemma2_to64();
    lemma_nb_le(iabs(diff), 11);
    lemma_nb(iabs(diff));
    let c = hc(co, si, s as int);
    let vb = val_bits(diff);
    lemma_bits_at_cat(e, n, c, vb);
    lemma_huff_enc(t, co, si, s as int, e, n);
    lemma_bits_of_len(vbits(diff, s), s);
    if diff != 0 {
        lemma_extend(diff, e, n + si[s as int]);
    } else {
        assert(vb.len() == 0);
    }
}

pub proof fn lemma_wrap(x: int)
    requires
        -32768 <= x < 32768,
    ensures
        wrap16(x) == x,
        wrap32(x) == x,
{
}

/// A block decodes to `b`, over a block of zeros.
pub proof fn lemma_block(
    dt: HuffTable,
    dco: Seq<u16>,
    dsi: Seq<u8>,
    at: HuffTable,
    aco: Seq<u16>,
    asi: Seq<u8>,
    e: Seq<u8>,
    n: int,
    b: Seq<i16>,
    pred: int,
    a: Seq<i16>,
    o: int,
)
    requires
        dc_ready(dt, dco, dsi),
        ac_ready(at, aco, asi),
        block_ok(b),
        -2048 < b[0] - pred < 2048,
        0 <= o,
        o + 64 <= a.len(),
        forall|i: int| 0 <= i < 64 ==> #[trigger] a[o + i] == 0,
        bits_at(e, n, block_bits(dco, dsi, aco, asi, b, pred)),
    ensures
        base_block(dt, at, e, n, pred, a, o) == (
            put_block(a, o, b),
            b[0] as int,
            n + block_bits(dco, dsi, aco, asi, b, pred).len(),
        ),
{
    lemma_zz_perm();
    let d = dc_bits(dco, dsi, b[0] - pred);
    let ac = ac_bits(aco, asi, b, 1, 0);
    lemma_bits_at_cat(e, n, d, ac);
    lemma_dc(dt, dco, dsi, e, n, b[0] - pred);
    let n1 = n + d.len();
    lemma_wrap(b[0] as int);
    let a1 = a.update(o, b[0]);
    assert(zz(0) == 0);
    assert forall|j: int| 1 <= j < 64 implies a1[o + #[trigger] zz(j)] == 0 by {
        assert(zzi(zz(j)) == j);
        assert(zz(j) != 0);
        assert(a[o + zz(j)] == 0);
    }
    lemma_ac(at, aco, asi, e, n1, b, 1, 0, a1, o);
    lemma_fill(a1, o, b, 1);
    let f = fill(a1, o, b, 1);
    assert forall|i: int| 0 <= i < a.len() implies f[i] == #[trigger] put_block(a, o, b)[i] by {
        if o <= i < o + 64 {
            if zzi(i - o) < 1 {
                assert(zz(zzi(i - o)) == i - o);
                assert(i == o);
            }
        }
    }
    assert(f =~= put_block(a, o, b));
}

// ---------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------
/// A table for encoding: each symbol's code and its length (0 for a symbol
/// the table does not have). libjpeg's `c_derived_tbl`.
pub struct ETab {
    pub co: [u16; 256],
    pub si: [u8; 256],
}

impl ETab {
    pub open spec fn has(&self, t: HuffTable) -> bool {
        forall|sym: int| 0 <= sym < 256 && #[trigger] self.si[sym] > 0 ==> code_ok(t, self.co@, self.si@, sym)
    }
}

/// The codes of a table (T.81 C.2; `jpeg_make_c_derived_tbl`).
pub fn etab(t: &HuffTab) -> (r: ETab)
    requires
        huff_ok(t@),
    ensures
        r.has(t@),
{
    let mut co = [0u16; 256];
    let mut si = [0u8; 256];
    let mut code: u32 = 0;
    let mut j: usize = 0;
    let mut l: usize = 1;
    proof {
        lemma_hbase_mono(t@, 1, 17);
    }
    while l <= 16
        invariant
            1 <= l <= 17,
            code == hfirst(t@, l as int),
            j == hbase(t@, l as int),
            hbase(t@, 17) <= 256,
            huff_ok(t@),
            forall|sym: int| 0 <= sym < 256 && #[trigger] si[sym] > 0 ==> code_ok(t@, co@, si@, sym),
        decreases 17 - l,
    {
        let n = t.counts[l - 1] as usize;
        proof {
            assert(hcount(t@, l as int) == n);
            lemma_hbase_mono(t@, l as int + 1, 17);
            assert(hbase(t@, l as int + 1) == j + n);
            assert(hfirst(t@, l as int) + hcount(t@, l as int) < pow2(l as nat));
            lemma_pow2_le16(l as nat);
            lemma_hfirst_nonneg(t@, l as int);
        }
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= l <= 16,
                i <= n,
                n == hcount(t@, l as int),
                code == hfirst(t@, l as int) + i,
                j == hbase(t@, l as int) + i,
                hbase(t@, l as int) + n <= 256,
                hfirst(t@, l as int) + n < pow2(l as nat),
                pow2(l as nat) <= 65536,
                forall|sym: int| 0 <= sym < 256 && #[trigger] si[sym] > 0 ==> code_ok(t@, co@, si@, sym),
            decreases n - i,
        {
            let sym = t.vals[j] as usize;
            let ghost co0 = co@;
            let ghost si0 = si@;
            co[sym] = code as u16;
            si[sym] = l as u8;
            proof {
                assert forall|s2: int| 0 <= s2 < 256 && #[trigger] si[s2] > 0 implies code_ok(t@, co@, si@, s2) by {
                    if s2 != sym {
                        assert(si0[s2] == si[s2] && co0[s2] == co[s2]);
                        assert(code_ok(t@, co0, si0, s2));
                    } else {
                        assert(si[s2] as int == l && co[s2] as int == code);
                    }
                }
            }
            code += 1;
            j += 1;
            i += 1;
        }
        code = 2 * code;
        l += 1;
    }
    ETab { co, si }
}

proof fn lemma_pow2_le16(l: nat)
    requires
        l <= 16,
    ensures
        pow2(l) <= 65536,
{
    lemma2_to64();
    if l < 16 {
        lemma_pow2_strictly_increases(l, 16);
    }
}

/// The table has every DC symbol this encoder writes.
pub fn dc_check(e: &ETab) -> (r: bool)
    ensures
        r ==> forall|s: int| 0 <= s <= 11 ==> #[trigger] e.si[s] > 0,
{
    let mut s: usize = 0;
    while s <= 11
        invariant
            s <= 12,
            forall|j: int| 0 <= j < s ==> #[trigger] e.si[j] > 0,
        decreases 12 - s,
    {
        if e.si[s] == 0 {
            return false;
        }
        s += 1;
    }
    true
}

/// The table has every AC symbol this encoder writes.
pub fn ac_check(e: &ETab) -> (r: bool)
    ensures
        r ==> forall|s: int| ac_sym(s) ==> #[trigger] e.si[s] > 0,
{
    let mut s: usize = 0;
    while s < 256
        invariant
            s <= 256,
            forall|j: int| 0 <= j < s && ac_sym(j) ==> #[trigger] e.si[j] > 0,
        decreases 256 - s,
    {
        let lo = s % 16;
        if (s == 0 || s == 0xF0 || (1 <= lo && lo <= 10)) && e.si[s] == 0 {
            return false;
        }
        s += 1;
    }
    true
}

/// The number of bits of `v` (`JPEG_NBITS`).
#[inline(always)]
pub fn nbits(v: u32) -> (s: u32)
    requires
        v < 2048,
    ensures
        s == nb(v as nat),
        s <= 11,
{
    let z = v.leading_zeros();
    proof {
        vstd::std_specs::bits::axiom_u32_leading_zeros(v);
        lemma2_to64();
        if v == 0 {
            assert(nb(0) == 0);
        } else {
            let s = (32 - z) as u32;
            assert(1 <= s <= 32);
            assert(v >> s == 0);
            assert((v >> ((s - 1) as u32)) & 1u32 != 0u32);
            if s < 32 {
                lemma_u32_shr_is_div(v, s);
                lemma_pow2_pos(s as nat);
                assert(v < pow2(s as nat)) by {
                    lemma_fundamental_div_mod(v as int, pow2(s as nat) as int);
                    lemma_mod_bound(v as int, pow2(s as nat) as int);
                }
            } else {
                assert(v < 0x1_0000_0000);
            }
            lemma_u32_shr_is_div(v, (s - 1) as u32);
            lemma_pow2_pos((s - 1) as nat);
            assert(v as int / pow2((s - 1) as nat) as int >= 1) by {
                assert((v >> ((s - 1) as u32)) != 0) by (bit_vector)
                    requires
                        (v >> ((s - 1) as u32)) & 1u32 != 0u32,
                ;
            }
            assert(v >= pow2((s - 1) as nat)) by {
                lemma_fundamental_div_mod(v as int, pow2((s - 1) as nat) as int);
                lemma_mod_bound(v as int, pow2((s - 1) as nat) as int);
                assert(pow2((s - 1) as nat) * (v as int / pow2((s - 1) as nat) as int) >= pow2((s - 1) as nat))
                    by (nonlinear_arith)
                    requires
                        v as int / pow2((s - 1) as nat) as int >= 1,
                        pow2((s - 1) as nat) > 0,
                ;
            }
            if s >= 32 {
                lemma_pow2_strictly_increases(11, 31);
                assert(false);
            }
            lemma_nb_unique(v as nat, s as nat);
            if s > 11 {
                lemma_pow2_strictly_increases(11, (s - 1) as nat);
                if (s - 1) as nat == 11 {
                }
                assert(false);
            }
        }
    }
    32 - z
}

/// Writes the size of `v` with table `t` and then its additional bits.
#[inline(always)]
fn put_coef(w: &mut BitWriter, t: &ETab, run: u32, v: i32, Ghost(ht): Ghost<HuffTable>)
    requires
        old(w).wf(),
        huff_ok(ht),
        t.has(ht),
        run < 16,
        -2048 < v < 2048,
        run > 0 ==> v != 0,
        t.si[(run * 16 + nb(iabs(v as int))) as int] > 0,
    ensures
        final(w).wf(),
        final(w).bits@ == old(w).bits@ + hc(t.co@, t.si@, run * 16 + nb(iabs(v as int)) as int) + val_bits(
            v as int,
        ),
{
    let a = if v < 0 {
        (-v) as u32
    } else {
        v as u32
    };
    let s = nbits(a);
    let sym = (run * 16 + s) as usize;
    proof {
        assert(sym < 256);
        assert(code_ok(ht, t.co@, t.si@, sym as int));
        let l = t.si[sym as int] as int;
        assert(hfirst(ht, l) + hcount(ht, l) < pow2(l as nat));
    }
    w.put(t.co[sym] as u32, t.si[sym] as u32);
    let ghost b1 = w.bits@;
    if s > 0 {
        proof {
            lemma_nb(a as nat);
            lemma2_to64();
            lemma_pow2_unfold(s as nat);
            lemma_u32_shl_is_mul(1, s);
            lemma_pow2_le16(s as nat);
        }
        let p = 1u32 << s;
        let bits = if v < 0 {
            (v + p as i32 - 1) as u32
        } else {
            v as u32
        };
        proof {
            assert(bits == vbits(v as int, s as nat));
        }
        w.put(bits, s);
    } else {
        proof {
            assert(val_bits(v as int) =~= Seq::<bool>::empty());
            assert(b1 + Seq::<bool>::empty() =~= b1);
        }
    }
}

/// Bit `j` of `m` is set exactly when the block's zigzag coefficient `j`
/// is nonzero and `j` is at least `k`.
pub open spec fn mask_ok(m: u64, b: Seq<i16>, k: int) -> bool {
    forall|j: u64| 0 <= j < 64 ==> (#[trigger] ((m >> j) & 1u64) == 1u64 <==> (j >= k && b[zz(j as int)] != 0))
}

/// Setting bit `p` of `m`.
pub proof fn lemma_bit_set(m: u64, p: u64, j: u64)
    requires
        p < 64,
        j < 64,
    ensures
        ((m | (1u64 << p)) >> j) & 1u64 == 1u64 <==> (((m >> j) & 1u64) == 1u64 || j == p),
{
    assert(((m | (1u64 << p)) >> j) & 1u64 == 1u64 <==> (((m >> j) & 1u64) == 1u64 || j == p)) by (bit_vector)
        requires
            p < 64,
            j < 64,
    ;
}

/// Clearing the lowest set bit, `t`, of `m`.
proof fn lemma_bit_clear(m: u64, t: u64, j: u64)
    requires
        m != 0,
        t < 64,
        (m >> t) & 1u64 == 1u64,
        m << sub(64, t) == 0,
        j < 64,
    ensures
        ((m & sub(m, 1)) >> j) & 1u64 == 1u64 <==> (((m >> j) & 1u64) == 1u64 && j != t),
{
    assert(((m & sub(m, 1)) >> j) & 1u64 == 1u64 <==> (((m >> j) & 1u64) == 1u64 && j != t)) by (bit_vector)
        requires
            m != 0,
            t < 64,
            (m >> t) & 1u64 == 1u64,
            m << sub(64, t) == 0,
            j < 64,
    ;
}

/// A run of zero coefficients from `k0` to `k1`.
pub proof fn lemma_ac_zeros(co: Seq<u16>, si: Seq<u8>, b: Seq<i16>, k0: int, k1: int, r: int)
    requires
        0 <= k0 <= k1 <= 64,
        0 <= r,
        forall|j: int| k0 <= j < k1 ==> b[#[trigger] zz(j)] == 0,
    ensures
        ac_bits(co, si, b, k0, r) == ac_bits(co, si, b, k1, r + (k1 - k0)),
    decreases k1 - k0,
{
    if k0 < k1 {
        lemma_ac_zero_step(co, si, b, k0, r);
        lemma_ac_zeros(co, si, b, k0 + 1, k1, r + 1);
    }
}

/// Codes one block: its DC as a difference from `pred`, then its AC
/// coefficients in zigzag order (`encode_one_block`). `m` is the mask of
/// the nonzero AC coefficients (`mask_ok(m, b, 1)`), so only those are
/// visited, as libjpeg-turbo does with its bit map.
// The default budget is too small for z3's Arm build here; x86 needs less.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn encode_block_m(
    w: &mut BitWriter,
    b: &[i16; 64],
    m: u64,
    pred: i32,
    dc: &ETab,
    ac: &ETab,
    Ghost(dt): Ghost<HuffTable>,
    Ghost(at): Ghost<HuffTable>,
)
    requires
        old(w).wf(),
        dc_ready(dt, dc.co@, dc.si@),
        ac_ready(at, ac.co@, ac.si@),
        dc.has(dt),
        ac.has(at),
        block_ok(b@),
        mask_ok(m, b@, 1),
        -2048 < b[0] - pred < 2048,
    ensures
        final(w).wf(),
        final(w).bits@ == old(w).bits@ + block_bits(dc.co@, dc.si@, ac.co@, ac.si@, b@, pred as int),
{
    let ghost target = old(w).bits@ + block_bits(dc.co@, dc.si@, ac.co@, ac.si@, b@, pred as int);
    proof {
        lemma2_to64();
        lemma_nb_le(iabs(b[0] - pred), 11);
        assert(code_ok(dt, dc.co@, dc.si@, nb(iabs(b[0] - pred)) as int));
    }
    put_coef(w, dc, 0, b[0] as i32 - pred, Ghost(dt));
    proof {
        assert(w.bits@ + ac_bits(ac.co@, ac.si@, b@, 1, 0) =~= target);
        lemma_zz_perm();
    }
    let mut m = m;
    let mut r: u32 = 0;
    let mut kn: u32 = 1;
    while m != 0
        invariant
            w.wf(),
            1 <= kn <= 64,
            r < kn,
            ac_ready(at, ac.co@, ac.si@),
            ac.has(at),
            block_ok(b@),
            mask_ok(m, b@, kn as int),
            w.bits@ + ac_bits(ac.co@, ac.si@, b@, kn as int, r as int) == target,
            forall|i: int| 0 <= i < 64 ==> 0 <= #[trigger] zz(i) < 64,
        decreases 64 - kn,
    {
        let t = m.trailing_zeros();
        proof {
            vstd::std_specs::bits::axiom_u64_trailing_zeros(m);
            let t64 = t as u64;
            assert((m >> t64) & 1u64 == 1u64);
            assert(t >= kn && b@[zz(t as int)] != 0);
            assert forall|j: int| kn <= j < t implies b@[#[trigger] zz(j)] == 0 by {
                let j64 = j as u64;
                assert((m >> j64) & 1u64 == 0u64);
            }
            lemma_ac_zeros(ac.co@, ac.si@, b@, kn as int, t as int, r as int);
        }
        r = r + (t - kn);
        let k = t as usize;
        let v = b[ZZ[k] as usize];
        while r > 15
            invariant
                w.wf(),
                1 <= k < 64,
                r < k,
                v == b@[zz(k as int)],
                v != 0,
                ac_ready(at, ac.co@, ac.si@),
                ac.has(at),
                w.bits@ + ac_bits(ac.co@, ac.si@, b@, k as int, r as int) == target,
            decreases r,
        {
            proof {
                assert(ac_sym(0xF0));
                assert(code_ok(at, ac.co@, ac.si@, 0xF0));
                let l = ac.si[0xF0] as int;
                assert(hfirst(at, l) + hcount(at, l) < pow2(l as nat));
            }
            let ghost b0 = w.bits@;
            w.put(ac.co[0xF0] as u32, ac.si[0xF0] as u32);
            r -= 16;
            proof {
                lemma_ac_zrl_step(ac.co@, ac.si@, b@, k as int, r + 16);
                assert(w.bits@ + ac_bits(ac.co@, ac.si@, b@, k as int, r as int) =~= b0 + ac_bits(
                    ac.co@,
                    ac.si@,
                    b@,
                    k as int,
                    r + 16,
                ));
            }
        }
        proof {
            lemma2_to64();
            lemma_nb_le(iabs(v as int), 10);
            lemma_nb(iabs(v as int));
            let sym = r * 16 + nb(iabs(v as int));
            assert(sym % 16 == nb(iabs(v as int)));
            assert(ac_sym(sym as int));
            assert(code_ok(at, ac.co@, ac.si@, sym as int));
        }
        let ghost b0 = w.bits@;
        put_coef(w, ac, r, v as i32, Ghost(at));
        proof {
            lemma_ac_coef_step(ac.co@, ac.si@, b@, k as int, r as int);
            assert(w.bits@ + ac_bits(ac.co@, ac.si@, b@, k + 1, 0) =~= b0 + ac_bits(
                ac.co@,
                ac.si@,
                b@,
                k as int,
                r as int,
            ));
        }
        let ghost m0 = m;
        m = m & (m - 1);
        proof {
            let t64 = t as u64;
            assert forall|j: u64| 0 <= j < 64 implies (#[trigger] ((m >> j) & 1u64) == 1u64 <==> (j >= t + 1 && b@[zz(j as int)] != 0)) by {
                lemma_bit_clear(m0, t64, j);
                assert(sub(m0, 1) == m0 - 1);
            }
        }
        r = 0;
        kn = t + 1;
    }
    proof {
        assert forall|j: int| kn <= j < 64 implies b@[#[trigger] zz(j)] == 0 by {
            let j64 = j as u64;
            assert((m >> j64) & 1u64 == 0u64) by (bit_vector)
                requires
                    m == 0,
            ;
        }
        lemma_ac_zeros(ac.co@, ac.si@, b@, kn as int, 64, r as int);
    }
    r = r + (64 - kn);
    if r > 0 {
        proof {
            assert(ac_sym(0));
            assert(code_ok(at, ac.co@, ac.si@, 0));
            let l = ac.si[0] as int;
            assert(hfirst(at, l) + hcount(at, l) < pow2(l as nat));
        }
        w.put(ac.co[0] as u32, ac.si[0] as u32);
        proof {
            lemma_ac_end(ac.co@, ac.si@, b@, r as int);
        }
    } else {
        proof {
            lemma_ac_end(ac.co@, ac.si@, b@, r as int);
            assert(w.bits@ + Seq::<bool>::empty() =~= w.bits@);
        }
    }
}

} // verus!
