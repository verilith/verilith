//! The verified Huffman encoder (RFC 7541 §5.2, Appendix B), with the
//! theorem that `verilith_hpack`'s Huffman decoding (`hdec`) of its output
//! is the input.
//!
//! The encoding of a string is the codes of its bytes, first bit most
//! significant, then padding to a byte boundary with the most significant
//! bits of EOS (all ones). `hval` is that bit string as a number and
//! `hbits` its length. The round trip rests on the code being canonical
//! and prefix-free, which `check` verifies at run time against the RFC
//! table, as `verilith_hpack::huffman::check` does for the decoder.
#[cfg(verus_only)]
use verilith_hpack::bits::*;
use verilith_hpack::htables::*;
#[cfg(verus_only)]
use verilith_hpack::huffman::{layout_ok, lemma_match};
#[cfg(verus_only)]
use verilith_hpack::spec::{code, hcode, hdec, hfind, hlen, hmatch, hsym, pow2_8};
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

/// The number of bits of the codes of `s`.
pub open spec fn hbits(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        hlen(s[0] as int) + hbits(s.drop_first())
    }
}

/// The codes of `s`, one after the other, as a number.
pub open spec fn hval(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        hcode(s[0] as int) * pow2(hbits(s.drop_first())) + hval(s.drop_first())
    }
}

/// What the round trip needs of the code, beyond `layout_ok`: the codes of
/// each length come after (in value) the prefixes of all shorter ones (so
/// the code is prefix-free), each code fits its length, and EOS is 30 ones.
#[verifier::opaque]
pub open spec fn code_ok() -> bool {
    &&& layout_ok()
    &&& forall|l: int| 1 <= l < 30 ==> (#[trigger] FIRST@[l] + CNT@[l]) * 2 <= FIRST@[l + 1]
    &&& forall|s: int| 0 <= s < 257 ==> #[trigger] hcode(s) < pow2(hlen(s))
    &&& hlen(256) == 30
    &&& hcode(256) == 0x3fff_ffff
}

/// Checks `code_ok` (once, when an encoder is made).
pub fn check() -> (r: bool)
    ensures
        r ==> code_ok(),
{
    if !verilith_hpack::huffman::check() {
        return false;
    }
    let mut l: usize = 1;
    while l < 30
        invariant
            1 <= l <= 30,
            forall|k: int| 1 <= k < l ==> (#[trigger] FIRST@[k] + CNT@[k]) * 2 <= FIRST@[k + 1],
        decreases 30 - l,
    {
        if (FIRST[l] as u64 + CNT[l] as u64) * 2 > FIRST[l + 1] as u64 {
            return false;
        }
        l = l + 1;
    }
    let mut s: usize = 0;
    while s < 257
        invariant
            s <= 257,
            layout_ok(),
            forall|t: int| 0 <= t < s ==> #[trigger] hcode(t) < pow2(hlen(t)),
        decreases 257 - s,
    {
        let n = HUFF_LEN[s] as u64;
        proof {
            assert(5 <= hlen(s as int) <= 30);
            lemma2_to64();
            lemma_pow2_strictly_increases(n as nat, 64);
            lemma_u64_shl_is_mul(1, n);
        }
        if HUFF_CODE[s] as u64 >= (1u64 << n) {
            return false;
        }
        s = s + 1;
    }
    let r = HUFF_LEN[256] == 30 && HUFF_CODE[256] == 0x3fff_ffff;
    proof {
        reveal(code_ok);
    }
    r
}

/// Each symbol's code fits its length, of 5 to 30 bits.
pub proof fn lemma_sym(x: int)
    requires
        code_ok(),
        0 <= x < 257,
    ensures
        hcode(x) < pow2(hlen(x)),
        5 <= hlen(x) <= 30,
{
    reveal(code_ok);
}

// ---------------------------------------------------------------------------
// Facts about hbits and hval
// ---------------------------------------------------------------------------

proof fn lemma_push_arith(a: nat, h: nat, l: nat, v: nat, c: nat)
    ensures
        a * pow2(h + l) + (v * pow2(l) + c) == (a * pow2(h) + v) * pow2(l) + c,
{
    lemma_pow2_adds(h, l);
    lemma_mul_is_associative(a as int, pow2(h) as int, pow2(l) as int);
    lemma_mul_is_distributive_add_other_way(pow2(l) as int, (a * pow2(h)) as int, v as int);
}

pub proof fn lemma_push(s: Seq<u8>, x: u8)
    ensures
        hbits(s.push(x)) == hbits(s) + hlen(x as int),
        hval(s.push(x)) == hval(s) * pow2(hlen(x as int)) + hcode(x as int),
    decreases s.len(),
{
    let t = s.push(x);
    let l = hlen(x as int);
    if s.len() == 0 {
        assert(t.drop_first() =~= Seq::<u8>::empty());
        assert(t[0] == x);
        assert(hbits(t.drop_first()) == 0);
        assert(hval(t.drop_first()) == 0);
        lemma2_to64();
        assert(hval(t) == hcode(x as int) * pow2(0) + 0);
        assert(hval(s) == 0);
        assert(hbits(s) == 0);
        lemma_mul_basics(hcode(x as int) as int);
        lemma_mul_basics(pow2(l) as int);
    } else {
        let r = s.drop_first();
        assert(t.drop_first() =~= r.push(x));
        assert(t[0] == s[0]);
        lemma_push(r, x);
        let a = hcode(s[0] as int);
        let h = hbits(r);
        let v = hval(r);
        assert(hbits(t) == hlen(s[0] as int) + hbits(r.push(x)));
        assert(hbits(r.push(x)) == h + l);
        assert(hval(t) == a * pow2(h + l) + (v * pow2(l) + hcode(x as int)));
        assert(hval(s) == a * pow2(h) + v);
        lemma_push_arith(a, h, l, v, hcode(x as int));
    }
}

pub proof fn lemma_hval_bound(s: Seq<u8>)
    requires
        code_ok(),
    ensures
        hval(s) < pow2(hbits(s)),
        hbits(s) <= 30 * s.len(),
    decreases s.len(),
{
    reveal(code_ok);
    if s.len() == 0 {
        lemma2_to64();
    } else {
        let r = s.drop_first();
        lemma_hval_bound(r);
        let a = hcode(s[0] as int);
        let l = hlen(s[0] as int);
        let h = hbits(r);
        assert(a < pow2(l));
        assert(5 <= l <= 30);
        lemma_pow2_adds(l, h);
        assert(a * pow2(h) + hval(r) < pow2(l) * pow2(h)) by (nonlinear_arith)
            requires
                a < pow2(l),
                hval(r) < pow2(h),
        ;
    }
}

// ---------------------------------------------------------------------------
// The round trip
// ---------------------------------------------------------------------------

/// The codes of length `L` start above every prefix of a shorter code.
proof fn lemma_chain(l: nat, L: nat)
    requires
        code_ok(),
        1 <= l < L <= 30,
    ensures
        FIRST@[L as int] as nat >= (FIRST@[l as int] + CNT@[l as int]) * pow2((L - l) as nat),
    decreases L - l,
{
    reveal(code_ok);
    let f = (FIRST@[l as int] + CNT@[l as int]) as nat;
    if L == l + 1 {
        lemma2_to64();
        assert(pow2(1) == 2);
    } else {
        lemma_chain(l, (L - 1) as nat);
        let k = (L - 1 - l) as nat;
        lemma_pow2_unfold((k + 1) as nat);
        assert((L - l) as nat == k + 1);
        assert(FIRST@[L - 1] + CNT@[L - 1] <= FIRST@[L as int] / 2);
        assert(f * pow2(k + 1) == 2 * (f * pow2(k))) by (nonlinear_arith)
            requires
                pow2(k + 1) == 2 * pow2(k),
        ;
    }
}

/// No code of length `l` is a prefix of a code of length `L > l`.
proof fn lemma_nomatch(l: nat, L: nat, v: nat)
    requires
        code_ok(),
        1 <= l < L <= 30,
        v >= FIRST@[L as int],
    ensures
        !hmatch(l, v / pow2((L - l) as nat)),
{
    reveal(code_ok);
    lemma_chain(l, L);
    let d = pow2((L - l) as nat);
    let f = (FIRST@[l as int] + CNT@[l as int]) as nat;
    lemma_pow2_pos((L - l) as nat);
    lemma_fundamental_div_mod(v as int, d as int);
    assert(v / d >= f) by (nonlinear_arith)
        requires
            v >= f * d,
            v == d * (v / d) + v % d,
            v % d < d,
            d > 0,
    ;
    lemma_match(l, v / d);
}

/// `a * k + c` with `c < k` determines `a` and `c`.
proof fn lemma_unique(a: nat, c: nat, a2: nat, c2: nat, k: nat)
    requires
        a * k + c == a2 * k + c2,
        c < k,
        c2 < k,
    ensures
        a == a2,
        c == c2,
{
    lemma_fundamental_div_mod_converse((a * k + c) as int, k as int, a as int, c as int);
    lemma_fundamental_div_mod_converse((a2 * k + c2) as int, k as int, a2 as int, c2 as int);
}

/// `hfind` from length `l0` finds symbol `x` when the next bits are its
/// code.
proof fn lemma_hfind_sym(b: Seq<u8>, p: int, r: nat, l0: nat, x: int)
    requires
        code_ok(),
        0 <= x < 257,
        1 <= l0 <= hlen(x),
        hlen(x) <= r,
        code(b, p, hlen(x)) == hcode(x),
    ensures
        hfind(b, p, r, l0) == Some((x, hlen(x))),
    decreases hlen(x) - l0,
{
    reveal(code_ok);
    let L = hlen(x);
    assert(5 <= L <= 30);
    if l0 == L {
        assert(hmatch(L, hcode(x)));
        lemma_match(L, hcode(x));
    } else {
        lemma_code_top(b, p, L, l0);
        lemma_nomatch(l0, L, hcode(x));
        lemma_hfind_sym(b, p, r, l0 + 1, x);
    }
}

/// `2^r - 1` (r ones) shifted right by `r - l` is `l` ones.
proof fn lemma_ones(r: nat, l: nat)
    requires
        l <= r,
    ensures
        ((pow2(r) - 1) as nat) / pow2((r - l) as nat) == (pow2(l) - 1) as nat,
        pow2(l) >= 1,
{
    let d = pow2((r - l) as nat);
    lemma_pow2_adds(l, (r - l) as nat);
    lemma_pow2_pos(l);
    lemma_pow2_pos((r - l) as nat);
    assert(pow2(r) - 1 == (pow2(l) - 1) * d + (d - 1)) by (nonlinear_arith)
        requires
            pow2(r) == pow2(l) * d,
    ;
    lemma_fundamental_div_mod_converse((pow2(r) - 1) as int, d as int, (pow2(l) - 1) as int, (d - 1) as int);
}

/// Padding (at most 7 ones) matches no code.
proof fn lemma_hfind_pad(b: Seq<u8>, p: int, r: nat, l0: nat)
    requires
        code_ok(),
        1 <= l0,
        r <= 7,
        code(b, p, r) == (pow2(r) - 1) as nat,
    ensures
        hfind(b, p, r, l0) is None,
    decreases 31 - l0,
{
    reveal(code_ok);
    if l0 > 30 || l0 > r {
    } else {
        lemma_code_top(b, p, r, l0);
        lemma_ones(r, l0);
        lemma_ones(30, l0);
        assert(pow2(30) == 0x4000_0000) by {
            lemma2_to64();
        }
        assert(hcode(256) >= FIRST@[30]);
        lemma_nomatch(l0, 30, hcode(256));
        lemma_hfind_pad(b, p, r, l0 + 1);
    }
}

proof fn lemma_dec_arith(c: nat, v: nat, h: nat, pad: nat, vs: nat)
    requires
        v < pow2(h),
        vs == c * pow2(h) + v,
    ensures
        v * pow2(pad) + pow2(pad) - 1 < pow2(h + pad),
        vs * pow2(pad) + pow2(pad) - 1 == c * pow2(h + pad) + (v * pow2(pad) + pow2(pad) - 1),
{
    lemma_pow2_adds(h, pad);
    lemma_pow2_pos(pad);
    let q = pow2(pad);
    lemma_mul_inequality((v + 1) as int, pow2(h) as int, q as int);
    lemma_mul_is_distributive_add_other_way(q as int, v as int, 1);
    lemma_mul_is_associative(c as int, pow2(h) as int, q as int);
    lemma_mul_is_distributive_add_other_way(q as int, (c * pow2(h)) as int, v as int);
}

/// The round trip, from bit `p`: bits that are the codes of `s` and then
/// `pad` ones, ending at the end of `b`, decode to `s`.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub proof fn lemma_dec(b: Seq<u8>, s: Seq<u8>, p: int, pad: nat)
    requires
        code_ok(),
        0 <= p,
        pad < 8,
        p + hbits(s) + pad == 8 * b.len(),
        code(b, p, hbits(s) + pad) == hval(s) * pow2(pad) + pow2(pad) - 1,
    ensures
        hdec(b, p) == Some(s),
    decreases s.len(),
{
    let r = (8 * b.len() - p) as nat;
    lemma_pow2_pos(pad);
    if s.len() == 0 {
        assert(s =~= Seq::<u8>::empty());
        assert(hbits(s) == 0 && hval(s) == 0);
        lemma_mul_basics(pow2(pad) as int);
        assert(r == pad);
        if r > 0 {
            lemma_hfind_pad(b, p, r, 1);
            lemma_pow2_8(r);
        }
    } else {
        let x = s[0];
        let L = hlen(x as int);
        let rest = s.drop_first();
        let m = hbits(rest) + pad;
        assert(5 <= L <= 30);
        lemma_code_split(b, p, L, m);
        lemma_code_bound(b, p + L, m);
        lemma_hval_bound(rest);
        lemma_pow2_adds(hbits(rest), pad);
        let w = (hval(rest) * pow2(pad) + pow2(pad) - 1) as nat;
        lemma_dec_arith(hcode(x as int), hval(rest), hbits(rest), pad, hval(s));
        lemma_unique(code(b, p, L), code(b, p + L, m), hcode(x as int), w as nat, pow2(m));
        lemma_hfind_sym(b, p, r, 1, x as int);
        lemma_dec(b, rest, p + L, pad);
        assert(seq![x] + rest =~= s);
    }
}

// ---------------------------------------------------------------------------
// The encoder
// ---------------------------------------------------------------------------

/// The length of the Huffman encoding of `s`, in bits.
pub fn bits_of(s: &[u8]) -> (n: u64)
    requires
        code_ok(),
        s@.len() <= 0x1_0000_0000,
    ensures
        n == hbits(s@),
{
    let mut n: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            s@.len() <= 0x1_0000_0000,
            code_ok(),
            n == hbits(s@.subrange(0, i as int)),
            n <= 30 * i,
        decreases s@.len() - i,
    {
        let x = s[i];
        proof {
            assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i as int).push(x));
            lemma_push(s@.subrange(0, i as int), x);
            assert(hlen(x as int) <= 30);
        }
        n = n + HUFF_LEN[x as usize] as u64;
        i = i + 1;
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    n
}

/// The bits of `e`, all of them, as a number.
pub open spec fn val(e: Seq<u8>) -> nat {
    code(e, 0, 8 * e.len())
}

proof fn lemma_val_push(e: Seq<u8>, x: u8)
    ensures
        val(e.push(x)) == val(e) * 256 + x as nat,
{
    let e2 = e.push(x);
    assert(e =~= e2.subrange(0, e.len() as int));
    lemma_code_prefix(e, e2, 0, 8 * e.len());
    lemma_code_push(e2, 0, 8 * e.len(), e.len() as int);
    assert(8 * e2.len() == 8 * e.len() + 8);
}

/// The new bytes of `out` after its first `z`.
pub open spec fn tail(out: Seq<u8>, z: int) -> Seq<u8> {
    out.subrange(z, out.len() as int)
}

proof fn lemma_tail_push(out: Seq<u8>, z: int, x: u8)
    requires
        0 <= z <= out.len(),
    ensures
        tail(out.push(x), z) == tail(out, z).push(x),
        out.push(x).subrange(0, z) == out.subrange(0, z),
{
    assert(tail(out.push(x), z) =~= tail(out, z).push(x));
    assert(out.push(x).subrange(0, z) =~= out.subrange(0, z));
}

/// Adds a code of `l` bits to a window of `nb < 8` bits.
#[inline(always)]
fn add_code(acc: u64, nb: u64, c: u64, l: u64) -> (r: u64)
    requires
        nb < 8,
        acc < pow2(nb as nat),
        1 <= l <= 30,
        c < pow2(l as nat),
    ensures
        r == acc * pow2(l as nat) + c,
        r < pow2((nb + l) as nat),
{
    proof {
        lemma_pow2_adds(nb as nat, l as nat);
        lemma_pow2_strictly_increases((nb + l) as nat, 64);
        lemma2_to64();
        lemma_mul_inequality((acc + 1) as int, pow2(nb as nat) as int, pow2(l as nat) as int);
        lemma_mul_is_distributive_add_other_way(pow2(l as nat) as int, acc as int, 1);
        lemma_u64_shl_is_mul(acc, l);
    }
    (acc << l) + c
}

/// Takes the top byte of a window of `nb >= 8` bits.
#[inline(always)]
fn take_byte(acc: u64, nb: u64) -> (r: (u8, u64))
    requires
        8 <= nb < 64,
        acc < pow2(nb as nat),
    ensures
        acc == r.0 as nat * pow2((nb - 8) as nat) + r.1,
        r.1 < pow2((nb - 8) as nat),
{
    let rest = nb - 8;
    let top = acc >> rest;
    let ghost an = acc as nat;
    let ghost d = pow2(rest as nat);
    proof {
        lemma2_to64();
        lemma_u64_shr_is_div(acc, rest);
        lemma_pow2_adds(rest as nat, 8);
        lemma_pow2_pos(rest as nat);
        lemma_fundamental_div_mod(an as int, d as int);
        lemma_div_by_multiple_is_strongly_ordered(an as int, (d * 256) as int, 256, d as int);
        lemma_mul_is_commutative(d as int, 256);
        lemma_div_multiples_vanish(256, d as int);
        lemma_pow2_strictly_increases(rest as nat, 64);
        lemma_u64_shl_is_mul(top, rest);
        lemma_mul_is_commutative(d as int, top as int);
    }
    (top as u8, acc - (top << rest))
}

/// Appends the Huffman encoding of `s` to `out`: `(hbits(s) + 7) / 8`
/// bytes that decode to `s`.
#[verifier::spinoff_prover]
pub fn encode(s: &[u8], out: &mut Vec<u8>)
    requires
        code_ok(),
        s@.len() <= 0x1_0000_0000,
    ensures
        final(out)@.len() == old(out)@.len() + (hbits(s@) + 7) / 8,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        hdec(final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), 0) == Some(s@),
{
    let ghost o0 = out@;
    let ghost z = o0.len() as int;
    let mut acc: u64 = 0;
    let mut nb: u64 = 0;
    let mut i: usize = 0;
    proof {
        lemma2_to64();
        assert(tail(out@, z) =~= Seq::<u8>::empty());
        assert(s@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(out@.subrange(0, z) =~= o0);
    }
    while i < s.len()
        invariant
            i <= s@.len(),
            code_ok(),
            z == o0.len(),
            z <= out@.len(),
            out@.subrange(0, z) == o0,
            nb < 8,
            acc < pow2(nb as nat),
            val(tail(out@, z)) * pow2(nb as nat) + acc == hval(s@.subrange(0, i as int)),
            8 * tail(out@, z).len() + nb == hbits(s@.subrange(0, i as int)),
        decreases s@.len() - i,
    {
        let x = s[i];
        let c = HUFF_CODE[x as usize] as u64;
        let l = HUFF_LEN[x as usize] as u64;
        let ghost a0 = acc as nat;
        let ghost n0 = nb as nat;
        proof {
            assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i as int).push(x));
            lemma_push(s@.subrange(0, i as int), x);
            lemma_sym(x as int);
        }
        acc = add_code(acc, nb, c, l);
        nb = nb + l;
        proof {
            let v0 = val(tail(out@, z));
            lemma_pow2_adds(n0, l as nat);
            lemma_mul_is_associative(v0 as int, pow2(n0) as int, pow2(l as nat) as int);
            lemma_mul_is_distributive_add_other_way(pow2(l as nat) as int, (v0 * pow2(n0)) as int, a0 as int);
        }
        while nb >= 8
            invariant
                i < s@.len(),
                nb < 38,
                code_ok(),
                z == o0.len(),
                z <= out@.len(),
                out@.subrange(0, z) == o0,
                acc < pow2(nb as nat),
                val(tail(out@, z)) * pow2(nb as nat) + acc == hval(s@.subrange(0, i + 1)),
                8 * tail(out@, z).len() + nb == hbits(s@.subrange(0, i + 1)),
            decreases nb,
        {
            let ghost e0 = tail(out@, z);
            let ghost an = acc as nat;
            let (top, low) = take_byte(acc, nb);
            proof {
                lemma_tail_push(out@, z, top);
                lemma_val_push(e0, top);
            }
            out.push(top);
            proof {
                let r = (nb - 8) as nat;
                lemma_pow2_adds(r, 8);
                lemma2_to64();
                let v0 = val(e0);
                // v0 * 2^nb + acc == (v0 * 256 + top) * 2^r + low
                lemma_mul_is_associative(v0 as int, 256, pow2(r) as int);
                lemma_mul_is_commutative(256, pow2(r) as int);
                lemma_mul_is_distributive_add_other_way(pow2(r) as int, (v0 * 256) as int, top as int);
            }
            acc = low;
            nb = nb - 8;
        }
        i = i + 1;
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    let ghost e0 = tail(out@, z);
    if nb > 0 {
        let p = 8 - nb;
        proof {
            lemma2_to64();
            lemma_pow2_adds(nb as nat, p as nat);
            lemma_pow2_pos(p as nat);
            lemma_pow2_strictly_increases(p as nat, 8);
            lemma_mul_inequality((acc + 1) as int, pow2(nb as nat) as int, pow2(p as nat) as int);
            lemma_mul_is_distributive_add_other_way(pow2(p as nat) as int, acc as int, 1);
            assert(acc * pow2(p as nat) + pow2(p as nat) <= 256);
            lemma_u64_shl_is_mul(acc, p);
            lemma_u64_shl_is_mul(1, p);
            lemma_mul_basics(pow2(p as nat) as int);
        }
        let byte = ((acc << p) + ((1u64 << p) - 1)) as u8;
        proof {
            lemma_tail_push(out@, z, byte);
            lemma_val_push(e0, byte);
        }
        out.push(byte);
        proof {
            let e = tail(out@, z);
            let v0 = val(e0);
            let q = pow2(p as nat);
            // v0 * 256 + byte == (v0 * 2^nb + acc) * q + q - 1
            lemma_mul_is_associative(v0 as int, pow2(nb as nat) as int, q as int);
            lemma_mul_is_distributive_add_other_way(q as int, (v0 * pow2(nb as nat)) as int, acc as int);
            assert(hbits(s@) + p as nat == 8 * e.len());
            assert(code(e, 0, hbits(s@) + p as nat) == val(e));
            lemma_dec(e, s@, 0, p as nat);
        }
    } else {
        proof {
            assert(pow2(0) == 1) by {
                lemma2_to64();
            }
            assert(hval(s@) * pow2(0) + pow2(0) - 1 == hval(s@));
            assert(acc == 0);
            lemma_mul_basics(val(e0) as int);
            assert(code(e0, 0, hbits(s@) + 0) == val(e0));
            lemma_dec(e0, s@, 0, 0);
        }
    }
}

} // verus!
