//! The verified Huffman encoder (RFC 7541 §5.2), proven against the
//! decoder's specification: the bytes `encode` writes decode, by
//! `spec::hdec`, to exactly the input.
//!
//! The proof works on bit sequences. `hbits(s)` is the codes of the
//! symbols of `s`, one after another (`cbits(v, n)` is the `n`-bit code
//! `v`, first bit most significant); the encoder's output is those bits
//! followed by fewer than 8 one bits of padding. That such bytes decode to
//! `s` needs the code to be prefix-free: `hdec` takes the shortest code
//! that matches, so no shorter prefix of a symbol's code may be a code,
//! and no padding of 1 to 7 one bits may be one. `check` verifies that at
//! run time against the RFC table, once (`ready`), the way the decoder's
//! `huffman::check` verifies its canonical layout.
use crate::bits::*;
use crate::htables::*;
use crate::huffman::*;
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/// The low `n` bits of `v`, first bit most significant.
pub open spec fn cbits(v: nat, n: nat) -> Seq<bool>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        cbits(v / 2, (n - 1) as nat).push(v % 2 == 1)
    }
}

/// The bits of `b`, first bit most significant.
pub open spec fn bitsof(b: Seq<u8>) -> Seq<bool> {
    Seq::new(8 * b.len(), |k: int| bit(b, k) == 1)
}

pub open spec fn ones(n: nat) -> Seq<bool> {
    Seq::new(n, |k: int| true)
}

/// The codes of the symbols of `s`, one after another.
pub open spec fn hbits(s: Seq<u8>) -> Seq<bool>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        cbits(hcode(s[0] as int), hlen(s[0] as int)) + hbits(s.drop_first())
    }
}

/// The top `l` bits of symbol `s`'s code.
pub open spec fn pfx(s: int, l: int) -> nat {
    hcode(s) / pow2((hlen(s) - l) as nat)
}

/// `l` one bits, as a number.
pub open spec fn allones(l: int) -> nat {
    (pow2(l as nat) - 1) as nat
}

/// What the encoder's proof needs of the code: the decoder's canonical
/// layout, every code fits its length, no proper prefix of a code is a
/// code, and no run of 1 to 7 one bits (padding) is a code.
pub open spec fn enc_ok() -> bool {
    &&& layout_ok()
    &&& forall|s: int| 0 <= s < 257 ==> #[trigger] hcode(s) < pow2(hlen(s))
    &&& forall|s: int, l: int| 0 <= s < 257 && 1 <= l < hlen(s) ==> !hmatch(l as nat, #[trigger] pfx(s, l))
    &&& forall|l: int| 1 <= l <= 7 ==> !hmatch(l as nat, #[trigger] allones(l))
}

const ONES: [u64; 8] = [0, 1, 3, 7, 15, 31, 63, 127];

proof fn lemma_ones_table()
    ensures
        forall|l: int| 0 <= l < 8 ==> #[trigger] ONES@[l] as nat == allones(l) && ONES@[l] < 128,
{
    lemma2_to64();
}

/// `FIRST[l] <= v < FIRST[l] + CNT[l]`, the decoder's test for a code.
#[inline(always)]
fn in_range(l: usize, v: u64) -> (r: bool)
    requires
        1 <= l <= 30,
    ensures
        r == (FIRST@[l as int] <= v < FIRST@[l as int] + CNT@[l as int]),
{
    v >= FIRST[l] as u64 && v - (FIRST[l] as u64) < CNT[l] as u64
}

/// `layout_ok`, hidden from the solver where it is only carried along.
#[verifier::opaque]
spec fn lay_ok() -> bool {
    layout_ok()
}

/// Checks the facts `enc_ok` needs of symbol `s`'s code.
fn check_sym(s: usize) -> (r: bool)
    requires
        s < 257,
        lay_ok(),
    ensures
        r ==> hcode(s as int) < pow2(hlen(s as int)),
        r ==> forall|l: int| 1 <= l < hlen(s as int) ==> !hmatch(l as nat, #[trigger] pfx(s as int, l)),
{
    let ln = HUFF_LEN[s] as u64;
    let c = HUFF_CODE[s] as u64;
    proof {
        reveal(lay_ok);
        assert(5 <= hlen(s as int) <= 30);
    }
    if c >> ln != 0 {
        return false;
    }
    proof {
        lemma_u64_shr_is_div(c, ln);
        lemma_pow2_pos(ln as nat);
        lemma_fundamental_div_mod(c as int, pow2(ln as nat) as int);
    }
    let mut l: u64 = 1;
    while l < ln
        invariant
            1 <= l <= ln,
            5 <= ln <= 30,
            s < 257,
            ln == hlen(s as int),
            c == hcode(s as int),
            layout_ok(),
            forall|k: int| 1 <= k < l ==> !hmatch(k as nat, #[trigger] pfx(s as int, k)),
        decreases ln - l,
    {
        let v = c >> (ln - l);
        proof {
            lemma_u64_shr_is_div(c, (ln - l) as u64);
            assert(v == pfx(s as int, l as int));
            lemma_match(l as nat, v as nat);
        }
        if in_range(l as usize, v) {
            return false;
        }
        l = l + 1;
    }
    true
}

/// Checks `enc_ok` (once: see `ready`).
pub fn check() -> (r: bool)
    ensures
        r ==> enc_ok(),
{
    if !crate::huffman::check() {
        return false;
    }
    proof {
        reveal(lay_ok);
    }
    let mut s: usize = 0;
    while s < 257
        invariant
            s <= 257,
            lay_ok(),
            forall|t: int| 0 <= t < s ==> #[trigger] hcode(t) < pow2(hlen(t)),
            forall|t: int, l: int| 0 <= t < s && 1 <= l < hlen(t) ==> !hmatch(l as nat, #[trigger] pfx(t, l)),
        decreases 257 - s,
    {
        if !check_sym(s) {
            return false;
        }
        s = s + 1;
    }
    proof {
        reveal(lay_ok);
    }
    let mut l: usize = 1;
    while l <= 7
        invariant
            1 <= l <= 8,
            layout_ok(),
            forall|k: int| 1 <= k < l ==> !hmatch(k as nat, #[trigger] allones(k)),
        decreases 8 - l,
    {
        proof {
            lemma_ones_table();
            lemma_match(l as nat, ONES@[l as int] as nat);
        }
        if in_range(l, ONES[l]) {
            return false;
        }
        l = l + 1;
    }
    true
}

/// `check`, run once. Trusted: that `OnceLock` returns what the closure
/// computed.
#[verifier::external_body]
pub fn ready() -> (r: bool)
    ensures
        r ==> enc_ok(),
{
    static T: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *T.get_or_init(check)
}

// ---------------------------------------------------------------------------
// Bit sequences
// ---------------------------------------------------------------------------

pub proof fn lemma_cbits_len(v: nat, n: nat)
    ensures
        #[trigger] cbits(v, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_cbits_len(v / 2, (n - 1) as nat);
    }
}

/// `n` bits of `a` then `m` bits of `c` are the `n + m` bits of
/// `a * 2^m + c`.
pub proof fn lemma_cbits_concat(a: nat, n: nat, c: nat, m: nat)
    requires
        c < pow2(m),
    ensures
        cbits(a * pow2(m) + c, n + m) == cbits(a, n) + cbits(c, m),
    decreases m,
{
    if m == 0 {
        lemma2_to64();
        assert(c == 0);
        assert(a * pow2(m) == a) by (nonlinear_arith)
            requires
                pow2(m) == 1,
        ;
        assert(cbits(c, m) =~= Seq::<bool>::empty());
        assert(cbits(a, n) + cbits(c, m) =~= cbits(a, n));
    } else {
        lemma_pow2_unfold(m);
        let q = a * pow2((m - 1) as nat);
        let x = a * pow2(m) + c;
        assert(a * pow2(m) == 2 * q) by (nonlinear_arith)
            requires
                pow2(m) == 2 * pow2((m - 1) as nat),
                q == a * pow2((m - 1) as nat),
        ;
        assert(x / 2 == q + c / 2 && x % 2 == c % 2);
        assert(c / 2 < pow2((m - 1) as nat));
        lemma_cbits_concat(a, n, c / 2, (m - 1) as nat);
        assert((n + m - 1) as nat == n + (m - 1) as nat);
        assert(cbits(x, n + m) == cbits(x / 2, (n + m - 1) as nat).push(x % 2 == 1));
        assert(cbits(x / 2, (n + m - 1) as nat) == cbits(a, n) + cbits(c / 2, (m - 1) as nat));
        assert(cbits(c, m) == cbits(c / 2, (m - 1) as nat).push(c % 2 == 1));
        assert(cbits(a, n) + cbits(c, m) =~= (cbits(a, n) + cbits(c / 2, (m - 1) as nat)).push(c % 2 == 1));
        assert(cbits(x, n + m) =~= cbits(a, n) + cbits(c, m));
    }
}

/// `l` one bits.
pub proof fn lemma_ones(l: nat)
    ensures
        cbits(allones(l as int), l) == ones(l),
        allones(l as int) < pow2(l),
    decreases l,
{
    lemma_pow2_pos(l);
    if l == 0 {
        assert(cbits(allones(0), 0) =~= ones(0));
    } else {
        lemma_pow2_unfold(l);
        lemma_ones((l - 1) as nat);
        assert(allones(l as int) / 2 == allones((l - 1) as int));
        assert(allones(l as int) % 2 == 1);
        assert(ones((l - 1) as nat).push(true) =~= ones(l));
    }
}

/// The `n` bits of `b` from `p`, read as a number, are `v` when they are
/// `v`'s bits.
pub proof fn lemma_code_of_bits(b: Seq<u8>, p: int, n: nat, v: nat)
    requires
        0 <= p,
        p + n <= 8 * b.len(),
        bitsof(b).subrange(p, p + n) == cbits(v, n),
        v < pow2(n),
    ensures
        code(b, p, n) == v,
    decreases n,
{
    lemma2_to64();
    if n > 0 {
        lemma_pow2_unfold(n);
        let bb = bitsof(b);
        assert(bb.subrange(p, p + n - 1) =~= bb.subrange(p, p + n).drop_last());
        assert(cbits(v, n).drop_last() =~= cbits(v / 2, (n - 1) as nat));
        lemma_code_of_bits(b, p, (n - 1) as nat, v / 2);
        assert(bb.subrange(p, p + n)[n - 1] == cbits(v, n)[n - 1]);
        assert(bb[p + n - 1] == (bit(b, p + n - 1) == 1));
        assert(bit(b, p + n - 1) < 2);
        assert(bit(b, p + n - 1) == v % 2);
    }
}

/// The bits of `b` from `p` are those of the number they read as.
pub proof fn lemma_bits_of_code(b: Seq<u8>, p: int, n: nat)
    requires
        0 <= p,
        p + n <= 8 * b.len(),
    ensures
        bitsof(b).subrange(p, p + n) == cbits(code(b, p, n), n),
    decreases n,
{
    if n == 0 {
        assert(bitsof(b).subrange(p, p) =~= Seq::<bool>::empty());
    } else {
        lemma_bits_of_code(b, p, (n - 1) as nat);
        let c = code(b, p, n);
        assert(c == 2 * code(b, p, (n - 1) as nat) + bit(b, p + n - 1));
        assert(bit(b, p + n - 1) < 2);
        assert(c / 2 == code(b, p, (n - 1) as nat));
        assert(c % 2 == bit(b, p + n - 1));
        assert(bitsof(b).subrange(p, p + n) =~= bitsof(b).subrange(p, p + n - 1).push(bit(b, p + n - 1) == 1));
    }
}

/// Appending a byte appends its 8 bits.
pub proof fn lemma_bitsof_push(o: Seq<u8>, x: u8)
    ensures
        bitsof(o.push(x)) == bitsof(o) + cbits(x as nat, 8),
{
    let b2 = o.push(x);
    let n = o.len() as int;
    lemma_code_byte(b2, n);
    lemma_bits_of_code(b2, 8 * n, 8);
    assert forall|k: int| 0 <= k < 8 * n implies #[trigger] bitsof(b2)[k] == bitsof(o)[k] by {
        lemma_div_pos_is_pos(k, 8);
        lemma_div_by_multiple_is_strongly_ordered(k, 8 * n, n, 8);
        assert(b2[k / 8] == o[k / 8]);
    }
    lemma_cbits_len(x as nat, 8);
    assert(bitsof(b2) =~= bitsof(o) + cbits(x as nat, 8)) by {
        assert forall|k: int| 0 <= k < 8 * n + 8 implies #[trigger] bitsof(b2)[k] == (bitsof(o) + cbits(x as nat, 8))[k] by {
            if k >= 8 * n {
                assert(bitsof(b2).subrange(8 * n, 8 * n + 8)[k - 8 * n] == bitsof(b2)[k]);
            }
        }
    }
}

pub proof fn lemma_hbits_push(s: Seq<u8>, x: u8)
    ensures
        hbits(s.push(x)) == hbits(s) + cbits(hcode(x as int), hlen(x as int)),
    decreases s.len(),
{
    let c = cbits(hcode(x as int), hlen(x as int));
    if s.len() == 0 {
        assert(s.push(x).drop_first() =~= Seq::<u8>::empty());
        assert(s.push(x)[0] == x);
        assert(hbits(Seq::<u8>::empty()) == Seq::<bool>::empty());
        assert(hbits(s.push(x)) == c + hbits(Seq::<u8>::empty()));
        assert(hbits(s.push(x)) =~= hbits(s) + c);
    } else {
        lemma_hbits_push(s.drop_first(), x);
        assert(s.push(x).drop_first() =~= s.drop_first().push(x));
        assert(s.push(x)[0] == s[0]);
        let h = cbits(hcode(s[0] as int), hlen(s[0] as int));
        assert(h + (hbits(s.drop_first()) + c) =~= (h + hbits(s.drop_first())) + c);
    }
}

pub proof fn lemma_hbits_len(s: Seq<u8>)
    requires
        layout_ok(),
    ensures
        5 * s.len() <= hbits(s).len() <= 30 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_hbits_len(s.drop_first());
        let x = s[0] as int;
        assert(5 <= hlen(x) <= 30);
        lemma_cbits_len(hcode(x), hlen(x));
    }
}

/// The main lemma: the codes of `s` followed by fewer than 8 one bits
/// decode to `s`.
pub proof fn lemma_hdec_enc(b: Seq<u8>, p: int, s: Seq<u8>, pd: nat)
    requires
        enc_ok(),
        0 <= p <= 8 * b.len(),
        pd < 8,
        bitsof(b).subrange(p, 8 * b.len() as int) == hbits(s) + ones(pd),
    ensures
        hdec(b, p) == Some(s),
    decreases s.len(),
{
    let bb = bitsof(b);
    let end = 8 * b.len() as int;
    let r = end - p;
    if s.len() == 0 {
        assert(hbits(s) + ones(pd) =~= ones(pd));
        if r > 0 {
            assert forall|l: nat| 1 <= l < r + 1 implies #[trigger] nomatch(b, p, r as nat, l) by {
                assert(bb.subrange(p, p + l) =~= bb.subrange(p, end).subrange(0, l as int));
                assert(ones(pd).subrange(0, l as int) =~= ones(l));
                lemma_ones(l);
                lemma_code_of_bits(b, p, l, allones(l as int));
            }
            lemma_hfind_skip(b, p, r as nat, 1, (r + 1) as nat);
            assert(hfind(b, p, r as nat, (r + 1) as nat) is None);
            assert(bb.subrange(p, p + r) =~= bb.subrange(p, end));
            lemma_ones(r as nat);
            lemma_code_of_bits(b, p, r as nat, allones(r));
            lemma_pow2_8(r as nat);
        }
        assert(Seq::<u8>::empty() =~= s);
    } else {
        let x = s[0] as int;
        let ln = hlen(x);
        let v = hcode(x);
        let rest = s.drop_first();
        assert(5 <= ln <= 30);
        lemma_cbits_len(v, ln);
        assert(hbits(s) + ones(pd) =~= cbits(v, ln) + (hbits(rest) + ones(pd)));
        assert(bb.subrange(p, p + ln) =~= bb.subrange(p, end).subrange(0, ln as int));
        assert(bb.subrange(p, end).subrange(0, ln as int) =~= cbits(v, ln));
        lemma_code_of_bits(b, p, ln, v);
        assert forall|l: nat| 1 <= l < ln implies #[trigger] nomatch(b, p, r as nat, l) by {
            lemma_code_top(b, p, ln, l);
            assert(code(b, p, l) == pfx(x, l as int));
        }
        lemma_hfind_skip(b, p, r as nat, 1, ln);
        assert(hmatch(ln, v)) by {
            assert(0 <= x < 257 && hlen(x) == ln && hcode(x) == v);
        }
        lemma_match(ln, v);
        assert(hsym(ln, v) == x);
        assert(hfind(b, p, r as nat, 1) == Some((x, ln)));
        assert(bb.subrange(p + ln, end) =~= bb.subrange(p, end).subrange(ln as int, r));
        assert(bb.subrange(p, end).subrange(ln as int, r) =~= hbits(rest) + ones(pd));
        lemma_hdec_enc(b, p + ln, rest, pd);
        assert(seq![x as u8] + rest =~= s);
    }
}

// ---------------------------------------------------------------------------
// The encoder
// ---------------------------------------------------------------------------

/// The length in bytes of `s` Huffman-coded.
pub fn encoded_len(s: &[u8]) -> (r: usize)
    requires
        layout_ok(),
        s@.len() <= 0x1000_0000,
    ensures
        r == (hbits(s@).len() + 7) / 8,
        r <= 4 * s@.len(),
{
    let mut t: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            s@.len() <= 0x1000_0000,
            layout_ok(),
            t == hbits(s@.subrange(0, i as int)).len(),
            t <= 30 * i,
        decreases s@.len() - i,
    {
        let x = s[i];
        proof {
            assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i as int).push(x));
            lemma_hbits_push(s@.subrange(0, i as int), x);
            lemma_cbits_len(hcode(x as int), hlen(x as int));
            assert(hlen(x as int) <= 30);
        }
        t = t + HUFF_LEN[x as usize] as u64;
        i = i + 1;
    }
    proof {
        assert(s@.subrange(0, i as int) =~= s@);
    }
    ((t + 7) / 8) as usize
}

/// `a < p` and `c < q` give `a * q + c < p * q`.
proof fn lemma_mul_lt(a: nat, p: nat, c: nat, q: nat)
    requires
        a < p,
        c < q,
    ensures
        a * q + c < p * q,
{
    assert(a * q + q <= p * q) by (nonlinear_arith)
        requires
            a + 1 <= p,
    ;
}

/// Appends the `ln`-bit code `c` to a window of `nb < 32` bits.
#[inline(always)]
fn append(acc: u64, nb: u64, c: u64, ln: u64) -> (r: u64)
    requires
        nb < 32,
        acc < pow2(nb as nat),
        1 <= ln <= 30,
        c < pow2(ln as nat),
    ensures
        r < pow2((nb + ln) as nat),
        cbits(r as nat, (nb + ln) as nat) == cbits(acc as nat, nb as nat) + cbits(c as nat, ln as nat),
{
    proof {
        lemma_pow2_adds(nb as nat, ln as nat);
        lemma2_to64();
        lemma2_to64_rest();
        lemma_pow2_strictly_increases((nb + ln) as nat, 64);
        lemma_pow2_strictly_increases(ln as nat, 64);
        lemma_mul_lt(acc as nat, pow2(nb as nat), c as nat, pow2(ln as nat));
        lemma_u64_shl_is_mul(acc, ln);
        lemma_u64_shl_is_mul(1, ln);
        assert((acc << ln) | c == (acc << ln) + c) by (bit_vector)
            requires
                c < (1u64 << ln),
                ln < 64,
        ;
        lemma_cbits_concat(acc as nat, nb as nat, c as nat, ln as nat);
    }
    (acc << ln) | c
}

/// Writes out the first bytes of a window of `nb` bits, leaving fewer
/// than `8 + keep`.
#[inline(always)]
fn flush(out: &mut Vec<u8>, acc: u64, nb: u64, keep: u64, Ghost(o0): Ghost<Seq<u8>>, Ghost(w): Ghost<Seq<u8>>) -> (r: (
    u64,
    u64,
    Ghost<Seq<u8>>,
))
    requires
        nb <= 61,
        keep <= 24,
        acc < pow2(nb as nat),
        old(out)@ == o0 + w,
    ensures
        r.1 < 8 + keep,
        r.0 < pow2(r.1 as nat),
        final(out)@ == o0 + r.2@,
        bitsof(r.2@) + cbits(r.0 as nat, r.1 as nat) == bitsof(w) + cbits(acc as nat, nb as nat),
{
    let ghost mut w2 = w;
    let ghost acc0 = acc;
    let ghost nb0 = nb;
    let mut acc = acc;
    let mut nb = nb;
    while nb >= 8 + keep
        invariant
            nb <= 61,
            keep <= 24,
            out@ == o0 + w2,
            acc < pow2(nb as nat),
            bitsof(w2) + cbits(acc as nat, nb as nat) == bitsof(w) + cbits(acc0 as nat, nb0 as nat),
        decreases nb,
    {
        nb = nb - 8;
        let hi = acc >> nb;
        proof {
            lemma_u64_shr_is_div(acc, nb);
            lemma_pow2_pos(nb as nat);
            lemma_fundamental_div_mod(acc as int, pow2(nb as nat) as int);
            lemma_mod_pos_bound(acc as int, pow2(nb as nat) as int);
            lemma_pow2_adds(nb as nat, 8);
            lemma2_to64();
            assert(hi < 256) by (nonlinear_arith)
                requires
                    acc == pow2(nb as nat) * hi + (acc as nat) % pow2(nb as nat),
                    (acc as nat) % pow2(nb as nat) >= 0,
                    acc < pow2(nb as nat) * 256,
                    pow2(nb as nat) > 0,
            ;
            lemma_pow2_strictly_increases(nb as nat, 64);
            assert(hi * pow2(nb as nat) <= acc) by (nonlinear_arith)
                requires
                    acc == pow2(nb as nat) * hi + (acc as nat) % pow2(nb as nat),
                    (acc as nat) % pow2(nb as nat) >= 0,
            ;
            lemma_u64_shl_is_mul(hi, nb);
        }
        let lo = acc - (hi << nb);
        proof {
            assert(acc == hi * pow2(nb as nat) + lo && lo < pow2(nb as nat)) by (nonlinear_arith)
                requires
                    lo == acc - hi * pow2(nb as nat),
                    acc == pow2(nb as nat) * hi + (acc as nat) % pow2(nb as nat),
                    (acc as nat) % pow2(nb as nat) < pow2(nb as nat),
            ;
            lemma_cbits_concat(hi as nat, 8, lo as nat, nb as nat);
            assert(8 + nb == nb + 8);
            lemma_bitsof_push(w2, hi as u8);
            assert(bitsof(w2) + (cbits(hi as nat, 8) + cbits(lo as nat, nb as nat)) =~= (bitsof(w2) + cbits(
                hi as nat,
                8,
            )) + cbits(lo as nat, nb as nat));
            w2 = w2.push(hi as u8);
        }
        out.push(hi as u8);
        acc = lo;
    }
    (acc, nb, Ghost(w2))
}

/// Writes out the first 4 bytes of a window of `nb >= 32` bits.
#[inline(always)]
fn flush4(out: &mut Vec<u8>, acc: u64, nb: u64, Ghost(o0): Ghost<Seq<u8>>, Ghost(w): Ghost<Seq<u8>>) -> (r: (
    u64,
    Ghost<Seq<u8>>,
))
    requires
        32 <= nb <= 61,
        acc < pow2(nb as nat),
        old(out)@ == o0 + w,
    ensures
        r.0 < pow2((nb - 32) as nat),
        final(out)@ == o0 + r.1@,
        bitsof(r.1@) + cbits(r.0 as nat, (nb - 32) as nat) == bitsof(w) + cbits(acc as nat, nb as nat),
{
    let k = nb - 32;
    let hi = acc >> k;
    proof {
        lemma_u64_shr_is_div(acc, k);
        lemma_pow2_pos(k as nat);
        lemma_fundamental_div_mod(acc as int, pow2(k as nat) as int);
        lemma_mod_pos_bound(acc as int, pow2(k as nat) as int);
        lemma_pow2_adds(k as nat, 32);
        lemma2_to64();
        lemma2_to64_rest();
        assert(hi < 0x1_0000_0000) by (nonlinear_arith)
            requires
                acc == pow2(k as nat) * hi + (acc as nat) % pow2(k as nat),
                (acc as nat) % pow2(k as nat) >= 0,
                acc < pow2(k as nat) * 0x1_0000_0000,
                pow2(k as nat) > 0,
        ;
        lemma_pow2_strictly_increases(k as nat, 64);
        assert(hi * pow2(k as nat) <= acc) by (nonlinear_arith)
            requires
                acc == pow2(k as nat) * hi + (acc as nat) % pow2(k as nat),
                (acc as nat) % pow2(k as nat) >= 0,
        ;
        lemma_u64_shl_is_mul(hi, k);
    }
    let lo = acc - (hi << k);
    let b0 = (hi >> 24) as u8;
    let b1 = (hi >> 16) as u8;
    let b2 = (hi >> 8) as u8;
    let b3 = hi as u8;
    proof {
        assert(acc == hi * pow2(k as nat) + lo && lo < pow2(k as nat)) by (nonlinear_arith)
            requires
                lo == acc - hi * pow2(k as nat),
                acc == pow2(k as nat) * hi + (acc as nat) % pow2(k as nat),
                (acc as nat) % pow2(k as nat) < pow2(k as nat),
        ;
        lemma_cbits_concat(hi as nat, 32, lo as nat, k as nat);
        assert(32 + k == nb);
        let r1: u64 = hi % 0x100_0000;
        let r2: u64 = hi % 0x1_0000;
        let r3: u64 = hi % 0x100;
        assert(hi == b0 * 0x100_0000 + r1 && r1 == b1 * 0x1_0000 + r2 && r2 == b2 * 0x100 + r3 && r3 == b3) by (
        bit_vector)
            requires
                hi < 0x1_0000_0000,
                b0 == (hi >> 24) as u8,
                b1 == (hi >> 16) as u8,
                b2 == (hi >> 8) as u8,
                b3 == hi as u8,
                r1 == hi % 0x100_0000,
                r2 == hi % 0x1_0000,
                r3 == hi % 0x100,
        ;
        assert(pow2(24) == 0x100_0000 && pow2(16) == 0x1_0000 && pow2(8) == 0x100);
        lemma_cbits_concat(b0 as nat, 8, r1 as nat, 24);
        lemma_cbits_concat(b1 as nat, 8, r2 as nat, 16);
        lemma_cbits_concat(b2 as nat, 8, r3 as nat, 8);
        lemma_bitsof_push(w, b0);
        lemma_bitsof_push(w.push(b0), b1);
        lemma_bitsof_push(w.push(b0).push(b1), b2);
        lemma_bitsof_push(w.push(b0).push(b1).push(b2), b3);
        let c0 = cbits(b0 as nat, 8);
        let c1 = cbits(b1 as nat, 8);
        let c2 = cbits(b2 as nat, 8);
        let c3 = cbits(b3 as nat, 8);
        assert(cbits(hi as nat, 32) == c0 + (c1 + (c2 + c3)));
        assert(bitsof(w) + (c0 + (c1 + (c2 + c3)) + cbits(lo as nat, k as nat)) =~= (((bitsof(w) + c0) + c1) + c2)
            + c3 + cbits(lo as nat, k as nat));
    }
    out.push(b0);
    out.push(b1);
    out.push(b2);
    out.push(b3);
    proof {
        assert(out@ =~= o0 + w.push(b0).push(b1).push(b2).push(b3));
    }
    (lo, Ghost(w.push(b0).push(b1).push(b2).push(b3)))
}

/// Appends `s` Huffman-coded (RFC 7541 §5.2): the codes of its bytes, then
/// ones to the end of the last byte. They decode to `s`.
pub fn encode(s: &[u8], out: &mut Vec<u8>)
    requires
        enc_ok(),
        s@.len() <= 0x1000_0000,
    ensures
        final(out)@.len() == old(out)@.len() + (hbits(s@).len() + 7) / 8,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        hdec(final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), 0) == Some(s@),
{
    let ghost o0 = out@;
    let ghost mut w: Seq<u8> = Seq::empty();
    let mut acc: u64 = 0;
    let mut nb: u64 = 0;
    let mut i: usize = 0;
    proof {
        lemma2_to64();
        assert(out@ =~= o0 + w);
        assert(bitsof(w) + cbits(0, 0) =~= hbits(s@.subrange(0, 0)));
    }
    while i < s.len()
        invariant
            i <= s@.len(),
            enc_ok(),
            out@ == o0 + w,
            nb < 32,
            acc < pow2(nb as nat),
            bitsof(w) + cbits(acc as nat, nb as nat) == hbits(s@.subrange(0, i as int)),
        decreases s@.len() - i,
    {
        let x = s[i];
        let c = HUFF_CODE[x as usize] as u64;
        let ln = HUFF_LEN[x as usize] as u64;
        proof {
            assert(5 <= hlen(x as int) <= 30);
            assert(c < pow2(ln as nat));
        }
        let a2 = append(acc, nb, c, ln);
        proof {
            assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i as int).push(x));
            lemma_hbits_push(s@.subrange(0, i as int), x);
            assert(bitsof(w) + (cbits(acc as nat, nb as nat) + cbits(c as nat, ln as nat)) =~= (bitsof(w)
                + cbits(acc as nat, nb as nat)) + cbits(c as nat, ln as nat));
        }
        if nb + ln >= 32 {
            let (a3, Ghost(w3)) = flush4(out, a2, nb + ln, Ghost(o0), Ghost(w));
            acc = a3;
            nb = nb + ln - 32;
            proof {
                w = w3;
            }
        } else {
            acc = a2;
            nb = nb + ln;
        }
        i = i + 1;
    }
    let (a3, n3, Ghost(w3)) = flush(out, acc, nb, 0, Ghost(o0), Ghost(w));
    acc = a3;
    nb = n3;
    proof {
        w = w3;
    }
    proof {
        assert(s@.subrange(0, i as int) =~= s@);
    }
    let ghost pd: nat = 0;
    if nb > 0 {
        let k = 8 - nb;
        let o = ONES[k as usize];
        proof {
            lemma_ones_table();
            lemma_ones(k as nat);
            lemma_pow2_adds(nb as nat, k as nat);
            lemma2_to64();
            lemma_mul_lt(acc as nat, pow2(nb as nat), allones(k as int), pow2(k as nat));
            lemma_u64_shl_is_mul(acc, k);
            lemma_u64_shl_is_mul(1, k);
            assert(o == allones(k as int));
            assert((acc << k) | o == (acc << k) + o) by (bit_vector)
                requires
                    o < (1u64 << k),
                    k < 64,
            ;
            lemma_cbits_concat(acc as nat, nb as nat, allones(k as int), k as nat);
            assert(nb + k == 8);
        }
        let byte = ((acc << k) | o) as u8;
        proof {
            lemma_bitsof_push(w, byte);
            assert(bitsof(w) + (cbits(acc as nat, nb as nat) + ones(k as nat)) =~= (bitsof(w) + cbits(
                acc as nat,
                nb as nat,
            )) + ones(k as nat));
            w = w.push(byte);
            pd = k as nat;
        }
        out.push(byte);
    } else {
        proof {
            assert(bitsof(w) + cbits(acc as nat, 0) =~= bitsof(w));
            assert(hbits(s@) + ones(0) =~= hbits(s@));
        }
    }
    proof {
        assert(bitsof(w) == hbits(s@) + ones(pd));
        assert(8 * w.len() == hbits(s@).len() + pd);
        assert(bitsof(w).subrange(0, 8 * w.len() as int) =~= bitsof(w));
        lemma_hdec_enc(w, 0, s@, pd);
        assert(out@.subrange(0, o0.len() as int) =~= o0);
        assert(out@.subrange(o0.len() as int, out@.len() as int) =~= w);
    }
}

} // verus!
