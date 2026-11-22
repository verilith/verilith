//! Proofs for the compressor: what it writes decodes, under `spec`, to
//! what it was given.
#[cfg(verus_only)]
use crate::bitwriter::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use crate::ilemmas::*;
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
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Canonical codes
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Written bits
// ---------------------------------------------------------------------------

/// Concatenation of the bits of each item, last item last.
pub open spec fn cat<A>(s: Seq<A>, f: spec_fn(A) -> Seq<nat>) -> Seq<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        cat(s.drop_last(), f) + f(s.last())
    }
}

pub proof fn lemma_cat_push<A>(s: Seq<A>, x: A, f: spec_fn(A) -> Seq<nat>)
    ensures
        cat(s.push(x), f) == cat(s, f) + f(x),
{
    assert(s.push(x).drop_last() =~= s);
}

/// The first item's bits come first.
pub proof fn lemma_cat_front<A>(s: Seq<A>, f: spec_fn(A) -> Seq<nat>)
    requires
        s.len() > 0,
    ensures
        cat(s, f) == f(s[0]) + cat(s.subrange(1, s.len() as int), f),
    decreases s.len(),
{
    let t = s.subrange(1, s.len() as int);
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<A>::empty());
        assert(t =~= Seq::<A>::empty());
        assert(f(s[0]) + Seq::<nat>::empty() =~= f(s[0]));
        assert(Seq::<nat>::empty() + f(s[0]) =~= f(s[0]));
    } else {
        lemma_cat_front(s.drop_last(), f);
        assert(s.drop_last().subrange(1, s.len() - 1) =~= t.drop_last());
        assert(t.last() == s.last());
        assert(f(s[0]) + cat(t.drop_last(), f) + f(s.last()) =~= f(s[0]) + (cat(t.drop_last(), f) + f(
            s.last(),
        )));
    }
}

/// A piece of the written bits at `p` reads back as the number it holds.
pub proof fn lemma_piece(b: Seq<u8>, w: Seq<nat>, p: int, v: nat, n: nat)
    requires
        bytes_hold(b, w),
        0 <= p,
        p + n <= w.len(),
        w.subrange(p, p + n) == bits_of(v, n),
    ensures
        bits(b, p, n) == v % pow2(n),
{
    lemma_written(b, w, p, n);
    lemma_bits_of(v, n);
    let pre = w.subrange(0, p);
    let u = w.subrange(p, p + n);
    let rest = w.subrange(p + n, w.len() as int);
    assert(w =~= pre + u + rest);
    lemma_wbits_prefix(pre + u, rest, p, n);
    lemma_wbits_suffix(pre, u, 0, n);
    assert(pre.len() + 0 == p);
}

/// Splitting the written bits at `p` into two pieces.
pub proof fn lemma_split(w: Seq<nat>, p: int, x: Seq<nat>, y: Seq<nat>)
    requires
        0 <= p,
        p + x.len() + y.len() <= w.len(),
        w.subrange(p, p + x.len() + y.len()) == x + y,
    ensures
        w.subrange(p, p + x.len()) == x,
        w.subrange(p + x.len(), p + x.len() + y.len()) == y,
{
    assert forall|i: int| 0 <= i < x.len() implies #[trigger] w.subrange(p, p + x.len())[i] == x[i] by {
        assert(w.subrange(p, p + x.len() + y.len())[i] == (x + y)[i]);
    }
    assert forall|i: int| 0 <= i < y.len() implies #[trigger] w.subrange(
        p + x.len(),
        p + x.len() + y.len(),
    )[i] == y[i] by {
        assert(w.subrange(p, p + x.len() + y.len())[x.len() + i] == (x + y)[x.len() + i]);
        assert(w.subrange(p, p + x.len() + y.len())[x.len() + i] == w[p + x.len() + i]);
        assert(w.subrange(p + x.len(), p + x.len() + y.len())[i] == w[p + x.len() + i]);
    }
    assert(w.subrange(p, p + x.len()) =~= x);
    assert(w.subrange(p + x.len(), p + x.len() + y.len()) =~= y);
}

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------

/// A token is a literal byte (below 256) or a match, `len * 65536 + dist`.
pub open spec fn is_lit(t: u32) -> bool {
    t < 256
}

pub open spec fn tlen(t: u32) -> nat {
    t as nat / 65536
}

pub open spec fn tdist(t: u32) -> nat {
    t as nat % 65536
}

/// What a token adds to the output.
pub open spec fn apply(out: Seq<u8>, t: u32) -> Seq<u8> {
    if is_lit(t) {
        out.push(t as u8)
    } else {
        copy_match(out, tdist(t), tlen(t))
    }
}

/// The output of tokens `ts`, after `out`.
pub open spec fn expand(out: Seq<u8>, ts: Seq<u32>) -> Seq<u8>
    decreases ts.len(),
{
    if ts.len() == 0 {
        out
    } else {
        expand(apply(out, ts[0]), ts.subrange(1, ts.len() as int))
    }
}

/// Every match is one DEFLATE can send, reaching back into the output.
pub open spec fn toks_ok(out: Seq<u8>, ts: Seq<u32>) -> bool
    decreases ts.len(),
{
    if ts.len() == 0 {
        true
    } else {
        let t = ts[0];
        &&& (!is_lit(t) ==> 3 <= tlen(t) <= 258 && 1 <= tdist(t) <= 32768 && tdist(t) <= out.len())
        &&& toks_ok(apply(out, t), ts.subrange(1, ts.len() as int))
    }
}

pub proof fn lemma_expand_push(out: Seq<u8>, ts: Seq<u32>, t: u32)
    ensures
        expand(out, ts.push(t)) == apply(expand(out, ts), t),
        toks_ok(out, ts.push(t)) == (toks_ok(out, ts) && (!is_lit(t) ==> 3 <= tlen(t) <= 258 && 1 <= tdist(t)
            <= 32768 && tdist(t) <= expand(out, ts).len())),
    decreases ts.len(),
{
    let ts2 = ts.push(t);
    assert(ts2[0] == if ts.len() == 0 { t } else { ts[0] });
    if ts.len() == 0 {
        assert(ts2.subrange(1, 1) =~= Seq::<u32>::empty());
        assert(expand(apply(out, t), Seq::<u32>::empty()) == apply(out, t));
        assert(toks_ok(apply(out, t), Seq::<u32>::empty()));
    } else {
        assert(ts2.subrange(1, ts2.len() as int) =~= ts.subrange(1, ts.len() as int).push(t));
        lemma_expand_push(apply(out, ts[0]), ts.subrange(1, ts.len() as int), t);
    }
}

// ---------------------------------------------------------------------------
// Length and distance symbols
// ---------------------------------------------------------------------------

/// The last table index from `i` down whose base is at most `v`.
pub open spec fn idx_from(base: Seq<nat>, v: nat, i: int) -> int
    decreases i,
{
    if i <= 0 || base[i] <= v {
        i
    } else {
        idx_from(base, v, i - 1)
    }
}

/// The length symbol (less 257) that sends length `len`.
pub open spec fn lidx(len: nat) -> int {
    if len == 258 {
        28
    } else {
        idx_from(len_base(), len, 27)
    }
}

/// The distance symbol that sends distance `d`.
pub open spec fn didx(d: nat) -> int {
    idx_from(dist_base(), d, 29)
}

pub proof fn lemma_steps()
    ensures
        forall|i: int| 0 <= i < 27 ==> #[trigger] len_base()[i + 1] == len_base()[i] + pow2(len_extra()[i]),
        forall|i: int| 0 <= i < 29 ==> #[trigger] dist_base()[i + 1] == dist_base()[i] + pow2(dist_extra()[i]),
        len_base()[0] == 3,
        dist_base()[0] == 1,
        len_base()[27] + pow2(len_extra()[27]) == 259,
        dist_base()[29] + pow2(dist_extra()[29]) == 32769,
        len_base()[28] == 258,
        len_extra()[28] == 0,
{
    lemma2_to64();
    assert(len_base()[1] == len_base()[0] + pow2(len_extra()[0]));
    assert(len_base()[2] == len_base()[1] + pow2(len_extra()[1]));
    assert(len_base()[3] == len_base()[2] + pow2(len_extra()[2]));
    assert(len_base()[4] == len_base()[3] + pow2(len_extra()[3]));
    assert(len_base()[5] == len_base()[4] + pow2(len_extra()[4]));
    assert(len_base()[6] == len_base()[5] + pow2(len_extra()[5]));
    assert(len_base()[7] == len_base()[6] + pow2(len_extra()[6]));
    assert(len_base()[8] == len_base()[7] + pow2(len_extra()[7]));
    assert(len_base()[9] == len_base()[8] + pow2(len_extra()[8]));
    assert(len_base()[10] == len_base()[9] + pow2(len_extra()[9]));
    assert(len_base()[11] == len_base()[10] + pow2(len_extra()[10]));
    assert(len_base()[12] == len_base()[11] + pow2(len_extra()[11]));
    assert(len_base()[13] == len_base()[12] + pow2(len_extra()[12]));
    assert(len_base()[14] == len_base()[13] + pow2(len_extra()[13]));
    assert(len_base()[15] == len_base()[14] + pow2(len_extra()[14]));
    assert(len_base()[16] == len_base()[15] + pow2(len_extra()[15]));
    assert(len_base()[17] == len_base()[16] + pow2(len_extra()[16]));
    assert(len_base()[18] == len_base()[17] + pow2(len_extra()[17]));
    assert(len_base()[19] == len_base()[18] + pow2(len_extra()[18]));
    assert(len_base()[20] == len_base()[19] + pow2(len_extra()[19]));
    assert(len_base()[21] == len_base()[20] + pow2(len_extra()[20]));
    assert(len_base()[22] == len_base()[21] + pow2(len_extra()[21]));
    assert(len_base()[23] == len_base()[22] + pow2(len_extra()[22]));
    assert(len_base()[24] == len_base()[23] + pow2(len_extra()[23]));
    assert(len_base()[25] == len_base()[24] + pow2(len_extra()[24]));
    assert(len_base()[26] == len_base()[25] + pow2(len_extra()[25]));
    assert(len_base()[27] == len_base()[26] + pow2(len_extra()[26]));
    assert(dist_base()[1] == dist_base()[0] + pow2(dist_extra()[0]));
    assert(dist_base()[2] == dist_base()[1] + pow2(dist_extra()[1]));
    assert(dist_base()[3] == dist_base()[2] + pow2(dist_extra()[2]));
    assert(dist_base()[4] == dist_base()[3] + pow2(dist_extra()[3]));
    assert(dist_base()[5] == dist_base()[4] + pow2(dist_extra()[4]));
    assert(dist_base()[6] == dist_base()[5] + pow2(dist_extra()[5]));
    assert(dist_base()[7] == dist_base()[6] + pow2(dist_extra()[6]));
    assert(dist_base()[8] == dist_base()[7] + pow2(dist_extra()[7]));
    assert(dist_base()[9] == dist_base()[8] + pow2(dist_extra()[8]));
    assert(dist_base()[10] == dist_base()[9] + pow2(dist_extra()[9]));
    assert(dist_base()[11] == dist_base()[10] + pow2(dist_extra()[10]));
    assert(dist_base()[12] == dist_base()[11] + pow2(dist_extra()[11]));
    assert(dist_base()[13] == dist_base()[12] + pow2(dist_extra()[12]));
    assert(dist_base()[14] == dist_base()[13] + pow2(dist_extra()[13]));
    assert(dist_base()[15] == dist_base()[14] + pow2(dist_extra()[14]));
    assert(dist_base()[16] == dist_base()[15] + pow2(dist_extra()[15]));
    assert(dist_base()[17] == dist_base()[16] + pow2(dist_extra()[16]));
    assert(dist_base()[18] == dist_base()[17] + pow2(dist_extra()[17]));
    assert(dist_base()[19] == dist_base()[18] + pow2(dist_extra()[18]));
    assert(dist_base()[20] == dist_base()[19] + pow2(dist_extra()[19]));
    assert(dist_base()[21] == dist_base()[20] + pow2(dist_extra()[20]));
    assert(dist_base()[22] == dist_base()[21] + pow2(dist_extra()[21]));
    assert(dist_base()[23] == dist_base()[22] + pow2(dist_extra()[22]));
    assert(dist_base()[24] == dist_base()[23] + pow2(dist_extra()[23]));
    assert(dist_base()[25] == dist_base()[24] + pow2(dist_extra()[24]));
    assert(dist_base()[26] == dist_base()[25] + pow2(dist_extra()[25]));
    assert(dist_base()[27] == dist_base()[26] + pow2(dist_extra()[26]));
    assert(dist_base()[28] == dist_base()[27] + pow2(dist_extra()[27]));
    assert(dist_base()[29] == dist_base()[28] + pow2(dist_extra()[28]));
    assert(len_base()[27] + pow2(len_extra()[27]) == 259);
    assert(dist_base()[29] + pow2(dist_extra()[29]) == 32769);
    assert(len_base()[0] == 3 && dist_base()[0] == 1 && len_base()[28] == 258 && len_extra()[28] == 0);
}

proof fn lemma_idx_from(base: Seq<nat>, extra: Seq<nat>, v: nat, i: int)
    requires
        0 <= i < base.len(),
        base.len() <= extra.len(),
        base[0] <= v,
        v < base[i] + pow2(extra[i]),
        forall|j: int| 0 <= j < i ==> #[trigger] base[j + 1] == base[j] + pow2(extra[j]),
    ensures
        0 <= idx_from(base, v, i) <= i,
        base[idx_from(base, v, i)] <= v < base[idx_from(base, v, i)] + pow2(extra[idx_from(base, v, i)]),
    decreases i,
{
    if !(i <= 0 || base[i] <= v) {
        assert(base[(i - 1) + 1] == base[i - 1] + pow2(extra[i - 1]));
        lemma_idx_from(base, extra, v, i - 1);
    }
}

/// `idx_from` finds the one interval holding `v`.
pub proof fn lemma_idx_unique(base: Seq<nat>, extra: Seq<nat>, v: nat, i: int, j: int)
    requires
        0 <= j <= i < base.len(),
        base.len() <= extra.len(),
        base[j] <= v,
        j == i || v < base[j + 1],
        forall|k: int| 0 <= k < i ==> #[trigger] base[k + 1] == base[k] + pow2(extra[k]),
    ensures
        idx_from(base, v, i) == j,
        i > j ==> base[i] > v,
    decreases i,
{
    if i > j {
        lemma_idx_unique(base, extra, v, i - 1, j);
        assert(base[(i - 1) + 1] == base[i - 1] + pow2(extra[i - 1]));
        vstd::arithmetic::power2::lemma_pow2_pos(extra[i - 1]);
    }
}

pub proof fn lemma_lidx(len: nat)
    requires
        3 <= len <= 258,
    ensures
        0 <= lidx(len) < 29,
        len_base()[lidx(len)] <= len,
        len - len_base()[lidx(len)] < pow2(len_extra()[lidx(len)]),
{
    lemma_steps();
    lemma_tables();
    if len < 258 {
        lemma_idx_from(len_base(), len_extra(), len, 27);
    } else {
        lemma2_to64();
    }
}

pub proof fn lemma_didx(d: nat)
    requires
        1 <= d <= 32768,
    ensures
        0 <= didx(d) < 30,
        dist_base()[didx(d)] <= d,
        d - dist_base()[didx(d)] < pow2(dist_extra()[didx(d)]),
{
    lemma_steps();
    lemma_tables();
    lemma_idx_from(dist_base(), dist_extra(), d, 29);
}

// ---------------------------------------------------------------------------
// Compressed blocks
// ---------------------------------------------------------------------------

/// Symbol `s`'s code, as written.
pub open spec fn code_of(lens: Seq<u8>, s: int) -> Seq<nat> {
    bits_of(rev(canon(lens, s), lens[s] as nat), lens[s] as nat)
}

/// A token, as written with the codes `lit` and `dist`.
pub open spec fn tok_bits(lit: Seq<u8>, dist: Seq<u8>, t: u32) -> Seq<nat> {
    if is_lit(t) {
        code_of(lit, t as int)
    } else {
        let li = lidx(tlen(t));
        let di = didx(tdist(t));
        code_of(lit, 257 + li) + bits_of((tlen(t) - len_base()[li]) as nat, len_extra()[li]) + code_of(dist, di)
            + bits_of((tdist(t) - dist_base()[di]) as nat, dist_extra()[di])
    }
}

pub open spec fn tok_fn(lit: Seq<u8>, dist: Seq<u8>) -> spec_fn(u32) -> Seq<nat> {
    |t: u32| tok_bits(lit, dist, t)
}

/// The codes the token needs have lengths.
pub open spec fn tok_coded(lit: Seq<u8>, dist: Seq<u8>, t: u32) -> bool {
    if is_lit(t) {
        t < lit.len() && 1 <= lit[t as int]
    } else {
        &&& 257 + lidx(tlen(t)) < lit.len()
        &&& 1 <= lit[257 + lidx(tlen(t))]
        &&& didx(tdist(t)) < dist.len()
        &&& 1 <= dist[didx(tdist(t))]
    }
}

/// Code lengths the decoder accepts, as far as the encoder needs.
pub open spec fn lens_ok(lens: Seq<u8>) -> bool {
    &&& forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] as nat <= MAX_BITS
    &&& forall|l: nat| 1 <= l <= MAX_BITS ==> #[trigger] left(lens, l) >= 0
}

/// A code's bits decode to its symbol.
pub proof fn lemma_read_code(b: Seq<u8>, w: Seq<nat>, p: int, lens: Seq<u8>, s: int)
    requires
        bytes_hold(b, w),
        0 <= p,
        0 <= s < lens.len(),
        1 <= lens[s],
        lens_ok(lens),
        p + lens[s] <= w.len(),
        w.subrange(p, p + lens[s]) == code_of(lens, s),
    ensures
        decode(lens, b, p) == Some((s as nat, lens[s] as nat)),
        code_of(lens, s).len() == lens[s],
{
    let m = lens[s] as nat;
    lemma_bits_of(rev(canon(lens, s), m), m);
    lemma_piece(b, w, p, rev(canon(lens, s), m), m);
    lemma_rev_bound(canon(lens, s), m);
    lemma_small_mod(rev(canon(lens, s), m), pow2(m));
    assert(w.len() == 8 * b.len());
    lemma_encode(lens, s, b, p);
}

/// One match: its fields decode to its length and distance.
#[verifier::rlimit(40)]
proof fn lemma_match_step(b: Seq<u8>, w: Seq<nat>, p: int, out: Seq<u8>, t: u32, lit: Seq<u8>, dist: Seq<u8>)
    requires
        bytes_hold(b, w),
        0 <= p,
        lit.len() > 256,
        lens_ok(lit),
        lens_ok(dist),
        !is_lit(t),
        tok_coded(lit, dist, t),
        3 <= tlen(t) <= 258 && 1 <= tdist(t) <= 32768 && tdist(t) <= out.len(),
        p + tok_bits(lit, dist, t).len() <= w.len(),
        w.subrange(p, p + tok_bits(lit, dist, t).len()) == tok_bits(lit, dist, t),
    ensures
        inflate_codes(b, p, out, lit, dist) == inflate_codes(b, p + tok_bits(lit, dist, t).len(), apply(out, t), lit, dist),
{
    let x = tok_bits(lit, dist, t);
    let q = p + x.len();
    let len = tlen(t);
    let d = tdist(t);
    let li = lidx(len);
    let di = didx(d);
    lemma_lidx(len);
    lemma_didx(d);
    lemma_tables();
    let c1 = code_of(lit, 257 + li);
    let e1 = bits_of((len - len_base()[li]) as nat, len_extra()[li]);
    let c2 = code_of(dist, di);
    let e2 = bits_of((d - dist_base()[di]) as nat, dist_extra()[di]);
    lemma_bits_of((len - len_base()[li]) as nat, len_extra()[li]);
    lemma_bits_of((d - dist_base()[di]) as nat, dist_extra()[di]);
    lemma_bits_of(rev(canon(lit, 257 + li), lit[257 + li] as nat), lit[257 + li] as nat);
    lemma_bits_of(rev(canon(dist, di), dist[di] as nat), dist[di] as nat);
    assert(x =~= c1 + (e1 + (c2 + e2)));
    lemma_split(w, p, c1, e1 + (c2 + e2));
    let p1 = p + c1.len();
    lemma_split(w, p1, e1, c2 + e2);
    let p2 = p1 + e1.len();
    lemma_split(w, p2, c2, e2);
    let p3 = p2 + c2.len();
    lemma_read_code(b, w, p, lit, 257 + li);
    lemma_piece(b, w, p1, (len - len_base()[li]) as nat, len_extra()[li]);
    lemma_small_mod((len - len_base()[li]) as nat, pow2(len_extra()[li]));
    lemma_read_code(b, w, p2, dist, di);
    lemma_piece(b, w, p3, (d - dist_base()[di]) as nat, dist_extra()[di]);
    lemma_small_mod((d - dist_base()[di]) as nat, pow2(dist_extra()[di]));
    assert((257 + li) as nat - 257 == li);
    assert(p3 + e2.len() == q);
}

/// The end-of-block code ends the block.
proof fn lemma_eob_step(b: Seq<u8>, w: Seq<nat>, p: int, out: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>)
    requires
        bytes_hold(b, w),
        0 <= p,
        lit.len() > 256,
        lens_ok(lit),
        1 <= lit[256],
        p + code_of(lit, 256).len() <= w.len(),
        w.subrange(p, p + code_of(lit, 256).len()) == code_of(lit, 256),
    ensures
        code_of(lit, 256).len() == lit[256],
        inflate_codes(b, p, out, lit, dist) == Some((p + lit[256], out)),
{
    lemma_bits_of(rev(canon(lit, 256), lit[256] as nat), lit[256] as nat);
    lemma_read_code(b, w, p, lit, 256);
}

/// A literal's code adds the literal.
proof fn lemma_lit_step(b: Seq<u8>, w: Seq<nat>, p: int, out: Seq<u8>, t: u32, lit: Seq<u8>, dist: Seq<u8>)
    requires
        bytes_hold(b, w),
        0 <= p,
        lit.len() > 256,
        lens_ok(lit),
        is_lit(t),
        tok_coded(lit, dist, t),
        p + tok_bits(lit, dist, t).len() <= w.len(),
        w.subrange(p, p + tok_bits(lit, dist, t).len()) == tok_bits(lit, dist, t),
    ensures
        inflate_codes(b, p, out, lit, dist) == inflate_codes(b, p + tok_bits(lit, dist, t).len(), apply(out, t), lit, dist),
{
    lemma_bits_of(rev(canon(lit, t as int), lit[t as int] as nat), lit[t as int] as nat);
    lemma_read_code(b, w, p, lit, t as int);
    assert(w.len() == nbits(b));
}

/// Decoding tokens written with `lit` and `dist`, then end-of-block,
/// gives the output the tokens describe.
pub proof fn lemma_codes(b: Seq<u8>, w: Seq<nat>, p: int, out: Seq<u8>, ts: Seq<u32>, lit: Seq<u8>, dist: Seq<u8>)
    requires
        bytes_hold(b, w),
        0 <= p,
        lit.len() > 256,
        lens_ok(lit),
        lens_ok(dist),
        1 <= lit[256],
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] tok_coded(lit, dist, ts[i]),
        toks_ok(out, ts),
        p + (cat(ts, tok_fn(lit, dist)) + code_of(lit, 256)).len() <= w.len(),
        w.subrange(p, p + (cat(ts, tok_fn(lit, dist)) + code_of(lit, 256)).len()) == cat(ts, tok_fn(lit, dist))
            + code_of(lit, 256),
    ensures
        inflate_codes(b, p, out, lit, dist) == Some((p + (cat(ts, tok_fn(lit, dist)) + code_of(lit, 256)).len(), expand(out, ts))),
    decreases ts.len(),
{
    let f = tok_fn(lit, dist);
    let eob = code_of(lit, 256);
    lemma_bits_of(rev(canon(lit, 256), lit[256] as nat), lit[256] as nat);
    if ts.len() == 0 {
        assert(cat(ts, f) + eob =~= eob);
        lemma_eob_step(b, w, p, out, lit, dist);
    } else {
        let t = ts[0];
        let rest = ts.subrange(1, ts.len() as int);
        lemma_cat_front(ts, f);
        let x = tok_bits(lit, dist, t);
        let y = cat(rest, f) + eob;
        assert(cat(ts, f) + eob =~= x + y);
        lemma_split(w, p, x, y);
        assert(tok_coded(lit, dist, ts[0]));
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] tok_coded(lit, dist, rest[i]) by {
            assert(rest[i] == ts[i + 1]);
        }
        let out2 = apply(out, t);
        lemma_codes(b, w, p + x.len(), out2, rest, lit, dist);
        let q = p + x.len();
        assert(f(t) == x);
        if is_lit(t) {
            lemma_lit_step(b, w, p, out, t, lit, dist);
        } else {
            lemma_match_step(b, w, p, out, t, lit, dist);
        }
    }
}


// ---------------------------------------------------------------------------
// Dynamic block headers
// ---------------------------------------------------------------------------

/// Items written in `n` bits each sit at multiples of `n`.
pub proof fn lemma_cat_fixed<A>(s: Seq<A>, f: spec_fn(A) -> Seq<nat>, n: nat)
    requires
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] f(s[i])).len() == n,
    ensures
        cat(s, f).len() == n * s.len(),
        forall|j: int| 0 <= j < s.len() ==> cat(s, f).subrange(n * j, n * j + n) == #[trigger] f(s[j]),
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies (#[trigger] f(t[i])).len() == n by {
            assert(t[i] == s[i]);
        }
        lemma_cat_fixed(t, f, n);
        let c = cat(t, f);
        let x = f(s.last());
        assert(f(s[s.len() - 1]).len() == n);
        assert(n * s.len() == n * t.len() + n) by (nonlinear_arith)
            requires
                s.len() == t.len() + 1,
        ;
        assert forall|j: int| 0 <= j < s.len() implies cat(s, f).subrange(n * j, n * j + n) == #[trigger] f(s[j]) by {
            if j < t.len() {
                assert(n * j + n <= n * t.len()) by (nonlinear_arith)
                    requires
                        j < t.len(),
                ;
                assert(0 <= n * j) by (nonlinear_arith)
                    requires
                        0 <= j,
                ;
                assert(cat(s, f).subrange(n * j, n * j + n) =~= c.subrange(n * j, n * j + n));
                assert(t[j] == s[j]);
            } else {
                assert(n * j == n * t.len()) by (nonlinear_arith)
                    requires
                        j == t.len(),
                ;
                assert(cat(s, f).subrange(n * j, n * j + n) =~= x);
            }
        }
    }
}

/// A piece of a piece.
pub proof fn lemma_sub(w: Seq<nat>, p: int, x: Seq<nat>, a: int, n: int)
    requires
        0 <= p,
        p + x.len() <= w.len(),
        w.subrange(p, p + x.len()) == x,
        0 <= a,
        a + n <= x.len(),
        0 <= n,
    ensures
        w.subrange(p + a, p + a + n) == x.subrange(a, a + n),
{
    assert forall|i: int| 0 <= i < n implies #[trigger] w.subrange(p + a, p + a + n)[i] == x.subrange(a, a + n)[i] by {
        assert(w.subrange(p, p + x.len())[a + i] == x[a + i]);
    }
    assert(w.subrange(p + a, p + a + n) =~= x.subrange(a, a + n));
}

pub open spec fn len_fn(cl: Seq<u8>) -> spec_fn(u8) -> Seq<nat> {
    |x: u8| code_of(cl, x as int)
}

pub open spec fn b3_fn() -> spec_fn(u8) -> Seq<nat> {
    |x: u8| bits_of(x as nat, 3)
}

/// The code length code's lengths in the order they are sent.
pub open spec fn cl_sent(cl: Seq<u8>, hclen: nat) -> Seq<u8> {
    Seq::new(hclen, |i: int| cl[clen_order()[i] as int])
}

/// Code lengths sent as plain symbols 0 to 15 decode to themselves.
pub proof fn lemma_lens(b: Seq<u8>, w: Seq<nat>, p: int, cl: Seq<u8>, pre: Seq<u8>, suf: Seq<u8>)
    requires
        bytes_hold(b, w),
        0 <= p,
        cl.len() == 19,
        lens_ok(cl),
        forall|i: int| 0 <= i < suf.len() ==> #[trigger] suf[i] < 16 && 1 <= cl[suf[i] as int],
        p + cat(suf, len_fn(cl)).len() <= w.len(),
        w.subrange(p, p + cat(suf, len_fn(cl)).len()) == cat(suf, len_fn(cl)),
    ensures
        read_lens(cl, b, p, pre, (pre.len() + suf.len()) as nat) == Some((p + cat(suf, len_fn(cl)).len(), pre + suf)),
    decreases suf.len(),
{
    let g = len_fn(cl);
    if suf.len() == 0 {
        assert(pre + suf =~= pre);
    } else {
        let x = suf[0];
        let rest = suf.subrange(1, suf.len() as int);
        lemma_cat_front(suf, g);
        let c = code_of(cl, x as int);
        assert(g(x) == c);
        lemma_bits_of(rev(canon(cl, x as int), cl[x as int] as nat), cl[x as int] as nat);
        lemma_split(w, p, c, cat(rest, g));
        assert(x < 16 && 1 <= cl[x as int]);
        lemma_read_code(b, w, p, cl, x as int);
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i] < 16 && 1 <= cl[rest[i] as int] by {
            assert(rest[i] == suf[i + 1]);
        }
        lemma_lens(b, w, p + c.len(), cl, pre.push(x), rest);
        assert(pre.push(x) + rest =~= pre + suf);
        assert((pre.push(x).len() + rest.len()) as nat == (pre.len() + suf.len()) as nat);
    }
}

/// The 3-bit code length code lengths, sent in `clen_order`, read back.
pub proof fn lemma_clen(b: Seq<u8>, w: Seq<nat>, p: int, cl: Seq<u8>, hclen: nat)
    requires
        bytes_hold(b, w),
        0 <= p,
        cl.len() == 19,
        4 <= hclen <= 19,
        forall|s: int| 0 <= s < 19 ==> #[trigger] cl[s] < 8,
        forall|s: int| 0 <= s < 19 && clen_slot()[s] >= hclen ==> #[trigger] cl[s] == 0,
        p + 3 * hclen <= w.len(),
        w.subrange(p, p + 3 * hclen) == cat(cl_sent(cl, hclen), b3_fn()),
    ensures
        clen_lens(b, p, hclen) == cl,
{
    let v = cl_sent(cl, hclen);
    let h = b3_fn();
    lemma_clen_order();
    assert forall|i: int| 0 <= i < v.len() implies (#[trigger] h(v[i])).len() == 3 by {
        lemma_bits_of(v[i] as nat, 3);
    }
    lemma_cat_fixed(v, h, 3);
    let c = cat(v, h);
    assert forall|s: int| 0 <= s < 19 implies #[trigger] clen_lens(b, p, hclen)[s] == cl[s] by {
        let j = clen_slot()[s] as int;
        if j < hclen {
            assert(c.subrange(3 * j, 3 * j + 3) == h(v[j]));
            lemma_sub(w, p, c, 3 * j, 3);
            assert(v[j] == cl[s]);
            lemma_piece(b, w, p + 3 * j, cl[s] as nat, 3);
            lemma2_to64();
            lemma_small_mod(cl[s] as nat, 8);
        }
    }
    assert(clen_lens(b, p, hclen) =~= cl);
}

/// The bits of a dynamic block header, after the 3 block header bits.
pub open spec fn dyn_bits(cl: Seq<u8>, hclen: nat, lit: Seq<u8>, dist: Seq<u8>) -> Seq<nat> {
    bits_of((lit.len() - 257) as nat, 5) + bits_of((dist.len() - 1) as nat, 5) + bits_of((hclen - 4) as nat, 4)
        + cat(cl_sent(cl, hclen), b3_fn()) + cat(lit + dist, len_fn(cl))
}

/// What a dynamic header needs to decode as `lit` and `dist`.
pub open spec fn dyn_ok(cl: Seq<u8>, hclen: nat, lit: Seq<u8>, dist: Seq<u8>) -> bool {
    &&& 257 <= lit.len() <= 286
    &&& 1 <= dist.len() <= 30
    &&& 4 <= hclen <= 19
    &&& cl.len() == 19
    &&& forall|s: int| 0 <= s < 19 ==> #[trigger] cl[s] < 8
    &&& forall|s: int| 0 <= s < 19 && clen_slot()[s] >= hclen ==> #[trigger] cl[s] == 0
    &&& valid_lens(cl, false)
    &&& forall|i: int| 0 <= i < (lit + dist).len() ==> #[trigger] (lit + dist)[i] < 16 && 1 <= cl[(lit + dist)[i] as int]
    &&& lit[256] != 0
    &&& valid_lens(lit, true)
    &&& valid_lens(dist, true)
}

pub proof fn lemma_dynamic(b: Seq<u8>, w: Seq<nat>, p: int, cl: Seq<u8>, hclen: nat, lit: Seq<u8>, dist: Seq<u8>)
    requires
        bytes_hold(b, w),
        0 <= p,
        dyn_ok(cl, hclen, lit, dist),
        p + dyn_bits(cl, hclen, lit, dist).len() <= w.len(),
        w.subrange(p, p + dyn_bits(cl, hclen, lit, dist).len()) == dyn_bits(cl, hclen, lit, dist),
    ensures
        read_dynamic(b, p) == Some((p + dyn_bits(cl, hclen, lit, dist).len(), lit, dist)),
{
    let a1 = bits_of((lit.len() - 257) as nat, 5);
    let a2 = bits_of((dist.len() - 1) as nat, 5);
    let a3 = bits_of((hclen - 4) as nat, 4);
    let c = cat(cl_sent(cl, hclen), b3_fn());
    let l = cat(lit + dist, len_fn(cl));
    lemma_bits_of((lit.len() - 257) as nat, 5);
    lemma_bits_of((dist.len() - 1) as nat, 5);
    lemma_bits_of((hclen - 4) as nat, 4);
    lemma_clen_order();
    let v = cl_sent(cl, hclen);
    assert forall|i: int| 0 <= i < v.len() implies (#[trigger] b3_fn()(v[i])).len() == 3 by {
        lemma_bits_of(v[i] as nat, 3);
    }
    lemma_cat_fixed(v, b3_fn(), 3);
    assert(dyn_bits(cl, hclen, lit, dist) =~= a1 + (a2 + (a3 + (c + l))));
    lemma_split(w, p, a1, a2 + (a3 + (c + l)));
    lemma_split(w, p + 5, a2, a3 + (c + l));
    lemma_split(w, p + 10, a3, c + l);
    lemma_split(w, p + 14, c, l);
    lemma2_to64();
    lemma_piece(b, w, p, (lit.len() - 257) as nat, 5);
    lemma_piece(b, w, p + 5, (dist.len() - 1) as nat, 5);
    lemma_piece(b, w, p + 10, (hclen - 4) as nat, 4);
    lemma_small_mod((lit.len() - 257) as nat, 32);
    lemma_small_mod((dist.len() - 1) as nat, 32);
    lemma_small_mod((hclen - 4) as nat, 16);
    lemma_clen(b, w, p + 14, cl, hclen);
    assert(p + 14 + 3 * hclen == p + 14 + c.len());
    assert(lens_ok(cl));
    lemma_lens(b, w, p + 14 + c.len(), cl, Seq::empty(), lit + dist);
    assert(Seq::<u8>::empty() + (lit + dist) =~= lit + dist);
    assert((lit + dist).subrange(0, lit.len() as int) =~= lit);
    assert((lit + dist).subrange(lit.len() as int, (lit.len() + dist.len()) as int) =~= dist);
}


// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

/// A block as the compressor writes it: stored (`kind` 0), with the fixed
/// codes (1), or with codes it sends (2).
pub struct Blk {
    pub kind: nat,
    /// Stored: the bytes, and the 0 bits before LEN.
    pub data: Seq<u8>,
    pub pad: nat,
    /// Coded: the code length code, the codes and the tokens.
    pub cl: Seq<u8>,
    pub hclen: nat,
    pub lit: Seq<u8>,
    pub dist: Seq<u8>,
    pub ts: Seq<u32>,
}

/// LEN, NLEN and the bytes of a stored block.
pub open spec fn stored_bytes(data: Seq<u8>) -> Seq<u8> {
    let n = data.len();
    let m = (65535 - n) as nat;
    seq![(n % 256) as u8, (n / 256) as u8, (m % 256) as u8, (m / 256) as u8] + data
}

pub open spec fn block_bits(k: Blk, fin: bool) -> Seq<nat> {
    bits_of(if fin { 1 } else { 0 }, 1) + bits_of(k.kind, 2) + body_bits(k)
}

/// A block after its 3 header bits.
#[verifier::opaque]
pub open spec fn body_bits(k: Blk) -> Seq<nat> {
    if k.kind == 0 {
        bits_of(0, k.pad) + bytes_bits(stored_bytes(k.data))
    } else if k.kind == 1 {
        cat(k.ts, tok_fn(k.lit, k.dist)) + code_of(k.lit, 256)
    } else {
        dyn_bits(k.cl, k.hclen, k.lit, k.dist) + (cat(k.ts, tok_fn(k.lit, k.dist)) + code_of(k.lit, 256))
    }
}

pub open spec fn blk_out(k: Blk, out: Seq<u8>) -> Seq<u8> {
    if k.kind == 0 {
        out + k.data
    } else {
        expand(out, k.ts)
    }
}

/// The codes and tokens of a coded block.
pub open spec fn codes_ok(k: Blk, out: Seq<u8>) -> bool {
    &&& k.lit.len() > 256
    &&& lens_ok(k.lit)
    &&& lens_ok(k.dist)
    &&& 1 <= k.lit[256]
    &&& forall|i: int| 0 <= i < k.ts.len() ==> #[trigger] tok_coded(k.lit, k.dist, k.ts[i])
    &&& toks_ok(out, k.ts)
}

/// A block the decoder reads back, written at bit `p` after output `out`.
#[verifier::opaque]
pub open spec fn blk_ok(k: Blk, p: int, out: Seq<u8>) -> bool {
    if k.kind == 0 {
        &&& k.data.len() <= 65535
        &&& k.pad < 8
        &&& (p + 3 + k.pad) % 8 == 0
    } else if k.kind == 1 {
        &&& k.lit == fixed_lit_lens()
        &&& k.dist == fixed_dist_lens()
        &&& codes_ok(k, out)
    } else {
        &&& k.kind == 2
        &&& dyn_ok(k.cl, k.hclen, k.lit, k.dist)
        &&& codes_ok(k, out)
    }
}

/// Written bits at `p`, read as the bits of `x` from `q`.
pub proof fn lemma_wsub(w: Seq<nat>, p: int, x: Seq<nat>, q: int, n: nat)
    requires
        0 <= p,
        p + x.len() <= w.len(),
        w.subrange(p, p + x.len()) == x,
        0 <= q,
        q + n <= x.len(),
    ensures
        wbits(w, p + q, n) == wbits(x, q, n),
{
    let pre = w.subrange(0, p);
    let rest = w.subrange(p + x.len(), w.len() as int);
    assert(w =~= pre + x + rest);
    lemma_wbits_prefix(pre + x, rest, p + q, n);
    lemma_wbits_suffix(pre, x, q, n);
}

proof fn lemma_stored_step(b: Seq<u8>, w: Seq<nat>, p: int, out: Seq<u8>, k: Blk)
    requires
        bytes_hold(b, w),
        0 <= p,
        k.kind == 0,
        k.data.len() <= 65535,
        k.pad < 8,
        (p + 3 + k.pad) % 8 == 0,
        p + 3 + k.pad + bytes_bits(stored_bytes(k.data)).len() <= w.len(),
        w.subrange(p + 3 + k.pad, p + 3 + k.pad + bytes_bits(stored_bytes(k.data)).len()) == bytes_bits(stored_bytes(k.data)),
    ensures
        inflate_stored(b, p + 3, out) == Some((p + 3 + k.pad + bytes_bits(stored_bytes(k.data)).len(), out + k.data)),
{
    let sb = stored_bytes(k.data);
    let x = bytes_bits(sb);
    lemma_bytes_bits(sb);
    let q = p + 3 + k.pad;
    let m = q / 8;
    assert(q == 8 * m);
    assert((p + 3 + 7) / 8 == m);
    assert forall|j: int| 0 <= j < sb.len() implies b[m + j] == #[trigger] sb[j] by {
        assert(8 * (m + j) == q + 8 * j);
        lemma_wsub(w, q, x, 8 * j, 8);
        assert(0 <= m + j < b.len());
        assert(b[m + j] as nat == wbits(w, 8 * (m + j), 8));
    }
    let n = k.data.len();
    assert(b[m + 0] == sb[0] && b[m + 1] == sb[1] && b[m + 2] == sb[2] && b[m + 3] == sb[3]);
    assert(m + 0 == m);
    assert(b.subrange(m + 4, m + 4 + n as int) =~= k.data) by {
        assert forall|j: int| 0 <= j < n implies #[trigger] b.subrange(m + 4, m + 4 + n as int)[j] == k.data[j] by {
            assert(b[m + (4 + j)] == sb[4 + j]);
            assert(m + (4 + j) == m + 4 + j);
        }
    }
}

/// The 3 block header bits, then the rest.
proof fn lemma_head(b: Seq<u8>, w: Seq<nat>, p: int, fin: bool, kind: nat, y: Seq<nat>)
    requires
        bytes_hold(b, w),
        0 <= p,
        kind < 4,
        p + 3 + y.len() <= w.len(),
        w.subrange(p, p + 3 + y.len()) == bits_of(if fin { 1 } else { 0 }, 1) + bits_of(kind, 2) + y,
    ensures
        bits(b, p, 1) == if fin { 1nat } else { 0nat },
        bits(b, p + 1, 2) == kind,
        w.subrange(p + 3, p + 3 + y.len()) == y,
        p + 3 <= nbits(b),
{
    let f = bits_of(if fin { 1 } else { 0 }, 1);
    let t = bits_of(kind, 2);
    lemma_bits_of(if fin { 1 } else { 0 }, 1);
    lemma_bits_of(kind, 2);
    lemma2_to64();
    assert(f + t + y =~= f + (t + y));
    lemma_split(w, p, f, t + y);
    lemma_split(w, p + 1, t, y);
    lemma_piece(b, w, p, if fin { 1 } else { 0 }, 1);
    lemma_piece(b, w, p + 1, kind, 2);
    lemma_small_mod(kind, 4);
}

proof fn lemma_body_stored(b: Seq<u8>, w: Seq<nat>, p: int, out: Seq<u8>, k: Blk)
    requires
        bytes_hold(b, w),
        0 <= p,
        k.kind == 0,
        blk_ok(k, p, out),
        p + 3 + body_bits(k).len() <= w.len(),
        w.subrange(p + 3, p + 3 + body_bits(k).len()) == body_bits(k),
    ensures
        inflate_stored(b, p + 3, out) == Some((p + 3 + body_bits(k).len(), blk_out(k, out))),
        body_bits(k).len() >= 1,
{
    reveal(body_bits);
    reveal(blk_ok);
    lemma_bytes_bits(stored_bytes(k.data));
    let z = bits_of(0, k.pad);
    let x = bytes_bits(stored_bytes(k.data));
    lemma_bits_of(0, k.pad);
    lemma_split(w, p + 3, z, x);
    lemma_stored_step(b, w, p, out, k);
}

proof fn lemma_body_coded(b: Seq<u8>, w: Seq<nat>, p: int, out: Seq<u8>, k: Blk)
    requires
        bytes_hold(b, w),
        0 <= p,
        k.kind == 1 || k.kind == 2,
        blk_ok(k, p, out),
        p + 3 + body_bits(k).len() <= w.len(),
        w.subrange(p + 3, p + 3 + body_bits(k).len()) == body_bits(k),
    ensures
        (if k.kind == 1 {
            inflate_codes(b, p + 3, out, fixed_lit_lens(), fixed_dist_lens())
        } else {
            match read_dynamic(b, p + 3) {
                None => None,
                Some((p2, lit, dist)) => inflate_codes(b, p2, out, lit, dist),
            }
        }) == Some((p + 3 + body_bits(k).len(), blk_out(k, out))),
        body_bits(k).len() >= 1,
{
    reveal(body_bits);
    reveal(blk_ok);
    lemma_bits_of(rev(canon(k.lit, 256), k.lit[256] as nat), k.lit[256] as nat);
    if k.kind == 1 {
        lemma_codes(b, w, p + 3, out, k.ts, k.lit, k.dist);
    } else {
        let h = dyn_bits(k.cl, k.hclen, k.lit, k.dist);
        let c = cat(k.ts, tok_fn(k.lit, k.dist)) + code_of(k.lit, 256);
        lemma_split(w, p + 3, h, c);
        lemma_dynamic(b, w, p + 3, k.cl, k.hclen, k.lit, k.dist);
        lemma_codes(b, w, p + 3 + h.len(), out, k.ts, k.lit, k.dist);
    }
}

/// One block, read from `p`.
pub proof fn lemma_block(b: Seq<u8>, w: Seq<nat>, p: int, out: Seq<u8>, k: Blk, fin: bool)
    requires
        bytes_hold(b, w),
        0 <= p,
        blk_ok(k, p, out),
        p + block_bits(k, fin).len() <= w.len(),
        w.subrange(p, p + block_bits(k, fin).len()) == block_bits(k, fin),
    ensures
        block_bits(k, fin).len() > 3,
        inflate_blocks(b, p, out) == if fin {
            Some((p + block_bits(k, fin).len(), blk_out(k, out)))
        } else {
            inflate_blocks(b, p + block_bits(k, fin).len(), blk_out(k, out))
        },
{
    hide(inflate_codes);
    hide(read_dynamic);
    hide(inflate_stored);
    hide(fixed_lit_lens);
    hide(fixed_dist_lens);
    lemma_bits_of(if fin { 1 } else { 0 }, 1);
    lemma_bits_of(k.kind, 2);
    let y = body_bits(k);
    assert(k.kind < 3) by {
        reveal(blk_ok);
    }
    lemma_head(b, w, p, fin, k.kind, y);
    if k.kind == 0 {
        lemma_body_stored(b, w, p, out, k);
    } else {
        lemma_body_coded(b, w, p, out, k);
    }
    lemma_bits_of(if fin { 1 } else { 0 }, 1);
    lemma_bits_of(k.kind, 2);
}


// ---------------------------------------------------------------------------
// The stream
// ---------------------------------------------------------------------------

/// Blocks `bs` written one after another from `ps[0]`: block `i` from bit
/// `ps[i]` after output `os[i]`, only the last one final.
pub open spec fn blocks_ok(w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>) -> bool {
    let n = bs.len();
    &&& n >= 1
    &&& ps.len() == n + 1
    &&& os.len() == n + 1
    &&& 0 <= ps[0]
    &&& ps[n as int] <= w.len()
    &&& forall|i: int| 0 <= i <= n ==> #[trigger] ps[i] <= ps[n as int]
    &&& forall|i: int| 0 <= i < n ==> #[trigger] blk_ok(bs[i], ps[i], os[i])
    &&& forall|i: int| 0 <= i < n ==> #[trigger] ps[i + 1] == ps[i] + block_bits(bs[i], i == n - 1).len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] os[i + 1] == blk_out(bs[i], os[i])
    &&& forall|i: int| 0 <= i < n ==> #[trigger] w.subrange(ps[i], ps[i + 1]) == block_bits(bs[i], i == n - 1)
}

pub proof fn lemma_blocks(b: Seq<u8>, w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>, j: int)
    requires
        bytes_hold(b, w),
        blocks_ok(w, bs, ps, os),
        0 <= j < bs.len(),
        forall|i: int| 0 <= i <= j ==> #[trigger] ps[i] >= 0,
    ensures
        inflate_blocks(b, ps[j], os[j]) == Some((ps[bs.len() as int], os[bs.len() as int])),
    decreases bs.len() - j,
{
    let n = bs.len() as int;
    assert(blk_ok(bs[j], ps[j], os[j]));
    assert(ps[j + 1] == ps[j] + block_bits(bs[j], j == n - 1).len());
    assert(w.subrange(ps[j], ps[j + 1]) == block_bits(bs[j], j == n - 1));
    assert(ps[j + 1] <= ps[n]);
    assert(os[j + 1] == blk_out(bs[j], os[j]));
    lemma_block(b, w, ps[j], os[j], bs[j], j == n - 1);
    if j < n - 1 {
        assert forall|i: int| 0 <= i <= j + 1 implies #[trigger] ps[i] >= 0 by {
            if i == j + 1 {
            } else {
                assert(ps[i] >= 0);
            }
        }
        lemma_blocks(b, w, bs, ps, os, j + 1);
    }
}

/// The compressor's theorem, for raw DEFLATE: what it writes inflates to
/// the output its blocks describe, using every byte.
pub proof fn lemma_deflate(b: Seq<u8>, w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>)
    requires
        bytes_hold(b, w),
        blocks_ok(w, bs, ps, os),
        ps[0] == 0,
        os[0] == Seq::<u8>::empty(),
        w.len() < ps[bs.len() as int] + 8,
    ensures
        inflate(b) == Some((os[bs.len() as int], b.len() as int)),
{
    lemma_blocks(b, w, bs, ps, os, 0);
    let e = ps[bs.len() as int];
    assert(w.len() == 8 * b.len());
    assert((e + 7) / 8 == b.len());
}


pub proof fn lemma_bytes_bits_concat(a: Seq<u8>, c: Seq<u8>)
    ensures
        bytes_bits(a + c) == bytes_bits(a) + bytes_bits(c),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + c =~= c);
        assert(Seq::<nat>::empty() + bytes_bits(c) =~= bytes_bits(c));
    } else {
        let t = a.subrange(1, a.len() as int);
        lemma_bytes_bits_concat(t, c);
        assert((a + c).subrange(1, (a + c).len() as int) =~= t + c);
        assert((a + c)[0] == a[0]);
        assert(bits_of(a[0] as nat, 8) + (bytes_bits(t) + bytes_bits(c)) =~= bits_of(a[0] as nat, 8) + bytes_bits(t)
            + bytes_bits(c));
    }
}

/// The compressor's state: blocks `bs` written from bit `ps[i]` after
/// output `os[i]`, only the last one final once `done`.
pub open spec fn enc_inv(w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>, done: bool) -> bool {
    let n = bs.len();
    &&& ps.len() == n + 1
    &&& os.len() == n + 1
    &&& ps[n as int] == w.len()
    &&& (done ==> n >= 1)
    &&& forall|i: int| 0 <= i <= n ==> 0 <= #[trigger] ps[i] <= ps[n as int]
    &&& forall|i: int| 0 <= i < n ==> #[trigger] blk_ok(bs[i], ps[i], os[i])
    &&& forall|i: int| 0 <= i < n ==> #[trigger] ps[i + 1] == ps[i] + block_bits(bs[i], done && i == n - 1).len()
    &&& forall|i: int| 0 <= i < n ==> #[trigger] os[i + 1] == blk_out(bs[i], os[i])
    &&& forall|i: int| 0 <= i < n ==> #[trigger] w.subrange(ps[i], ps[i + 1]) == block_bits(bs[i], done && i == n - 1)
}

/// Appending a block keeps the state.
pub proof fn lemma_enc_push(w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>, k: Blk, fin: bool)
    requires
        enc_inv(w, bs, ps, os, false),
        blk_ok(k, w.len() as int, os[bs.len() as int]),
    ensures
        enc_inv(w + block_bits(k, fin), bs.push(k), ps.push((w.len() + block_bits(k, fin).len()) as int), os.push(
            blk_out(k, os[bs.len() as int]),
        ), fin),
{
    let n = bs.len() as int;
    let x = block_bits(k, fin);
    let w2 = w + x;
    let bs2 = bs.push(k);
    let ps2 = ps.push((w.len() + x.len()) as int);
    let os2 = os.push(blk_out(k, os[n]));
    assert forall|i: int| 0 <= i <= n + 1 implies 0 <= #[trigger] ps2[i] <= ps2[n + 1] by {
        if i <= n {
            assert(ps2[i] == ps[i]);
        }
    }
    assert forall|i: int| 0 <= i < n + 1 implies #[trigger] blk_ok(bs2[i], ps2[i], os2[i]) by {
        if i < n {
            assert(bs2[i] == bs[i] && ps2[i] == ps[i] && os2[i] == os[i]);
        }
    }
    assert forall|i: int| 0 <= i < n + 1 implies #[trigger] ps2[i + 1] == ps2[i] + block_bits(bs2[i], fin && i == n).len() by {
        if i < n {
            assert(bs2[i] == bs[i] && ps2[i] == ps[i] && ps2[i + 1] == ps[i + 1]);
            assert(block_bits(bs[i], false && i == n - 1) == block_bits(bs[i], fin && i == n));
        }
    }
    assert forall|i: int| 0 <= i < n + 1 implies #[trigger] os2[i + 1] == blk_out(bs2[i], os2[i]) by {
        if i < n {
            assert(bs2[i] == bs[i] && os2[i] == os[i] && os2[i + 1] == os[i + 1]);
        }
    }
    assert forall|i: int| 0 <= i < n + 1 implies #[trigger] w2.subrange(ps2[i], ps2[i + 1]) == block_bits(bs2[i], fin && i == n) by {
        if i < n {
            assert(bs2[i] == bs[i] && ps2[i] == ps[i] && ps2[i + 1] == ps[i + 1]);
            assert(ps[i + 1] <= ps[n]);
            assert(w2.subrange(ps[i], ps[i + 1]) =~= w.subrange(ps[i], ps[i + 1]));
            assert(block_bits(bs[i], false && i == n - 1) == block_bits(bs[i], fin && i == n));
        } else {
            assert(w2.subrange(w.len() as int, (w.len() + x.len()) as int) =~= x);
        }
    }
    assert((bs2.len() - 1) as int == n);
}

/// Once the final block is written and the bytes padded, they inflate to
/// the output.
pub proof fn lemma_enc_done(b: Seq<u8>, wf: Seq<nat>, w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>)
    requires
        ps[0] == 0,
        os[0] == Seq::<u8>::empty(),
        enc_inv(w, bs, ps, os, true),
        bytes_hold(b, wf),
        wf.len() >= w.len(),
        wf.len() < w.len() + 8,
        wf.subrange(0, w.len() as int) == w,
    ensures
        inflate(b) == Some((os[bs.len() as int], b.len() as int)),
{
    let n = bs.len() as int;
    assert forall|i: int| 0 <= i < n implies #[trigger] wf.subrange(ps[i], ps[i + 1]) == block_bits(bs[i], i == n - 1) by {
        assert(ps[i + 1] <= ps[n]);
        assert(wf.subrange(ps[i], ps[i + 1]) =~= w.subrange(ps[i], ps[i + 1]));
        assert(block_bits(bs[i], true && i == n - 1) == block_bits(bs[i], i == n - 1));
    }
    assert(blocks_ok(wf, bs, ps, os));
    lemma_deflate(b, wf, bs, ps, os);
}


/// A match found by comparing the data with itself `d` bytes back adds
/// the matched bytes.
pub proof fn lemma_copy_data(data: Seq<u8>, p: int, d: nat, len: nat)
    requires
        1 <= d <= p,
        p + len <= data.len(),
        forall|k: int| 0 <= k < len ==> #[trigger] data[p + k] == data[p + k - d],
    ensures
        copy_match(data.subrange(0, p), d, len) == data.subrange(0, p + len),
    decreases len,
{
    if len == 0 {
    } else {
        let out = data.subrange(0, p);
        assert(out[out.len() - d] == data[p - d]);
        assert(data[p + 0] == data[p + 0 - d]);
        assert(out.push(out[out.len() - d]) =~= data.subrange(0, p + 1));
        assert forall|k: int| 0 <= k < (len - 1) as nat implies #[trigger] data[(p + 1) + k] == data[(p + 1) + k - d] by {
            assert(data[p + (k + 1)] == data[p + (k + 1) - d]);
            assert(p + (k + 1) == (p + 1) + k);
        }
        lemma_copy_data(data, p + 1, d, (len - 1) as nat);
        assert(p + 1 + (len - 1) as nat == p + len);
    }
}


/// The blocks, read from where they start in `b`.
pub proof fn lemma_enc_done_at(b: Seq<u8>, wf: Seq<nat>, w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>)
    requires
        enc_inv(w, bs, ps, os, true),
        bytes_hold(b, wf),
        wf.len() >= w.len(),
        wf.subrange(0, w.len() as int) == w,
    ensures
        inflate_blocks(b, ps[0], os[0]) == Some((ps[bs.len() as int], os[bs.len() as int])),
{
    let n = bs.len() as int;
    assert forall|i: int| 0 <= i < n implies #[trigger] wf.subrange(ps[i], ps[i + 1]) == block_bits(bs[i], i == n - 1) by {
        assert(ps[i + 1] <= ps[n]);
        assert(wf.subrange(ps[i], ps[i + 1]) =~= w.subrange(ps[i], ps[i + 1]));
        assert(block_bits(bs[i], true && i == n - 1) == block_bits(bs[i], i == n - 1));
    }
    assert(blocks_ok(wf, bs, ps, os));
    assert forall|i: int| 0 <= i <= 0 implies #[trigger] ps[i] >= 0 by {}
    lemma_blocks(b, wf, bs, ps, os, 0);
}

/// Bytes written whole are the bytes read back.
pub proof fn lemma_bytes_at(b: Seq<u8>, w: Seq<nat>, k: int, t: Seq<u8>)
    requires
        bytes_hold(b, w),
        0 <= k,
        8 * k + 8 * t.len() <= w.len(),
        w.subrange(8 * k, 8 * k + 8 * t.len()) == bytes_bits(t),
    ensures
        b.subrange(k, k + t.len()) == t,
{
    lemma_bytes_bits(t);
    let a = w.subrange(0, 8 * k);
    let m = w.subrange(8 * k, 8 * k + 8 * t.len());
    let c = w.subrange(8 * k + 8 * t.len(), w.len() as int);
    assert(w =~= (a + m) + c);
    assert forall|j: int| 0 <= j < t.len() implies #[trigger] b.subrange(k, k + t.len())[j] == t[j] by {
        assert(b[k + j] as nat == wbits(w, 8 * (k + j), 8));
        lemma_wbits_prefix(a + m, c, 8 * k + 8 * j, 8);
        lemma_wbits_suffix(a, m, 8 * j, 8);
        assert(8 * (k + j) == a.len() + 8 * j);
    }
    assert(b.subrange(k, k + t.len()) =~= t);
}


/// A match copies the same bytes after any earlier output.
pub proof fn lemma_copy_shift(p: Seq<u8>, w: Seq<u8>, d: nat, l: nat)
    requires
        1 <= d <= w.len(),
    ensures
        copy_match(p + w, d, l) == p + copy_match(w, d, l),
    decreases l,
{
    if l > 0 {
        let x = w[w.len() - d];
        assert((p + w)[(p + w).len() - d] == x);
        assert((p + w).push(x) =~= p + w.push(x));
        lemma_copy_shift(p, w.push(x), d, (l - 1) as nat);
    }
}

/// Tokens that only refer back into `w` expand the same after `p + w`.
pub proof fn lemma_expand_shift(p: Seq<u8>, w: Seq<u8>, ts: Seq<u32>)
    requires
        toks_ok(w, ts),
    ensures
        toks_ok(p + w, ts),
        expand(p + w, ts) == p + expand(w, ts),
    decreases ts.len(),
{
    if ts.len() > 0 {
        let t = ts[0];
        if is_lit(t) {
            assert((p + w).push(t as u8) =~= p + w.push(t as u8));
        } else {
            lemma_copy_shift(p, w, tdist(t), tlen(t));
        }
        assert(apply(p + w, t) == p + apply(w, t));
        lemma_expand_shift(p, apply(w, t), ts.subrange(1, ts.len() as int));
    }
}

/// Bytes appended hold the bits appended.
pub proof fn lemma_hold_append(s: Seq<u8>, w: Seq<nat>, t: Seq<u8>)
    requires
        bytes_hold(s, w),
    ensures
        bytes_hold(s + t, w + bytes_bits(t)),
{
    let u = bytes_bits(t);
    let b = s + t;
    let w2 = w + u;
    lemma_bytes_bits(t);
    assert forall|i: int| 0 <= i < b.len() implies #[trigger] b[i] as nat == wbits(w2, 8 * i, 8) by {
        if i < s.len() {
            lemma_wbits_prefix(w, u, 8 * i, 8);
            assert(b[i] == s[i]);
        } else {
            lemma_wbits_suffix(w, u, 8 * (i - s.len()), 8);
            assert(w.len() + 8 * (i - s.len()) == 8 * i);
            assert(b[i] == t[i - s.len()]);
        }
    }
    assert forall|k: int| 0 <= k < w2.len() implies #[trigger] w2[k] < 2 by {
        if k >= w.len() {
            assert(w2[k] == u[k - w.len()]);
        } else {
            assert(w2[k] == w[k]);
        }
    }
}

/// Blocks written with none final: reading from block `j` is reading from
/// their end, whatever follows them in `b`.
pub proof fn lemma_mid_blocks(b: Seq<u8>, wf: Seq<nat>, w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>, j: int)
    requires
        enc_inv(w, bs, ps, os, false),
        bytes_hold(b, wf),
        wf.len() >= w.len(),
        wf.subrange(0, w.len() as int) == w,
        0 <= j <= bs.len(),
    ensures
        inflate_blocks(b, ps[j], os[j]) == inflate_blocks(b, ps[bs.len() as int], os[bs.len() as int]),
    decreases bs.len() - j,
{
    let n = bs.len() as int;
    if j < n {
        assert(blk_ok(bs[j], ps[j], os[j]));
        assert(ps[j + 1] == ps[j] + block_bits(bs[j], false && j == n - 1).len());
        assert(w.subrange(ps[j], ps[j + 1]) == block_bits(bs[j], false && j == n - 1));
        assert(0 <= ps[j]);
        assert(ps[j + 1] <= ps[n]);
        assert(os[j + 1] == blk_out(bs[j], os[j]));
        assert(wf.subrange(ps[j], ps[j + 1]) =~= w.subrange(ps[j], ps[j + 1]));
        lemma_block(b, wf, ps[j], os[j], bs[j], false);
        lemma_mid_blocks(b, wf, w, bs, ps, os, j + 1);
    }
}

/// The bytes of an encoder with no header that stopped on a byte boundary
/// without a final block: whatever follows them, decoding from their start
/// is decoding from their end after the blocks' output.
pub proof fn lemma_enc_piece(s: Seq<u8>, w: Seq<nat>, bs: Seq<Blk>, ps: Seq<int>, os: Seq<Seq<u8>>)
    requires
        enc_inv(w, bs, ps, os, false),
        ps[0] == 0,
        bytes_hold(s, w),
    ensures
        forall|t: Seq<u8>| #[trigger] inflate_blocks(s + t, 0, os[0]) == inflate_blocks(s + t, 8 * s.len() as int, os[bs.len() as int]),
{
    assert forall|t: Seq<u8>| #[trigger] inflate_blocks(s + t, 0, os[0]) == inflate_blocks(s + t, 8 * s.len() as int, os[bs.len() as int]) by {
        let wf = w + bytes_bits(t);
        lemma_hold_append(s, w, t);
        assert(wf.subrange(0, w.len() as int) =~= w);
        lemma_mid_blocks(s + t, wf, w, bs, ps, os, 0);
    }
}

} // verus!
