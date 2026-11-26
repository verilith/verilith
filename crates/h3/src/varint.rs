//! Variable-length integers (RFC 9000 §16): the verified decoder and
//! encoder, and the round trip.
use crate::spec::*;
use verilith_core::prims::{get, set};
use vstd::prelude::*;

verus! {

pub proof fn lemma_p256(n: nat)
    ensures
        p256(n) >= 1,
        n == 0 ==> p256(n) == 1,
        n == 1 ==> p256(n) == 256,
        n == 2 ==> p256(n) == 65536,
        n == 3 ==> p256(n) == 16777216,
        n == 4 ==> p256(n) == 4294967296,
        n == 7 ==> p256(n) == 72057594037927936,
        n == 8 ==> p256(n) == 18446744073709551616,
    decreases n,
{
    reveal_with_fuel(p256, 9);
    if n > 0 {
        lemma_p256((n - 1) as nat);
    }
}

/// `be` reads only `s[0..n]`.
pub proof fn lemma_be_prefix(s: Seq<u8>, t: Seq<u8>, n: nat)
    requires
        n <= s.len(),
        n <= t.len(),
        s.take(n as int) =~= t.take(n as int),
    ensures
        be(s, n) == be(t, n),
    decreases n,
{
    if n > 0 {
        assert(s[n - 1] == s.take(n as int)[n - 1]);
        assert(t[n - 1] == t.take(n as int)[n - 1]);
        assert(s.take(n - 1) =~= s.take(n as int).take(n - 1));
        assert(t.take(n - 1) =~= t.take(n as int).take(n - 1));
        lemma_be_prefix(s, t, (n - 1) as nat);
    }
}

pub proof fn lemma_be_bound(s: Seq<u8>, n: nat)
    requires
        n <= s.len(),
    ensures
        be(s, n) < p256(n),
    decreases n,
{
    if n > 0 {
        lemma_be_bound(s, (n - 1) as nat);
        let a = be(s, (n - 1) as nat);
        let b = s[n - 1] as nat;
        let p = p256((n - 1) as nat);
        assert(a * 256 + b < 256 * p) by (nonlinear_arith)
            requires
                a < p,
                b < 256,
        ;
    }
}

/// The first byte's share: `be(s, n) < x * 256^(n-1)` when `s[0] < x`.
pub proof fn lemma_be_first(s: Seq<u8>, n: nat, x: nat)
    requires
        1 <= n <= s.len(),
        s[0] < x,
    ensures
        be(s, n) < x * p256((n - 1) as nat),
    decreases n,
{
    if n == 1 {
        reveal_with_fuel(be, 2);
        assert(p256(0) == 1);
        assert(be(s, 1) == s[0] as nat);
        assert(x * 1 == x);
    } else {
        lemma_be_first(s, (n - 1) as nat, x);
        let a = be(s, (n - 1) as nat);
        let b = s[n - 1] as nat;
        let p = p256((n - 2) as nat);
        assert(p256((n - 1) as nat) == 256 * p);
        assert(a * 256 + b < x * (256 * p)) by (nonlinear_arith)
            requires
                a < x * p,
                b < 256,
        ;
    }
}

pub proof fn lemma_be_enc(v: nat, n: nat)
    ensures
        be_enc(v, n).len() == n,
        be(be_enc(v, n), n) == v % p256(n),
        n >= 1 ==> be_enc(v, n)[0] as nat == (v / p256((n - 1) as nat)) % 256,
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        lemma_be_enc(v / 256, m);
        let e = be_enc(v / 256, m);
        let f = be_enc(v, n);
        assert(f =~= e.push((v % 256) as u8));
        assert(f.take(m as int) =~= e.take(m as int));
        lemma_be_prefix(f, e, m);
        assert(be(f, n) == be(e, m) * 256 + (v % 256));
        lemma_p256(m);
        vstd::arithmetic::div_mod::lemma_breakdown(v as int, 256, p256(m) as int);
        assert(p256(n) == 256 * p256(m));
        assert(be(f, n) == v % p256(n)) by (nonlinear_arith)
            requires
                be(f, n) == ((v / 256) % p256(m)) * 256 + (v % 256),
                v % (256 * p256(m)) == 256 * ((v / 256) % p256(m)) + v % 256,
                p256(n) == 256 * p256(m),
        ;
        if m >= 1 {
            assert(f[0] == e[0]);
            vstd::arithmetic::div_mod::lemma_div_denominator(v as int, 256, p256((m - 1) as nat) as int);
            assert(p256(m) == 256 * p256((m - 1) as nat));
        } else {
            assert(f[0] == (v % 256) as u8);
            assert(v / 1 == v);
        }
    }
}

proof fn lemma_size(v: nat)
    requires
        v <= MAX_VARINT,
    ensures
        v < 64 * p256((var_size(v) - 1) as nat),
        var_size(v) == 1 || var_size(v) == 2 || var_size(v) == 4 || var_size(v) == 8,
{
    lemma_p256(0);
    lemma_p256(1);
    lemma_p256(3);
    lemma_p256(7);
}

/// The encoding is a varint of `var_size(v)` bytes whose value is `v`.
pub proof fn lemma_var_enc(v: nat)
    requires
        v <= MAX_VARINT,
    ensures
        var_enc(v).len() == var_size(v),
        var_len(var_enc(v)[0]) == var_size(v),
        var_dec(var_enc(v)) == Var::Ok(v, var_size(v)),
{
    let n = var_size(v);
    lemma_size(v);
    lemma_be_enc(v, n);
    let b = be_enc(v, n);
    let m = (n - 1) as nat;
    lemma_p256(m);
    vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(v as int, 1, p256(m) as int);
    assert(v / p256(m) < 64) by {
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(v as int, p256(m) as int, 64);
    }
    vstd::arithmetic::div_mod::lemma_small_mod(v / p256(m), 256);
    assert(b[0] < 64);
    let e = var_enc(v);
    assert(e[0] == (b[0] + var_tag(n)) as u8);
    assert(var_len(e[0]) == n);
    assert(e.update(0, e[0] % 64) =~= b);
    assert(v < p256(n)) by {
        assert(p256(n) == 256 * p256(m));
    }
    vstd::arithmetic::div_mod::lemma_small_mod(v, p256(n));
}

/// A varint read from `s` is still read the same once more bytes follow
/// it, and from any prefix of `s` that holds it.
pub proof fn lemma_var_ext(s: Seq<u8>, t: Seq<u8>)
    requires
        var_dec(s) is Ok,
        t.len() >= var_dec(s)->Ok_1,
        t.take(var_dec(s)->Ok_1 as int) =~= s.take(var_dec(s)->Ok_1 as int),
    ensures
        var_dec(t) == var_dec(s),
{
    let n = var_dec(s)->Ok_1;
    assert(n >= 1);
    assert forall|i: int| 0 <= i < n implies #[trigger] t[i] == s[i] by {
        assert(t[i] == t.take(n as int)[i]);
        assert(s[i] == s.take(n as int)[i]);
    }
    let su = s.update(0, s[0] % 64);
    let tu = t.update(0, t[0] % 64);
    assert(su.take(n as int) =~= tu.take(n as int));
    lemma_be_prefix(su, tu, n);
}

/// A varint at `b[p..]`.
pub open spec fn var_at(b: Seq<u8>, p: int) -> Var {
    var_dec(b.skip(p))
}

/// Reads the varint at `b[p..]`: `None` if `b` ends inside it.
#[inline(always)]
pub fn read_var(b: &[u8], p: usize) -> (r: Option<(u64, usize)>)
    requires
        p <= b@.len(),
    ensures
        match var_dec(b@.skip(p as int)) {
            Var::Short => r is None,
            Var::Ok(v, n) => r matches Some((rv, e)) && rv as nat == v && e as nat == p + n && v <= MAX_VARINT && 1 <= n <= 8 && p + n <= b@.len(),
        },
        r matches Some((v, e)) ==> v <= MAX_VARINT && p < e <= b@.len() && e <= p + 8,
{
    let ghost s = b@.skip(p as int);
    let len = b.len();
    if p >= len {
        return None;
    }
    let first = get(b, p);
    let x = (first % 64) as u64;
    let ghost su = s.update(0, s[0] % 64);
    assert(s[0] == first);
    proof {
        reveal_with_fuel(be, 9);
        lemma_p256(0);
    }
    if first < 0x40 {
        assert(be(su, 1) == x);
        return Some((x, p + 1));
    }
    if first < 0x80 {
        if b.len() - p < 2 {
            return None;
        }
        let v = x * 256 + get(b, p + 1) as u64;
        assert(su[1] == b@[p + 1]);
        assert(be(su, 2) == v);
        return Some((v, p + 2));
    }
    if first < 0xc0 {
        if b.len() - p < 4 {
            return None;
        }
        let b1 = get(b, p + 1) as u64;
        let b2 = get(b, p + 2) as u64;
        let b3 = get(b, p + 3) as u64;
        assert(x * 256 + b1 < 16384) by (nonlinear_arith) requires x < 64, b1 < 256;
        assert((x * 256 + b1) * 256 + b2 < 4194304) by (nonlinear_arith) requires x * 256 + b1 < 16384, b2 < 256;
        let v = ((x * 256 + b1) * 256 + b2) * 256 + b3;
        assert(v < 0x4000_0000) by (nonlinear_arith) requires v == ((x * 256 + b1) * 256 + b2) * 256 + b3, (x * 256 + b1) * 256 + b2 < 4194304, b3 < 256;
        assert(su[1] == b@[p + 1] && su[2] == b@[p + 2] && su[3] == b@[p + 3]);
        assert(be(su, 4) == v);
        return Some((v, p + 4));
    }
    if b.len() - p < 8 {
        return None;
    }
    let mut v = x;
    let mut i: usize = 1;
    while i < 8
        invariant
            1 <= i <= 8,
            p + 8 <= b@.len(),
            len == b@.len(),
            s == b@.skip(p as int),
            su == s.update(0, s[0] % 64),
            x == su[0],
            v as nat == be(su, i as nat),
            v < 64 * p256((i - 1) as nat),
        decreases 8 - i,
    {
        let c = get(b, p + i) as u64;
        assert(su[i as int] == b@[p + i]);
        proof {
            lemma_p256((i - 1) as nat);
            assert(p256(i as nat) == 256 * p256((i - 1) as nat));
            assert(64 * p256(i as nat) <= 64 * p256(7)) by {
                lemma_p256_mono(i as nat, 7);
            }
            lemma_p256(7);
            assert(v * 256 + c < 64 * p256(i as nat)) by (nonlinear_arith)
                requires
                    v < 64 * p256((i - 1) as nat),
                    c < 256,
                    p256(i as nat) == 256 * p256((i - 1) as nat),
            ;
        }
        v = v * 256 + c;
        i = i + 1;
    }
    proof {
        lemma_p256(7);
    }
    Some((v, p + 8))
}

pub proof fn lemma_p256_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        p256(a) <= p256(b),
    decreases b,
{
    if a < b {
        lemma_p256_mono(a, (b - 1) as nat);
        lemma_p256((b - 1) as nat);
    }
}

/// The length of `v`'s encoding.
#[inline(always)]
pub fn var_size_of(v: u64) -> (r: usize)
    ensures
        r == var_size(v as nat),
{
    if v < 0x40 {
        1
    } else if v < 0x4000 {
        2
    } else if v < 0x4000_0000 {
        4
    } else {
        8
    }
}

/// Writes `v`'s encoding at `out[at..]`; returns its end.
#[inline(always)]
pub fn put_var(out: &mut [u8], at: usize, v: u64) -> (r: usize)
    requires
        v <= MAX_VARINT,
        at + var_size(v as nat) <= old(out)@.len(),
    ensures
        r == at + var_size(v as nat),
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(at as int, r as int) == var_enc(v as nat),
        final(out)@.subrange(0, at as int) == old(out)@.subrange(0, at as int),
        final(out)@.subrange(r as int, final(out)@.len() as int) == old(out)@.subrange(r as int, old(out)@.len() as int),
{
    let n = var_size_of(v);
    let len = out.len();
    let ghost e = var_enc(v as nat);
    proof {
        lemma_var_enc(v as nat);
        lemma_be_enc(v as nat, n as nat);
        reveal_with_fuel(be_enc, 9);
        lemma_p256(0);
        lemma_p256(1);
        lemma_p256(2);
        lemma_p256(3);
    }
    if n == 1 {
        set(out, at, v as u8);
        assert(final(out)@.subrange(at as int, at + 1) =~= e);
    } else if n == 2 {
        let b0 = (v / 256) as u8 + 0x40;
        set(out, at, b0);
        set(out, at + 1, (v % 256) as u8);
        assert(e[0] == b0 && e[1] == (v % 256) as u8);
        assert(final(out)@.subrange(at as int, at + 2) =~= e);
    } else if n == 4 {
        assert(v / 16777216 < 64);
        let b0 = (v / 16777216) as u8 + 0x80;
        set(out, at, b0);
        set(out, at + 1, (v / 65536 % 256) as u8);
        set(out, at + 2, (v / 256 % 256) as u8);
        set(out, at + 3, (v % 256) as u8);
        proof {
            let r = be_enc(v as nat, 4);
            assert(be_enc(v as nat, 4) == be_enc((v / 256) as nat, 3).push((v % 256) as u8));
            assert(be_enc((v / 256) as nat, 3) == be_enc((v / 256 / 256) as nat, 2).push((v / 256 % 256) as u8));
            assert(be_enc((v / 256 / 256) as nat, 2) == be_enc((v / 256 / 256 / 256) as nat, 1).push((v / 256 / 256 % 256) as u8));
            assert(v / 256 / 256 == v / 65536) by {
                vstd::arithmetic::div_mod::lemma_div_denominator(v as int, 256, 256);
            }
            assert(v / 65536 / 256 == v / 16777216) by {
                vstd::arithmetic::div_mod::lemma_div_denominator(v as int, 65536, 256);
            }
            assert(e[1] == r[1] && e[2] == r[2] && e[3] == r[3]);
        }
        assert(final(out)@.subrange(at as int, at + 4) =~= e);
    } else {
        let mut i: usize = 8;
        let mut w = v;
        proof {
            lemma_be_enc(v as nat, 8);
            assert(v as nat / 1 == v as nat);
        }
        let ghost o = out@;
        while i > 1
            invariant
                1 <= i <= 8,
                at + 8 <= out@.len(),
                len == out@.len(),
                be_enc(v as nat, 8).len() == 8,
                out@.len() == o.len(),
                w as nat == v as nat / p256((8 - i) as nat),
                forall|j: int| at + i <= j < at + 8 ==> #[trigger] out@[j] == be_enc(v as nat, 8)[j - at],
                forall|j: int| 0 <= j < at + 1 || at + 8 <= j < o.len() ==> #[trigger] out@[j] == o[j],
            decreases i,
        {
            i = i - 1;
            set(out, at + i, (w % 256) as u8);
            proof {
                lemma_be_enc_byte(v as nat, 8, i as nat);
                lemma_p256((7 - i) as nat);
                vstd::arithmetic::div_mod::lemma_div_denominator(v as int, p256((7 - i) as nat) as int, 256);
                assert(p256((8 - i) as nat) == p256((7 - i) as nat) * 256) by {
                    lemma_p256((8 - i) as nat);
                }
            }
            w = w / 256;
        }
        proof {
            lemma_be_enc_byte(v as nat, 8, 0);
            lemma_p256(7);
            vstd::arithmetic::div_mod::lemma_multiply_divide_lt(v as int, p256(7) as int, 64);
            vstd::arithmetic::div_mod::lemma_small_mod(w as nat, 256);
        }
        assert(w < 64);
        set(out, at, w as u8 + 0xc0);
        assert(final(out)@.subrange(at as int, at + 8) =~= e);
    }
    assert(final(out)@.subrange(0, at as int) =~= old(out)@.subrange(0, at as int));
    assert(final(out)@.subrange((at + n) as int, final(out)@.len() as int) =~= old(out)@.subrange((at + n) as int, old(out)@.len() as int));
    at + n
}

/// Byte `i` of the `n`-byte big-endian encoding of `v`.
pub proof fn lemma_be_enc_byte(v: nat, n: nat, i: nat)
    requires
        i < n,
    ensures
        be_enc(v, n).len() == n,
        be_enc(v, n)[i as int] as nat == (v / p256((n - 1 - i) as nat)) % 256,
    decreases n,
{
    lemma_be_enc(v, n);
    let m = (n - 1) as nat;
    if i == m {
        assert(be_enc(v, n)[i as int] == (v % 256) as u8);
        lemma_p256(0);
        assert(v / 1 == v);
    } else {
        lemma_be_enc_byte(v / 256, m, i);
        lemma_p256((m - 1 - i) as nat);
        assert(be_enc(v, n)[i as int] == be_enc(v / 256, m)[i as int]);
        vstd::arithmetic::div_mod::lemma_div_denominator(v as int, 256, p256((m - 1 - i) as nat) as int);
        lemma_p256((n - 1 - i) as nat);
    }
}

} // verus!
