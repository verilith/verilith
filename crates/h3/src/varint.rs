//! Variable-length integers (RFC 9000 §16): the verified decoder and
//! encoder, and the round trip.
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::varint::{b8, varint, varint_enc, varint_size, vlen};
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

/// One step of a big-endian value: `x * 256 + c` is `x` shifted up a byte
/// with `c` in the low byte.
proof fn lemma_step(x: u64, c: u64)
    requires
        x < 0x100_0000_0000_0000,
        c < 256,
    ensures
        (x * 256 + c) as nat == x as nat * 256 + c as nat,
        ((x << 8u64) | c) == (x * 256 + c) as u64,
        x * 256 + c < 0x1_0000_0000_0000_0000,
{
    assert(((x << 8u64) | c) == (x * 256 + c) as u64) by (bit_vector)
        requires
            x < 0x100_0000_0000_0000,
            c < 256,
    ;
    assert(x * 256 + c < 0x1_0000_0000_0000_0000) by (nonlinear_arith)
        requires
            x < 0x100_0000_0000_0000,
            c < 256,
    ;
}

/// `var_dec` (this crate's statement, in arithmetic) and verilith-core's
/// `varint` (RFC 9000's, in bit operations) read the same varint.
pub proof fn lemma_var_core(b: Seq<u8>, p: int)
    requires
        0 <= p <= b.len(),
    ensures
        match var_dec(b.skip(p)) {
            Var::Short => varint(b, p) is None,
            Var::Ok(v, n) => varint(b, p) matches Some((x, e)) && x as nat == v && e == p + n,
        },
{
    let s = b.skip(p);
    if p == b.len() {
        assert(s.len() == 0);
        return;
    }
    assert(s[0] == b[p]);
    let n = var_len(s[0]);
    assert(n == vlen(b[p]));
    if s.len() < n {
        return;
    }
    let su = s.update(0, s[0] % 64);
    reveal_with_fuel(be, 9);
    let c0 = b[p];
    let x0 = (c0 as u64) & 0x3f;
    assert(x0 == (c0 % 64) as u64 && x0 < 64) by (bit_vector)
        requires
            x0 == (c0 as u64) & 0x3f,
    ;
    assert(su[0] as nat == x0 as nat);
    if n == 1 {
        return;
    }
    assert(forall|k: int| 1 <= k < n ==> #[trigger] su[k] == b[p + k]);
    let x1 = b[p + 1] as u64;
    lemma_step(x0, x1);
    let y1 = (x0 * 256 + x1) as u64;
    assert(be(su, 2) == y1 as nat);
    if n == 2 {
        return;
    }
    let x2 = b[p + 2] as u64;
    let x3 = b[p + 3] as u64;
    lemma_step(y1, x2);
    let y2 = (y1 * 256 + x2) as u64;
    lemma_step(y2, x3);
    let y3 = (y2 * 256 + x3) as u64;
    assert(be(su, 4) == y3 as nat);
    if n == 4 {
        assert(y3 == (x0 << 24u64) | (x1 << 16u64) | (x2 << 8u64) | x3) by (bit_vector)
            requires
                x0 < 64 && x1 < 256 && x2 < 256 && x3 < 256,
                y1 == (x0 << 8u64) | x1,
                y2 == (y1 << 8u64) | x2,
                y3 == (y2 << 8u64) | x3,
        ;
        return;
    }
    let x4 = b[p + 4] as u64;
    let x5 = b[p + 5] as u64;
    let x6 = b[p + 6] as u64;
    let x7 = b[p + 7] as u64;
    assert(y3 < 0x4000_0000) by (bit_vector)
        requires
            x0 < 64 && x1 < 256 && x2 < 256 && x3 < 256,
            y1 == (x0 << 8u64) | x1,
            y2 == (y1 << 8u64) | x2,
            y3 == (y2 << 8u64) | x3,
    ;
    lemma_step(y3, x4);
    let y4 = (y3 * 256 + x4) as u64;
    assert(y4 < 0x40_0000_0000) by (bit_vector)
        requires
            y3 < 0x4000_0000 && x4 < 256,
            y4 == (y3 << 8u64) | x4,
    ;
    lemma_step(y4, x5);
    let y5 = (y4 * 256 + x5) as u64;
    assert(y5 < 0x4000_0000_0000) by (bit_vector)
        requires
            y4 < 0x40_0000_0000 && x5 < 256,
            y5 == (y4 << 8u64) | x5,
    ;
    lemma_step(y5, x6);
    let y6 = (y5 * 256 + x6) as u64;
    assert(y6 < 0x40_0000_0000_0000) by (bit_vector)
        requires
            y5 < 0x4000_0000_0000 && x6 < 256,
            y6 == (y5 << 8u64) | x6,
    ;
    lemma_step(y6, x7);
    let y7 = (y6 * 256 + x7) as u64;
    assert(be(su, 8) == y7 as nat);
    assert(y7 == (x0 << 56u64) | (x1 << 48u64) | (x2 << 40u64) | (x3 << 32u64) | (x4 << 24u64) | (x5
        << 16u64) | (x6 << 8u64) | x7) by (bit_vector)
        requires
            x0 < 64 && x1 < 256 && x2 < 256 && x3 < 256 && x4 < 256 && x5 < 256 && x6 < 256 && x7
                < 256,
            y1 == (x0 << 8u64) | x1,
            y2 == (y1 << 8u64) | x2,
            y3 == (y2 << 8u64) | x3,
            y4 == (y3 << 8u64) | x4,
            y5 == (y4 << 8u64) | x5,
            y6 == (y5 << 8u64) | x6,
            y7 == (y6 << 8u64) | x7,
    ;
}

/// Reads the varint at `b[p..]`: `None` if `b` ends inside it. The reader
/// is verilith-core's, shared with QUIC.
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
    let r = verilith_core::varint::read(b, p);
    proof {
        lemma_var_core(b@, p as int);
        verilith_core::varint::lemma_varint_bound(b@, p as int);
    }
    r
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

/// Byte `k` of `v` (from the least significant) by shifts and by division.
proof fn lemma_b8(v: u64)
    ensures
        b8(v) as nat == v as nat % 256,
        b8(v >> 8u64) as nat == (v as nat / 0x100) % 256,
        b8(v >> 16u64) as nat == (v as nat / 0x1_0000) % 256,
        b8(v >> 24u64) as nat == (v as nat / 0x100_0000) % 256,
        b8(v >> 32u64) as nat == (v as nat / 0x1_0000_0000) % 256,
        b8(v >> 40u64) as nat == (v as nat / 0x100_0000_0000) % 256,
        b8(v >> 48u64) as nat == (v as nat / 0x1_0000_0000_0000) % 256,
        b8(v >> 56u64) as nat == (v as nat / 0x100_0000_0000_0000) % 256,
{
    assert(v as u8 == (v % 256) as u8 && (v >> 8u64) as u8 == ((v / 0x100) % 256) as u8 && (v
        >> 16u64) as u8 == ((v / 0x1_0000) % 256) as u8 && (v >> 24u64) as u8 == ((v / 0x100_0000)
        % 256) as u8 && (v >> 32u64) as u8 == ((v / 0x1_0000_0000) % 256) as u8 && (v >> 40u64) as u8
        == ((v / 0x100_0000_0000) % 256) as u8 && (v >> 48u64) as u8 == ((v / 0x1_0000_0000_0000)
        % 256) as u8 && (v >> 56u64) as u8 == ((v / 0x100_0000_0000_0000) % 256) as u8)
        by (bit_vector);
}

/// This crate's encoding of `v` is verilith-core's.
pub proof fn lemma_enc_core(v: u64)
    requires
        v <= MAX_VARINT,
    ensures
        var_size(v as nat) == varint_size(v),
        var_enc(v as nat) == varint_enc(v),
{
    let x = v as nat;
    let n = var_size(x);
    lemma_var_enc(x);
    lemma_size(x);
    lemma_b8(v);
    reveal_with_fuel(p256, 9);
    assert(p256(0) == 1 && p256(1) == 0x100 && p256(2) == 0x1_0000 && p256(3) == 0x100_0000) by (compute);
    assert(p256(4) == 0x1_0000_0000 && p256(5) == 0x100_0000_0000 && p256(6) == 0x1_0000_0000_0000
        && p256(7) == 0x100_0000_0000_0000) by (compute);
    let be = be_enc(x, n);
    let e = var_enc(x);
    let c = varint_enc(v);
    assert forall|i: int| 0 <= i < n implies #[trigger] be[i] as nat == (x / p256((n - 1 - i) as nat)) % 256 by {
        lemma_be_enc_byte(x, n, i as nat);
    }
    // The first byte: the tag, then the top bits, which are below 64.
    let top = x / p256((n - 1) as nat);
    assert(top < 64) by {
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(x as int, p256((n - 1) as nat) as int, 64);
    }
    vstd::arithmetic::div_mod::lemma_small_mod(top, 256);
    assert(e[0] == (be[0] + var_tag(n)) as u8);
    if n == 1 {
        assert(v < 0x40);
        assert(e =~= c);
    } else if n == 2 {
        assert(b8(0x40 | (v >> 8u64)) == ((v >> 8u64) + 0x40) as u8 && (v >> 8u64) as nat == x / 0x100) by {
            assert(0x40 <= v < 0x4000 ==> b8(0x40 | (v >> 8u64)) == ((v >> 8u64) + 0x40) as u8 && v >> 8u64 == v / 0x100) by (bit_vector);
        }
        assert(e =~= c);
    } else if n == 4 {
        assert(b8(0x80 | (v >> 24u64)) == ((v >> 24u64) + 0x80) as u8 && (v >> 24u64) as nat == x / 0x100_0000) by {
            assert(0x4000 <= v < 0x4000_0000 ==> b8(0x80 | (v >> 24u64)) == ((v >> 24u64) + 0x80) as u8 && v >> 24u64 == v / 0x100_0000) by (bit_vector);
        }
        assert(e =~= c);
    } else {
        assert(b8(0xc0 | (v >> 56u64)) == ((v >> 56u64) + 0xc0) as u8 && (v >> 56u64) as nat == x / 0x100_0000_0000_0000) by {
            assert(0x4000_0000 <= v < 0x4000_0000_0000_0000 ==> b8(0xc0 | (v >> 56u64)) == ((v >> 56u64) + 0xc0) as u8 && v >> 56u64 == v / 0x100_0000_0000_0000) by (bit_vector);
        }
        assert(e =~= c);
    }
}

/// The length of `v`'s encoding.
#[inline(always)]
pub fn var_size_of(v: u64) -> (r: usize)
    ensures
        r == var_size(v as nat),
{
    verilith_core::varint::size(v)
}

/// Writes `v`'s encoding at `out[at..]`; returns its end. The writer is
/// verilith-core's, shared with QUIC.
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
    proof {
        lemma_enc_core(v);
    }
    verilith_core::varint::put(out, at, v)
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
