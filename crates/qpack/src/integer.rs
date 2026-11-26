//! Prefixed integers (RFC 9204 §4.1.1, RFC 7541 §5.1): the verified
//! decoder and encoder, and the round trip between them.
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub enum IntE {
    Short,
    Bad,
    Ok(u64, usize),
}

pub open spec fn int_matches(r: IntE, s: IntR) -> bool {
    match (r, s) {
        (IntE::Short, IntR::Short) => true,
        (IntE::Bad, IntR::Bad) => true,
        (IntE::Ok(v, e), IntR::Ok(sv, se)) => v as nat == sv && e as int == se,
        _ => false,
    }
}

pub const P128: [u64; 9] = [1, 128, 16384, 2097152, 268435456, 34359738368, 4398046511104, 562949953421312, 72057594037927936];

pub const P2: [u64; 9] = [1, 2, 4, 8, 16, 32, 64, 128, 256];

pub proof fn lemma_pows()
    ensures
        forall|i: int| 0 <= i < 9 ==> #[trigger] P128@[i] as nat == p128(i as nat),
        forall|i: int| 0 <= i < 9 ==> #[trigger] P2@[i] as nat == p2(i as nat),
        forall|i: int| 0 <= i < 9 ==> #[trigger] P128@[i] <= 72057594037927936,
{
    assert(p128(0) == 1);
    assert(p128(1) == 128) by (compute);
    assert(p128(2) == 16384) by (compute);
    assert(p128(3) == 2097152) by (compute);
    assert(p128(4) == 268435456) by (compute);
    assert(p128(5) == 34359738368) by (compute);
    assert(p128(6) == 4398046511104) by (compute);
    assert(p128(7) == 562949953421312) by (compute);
    assert(p128(8) == 72057594037927936) by (compute);
    assert(p2(0) == 1);
    assert(p2(1) == 2) by (compute);
    assert(p2(2) == 4) by (compute);
    assert(p2(3) == 8) by (compute);
    assert(p2(4) == 16) by (compute);
    assert(p2(5) == 32) by (compute);
    assert(p2(6) == 64) by (compute);
    assert(p2(7) == 128) by (compute);
    assert(p2(8) == 256) by (compute);
}

/// Decodes the integer with an `n`-bit prefix at `b[pos]`.
#[inline(always)]
pub fn decode(b: &[u8], pos: usize, n: u8) -> (r: IntE)
    requires
        1 <= n <= 8,
    ensures
        int_matches(r, int_dec(b@, pos as int, n as nat)),
        r matches IntE::Ok(v, e) ==> pos < e <= b@.len() && v <= MAX_INT,
{
    proof {
        lemma_pows();
    }
    if pos >= b.len() {
        return IntE::Short;
    }
    let k = P2[n as usize] - 1;
    let first = (b[pos] as u64) % P2[n as usize];
    if first < k {
        return IntE::Ok(first, pos + 1);
    }
    let mut acc: u64 = k;
    let mut p = pos + 1;
    let mut i: usize = 0;
    while p < b.len()
        invariant
            pos < p <= b@.len(),
            i <= 9,
            acc <= MAX_INT,
            int_dec(b@, pos as int, n as nat) == int_tail(b@, p as int, i as nat, acc as nat),
            forall|j: int| 0 <= j < 9 ==> #[trigger] P128@[j] as nat == p128(j as nat),
            forall|j: int| 0 <= j < 9 ==> #[trigger] P128@[j] <= 72057594037927936,
        decreases b@.len() - p,
    {
        if i >= 9 {
            return IntE::Bad;
        }
        let x = b[p];
        let m = P128[i];
        let lo = (x % 128) as u64;
        assert(lo * m <= 127 * 72057594037927936) by (nonlinear_arith)
            requires
                lo <= 127,
                m <= 72057594037927936,
        ;
        let add = lo * m;
        if add > MAX_INT - acc {
            return IntE::Bad;
        }
        acc = acc + add;
        if x < 128 {
            return IntE::Ok(acc, p + 1);
        }
        p = p + 1;
        i = i + 1;
    }
    IntE::Short
}

/// Appends the encoding of `v` with an `n`-bit prefix under `flags`.
#[inline(always)]
pub fn encode(out: &mut Vec<u8>, flags: u8, n: u8, v: u64)
    requires
        1 <= n <= 8,
        (flags as nat) % p2(n as nat) == 0,
    ensures
        final(out)@ == old(out)@ + int_enc(flags as nat, n as nat, v as nat),
{
    proof {
        lemma_pows();
    }
    let k = P2[n as usize] - 1;
    proof {
        assert(P2@[n as int] as nat == p2(n as nat));
        lemma_flags(flags as nat, n as nat, k as nat);
    }
    if v < k {
        out.push(flags + v as u8);
        return;
    }
    out.push(flags + k as u8);
    let ghost o0 = out@;
    let mut x = v - k;
    proof {
        assert(int_enc(flags as nat, n as nat, v as nat) == seq![(flags as nat + k) as u8] + int_enc_tail(x as nat));
        assert(o0 == old(out)@ + seq![(flags as nat + k) as u8]);
    }
    while x >= 128
        invariant
            int_enc_tail((v - k) as nat) =~= out@.subrange(o0.len() as int, out@.len() as int) + int_enc_tail(x as nat),
            o0.len() <= out@.len(),
            out@.subrange(0, o0.len() as int) == o0,
        decreases x,
    {
        let ghost o1 = out@;
        out.push((x % 128) as u8 + 128);
        proof {
            assert(int_enc_tail(x as nat) == seq![(x as nat % 128 + 128) as u8] + int_enc_tail(x as nat / 128));
            assert(out@.subrange(o0.len() as int, out@.len() as int) =~= o1.subrange(o0.len() as int, o1.len() as int).push((x % 128 + 128) as u8));
            assert(out@.subrange(0, o0.len() as int) =~= o1.subrange(0, o0.len() as int));
        }
        x = x / 128;
    }
    let ghost o1 = out@;
    out.push(x as u8);
    proof {
        assert(out@.subrange(o0.len() as int, out@.len() as int) =~= o1.subrange(o0.len() as int, o1.len() as int).push(x as u8));
        assert(out@.subrange(0, o0.len() as int) =~= o1.subrange(0, o0.len() as int));
        assert(out@ =~= out@.subrange(0, o0.len() as int) + out@.subrange(o0.len() as int, out@.len() as int));
    }
}

// ---------------------------------------------------------------------------
// The round trip
// ---------------------------------------------------------------------------

proof fn lemma_tail_rt(v: nat, rest: Seq<u8>, i: nat, acc: nat)
    requires
        i < 9,
        acc + v * p128(i) <= MAX_INT,
        v * p128(i) < p128(9),
    ensures
        int_tail(int_enc_tail(v) + rest, 0, i, acc) == IntR::Ok(acc + v * p128(i), int_enc_tail(v).len() as int),
        int_enc_tail(v).len() >= 1,
    decreases v,
{
    let e = int_enc_tail(v);
    let b = e + rest;
    if v < 128 {
        assert(b[0] == v as u8);
        assert((v as u8) as nat % 128 == v);
    } else {
        let byte = (v % 128 + 128) as u8;
        let t = int_enc_tail(v / 128);
        assert(e == seq![byte] + t);
        assert(b[0] == byte);
        assert(byte as nat % 128 == v % 128);
        assert(p128(i + 1) == 128 * p128(i));
        assert(v * p128(i) >= p128(i + 1)) by (nonlinear_arith)
            requires
                v >= 128,
                p128(i + 1) == 128 * p128(i),
        ;
        if i + 1 >= 9 {
            assert(i + 1 == 9);
            assert(false);
        }
        let acc2 = acc + (v % 128) * p128(i);
        assert(acc2 + (v / 128) * p128(i + 1) == acc + v * p128(i)) by (nonlinear_arith)
            requires
                acc2 == acc + (v % 128) * p128(i),
                p128(i + 1) == 128 * p128(i),
                v == 128 * (v / 128) + v % 128,
        ;
        assert((v / 128) * p128(i + 1) <= v * p128(i)) by (nonlinear_arith)
            requires
                p128(i + 1) == 128 * p128(i),
                v >= 128 * (v / 128),
        ;
        assert(acc2 <= MAX_INT) by (nonlinear_arith)
            requires
                acc2 + (v / 128) * p128(i + 1) == acc + v * p128(i),
                acc + v * p128(i) <= MAX_INT,
                (v / 128) * p128(i + 1) >= 0,
        ;
        lemma_tail_rt(v / 128, rest, i + 1, acc2);
        assert(b.subrange(1, b.len() as int) =~= t + rest);
        lemma_tail_shift(b, 1, i + 1, acc2);
    }
}

/// `int_tail` reads only from `pos` on.
proof fn lemma_tail_shift(b: Seq<u8>, pos: int, i: nat, acc: nat)
    requires
        0 <= pos <= b.len(),
    ensures
        int_tail(b, pos, i, acc) == match int_tail(b.subrange(pos, b.len() as int), 0, i, acc) {
            IntR::Ok(v, e) => IntR::Ok(v, e + pos),
            r => r,
        },
    decreases 9 - i,
{
    let c = b.subrange(pos, b.len() as int);
    if pos < b.len() {
        assert(c[0] == b[pos]);
        if i < 9 {
            let acc2 = acc + ((b[pos] as nat) % 128) * p128(i);
            if !(acc2 > MAX_INT) && !(b[pos] < 128) {
                lemma_tail_shift(b, pos + 1, i + 1, acc2);
                lemma_tail_shift(c, 1, i + 1, acc2);
                assert(c.subrange(1, c.len() as int) =~= b.subrange(pos + 1, b.len() as int));
            }
        }
    }
}

/// A prefix value under flags that are a multiple of `2^n`.
pub proof fn lemma_flags(flags: nat, n: nat, x: nat)
    requires
        1 <= n <= 8,
        flags % p2(n) == 0,
        flags < 256,
        x < p2(n),
    ensures
        flags + x < 256,
        (flags + x) % p2(n) == x,
        (flags + x) / p2(n) == flags / p2(n),
{
    lemma_pows();
    assert(P2@[n as int] as nat == p2(n));
    if n == 1 {
        assert(p2(n) == 2);
    } else if n == 2 {
        assert(p2(n) == 4);
    } else if n == 3 {
        assert(p2(n) == 8);
    } else if n == 4 {
        assert(p2(n) == 16);
    } else if n == 5 {
        assert(p2(n) == 32);
    } else if n == 6 {
        assert(p2(n) == 64);
    } else if n == 7 {
        assert(p2(n) == 128);
    } else {
        assert(p2(n) == 256);
    }
}

/// Decoding an encoded integer gives it back, and the flags are untouched.
pub proof fn lemma_int_rt(flags: nat, n: nat, v: nat, rest: Seq<u8>)
    requires
        1 <= n <= 8,
        flags % p2(n) == 0,
        flags < 256,
        v <= MAX_INT,
    ensures
        int_dec(int_enc(flags, n, v) + rest, 0, n) == IntR::Ok(v, int_enc(flags, n, v).len() as int),
        int_enc(flags, n, v).len() >= 1,
        (int_enc(flags, n, v)[0] as nat) / p2(n) == flags / p2(n),
        int_enc(flags, n, v).len() <= 10,
{
    lemma_pows();
    let k = (p2(n) - 1) as nat;
    let e = int_enc(flags, n, v);
    let b = e + rest;
    assert(P2@[n as int] as nat == p2(n));
    assert(2 <= p2(n) <= 256);
    lemma_flags(flags, n, k);
    if v < k {
        assert(b[0] == (flags + v) as u8);
        lemma_flags(flags, n, v);
    } else {
        assert(b[0] == (flags + k) as u8);
        let t = int_enc_tail((v - k) as nat);
        assert(P128@[8] as nat == p128(8));
        assert(p128(9) == 128 * p128(8));
        assert((v - k) * p128(0) < p128(9));
        lemma_tail_rt((v - k) as nat, rest, 0, k);
        assert(b.subrange(1, b.len() as int) =~= t + rest);
        lemma_tail_shift(b, 1, 0, k);
        lemma_tail_len((v - k) as nat);
    }
}

proof fn lemma_tail_len(v: nat)
    requires
        v <= MAX_INT,
    ensures
        int_enc_tail(v).len() <= 9,
{
    assert(p128(9) == 9223372036854775808) by (compute);
    lemma_tail_len_k(v, 9);
}

proof fn lemma_tail_len_k(v: nat, k: nat)
    requires
        k >= 1,
        v < p128(k),
    ensures
        int_enc_tail(v).len() <= k,
    decreases v,
{
    if v >= 128 {
        if k == 1 {
            assert(p128(1) == 128) by (compute);
        } else {
            assert(p128(k) == 128 * p128((k - 1) as nat));
            assert(v / 128 < p128((k - 1) as nat)) by (nonlinear_arith)
                requires
                    v < 128 * p128((k - 1) as nat),
            ;
            lemma_tail_len_k(v / 128, (k - 1) as nat);
        }
    }
}

} // verus!
