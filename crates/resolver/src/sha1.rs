//! SHA-1 (FIPS 180-4 §6.1), proven: what NSEC3 hashes owner names with
//! (RFC 5155 §5) and what DS digest type 1 is (RFC 3658). It is never
//! used to check a signature: DNSSEC algorithms 5 and 7 (RSA/SHA-1) are
//! not supported (RFC 9905), so a collision in SHA-1 buys an attacker
//! nothing here but an NSEC3 hash it could already choose.
//!
//! The padding and the parsing of blocks (§5.1.1, §5.2.1) are SHA-256's,
//! from verilith-sha2's specification; this file adds §4.1.1, §4.2.1,
//! §5.3.1 and §6.1.2.
#[cfg(verus_only)]
use verilith_sha2::spec::{add, block, pad, words};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The specification (trusted)
// ---------------------------------------------------------------------------

/// ROTL^n(x), 0 < n < 32 (§3.2 item 5).
pub open spec fn rotl(x: u32, n: u32) -> u32 {
    (x << n) | (x >> ((32 - n) as u32))
}

/// f_t(x, y, z) (§4.1.1, 4.1).
pub open spec fn f(t: int, x: u32, y: u32, z: u32) -> u32 {
    if t < 20 {
        (x & y) ^ (!x & z)
    } else if t < 40 {
        x ^ y ^ z
    } else if t < 60 {
        (x & y) ^ (x & z) ^ (y & z)
    } else {
        x ^ y ^ z
    }
}

/// K_t (§4.2.1).
pub open spec fn k(t: int) -> u32 {
    if t < 20 {
        0x5a827999
    } else if t < 40 {
        0x6ed9eba1
    } else if t < 60 {
        0x8f1bbcdc
    } else {
        0xca62c1d6
    }
}

/// H(0) (§5.3.1).
pub open spec fn iv() -> Seq<u32> {
    seq![0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32, 0xc3d2e1f0u32]
}

/// The message schedule W_t (§6.1.2 step 1).
pub open spec fn schedule(m: Seq<u32>, t: int) -> u32
    decreases t,
{
    if t < 16 {
        m[t]
    } else {
        rotl(schedule(m, t - 3) ^ schedule(m, t - 8) ^ schedule(m, t - 14) ^ schedule(m, t - 16), 1)
    }
}

/// The working variables a, b, c, d, e.
pub struct V5 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub d: u32,
    pub e: u32,
}

/// One iteration of step 3.
pub open spec fn round(v: V5, t: int, w: u32) -> V5 {
    let tt = add(add(add(add(rotl(v.a, 5), f(t, v.b, v.c, v.d)), v.e), k(t)), w);
    V5 { a: tt, b: v.a, c: rotl(v.b, 30), d: v.c, e: v.d }
}

/// The working variables after the first `t` iterations of step 3.
pub open spec fn rounds(v: V5, m: Seq<u32>, t: nat) -> V5
    decreases t,
{
    if t == 0 {
        v
    } else {
        round(rounds(v, m, (t - 1) as nat), t - 1, schedule(m, t - 1))
    }
}

/// H(i) from H(i-1) and block M(i) (steps 1 to 4).
#[verifier::opaque]
pub open spec fn compress(h: Seq<u32>, b: Seq<u8>) -> Seq<u32> {
    let v = rounds(V5 { a: h[0], b: h[1], c: h[2], d: h[3], e: h[4] }, words(b), 80);
    seq![add(v.a, h[0]), add(v.b, h[1]), add(v.c, h[2]), add(v.d, h[3]), add(v.e, h[4])]
}

pub open spec fn hash_blocks(p: Seq<u8>, n: nat) -> Seq<u32>
    decreases n,
{
    if n == 0 {
        iv()
    } else {
        compress(hash_blocks(p, (n - 1) as nat), block(p, n - 1))
    }
}

/// SHA-1(m): H(N) as 20 bytes, most significant first.
pub open spec fn sha1(m: Seq<u8>) -> Seq<u8> {
    let h = hash_blocks(pad(m), pad(m).len() / 64);
    Seq::new(20, |i: int| #[verifier::truncate] (((h[i / 4] >> ((24 - 8 * (i % 4)) as u32)) & 0xff) as u8))
}

// ---------------------------------------------------------------------------
// The implementation
// ---------------------------------------------------------------------------

fn rotl_x(x: u32, n: u32) -> (r: u32)
    requires
        0 < n < 32,
    ensures
        r == rotl(x, n),
{
    (x << n) | (x >> (32 - n))
}

fn f_x(t: usize, x: u32, y: u32, z: u32) -> (r: u32)
    ensures
        r == f(t as int, x, y, z),
{
    if t < 20 {
        (x & y) ^ (!x & z)
    } else if t < 40 {
        x ^ y ^ z
    } else if t < 60 {
        (x & y) ^ (x & z) ^ (y & z)
    } else {
        x ^ y ^ z
    }
}

fn k_x(t: usize) -> (r: u32)
    ensures
        r == k(t as int),
{
    if t < 20 {
        0x5a827999
    } else if t < 40 {
        0x6ed9eba1
    } else if t < 60 {
        0x8f1bbcdc
    } else {
        0xca62c1d6
    }
}

fn add_x(x: u32, y: u32) -> (r: u32)
    ensures
        r == add(x, y),
{
    x.wrapping_add(y)
}

fn be32_at(p: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= p@.len(),
    ensures
        r == verilith_sha2::spec::be32(p@, i as int),
{
    (p[i] as u32) << 24u32 | (p[i + 1] as u32) << 16u32 | (p[i + 2] as u32) << 8u32 | (p[i + 3] as u32)
}

/// The compression of the block at `p[off..off + 64]`.
fn compress_x(h: &[u32; 5], p: &[u8], off: usize) -> (r: [u32; 5])
    requires
        off + 64 <= p@.len(),
    ensures
        r@ == compress(h@, p@.subrange(off as int, off + 64)),
{
    let ghost b = p@.subrange(off as int, off + 64);
    let ghost m = words(b);
    let n = p.len();
    let mut w: Vec<u32> = Vec::with_capacity(80);
    let mut t: usize = 0;
    while t < 16
        invariant
            off + 64 <= p@.len(),
            n == p@.len(),
            b == p@.subrange(off as int, off + 64),
            m == words(b),
            t <= 16,
            w@.len() == t,
            forall|j: int| 0 <= j < t ==> w@[j] == #[trigger] schedule(m, j),
        decreases 16 - t,
    {
        assert(4 * t + 4 <= 64) by (nonlinear_arith)
            requires
                t < 16,
        ;
        let x = be32_at(p, off + 4 * t);
        proof {
            assert(verilith_sha2::spec::be32(p@, off + 4 * t) == verilith_sha2::spec::be32(b, 4 * t));
        }
        w.push(x);
        t = t + 1;
    }
    while t < 80
        invariant
            16 <= t <= 80,
            w@.len() == t,
            forall|j: int| 0 <= j < t ==> w@[j] == #[trigger] schedule(m, j),
        decreases 80 - t,
    {
        let x = rotl_x(w[t - 3] ^ w[t - 8] ^ w[t - 14] ^ w[t - 16], 1);
        proof {
            assert(w@[t - 3] == schedule(m, t - 3));
            assert(w@[t - 8] == schedule(m, t - 8));
            assert(w@[t - 14] == schedule(m, t - 14));
            assert(w@[t - 16] == schedule(m, t - 16));
        }
        w.push(x);
        t = t + 1;
    }
    let ghost v0 = V5 { a: h[0], b: h[1], c: h[2], d: h[3], e: h[4] };
    let (mut a, mut bb, mut c, mut d, mut e) = (h[0], h[1], h[2], h[3], h[4]);
    let mut t: usize = 0;
    while t < 80
        invariant
            t <= 80,
            w@.len() == 80,
            forall|j: int| 0 <= j < 80 ==> w@[j] == #[trigger] schedule(m, j),
            rounds(v0, m, t as nat) == (V5 { a, b: bb, c, d, e }),
        decreases 80 - t,
    {
        proof {
            assert(w@[t as int] == schedule(m, t as int));
        }
        let tt = add_x(add_x(add_x(add_x(rotl_x(a, 5), f_x(t, bb, c, d)), e), k_x(t)), w[t]);
        e = d;
        d = c;
        c = rotl_x(bb, 30);
        bb = a;
        a = tt;
        t = t + 1;
    }
    let r = [add_x(a, h[0]), add_x(bb, h[1]), add_x(c, h[2]), add_x(d, h[3]), add_x(e, h[4])];
    proof {
        reveal(compress);
        assert(r@ =~= compress(h@, b));
    }
    r
}

/// The padded message, built (§5.1.1).
fn pad_x(d: &[u8]) -> (p: Vec<u8>)
    requires
        d@.len() < 0x1000_0000,
    ensures
        p@ == pad(d@),
        p@.len() % 64 == 0,
{
    let mut p: Vec<u8> = Vec::with_capacity(d.len() + 72);
    let mut i: usize = 0;
    while i < d.len()
        invariant
            i <= d@.len(),
            p@ == d@.subrange(0, i as int),
        decreases d@.len() - i,
    {
        p.push(d[i]);
        i = i + 1;
        proof {
            assert(p@ =~= d@.subrange(0, i as int));
        }
    }
    p.push(0x80);
    let ghost p1 = p@;
    let z: usize = ((55 + 64 * 0x0100_0000 - d.len()) % 64) as usize;
    proof {
        assert(z == verilith_sha2::spec::zeros(d@.len() as nat));
    }
    let mut j: usize = 0;
    while j < z
        invariant
            j <= z,
            p@ == p1 + Seq::new(j as nat, |i: int| 0u8),
        decreases z - j,
    {
        p.push(0);
        j = j + 1;
        proof {
            assert(p@ =~= p1 + Seq::new(j as nat, |i: int| 0u8));
        }
    }
    let bits: u64 = (d.len() as u64) * 8;
    let ghost p2 = p@;
    let mut s: usize = 0;
    while s < 8
        invariant
            s <= 8,
            bits == (d@.len() * 8) as u64,
            p@ == p2 + verilith_sha2::spec::be64(bits).subrange(0, s as int),
        decreases 8 - s,
    {
        p.push(((bits >> (56 - 8 * s) as u64) & 0xff) as u8);
        s = s + 1;
        proof {
            assert(p@ =~= p2 + verilith_sha2::spec::be64(bits).subrange(0, s as int));
        }
    }
    proof {
        assert(verilith_sha2::spec::bit_len(d@.len() as nat) == bits);
        assert(verilith_sha2::spec::be64(bits).subrange(0, 8) =~= verilith_sha2::spec::be64(bits));
        assert(p@ =~= pad(d@));
        assert(p@.len() == d@.len() + 1 + z + 8);
    }
    p
}

/// SHA-1 of `d` (`d` shorter than 256 MiB: NSEC3 hashes at most 510 bytes,
/// DS digests a name and a key).
pub fn sha1_x(d: &[u8]) -> (r: [u8; 20])
    requires
        d@.len() < 0x1000_0000,
    ensures
        r@ == sha1(d@),
{
    let p = pad_x(d);
    let plen = p.len();
    let nb = plen / 64;
    let mut h: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
    proof {
        assert(h@ =~= iv());
    }
    let mut i: usize = 0;
    while i < nb
        invariant
            nb == p@.len() / 64,
            plen == p@.len(),
            p@.len() % 64 == 0,
            i <= nb,
            h@ == hash_blocks(p@, i as nat),
        decreases nb - i,
    {
        assert(64 * i + 64 <= p@.len()) by (nonlinear_arith)
            requires
                i < nb,
                nb == p@.len() / 64,
        ;
        h = compress_x(&h, &p, 64 * i);
        proof {
            assert(block(p@, i as int) == p@.subrange(64 * i, 64 * i + 64));
        }
        i = i + 1;
    }
    let mut out = [0u8; 20];
    let mut j: usize = 0;
    while j < 20
        invariant
            j <= 20,
            h@ == hash_blocks(pad(d@), pad(d@).len() / 64),
            forall|q: int| 0 <= q < j ==> out@[q] == #[verifier::truncate] (((h@[q / 4] >> ((24 - 8 * (q % 4)) as u32)) & 0xff) as u8),
        decreases 20 - j,
    {
        out[j] = ((h[j / 4] >> (24 - 8 * (j % 4)) as u32) & 0xff) as u8;
        j = j + 1;
    }
    proof {
        assert(out@ =~= sha1(d@));
    }
    out
}

} // verus!
