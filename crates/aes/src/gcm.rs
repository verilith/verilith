//! AES-GCM, proven over [`Isa`] to compute [`spec::gcm_seal`]'s
//! ciphertext and tag and [`spec::gcm_open`]'s decision: the key
//! expansion, H and its powers, GHASH of the additional data, CTR and
//! GHASH of the text sixteen, eight or one block at a time, the last
//! partial block, the length block and the tag.
#![allow(unused_imports)]
use crate::gf::*;
use crate::isa::*;
use crate::lemmas::*;
use crate::arch::*;
use crate::kernels::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// An expanded key: the round keys, and H^1..H^16 for GHASH.
pub struct Gcm {
    pub rk: [u128; 15],
    pub nr: usize,
    pub hp: [u128; 16],
    pub hr: [u128; 16],
    pub key: Ghost<Seq<u8>>,
    pub h: Ghost<u128>,
}

impl Gcm {
    pub open spec fn wf(&self) -> bool {
        &&& rk_ok(self.key@, self.rk@)
        &&& self.nr == nr(self.key@)
        &&& self.h@ == hash_key(self.key@)
        &&& powers_ok(self.h@, self.hp@)
        &&& rpowers_ok(self.h@, self.hr@)
    }
}

/// Rcon[j] (Table 5).
#[inline(always)]
fn rcon_x(j: usize) -> (r: u32)
    requires
        1 <= j <= 10,
    ensures
        r == rcon(j as int),
{
    if j == 1 {
        0x01
    } else if j == 2 {
        0x02
    } else if j == 3 {
        0x04
    } else if j == 4 {
        0x08
    } else if j == 5 {
        0x10
    } else if j == 6 {
        0x20
    } else if j == 7 {
        0x40
    } else if j == 8 {
        0x80
    } else if j == 9 {
        0x1b
    } else {
        0x36
    }
}

proof fn lemma_rot(t: u32)
    ensures
        rot_word(t) == (t >> 8u32) | (t << 24u32),
{
    assert(word((t >> 8u32) as u8, (t >> 16u32) as u8, (t >> 24u32) as u8, (t >> 0u32) as u8) == (t >> 8u32) | (t
        << 24u32)) by (bit_vector);
}

proof fn lemma_rk_bytes(a: u32, b: u32, c: u32, d: u32)
    ensures
        ({
            let v = (a as u128) | (b as u128) << 32u128 | (c as u128) << 64u128 | (d as u128) << 96u128;
            forall|q: int| 0 <= q < 16 ==> #[trigger] bytes16(v)[q] == wbyte(seq![a, b, c, d][q / 4], q % 4)
        }),
{
    let v = (a as u128) | (b as u128) << 32u128 | (c as u128) << 64u128 | (d as u128) << 96u128;
    assert((v >> 0u128) as u8 == (a >> 0u32) as u8 && (v >> 8u128) as u8 == (a >> 8u32) as u8 && (v >> 16u128) as u8
        == (a >> 16u32) as u8 && (v >> 24u128) as u8 == (a >> 24u32) as u8 && (v >> 32u128) as u8 == (b >> 0u32) as u8
        && (v >> 40u128) as u8 == (b >> 8u32) as u8 && (v >> 48u128) as u8 == (b >> 16u32) as u8 && (v >> 56u128) as u8
        == (b >> 24u32) as u8 && (v >> 64u128) as u8 == (c >> 0u32) as u8 && (v >> 72u128) as u8 == (c >> 8u32) as u8
        && (v >> 80u128) as u8 == (c >> 16u32) as u8 && (v >> 88u128) as u8 == (c >> 24u32) as u8 && (v >> 96u128) as u8
        == (d >> 0u32) as u8 && (v >> 104u128) as u8 == (d >> 8u32) as u8 && (v >> 112u128) as u8 == (d >> 16u32) as u8
        && (v >> 120u128) as u8 == (d >> 24u32) as u8) by (bit_vector)
        requires
            v == (a as u128) | (b as u128) << 32u128 | (c as u128) << 64u128 | (d as u128) << 96u128,
    ;
    assert forall|q: int| 0 <= q < 16 implies #[trigger] bytes16(v)[q] == wbyte(seq![a, b, c, d][q / 4], q % 4) by {
        assert(bytes16(v)[q] == (v >> (8 * q) as u128) as u8);
    };
}

/// KEYEXPANSION() (Algorithm 2) into round-key registers.
#[inline(always)]
pub fn expand<A: Wide>(key: &[u8]) -> (r: ([u128; 15], usize))
    requires
        A::ok(),
        key@.len() == 16 || key@.len() == 32,
    ensures
        rk_ok(key@, r.0@),
        r.1 == nr(key@),
{
    let nk = key.len() / 4;
    let nrr = nk + 6;
    let total = 4 * (nrr + 1);
    let mut ws = [0u32; 60];
    let mut i: usize = 0;
    while i < nk
        invariant
            A::ok(),
            key@.len() == 16 || key@.len() == 32,
            nk == key@.len() / 4,
            nk == crate::spec::nk(key@),
            i <= nk,
            forall|j: int| 0 <= j < i ==> #[trigger] ws@[j] == w(key@, j),
        decreases nk - i,
    {
        ws[i] = (key[4 * i] as u32) | (key[4 * i + 1] as u32) << 8 | (key[4 * i + 2] as u32) << 16 | (key[4 * i + 3]
            as u32) << 24;
        i = i + 1;
    }
    while i < total
        invariant
            A::ok(),
            key@.len() == 16 || key@.len() == 32,
            nk == crate::spec::nk(key@),
            nrr == nk + 6,
            total == 4 * (nrr + 1),
            nk <= i <= total,
            forall|j: int| 0 <= j < i ==> #[trigger] ws@[j] == w(key@, j),
        decreases total - i,
    {
        let mut t = ws[i - 1];
        let ghost temp = t;
        if i % nk == 0 {
            proof {
                lemma_rot(t);
                assert(1 <= i / nk <= 10) by (nonlinear_arith)
                    requires
                        nk == 4 || nk == 8,
                        nk <= i < 4 * (nk + 7),
                ;
            }
            t = A::sub_word((t >> 8) | (t << 24)) ^ rcon_x(i / nk);
        } else if nk > 6 && i % nk == 4 {
            t = A::sub_word(t);
        }
        ws[i] = ws[i - nk] ^ t;
        i = i + 1;
    }
    let mut rk = [0u128; 15];
    let mut r: usize = 0;
    while r <= nrr
        invariant
            key@.len() == 16 || key@.len() == 32,
            nrr == nr(key@),
            total == 4 * (nrr + 1),
            r <= nrr + 1,
            forall|j: int| 0 <= j < total ==> #[trigger] ws@[j] == w(key@, j),
            forall|q: int| 0 <= q < r ==> #[trigger] bytes16(rk@[q]) == round_key(key@, q),
        decreases nrr + 1 - r,
    {
        let a = ws[4 * r];
        let b = ws[4 * r + 1];
        let c = ws[4 * r + 2];
        let d = ws[4 * r + 3];
        rk[r] = (a as u128) | (b as u128) << 32 | (c as u128) << 64 | (d as u128) << 96;
        proof {
            lemma_rk_bytes(a, b, c, d);
            let v = rk@[r as int];
            assert(bytes16(v) =~= round_key(key@, r as int)) by {
                assert forall|q: int| 0 <= q < 16 implies #[trigger] bytes16(v)[q] == round_key(key@, r as int)[q] by {
                    assert(bytes16(v)[q] == wbyte(seq![a, b, c, d][q / 4], q % 4));
                    assert(seq![a, b, c, d][q / 4] == ws@[4 * r + q / 4]);
                };
            };
        }
        r = r + 1;
    }
    (rk, nrr)
}

proof fn lemma_zero_bytes16()
    ensures
        bytes16(0) == zeros(16),
{
    assert forall|i: int| 0 <= i < 16 implies #[trigger] bytes16(0)[i] == 0u8 by {
        let s = (8 * i) as u128;
        assert((0u128 >> s) as u8 == 0) by (bit_vector);
    };
    assert(bytes16(0) =~= zeros(16));
}

impl Gcm {
    /// The key schedule, H = CIPHER(0^128) and its powers.
    #[inline(always)]
    pub fn new<A: Wide>(key: &[u8]) -> (r: Self)
        requires
            A::ok(),
            key@.len() == 16 || key@.len() == 32,
        ensures
            r.wf(),
            r.key@ == key@,
    {
        let (rk, nr) = expand::<A>(key);
        let z = A::set(0);
        proof {
            lemma_zero_bytes16();
        }
        let e = enc_x::<A>(&rk, nr, z, Ghost(key@));
        let rev = rev_x::<A>();
        let hx = A::pshufb(e, rev);
        proof {
            lemma_rev(A::v(e), A::v(hx));
        }
        let ghost h = A::v(hx);
        let mut hp = [0u128; 16];
        hp[0] = A::get(hx);
        let mut m: usize = 1;
        while m < 16
            invariant
                A::ok(),
                1 <= m <= 16,
                A::v(hx) == h,
                forall|q: int| 0 <= q < m ==> #[trigger] hp@[q] == pow(h, (q + 1) as nat),
            decreases 16 - m,
        {
            let p = mul_x::<A>(A::set(hp[m - 1]), hx);
            hp[m] = A::get(p);
            m = m + 1;
        }
        let mut hr = [0u128; 16];
        let mut m: usize = 0;
        while m < 16
            invariant
                forall|q: int| 0 <= q < 16 ==> #[trigger] hp@[q] == pow(h, (q + 1) as nat),
                m <= 16,
                forall|q: int| 0 <= q < m ==> #[trigger] hr@[q] == pow(h, (16 - q) as nat),
            decreases 16 - m,
        {
            hr[m] = hp[15 - m];
            m = m + 1;
        }
        Gcm { rk, nr, hp, hr, key: Ghost(key@), h: Ghost(h) }
    }
}


// ---------------------------------------------------------------------------
// GHASH over byte strings
// ---------------------------------------------------------------------------

/// The blocks GHASH reads at `d[i..i + 16 m]` are those of `s`, if the two
/// agree there.
pub proof fn lemma_blocks_at_pad(d: Seq<u8>, s: Seq<u8>, i: int, m: int)
    requires
        0 <= i,
        0 <= m,
        i % 16 == 0,
        i + 16 * m <= s.len(),
        i + 16 * m <= d.len(),
        forall|k: int| i <= k < i + 16 * m ==> #[trigger] d[k] == s[k],
    ensures
        blocks_at(d, i, m) == pad_blocks(s).subrange(i / 16, i / 16 + m),
{
    lemma_pad_blocks(s);
    assert((s.len() + 15) / 16 >= i / 16 + m) by (nonlinear_arith)
        requires
            i % 16 == 0,
            i + 16 * m <= s.len(),
            0 <= i,
    ;
    assert forall|j: int| 0 <= j < m implies #[trigger] blocks_at(d, i, m)[j] == pad_blocks(s)[i / 16 + j] by {
        assert(16 * (i / 16 + j) == i + 16 * j) by (nonlinear_arith)
            requires
                i % 16 == 0,
        ;
        assert(16 * j + 16 <= 16 * m) by (nonlinear_arith)
            requires
                j < m,
        ;
        assert(d.subrange(i + 16 * j, i + 16 * j + 16) =~= chunk(s, i / 16 + j));
    };
    assert(blocks_at(d, i, m) =~= pad_blocks(s).subrange(i / 16, i / 16 + m));
}

pub proof fn lemma_ghash_more(h: u128, a: u128, xs: Seq<u128>, q: int, m: int)
    requires
        0 <= q,
        0 <= m,
        q + m <= xs.len(),
    ensures
        ghash_from(h, ghash_from(h, a, xs.take(q)), xs.subrange(q, q + m)) == ghash_from(h, a, xs.take(q + m)),
{
    lemma_ghash_append(h, a, xs.take(q), xs.subrange(q, q + m));
    assert(xs.take(q) + xs.subrange(q, q + m) =~= xs.take(q + m));
}

/// GHASH_H of `d` padded to whole blocks, from `acc`.
#[inline(always)]
pub fn ghash_bytes<A: Wide>(g: &Gcm, acc: u128, d: &[u8]) -> (r: u128)
    requires
        A::ok(),
        g.wf(),
    ensures
        r == ghash_from(g.h@, acc, pad_blocks(d@)),
{
    let ghost h = g.h@;
    let ghost xs = pad_blocks(d@);
    proof {
        lemma_pad_blocks(d@);
    }
    let len = d.len();
    let mut acc = acc;
    let ghost a0 = acc;
    let mut i: usize = 0;
    while len - i >= 128
        invariant
            A::ok(),
            g.wf(),
            h == g.h@,
            xs == pad_blocks(d@),
            xs.len() == (d@.len() + 15) / 16,
            len == d@.len(),
            i % 16 == 0,
            i <= len,
            acc == ghash_from(h, a0, xs.take(i as int / 16)),
        decreases len - i,
    {
        proof {
            lemma_blocks_at_pad(d@, d@, i as int, 8);
            lemma_ghash_more(h, a0, xs, i as int / 16, 8);
        }
        acc = ghash_x::<A>(acc, d, i, 8, &g.hp, Ghost(h));
        i = i + 128;
    }
    let n = (len - i) / 16;
    if n > 0 {
        proof {
            lemma_blocks_at_pad(d@, d@, i as int, n as int);
            lemma_ghash_more(h, a0, xs, i as int / 16, n as int);
        }
        acc = ghash_x::<A>(acc, d, i, n, &g.hp, Ghost(h));
        proof {
            assert((i + 16 * n) as int / 16 == i as int / 16 + n && (i + 16 * n) % 16 == 0 && len - (i + 16 * n) < 16)
                by (nonlinear_arith)
                requires
                    i % 16 == 0,
                    n == (len - i) / 16,
                    i <= len,
            ;
        }
        i = i + 16 * n;
    } else {
        assert(len - i < 16) by (nonlinear_arith)
            requires
                0 == (len - i) / 16,
                i <= len,
        ;
    }
    if i < len {
        let mut t = [0u8; 16];
        let mut q: usize = 0;
        while q < len - i
            invariant
                i < len,
                len == d@.len(),
                len - i < 16,
                q <= len - i,
                forall|k: int| 0 <= k < q ==> #[trigger] t@[k] == d@[i + k],
                forall|k: int| q <= k < 16 ==> #[trigger] t@[k] == 0,
            decreases len - i - q,
        {
            t[q] = d[i + q];
            q = q + 1;
        }
        let ghost old_acc = acc;
        let rev = rev_x::<A>();
        let tx = A::load16(&t);
        let x = A::pshufb(tx, rev);
        let hx = A::load_u128(&g.hp, 0);
        let y = mul_x::<A>(A::xor(A::set(acc), x), hx);
        proof {
            lemma_rev(A::v(tx), A::v(x));
            assert(t@ =~= chunk(d@, i as int / 16));
            assert((len + 15) / 16 == i as int / 16 + 1) by (nonlinear_arith)
                requires
                    i % 16 == 0,
                    i < len,
                    len - i < 16,
            ;
            assert(xs.len() == i as int / 16 + 1);
            assert(xs.take(i as int / 16 + 1) =~= xs);
            assert(xs.subrange(i as int / 16, i as int / 16 + 1) =~= seq![A::v(x)]);
            lemma_ghash_more(h, a0, xs, i as int / 16, 1);
            assert(seq![A::v(x)].drop_first() =~= Seq::<u128>::empty());
            assert(pow(h, 1) == h);
        }
        acc = A::get(y);
        assert(ghash_from(h, gf_mul(old_acc ^ A::v(x), h), Seq::<u128>::empty()) == gf_mul(old_acc ^ A::v(x), h));
        assert(ghash_from(h, old_acc, seq![A::v(x)]) == gf_mul(old_acc ^ A::v(x), h));
        assert(acc == ghash_from(h, a0, xs));
    } else {
        proof {
            assert((len + 15) / 16 == i as int / 16) by (nonlinear_arith)
                requires
                    i % 16 == 0,
                    i == len,
            ;
            assert(xs.take(i as int / 16) =~= xs);
        }
        assert(acc == ghash_from(h, a0, xs));
    }
    acc
}


// ---------------------------------------------------------------------------
// CTR and GHASH of the text
// ---------------------------------------------------------------------------

proof fn lemma_ctr_reg(iv: Seq<u8>, c: u32, v: u128)
    requires
        iv.len() == 12,
        v == (iv[0] as u128) | (iv[1] as u128) << 8u128 | (iv[2] as u128) << 16u128 | (iv[3] as u128) << 24u128 | (
        iv[4] as u128) << 32u128 | (iv[5] as u128) << 40u128 | (iv[6] as u128) << 48u128 | (iv[7] as u128) << 56u128
            | (iv[8] as u128) << 64u128 | (iv[9] as u128) << 72u128 | (iv[10] as u128) << 80u128 | (iv[11] as u128)
            << 88u128 | (c as u128) << 96u128,
    ensures
        ctr_reg_ok(v, iv, c as int),
{
    let (b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11) = (iv[0], iv[1], iv[2], iv[3], iv[4], iv[5], iv[6], iv[7], iv[8], iv[9], iv[10], iv[11]);
    assert((v >> 0u128) as u8 == b0 && (v >> 8u128) as u8 == b1 && (v >> 16u128) as u8 == b2 && (v >> 24u128) as u8 == b3
        && (v >> 32u128) as u8 == b4 && (v >> 40u128) as u8 == b5 && (v >> 48u128) as u8 == b6 && (v >> 56u128) as u8
        == b7 && (v >> 64u128) as u8 == b8 && (v >> 72u128) as u8 == b9 && (v >> 80u128) as u8 == b10 && (v >> 88u128)
        as u8 == b11 && (v >> 96u128) as u32 == c) by (bit_vector)
        requires
            v == (b0 as u128) | (b1 as u128) << 8u128 | (b2 as u128) << 16u128 | (b3 as u128) << 24u128 | (b4 as u128)
                << 32u128 | (b5 as u128) << 40u128 | (b6 as u128) << 48u128 | (b7 as u128) << 56u128 | (b8 as u128)
                << 64u128 | (b9 as u128) << 72u128 | (b10 as u128) << 80u128 | (b11 as u128) << 88u128 | (c as u128)
                << 96u128,
    ;
    assert forall|k: int| 0 <= k < 12 implies #[trigger] bytes16(v).subrange(0, 12)[k] == iv[k] by {
        assert(bytes16(v)[k] == (v >> (8 * k) as u128) as u8);
    };
    assert(bytes16(v).subrange(0, 12) =~= iv);
    assert(lane32(v, 3) == (v >> 96u128) as u32);
}

/// The counter register for counter c.
#[inline(always)]
fn ctr_reg<A: Wide>(iv: &[u8; 12], c: u32) -> (r: A::R)
    requires
        A::ok(),
    ensures
        ctr_reg_ok(A::v(r), iv@, c as int),
{
    let v: u128 = (iv[0] as u128) | (iv[1] as u128) << 8 | (iv[2] as u128) << 16 | (iv[3] as u128) << 24 | (iv[4]
        as u128) << 32 | (iv[5] as u128) << 40 | (iv[6] as u128) << 48 | (iv[7] as u128) << 56 | (iv[8] as u128) << 64
        | (iv[9] as u128) << 72 | (iv[10] as u128) << 80 | (iv[11] as u128) << 88 | (c as u128) << 96;
    proof {
        lemma_ctr_reg(iv@, c, v);
    }
    A::set(v)
}

proof fn lemma_ctr_gctr(nb: Seq<u8>, b0: Seq<u8>, p: Seq<u8>, key: Seq<u8>, iv: Seq<u8>, i: int, m: int)
    requires
        ctr_done(nb, b0, i, m, key, iv, 2 + i / 16),
        0 <= i,
        i % 16 == 0,
        i + 16 * m <= p.len(),
        b0.len() == p.len(),
        forall|k: int| i <= k < i + 16 * m ==> #[trigger] b0[k] == p[k],
    ensures
        nb.len() == b0.len(),
        forall|k: int| i <= k < i + 16 * m ==> #[trigger] nb[k] == gctr(key, iv, p)[k],
        forall|k: int| 0 <= k < nb.len() && !(i <= k < i + 16 * m) ==> #[trigger] nb[k] == b0[k],
{
    reveal(ctr_done);
    assert forall|k: int| i <= k < i + 16 * m implies #[trigger] nb[k] == gctr(key, iv, p)[k] by {
        assert(2 + i / 16 + (k - i) / 16 == 2 + k / 16 && (k - i) % 16 == k % 16) by (nonlinear_arith)
            requires
                i % 16 == 0,
                i <= k,
        ;
    };
}

/// The last, partial block of CTR, and GHASH's last text block.
#[verifier::spinoff_prover]
#[inline(always)]
fn tail_x<A: Wide>(
    g: &Gcm,
    iv: &[u8; 12],
    buf: &mut [u8],
    i: usize,
    ctr: A::R,
    cmask: A::R,
    acc: u128,
    dec: bool,
    Ghost(p): Ghost<Seq<u8>>,
    Ghost(cc): Ghost<Seq<u8>>,
    Ghost(gs): Ghost<Seq<u8>>,
    Ghost(xs): Ghost<Seq<u128>>,
    Ghost(a0): Ghost<u128>,
) -> (r: u128)
    requires
        A::ok(),
        g.wf(),
        p.len() <= max_len(),
        cc == gctr(g.key@, iv@, p),
        gs == if dec { p } else { cc },
        xs == pad_blocks(gs),
        xs.len() == (gs.len() + 15) / 16,
        xb::<A>(cmask) == ctr_mask(),
        old(buf)@.len() == p.len(),
        i % 16 == 0,
        i <= p.len(),
        p.len() - i < 16,
        forall|k: int| 0 <= k < i ==> #[trigger] old(buf)@[k] == cc[k],
        forall|k: int| i <= k < p.len() ==> #[trigger] old(buf)@[k] == p[k],
        ctr_reg_ok(A::v(ctr), iv@, 2 + i / 16),
        acc == ghash_from(g.h@, a0, xs.take(i as int / 16)),
    ensures
        final(buf)@ == cc,
        r == ghash_from(g.h@, a0, xs),
{
    let ghost key = g.key@;
    let ghost h = g.h@;
    proof {
        lemma_pad_blocks(gs);
    }
    let len = buf.len();
    let mut acc = acc;
    if i < len {
        let ghost b0 = buf@;
        let ghost q = i as int / 16;
        let mut t = [0u8; 16];
        let mut k: usize = 0;
        while k < len - i
            invariant
                i < len,
                len == buf@.len(),
                len - i < 16,
                k <= len - i,
                forall|j: int| 0 <= j < k ==> #[trigger] t@[j] == buf@[i + j],
                forall|j: int| k <= j < 16 ==> #[trigger] t@[j] == 0,
            decreases len - i - k,
        {
            t[k] = buf[i + k];
            k = k + 1;
        }
        let ghost t0 = t@;
        let x = A::load16(&t);
        let e = enc_x::<A>(&g.rk, g.nr, A::pshufb(ctr, cmask), Ghost(key));
        let o = A::xor(x, e);
        let mut u = [0u8; 16];
        A::store16(&mut u, o);
        proof {
            lemma_ctr_block(A::v(ctr), iv@, 2 + q);
            lemma_xor_bytes16(A::v(x), A::v(e));
            assert(i as int / 16 + 0 == q);
        }
        let mut k: usize = 0;
        while k < len - i
            invariant
                i < len,
                len == buf@.len(),
                len - i < 16,
                k <= len - i,
                forall|j: int| 0 <= j < k ==> #[trigger] buf@[i + j] == u@[j],
                forall|j: int| 0 <= j < len && !(i <= j < i + k) ==> #[trigger] buf@[j] == b0[j],
            decreases len - i - k,
        {
            buf[i + k] = u[k];
            k = k + 1;
        }
        let mut v = [0u8; 16];
        let mut k: usize = 0;
        while k < len - i
            invariant
                i < len,
                len - i < 16,
                k <= len - i,
                forall|j: int| 0 <= j < k ==> #[trigger] v@[j] == u@[j],
                forall|j: int| k <= j < 16 ==> #[trigger] v@[j] == 0,
            decreases len - i - k,
        {
            v[k] = u[k];
            k = k + 1;
        }
        let ghost v0 = v@;
        let rev = rev_x::<A>();
        let gx = if dec { A::load16(&t) } else { A::load16(&v) };
        let y = A::pshufb(gx, rev);
        proof {
            assert forall|j: int| i <= j < len implies #[trigger] buf@[j] == cc[j] by {
                assert(buf@[j] == u@[j - i]);
                assert(j / 16 == q && j % 16 == j - i) by (nonlinear_arith)
                    requires
                        i % 16 == 0,
                        q == i / 16,
                        i <= j < i + 16,
                ;
            };
            assert(t0 =~= chunk(p, q));
            assert(v0 =~= chunk(cc, q));
            lemma_rev(A::v(gx), A::v(y));
            assert((gs.len() + 15) / 16 == q + 1) by (nonlinear_arith)
                requires
                    i % 16 == 0,
                    q == i / 16,
                    i < gs.len(),
                    gs.len() - i < 16,
            ;
            assert(xs.take(q + 1) =~= xs);
            assert(xs.subrange(q, q + 1) =~= seq![A::v(y)]);
            lemma_ghash_more(h, a0, xs, q, 1);
            assert(seq![A::v(y)].drop_first() =~= Seq::<u128>::empty());
        }
        let hx = A::load_u128(&g.hp, 0);
        let z = mul_x::<A>(A::xor(A::set(acc), y), hx);
        acc = A::get(z);
        proof {
            assert(ghash_from(h, gf_mul((acc_before(a0, h, xs, q)) ^ A::v(y), h), Seq::<u128>::empty()) == gf_mul(
                acc_before(a0, h, xs, q) ^ A::v(y),
                h,
            ));
        }
    } else {
        proof {
            assert((gs.len() + 15) / 16 == i as int / 16) by (nonlinear_arith)
                requires
                    i % 16 == 0,
                    i == gs.len(),
            ;
            assert(xs.take(i as int / 16) =~= xs);
        }
    }
    proof {
        assert(buf@ =~= cc);
    }
    acc
}

/// GHASH of the n <= 16 blocks of `d` at i.
#[inline(always)]
fn ghash_chunk<A: Wide>(g: &Gcm, acc: u128, d: &[u8], i: usize, n: usize, wide: bool) -> (r: u128)
    requires
        A::ok(),
        g.wf(),
        1 <= n <= 16,
        n == 16 ==> wide,
        wide ==> A::wide(),
        i + 16 * n <= d@.len(),
    ensures
        r == ghash_from(g.h@, acc, blocks_at(d@, i as int, n as int)),
{
    if n == 16 {
        A::ghash16(acc, d, i, &g.hr, Ghost(g.h@))
    } else {
        ghash_x::<A>(acc, d, i, n, &g.hp, Ghost(g.h@))
    }
}

/// CTR and GHASH from `acc` over `buf`, whole blocks then the partial
/// one: GHASH reads the text before CTR when decrypting (`dec`) and a
/// chunk behind it when encrypting.
#[verifier::spinoff_prover]
#[inline(always)]
fn crypt<A: Wide>(g: &Gcm, iv: &[u8; 12], buf: &mut [u8], acc: u128, dec: bool, wide: bool) -> (r: u128)
    requires
        A::ok(),
        wide ==> A::wide(),
        g.wf(),
        old(buf)@.len() <= max_len(),
    ensures
        final(buf)@ == gctr(g.key@, iv@, old(buf)@),
        r == ghash_from(g.h@, acc, pad_blocks(if dec { old(buf)@ } else { final(buf)@ })),
{
    let ghost key = g.key@;
    let ghost h = g.h@;
    let ghost p = buf@;
    let ghost cc = gctr(key, iv@, p);
    let ghost gs = if dec { p } else { cc };
    let ghost xs = pad_blocks(gs);
    proof {
        lemma_pad_blocks(gs);
    }
    let len = buf.len();
    let cmask = ctr_x::<A>();
    let mut ctr = ctr_reg::<A>(iv, 2);
    let mut acc = acc;
    let ghost a0 = acc;
    let mut i: usize = 0;
    // When encrypting, GHASH runs one chunk behind CTR (blocks gi..i are
    // ciphertext still to hash), so the two are independent work.
    let mut gi: usize = 0;
    let mut pend: usize = 0;
    while len - i >= 16
        invariant
            A::ok(),
            g.wf(),
            key == g.key@,
            h == g.h@,
            p.len() <= max_len(),
            cc == gctr(key, iv@, p),
            gs == if dec { p } else { cc },
            xs == pad_blocks(gs),
            xs.len() == (gs.len() + 15) / 16,
            xb::<A>(cmask) == ctr_mask(),
            len == p.len(),
            buf@.len() == len,
            i % 16 == 0,
            i <= len,
            forall|k: int| 0 <= k < i ==> #[trigger] buf@[k] == cc[k],
            forall|k: int| i <= k < len ==> #[trigger] buf@[k] == p[k],
            ctr_reg_ok(A::v(ctr), iv@, 2 + i / 16),
            gi % 16 == 0,
            gi + 16 * pend == i,
            pend <= 16,
            pend == 16 ==> wide,
            dec ==> pend == 0,
            acc == ghash_from(h, a0, xs.take(gi as int / 16)),
            wide ==> A::wide(),
        decreases len - i,
    {
        let m: usize = if wide && len - i >= 256 { 16 } else if len - i >= 128 { 8 } else { 1 };
        if dec {
            proof {
                lemma_blocks_at_pad(buf@, gs, i as int, m as int);
                lemma_ghash_more(h, a0, xs, i as int / 16, m as int);
            }
            if m == 16 {
                acc = A::ghash16(acc, buf, i, &g.hr, Ghost(h));
            } else {
                acc = ghash_x::<A>(acc, buf, i, m, &g.hp, Ghost(h));
            }
        }
        let ghost b0 = buf@;
        if m == 16 {
            A::ctr16(&g.rk, g.nr, ctr, buf, i, Ghost(key), Ghost(iv@), Ghost(2 + i / 16));
        } else if m == 8 {
            ctr8_x::<A>(&g.rk, g.nr, ctr, cmask, buf, i, Ghost(key), Ghost(iv@), Ghost(2 + i / 16));
        } else {
            ctr1_x::<A>(&g.rk, g.nr, ctr, cmask, buf, i, Ghost(key), Ghost(iv@), Ghost(2 + i / 16));
        }
        proof {
            lemma_ctr_gctr(buf@, b0, p, key, iv@, i as int, m as int);
        }
        if !dec && pend > 0 {
            proof {
                lemma_blocks_at_pad(buf@, gs, gi as int, pend as int);
                lemma_ghash_more(h, a0, xs, gi as int / 16, pend as int);
            }
            acc = ghash_chunk::<A>(g, acc, buf, gi, pend, wide);
        }
        proof {
            lemma_ctr_add(A::v(ctr), iv@, 2 + i / 16, m as u32);
            assert(2 + i / 16 + m == 2 + (i + 16 * m) / 16 && (i + 16 * m) % 16 == 0) by (nonlinear_arith)
                requires
                    i % 16 == 0,
            ;
        }
        ctr = A::add32(ctr, A::set((m as u32 as u128) << 96));
        if dec {
            gi = i + 16 * m;
        } else {
            gi = i;
            pend = m;
        }
        i = i + 16 * m;
    }
    if pend > 0 {
        proof {
            lemma_blocks_at_pad(buf@, gs, gi as int, pend as int);
            lemma_ghash_more(h, a0, xs, gi as int / 16, pend as int);
        }
        acc = ghash_chunk::<A>(g, acc, buf, gi, pend, wide);
    }
    acc = tail_x::<A>(g, iv, buf, i, ctr, cmask, acc, dec, Ghost(p), Ghost(cc), Ghost(gs), Ghost(xs), Ghost(a0));
    proof {
        assert(buf@ =~= cc);
    }
    acc
}

pub open spec fn acc_before(a0: u128, h: u128, xs: Seq<u128>, q: int) -> u128 {
    ghash_from(h, a0, xs.take(q))
}


// ---------------------------------------------------------------------------
// GCM-AE and GCM-AD
// ---------------------------------------------------------------------------

proof fn lemma_rev_bytes(v: u128)
    ensures
        pshufb(bytes16(v), rev_mask()) == be_bytes(v),
{
    let b = bytes16(v);
    let m = rev_mask();
    assert forall|k: int| 0 <= k < 16 implies #[trigger] pshufb(b, m)[k] == b[15 - k] by {
        let j = (15 - k) as u8;
        assert(m[k] == j);
        assert(j & 0x80 == 0 && j & 15 == j) by (bit_vector)
            requires
                j < 16,
        ;
    };
    lemma_be_bytes_rev(v);
    assert(pshufb(b, m) =~= be_bytes(v));
}

/// The tag from S: CIPHER(J0) XOR S.
#[inline(always)]
fn tag_x<A: Wide>(g: &Gcm, iv: &[u8; 12], s: u128) -> (r: A::R)
    requires
        A::ok(),
        g.wf(),
    ensures
        xb::<A>(r) == xor_bytes(cipher(g.key@, counter_block(iv@, 1)), be_bytes(s)),
{
    let cmask = ctr_x::<A>();
    let j0 = ctr_reg::<A>(iv, 1);
    let e = enc_x::<A>(&g.rk, g.nr, A::pshufb(j0, cmask), Ghost(g.key@));
    let sv = A::pshufb(A::set(s), rev_x::<A>());
    proof {
        lemma_ctr_block(A::v(j0), iv@, 1);
        lemma_rev_bytes(s);
        lemma_xor_bytes16(A::v(e), A::v(sv));
    }
    A::xor(e, sv)
}

/// GHASH's last block and the tag: S from the GHASH state after the
/// additional data and the ciphertext.
#[inline(always)]
fn finish_x<A: Wide>(g: &Gcm, iv: &[u8; 12], acc: u128, alen: usize, clen: usize, Ghost(aad): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>) -> (r: A::R)
    requires
        A::ok(),
        g.wf(),
        alen == aad.len(),
        clen == c.len(),
        aad.len() < 0x2000_0000_0000_0000,
        c.len() <= max_len(),
        acc == ghash_from(g.h@, ghash(g.h@, pad_blocks(aad)), pad_blocks(c)),
    ensures
        xb::<A>(r) == gcm_tag(g.key@, iv@, aad, c),
{
    let ghost h = g.h@;
    let lb: u128 = ((alen as u64 * 8) as u128) << 64 | ((clen as u64 * 8) as u128);
    let hx = A::load_u128(&g.hp, 0);
    let sx = mul_x::<A>(A::set(acc ^ lb), hx);
    let s = A::get(sx);
    proof {
        assert(lb == len_block(aad.len(), c.len()));
        let xa = pad_blocks(aad);
        let xc = pad_blocks(c);
        lemma_ghash_append(h, 0, xa + xc, seq![lb]);
        lemma_ghash_append(h, 0, xa, xc);
        assert(seq![lb].drop_first() =~= Seq::<u128>::empty());
        assert(pow(h, 1) == h);
        assert(A::v(hx) == h);
        assert(s == gf_mul(acc ^ lb, h));
        assert(ghash_from(h, gf_mul(acc ^ lb, h), Seq::<u128>::empty()) == gf_mul(acc ^ lb, h));
        assert(s == ghash_from(h, acc, seq![lb]));
        assert(s == gcm_s(h, aad, c));
    }
    tag_x::<A>(g, iv, s)
}

impl Gcm {
    /// GCM-AE: encrypts `buf` in place and returns the tag.
    #[inline(always)]
    pub fn seal<A: Wide>(&self, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16], wide: bool)
        requires
            A::ok(),
            wide ==> A::wide(),
            self.wf(),
            gcm_ok(self.key@, iv@, aad@, old(buf)@.len()),
        ensures
            final(buf)@ + final(tag)@ == gcm_seal(self.key@, iv@, aad@, old(buf)@),
            final(buf)@ == gctr(self.key@, iv@, old(buf)@),
    {
        let ghost p = buf@;
        let a = ghash_bytes::<A>(self, 0, aad);
        let acc = crypt::<A>(self, iv, buf, a, false, wide);
        let t = finish_x::<A>(self, iv, acc, aad.len(), buf.len(), Ghost(aad@), Ghost(buf@));
        A::store16(tag, t);
    }

    /// GCM-AD: decrypts `buf` in place if `tag` is the tag. If it is not,
    /// returns `false` and zeroes `buf`.
    #[inline(always)]
    pub fn open<A: Wide>(&self, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16], wide: bool) -> (r: bool)
        requires
            A::ok(),
            wide ==> A::wide(),
            self.wf(),
            gcm_ok(self.key@, iv@, aad@, old(buf)@.len()),
        ensures
            r == (gcm_tag(self.key@, iv@, aad@, old(buf)@) == tag@),
            r ==> final(buf)@ == gctr(self.key@, iv@, old(buf)@),
            r ==> gcm_open(self.key@, iv@, aad@, old(buf)@ + tag@) == Some(final(buf)@),
            !r ==> gcm_open(self.key@, iv@, aad@, old(buf)@ + tag@) is None,
            !r ==> final(buf)@ == zeros(old(buf)@.len()),
    {
        let ghost c = buf@;
        let a = ghash_bytes::<A>(self, 0, aad);
        let acc = crypt::<A>(self, iv, buf, a, true, wide);
        let t = finish_x::<A>(self, iv, acc, aad.len(), buf.len(), Ghost(aad@), Ghost(c));
        let given = A::load16(tag);
        let d = A::get(A::xor(t, given));
        let ok = d == 0;
        proof {
            let (tv, gv) = (A::v(t), A::v(given));
            assert(tv ^ gv == 0 <==> tv == gv) by (bit_vector);
            if tv == gv {
                assert(xb::<A>(t) == xb::<A>(given));
            } else {
                if xb::<A>(t) == xb::<A>(given) {
                    lemma_bytes_inj(tv, gv);
                }
            }
            let ct = c + tag@;
            assert(ct.take(ct.len() - 16) =~= c);
            assert(ct.skip(ct.len() - 16) =~= tag@);
        }
        if !ok {
            let n = buf.len();
            let mut k: usize = 0;
            while k < n
                invariant
                    n == buf@.len(),
                    k <= n,
                    forall|j: int| 0 <= j < k ==> #[trigger] buf@[j] == 0,
                decreases n - k,
            {
                buf[k] = 0;
                k = k + 1;
            }
            proof {
                assert(buf@ =~= zeros(c.len()));
            }
        }
        ok
    }
}

// ---------------------------------------------------------------------------
// The block cipher alone
// ---------------------------------------------------------------------------

/// `b := CIPHER(b)` with the round keys `rk`.
#[inline(always)]
pub fn encrypt_block<A: Wide>(rk: &[u128; 15], nr: usize, b: &mut [u8; 16], key: Ghost<Seq<u8>>)
    requires
        A::ok(),
        rk_ok(key@, rk@),
        nr == crate::spec::nr(key@),
    ensures
        final(b)@ == cipher(key@, old(b)@),
{
    let x = A::load16(b);
    let e = enc_x::<A>(rk, nr, x, key);
    A::store16(b, e);
}

} // verus!
