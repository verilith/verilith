//! The 512-bit x86-64 kernels (VAES, VPCLMULQDQ, AVX-512), proven over
//! the instruction wrappers of [`crate::x86`]: sixteen blocks of CTR, four
//! to a register, and GHASH of sixteen blocks with one reduction.
#![allow(unused_imports)]
use crate::gf::*;
use crate::isa::*;
use crate::lemmas::*;
use crate::ni::*;
use crate::spec::*;
use crate::x86::*;
use vstd::prelude::*;

verus! {

broadcast use axiom_zl_len;

/// The four lanes' inputs: the counter blocks for c + 4q .. c + 4q + 3.
pub open spec fn ins4(iv: Seq<u8>, c: int, q: int) -> Seq<Seq<u8>> {
    Seq::new(4, |l: int| counter_block(iv, c + 4 * q + l))
}

/// The counter registers for c + 4q + l in lane l, made from the counter
/// register for c.
#[inline(always)]
pub fn ctrs_z(ctr: X128, Ghost(iv): Ghost<Seq<u8>>, Ghost(c): Ghost<int>) -> (r: (Z512, Z512))
    requires
        vaes(),
        ni(),
        ctr_reg_ok(xv(ctr), iv, c),
        c >= 0,
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] ctr_reg_ok(zl(r.0)[l], iv, c + l),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r.1)[l] == (4u32 as u128) << 96u128,
{
    let offs: [u128; 4] = [0, 1u128 << 96, 2u128 << 96, 3u128 << 96];
    let o = z_load_u128(&offs, 0);
    let b = z_bcast_x(ctr);
    let z = z_add32(b, o);
    let four = z_bcast_x(x_set(4u128 << 96));
    proof {
        assert((0u32 as u128) << 96u128 == 0u128 && (1u32 as u128) << 96u128 == 1u128 << 96u128 && (2u32 as u128)
            << 96u128 == 2u128 << 96u128 && (3u32 as u128) << 96u128 == 3u128 << 96u128) by (bit_vector);
        assert forall|l: int| 0 <= l < 4 implies #[trigger] ctr_reg_ok(zl(z)[l], iv, c + l) by {
            assert(zl(o)[l] == offs@[l]);
            assert(zl(b)[l] == xv(ctr));
            let j = l as u32;
            if l == 0 {
                assert(offs@[0] == 0u128);
            } else if l == 1 {
                assert(offs@[1] == 1u128 << 96u128);
            } else if l == 2 {
                assert(offs@[2] == 2u128 << 96u128);
            } else {
                assert(offs@[3] == 3u128 << 96u128);
            }
            assert(offs@[l] == (j as u128) << 96u128);
            lemma_ctr_add(xv(ctr), iv, c, j);
        };
    }
    (z, four)
}

/// Advances each lane's counter by 4.
#[inline(always)]
pub fn next_z(z: Z512, four: Z512, Ghost(iv): Ghost<Seq<u8>>, Ghost(c): Ghost<int>) -> (r: Z512)
    requires
        vaes(),
        forall|l: int| 0 <= l < 4 ==> #[trigger] ctr_reg_ok(zl(z)[l], iv, c + l),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(four)[l] == (4u32 as u128) << 96u128,
        c >= 0,
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] ctr_reg_ok(zl(r)[l], iv, c + 4 + l),
{
    let r = z_add32(z, four);
    proof {
        assert forall|l: int| 0 <= l < 4 implies #[trigger] ctr_reg_ok(zl(r)[l], iv, c + 4 + l) by {
            lemma_ctr_add(zl(z)[l], iv, c + l, 4u32);
        };
    }
    r
}

/// The four counter blocks after round 0.
#[inline(always)]
pub fn start_z(z: Z512, m: Z512, k0: Z512, Ghost(key): Ghost<Seq<u8>>, Ghost(iv): Ghost<Seq<u8>>, Ghost(c): Ghost<int>, Ghost(q): Ghost<int>) -> (r: Z512)
    requires
        vaes(),
        key_ok(key),
        iv.len() == 12,
        forall|l: int| 0 <= l < 4 ==> #[trigger] ctr_reg_ok(zl(z)[l], iv, c + 4 * q + l),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(m, l) == ctr_mask(),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(k0, l) == round_key(key, 0),
        c + 4 * q >= 0,
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r, l) == rounds(key, ins4(iv, c, q)[l], 1),
        forall|l: int| 0 <= l < 4 ==> (#[trigger] ins4(iv, c, q)[l]).len() == 16,
{
    let b = z_pshufb(z, m);
    let r = z_xor(b, k0);
    proof {
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zb(r, l) == rounds(key, ins4(iv, c, q)[l], 1) by {
            assert(ctr_reg_ok(zl(z)[l], iv, c + 4 * q + l));
            assert(zb(m, l) == ctr_mask());
            assert(zb(b, l) == pshufb(zb(z, l), zb(m, l)));
            assert(zl(r)[l] == zl(b)[l] ^ zl(k0)[l]);
            assert(zb(k0, l) == round_key(key, 0));
            lemma_ctr_block(zl(z)[l], iv, c + 4 * q + l);
            lemma_xor_bytes16(zl(b)[l], zl(k0)[l]);
            lemma_rounds_step(key, counter_block(iv, c + 4 * q + l), 1);
        };
        assert forall|l: int| 0 <= l < 4 implies (#[trigger] ins4(iv, c, q)[l]).len() == 16 by {
            lemma_counter_block_len(iv, c + 4 * q + l);
        };
    }
    r
}

/// Round r on four blocks.
#[inline(always)]
pub fn round_z(s: Z512, k: Z512, Ghost(key): Ghost<Seq<u8>>, Ghost(ins): Ghost<Seq<Seq<u8>>>, Ghost(r): Ghost<int>) -> (o: Z512)
    requires
        vaes(),
        ins.len() == 4,
        r >= 1,
        forall|l: int| 0 <= l < 4 ==> (#[trigger] ins[l]).len() == 16,
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(s, l) == rounds(key, ins[l], r),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(k, l) == round_key(key, r),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(o, l) == rounds(key, ins[l], r + 1),
{
    let o = z_aesenc(s, k);
    proof {
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zb(o, l) == rounds(key, ins[l], r + 1) by {
            lemma_rounds_len(key, ins[l], r);
            lemma_aesenc(zb(s, l), zb(k, l));
            lemma_rounds_step(key, ins[l], r);
        };
    }
    o
}

/// The last round on four blocks.
#[inline(always)]
pub fn last_z(s: Z512, k: Z512, Ghost(key): Ghost<Seq<u8>>, Ghost(ins): Ghost<Seq<Seq<u8>>>) -> (o: Z512)
    requires
        vaes(),
        ins.len() == 4,
        forall|l: int| 0 <= l < 4 ==> (#[trigger] ins[l]).len() == 16,
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(s, l) == rounds(key, ins[l], crate::spec::nr(key)),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(k, l) == round_key(key, crate::spec::nr(key)),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(o, l) == cipher(key, ins[l]),
{
    let o = z_aesenclast(s, k);
    proof {
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zb(o, l) == cipher(key, ins[l]) by {
            lemma_rounds_len(key, ins[l], crate::spec::nr(key));
            lemma_aesenc(zb(s, l), zb(k, l));
            lemma_cipher(key, ins[l]);
        };
    }
    o
}

/// Round key r in every lane.
#[inline(always)]
pub fn rk_z(rk: &[u128; 15], r: usize, Ghost(key): Ghost<Seq<u8>>) -> (k: Z512)
    requires
        vaes(),
        rk_ok(key, rk@),
        r <= crate::spec::nr(key),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(k, l) == round_key(key, r as int),
{
    z_bcast(rk, r)
}

/// Sixteen keystream blocks from counter c: lane l of register q is
/// CIPHER of the counter block for c + 4q + l.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ks16_z(rk: &[u128; 15], nr: usize, ctr: X128, Ghost(key): Ghost<Seq<u8>>, Ghost(iv): Ghost<Seq<u8>>, Ghost(c): Ghost<int>) -> (r: (Z512, Z512, Z512, Z512))
    requires
        vaes(),
        ni(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        ctr_reg_ok(xv(ctr), iv, c),
        c >= 0,
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r.0, l) == cipher(key, ins4(iv, c, 0)[l]),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r.1, l) == cipher(key, ins4(iv, c, 1)[l]),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r.2, l) == cipher(key, ins4(iv, c, 2)[l]),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(r.3, l) == cipher(key, ins4(iv, c, 3)[l]),
{
    let m = z_bcast_x(ctr_x());
    let (z0, four) = ctrs_z(ctr, Ghost(iv), Ghost(c));
    let z1 = next_z(z0, four, Ghost(iv), Ghost(c));
    let z2 = next_z(z1, four, Ghost(iv), Ghost(c + 4));
    proof {
        assert forall|l: int| 0 <= l < 4 implies #[trigger] ctr_reg_ok(zl(z2)[l], iv, c + 8 + l) by {
            assert(ctr_reg_ok(zl(z2)[l], iv, c + 4 + 4 + l));
            assert(c + 4 + 4 + l == c + 8 + l);
        };
    }
    let z3 = next_z(z2, four, Ghost(iv), Ghost(c + 8));
    proof {
        assert forall|l: int| 0 <= l < 4 implies #[trigger] ctr_reg_ok(zl(z0)[l], iv, c + 4 * 0 + l) by {};
        assert forall|l: int| 0 <= l < 4 implies #[trigger] ctr_reg_ok(zl(z1)[l], iv, c + 4 * 1 + l) by {
            assert(c + 4 + l == c + 4 * 1 + l);
        };
        assert forall|l: int| 0 <= l < 4 implies #[trigger] ctr_reg_ok(zl(z2)[l], iv, c + 4 * 2 + l) by {
            assert(c + 4 + 4 + l == c + 4 * 2 + l);
        };
        assert forall|l: int| 0 <= l < 4 implies #[trigger] ctr_reg_ok(zl(z3)[l], iv, c + 4 * 3 + l) by {
            assert(c + 8 + 4 + l == c + 4 * 3 + l);
        };
    }
    let k0 = rk_z(rk, 0, Ghost(key));
    let ghost i0 = ins4(iv, c, 0);
    let ghost i1 = ins4(iv, c, 1);
    let ghost i2 = ins4(iv, c, 2);
    let ghost i3 = ins4(iv, c, 3);
    let mut s0 = start_z(z0, m, k0, Ghost(key), Ghost(iv), Ghost(c), Ghost(0));
    let mut s1 = start_z(z1, m, k0, Ghost(key), Ghost(iv), Ghost(c), Ghost(1));
    let mut s2 = start_z(z2, m, k0, Ghost(key), Ghost(iv), Ghost(c), Ghost(2));
    let mut s3 = start_z(z3, m, k0, Ghost(key), Ghost(iv), Ghost(c), Ghost(3));
    let mut r: usize = 1;
    while r < nr
        invariant
            vaes(),
            rk_ok(key, rk@),
            nr == crate::spec::nr(key),
            1 <= r <= nr,
            i0.len() == 4 && i1.len() == 4 && i2.len() == 4 && i3.len() == 4,
            forall|l: int| 0 <= l < 4 ==> (#[trigger] i0[l]).len() == 16,
            forall|l: int| 0 <= l < 4 ==> (#[trigger] i1[l]).len() == 16,
            forall|l: int| 0 <= l < 4 ==> (#[trigger] i2[l]).len() == 16,
            forall|l: int| 0 <= l < 4 ==> (#[trigger] i3[l]).len() == 16,
            forall|l: int| 0 <= l < 4 ==> #[trigger] zb(s0, l) == rounds(key, i0[l], r as int),
            forall|l: int| 0 <= l < 4 ==> #[trigger] zb(s1, l) == rounds(key, i1[l], r as int),
            forall|l: int| 0 <= l < 4 ==> #[trigger] zb(s2, l) == rounds(key, i2[l], r as int),
            forall|l: int| 0 <= l < 4 ==> #[trigger] zb(s3, l) == rounds(key, i3[l], r as int),
        decreases nr - r,
    {
        let k = rk_z(rk, r, Ghost(key));
        s0 = round_z(s0, k, Ghost(key), Ghost(i0), Ghost(r as int));
        s1 = round_z(s1, k, Ghost(key), Ghost(i1), Ghost(r as int));
        s2 = round_z(s2, k, Ghost(key), Ghost(i2), Ghost(r as int));
        s3 = round_z(s3, k, Ghost(key), Ghost(i3), Ghost(r as int));
        r = r + 1;
    }
    let k = rk_z(rk, nr, Ghost(key));
    (last_z(s0, k, Ghost(key), Ghost(i0)), last_z(s1, k, Ghost(key), Ghost(i1)), last_z(s2, k, Ghost(key), Ghost(i2)), last_z(s3, k, Ghost(key), Ghost(i3)))
}

/// Blocks 4q .. 4q + 3 of a CTR run: XOR the keystream register `s` into
/// `buf[o..o + 64]`.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn xor_z(
    buf: &mut [u8],
    i: usize,
    q: usize,
    o: usize,
    s: Z512,
    Ghost(b0): Ghost<Seq<u8>>,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
)
    requires
        vaes(),
        ctr_done(old(buf)@, b0, i as int, 4 * q as int, key, iv, c),
        old(buf)@.len() == b0.len(),
        i + 16 * (4 * q + 4) <= b0.len(),
        o == i + 64 * q,
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(s, l) == cipher(key, ins4(iv, c, q as int)[l]),
    ensures
        ctr_done(final(buf)@, b0, i as int, 4 * q + 4, key, iv, c),
        final(buf)@.len() == b0.len(),
{
    proof {
        reveal(ctr_done);
    }
    let p = z_load(buf, o);
    let x = z_xor(p, s);
    z_store(buf, o, x);
    proof {
        reveal(ctr_done);
        assert forall|k: int| 0 <= k < buf@.len() implies #[trigger] buf@[k] == if i <= k < i + 16 * (4 * q + 4) {
            b0[k] ^ ks(key, iv, c, k - i)
        } else {
            b0[k]
        } by {
            if o <= k < o + 64 {
                let l = (k - o) / 16;
                assert(0 <= l < 4 && (k - i) / 16 == 4 * q + l && (k - i) % 16 == (k - o) % 16) by (nonlinear_arith)
                    requires
                        o == i + 64 * q,
                        o <= k < o + 64,
                        l == (k - o) / 16,
                ;
                lemma_xor_bytes16(zl(p)[l], zl(s)[l]);
                assert(buf@[k] == zb(x, l)[(k - o) % 16]);
                assert(zl(x)[l] == zl(p)[l] ^ zl(s)[l]);
                assert(zb(x, l)[(k - o) % 16] == zb(p, l)[(k - o) % 16] ^ zb(s, l)[(k - o) % 16]);
                assert(zb(p, l)[(k - o) % 16] == b0[k]) by {
                    assert(zb(p, l) == old(buf)@.subrange(o + 16 * l, o + 16 * l + 16));
                    assert(o + 16 * l + (k - o) % 16 == k) by (nonlinear_arith)
                        requires
                            l == (k - o) / 16,
                            o <= k,
                    ;
                };
                assert(ins4(iv, c, q as int)[l] == counter_block(iv, c + (k - i) / 16));
            }
        };
    }
}

/// Sixteen blocks of CTR: `buf[i..i + 256]` XOR the keystream from
/// counter c.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ctr16_z(
    rk: &[u128; 15],
    nr: usize,
    ctr: X128,
    buf: &mut [u8],
    i: usize,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
)
    requires
        vaes(),
        ni(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        ctr_reg_ok(xv(ctr), iv, c),
        c >= 0,
        i + 256 <= old(buf)@.len(),
    ensures
        ctr_done(final(buf)@, old(buf)@, i as int, 16, key, iv, c),
        final(buf)@.len() == old(buf)@.len(),
{
    let (k0, k1, k2, k3) = ks16_z(rk, nr, ctr, Ghost(key), Ghost(iv), Ghost(c));
    let _len = buf.len();
    let ghost b0 = buf@;
    proof {
        reveal(ctr_done);
        assert(ctr_done(buf@, b0, i as int, 0, key, iv, c));
    }
    xor_z(buf, i, 0, i, k0, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_z(buf, i, 1, i + 64, k1, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_z(buf, i, 2, i + 128, k2, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_z(buf, i, 3, i + 192, k3, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
}


/// `hr[m]` is H^(16 - m): register q of `hr` holds the powers for blocks
/// 4q .. 4q + 3 of sixteen.
pub open spec fn rpowers_ok(h: u128, hr: Seq<u128>) -> bool {
    hr.len() == 16 && forall|m: int| 0 <= m < 16 ==> #[trigger] hr[m] == pow(h, (16 - m) as nat)
}

/// The three parts of the four lanes' products.
#[inline(always)]
pub fn prod_z(a: Z512, b: Z512) -> (r: (Z512, Z512, Z512))
    requires
        vaes(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r.0)[l] == clmul(lo64(zl(a)[l]), lo64(zl(b)[l])),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r.1)[l] == mid(zl(a)[l], zl(b)[l]),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r.2)[l] == clmul(hi64(zl(a)[l]), hi64(zl(b)[l])),
{
    let l = z_clmul::<0x00>(a, b);
    let h = z_clmul::<0x11>(a, b);
    let m1 = z_clmul::<0x10>(a, b);
    let m2 = z_clmul::<0x01>(a, b);
    proof {
        assert(0x00i32 & 1 == 0 && 0x00i32 & 0x10 == 0) by (bit_vector);
        assert(0x11i32 & 1 != 0 && 0x11i32 & 0x10 != 0) by (bit_vector);
        assert(0x10i32 & 1 == 0 && 0x10i32 & 0x10 != 0) by (bit_vector);
        assert(0x01i32 & 1 != 0 && 0x01i32 & 0x10 == 0) by (bit_vector);
    }
    (l, z_xor(m1, m2), h)
}

/// The blocks at `d[o..o + 64]`, reversed, one to a lane.
#[inline(always)]
pub fn load_be_z(d: &[u8], o: usize, rz: Z512) -> (r: Z512)
    requires
        vaes(),
        o + 64 <= d@.len(),
        forall|l: int| 0 <= l < 4 ==> #[trigger] zb(rz, l) == rev_mask(),
    ensures
        forall|l: int| 0 <= l < 4 ==> #[trigger] zl(r)[l] == be128(d@.subrange(o + 16 * l, o + 16 * l + 16)),
{
    let x = z_load(d, o);
    let r = z_pshufb(x, rz);
    proof {
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zl(r)[l] == be128(d@.subrange(o + 16 * l, o + 16 * l + 16)) by {
            assert(zb(rz, l) == rev_mask());
            assert(zb(r, l) == pshufb(zb(x, l), zb(rz, l)));
            assert(zb(x, l) == d@.subrange(o + 16 * l, o + 16 * l + 16));
            lemma_rev(zl(x)[l], zl(r)[l]);
        };
    }
    r
}

/// The XOR of the four lanes.
#[inline(always)]
pub fn fold_z(z: Z512) -> (r: X128)
    requires
        vaes(),
        ni(),
    ensures
        xv(r) == ((zl(z)[0] ^ zl(z)[1]) ^ zl(z)[2]) ^ zl(z)[3],
{
    x_xor(x_xor(x_xor(z_lane::<0>(z), z_lane::<1>(z)), z_lane::<2>(z)), z_lane::<3>(z))
}

proof fn lemma_xsum_take(s: Seq<u128>, k: int)
    requires
        0 <= k < s.len(),
    ensures
        xsum(s.take(k + 1)) == xsum(s.take(k)) ^ s[k],
{
    assert(s.take(k + 1).drop_last() =~= s.take(k));
}

/// The XOR of sixteen terms, lane by lane and then across lanes, is their
/// XOR in order.
proof fn lemma_xsum16(s: Seq<u128>)
    requires
        s.len() == 16,
    ensures
        ({
            let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15) = (s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9], s[10], s[11], s[12], s[13], s[14], s[15]);
            ((((t0 ^ t4) ^ t8) ^ t12) ^ (((t1 ^ t5) ^ t9) ^ t13)) ^ (((t2 ^ t6) ^ t10) ^ t14) ^ (((t3 ^ t7) ^ t11) ^ t15)
        }) == xsum(s),
{
    assert(s.take(0) =~= Seq::<u128>::empty());
    let mut k: int = 0;
    lemma_xsum_take(s, 0);
    lemma_xsum_take(s, 1);
    lemma_xsum_take(s, 2);
    lemma_xsum_take(s, 3);
    lemma_xsum_take(s, 4);
    lemma_xsum_take(s, 5);
    lemma_xsum_take(s, 6);
    lemma_xsum_take(s, 7);
    lemma_xsum_take(s, 8);
    lemma_xsum_take(s, 9);
    lemma_xsum_take(s, 10);
    lemma_xsum_take(s, 11);
    lemma_xsum_take(s, 12);
    lemma_xsum_take(s, 13);
    lemma_xsum_take(s, 14);
    lemma_xsum_take(s, 15);
    assert(s.take(16) =~= s);
    let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15) = (s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9], s[10], s[11], s[12], s[13], s[14], s[15]);
    assert(((((t0 ^ t4) ^ t8) ^ t12) ^ (((t1 ^ t5) ^ t9) ^ t13)) ^ (((t2 ^ t6) ^ t10) ^ t14) ^ (((t3 ^ t7) ^ t11) ^ t15) == (((((((((((((((0u128 ^ t0) ^ t1) ^ t2) ^ t3) ^ t4) ^ t5) ^ t6) ^ t7) ^ t8) ^ t9) ^ t10) ^ t11) ^ t12) ^ t13) ^ t14) ^ t15) by (bit_vector);
}

/// GHASH of sixteen blocks at `d[i..]`, from `acc`, with one reduction:
/// four lanes of products with H^16 .. H^1, summed, folded, reduced.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ghash16_z(acc: u128, d: &[u8], i: usize, hr: &[u128; 16], Ghost(h): Ghost<u128>) -> (r: u128)
    requires
        vaes(),
        ni(),
        i + 256 <= d@.len(),
        rpowers_ok(h, hr@),
    ensures
        r == ghash_from(h, acc, blocks_at(d@, i as int, 16)),
{
    let ghost xs = blocks_at(d@, i as int, 16);
    let ghost ys = xs.update(0, acc ^ xs[0]);
    let rz = z_bcast_x(rev_x());
    let _len = d.len();
    let x0a = load_be_z(d, i, rz);
    let x1 = load_be_z(d, i + 64, rz);
    let x2 = load_be_z(d, i + 128, rz);
    let x3 = load_be_z(d, i + 192, rz);
    let az = z_from_x(x_set(acc));
    let x0 = z_xor(x0a, az);
    let h0 = z_load_u128(hr, 0);
    let h1 = z_load_u128(hr, 4);
    let h2 = z_load_u128(hr, 8);
    let h3 = z_load_u128(hr, 12);
    let (l0, m0, g0) = prod_z(x0, h0);
    let (l1, m1, g1) = prod_z(x1, h1);
    let (l2, m2, g2) = prod_z(x2, h2);
    let (l3, m3, g3) = prod_z(x3, h3);
    let lz = z_xor(z_xor(z_xor(l0, l1), l2), l3);
    let mz = z_xor(z_xor(z_xor(m0, m1), m2), m3);
    let gz = z_xor(z_xor(z_xor(g0, g1), g2), g3);
    let lx = fold_z(lz);
    let mx = fold_z(mz);
    let gx = fold_z(gz);
    let (lo, hi) = join_x(lx, mx, gx);
    let r = red_x(lo, hi);
    proof {
        let pw = |b: int| pow(h, (16 - b) as nat);
        let ls = Seq::new(16, |b: int| clmul(lo64(ys[b]), lo64(pow(h, (16 - b) as nat))));
        let ms = Seq::new(16, |b: int| mid(ys[b], pow(h, (16 - b) as nat)));
        let gs = Seq::new(16, |b: int| clmul(hi64(ys[b]), hi64(pow(h, (16 - b) as nat))));
        // Block b = 4q + l is lane l of register q.
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zl(x0)[l] == ys[l] by {
            assert(zl(x0a)[l] == xs[l]);
            let a = xs[l];
            if l == 0 {
                assert(a ^ acc == acc ^ a) by (bit_vector);
            } else {
                assert(a ^ 0u128 == a) by (bit_vector);
            }
        };
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zl(x1)[l] == ys[4 + l] by {
            assert(xs[4 + l] == be128(d@.subrange(i + 64 + 16 * l, i + 64 + 16 * l + 16)));
        };
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zl(x2)[l] == ys[8 + l] by {
            assert(xs[8 + l] == be128(d@.subrange(i + 128 + 16 * l, i + 128 + 16 * l + 16)));
        };
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zl(x3)[l] == ys[12 + l] by {
            assert(xs[12 + l] == be128(d@.subrange(i + 192 + 16 * l, i + 192 + 16 * l + 16)));
        };
        assert forall|l: int| 0 <= l < 4 implies #[trigger] zl(lz)[l] == ((ls[l] ^ ls[4 + l]) ^ ls[8 + l]) ^ ls[12 + l]
            && zl(mz)[l] == ((ms[l] ^ ms[4 + l]) ^ ms[8 + l]) ^ ms[12 + l] && zl(gz)[l] == ((gs[l] ^ gs[4 + l]) ^ gs[8
            + l]) ^ gs[12 + l] by {
            assert(zl(h0)[l] == hr@[l] && zl(h1)[l] == hr@[4 + l] && zl(h2)[l] == hr@[8 + l] && zl(h3)[l] == hr@[12 + l]);
            assert(zl(x0)[l] == ys[l] && zl(x1)[l] == ys[4 + l] && zl(x2)[l] == ys[8 + l] && zl(x3)[l] == ys[12 + l]);
        };
        lemma_xsum16(ls);
        lemma_xsum16(ms);
        lemma_xsum16(gs);
        assert(xv(lx) == xsum(ls) && xv(mx) == xsum(ms) && xv(gx) == xsum(gs));
        lemma_red_join_sum(ls, ms, gs);
        assert forall|b: int| 0 <= b < 16 implies #[trigger] red(join(ls[b], ms[b], gs[b])) == gf_mul(ys[b], pow(h, (16 - b) as nat)) by {
            lemma_gf_mul_prod(ys[b], pow(h, (16 - b) as nat));
        };
        assert(Seq::new(16, |b: int| red(join(ls[b], ms[b], gs[b]))) =~= Seq::new(ys.len(), |b: int| gf_mul(ys[b], pow(h, (16 - b) as nat))));
        lemma_dsum_xsum(h, ys, 16);
        lemma_ghash_dsum(h, ys);
        lemma_ghash_from_first(h, acc, xs);
    }
    x_get(r)
}

} // verus!
