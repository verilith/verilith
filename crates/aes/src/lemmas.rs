//! Lemmas about the specification shared by the kernels: bytes and
//! registers, the round functions as the instructions group them, counter
//! blocks, and the blocks GHASH reads.
#![allow(unused_imports)]
use crate::gf::*;
use crate::isa::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Bytes and registers
// ---------------------------------------------------------------------------

pub proof fn lemma_le128_bytes(v: u128)
    ensures
        le128(bytes16(v)) == v,
{
    let b = bytes16(v);
    assert(le128(b) == ((v >> 120u128) as u8 as u128) << 120u128 | ((v >> 112u128) as u8 as u128) << 112u128 | ((v
        >> 104u128) as u8 as u128) << 104u128 | ((v >> 96u128) as u8 as u128) << 96u128 | ((v >> 88u128) as u8 as u128)
        << 88u128 | ((v >> 80u128) as u8 as u128) << 80u128 | ((v >> 72u128) as u8 as u128) << 72u128 | ((v >> 64u128)
        as u8 as u128) << 64u128 | ((v >> 56u128) as u8 as u128) << 56u128 | ((v >> 48u128) as u8 as u128) << 48u128 | ((v
        >> 40u128) as u8 as u128) << 40u128 | ((v >> 32u128) as u8 as u128) << 32u128 | ((v >> 24u128) as u8 as u128)
        << 24u128 | ((v >> 16u128) as u8 as u128) << 16u128 | ((v >> 8u128) as u8 as u128) << 8u128 | ((v >> 0u128)
        as u8 as u128));
    assert(((v >> 120u128) as u8 as u128) << 120u128 | ((v >> 112u128) as u8 as u128) << 112u128 | ((v >> 104u128)
        as u8 as u128) << 104u128 | ((v >> 96u128) as u8 as u128) << 96u128 | ((v >> 88u128) as u8 as u128) << 88u128
        | ((v >> 80u128) as u8 as u128) << 80u128 | ((v >> 72u128) as u8 as u128) << 72u128 | ((v >> 64u128) as u8
        as u128) << 64u128 | ((v >> 56u128) as u8 as u128) << 56u128 | ((v >> 48u128) as u8 as u128) << 48u128 | ((v
        >> 40u128) as u8 as u128) << 40u128 | ((v >> 32u128) as u8 as u128) << 32u128 | ((v >> 24u128) as u8 as u128)
        << 24u128 | ((v >> 16u128) as u8 as u128) << 16u128 | ((v >> 8u128) as u8 as u128) << 8u128 | ((v >> 0u128)
        as u8 as u128) == v) by (bit_vector);
}

/// One byte of a register built from bytes.
proof fn lemma_byte_of_le(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8, b8: u8, b9: u8, b10: u8, b11: u8, b12: u8, b13: u8, b14: u8, b15: u8)
    ensures
        ({
            let v = (b15 as u128) << 120u128 | (b14 as u128) << 112u128 | (b13 as u128) << 104u128 | (b12 as u128)
                << 96u128 | (b11 as u128) << 88u128 | (b10 as u128) << 80u128 | (b9 as u128) << 72u128 | (b8 as u128)
                << 64u128 | (b7 as u128) << 56u128 | (b6 as u128) << 48u128 | (b5 as u128) << 40u128 | (b4 as u128)
                << 32u128 | (b3 as u128) << 24u128 | (b2 as u128) << 16u128 | (b1 as u128) << 8u128 | (b0 as u128);
            (v >> 0u128) as u8 == b0 && (v >> 8u128) as u8 == b1 && (v >> 16u128) as u8 == b2 && (v >> 24u128) as u8
                == b3 && (v >> 32u128) as u8 == b4 && (v >> 40u128) as u8 == b5 && (v >> 48u128) as u8 == b6 && (v
                >> 56u128) as u8 == b7 && (v >> 64u128) as u8 == b8 && (v >> 72u128) as u8 == b9 && (v >> 80u128) as u8
                == b10 && (v >> 88u128) as u8 == b11 && (v >> 96u128) as u8 == b12 && (v >> 104u128) as u8 == b13 && (v
                >> 112u128) as u8 == b14 && (v >> 120u128) as u8 == b15
        }),
{
    assert({
        let v = (b15 as u128) << 120u128 | (b14 as u128) << 112u128 | (b13 as u128) << 104u128 | (b12 as u128) << 96u128
            | (b11 as u128) << 88u128 | (b10 as u128) << 80u128 | (b9 as u128) << 72u128 | (b8 as u128) << 64u128 | (b7
            as u128) << 56u128 | (b6 as u128) << 48u128 | (b5 as u128) << 40u128 | (b4 as u128) << 32u128 | (b3 as u128)
            << 24u128 | (b2 as u128) << 16u128 | (b1 as u128) << 8u128 | (b0 as u128);
        (v >> 0u128) as u8 == b0 && (v >> 8u128) as u8 == b1 && (v >> 16u128) as u8 == b2 && (v >> 24u128) as u8 == b3
            && (v >> 32u128) as u8 == b4 && (v >> 40u128) as u8 == b5 && (v >> 48u128) as u8 == b6 && (v >> 56u128)
            as u8 == b7 && (v >> 64u128) as u8 == b8 && (v >> 72u128) as u8 == b9 && (v >> 80u128) as u8 == b10 && (v
            >> 88u128) as u8 == b11 && (v >> 96u128) as u8 == b12 && (v >> 104u128) as u8 == b13 && (v >> 112u128)
            as u8 == b14 && (v >> 120u128) as u8 == b15
    }) by (bit_vector);
}

pub proof fn lemma_bytes_le128(b: Seq<u8>)
    requires
        b.len() == 16,
    ensures
        bytes16(le128(b)) == b,
{
    lemma_byte_of_le(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9], b[10], b[11], b[12], b[13], b[14], b[15]);
    let v = le128(b);
    assert forall|k: int| 0 <= k < 16 implies #[trigger] bytes16(v)[k] == b[k] by {
        assert(bytes16(v)[k] == (v >> (8 * k) as u128) as u8);
        if k == 0 {
            assert((8 * k) as u128 == 0);
        }
    };
    assert(bytes16(v) =~= b);
}

/// The bytes of a register determine it.
pub proof fn lemma_bytes_inj(a: u128, b: u128)
    requires
        bytes16(a) == bytes16(b),
    ensures
        a == b,
{
    lemma_le128_bytes(a);
    lemma_le128_bytes(b);
}

/// A register with its bytes reversed is the block they make.
pub proof fn lemma_rev_be(v: u128, b: Seq<u8>)
    requires
        b.len() == 16,
        bytes16(v) == Seq::new(16, |k: int| b[15 - k]),
    ensures
        v == be128(b),
{
    lemma_le128_bytes(v);
}

/// The bytes of a block, as a register reversed.
pub proof fn lemma_be_bytes_rev(v: u128)
    ensures
        be_bytes(v) == Seq::new(16, |k: int| bytes16(v)[15 - k]),
{
    assert(be_bytes(v) =~= Seq::new(16, |k: int| bytes16(v)[15 - k]));
}

pub proof fn lemma_be128_bytes(v: u128)
    ensures
        be128(be_bytes(v)) == v,
{
    let r = Seq::new(16, |k: int| bytes16(v)[15 - k]);
    lemma_be_bytes_rev(v);
    assert(Seq::new(16, |k: int| r[15 - k]) =~= bytes16(v));
    lemma_rev_be(v, r);
}

pub proof fn lemma_xor_bytes16(a: u128, b: u128)
    ensures
        bytes16(a ^ b) == add_round_key(bytes16(a), bytes16(b)),
        bytes16(a ^ b) == xor_bytes(bytes16(a), bytes16(b)),
{
    assert forall|k: int| 0 <= k < 16 implies #[trigger] bytes16(a ^ b)[k] == bytes16(a)[k] ^ bytes16(b)[k] by {
        let s = (8 * k) as u128;
        assert(((a ^ b) >> s) as u8 == ((a >> s) as u8) ^ ((b >> s) as u8)) by (bit_vector);
    };
    assert(bytes16(a ^ b) =~= add_round_key(bytes16(a), bytes16(b)));
    assert(bytes16(a ^ b) =~= xor_bytes(bytes16(a), bytes16(b)));
}

// ---------------------------------------------------------------------------
// The rounds as the instructions group them
// ---------------------------------------------------------------------------

pub proof fn lemma_sub_shift(s: Seq<u8>)
    requires
        s.len() == 16,
    ensures
        sub_bytes(shift_rows(s)) == shift_rows(sub_bytes(s)),
{
    assert forall|i: int| 0 <= i < 16 implies 0 <= #[trigger] (i % 4 + 4 * ((i / 4 + i % 4) % 4)) < 16 by {};
    assert(sub_bytes(shift_rows(s)) =~= shift_rows(sub_bytes(s)));
}

/// `AESENC` is a middle round and `AESENCLAST` the last.
pub proof fn lemma_aesenc(s: Seq<u8>, k: Seq<u8>)
    requires
        s.len() == 16,
    ensures
        aesenc(s, k) == round(s, k),
        aesenclast(s, k) == final_round(s, k),
{
    reveal(aesenc);
    reveal(aesenclast);
    reveal(round);
    reveal(final_round);
    lemma_sub_shift(s);
}

/// `AESMC(AESE(s, k))` is a middle round of `s XOR k`, without its
/// round key.
pub proof fn lemma_aese(s: Seq<u8>, k: Seq<u8>)
    requires
        s.len() == 16,
        k.len() == 16,
    ensures
        aese(s, k) == shift_rows(sub_bytes(add_round_key(s, k))),
{
    reveal(aese);
    lemma_sub_shift(add_round_key(s, k));
}

/// Round keys as registers: `rk[r]` holds round key r, for r = 0..Nr.
pub open spec fn rk_ok(key: Seq<u8>, rk: Seq<u128>) -> bool {
    &&& key_ok(key)
    &&& rk.len() == 15
    &&& forall|r: int| 0 <= r <= nr(key) ==> #[trigger] bytes16(rk[r]) == round_key(key, r)
}

pub proof fn lemma_rounds_len(key: Seq<u8>, input: Seq<u8>, n: int)
    requires
        input.len() == 16,
    ensures
        rounds(key, input, n).len() == 16,
    decreases n,
{
    reveal(rounds);
    reveal(round);
    if n > 1 {
        lemma_rounds_len(key, input, n - 1);
    }
}

/// Round 0, and rounds 1 to n - 1 one at a time.
pub proof fn lemma_rounds_step(key: Seq<u8>, input: Seq<u8>, n: int)
    ensures
        rounds(key, input, 1) == add_round_key(input, round_key(key, 0)),
        n >= 1 ==> rounds(key, input, n + 1) == round(rounds(key, input, n), round_key(key, n)),
{
    reveal(rounds);
}

pub proof fn lemma_cipher(key: Seq<u8>, input: Seq<u8>)
    ensures
        cipher(key, input) == final_round(rounds(key, input, nr(key)), round_key(key, nr(key))),
{
    reveal(cipher);
}

// ---------------------------------------------------------------------------
// Counter blocks
// ---------------------------------------------------------------------------

/// The register a counter block is made from: the IV in bytes 0..11 and
/// the counter as a number in 32-bit lane 3. A byte shuffle makes the
/// block.
pub open spec fn ctr_reg_ok(v: u128, iv: Seq<u8>, c: int) -> bool {
    &&& iv.len() == 12
    &&& bytes16(v).subrange(0, 12) == iv
    &&& lane32(v, 3) as int == c % 0x1_0000_0000
}

/// The shuffle that swaps bytes 12..15 into big-endian order.
pub open spec fn ctr_mask() -> Seq<u8> {
    seq![0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 14, 13, 12]
}

/// The shuffle that reverses the bytes.
pub open spec fn rev_mask() -> Seq<u8> {
    seq![15u8, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
}

pub proof fn lemma_ctr_block(v: u128, iv: Seq<u8>, c: int)
    requires
        ctr_reg_ok(v, iv, c),
    ensures
        pshufb(bytes16(v), ctr_mask()) == counter_block(iv, c),
{
    reveal(counter_block);
    let b = bytes16(v);
    let x = lane32(v, 3);
    let c32 = c % 0x1_0000_0000;
    assert(x as int == c32);
    assert((v >> 96u128) as u32 == x);
    assert((v >> 120u128) as u8 == (x >> 24u32) as u8 && (v >> 112u128) as u8 == (x >> 16u32) as u8 && (v >> 104u128)
        as u8 == (x >> 8u32) as u8 && (v >> 96u128) as u8 == x as u8) by (bit_vector)
        requires
            (v >> 96u128) as u32 == x,
    ;
    assert((x >> 24u32) as int == x as int / 0x100_0000) by {
        vstd::bits::lemma_u32_shr_is_div(x, 24);
        vstd::arithmetic::power2::lemma2_to64();
    };
    assert(((x >> 16u32) as u8) as int == (x as int / 0x1_0000) % 0x100) by {
        vstd::bits::lemma_u32_shr_is_div(x, 16);
        vstd::arithmetic::power2::lemma2_to64();
        let y = x >> 16u32;
        assert(y as u8 == y & 0xff) by (bit_vector);
        vstd::bits::lemma_u32_low_bits_mask_is_mod(y, 8);
    };
    assert(((x >> 8u32) as u8) as int == (x as int / 0x100) % 0x100) by {
        vstd::bits::lemma_u32_shr_is_div(x, 8);
        vstd::arithmetic::power2::lemma2_to64();
        let y = x >> 8u32;
        assert(y as u8 == y & 0xff) by (bit_vector);
        vstd::bits::lemma_u32_low_bits_mask_is_mod(y, 8);
    };
    assert((x as u8) as int == x as int % 0x100) by {
        assert(x as u8 == x & 0xff) by (bit_vector);
        vstd::bits::lemma_u32_low_bits_mask_is_mod(x, 8);
        vstd::arithmetic::power2::lemma2_to64();
    };
    let m = ctr_mask();
    assert forall|k: int| 0 <= k < 16 implies #[trigger] pshufb(b, m)[k] == counter_block(iv, c)[k] by {
        if k < 12 {
            let kb = k as u8;
            assert(m[k] == kb);
            assert(kb & 0x80 == 0 && (kb & 15) == kb) by (bit_vector)
                requires
                    kb < 12,
            ;
            assert(b[k] == iv[k]);
        } else if k == 12 {
            assert(15u8 & 0x80 == 0 && 15u8 & 15 == 15) by (bit_vector);
        } else if k == 13 {
            assert(14u8 & 0x80 == 0 && 14u8 & 15 == 14) by (bit_vector);
        } else if k == 14 {
            assert(13u8 & 0x80 == 0 && 13u8 & 15 == 13) by (bit_vector);
        } else {
            assert(12u8 & 0x80 == 0 && 12u8 & 15 == 12) by (bit_vector);
        }
    };
    assert(pshufb(b, m) =~= counter_block(iv, c));
}

pub proof fn lemma_counter_block_len(iv: Seq<u8>, c: int)
    requires
        iv.len() == 12,
    ensures
        counter_block(iv, c).len() == 16,
{
    reveal(counter_block);
}

/// Reversing a register's bytes makes the block they are.
pub proof fn lemma_rev(v: u128, r: u128)
    requires
        bytes16(r) == pshufb(bytes16(v), rev_mask()),
    ensures
        r == be128(bytes16(v)),
        be_bytes(r) == bytes16(v),
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
    assert(pshufb(b, m) =~= Seq::new(16, |k: int| b[15 - k]));
    lemma_rev_be(r, b);
    lemma_be_bytes_rev(r);
    assert(be_bytes(r) =~= b);
}

/// The counter register advanced by `j`.
pub proof fn lemma_ctr_add(v: u128, iv: Seq<u8>, c: int, j: u32)
    requires
        ctr_reg_ok(v, iv, c),
        c >= 0,
    ensures
        ctr_reg_ok(add32x4(v, (j as u128) << 96u128), iv, c + j),
{
    let r = add32x4(v, (j as u128) << 96u128);
    let x = lane32(v, 3);
    assert(lane32(r, 3) == x.wrapping_add(j) && forall|k: int|
        0 <= k < 12 ==> #[trigger] bytes16(r)[k] == bytes16(v)[k]) by {
        let a0 = lane32(v, 0);
        let a1 = lane32(v, 1);
        let a2 = lane32(v, 2);
        let z = (j as u128) << 96u128;
        assert(lane32(z, 0) == 0 && lane32(z, 1) == 0 && lane32(z, 2) == 0 && lane32(z, 3) == j) by {
            assert(((z >> 0u128) as u32) == 0 && ((z >> 32u128) as u32) == 0 && ((z >> 64u128) as u32) == 0 && ((z
                >> 96u128) as u32) == j) by (bit_vector)
                requires
                    z == (j as u128) << 96u128,
            ;
        };
        assert(a0.wrapping_add(0) == a0 && a1.wrapping_add(0) == a1 && a2.wrapping_add(0) == a2);
        let y = x.wrapping_add(j);
        assert(r == (a0 as u128) | (a1 as u128) << 32u128 | (a2 as u128) << 64u128 | (y as u128) << 96u128);
        assert forall|k: int| 0 <= k < 12 implies #[trigger] bytes16(r)[k] == bytes16(v)[k] by {
            let s = (8 * k) as u128;
            assert(((((a0 as u128) | (a1 as u128) << 32u128 | (a2 as u128) << 64u128 | (y as u128) << 96u128) >> s)
                as u8) == ((v >> s) as u8)) by (bit_vector)
                requires
                    s <= 88,
                    a0 == (v >> 0u128) as u32,
                    a1 == (v >> 32u128) as u32,
                    a2 == (v >> 64u128) as u32,
            ;
        };
        assert((((a0 as u128) | (a1 as u128) << 32u128 | (a2 as u128) << 64u128 | (y as u128) << 96u128) >> 96u128)
            as u32 == y) by (bit_vector);
    };
    assert(bytes16(r).subrange(0, 12) =~= bytes16(v).subrange(0, 12));
    assert(x.wrapping_add(j) as int == (x as int + j as int) % 0x1_0000_0000);
    assert(((c % 0x1_0000_0000) + j as int) % 0x1_0000_0000 == (c + j) % 0x1_0000_0000) by {
        vstd::arithmetic::div_mod::lemma_add_mod_noop(c, j as int, 0x1_0000_0000);
        vstd::arithmetic::div_mod::lemma_mod_twice(j as int, 0x1_0000_0000);
    };
}

// ---------------------------------------------------------------------------
// The blocks GHASH reads
// ---------------------------------------------------------------------------

/// Block i of `s` padded with zeros.
pub open spec fn chunk(s: Seq<u8>, i: int) -> Seq<u8> {
    Seq::new(16, |k: int| if 16 * i + k < s.len() { s[16 * i + k] } else { 0u8 })
}

pub proof fn lemma_pad_blocks(s: Seq<u8>)
    ensures
        pad_blocks(s).len() == (s.len() + 15) / 16,
        forall|i: int| 0 <= i < pad_blocks(s).len() ==> #[trigger] pad_blocks(s)[i] == be128(chunk(s, i)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else if s.len() <= 16 {
        assert(s + zeros((16 - s.len()) as nat) =~= chunk(s, 0));
    } else {
        let t = s.skip(16);
        lemma_pad_blocks(t);
        assert(s.take(16) =~= chunk(s, 0));
        assert forall|i: int| 1 <= i < pad_blocks(s).len() implies #[trigger] pad_blocks(s)[i] == be128(chunk(s, i)) by {
            assert(pad_blocks(s)[i] == pad_blocks(t)[i - 1]);
            assert(chunk(t, i - 1) =~= chunk(s, i));
        };
    }
}

/// The blocks of a prefix of whole blocks.
pub proof fn lemma_pad_blocks_prefix(s: Seq<u8>, n: int)
    requires
        0 <= 16 * n <= s.len(),
    ensures
        pad_blocks(s.take(16 * n)) == pad_blocks(s).take(n),
{
    lemma_pad_blocks(s);
    lemma_pad_blocks(s.take(16 * n));
    assert forall|i: int| 0 <= i < n implies chunk(s.take(16 * n), i) == chunk(s, i) by {
        assert(chunk(s.take(16 * n), i) =~= chunk(s, i));
    };
    assert(pad_blocks(s.take(16 * n)) =~= pad_blocks(s).take(n));
}

} // verus!
