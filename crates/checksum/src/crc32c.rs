//! CRC-32C, proven to compute `spec::crc32c`.
//!
//! [`crc32c_update`] is the portable verified kernel (a table lookup per
//! byte). [`crc32c_words`] is the verified kernel for CPUs with a CRC-32C
//! instruction (SSE4.2's `crc32` on x86-64, `crc32cx` on AArch64): one
//! instruction per eight bytes, then the table for the rest, proven from
//! verilith-simd's specification of the instructions (`verilith_simd::crc`,
//! where they and the CPU check [`has_crc32c`] are trusted).
//! [`crc32c`] picks between them (`cpu::crc32c_update`).
#[cfg(verus_only)]
use super::spec::{crc32c_byte, crc32c_reg, crc32c_step, crc32c_steps};
use vstd::prelude::*;

verus! {

/// `T[x]` is the register update for byte `x` from a zero register.
/// `lemma_entries` checks every entry against the spec.
pub const T: [u32; 256] = [
    0x00000000, 0xf26b8303, 0xe13b70f7, 0x1350f3f4, 0xc79a971f, 0x35f1141c, 0x26a1e7e8, 0xd4ca64eb,
    0x8ad958cf, 0x78b2dbcc, 0x6be22838, 0x9989ab3b, 0x4d43cfd0, 0xbf284cd3, 0xac78bf27, 0x5e133c24,
    0x105ec76f, 0xe235446c, 0xf165b798, 0x030e349b, 0xd7c45070, 0x25afd373, 0x36ff2087, 0xc494a384,
    0x9a879fa0, 0x68ec1ca3, 0x7bbcef57, 0x89d76c54, 0x5d1d08bf, 0xaf768bbc, 0xbc267848, 0x4e4dfb4b,
    0x20bd8ede, 0xd2d60ddd, 0xc186fe29, 0x33ed7d2a, 0xe72719c1, 0x154c9ac2, 0x061c6936, 0xf477ea35,
    0xaa64d611, 0x580f5512, 0x4b5fa6e6, 0xb93425e5, 0x6dfe410e, 0x9f95c20d, 0x8cc531f9, 0x7eaeb2fa,
    0x30e349b1, 0xc288cab2, 0xd1d83946, 0x23b3ba45, 0xf779deae, 0x05125dad, 0x1642ae59, 0xe4292d5a,
    0xba3a117e, 0x4851927d, 0x5b016189, 0xa96ae28a, 0x7da08661, 0x8fcb0562, 0x9c9bf696, 0x6ef07595,
    0x417b1dbc, 0xb3109ebf, 0xa0406d4b, 0x522bee48, 0x86e18aa3, 0x748a09a0, 0x67dafa54, 0x95b17957,
    0xcba24573, 0x39c9c670, 0x2a993584, 0xd8f2b687, 0x0c38d26c, 0xfe53516f, 0xed03a29b, 0x1f682198,
    0x5125dad3, 0xa34e59d0, 0xb01eaa24, 0x42752927, 0x96bf4dcc, 0x64d4cecf, 0x77843d3b, 0x85efbe38,
    0xdbfc821c, 0x2997011f, 0x3ac7f2eb, 0xc8ac71e8, 0x1c661503, 0xee0d9600, 0xfd5d65f4, 0x0f36e6f7,
    0x61c69362, 0x93ad1061, 0x80fde395, 0x72966096, 0xa65c047d, 0x5437877e, 0x4767748a, 0xb50cf789,
    0xeb1fcbad, 0x197448ae, 0x0a24bb5a, 0xf84f3859, 0x2c855cb2, 0xdeeedfb1, 0xcdbe2c45, 0x3fd5af46,
    0x7198540d, 0x83f3d70e, 0x90a324fa, 0x62c8a7f9, 0xb602c312, 0x44694011, 0x5739b3e5, 0xa55230e6,
    0xfb410cc2, 0x092a8fc1, 0x1a7a7c35, 0xe811ff36, 0x3cdb9bdd, 0xceb018de, 0xdde0eb2a, 0x2f8b6829,
    0x82f63b78, 0x709db87b, 0x63cd4b8f, 0x91a6c88c, 0x456cac67, 0xb7072f64, 0xa457dc90, 0x563c5f93,
    0x082f63b7, 0xfa44e0b4, 0xe9141340, 0x1b7f9043, 0xcfb5f4a8, 0x3dde77ab, 0x2e8e845f, 0xdce5075c,
    0x92a8fc17, 0x60c37f14, 0x73938ce0, 0x81f80fe3, 0x55326b08, 0xa759e80b, 0xb4091bff, 0x466298fc,
    0x1871a4d8, 0xea1a27db, 0xf94ad42f, 0x0b21572c, 0xdfeb33c7, 0x2d80b0c4, 0x3ed04330, 0xccbbc033,
    0xa24bb5a6, 0x502036a5, 0x4370c551, 0xb11b4652, 0x65d122b9, 0x97baa1ba, 0x84ea524e, 0x7681d14d,
    0x2892ed69, 0xdaf96e6a, 0xc9a99d9e, 0x3bc21e9d, 0xef087a76, 0x1d63f975, 0x0e330a81, 0xfc588982,
    0xb21572c9, 0x407ef1ca, 0x532e023e, 0xa145813d, 0x758fe5d6, 0x87e466d5, 0x94b49521, 0x66df1622,
    0x38cc2a06, 0xcaa7a905, 0xd9f75af1, 0x2b9cd9f2, 0xff56bd19, 0x0d3d3e1a, 0x1e6dcdee, 0xec064eed,
    0xc38d26c4, 0x31e6a5c7, 0x22b65633, 0xd0ddd530, 0x0417b1db, 0xf67c32d8, 0xe52cc12c, 0x1747422f,
    0x49547e0b, 0xbb3ffd08, 0xa86f0efc, 0x5a048dff, 0x8ecee914, 0x7ca56a17, 0x6ff599e3, 0x9d9e1ae0,
    0xd3d3e1ab, 0x21b862a8, 0x32e8915c, 0xc083125f, 0x144976b4, 0xe622f5b7, 0xf5720643, 0x07198540,
    0x590ab964, 0xab613a67, 0xb831c993, 0x4a5a4a90, 0x9e902e7b, 0x6cfbad78, 0x7fab5e8c, 0x8dc0dd8f,
    0xe330a81a, 0x115b2b19, 0x020bd8ed, 0xf0605bee, 0x24aa3f05, 0xd6c1bc06, 0xc5914ff2, 0x37faccf1,
    0x69e9f0d5, 0x9b8273d6, 0x88d28022, 0x7ab90321, 0xae7367ca, 0x5c18e4c9, 0x4f48173d, 0xbd23943e,
    0xf36e6f75, 0x0105ec76, 0x12551f82, 0xe03e9c81, 0x34f4f86a, 0xc69f7b69, 0xd5cf889d, 0x27a40b9e,
    0x79b737ba, 0x8bdcb4b9, 0x988c474d, 0x6ae7c44e, 0xbe2da0a5, 0x4c4623a6, 0x5f16d052, 0xad7d5351,
];

/// Entries `lo..hi` of `T` are 8 steps from their index.
pub open spec fn first_ok(lo: int, hi: int) -> bool
    decreases hi - lo,
{
    if hi - lo <= 0 {
        true
    } else if hi - lo == 1 {
        T[lo] == crc32c_steps(lo as u32, 8)
    } else {
        let mid = lo + (hi - lo) / 2;
        first_ok(lo, mid) && first_ok(mid, hi)
    }
}

proof fn lemma_first_ok(lo: int, hi: int, i: int)
    requires
        first_ok(lo, hi),
        lo <= i < hi,
    ensures
        T[i] == crc32c_steps(i as u32, 8),
    decreases hi - lo,
{
    if hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if i < mid {
            lemma_first_ok(lo, mid, i);
        } else {
            lemma_first_ok(mid, hi, i);
        }
    }
}

/// Every entry is right (checked by evaluation).
pub proof fn lemma_entries()
    ensures
        forall|x: int| 0 <= x < 256 ==> #[trigger] T[x] == crc32c_steps(x as u32, 8),
{
    assert(first_ok(0, 256)) by (compute_only);
    assert forall|x: int| 0 <= x < 256 implies #[trigger] T[x] == crc32c_steps(x as u32, 8) by {
        lemma_first_ok(0, 256, x);
    }
}

/// The CRC update is linear (over GF(2)): a step of an XOR is the XOR of
/// the steps.
proof fn lemma_step_xor(a: u32, b: u32)
    ensures
        crc32c_step(a ^ b) == crc32c_step(a) ^ crc32c_step(b),
{
    assert((if (a ^ b) & 1 == 1 {
        ((a ^ b) >> 1u32) ^ 0x82f63b78u32
    } else {
        (a ^ b) >> 1u32
    }) == (if a & 1 == 1 {
        (a >> 1u32) ^ 0x82f63b78u32
    } else {
        a >> 1u32
    }) ^ (if b & 1 == 1 {
        (b >> 1u32) ^ 0x82f63b78u32
    } else {
        b >> 1u32
    })) by (bit_vector);
}

proof fn lemma_steps_xor(a: u32, b: u32, n: nat)
    ensures
        crc32c_steps(a ^ b, n) == crc32c_steps(a, n) ^ crc32c_steps(b, n),
    decreases n,
{
    if n > 0 {
        lemma_step_xor(a, b);
        lemma_steps_xor(crc32c_step(a), crc32c_step(b), (n - 1) as nat);
    }
}

/// Steps on a register whose low `n` bits are zero just shift it.
proof fn lemma_steps_even(y: u32, n: nat)
    requires
        n < 32,
        y & ((1u32 << n as u32) - 1) as u32 == 0,
    ensures
        crc32c_steps(y, n) == y >> n as u32,
    decreases n,
{
    if n == 0 {
        assert(y >> 0u32 == y) by (bit_vector);
    } else {
        let nu = n as u32;
        assert(y & 1 == 0 && (y >> 1u32) & ((1u32 << (nu - 1) as u32) - 1) as u32 == 0 && (y >> 1u32) >> (nu
            - 1) as u32 == y >> nu) by (bit_vector)
            requires
                0 < nu < 32,
                y & ((1u32 << nu) - 1) as u32 == 0,
        ;
        lemma_steps_even(y >> 1u32, (n - 1) as nat);
    }
}

/// A byte's update is a shift and a table entry.
proof fn lemma_crc32c_byte(c: u32, x: u8)
    ensures
        crc32c_byte(c, x) == (c >> 8u32) ^ T[((c ^ x as u32) & 0xff) as int],
{
    lemma_entries();
    let y = c ^ x as u32;
    let z = y & 0xff;
    let hi = y & 0xffff_ff00u32;
    assert(y == z ^ hi && hi & ((1u32 << 8u32) - 1) as u32 == 0 && hi >> 8u32 == c >> 8u32 && z < 256 && (z as int) as u32
        == z) by (bit_vector)
        requires
            y == c ^ x as u32,
            z == y & 0xff,
            hi == y & 0xffff_ff00u32,
            x < 256,
    ;
    lemma_steps_xor(z, hi, 8);
    lemma_steps_even(hi, 8);
    assert(T[z as int] == crc32c_steps(z, 8));
    let u = c >> 8u32;
    let v = T[z as int];
    assert(v ^ u == u ^ v) by (bit_vector);
}

/// The CRC register after `d`, starting from `c`.
pub open spec fn crc32c_from(c: u32, d: Seq<u8>) -> u32
    decreases d.len(),
{
    if d.len() == 0 {
        c
    } else {
        crc32c_byte(crc32c_from(c, d.drop_last()), d.last())
    }
}

pub proof fn lemma_crc32c_from(d: Seq<u8>)
    ensures
        crc32c_from(0xffff_ffff, d) == crc32c_reg(d),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_crc32c_from(d.drop_last());
    }
}

/// Continues a CRC-32C register over `d`, a byte at a time.
pub fn crc32c_update(reg: u32, d: &[u8]) -> (r: u32)
    ensures
        r == crc32c_from(reg, d@),
{
    let mut c = reg;
    let n = d.len();
    let mut i: usize = 0;
    proof {
        assert(d@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while i < n
        invariant
            n == d@.len(),
            i <= n,
            c == crc32c_from(reg, d@.subrange(0, i as int)),
        decreases n - i,
    {
        let x = d[i];
        proof {
            assert(d@.subrange(0, i + 1).drop_last() =~= d@.subrange(0, i as int));
            assert(d@.subrange(0, i + 1).last() == d@[i as int]);
            lemma_crc32c_byte(c, x);
            assert(((c ^ x as u32) & 0xff) < 256) by (bit_vector);
        }
        c = (c >> 8) ^ T[((c ^ x as u32) & 0xff) as usize];
        i = i + 1;
    }
    proof {
        assert(d@.subrange(0, n as int) =~= d@);
    }
    c
}

/// `crc32c_from` over a concatenation is the register after the first
/// part, continued over the second.
pub proof fn lemma_crc32c_append(c: u32, a: Seq<u8>, b: Seq<u8>)
    ensures
        crc32c_from(c, a + b) == crc32c_from(crc32c_from(c, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_crc32c_append(c, a, b.drop_last());
    }
}

} // verus!

/// The CPU has a CRC-32C instruction (verilith-simd's predicate), and its
/// run-time check.
#[cfg(verus_only)]
pub use verilith_simd::crc::crc32c_cpu;
pub use verilith_simd::crc::has_crc32c;

verus! {

/// `crc32c_steps` is verilith-simd's `crc_bits` with CRC-32C's polynomial.
pub proof fn lemma_steps_simd(c: u32, n: nat)
    ensures
        crc32c_steps(c, n) == verilith_simd::crc::crc_bits(verilith_simd::crc::POLY_CRC32C, c, n),
    decreases n,
{
    if n > 0 {
        assert(crc32c_step(c) == verilith_simd::crc::crc_bit(verilith_simd::crc::POLY_CRC32C, c));
        lemma_steps_simd(crc32c_step(c), (n - 1) as nat);
    }
}

/// `crc32c_from` is verilith-simd's `crc_bytes` with CRC-32C's polynomial,
/// which is how the CRC-32C instructions are specified there.
pub proof fn lemma_from_simd(c: u32, d: Seq<u8>)
    ensures
        crc32c_from(c, d) == verilith_simd::crc::crc_bytes(verilith_simd::crc::POLY_CRC32C, c, d),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_from_simd(c, d.drop_last());
        lemma_steps_simd(crc32c_from(c, d.drop_last()) ^ (d.last() as u32), 8);
    }
}

/// **The CRC-32C instruction**: the register after the eight bytes of
/// `d` at `i`, with verilith-simd's `crc32c_u64` (SSE4.2's `crc32` on
/// x86-64, `crc32cx` on AArch64), proven from its specification.
#[inline(always)]
pub fn crc32c_word(c: u64, d: &[u8], i: usize) -> (r: u64)
    requires
        crc32c_cpu(),
        c < 0x1_0000_0000,
        i + 8 <= d@.len(),
    ensures
        r < 0x1_0000_0000,
        r as u32 == crc32c_from(c as u32, d@.subrange(i as int, i + 8)),
{
    let r = verilith_simd::crc::crc32c_u64(c, d, i);
    proof {
        lemma_from_simd(c as u32, d@.subrange(i as int, i + 8));
    }
    r
}

/// **The CRC-32C instruction on one byte**: `crc32c_byte`, with
/// verilith-simd's `crc32c_u8`.
#[inline(always)]
pub fn crc32c_byte_hw(c: u32, x: u8) -> (r: u32)
    requires
        crc32c_cpu(),
    ensures
        r == crc32c_byte(c, x),
{
    let r = verilith_simd::crc::crc32c_u8(c, x);
    proof {
        lemma_steps_simd(c ^ (x as u32), 8);
    }
    r
}

/// Continues a CRC-32C register over `d` with the CPU's instruction,
/// eight bytes at a time, then a byte at a time. Call it
/// compiled with the instruction enabled (`cpu` does).
#[inline(always)]
pub fn crc32c_words(reg: u32, d: &[u8]) -> (r: u32)
    requires
        crc32c_cpu(),
    ensures
        r == crc32c_from(reg, d@),
{
    let n = d.len();
    let mut w = reg as u64;
    let mut i: usize = 0;
    proof {
        assert(d@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while n - i >= 8
        invariant
            n == d@.len(),
            i <= n,
            crc32c_cpu(),
            w < 0x1_0000_0000,
            w as u32 == crc32c_from(reg, d@.subrange(0, i as int)),
        decreases n - i,
    {
        let w2 = crc32c_word(w, d, i);
        proof {
            lemma_crc32c_append(reg, d@.subrange(0, i as int), d@.subrange(i as int, i + 8));
            assert(d@.subrange(0, i as int) + d@.subrange(i as int, i + 8) =~= d@.subrange(0, i + 8));
        }
        w = w2;
        i = i + 8;
    }
    let mut c = w as u32;
    while i < n
        invariant
            n == d@.len(),
            i <= n,
            crc32c_cpu(),
            c == crc32c_from(reg, d@.subrange(0, i as int)),
        decreases n - i,
    {
        let x = d[i];
        proof {
            assert(d@.subrange(0, i + 1).drop_last() =~= d@.subrange(0, i as int));
            assert(d@.subrange(0, i + 1).last() == d@[i as int]);
        }
        c = crc32c_byte_hw(c, x);
        i = i + 1;
    }
    proof {
        assert(d@.subrange(0, n as int) =~= d@);
    }
    c
}

/// The CRC-32C of `d`.
pub fn crc32c(d: &[u8]) -> (r: u32)
    ensures
        r == super::spec::crc32c(d@),
{
    proof {
        lemma_crc32c_from(d@);
    }
    !super::cpu::crc32c_update(0xffff_ffff, d)
}

} // verus!
