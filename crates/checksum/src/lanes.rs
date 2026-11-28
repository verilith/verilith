//! CRC-32 over three interleaved lanes, for CPUs with a CRC-32 instruction.
//!
//! One CRC instruction depends on the one before it, so a single chain
//! runs at the instruction's latency (three cycles for eight bytes). Three
//! independent chains over three adjacent blocks run at its throughput, and
//! are then combined: the register after `A ++ B` from `c` is the register
//! after `A`, stepped past `B`'s length, XOR the register after `B` from 0.
//!
//! Everything here is verified, against `crc_from`, from verilith-simd's
//! specification of the instruction (`verilith_simd::crc::crc32_u64`).
#[cfg(verus_only)]
use super::{crc_from, lemma_crc_append, lemma_crc_sum, lemma_steps_xor, spec};
use vstd::prelude::*;

verus! {


/// `n` bit steps of the register.
pub const fn steps_exec(c: u32, n: u32) -> (r: u32)
    ensures
        r == spec::crc_steps(c, n as nat),
{
    let mut r = c;
    let mut k = n;
    while k > 0
        invariant
            spec::crc_steps(r, k as nat) == spec::crc_steps(c, n as nat),
        decreases k,
    {
        r = if r & 1 == 1 {
            (r >> 1) ^ 0xedb8_8320
        } else {
            r >> 1
        };
        k = k - 1;
    }
    r
}

} // verus!
verus! {

/// `t[k][v]` is `v` in nibble `k`, stepped `n` times.
pub open spec fn nibs_ok(t: [[u32; 16]; 8], n: nat) -> bool {
    forall|k: int, v: int|
        0 <= k < 8 && 0 <= v < 16 ==> #[trigger] t@[k]@[v] == spec::crc_steps((v as u32) << (4 * k) as u32, n)
}

/// Entry `[k][v]` is the register with nibble `k` equal to `v` (and zero
/// elsewhere) stepped past 32 zero bytes, computed by the compiler with
/// the verified `steps_exec`.
pub exec const NIBS_32: [[u32; 16]; 8]
    ensures
        nibs_ok(NIBS_32, 256),
{
    [
        [
            steps_exec(0u32 << 0u32, 256),
            steps_exec(1u32 << 0u32, 256),
            steps_exec(2u32 << 0u32, 256),
            steps_exec(3u32 << 0u32, 256),
            steps_exec(4u32 << 0u32, 256),
            steps_exec(5u32 << 0u32, 256),
            steps_exec(6u32 << 0u32, 256),
            steps_exec(7u32 << 0u32, 256),
            steps_exec(8u32 << 0u32, 256),
            steps_exec(9u32 << 0u32, 256),
            steps_exec(10u32 << 0u32, 256),
            steps_exec(11u32 << 0u32, 256),
            steps_exec(12u32 << 0u32, 256),
            steps_exec(13u32 << 0u32, 256),
            steps_exec(14u32 << 0u32, 256),
            steps_exec(15u32 << 0u32, 256),
        ],
        [
            steps_exec(0u32 << 4u32, 256),
            steps_exec(1u32 << 4u32, 256),
            steps_exec(2u32 << 4u32, 256),
            steps_exec(3u32 << 4u32, 256),
            steps_exec(4u32 << 4u32, 256),
            steps_exec(5u32 << 4u32, 256),
            steps_exec(6u32 << 4u32, 256),
            steps_exec(7u32 << 4u32, 256),
            steps_exec(8u32 << 4u32, 256),
            steps_exec(9u32 << 4u32, 256),
            steps_exec(10u32 << 4u32, 256),
            steps_exec(11u32 << 4u32, 256),
            steps_exec(12u32 << 4u32, 256),
            steps_exec(13u32 << 4u32, 256),
            steps_exec(14u32 << 4u32, 256),
            steps_exec(15u32 << 4u32, 256),
        ],
        [
            steps_exec(0u32 << 8u32, 256),
            steps_exec(1u32 << 8u32, 256),
            steps_exec(2u32 << 8u32, 256),
            steps_exec(3u32 << 8u32, 256),
            steps_exec(4u32 << 8u32, 256),
            steps_exec(5u32 << 8u32, 256),
            steps_exec(6u32 << 8u32, 256),
            steps_exec(7u32 << 8u32, 256),
            steps_exec(8u32 << 8u32, 256),
            steps_exec(9u32 << 8u32, 256),
            steps_exec(10u32 << 8u32, 256),
            steps_exec(11u32 << 8u32, 256),
            steps_exec(12u32 << 8u32, 256),
            steps_exec(13u32 << 8u32, 256),
            steps_exec(14u32 << 8u32, 256),
            steps_exec(15u32 << 8u32, 256),
        ],
        [
            steps_exec(0u32 << 12u32, 256),
            steps_exec(1u32 << 12u32, 256),
            steps_exec(2u32 << 12u32, 256),
            steps_exec(3u32 << 12u32, 256),
            steps_exec(4u32 << 12u32, 256),
            steps_exec(5u32 << 12u32, 256),
            steps_exec(6u32 << 12u32, 256),
            steps_exec(7u32 << 12u32, 256),
            steps_exec(8u32 << 12u32, 256),
            steps_exec(9u32 << 12u32, 256),
            steps_exec(10u32 << 12u32, 256),
            steps_exec(11u32 << 12u32, 256),
            steps_exec(12u32 << 12u32, 256),
            steps_exec(13u32 << 12u32, 256),
            steps_exec(14u32 << 12u32, 256),
            steps_exec(15u32 << 12u32, 256),
        ],
        [
            steps_exec(0u32 << 16u32, 256),
            steps_exec(1u32 << 16u32, 256),
            steps_exec(2u32 << 16u32, 256),
            steps_exec(3u32 << 16u32, 256),
            steps_exec(4u32 << 16u32, 256),
            steps_exec(5u32 << 16u32, 256),
            steps_exec(6u32 << 16u32, 256),
            steps_exec(7u32 << 16u32, 256),
            steps_exec(8u32 << 16u32, 256),
            steps_exec(9u32 << 16u32, 256),
            steps_exec(10u32 << 16u32, 256),
            steps_exec(11u32 << 16u32, 256),
            steps_exec(12u32 << 16u32, 256),
            steps_exec(13u32 << 16u32, 256),
            steps_exec(14u32 << 16u32, 256),
            steps_exec(15u32 << 16u32, 256),
        ],
        [
            steps_exec(0u32 << 20u32, 256),
            steps_exec(1u32 << 20u32, 256),
            steps_exec(2u32 << 20u32, 256),
            steps_exec(3u32 << 20u32, 256),
            steps_exec(4u32 << 20u32, 256),
            steps_exec(5u32 << 20u32, 256),
            steps_exec(6u32 << 20u32, 256),
            steps_exec(7u32 << 20u32, 256),
            steps_exec(8u32 << 20u32, 256),
            steps_exec(9u32 << 20u32, 256),
            steps_exec(10u32 << 20u32, 256),
            steps_exec(11u32 << 20u32, 256),
            steps_exec(12u32 << 20u32, 256),
            steps_exec(13u32 << 20u32, 256),
            steps_exec(14u32 << 20u32, 256),
            steps_exec(15u32 << 20u32, 256),
        ],
        [
            steps_exec(0u32 << 24u32, 256),
            steps_exec(1u32 << 24u32, 256),
            steps_exec(2u32 << 24u32, 256),
            steps_exec(3u32 << 24u32, 256),
            steps_exec(4u32 << 24u32, 256),
            steps_exec(5u32 << 24u32, 256),
            steps_exec(6u32 << 24u32, 256),
            steps_exec(7u32 << 24u32, 256),
            steps_exec(8u32 << 24u32, 256),
            steps_exec(9u32 << 24u32, 256),
            steps_exec(10u32 << 24u32, 256),
            steps_exec(11u32 << 24u32, 256),
            steps_exec(12u32 << 24u32, 256),
            steps_exec(13u32 << 24u32, 256),
            steps_exec(14u32 << 24u32, 256),
            steps_exec(15u32 << 24u32, 256),
        ],
        [
            steps_exec(0u32 << 28u32, 256),
            steps_exec(1u32 << 28u32, 256),
            steps_exec(2u32 << 28u32, 256),
            steps_exec(3u32 << 28u32, 256),
            steps_exec(4u32 << 28u32, 256),
            steps_exec(5u32 << 28u32, 256),
            steps_exec(6u32 << 28u32, 256),
            steps_exec(7u32 << 28u32, 256),
            steps_exec(8u32 << 28u32, 256),
            steps_exec(9u32 << 28u32, 256),
            steps_exec(10u32 << 28u32, 256),
            steps_exec(11u32 << 28u32, 256),
            steps_exec(12u32 << 28u32, 256),
            steps_exec(13u32 << 28u32, 256),
            steps_exec(14u32 << 28u32, 256),
            steps_exec(15u32 << 28u32, 256),
        ],
    ]
}

/// **Steps a register `n` times**, as the XOR of the table entries of its
/// eight nibbles (the update is linear over GF(2)).
#[inline(always)]
pub const fn shift(t: &[[u32; 16]; 8], x: u32, Ghost(n): Ghost<nat>) -> (r: u32)
    requires
        nibs_ok(*t, n),
    ensures
        r == spec::crc_steps(x, n),
{
    let v0 = x & 15;
    let v1 = (x >> 4) & 15;
    let v2 = (x >> 8) & 15;
    let v3 = (x >> 12) & 15;
    let v4 = (x >> 16) & 15;
    let v5 = (x >> 20) & 15;
    let v6 = (x >> 24) & 15;
    let v7 = x >> 28;
    proof {
        assert(v0 < 16 && v1 < 16 && v2 < 16 && v3 < 16 && v4 < 16 && v5 < 16 && v6 < 16 && v7 < 16) by (bit_vector)
            requires
                v0 == x & 15,
                v1 == (x >> 4) & 15,
                v2 == (x >> 8) & 15,
                v3 == (x >> 12) & 15,
                v4 == (x >> 16) & 15,
                v5 == (x >> 20) & 15,
                v6 == (x >> 24) & 15,
                v7 == x >> 28,
        ;
        let p0 = v0 << 0u32;
        let p1 = v1 << 4u32;
        let p2 = v2 << 8u32;
        let p3 = v3 << 12u32;
        let p4 = v4 << 16u32;
        let p5 = v5 << 20u32;
        let p6 = v6 << 24u32;
        let p7 = v7 << 28u32;
        assert(x == p0 ^ p1 ^ p2 ^ p3 ^ p4 ^ p5 ^ p6 ^ p7) by (bit_vector)
            requires
                p0 == (x & 15) << 0u32,
                p1 == ((x >> 4) & 15) << 4u32,
                p2 == ((x >> 8) & 15) << 8u32,
                p3 == ((x >> 12) & 15) << 12u32,
                p4 == ((x >> 16) & 15) << 16u32,
                p5 == ((x >> 20) & 15) << 20u32,
                p6 == ((x >> 24) & 15) << 24u32,
                p7 == (x >> 28) << 28u32,
        ;
        lemma_steps_xor(p0 ^ p1 ^ p2 ^ p3 ^ p4 ^ p5 ^ p6, p7, n);
        lemma_steps_xor(p0 ^ p1 ^ p2 ^ p3 ^ p4 ^ p5, p6, n);
        lemma_steps_xor(p0 ^ p1 ^ p2 ^ p3 ^ p4, p5, n);
        lemma_steps_xor(p0 ^ p1 ^ p2 ^ p3, p4, n);
        lemma_steps_xor(p0 ^ p1 ^ p2, p3, n);
        lemma_steps_xor(p0 ^ p1, p2, n);
        lemma_steps_xor(p0, p1, n);
        assert(t@[0]@[v0 as int] == spec::crc_steps((v0 as int as u32) << (4 * 0) as u32, n));
        assert(t@[1]@[v1 as int] == spec::crc_steps((v1 as int as u32) << (4 * 1) as u32, n));
        assert(t@[2]@[v2 as int] == spec::crc_steps((v2 as int as u32) << (4 * 2) as u32, n));
        assert(t@[3]@[v3 as int] == spec::crc_steps((v3 as int as u32) << (4 * 3) as u32, n));
        assert(t@[4]@[v4 as int] == spec::crc_steps((v4 as int as u32) << (4 * 4) as u32, n));
        assert(t@[5]@[v5 as int] == spec::crc_steps((v5 as int as u32) << (4 * 5) as u32, n));
        assert(t@[6]@[v6 as int] == spec::crc_steps((v6 as int as u32) << (4 * 6) as u32, n));
        assert(t@[7]@[v7 as int] == spec::crc_steps((v7 as int as u32) << (4 * 7) as u32, n));
    }
    t[0][v0 as usize] ^ t[1][v1 as usize] ^ t[2][v2 as usize] ^ t[3][v3 as usize] ^ t[4][v4 as usize] ^ t[5][v5
        as usize] ^ t[6][v6 as usize] ^ t[7][v7 as usize]
}

/// `2 * n` steps.
pub const fn shift2(t: &[[u32; 16]; 8], x: u32, Ghost(n): Ghost<nat>) -> (r: u32)
    requires
        nibs_ok(*t, n),
    ensures
        r == spec::crc_steps(x, 2 * n),
{
    let a = shift(t, x, Ghost(n));
    proof {
        super::lemma_steps_add(x, n, n);
    }
    shift(t, a, Ghost(n))
}

/// `4 * n` steps, as four `n`-step shifts.
pub const fn shift4(t: &[[u32; 16]; 8], x: u32, Ghost(n): Ghost<nat>) -> (r: u32)
    requires
        nibs_ok(*t, n),
    ensures
        r == spec::crc_steps(x, 4 * n),
{
    let a = shift(t, x, Ghost(n));
    let b = shift(t, a, Ghost(n));
    let c = shift(t, b, Ghost(n));
    proof {
        super::lemma_steps_add(x, n, n);
        super::lemma_steps_add(x, n + n, n);
        super::lemma_steps_add(x, n + n + n, n);
    }
    shift(t, c, Ghost(n))
}

/// `8 * n` steps.
pub const fn shift8(t: &[[u32; 16]; 8], x: u32, Ghost(n): Ghost<nat>) -> (r: u32)
    requires
        nibs_ok(*t, n),
    ensures
        r == spec::crc_steps(x, 8 * n),
{
    let a = shift4(t, x, Ghost(n));
    let b = shift4(t, a, Ghost(n));
    proof {
        super::lemma_steps_add(x, 4 * n, 4 * n);
    }
    b
}

/// Entry `[k][v]` is the register with nibble `k` equal to `v` (and zero
/// elsewhere) stepped past 128 zero bytes, computed by the compiler with
/// `shift4` from the table before.
pub exec const NIBS_128: [[u32; 16]; 8]
    ensures
        nibs_ok(NIBS_128, 1024),
{
    [
        [
            shift4(&NIBS_32, 0u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 1u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 2u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 3u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 4u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 5u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 6u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 7u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 8u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 9u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 10u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 11u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 12u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 13u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 14u32 << 0u32, Ghost(256)),
            shift4(&NIBS_32, 15u32 << 0u32, Ghost(256)),
        ],
        [
            shift4(&NIBS_32, 0u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 1u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 2u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 3u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 4u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 5u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 6u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 7u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 8u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 9u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 10u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 11u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 12u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 13u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 14u32 << 4u32, Ghost(256)),
            shift4(&NIBS_32, 15u32 << 4u32, Ghost(256)),
        ],
        [
            shift4(&NIBS_32, 0u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 1u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 2u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 3u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 4u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 5u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 6u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 7u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 8u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 9u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 10u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 11u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 12u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 13u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 14u32 << 8u32, Ghost(256)),
            shift4(&NIBS_32, 15u32 << 8u32, Ghost(256)),
        ],
        [
            shift4(&NIBS_32, 0u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 1u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 2u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 3u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 4u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 5u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 6u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 7u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 8u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 9u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 10u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 11u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 12u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 13u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 14u32 << 12u32, Ghost(256)),
            shift4(&NIBS_32, 15u32 << 12u32, Ghost(256)),
        ],
        [
            shift4(&NIBS_32, 0u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 1u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 2u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 3u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 4u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 5u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 6u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 7u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 8u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 9u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 10u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 11u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 12u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 13u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 14u32 << 16u32, Ghost(256)),
            shift4(&NIBS_32, 15u32 << 16u32, Ghost(256)),
        ],
        [
            shift4(&NIBS_32, 0u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 1u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 2u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 3u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 4u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 5u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 6u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 7u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 8u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 9u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 10u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 11u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 12u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 13u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 14u32 << 20u32, Ghost(256)),
            shift4(&NIBS_32, 15u32 << 20u32, Ghost(256)),
        ],
        [
            shift4(&NIBS_32, 0u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 1u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 2u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 3u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 4u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 5u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 6u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 7u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 8u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 9u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 10u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 11u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 12u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 13u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 14u32 << 24u32, Ghost(256)),
            shift4(&NIBS_32, 15u32 << 24u32, Ghost(256)),
        ],
        [
            shift4(&NIBS_32, 0u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 1u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 2u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 3u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 4u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 5u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 6u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 7u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 8u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 9u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 10u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 11u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 12u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 13u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 14u32 << 28u32, Ghost(256)),
            shift4(&NIBS_32, 15u32 << 28u32, Ghost(256)),
        ],
    ]
}

/// Entry `[k][v]` is the register with nibble `k` equal to `v` (and zero
/// elsewhere) stepped past 256 zero bytes, computed by the compiler with
/// `shift2` from the table before.
pub exec const NIBS_256: [[u32; 16]; 8]
    ensures
        nibs_ok(NIBS_256, 2048),
{
    [
        [
            shift2(&NIBS_128, 0u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 1u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 2u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 3u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 4u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 5u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 6u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 7u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 8u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 9u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 10u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 11u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 12u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 13u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 14u32 << 0u32, Ghost(1024)),
            shift2(&NIBS_128, 15u32 << 0u32, Ghost(1024)),
        ],
        [
            shift2(&NIBS_128, 0u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 1u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 2u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 3u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 4u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 5u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 6u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 7u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 8u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 9u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 10u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 11u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 12u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 13u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 14u32 << 4u32, Ghost(1024)),
            shift2(&NIBS_128, 15u32 << 4u32, Ghost(1024)),
        ],
        [
            shift2(&NIBS_128, 0u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 1u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 2u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 3u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 4u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 5u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 6u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 7u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 8u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 9u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 10u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 11u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 12u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 13u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 14u32 << 8u32, Ghost(1024)),
            shift2(&NIBS_128, 15u32 << 8u32, Ghost(1024)),
        ],
        [
            shift2(&NIBS_128, 0u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 1u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 2u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 3u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 4u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 5u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 6u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 7u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 8u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 9u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 10u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 11u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 12u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 13u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 14u32 << 12u32, Ghost(1024)),
            shift2(&NIBS_128, 15u32 << 12u32, Ghost(1024)),
        ],
        [
            shift2(&NIBS_128, 0u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 1u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 2u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 3u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 4u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 5u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 6u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 7u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 8u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 9u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 10u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 11u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 12u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 13u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 14u32 << 16u32, Ghost(1024)),
            shift2(&NIBS_128, 15u32 << 16u32, Ghost(1024)),
        ],
        [
            shift2(&NIBS_128, 0u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 1u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 2u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 3u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 4u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 5u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 6u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 7u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 8u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 9u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 10u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 11u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 12u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 13u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 14u32 << 20u32, Ghost(1024)),
            shift2(&NIBS_128, 15u32 << 20u32, Ghost(1024)),
        ],
        [
            shift2(&NIBS_128, 0u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 1u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 2u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 3u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 4u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 5u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 6u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 7u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 8u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 9u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 10u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 11u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 12u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 13u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 14u32 << 24u32, Ghost(1024)),
            shift2(&NIBS_128, 15u32 << 24u32, Ghost(1024)),
        ],
        [
            shift2(&NIBS_128, 0u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 1u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 2u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 3u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 4u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 5u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 6u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 7u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 8u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 9u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 10u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 11u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 12u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 13u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 14u32 << 28u32, Ghost(1024)),
            shift2(&NIBS_128, 15u32 << 28u32, Ghost(1024)),
        ],
    ]
}

/// Entry `[k][v]` is the register with nibble `k` equal to `v` (and zero
/// elsewhere) stepped past 512 zero bytes, computed by the compiler with
/// `shift4` from the table before.
pub exec const NIBS_512: [[u32; 16]; 8]
    ensures
        nibs_ok(NIBS_512, 4096),
{
    [
        [
            shift4(&NIBS_128, 0u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 1u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 2u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 3u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 4u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 5u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 6u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 7u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 8u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 9u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 10u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 11u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 12u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 13u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 14u32 << 0u32, Ghost(1024)),
            shift4(&NIBS_128, 15u32 << 0u32, Ghost(1024)),
        ],
        [
            shift4(&NIBS_128, 0u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 1u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 2u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 3u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 4u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 5u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 6u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 7u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 8u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 9u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 10u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 11u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 12u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 13u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 14u32 << 4u32, Ghost(1024)),
            shift4(&NIBS_128, 15u32 << 4u32, Ghost(1024)),
        ],
        [
            shift4(&NIBS_128, 0u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 1u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 2u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 3u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 4u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 5u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 6u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 7u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 8u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 9u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 10u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 11u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 12u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 13u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 14u32 << 8u32, Ghost(1024)),
            shift4(&NIBS_128, 15u32 << 8u32, Ghost(1024)),
        ],
        [
            shift4(&NIBS_128, 0u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 1u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 2u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 3u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 4u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 5u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 6u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 7u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 8u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 9u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 10u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 11u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 12u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 13u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 14u32 << 12u32, Ghost(1024)),
            shift4(&NIBS_128, 15u32 << 12u32, Ghost(1024)),
        ],
        [
            shift4(&NIBS_128, 0u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 1u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 2u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 3u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 4u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 5u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 6u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 7u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 8u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 9u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 10u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 11u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 12u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 13u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 14u32 << 16u32, Ghost(1024)),
            shift4(&NIBS_128, 15u32 << 16u32, Ghost(1024)),
        ],
        [
            shift4(&NIBS_128, 0u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 1u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 2u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 3u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 4u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 5u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 6u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 7u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 8u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 9u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 10u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 11u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 12u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 13u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 14u32 << 20u32, Ghost(1024)),
            shift4(&NIBS_128, 15u32 << 20u32, Ghost(1024)),
        ],
        [
            shift4(&NIBS_128, 0u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 1u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 2u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 3u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 4u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 5u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 6u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 7u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 8u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 9u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 10u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 11u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 12u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 13u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 14u32 << 24u32, Ghost(1024)),
            shift4(&NIBS_128, 15u32 << 24u32, Ghost(1024)),
        ],
        [
            shift4(&NIBS_128, 0u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 1u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 2u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 3u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 4u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 5u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 6u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 7u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 8u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 9u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 10u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 11u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 12u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 13u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 14u32 << 28u32, Ghost(1024)),
            shift4(&NIBS_128, 15u32 << 28u32, Ghost(1024)),
        ],
    ]
}

/// Entry `[k][v]` is the register with nibble `k` equal to `v` (and zero
/// elsewhere) stepped past 4096 zero bytes, computed by the compiler with
/// `shift8` from the table before.
pub exec const NIBS_4096: [[u32; 16]; 8]
    ensures
        nibs_ok(NIBS_4096, 32768),
{
    [
        [
            shift8(&NIBS_512, 0u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 1u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 2u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 3u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 4u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 5u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 6u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 7u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 8u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 9u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 10u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 11u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 12u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 13u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 14u32 << 0u32, Ghost(4096)),
            shift8(&NIBS_512, 15u32 << 0u32, Ghost(4096)),
        ],
        [
            shift8(&NIBS_512, 0u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 1u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 2u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 3u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 4u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 5u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 6u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 7u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 8u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 9u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 10u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 11u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 12u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 13u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 14u32 << 4u32, Ghost(4096)),
            shift8(&NIBS_512, 15u32 << 4u32, Ghost(4096)),
        ],
        [
            shift8(&NIBS_512, 0u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 1u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 2u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 3u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 4u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 5u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 6u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 7u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 8u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 9u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 10u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 11u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 12u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 13u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 14u32 << 8u32, Ghost(4096)),
            shift8(&NIBS_512, 15u32 << 8u32, Ghost(4096)),
        ],
        [
            shift8(&NIBS_512, 0u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 1u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 2u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 3u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 4u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 5u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 6u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 7u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 8u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 9u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 10u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 11u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 12u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 13u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 14u32 << 12u32, Ghost(4096)),
            shift8(&NIBS_512, 15u32 << 12u32, Ghost(4096)),
        ],
        [
            shift8(&NIBS_512, 0u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 1u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 2u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 3u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 4u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 5u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 6u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 7u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 8u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 9u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 10u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 11u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 12u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 13u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 14u32 << 16u32, Ghost(4096)),
            shift8(&NIBS_512, 15u32 << 16u32, Ghost(4096)),
        ],
        [
            shift8(&NIBS_512, 0u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 1u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 2u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 3u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 4u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 5u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 6u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 7u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 8u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 9u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 10u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 11u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 12u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 13u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 14u32 << 20u32, Ghost(4096)),
            shift8(&NIBS_512, 15u32 << 20u32, Ghost(4096)),
        ],
        [
            shift8(&NIBS_512, 0u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 1u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 2u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 3u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 4u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 5u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 6u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 7u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 8u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 9u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 10u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 11u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 12u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 13u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 14u32 << 24u32, Ghost(4096)),
            shift8(&NIBS_512, 15u32 << 24u32, Ghost(4096)),
        ],
        [
            shift8(&NIBS_512, 0u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 1u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 2u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 3u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 4u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 5u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 6u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 7u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 8u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 9u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 10u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 11u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 12u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 13u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 14u32 << 28u32, Ghost(4096)),
            shift8(&NIBS_512, 15u32 << 28u32, Ghost(4096)),
        ],
    ]
}

} // verus!

verus! {

pub proof fn lemma_steps_zero(n: nat)
    ensures
        spec::crc_steps(0, n) == 0,
    decreases n,
{
    if n > 0 {
        assert(spec::crc_step(0) == 0) by (compute_only);
        lemma_steps_zero((n - 1) as nat);
    }
}

/// The register after `d` from `c` is `c` stepped past `d`, XOR the
/// register after `d` from zero.
pub proof fn lemma_crc_split(c: u32, d: Seq<u8>)
    ensures
        crc_from(c, d) == spec::crc_steps(c, (8 * d.len()) as nat) ^ crc_from(0, d),
{
    lemma_crc_sum(c, d);
    lemma_crc_sum(0, d);
    lemma_steps_zero((8 * d.len()) as nat);
    let t = super::tsum(d, d.len());
    assert(0u32 ^ t == t) by (bit_vector);
}

/// `spec::crc_steps` is verilith-simd's `crc_bits` with CRC-32's
/// polynomial.
pub proof fn lemma_steps_simd(c: u32, n: nat)
    ensures
        spec::crc_steps(c, n) == verilith_simd::crc::crc_bits(verilith_simd::crc::POLY_CRC32, c, n),
    decreases n,
{
    if n > 0 {
        assert(spec::crc_step(c) == verilith_simd::crc::crc_bit(verilith_simd::crc::POLY_CRC32, c));
        lemma_steps_simd(spec::crc_step(c), (n - 1) as nat);
    }
}

/// `crc_from` is verilith-simd's `crc_bytes` with CRC-32's polynomial.
pub proof fn lemma_from_simd(c: u32, d: Seq<u8>)
    ensures
        crc_from(c, d) == verilith_simd::crc::crc_bytes(verilith_simd::crc::POLY_CRC32, c, d),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_from_simd(c, d.drop_last());
        lemma_steps_simd(crc_from(c, d.drop_last()) ^ (d.last() as u32), 8);
    }
}

/// **The CRC-32 instruction**: the register after the eight bytes of `d`
/// at `i`, with verilith-simd's `crc32_u64` (AArch64's `crc32x`), proven
/// from its specification. Needs the CPU's CRC extension, which
/// `cpu::crc32_update` checks.
#[inline(always)]
pub fn crc_word(c: u32, d: &[u8], i: usize) -> (r: u32)
    requires
        verilith_simd::crc::crc_arm(),
        i + 8 <= d@.len(),
    ensures
        r == crc_from(c, d@.subrange(i as int, i + 8)),
{
    let r = verilith_simd::crc::crc32_u64(c, d, i);
    proof {
        lemma_from_simd(c, d@.subrange(i as int, i + 8));
    }
    r
}

/// Three lanes of `lane` bytes each, from `i`: the register after all
/// `3 * lane` bytes.
#[inline(always)]
fn triple(c: u32, d: &[u8], i: usize, lane: usize, cols: &[[u32; 16]; 8]) -> (r: u32)
    requires
        verilith_simd::crc::crc_arm(),
        lane % 8 == 0,
        0 < lane <= 0x1000_0000,
        i + 3 * lane <= d@.len(),
        nibs_ok(*cols, (8 * lane) as nat),
    ensures
        r == crc_from(c, d@.subrange(i as int, i + 3 * lane)),
{
    let n = d.len();
    let mut c0 = c;
    let mut c1: u32 = 0;
    let mut c2: u32 = 0;
    let mut j: usize = 0;
    let ghost a = d@.subrange(i as int, i + lane);
    let ghost b = d@.subrange(i + lane, i + 2 * lane);
    let ghost e = d@.subrange(i + 2 * lane, i + 3 * lane);
    proof {
        assert(a.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(b.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(e.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while j < lane
        invariant
            verilith_simd::crc::crc_arm(),
            lane % 8 == 0,
            0 < lane <= 0x1000_0000,
            n == d@.len(),
            i + 3 * lane <= d@.len(),
            j <= lane,
            j % 8 == 0,
            a == d@.subrange(i as int, i + lane),
            b == d@.subrange(i + lane, i + 2 * lane),
            e == d@.subrange(i + 2 * lane, i + 3 * lane),
            c0 == crc_from(c, a.subrange(0, j as int)),
            c1 == crc_from(0, b.subrange(0, j as int)),
            c2 == crc_from(0, e.subrange(0, j as int)),
        decreases lane - j,
    {
        proof {
            let wa = d@.subrange(i + j, i + j + 8);
            let wb = d@.subrange(i + lane + j, i + lane + j + 8);
            let we = d@.subrange(i + 2 * lane + j, i + 2 * lane + j + 8);
            assert(a.subrange(0, j as int) + wa =~= a.subrange(0, j + 8));
            assert(b.subrange(0, j as int) + wb =~= b.subrange(0, j + 8));
            assert(e.subrange(0, j as int) + we =~= e.subrange(0, j + 8));
            lemma_crc_append(c, a.subrange(0, j as int), wa);
            lemma_crc_append(0, b.subrange(0, j as int), wb);
            lemma_crc_append(0, e.subrange(0, j as int), we);
        }
        c0 = crc_word(c0, d, i + j);
        c1 = crc_word(c1, d, i + lane + j);
        c2 = crc_word(c2, d, i + 2 * lane + j);
        j = j + 8;
    }
    let m = shift(cols, c0, Ghost((8 * lane) as nat)) ^ c1;
    let r = shift(cols, m, Ghost((8 * lane) as nat)) ^ c2;
    proof {
        assert(a.subrange(0, lane as int) =~= a);
        assert(b.subrange(0, lane as int) =~= b);
        assert(e.subrange(0, lane as int) =~= e);
        lemma_crc_split(c0, b);
        lemma_crc_split(m, e);
        lemma_crc_append(c, a, b);
        lemma_crc_append(c, a + b, e);
        assert(a + b + e =~= d@.subrange(i as int, i + 3 * lane));
    }
    r
}

/// **Continues a CRC-32 register over `d`** with three interleaved lanes
/// of the CRC instruction: lanes of 4096 bytes while they fit, then of 512,
/// 256, 128 and 32, then one chain.
#[inline(always)]
pub fn crc32_update(reg: u32, d: &[u8]) -> (r: u32)
    requires
        verilith_simd::crc::crc_arm(),
    ensures
        r == crc_from(reg, d@),
{
    let n = d.len();
    let mut c = reg;
    let mut i: usize = 0;
    proof {
        assert(d@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    // Short inputs go straight to the single chain.
    if n >= 96 {
        while n - i >= 12288
            invariant
                verilith_simd::crc::crc_arm(),
            verilith_simd::crc::crc_arm(),
                n == d@.len(),
                i <= n,
                c == crc_from(reg, d@.subrange(0, i as int)),
            decreases n - i,
        {
            proof {
                let blk = d@.subrange(i as int, i + 12288);
                lemma_crc_append(reg, d@.subrange(0, i as int), blk);
                assert(d@.subrange(0, i as int) + blk =~= d@.subrange(0, i + 12288));
            }
            c = triple(c, d, i, 4096, &NIBS_4096);
            i = i + 12288;
        }
        while n - i >= 1536
            invariant
                verilith_simd::crc::crc_arm(),
            verilith_simd::crc::crc_arm(),
                n == d@.len(),
                i <= n,
                c == crc_from(reg, d@.subrange(0, i as int)),
            decreases n - i,
        {
            proof {
                let blk = d@.subrange(i as int, i + 1536);
                lemma_crc_append(reg, d@.subrange(0, i as int), blk);
                assert(d@.subrange(0, i as int) + blk =~= d@.subrange(0, i + 1536));
            }
            c = triple(c, d, i, 512, &NIBS_512);
            i = i + 1536;
        }
        while n - i >= 768
            invariant
                verilith_simd::crc::crc_arm(),
            verilith_simd::crc::crc_arm(),
                n == d@.len(),
                i <= n,
                c == crc_from(reg, d@.subrange(0, i as int)),
            decreases n - i,
        {
            proof {
                let blk = d@.subrange(i as int, i + 768);
                lemma_crc_append(reg, d@.subrange(0, i as int), blk);
                assert(d@.subrange(0, i as int) + blk =~= d@.subrange(0, i + 768));
            }
            c = triple(c, d, i, 256, &NIBS_256);
            i = i + 768;
        }
        while n - i >= 384
            invariant
                verilith_simd::crc::crc_arm(),
            verilith_simd::crc::crc_arm(),
                n == d@.len(),
                i <= n,
                c == crc_from(reg, d@.subrange(0, i as int)),
            decreases n - i,
        {
            proof {
                let blk = d@.subrange(i as int, i + 384);
                lemma_crc_append(reg, d@.subrange(0, i as int), blk);
                assert(d@.subrange(0, i as int) + blk =~= d@.subrange(0, i + 384));
            }
            c = triple(c, d, i, 128, &NIBS_128);
            i = i + 384;
        }
        while n - i >= 96
            invariant
                verilith_simd::crc::crc_arm(),
            verilith_simd::crc::crc_arm(),
                n == d@.len(),
                i <= n,
                c == crc_from(reg, d@.subrange(0, i as int)),
            decreases n - i,
        {
            proof {
                let blk = d@.subrange(i as int, i + 96);
                lemma_crc_append(reg, d@.subrange(0, i as int), blk);
                assert(d@.subrange(0, i as int) + blk =~= d@.subrange(0, i + 96));
            }
            c = triple(c, d, i, 32, &NIBS_32);
            i = i + 96;
        }
    }
    while n - i >= 8
        invariant
            verilith_simd::crc::crc_arm(),
            n == d@.len(),
            i <= n,
            c == crc_from(reg, d@.subrange(0, i as int)),
        decreases n - i,
    {
        proof {
            let blk = d@.subrange(i as int, i + 8);
            lemma_crc_append(reg, d@.subrange(0, i as int), blk);
            assert(d@.subrange(0, i as int) + blk =~= d@.subrange(0, i + 8));
        }
        c = crc_word(c, d, i);
        i = i + 8;
    }
    let tail = vstd::slice::slice_subrange(d, i, n);
    proof {
        lemma_crc_append(reg, d@.subrange(0, i as int), tail@);
        assert(d@.subrange(0, i as int) + tail@ =~= d@);
    }
    super::crc32_update(c, tail)
}

} // verus!
