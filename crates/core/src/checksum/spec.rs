//! Adler-32 (RFC 1950 §8.2) and CRC-32 (RFC 1952 §8, ISO 3309) as pure
//! functions over `Seq<u8>`: the trusted specification the exec code in
//! `checksum` is proven to compute.
use vstd::prelude::*;

verus! {

pub spec const ADLER_MOD: nat = 65521;

/// Adler-32's running sums A and B (RFC 1950 §8.2), defined by appending one
/// byte at a time.
pub open spec fn adler_a(d: Seq<u8>) -> nat
    decreases d.len(),
{
    if d.len() == 0 {
        1
    } else {
        (adler_a(d.drop_last()) + d.last() as nat) % ADLER_MOD
    }
}

pub open spec fn adler_b(d: Seq<u8>) -> nat
    decreases d.len(),
{
    if d.len() == 0 {
        0
    } else {
        (adler_b(d.drop_last()) + adler_a(d)) % ADLER_MOD
    }
}

pub open spec fn adler32(d: Seq<u8>) -> nat {
    adler_b(d) * 65536 + adler_a(d)
}

/// CRC-32's reversed polynomial (RFC 1952 §8, ISO 3309).
pub spec const CRC_POLY: u32 = 0xedb88320;

/// One bit of the CRC register update.
pub open spec fn crc_step(c: u32) -> u32 {
    if c & 1 == 1 {
        (c >> 1u32) ^ CRC_POLY
    } else {
        c >> 1u32
    }
}

/// `n` bit steps.
pub open spec fn crc_steps(c: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 {
        c
    } else {
        crc_steps(crc_step(c), (n - 1) as nat)
    }
}

/// The CRC register after one more byte.
pub open spec fn crc_byte(c: u32, x: u8) -> u32 {
    crc_steps(c ^ (x as u32), 8)
}

/// The CRC register after `d`, starting from all ones.
pub open spec fn crc_reg(d: Seq<u8>) -> u32
    decreases d.len(),
{
    if d.len() == 0 {
        0xffff_ffff
    } else {
        crc_byte(crc_reg(d.drop_last()), d.last())
    }
}

/// CRC-32 as gzip uses it: the final register, complemented.
pub open spec fn crc32(d: Seq<u8>) -> u32 {
    !crc_reg(d)
}

} // verus!
