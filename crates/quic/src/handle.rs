//! Checks a server makes on frames as it handles them, beyond parsing
//! (RFC 9000 §19.3, §19.15, §19.16).
//!
//! Proven:
//!
//! - [`ack_delay`] scales an ACK frame's ACK Delay by `2^exponent`,
//!   saturating rather than losing high bits (the field may be up to
//!   2^62 - 1, the exponent up to 20);
//! - [`new_cid_allowed`]: a NEW_CONNECTION_ID frame is a PROTOCOL_VIOLATION
//!   when we send to a zero-length connection ID (§19.15);
//! - [`retire_allowed`]: RETIRE_CONNECTION_ID may only name a sequence
//!   number we issued (§19.16).
use vstd::prelude::*;

verus! {

/// `d` doubled `e` times, saturating at `u64::MAX`.
pub open spec fn sat_shl(d: u64, e: nat) -> u64
    decreases e,
{
    if e == 0 {
        d
    } else {
        let h = sat_shl(d, (e - 1) as nat);
        if h > u64::MAX / 2 { u64::MAX } else { (2 * h) as u64 }
    }
}

/// Doubling saturates: a value is exact until it would pass `u64::MAX`.
proof fn lemma_sat_shl(d: u64, e: nat)
    ensures
        sat_shl(d, e) == u64::MAX || sat_shl(d, e) as int == d * pow2(e),
        sat_shl(d, e) >= d,
    decreases e,
{
    if e > 0 {
        lemma_sat_shl(d, (e - 1) as nat);
        vstd::arithmetic::power2::lemma_pow2_unfold(e);
        let h = sat_shl(d, (e - 1) as nat);
        if h != u64::MAX && h <= u64::MAX / 2 {
            assert(2 * h == 2 * (d * pow2((e - 1) as nat))) by (nonlinear_arith)
                requires
                    h as int == d * pow2((e - 1) as nat),
            ;
            assert(d * pow2(e) == 2 * (d * pow2((e - 1) as nat))) by (nonlinear_arith)
                requires
                    pow2(e) == 2 * pow2((e - 1) as nat),
            ;
            assert(sat_shl(d, e) == (2 * h) as u64);
        }
    } else {
        assert(vstd::arithmetic::power2::pow2(0) == 1) by {
            vstd::arithmetic::power::lemma_pow0(2);
        }
    }
}

pub open spec fn pow2(e: nat) -> int {
    vstd::arithmetic::power2::pow2(e) as int
}

/// The ACK Delay of an ACK frame, in microseconds, from its field and the
/// peer's ack_delay_exponent (§18.2: at most 20; a larger one is treated
/// as 20 here, though the transport parameter check refuses it).
pub fn ack_delay(field: u64, exponent: u64) -> (r: u64)
    ensures
        r == sat_shl(field, if exponent > 20 { 20 } else { exponent as nat }),
        r == u64::MAX || r as int == field * pow2(if exponent > 20 { 20 } else { exponent as nat }),
        r >= field,
{
    let e = if exponent > 20 { 20 } else { exponent };
    let mut r = field;
    let mut i: u64 = 0;
    while i < e
        invariant
            0 <= i <= e <= 20,
            r == sat_shl(field, i as nat),
        decreases e - i,
    {
        r = if r > u64::MAX / 2 { u64::MAX } else { 2 * r };
        i = i + 1;
    }
    proof {
        lemma_sat_shl(field, e as nat);
    }
    r
}

/// A NEW_CONNECTION_ID frame is allowed: we send to a connection ID that is
/// not empty (§19.15).
pub fn new_cid_allowed(remote_cid_len: usize) -> (r: bool)
    ensures
        r == (remote_cid_len > 0),
{
    remote_cid_len > 0
}

/// RETIRE_CONNECTION_ID with sequence number `seq` is allowed: we issued it
/// (`issued` is the largest sequence number we issued, §19.16).
pub fn retire_allowed(seq: u64, issued: u64) -> (r: bool)
    ensures
        r == (seq <= issued),
{
    seq <= issued
}

} // verus!
