//! The specification of record protection (RFC 8446 §5.2, §5.3), over
//! the AEADs of `crypto.rs`. Trusted, like the other spec files.
use crate::crypto::*;
use crate::spec_keys::*;
use vstd::prelude::*;

verus! {

/// The header of a protected record whose `encrypted_record` is `len`
/// bytes: opaque_type application_data (23), legacy_record_version
/// 0x0303, length. It is also the AEAD's additional_data (§5.2).
pub open spec fn protected_header(len: nat) -> Seq<u8> {
    seq![23u8, 3u8, 3u8, (len / 256) as u8, (len % 256) as u8]
}

/// A protected record of content type `ct` with `content`, sent with
/// sequence number `seq`: `TLSInnerPlaintext` is the content, the type,
/// and no padding.
pub open spec fn seal_record(suite: u16, key: Seq<u8>, iv: Seq<u8>, seq: u64, ct: u8, content: Seq<u8>) -> Seq<
    u8,
> {
    let n = content.len() + 1 + 16;
    protected_header(n) + aead_seal(
        suite,
        key,
        record_nonce(iv, seq),
        protected_header(n),
        content + seq![ct],
    )
}

/// `data` of type `ct` sent as protected records of at most 2^14 bytes of
/// content each, the first with sequence number `seq`.
#[verifier::opaque]
pub open spec fn seal_chunks(suite: u16, key: Seq<u8>, iv: Seq<u8>, seq: u64, ct: u8, data: Seq<u8>) -> Seq<
    u8,
>
    decreases data.len(),
{
    if data.len() == 0 {
        Seq::empty()
    } else {
        let n: int = if data.len() > 16384 { 16384 } else { data.len() as int };
        seal_record(suite, key, iv, seq, ct, data.take(n)) + seal_chunks(
            suite,
            key,
            iv,
            (seq + 1) as u64,
            ct,
            data.skip(n),
        )
    }
}

/// How many records `seal_chunks` makes of `n` bytes.
pub open spec fn chunks(n: nat) -> nat {
    if n == 0 { 0 } else { ((n - 1) / 16384 + 1) as nat }
}

/// `TLSInnerPlaintext` without its padding: the last non-zero byte of
/// `inner[..n]` is the content type, and what is before it the content.
pub open spec fn unpad(inner: Seq<u8>, n: nat) -> Option<(u8, Seq<u8>)>
    decreases n,
{
    if n == 0 || n > inner.len() {
        None
    } else if inner[n - 1] != 0 {
        Some((inner[n - 1], inner.take(n - 1)))
    } else {
        unpad(inner, (n - 1) as nat)
    }
}

/// Why a protected record was refused.
pub enum SpecRecErr {
    /// `record_overflow`: more than 2^14 + 256 bytes of ciphertext, or
    /// more than 2^14 + 1 of TLSInnerPlaintext (§5.2).
    Overflow,
    /// `bad_record_mac`: the AEAD did not verify.
    BadMac,
    /// `unexpected_message`: all padding, no content type.
    NoType,
    /// The sequence number would wrap (§5.3): the connection must end.
    Exhausted,
}

/// A protected record with header `hdr` and `encrypted_record` `body`,
/// received with sequence number `seq`: its content type and content.
pub open spec fn open_record(suite: u16, key: Seq<u8>, iv: Seq<u8>, seq: u64, hdr: Seq<u8>, body: Seq<u8>) -> Result<
    (u8, Seq<u8>),
    SpecRecErr,
> {
    if seq == 0xffff_ffff_ffff_ffffu64 {
        Err(SpecRecErr::Exhausted)
    } else if body.len() > 16640 {
        Err(SpecRecErr::Overflow)
    } else {
        match aead_open(suite, key, record_nonce(iv, seq), hdr, body) {
            None => Err(SpecRecErr::BadMac),
            Some(inner) => if inner.len() > 16385 {
                Err(SpecRecErr::Overflow)
            } else {
                match unpad(inner, inner.len()) {
                    None => Err(SpecRecErr::NoType),
                    Some(r) => Ok(r),
                }
            },
        }
    }
}

} // verus!
