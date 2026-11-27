//! A server's routing of datagrams to connections (RFC 9000 §5.2, §6,
//! §7.2, §14.1, §17.2.1).
//!
//! Proven:
//!
//! - a connection ID made by [`make_cid`] names its slot: [`cid_slot`]
//!   gives the slot back, and any other length gives none;
//! - [`may_start`] opens a connection only for an Initial packet in a
//!   datagram of at least 1200 bytes (§14.1) whose Destination Connection
//!   ID is at least 8 bytes (§7.2);
//! - [`version_negotiation`] writes a Version Negotiation packet (§17.2.1)
//!   that echoes the client's connection IDs swapped (§6.1) and lists
//!   version 1, and it parses back as exactly that. It is sent only for a
//!   datagram of at least 1200 bytes ([`may_negotiate`], §6.1, §14.1); a
//!   Version Negotiation packet is never answered (`packet::parse_header`
//!   reports it as its own kind).
#[cfg(verus_only)]
use crate::lemmas::*;
use crate::packet::{encode_header, Header};
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The length of the server's connection IDs.
pub const CID_LEN: usize = 8;

/// The smallest datagram that may start a connection or be answered with
/// Version Negotiation (§14.1).
pub const MIN_FIRST: usize = 1200;

/// The slot a connection ID of ours names: its first four bytes.
pub open spec fn slot_spec(c: Seq<u8>) -> Option<u32> {
    if c.len() == CID_LEN {
        Some(u32be(c, 0))
    } else {
        None
    }
}

/// A connection ID for slot `slot`: the slot, big-endian, then four random
/// bytes.
pub fn make_cid(slot: u32, rnd: &[u8]) -> (r: Vec<u8>)
    requires
        rnd@.len() >= 4,
    ensures
        r@.len() == CID_LEN,
        slot_spec(r@) == Some(slot),
        r@.subrange(4, 8) == rnd@.subrange(0, 4),
{
    let mut r: Vec<u8> = Vec::new();
    r.push((slot >> 24u32) as u8);
    r.push((slot >> 16u32) as u8);
    r.push((slot >> 8u32) as u8);
    r.push(slot as u8);
    r.push(rnd[0]);
    r.push(rnd[1]);
    r.push(rnd[2]);
    r.push(rnd[3]);
    proof {
        assert(((((slot >> 24u32) as u8) as u32) << 24u32) | ((((slot >> 16u32) as u8) as u32) << 16u32) | ((((slot
            >> 8u32) as u8) as u32) << 8u32) | ((slot as u8) as u32) == slot) by (bit_vector);
        assert(r@.subrange(4, 8) =~= rnd@.subrange(0, 4));
    }
    r
}

/// The slot connection ID `c` names, if it has our length.
pub fn cid_slot(c: &[u8]) -> (r: Option<u32>)
    ensures
        r == slot_spec(c@),
{
    if c.len() != CID_LEN {
        return None;
    }
    Some(((c[0] as u32) << 24u32) | ((c[1] as u32) << 16u32) | ((c[2] as u32) << 8u32) | (c[3] as u32))
}

/// A datagram may start a connection: it holds an Initial packet (`initial`),
/// fills at least 1200 bytes, and the client's Destination Connection ID is
/// at least 8 bytes.
pub fn may_start(initial: bool, datagram_len: usize, dcid_len: usize) -> (r: bool)
    ensures
        r == (initial && datagram_len >= MIN_FIRST && dcid_len >= 8),
{
    initial && datagram_len >= MIN_FIRST && dcid_len >= 8
}

/// A datagram of an unknown version may be answered with Version
/// Negotiation: it is big enough to be a client's first.
pub fn may_negotiate(datagram_len: usize) -> (r: bool)
    ensures
        r == (datagram_len >= MIN_FIRST),
{
    datagram_len >= MIN_FIRST
}

/// The Version Negotiation packet answering a client that used connection
/// IDs `dcid` and `scid`.
pub open spec fn vn_spec(rnd: u8, dcid: Seq<u8>, scid: Seq<u8>) -> Hdr {
    Hdr::VersionNegotiation { first: 0x80u8 | (rnd & 0x7fu8), dcid: scid, scid: dcid, versions: seq![VERSION_1] }
}

/// Writes the Version Negotiation packet for a client's `dcid` and `scid`
/// (each at most 255 bytes, as parsed) to `out`, replacing its contents;
/// false and nothing written if either is longer.
pub fn version_negotiation(dcid: &[u8], scid: &[u8], rnd: u8, out: &mut Vec<u8>) -> (ok: bool)
    ensures
        ok == (dcid@.len() <= 255 && scid@.len() <= 255),
        ok ==> final(out)@ == header_enc(vn_spec(rnd, dcid@, scid@)),
        ok ==> header(final(out)@, 0, 0) == Some((vn_spec(rnd, dcid@, scid@), final(out)@.len() as int)),
{
    if dcid.len() > 255 || scid.len() > 255 {
        return false;
    }
    out.clear();
    let versions: [u8; 4] = [0, 0, 0, 1];
    let first = 0x80u8 | (rnd & 0x7fu8);
    let h = Header::VersionNegotiation { first, dcid: scid, scid: dcid, versions: versions.as_slice() };
    proof {
        assert(first & 0x80 != 0) by (bit_vector)
            requires
                first == 0x80u8 | (rnd & 0x7fu8),
        ;
        let vs = versions@;
        assert(vs[0] == 0 && vs[1] == 0 && vs[2] == 0 && vs[3] == 1);
        assert(((0u8 as u32) << 24u32) | ((0u8 as u32) << 16u32) | ((0u8 as u32) << 8u32) | (1u8 as u32) == 1u32)
            by (bit_vector);
        assert(u32be(vs, 0) == VERSION_1);
        assert(u32s(vs, 4, 0) =~= Seq::<u32>::empty());
        assert(u32s(vs, 0, 1) =~= seq![VERSION_1]);
        assert(h@ == vn_spec(rnd, dcid@, scid@));
        assert(header_wf(h@, 0));
    }
    encode_header(&h, out);
    proof {
        let e = header_enc(vn_spec(rnd, dcid@, scid@));
        assert(out@ =~= e);
        lemma_header_roundtrip(vn_spec(rnd, dcid@, scid@), 0, Seq::empty(), Seq::empty());
        assert(Seq::<u8>::empty() + e + Seq::<u8>::empty() =~= e);
    }
    true
}

} // verus!
