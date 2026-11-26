//! Packet headers (§17) and packet numbers (§17.1, Appendix A).
//!
//! [`parse_header`] reads the header of the packet at a position in a
//! datagram, before header protection is removed: what a receiver needs
//! to find the keys and the packet's extent. [`packet_end`] gives where a
//! packet ends, so a datagram's coalesced packets (§12.2) are read one
//! after the other. Once the header protection mask is applied (by the
//! trusted TLS layer), [`decode_pn`] recovers the full packet number.
use crate::spec::*;
use crate::varint;
use verilith_core::prims::extend;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// A packet header (§17), borrowing from the datagram. See `spec::Hdr`.
#[derive(Clone, Copy)]
pub enum Header<'a> {
    /// An Initial, 0-RTT or Handshake packet of version 1.
    Long {
        /// The first byte (its low 4 bits still protected).
        first: u8,
        /// Destination Connection ID.
        dcid: &'a [u8],
        /// Source Connection ID.
        scid: &'a [u8],
        /// Token (Initial packets only; empty otherwise).
        token: &'a [u8],
        /// Length: of the packet number and the payload after the header.
        len: u64,
    },
    /// A Retry packet.
    Retry {
        /// The first byte.
        first: u8,
        /// Destination Connection ID.
        dcid: &'a [u8],
        /// Source Connection ID.
        scid: &'a [u8],
        /// Retry Token.
        token: &'a [u8],
        /// Retry Integrity Tag (16 bytes).
        tag: &'a [u8],
    },
    /// A Version Negotiation packet.
    VersionNegotiation {
        /// The first byte.
        first: u8,
        /// Destination Connection ID.
        dcid: &'a [u8],
        /// Source Connection ID.
        scid: &'a [u8],
        /// Supported Versions, 4 bytes each, big-endian.
        versions: &'a [u8],
    },
    /// A long header of a version other than 1.
    OtherVersion {
        /// The first byte.
        first: u8,
        /// Version.
        version: u32,
        /// Destination Connection ID.
        dcid: &'a [u8],
        /// Source Connection ID.
        scid: &'a [u8],
    },
    /// A 1-RTT packet.
    Short {
        /// The first byte (its low 5 bits still protected).
        first: u8,
        /// Destination Connection ID.
        dcid: &'a [u8],
    },
}

impl<'a> Header<'a> {
    /// The header as `spec::Hdr`.
    pub open spec fn view(self) -> Hdr {
        match self {
            Header::Long { first, dcid, scid, token, len } => Hdr::Long {
                first,
                dcid: dcid@,
                scid: scid@,
                token: token@,
                len,
            },
            Header::Retry { first, dcid, scid, token, tag } => Hdr::Retry {
                first,
                dcid: dcid@,
                scid: scid@,
                token: token@,
                tag: tag@,
            },
            Header::VersionNegotiation { first, dcid, scid, versions } => Hdr::VersionNegotiation {
                first,
                dcid: dcid@,
                scid: scid@,
                versions: u32s(versions@, 0, (versions@.len() / 4) as nat),
            },
            Header::OtherVersion { first, version, dcid, scid } => Hdr::OtherVersion {
                first,
                version,
                dcid: dcid@,
                scid: scid@,
            },
            Header::Short { first, dcid } => Hdr::Short { first, dcid: dcid@ },
        }
    }

    /// A Version Negotiation packet's versions are whole `u32`s.
    pub open spec fn wf(self) -> bool {
        self matches Header::VersionNegotiation { versions, .. } ==> versions@.len() % 4 == 0
    }
}

/// The big-endian `u32` at `b[p]`.
#[inline(always)]
fn read_u32(b: &[u8], p: usize) -> (r: u32)
    requires
        p + 4 <= b@.len(),
    ensures
        r == u32be(b@, p as int),
{
    ((b[p] as u32) << 24) | ((b[p + 1] as u32) << 16) | ((b[p + 2] as u32) << 8) | (b[p + 3] as u32)
}

/// `n` bytes from `p`.
#[inline(always)]
fn take_n<'a>(b: &'a [u8], p: usize, n: usize) -> (r: Option<(&'a [u8], usize)>)
    requires
        p <= b@.len(),
    ensures
        match (r, take(b@, p as int, n as int)) {
            (None, None) => true,
            (Some((d, e)), Some((sd, se))) => d@ == sd && e == se,
            _ => false,
        },
{
    if n > b.len() - p {
        return None;
    }
    Some((slice_subrange(b, p, p + n), p + n))
}

/// The two connection IDs.
#[inline(always)]
fn read_cids<'a>(b: &'a [u8], p: usize, max: u8) -> (r: Option<(&'a [u8], &'a [u8], usize)>)
    requires
        p <= b@.len(),
    ensures
        match (r, cids(b@, p as int, max as int)) {
            (None, None) => true,
            (Some((d, s, e)), Some((sd, ss, se))) => d@ == sd && s@ == ss && e == se,
            _ => false,
        },
        r matches Some((_, _, e)) ==> e <= b@.len(),
{
    if p >= b.len() || b[p] > max {
        return None;
    }
    let (dcid, p1) = match take_n(b, p + 1, b[p] as usize) {
        None => return None,
        Some(v) => v,
    };
    if p1 >= b.len() || b[p1] > max {
        return None;
    }
    let (scid, p2) = match take_n(b, p1 + 1, b[p1] as usize) {
        None => return None,
        Some(v) => v,
    };
    Some((dcid, scid, p2))
}

/// `r` is the exec form of the spec result `s`.
pub open spec fn hres_matches<'a>(r: Option<(Header<'a>, usize)>, s: Option<(Hdr, int)>) -> bool {
    match (r, s) {
        (None, None) => true,
        (Some((h, e)), Some((sh, se))) => h.wf() && h@ == sh && e == se,
        _ => false,
    }
}

/// Parses the header of the packet at `b[p]` in the datagram `b`, whose
/// 1-RTT packets have destination connection IDs of `cid_len` bytes:
/// `spec::header`. `None` means the packet is to be discarded.
pub fn parse_header<'a>(b: &'a [u8], p: usize, cid_len: usize) -> (r: Option<(Header<'a>, usize)>)
    ensures
        hres_matches(r, header(b@, p as int, cid_len as nat)),
        r matches Some((_, e)) ==> p < e <= b@.len(),
{
    if p >= b.len() {
        return None;
    }
    let first = b[p];
    if first & 0x80 == 0 {
        if first & 0x40 == 0 {
            return None;
        }
        let (dcid, e) = match take_n(b, p + 1, cid_len) {
            None => return None,
            Some(v) => v,
        };
        return Some((Header::Short { first, dcid }, e));
    }
    if b.len() - p < 5 {
        return None;
    }
    let version = read_u32(b, p + 1);
    if version == 0 {
        let (dcid, scid, q) = match read_cids(b, p + 5, 255) {
            None => return None,
            Some(v) => v,
        };
        if (b.len() - q) % 4 != 0 {
            return None;
        }
        let versions = slice_subrange(b, q, b.len());
        proof {
            crate::lemmas::lemma_u32s_frame(b@, q as int, ((b@.len() - q) / 4) as nat);
        }
        return Some((Header::VersionNegotiation { first, dcid, scid, versions }, b.len()));
    }
    if version != VERSION_1 {
        let (dcid, scid, q) = match read_cids(b, p + 5, 255) {
            None => return None,
            Some(v) => v,
        };
        return Some((Header::OtherVersion { first, version, dcid, scid }, q));
    }
    if first & 0x40 == 0 {
        return None;
    }
    let (dcid, scid, q) = match read_cids(b, p + 5, MAX_CID_LEN as u8) {
        None => return None,
        Some(v) => v,
    };
    let ty = (first >> 4) & 3;
    if ty == 3 {
        if b.len() - q < 17 {
            return None;
        }
        let token = slice_subrange(b, q, b.len() - 16);
        let tag = slice_subrange(b, b.len() - 16, b.len());
        return Some((Header::Retry { first, dcid, scid, token, tag }, b.len()));
    }
    let (token, q1) = if ty == 0 {
        let (n, q0) = match varint::read(b, q) {
            None => return None,
            Some(v) => v,
        };
        if n > (b.len() - q0) as u64 {
            return None;
        }
        (slice_subrange(b, q0, q0 + n as usize), q0 + n as usize)
    } else {
        (slice_subrange(b, q, q), q)
    };
    proof {
        if ty != 0 {
            assert(b@.subrange(q as int, q as int) =~= Seq::<u8>::empty());
        }
    }
    let (len, e) = match varint::read(b, q1) {
        None => return None,
        Some(v) => v,
    };
    if len > (b.len() - e) as u64 {
        return None;
    }
    Some((Header::Long { first, dcid, scid, token, len }, e))
}

/// Where the packet whose header is `h`, ending at `e`, ends in the
/// datagram `b` (§12.2): `spec::packet_end`.
pub fn packet_end(h: Header, e: usize, b: &[u8]) -> (r: usize)
    requires
        e <= b@.len(),
        h is Long ==> e + h->Long_len <= b@.len(),
    ensures
        r == crate::spec::packet_end(h@, e as int, b@.len() as int),
{
    match h {
        Header::Long { len, .. } => {
            let room = b.len() - e;
            if len <= room as u64 {
                e + len as usize
            } else {
                b.len()
            }
        },
        _ => b.len(),
    }
}

/// Appends the encoding of `v`, big-endian.
#[inline(always)]
fn write_u32(out: &mut Vec<u8>, v: u32)
    ensures
        final(out)@ == old(out)@ + u32_enc(v),
{
    out.push((v >> 24) as u8);
    out.push(((v >> 16) & 0xff) as u8);
    out.push(((v >> 8) & 0xff) as u8);
    out.push((v & 0xff) as u8);
    proof {
        assert(((v >> 16) & 0xff) as u8 == (v >> 16) as u8 && ((v >> 8) & 0xff) as u8 == (v >> 8) as u8
            && (v & 0xff) as u8 == v as u8 && (v >> 24) < 256) by (bit_vector);
        assert(final(out)@ =~= old(out)@ + u32_enc(v));
    }
}

/// Appends the two connection IDs with their lengths.
#[inline(always)]
fn write_cids(out: &mut Vec<u8>, dcid: &[u8], scid: &[u8])
    requires
        dcid@.len() <= 255,
        scid@.len() <= 255,
    ensures
        final(out)@ == old(out)@ + seq![dcid@.len() as u8] + dcid@ + seq![scid@.len() as u8] + scid@,
{
    out.push(dcid.len() as u8);
    extend(out, dcid);
    out.push(scid.len() as u8);
    extend(out, scid);
    proof {
        assert(final(out)@ =~= old(out)@ + seq![dcid@.len() as u8] + dcid@ + seq![scid@.len() as u8] + scid@);
    }
}

/// Appends the encoding of `h` (`spec::header_enc`) to `out`.
#[verifier::rlimit(40)]
pub fn encode_header(h: &Header, out: &mut Vec<u8>)
    requires
        h.wf(),
        header_wf(h@, h@->Short_dcid.len()) || !(h is Short),
        !(h is Short) ==> header_wf(h@, 0),
    ensures
        final(out)@ == old(out)@ + header_enc(h@),
{
    let ghost o = old(out)@;
    match h {
        Header::Long { first, dcid, scid, token, len } => {
            out.push(*first);
            write_u32(out, VERSION_1);
            write_cids(out, dcid, scid);
            if (*first >> 4) & 3 == 0 {
                varint::write(out, token.len() as u64);
                extend(out, token);
            }
            varint::write(out, *len);
            proof {
                assert(out@ =~= o + header_enc(h@));
            }
        },
        Header::Retry { first, dcid, scid, token, tag } => {
            out.push(*first);
            write_u32(out, VERSION_1);
            write_cids(out, dcid, scid);
            extend(out, token);
            extend(out, tag);
            proof {
                assert(out@ =~= o + header_enc(h@));
            }
        },
        Header::VersionNegotiation { first, dcid, scid, versions } => {
            out.push(*first);
            write_u32(out, 0);
            write_cids(out, dcid, scid);
            extend(out, versions);
            proof {
                crate::lemmas::lemma_u32s_raw(versions@);
                assert(out@ =~= o + header_enc(h@));
            }
        },
        Header::OtherVersion { first, version, dcid, scid } => {
            out.push(*first);
            write_u32(out, *version);
            write_cids(out, dcid, scid);
            proof {
                assert(out@ =~= o + header_enc(h@));
            }
        },
        Header::Short { first, dcid } => {
            out.push(*first);
            extend(out, dcid);
            proof {
                assert(out@ =~= o + header_enc(h@));
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Packet numbers
// ---------------------------------------------------------------------------

/// Recovers a packet number from its `8 * n` least significant bits
/// `truncated` (`n` from 1 to 4), when the next packet number expected is
/// `expected` (Appendix A.3): `spec::decode_pn`.
pub fn decode_pn(expected: u64, truncated: u32, n: usize) -> (r: u64)
    requires
        1 <= n <= 4,
        expected < VARINT_LIMIT,
        (truncated as int) < pow2(8 * n as nat),
    ensures
        r as int == crate::spec::decode_pn(expected as int, truncated as int, 8 * n as nat),
{
    proof {
        crate::lemmas::lemma_pow2_bytes();
    }
    let win: u64 = if n == 1 {
        0x100
    } else if n == 2 {
        0x1_0000
    } else if n == 3 {
        0x100_0000
    } else {
        0x1_0000_0000
    };
    let hwin = win / 2;
    let candidate = expected - expected % win + truncated as u64;
    if candidate + hwin <= expected && candidate < VARINT_LIMIT - win {
        candidate + win
    } else if candidate > expected + hwin && candidate >= win {
        candidate - win
    } else {
        candidate
    }
}

/// How many bytes to encode packet number `pn` with, when the peer has
/// acknowledged up to `largest_acked` (`None` before any): Appendix A.2,
/// `spec::pn_len`. More than `2^31` packets in flight cannot be encoded.
pub fn pn_len(pn: u64, largest_acked: Option<u64>) -> (r: usize)
    requires
        largest_acked matches Some(l) ==> l < pn,
    ensures
        r as int == crate::spec::pn_len(pn as int, match largest_acked { Some(l) => l as int, None => -1 }),
{
    let unacked: u64 = match largest_acked {
        Some(l) => pn - l,
        None => if pn == u64::MAX { u64::MAX } else { pn + 1 },
    };
    proof {
        if largest_acked is None && pn == u64::MAX {
            assert(pn as int + 1 > 0x80_0000);
        }
    }
    if unacked <= 0x80 {
        1
    } else if unacked <= 0x8000 {
        2
    } else if unacked <= 0x80_0000 {
        3
    } else {
        4
    }
}

} // verus!
