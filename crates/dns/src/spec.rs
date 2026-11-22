//! Executable-independent specification of the RFC 1035 wire format.
//!
//! Parsing is specified as total recursive functions over `Seq<u8>`; every
//! exec function in this crate is proven to compute exactly these functions.
#[cfg(verus_only)]
use crate::spec_rdata::canon_rdata;
#[cfg(verus_only)]
pub use verilith_core::bytes::{parse_u16, parse_u32};
use vstd::prelude::*;

verus! {

/// Maximum length of a single label (RFC 1035 §2.3.4).
pub spec const MAX_LABEL_LEN: nat = 63;

/// Maximum wire length of a name, including the root octet (RFC 1035 §2.3.4).
pub spec const MAX_NAME_WIRE_LEN: nat = 255;

/// Length of the fixed message header (RFC 1035 §4.1.1).
pub spec const HEADER_LEN: nat = 12;

/// A domain name: its labels, excluding the terminating root label.
pub type SpecName = Seq<Seq<u8>>;

pub struct SpecQuestion {
    pub qname: SpecName,
    pub qtype: u16,
    pub qclass: u16,
}

pub struct SpecRecord {
    pub name: SpecName,
    pub rtype: u16,
    pub rclass: u16,
    pub ttl: u32,
    /// The RDATA in canonical form (`spec_rdata::canon_rdata`): names
    /// inside it are decompressed, so it means the same wherever it is
    /// placed.
    pub rdata: Seq<u8>,
}

/// A DNS message. Section counts are implied by the section lengths.
pub struct SpecMessage {
    pub id: u16,
    /// QR, Opcode, AA, TC, RD, RA, Z and RCODE, as the raw 16-bit field.
    pub flags: u16,
    pub questions: Seq<SpecQuestion>,
    pub answers: Seq<SpecRecord>,
    pub authorities: Seq<SpecRecord>,
    pub additionals: Seq<SpecRecord>,
}

// ---------------------------------------------------------------------------
// Serialization (uncompressed, canonical form)
// ---------------------------------------------------------------------------

pub open spec fn ser_u16(x: u16) -> Seq<u8> {
    seq![(x / 256) as u8, (x % 256) as u8]
}

pub open spec fn ser_u32(x: u32) -> Seq<u8> {
    seq![
        (x / 0x100_0000) as u8,
        ((x / 0x1_0000) % 256) as u8,
        ((x / 256) % 256) as u8,
        (x % 256) as u8,
    ]
}

pub open spec fn ser_label(l: Seq<u8>) -> Seq<u8> {
    seq![l.len() as u8] + l
}

/// The labels of a name, without the root octet.
pub open spec fn ser_labels(labels: SpecName) -> Seq<u8>
    decreases labels.len(),
{
    if labels.len() == 0 {
        Seq::empty()
    } else {
        ser_label(labels[0]) + ser_labels(labels.drop_first())
    }
}

pub open spec fn ser_name(n: SpecName) -> Seq<u8> {
    ser_labels(n) + seq![0u8]
}

pub open spec fn ser_question(q: SpecQuestion) -> Seq<u8> {
    ser_name(q.qname) + ser_u16(q.qtype) + ser_u16(q.qclass)
}

pub open spec fn ser_record(r: SpecRecord) -> Seq<u8> {
    ser_name(r.name) + ser_u16(r.rtype) + ser_u16(r.rclass) + ser_u32(r.ttl) + ser_u16(
        r.rdata.len() as u16,
    ) + r.rdata
}

pub open spec fn ser_questions(qs: Seq<SpecQuestion>) -> Seq<u8>
    decreases qs.len(),
{
    if qs.len() == 0 {
        Seq::empty()
    } else {
        ser_question(qs[0]) + ser_questions(qs.drop_first())
    }
}

pub open spec fn ser_records(rs: Seq<SpecRecord>) -> Seq<u8>
    decreases rs.len(),
{
    if rs.len() == 0 {
        Seq::empty()
    } else {
        ser_record(rs[0]) + ser_records(rs.drop_first())
    }
}

pub open spec fn ser_header(m: SpecMessage) -> Seq<u8> {
    ser_u16(m.id) + ser_u16(m.flags) + ser_u16(m.questions.len() as u16) + ser_u16(
        m.answers.len() as u16,
    ) + ser_u16(m.authorities.len() as u16) + ser_u16(m.additionals.len() as u16)
}

pub open spec fn ser_message(m: SpecMessage) -> Seq<u8> {
    ser_header(m) + ser_questions(m.questions) + ser_records(m.answers) + ser_records(
        m.authorities,
    ) + ser_records(m.additionals)
}

// ---------------------------------------------------------------------------
// Well-formedness
// ---------------------------------------------------------------------------

pub open spec fn valid_label(l: Seq<u8>) -> bool {
    1 <= l.len() <= MAX_LABEL_LEN
}

pub open spec fn valid_name(n: SpecName) -> bool {
    &&& forall|i: int| 0 <= i < n.len() ==> valid_label(#[trigger] n[i])
    &&& ser_name(n).len() <= MAX_NAME_WIRE_LEN
}

pub open spec fn valid_question(q: SpecQuestion) -> bool {
    valid_name(q.qname)
}

pub open spec fn valid_record(r: SpecRecord) -> bool {
    &&& valid_name(r.name)
    &&& r.rdata.len() <= u16::MAX
    &&& canon_rdata(r.rdata, r.rtype, 0, r.rdata.len() as int) == Some(r.rdata)
}

pub open spec fn valid_records(rs: Seq<SpecRecord>) -> bool {
    &&& rs.len() <= u16::MAX
    &&& forall|i: int| 0 <= i < rs.len() ==> valid_record(#[trigger] rs[i])
}

pub open spec fn valid_message(m: SpecMessage) -> bool {
    &&& m.questions.len() <= u16::MAX
    &&& forall|i: int| 0 <= i < m.questions.len() ==> valid_question(#[trigger] m.questions[i])
    &&& valid_records(m.answers)
    &&& valid_records(m.authorities)
    &&& valid_records(m.additionals)
}

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

/// Decodes the labels of a (possibly compressed) name starting at `pos`.
///
/// `seg` is the start of the current run of contiguous labels. A compression
/// pointer must target an offset strictly before `seg` (the rule c-ares and
/// BIND enforce, from RFC 1035 §4.1.4's "prior occurrence"; it implies RFC
/// 9267 §2's "smaller than the offset at which the compression pointer is
/// located"). Since `seg` strictly decreases on every jump, pointer loops are
/// impossible. The target must also be a label length octet (RFC 9267 §2).
///
/// Returns the labels and the offset just past the name's terminator in the
/// current segment (the root octet, or the 2-byte pointer).
pub open spec fn parse_labels(b: Seq<u8>, pos: int, seg: int) -> Option<(SpecName, int)>
    decreases seg, b.len() - pos,
{
    if pos < 0 || pos >= b.len() || seg < 0 || pos < seg {
        None
    } else {
        let c = b[pos];
        if c == 0 {
            Some((Seq::empty(), pos + 1))
        } else if c >= 192 {
            if pos + 1 >= b.len() {
                None
            } else {
                let target = (c as int - 192) * 256 + b[pos + 1] as int;
                if target >= seg {
                    None
                } else if b[target] >= 64 {
                    // RFC 9267 §2: a pointer must land on a label length
                    // octet (0..=63, the root octet included), never on
                    // another pointer.
                    None
                } else {
                    match parse_labels(b, target, target) {
                        Some((labels, _)) => Some((labels, pos + 2)),
                        None => None,
                    }
                }
            }
        } else if c >= 64 {
            // 0b01 and 0b10 prefixes are reserved.
            None
        } else if pos + 1 + c as int > b.len() {
            None
        } else {
            let l = b.subrange(pos + 1, pos + 1 + c as int);
            match parse_labels(b, pos + 1 + c as int, seg) {
                Some((rest, end)) => Some((seq![l] + rest, end)),
                None => None,
            }
        }
    }
}

/// Decodes a name at `pos`, rejecting names whose uncompressed wire form
/// exceeds 255 octets. Returns the name and the offset where the message
/// continues.
pub open spec fn parse_name(b: Seq<u8>, pos: int) -> Option<(SpecName, int)> {
    match parse_labels(b, pos, pos) {
        Some((n, end)) => if ser_name(n).len() <= MAX_NAME_WIRE_LEN {
            Some((n, end))
        } else {
            None
        },
        None => None,
    }
}

pub open spec fn parse_question(b: Seq<u8>, pos: int) -> Option<(SpecQuestion, int)> {
    match parse_name(b, pos) {
        None => None,
        Some((qname, p1)) => match parse_u16(b, p1) {
            None => None,
            Some((qtype, p2)) => match parse_u16(b, p2) {
                None => None,
                Some((qclass, p3)) => Some((SpecQuestion { qname, qtype, qclass }, p3)),
            },
        },
    }
}

pub open spec fn parse_record(b: Seq<u8>, pos: int) -> Option<(SpecRecord, int)> {
    match parse_name(b, pos) {
        None => None,
        Some((name, p1)) => match parse_u16(b, p1) {
            None => None,
            Some((rtype, p2)) => match parse_u16(b, p2) {
                None => None,
                Some((rclass, p3)) => match parse_u32(b, p3) {
                    None => None,
                    Some((ttl, p4)) => match parse_u16(b, p4) {
                        None => None,
                        Some((rdlen, p5)) => if p5 + rdlen as int <= b.len() {
                            // Names inside RDATA are decompressed here, so a
                            // record never refers to the rest of its message.
                            match canon_rdata(b, rtype, p5, p5 + rdlen as int) {
                                Some(rdata) => Some(
                                    (SpecRecord { name, rtype, rclass, ttl, rdata }, p5 + rdlen as int),
                                ),
                                None => None,
                            }
                        } else {
                            None
                        },
                    },
                },
            },
        },
    }
}

pub open spec fn parse_questions(b: Seq<u8>, pos: int, n: nat) -> Option<(Seq<SpecQuestion>, int)>
    decreases n,
{
    if n == 0 {
        Some((Seq::empty(), pos))
    } else {
        match parse_question(b, pos) {
            None => None,
            Some((q, p)) => match parse_questions(b, p, (n - 1) as nat) {
                None => None,
                Some((qs, p2)) => Some((seq![q] + qs, p2)),
            },
        }
    }
}

pub open spec fn parse_records(b: Seq<u8>, pos: int, n: nat) -> Option<(Seq<SpecRecord>, int)>
    decreases n,
{
    if n == 0 {
        Some((Seq::empty(), pos))
    } else {
        match parse_record(b, pos) {
            None => None,
            Some((r, p)) => match parse_records(b, p, (n - 1) as nat) {
                None => None,
                Some((rs, p2)) => Some((seq![r] + rs, p2)),
            },
        }
    }
}

/// Decodes a whole message. The section counts must account for exactly the
/// bytes present (RFC 9267 §6), so trailing bytes are rejected.
pub open spec fn parse_message(b: Seq<u8>) -> Option<SpecMessage> {
    if b.len() < HEADER_LEN {
        None
    } else {
        let id = parse_u16(b, 0).unwrap().0;
        let flags = parse_u16(b, 2).unwrap().0;
        let qd = parse_u16(b, 4).unwrap().0;
        let an = parse_u16(b, 6).unwrap().0;
        let ns = parse_u16(b, 8).unwrap().0;
        let ar = parse_u16(b, 10).unwrap().0;
        match parse_questions(b, 12, qd as nat) {
            None => None,
            Some((questions, p1)) => match parse_records(b, p1, an as nat) {
                None => None,
                Some((answers, p2)) => match parse_records(b, p2, ns as nat) {
                    None => None,
                    Some((authorities, p3)) => match parse_records(b, p3, ar as nat) {
                        None => None,
                        Some((additionals, end)) => if end == b.len() {
                            Some(
                                SpecMessage {
                                    id,
                                    flags,
                                    questions,
                                    answers,
                                    authorities,
                                    additionals,
                                },
                            )
                        } else {
                            None
                        },
                    },
                },
            },
        }
    }
}

} // verus!
