//! The specification: what the resolver may believe and what it may answer,
//! as pure functions. Every verified function in this crate is proven
//! against these definitions. Read this file to check the claims.
//!
//! Names are handled in uncompressed wire form (RFC 1035 §3.1: length
//! octet, label, ..., root octet), as verilith-dns hands them out. Label
//! length octets are at most 63, below `A` (65), so comparing two wire
//! forms with ASCII case folded compares the names label by label as
//! RFC 4343 says.
use verilith_dns::spec::*;
use vstd::prelude::*;

verus! {

pub const TYPE_A: u16 = 1;
pub const TYPE_NS: u16 = 2;
pub const TYPE_CNAME: u16 = 5;
pub const TYPE_SOA: u16 = 6;
pub const TYPE_AAAA: u16 = 28;
pub const TYPE_OPT: u16 = 41;
pub const TYPE_DS: u16 = 43;
pub const TYPE_ANY: u16 = 255;
pub const CLASS_IN: u16 = 1;

pub const RCODE_NOERROR: u16 = 0;
pub const RCODE_FORMERR: u16 = 1;
pub const RCODE_SERVFAIL: u16 = 2;
pub const RCODE_NXDOMAIN: u16 = 3;
pub const RCODE_NOTIMP: u16 = 4;
pub const RCODE_REFUSED: u16 = 5;

/// The most CNAME (RFC 1034 §3.6.2) links followed for one client question.
pub const MAX_CNAME: u32 = 8;

/// The largest TTL the resolver keeps or hands out (one day, as Unbound's
/// `cache-max-ttl`).
pub const MAX_TTL: u32 = 86400;

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

/// ASCII lowercase (RFC 4343 §3: only A-Z fold).
pub open spec fn lower(c: u8) -> u8 {
    if 65 <= c && c <= 90 {
        (c + 32) as u8
    } else {
        c
    }
}

/// Two wire-form names are the same name, ignoring ASCII case.
pub open spec fn eq_ci(a: Seq<u8>, b: Seq<u8>) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> lower(#[trigger] a[i]) == lower(b[i])
}

/// `z` is `w` from label boundary `off` on, or from a later one: `z` is
/// `w` or one of its ancestors (RFC 1034 §3.1). Boundaries are found by
/// stepping over each label's length octet and its octets.
pub open spec fn sub_from(w: Seq<u8>, off: int, z: Seq<u8>) -> bool
    decreases w.len() - off,
{
    if off < 0 || off >= w.len() {
        false
    } else if eq_ci(w.subrange(off, w.len() as int), z) {
        true
    } else if w[off] == 0 || off + 1 + w[off] as int >= w.len() {
        false
    } else {
        sub_from(w, off + 1 + w[off] as int, z)
    }
}

/// `w` is at or below `z` in the tree: `z` is `w` or an ancestor of `w`.
/// This is the bailiwick test: data about `w` may come from a server for
/// zone `z` only if `is_sub(w, z)`.
pub open spec fn is_sub(w: Seq<u8>, z: Seq<u8>) -> bool {
    sub_from(w, 0, z)
}

/// The root name in wire form.
pub open spec fn root() -> Seq<u8> {
    seq![0u8]
}

// ---------------------------------------------------------------------------
// Records the resolver holds
// ---------------------------------------------------------------------------

/// A resource record, owned: the name in uncompressed wire form and the
/// RDATA in verilith-dns's canonical form (names in it uncompressed, so a
/// CNAME's RDATA is its target in wire form).
pub struct RrS {
    pub name: Seq<u8>,
    pub rtype: u16,
    pub rclass: u16,
    pub ttl: u32,
    pub rdata: Seq<u8>,
}

/// A record of a parsed message, as the resolver copies it.
pub open spec fn rr_of(r: SpecRecord) -> RrS {
    RrS { name: ser_name(r.name), rtype: r.rtype, rclass: r.rclass, ttl: r.ttl, rdata: r.rdata }
}

/// A record answers a question of type `qtype` (RFC 1034 §3.7.1: QTYPE
/// `*` matches every type).
pub open spec fn type_ok(rtype: u16, qtype: u16) -> bool {
    qtype == TYPE_ANY || rtype == qtype
}

/// A record `r` links `cur` to the next name: a CNAME of class IN owned
/// by `cur`, for a question that is not itself for CNAME or `*`.
pub open spec fn cname_link(r: RrS, cur: Seq<u8>, qtype: u16) -> bool {
    &&& r.rtype == TYPE_CNAME
    &&& r.rclass == CLASS_IN
    &&& qtype != TYPE_CNAME
    &&& qtype != TYPE_ANY
    &&& eq_ci(r.name, cur)
}

/// A record `r` is an answer at `cur`: owned by `cur`, of class IN and of
/// the type asked.
pub open spec fn final_rr(r: RrS, cur: Seq<u8>, qtype: u16) -> bool {
    &&& eq_ci(r.name, cur)
    &&& type_ok(r.rtype, qtype)
    &&& r.rclass == CLASS_IN
}

/// The answer section a resolver may give for `cur`/`qtype`
/// (RFC 1034 §3.6.2, §4.3.2 step 3a and 3b): a chain of CNAME records, each
/// owned by the previous one's target, the first by `cur`, then records
/// of the type asked owned by the chain's last name. Either part may be
/// empty.
pub open spec fn chain(cur: Seq<u8>, qtype: u16, rs: Seq<RrS>) -> bool
    decreases rs.len(),
{
    if rs.len() == 0 {
        true
    } else if cname_link(rs[0], cur, qtype) {
        chain(rs[0].rdata, qtype, rs.drop_first())
    } else {
        forall|i: int| 0 <= i < rs.len() ==> final_rr(#[trigger] rs[i], cur, qtype)
    }
}

/// The name a chain from `cur` ends at: the last CNAME's target, or `cur`.
pub open spec fn chain_end(cur: Seq<u8>, qtype: u16, rs: Seq<RrS>) -> Seq<u8>
    decreases rs.len(),
{
    if rs.len() == 0 {
        cur
    } else if cname_link(rs[0], cur, qtype) {
        chain_end(rs[0].rdata, qtype, rs.drop_first())
    } else {
        cur
    }
}

/// How many CNAME links the chain from `cur` has.
pub open spec fn chain_links(cur: Seq<u8>, qtype: u16, rs: Seq<RrS>) -> nat
    decreases rs.len(),
{
    if rs.len() == 0 {
        0
    } else if cname_link(rs[0], cur, qtype) {
        1 + chain_links(rs[0].rdata, qtype, rs.drop_first())
    } else {
        0
    }
}

/// A chain of CNAME links only, with no answer at its end yet.
pub open spec fn links_only(cur: Seq<u8>, qtype: u16, rs: Seq<RrS>) -> bool {
    chain(cur, qtype, rs) && chain_links(cur, qtype, rs) == rs.len()
}

/// A positive answer: a chain that ends in at least one record of the
/// type asked.
pub open spec fn positive(cur: Seq<u8>, qtype: u16, rs: Seq<RrS>) -> bool {
    chain(cur, qtype, rs) && chain_links(cur, qtype, rs) < rs.len()
}

/// Every record of `rs` is owned by a name at or below `zone`.
pub open spec fn all_in_zone(rs: Seq<RrS>, zone: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> is_sub(#[trigger] rs[i].name, zone)
}

/// Every TTL in `rs` is at most `t`.
pub open spec fn ttls_at_most(rs: Seq<RrS>, t: u32) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> (#[trigger] rs[i]).ttl <= t
}

// ---------------------------------------------------------------------------
// Header fields (RFC 1035 §4.1.1)
// ---------------------------------------------------------------------------

pub open spec fn qr(flags: u16) -> bool {
    flags >= 0x8000
}

pub open spec fn opcode(flags: u16) -> u16 {
    ((flags / 0x0800) % 16) as u16
}

pub open spec fn aa(flags: u16) -> bool {
    (flags / 0x0400) % 2 == 1
}

pub open spec fn tc(flags: u16) -> bool {
    (flags / 0x0200) % 2 == 1
}

pub open spec fn rd(flags: u16) -> bool {
    (flags / 0x0100) % 2 == 1
}

pub open spec fn rcode(flags: u16) -> u16 {
    (flags % 16) as u16
}

// ---------------------------------------------------------------------------
// Which responses are taken (RFC 5452 §9.1)
// ---------------------------------------------------------------------------

/// A response is taken as the answer to the query sent only if it is a
/// response (QR), to a standard query (Opcode 0), with the query's ID and
/// exactly its question: the name byte for byte, so with the random case
/// the query was sent with (0x20 bits, draft-vixie-dnsext-dns0x20), and
/// the same type and class. That the response came from the address and
/// port queried is checked by the socket layer (TRUST.md).
pub open spec fn response_ok(m: SpecMessage, id: u16, qname: Seq<u8>, qtype: u16) -> bool {
    &&& m.id == id
    &&& qr(m.flags)
    &&& opcode(m.flags) == 0
    &&& m.questions.len() == 1
    &&& ser_name(m.questions[0].qname) == qname
    &&& m.questions[0].qtype == qtype
    &&& m.questions[0].qclass == CLASS_IN
}

} // verus!
