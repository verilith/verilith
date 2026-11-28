//! Messages the resolver writes: its queries to servers, and its replies
//! to clients, proven (with verilith-dns's serializer theorems) to parse
//! back to exactly the message decided on.
use crate::rr::*;
use crate::spec::*;
#[cfg(verus_only)]
use verilith_dns::lemmas::*;
#[cfg(verus_only)]
use verilith_dns::message::wire_name;
use verilith_dns::message::Section;
use verilith_dns::spec::*;
#[cfg(verus_only)]
use verilith_dns::spec_rdata::canon_rdata;
use verilith_dns::Message;
use vstd::prelude::*;

verus! {

/// The UDP payload size the resolver offers and asks for (EDNS(0), RFC
/// 6891; 1232 is the DNS Flag Day 2020 value, which avoids fragmentation).
pub const EDNS_SIZE: u16 = 1232;

/// A query to a server: one question, no recursion desired (the resolver
/// iterates itself), and an EDNS(0) OPT record offering `EDNS_SIZE`, with
/// the DO bit (RFC 3225), so signed zones send their RRSIGs and NSEC
/// records.
pub fn build_query(id: u16, name: &[u8], qtype: u16) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(b) ==> parse_message(b@) matches Some(m) && m.id == id && m.flags == 0
            && m.questions.len() == 1 && m.questions[0] == (SpecQuestion {
            qname: wire_name(name@).unwrap(),
            qtype,
            qclass: CLASS_IN,
        }),
{
    let mut m = Message::new(id, 0);
    if m.add_question(name, qtype, CLASS_IN).is_err() {
        return None;
    }
    let root: [u8; 1] = [0];
    if m.add_record(Section::Additional, root.as_slice(), TYPE_OPT, EDNS_SIZE, 0x8000, &[]).is_err() {
        return None;
    }
    Some(m.to_bytes())
}

/// A record as verilith-dns stores it once added to a message.
pub open spec fn spec_rec(r: RrS) -> SpecRecord {
    SpecRecord {
        name: wire_name(r.name).unwrap(),
        rtype: r.rtype,
        rclass: r.rclass,
        ttl: r.ttl,
        rdata: canon_rdata(r.rdata, r.rtype, 0, r.rdata.len() as int).unwrap(),
    }
}

pub open spec fn reply_flags(rd: bool, tc: bool, ad: bool, code: u16) -> u16 {
    (0x8000 + (if tc { 0x0200int } else { 0 }) + (if rd { 0x0100int } else { 0 }) + 0x0080 + (if ad {
        0x0020int
    } else {
        0
    }) + code) as u16
}

/// What a reply to `client` says, when it says `code` with these records.
pub open spec fn reply_ok(m: SpecMessage, client: SpecMessage, code: u16, answers: Seq<RrS>, authority: Seq<RrS>, ad_ok: bool) -> bool {
    &&& m.id == client.id
    &&& crate::spec::ad(m.flags) ==> ad_ok && !tc(m.flags) && rcode(m.flags) == code
    &&& qr(m.flags)
    &&& opcode(m.flags) == 0
    &&& rd(m.flags) == rd(client.flags)
    &&& m.questions == client.questions
    // Either the reply says exactly what was decided, or it is truncated
    // (TC, no records: the client asks again over TCP), or, if a record
    // could not be written, it is SERVFAIL with no records.
    &&& if !tc(m.flags) && rcode(m.flags) == code {
        &&& m.answers == answers.map_values(|r: RrS| spec_rec(r))
        &&& m.authorities == authority.map_values(|r: RrS| spec_rec(r))
    } else {
        &&& m.answers.len() == 0
        &&& m.authorities.len() == 0
        &&& tc(m.flags) || rcode(m.flags) == RCODE_SERVFAIL
    }
}

proof fn lemma_flags(rd: bool, tc: bool, ad: bool, code: u16)
    requires
        code < 16,
    ensures
        qr(reply_flags(rd, tc, ad, code)),
        opcode(reply_flags(rd, tc, ad, code)) == 0,
        crate::spec::rd(reply_flags(rd, tc, ad, code)) == rd,
        crate::spec::tc(reply_flags(rd, tc, ad, code)) == tc,
        crate::spec::ad(reply_flags(rd, tc, ad, code)) == ad,
        rcode(reply_flags(rd, tc, ad, code)) == code,
{
}

fn add_all(m: &mut Message, s: Section, rs: &Vec<Rr>) -> (ok: bool)
    ensures
        rs@.len() == 0 ==> ok,
        ok ==> final(m)@ == match s {
            Section::Answer => SpecMessage {
                answers: old(m)@.answers + rrs(rs@).map_values(|r: RrS| spec_rec(r)),
                ..old(m)@
            },
            Section::Authority => SpecMessage {
                authorities: old(m)@.authorities + rrs(rs@).map_values(|r: RrS| spec_rec(r)),
                ..old(m)@
            },
            Section::Additional => SpecMessage {
                additionals: old(m)@.additionals + rrs(rs@).map_values(|r: RrS| spec_rec(r)),
                ..old(m)@
            },
        },
{
    let ghost m0 = m@;
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            i <= rs@.len(),
            m@ == match s {
                Section::Answer => SpecMessage {
                    answers: m0.answers + rrs(rs@).take(i as int).map_values(|r: RrS| spec_rec(r)),
                    ..m0
                },
                Section::Authority => SpecMessage {
                    authorities: m0.authorities + rrs(rs@).take(i as int).map_values(|r: RrS| spec_rec(r)),
                    ..m0
                },
                Section::Additional => SpecMessage {
                    additionals: m0.additionals + rrs(rs@).take(i as int).map_values(|r: RrS| spec_rec(r)),
                    ..m0
                },
            },
        decreases rs@.len() - i,
    {
        let r = &rs[i];
        let ghost x = r@;
        let ghost before = m@;
        if m.add_record(s, &r.name, r.rtype, r.rclass, r.ttl, &r.rdata).is_err() {
            return false;
        }
        proof {
            let t0 = rrs(rs@).take(i as int).map_values(|r: RrS| spec_rec(r));
            let t1 = rrs(rs@).take(i + 1).map_values(|r: RrS| spec_rec(r));
            assert(rrs(rs@)[i as int] == x);
            assert(t1 =~= t0.push(spec_rec(x)));
            match s {
                Section::Answer => assert(m@.answers =~= m0.answers + t1),
                Section::Authority => assert(m@.authorities =~= m0.authorities + t1),
                Section::Additional => assert(m@.additionals =~= m0.additionals + t1),
            }
        }
        i = i + 1;
    }
    proof {
        assert(rrs(rs@).take(rs@.len() as int) =~= rrs(rs@));
    }
    true
}

/// The client's question in a reply with no records yet.
fn start(client: &Message, rd: bool, tc: bool, ad: bool, code: u16) -> (m: Message)
    requires
        client@.questions.len() == 1,
        code < 16,
    ensures
        m@.id == client@.id,
        m@.flags == reply_flags(rd, tc, ad, code),
        m@.questions == client@.questions,
        m@.answers.len() == 0,
        m@.authorities.len() == 0,
{
    let q = client.question(0).unwrap();
    let f: u16 = 0x8000 + (if tc { 0x0200 } else { 0 }) + (if rd { 0x0100 } else { 0 }) + 0x0080 + (if ad {
        0x0020
    } else {
        0
    }) + code;
    let mut m = Message::new(client.id(), f);
    proof {
        client.lemma_valid();
        let sq = client@.questions[0];
        assert(valid_question(sq));
        lemma_at_whole(ser_name(sq.qname));
        lemma_name_roundtrip(ser_name(sq.qname), 0, sq.qname);
        assert(wire_name(q.name@) == Some(sq.qname));
    }
    let r = m.add_question(q.name, q.qtype, q.qclass);
    proof {
        assert(r is Ok);
        assert(m@.questions =~= client@.questions);
    }
    m
}

/// Adds the OPT record of a reply to a client that sent EDNS(0).
fn add_opt(m: &mut Message)
    ensures
        final(m)@.id == old(m)@.id,
        final(m)@.flags == old(m)@.flags,
        final(m)@.questions == old(m)@.questions,
        final(m)@.answers == old(m)@.answers,
        final(m)@.authorities == old(m)@.authorities,
{
    let root: [u8; 1] = [0];
    let _ = m.add_record(Section::Additional, root.as_slice(), TYPE_OPT, EDNS_SIZE, 0, &[]);
}

/// The reply to `client` (a query with one question) saying `code` with
/// `answers` and `authority`, at most `max` bytes long: if it would be
/// longer it is sent truncated (TC set, no records), so the client asks
/// again over TCP (RFC 7766 §5). `edns`: the client sent an OPT record.
pub fn build_reply(
    client: &Message,
    code: u16,
    answers: &Vec<Rr>,
    authority: &Vec<Rr>,
    edns: bool,
    max: usize,
    ad: bool,
) -> (r: (Vec<u8>, Ghost<SpecMessage>))
    requires
        client@.questions.len() == 1,
        code < 16,
        code == RCODE_SERVFAIL ==> answers@.len() == 0 && authority@.len() == 0,
    ensures
        parse_message(r.0@) == Some(r.1@),
        reply_ok(r.1@, client@, code, rrs(answers@), rrs(authority@), ad),
{
    let rd = (client.flags() / 0x0100) % 2 == 1;
    proof {
        lemma_flags(rd, false, ad, code);
        lemma_flags(rd, true, false, code);
        lemma_flags(rd, false, false, RCODE_SERVFAIL);
    }
    let mut m = start(client, rd, false, ad, code);
    let ok = add_all(&mut m, Section::Answer, answers) && add_all(&mut m, Section::Authority, authority);
    if !ok {
        let mut f = start(client, rd, false, false, RCODE_SERVFAIL);
        if edns {
            add_opt(&mut f);
        }
        let b = f.to_bytes_compressed();
        return (b, Ghost(f@));
    }
    if edns {
        add_opt(&mut m);
    }
    proof {
        assert(m@.answers =~= rrs(answers@).map_values(|r: RrS| spec_rec(r)));
        assert(m@.authorities =~= rrs(authority@).map_values(|r: RrS| spec_rec(r)));
    }
    let b = m.to_bytes_compressed();
    if b.len() <= max {
        return (b, Ghost(m@));
    }
    let mut t = start(client, rd, true, false, code);
    if edns {
        add_opt(&mut t);
    }
    let b = t.to_bytes_compressed();
    (b, Ghost(t@))
}

/// A reply with no records: FORMERR, NOTIMP, REFUSED or SERVFAIL.
pub fn error_reply(client: &Message, code: u16, edns: bool) -> (r: (Vec<u8>, Ghost<SpecMessage>))
    requires
        client@.questions.len() == 1,
        code < 16,
    ensures
        parse_message(r.0@) == Some(r.1@),
        r.1@.id == client@.id,
        qr(r.1@.flags),
        opcode(r.1@.flags) == 0,
        rcode(r.1@.flags) == code,
        r.1@.questions == client@.questions,
        r.1@.answers.len() == 0,
        !crate::spec::ad(r.1@.flags),
{
    let rd = (client.flags() / 0x0100) % 2 == 1;
    proof {
        lemma_flags(rd, false, false, code);
    }
    let mut m = start(client, rd, false, false, code);
    if edns {
        add_opt(&mut m);
    }
    let b = m.to_bytes_compressed();
    (b, Ghost(m@))
}

} // verus!
