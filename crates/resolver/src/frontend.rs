//! A client's query in, the reply out: the whole of what the resolver does
//! with a message from a client, whichever transport it came over (UDP,
//! TCP, DNS over TLS, DNS over HTTPS).
use crate::cache::{DELEG, KEYS};
#[cfg(verus_only)]
use crate::dspec::sec_ok;
use crate::dspec::{Ev, SECURE};
use crate::reply::*;
use crate::resolve::*;
use crate::rr::*;
use crate::spec::*;
use verilith_dns::message::Section;
use verilith_dns::parse::parse;
use verilith_dns::spec::*;
use verilith_dns::Message;
use vstd::prelude::*;

verus! {

/// Queries to servers allowed for one client question, all lookups
/// included (Unbound's `max-sent-count` is 32).
pub const QUERY_BUDGET: u32 = 32;

/// How many zones up a chain of trust may be followed from a name, its
/// CNAME targets' zones included.
pub const VALIDATION_DEPTH: u32 = 12;

/// What the reply to a query says: it parses (to `g`), it is a response
/// to this query (ID, the question exactly), and its answer section is
/// empty or exactly `ans`, a chain for the question as `answer_ok` has it.
///
/// And if it says AD, every record in it was validated from the trust
/// anchors, and the nonexistence it says was proven (`sec_ok`, with the
/// evidence `ev`).
pub open spec fn served_ok(g: SpecMessage, q: SpecMessage, ans: Seq<RrS>, auth: Seq<RrS>, sec: u8, ev: Ev) -> bool {
    &&& g.id == q.id
    &&& ad(g.flags) ==> {
        &&& sec == SECURE
        &&& sec_ok(sec, ev, ser_name(q.questions[0].qname), q.questions[0].qtype, rcode(g.flags), ans, auth)
        &&& g.answers == ans.map_values(|r: RrS| spec_rec(r))
        &&& g.authorities == auth.map_values(|r: RrS| spec_rec(r))
    }
    &&& qr(g.flags)
    &&& opcode(g.flags) == 0
    &&& g.questions == q.questions
    &&& chain(ser_name(q.questions[0].qname), q.questions[0].qtype, ans)
    &&& chain_links(ser_name(q.questions[0].qname), q.questions[0].qtype, ans) <= MAX_CNAME
    &&& ttls_at_most(ans, MAX_TTL)
    &&& g.answers == ans.map_values(|r: RrS| spec_rec(r)) || g.answers.len() == 0
}

/// The UDP payload limit for a reply: 512 without EDNS (RFC 1035 §4.2.1),
/// else what the client offers, between 512 and `EDNS_SIZE`; and whether
/// the client set DO (RFC 3225).
fn udp_limit(m: &Message) -> (r: (bool, usize, bool))
    ensures
        r.1 <= 65535,
{
    let n = m.record_count(Section::Additional);
    let mut i: usize = 0;
    while i < n
        invariant
            n == verilith_dns::message::section_of(m@, Section::Additional).len(),
        decreases n - i,
    {
        let r = m.record(Section::Additional, i).unwrap();
        if r.rtype == TYPE_OPT {
            let size = r.rclass as usize;
            let lim = if size < 512 { 512 } else if size > EDNS_SIZE as usize { EDNS_SIZE as usize } else { size };
            return (true, lim, (r.ttl / 0x8000) % 2 == 1);
        }
        i = i + 1;
    }
    (false, 512, false)
}

/// The reply to the client message `query`, or `None` if it gets none (it
/// does not parse, it is itself a response, or it has no question). `udp`:
/// it came over UDP, so the reply is limited in size; over TCP (and DoT,
/// DoH) it may be 65535 bytes. `budget`: the queries to servers it may
/// send (at most `QUERY_BUDGET`); with 0 it answers from the cache or
/// says SERVFAIL. With trust anchors configured, answers are validated
/// unless the client set CD (RFC 4035 §3.2.2); AD is set on secure ones
/// for a client that set DO or AD (RFC 6840 §5.8).
pub fn serve(roots: &Vec<Vec<u8>>, net: &Net, cache: &Shared, query: &[u8], udp: bool, budget: u32) -> (r: Option<
    (Vec<u8>, Ghost<SpecMessage>, Ghost<Seq<RrS>>, Ghost<Seq<RrS>>, Ghost<u8>, Ghost<Ev>),
>)
    requires
        crate::cache::addrs_ok(roots@),
    ensures
        r matches Some((b, g, ans, auth, sec, ev)) ==> parse_message(query@) matches Some(q) && q.questions.len()
            == 1 && parse_message(b@) == Some(g@) && served_ok(g@, q, ans@, auth@, sec@, ev@),
{
    let m = match parse(query) {
        Some(m) => m,
        None => {
            return None;
        },
    };
    let f = m.flags();
    if f >= 0x8000 || m.question_count() != 1 {
        return None;
    }
    let (edns, lim, dnssec_ok) = udp_limit(&m);
    let max = if udp { lim } else { 65535 };
    let q = m.question(0).unwrap();
    let ghost sq = m@.questions[0];
    assert(q.name@ == ser_name(sq.qname));
    let empty: Ghost<Seq<RrS>> = Ghost(Seq::empty());
    proof {
        assert(empty@.map_values(|r: RrS| spec_rec(r)) =~= Seq::<SpecRecord>::empty());
    }
    let code = if (f / 0x0800) % 16 != 0 {
        RCODE_NOTIMP
    } else if q.qclass != CLASS_IN {
        RCODE_REFUSED
    } else if q.qtype == DELEG || q.qtype == KEYS || (q.qtype >= 251 && q.qtype <= 254) {
        // Type 0, and IXFR, AXFR, MAILB, MAILA: zone transfers and
        // obsolete types are not for a resolver.
        RCODE_NOTIMP
    } else {
        RCODE_NOERROR
    };
    if code != RCODE_NOERROR {
        let (b, g) = error_reply(&m, code, edns);
        proof {
            assert(chain(ser_name(sq.qname), sq.qtype, empty@));
            assert(chain_links(ser_name(sq.qname), sq.qtype, empty@) == 0);
        }
        return Some((b, g, empty, empty, Ghost(0u8), Ghost(crate::dspec::ev_empty())));
    }
    let mut budget = if budget < QUERY_BUDGET { budget } else { QUERY_BUDGET };
    let cd = (f / 0x0010) % 2 == 1;
    let want_ad = dnssec_ok || (f / 0x0020) % 2 == 1;
    let a = resolve(roots, net, cache, q.name, q.qtype, &mut budget, NS_DEPTH, VALIDATION_DEPTH, !cd);
    let r = finish(&m, &a, edns, max, want_ad);
    Some(r)
}

fn finish(m: &Message, a: &Answer, edns: bool, max: usize, want_ad: bool) -> (r: (
    Vec<u8>,
    Ghost<SpecMessage>,
    Ghost<Seq<RrS>>,
    Ghost<Seq<RrS>>,
    Ghost<u8>,
    Ghost<Ev>,
))
    requires
        m@.questions.len() == 1,
        answer_ok(*a, ser_name(m@.questions[0].qname), m@.questions[0].qtype, true) || answer_ok(
            *a,
            ser_name(m@.questions[0].qname),
            m@.questions[0].qtype,
            false,
        ),
    ensures
        parse_message(r.0@) == Some(r.1@),
        served_ok(r.1@, m@, r.2@, r.3@, r.4@, r.5@),
{
    let ad = want_ad && a.sec == SECURE && a.rcode != RCODE_SERVFAIL;
    let (b, g) = build_reply(m, a.rcode, &a.answers, &a.authority, edns, max, ad);
    let ghost ans = rrs(a.answers@);
    let ghost auth = rrs(a.authority@);
    proof {
        let gm = g@;
        assert(reply_ok(gm, m@, a.rcode, ans, auth, ad));
        if !tc(gm.flags) && rcode(gm.flags) == a.rcode {
            assert(gm.answers == ans.map_values(|r: RrS| spec_rec(r)));
        } else {
            assert(gm.answers.len() == 0);
        }
    }
    (b, g, Ghost(ans), Ghost(auth), Ghost(a.sec), a.ev)
}

} // verus!
