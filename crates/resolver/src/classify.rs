//! What a response from a zone's server means (RFC 1034 §4.3.2, RFC 2308),
//! and which of its records the resolver may believe: only records owned
//! by names at or below the zone the server was asked as (the bailiwick
//! rule, RFC 5452 §6 and §9.1), which is what defeats cache poisoning with
//! out-of-zone records (Kaminsky 2008).
use crate::name::*;
use crate::rr::*;
use crate::spec::*;
#[cfg(verus_only)]
use verilith_dns::message::section_of;
use verilith_dns::message::Section;
use verilith_dns::spec::*;
use verilith_dns::Message;
use vstd::prelude::*;

verus! {

/// What a response says about the name and type asked.
pub enum Outcome {
    /// An answer: CNAME links from the name asked, then the records asked
    /// for at the chain's end.
    Answer(Vec<Rr>),
    /// CNAME links from the name asked, ending at a name this server
    /// cannot speak for (or did not): resolution continues there.
    Cname(Vec<Rr>, Vec<u8>),
    /// The chain's end does not exist (RFC 2308 §2.1): the links, and the
    /// zone's SOA if the server gave one (for the negative TTL).
    NxDomain(Vec<Rr>, Vec<Rr>),
    /// The chain's end exists but has no records of the type (RFC 2308
    /// §2.2).
    NoData(Vec<Rr>, Vec<Rr>),
    /// A referral to a zone below this one: the child zone, its name
    /// servers' names, and the addresses (A, AAAA) given for them.
    Referral(Vec<u8>, Vec<Vec<u8>>, Vec<Rr>),
    /// Nothing usable: try another server.
    Lame,
}

/// The SOA records given for a negative answer are of type SOA and class
/// IN, owned by a name in the zone that is the end name or an ancestor.
pub open spec fn soa_ok(m: SpecMessage, soa: Seq<RrS>, end: Seq<u8>, zone: Seq<u8>) -> bool {
    &&& soa.len() <= 1
    &&& forall|i: int| 0 <= i < soa.len() ==> {
        &&& (#[trigger] soa[i]).rtype == TYPE_SOA
        &&& soa[i].rclass == CLASS_IN
        &&& is_sub(soa[i].name, zone)
        &&& is_sub(end, soa[i].name)
        &&& in_section(m, Section::Authority, soa[i])
    }
}

/// What `classify` proves about its outcome, for a response `m` from a
/// server asked as authority for `zone`, to the question `qname`/`qtype`.
pub open spec fn outcome_ok(o: Outcome, m: SpecMessage, qname: Seq<u8>, qtype: u16, zone: Seq<u8>) -> bool {
    match o {
        Outcome::Answer(rs) => {
            &&& positive(qname, qtype, rrs(rs@))
            &&& all_in_zone(rrs(rs@), zone)
            &&& forall|i: int| 0 <= i < rs@.len() ==> in_section(m, Section::Answer, #[trigger] rrs(rs@)[i])
        },
        Outcome::Cname(rs, t) => {
            &&& links_only(qname, qtype, rrs(rs@))
            &&& rs@.len() > 0
            &&& chain_end(qname, qtype, rrs(rs@)) == t@
            &&& all_in_zone(rrs(rs@), zone)
            &&& forall|i: int| 0 <= i < rs@.len() ==> in_section(m, Section::Answer, #[trigger] rrs(rs@)[i])
        },
        Outcome::NxDomain(rs, soa) => {
            &&& rcode(m.flags) == RCODE_NXDOMAIN
            &&& links_only(qname, qtype, rrs(rs@))
            &&& all_in_zone(rrs(rs@), zone)
            &&& is_sub(chain_end(qname, qtype, rrs(rs@)), zone)
            &&& forall|i: int| 0 <= i < rs@.len() ==> in_section(m, Section::Answer, #[trigger] rrs(rs@)[i])
            &&& soa_ok(m, rrs(soa@), chain_end(qname, qtype, rrs(rs@)), zone)
        },
        Outcome::NoData(rs, soa) => {
            &&& rcode(m.flags) == RCODE_NOERROR
            &&& links_only(qname, qtype, rrs(rs@))
            &&& all_in_zone(rrs(rs@), zone)
            &&& is_sub(chain_end(qname, qtype, rrs(rs@)), zone)
            &&& forall|i: int| 0 <= i < rs@.len() ==> in_section(m, Section::Answer, #[trigger] rrs(rs@)[i])
            &&& soa_ok(m, rrs(soa@), chain_end(qname, qtype, rrs(rs@)), zone)
        },
        Outcome::Referral(z, ns, glue) => {
            // The child zone is strictly below this one and at or above
            // the name asked: referrals only ever go down, toward the name.
            // Each name server name is the target of an NS record of the
            // child zone in the authority section.
            &&& deleg_ok(m, qname, zone, z@, ns@)
            &&& ns@.len() > 0
            // Each address is an A or AAAA record of the additional
            // section, for one of those names, and in this zone.
            &&& glue_ok(m, rrs(glue@), ns@, zone)
        },
        Outcome::Lame => true,
    }
}

/// The answer section's records that are final at `cur`, in the zone.
fn finals_at(m: &Message, cur: &[u8], qtype: u16, zone: &[u8]) -> (r: Vec<Rr>)
    ensures
        forall|i: int| 0 <= i < r@.len() ==> {
            let x = #[trigger] rrs(r@)[i];
            final_rr(x, cur@, qtype) && is_sub(x.name, zone@) && in_section(m@, Section::Answer, x)
        },
{
    let n = m.record_count(Section::Answer);
    let mut out: Vec<Rr> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == section_of(m@, Section::Answer).len(),
            i <= n,
            forall|k: int| 0 <= k < out@.len() ==> {
                let x = #[trigger] out@[k]@;
                final_rr(x, cur@, qtype) && is_sub(x.name, zone@) && in_section(m@, Section::Answer, x)
            },
        decreases n - i,
    {
        let r = take_record(m, Section::Answer, i);
        let t = r.rtype;
        if (qtype == TYPE_ANY || t == qtype) && r.rclass == CLASS_IN && eq_ci_exec(&r.name, cur)
            && is_sub_exec(&r.name, zone) {
            out.push(r);
        }
        i = i + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < out@.len() implies {
            let x = #[trigger] rrs(out@)[i];
            final_rr(x, cur@, qtype) && is_sub(x.name, zone@) && in_section(m@, Section::Answer, x)
        } by {
            assert(rrs(out@)[i] == out@[i]@);
        }
    }
    out
}

/// The first CNAME link at `cur` in the answer section, in the zone.
fn link_at(m: &Message, cur: &[u8], qtype: u16, zone: &[u8]) -> (r: Option<Rr>)
    ensures
        r matches Some(x) ==> cname_link(x@, cur@, qtype) && is_sub(x@.name, zone@) && in_section(
            m@,
            Section::Answer,
            x@,
        ),
{
    if qtype == TYPE_CNAME || qtype == TYPE_ANY {
        return None;
    }
    let n = m.record_count(Section::Answer);
    let mut i: usize = 0;
    while i < n
        invariant
            n == section_of(m@, Section::Answer).len(),
            i <= n,
            qtype != TYPE_CNAME && qtype != TYPE_ANY,
        decreases n - i,
    {
        let r = take_record(m, Section::Answer, i);
        if r.rtype == TYPE_CNAME && r.rclass == CLASS_IN && eq_ci_exec(&r.name, cur) && is_sub_exec(
            &r.name,
            zone,
        ) {
            proof {
                assert(eq_ci(r@.name, cur@));
                assert(cname_link(r@, cur@, qtype));
                assert(in_section(m@, Section::Answer, r@));
            }
            return Some(r);
        }
        i = i + 1;
    }
    None
}

/// The first SOA of the authority section in the zone, at or above `end`.
fn soa_for(m: &Message, end: &[u8], zone: &[u8]) -> (r: Vec<Rr>)
    ensures
        soa_ok(m@, rrs(r@), end@, zone@),
{
    let n = m.record_count(Section::Authority);
    let mut i: usize = 0;
    while i < n
        invariant
            n == section_of(m@, Section::Authority).len(),
            i <= n,
        decreases n - i,
    {
        let r = take_record(m, Section::Authority, i);
        if r.rtype == TYPE_SOA && r.rclass == CLASS_IN && is_sub_exec(&r.name, zone) && is_sub_exec(end, &r.name) {
            let mut v: Vec<Rr> = Vec::new();
            v.push(r);
            proof {
                assert(rrs(v@)[0] == v@[0]@);
            }
            return v;
        }
        i = i + 1;
    }
    let v: Vec<Rr> = Vec::new();
    proof {
        assert(rrs(v@).len() == 0);
    }
    v
}

pub open spec fn ns_ok(m: SpecMessage, z: Seq<u8>, ns: Seq<Vec<u8>>) -> bool {
    forall|j: int| 0 <= j < ns.len() ==> exists|r: RrS| {
        &&& #[trigger] in_section(m, Section::Authority, r)
        &&& r.rtype == TYPE_NS
        &&& r.rclass == CLASS_IN
        &&& eq_ci(r.name, z)
        &&& r.rdata == (#[trigger] ns[j])@
    }
}

pub open spec fn deleg_ok(m: SpecMessage, cur: Seq<u8>, zone: Seq<u8>, z: Seq<u8>, ns: Seq<Vec<u8>>) -> bool {
    &&& is_sub(cur, z)
    &&& is_sub(z, zone)
    &&& !eq_ci(z, zone)
    &&& ns_ok(m, z, ns)
}

pub open spec fn glue_one(m: SpecMessage, g: RrS, ns: Seq<Vec<u8>>, zone: Seq<u8>) -> bool {
    &&& g.rtype == TYPE_A || g.rtype == TYPE_AAAA
    &&& g.rclass == CLASS_IN
    &&& is_sub(g.name, zone)
    &&& in_section(m, Section::Additional, g)
    &&& exists|j: int| 0 <= j < ns.len() && eq_ci(g.name, (#[trigger] ns[j])@)
}

pub open spec fn glue_ok(m: SpecMessage, glue: Seq<RrS>, ns: Seq<Vec<u8>>, zone: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < glue.len() ==> glue_one(m, #[trigger] glue[i], ns, zone)
}

/// The NS records of the authority section that delegate a child zone of
/// `zone` at or above `cur`: the child zone and the name servers' names.
fn delegation(m: &Message, cur: &[u8], zone: &[u8]) -> (r: Option<(Vec<u8>, Vec<Vec<u8>>)>)
    ensures
        r matches Some((z, ns)) ==> deleg_ok(m@, cur@, zone@, z@, ns@) && ns@.len() > 0,
{
    let n = m.record_count(Section::Authority);
    let mut child: Option<Vec<u8>> = None;
    let mut ns: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == section_of(m@, Section::Authority).len(),
            i <= n,
            child is None ==> ns@.len() == 0,
            child is Some ==> ns@.len() > 0,
            child matches Some(z) ==> deleg_ok(m@, cur@, zone@, z@, ns@),
        decreases n - i,
    {
        let r = take_record(m, Section::Authority, i);
        if r.rtype == TYPE_NS && r.rclass == CLASS_IN {
            let take = match &child {
                Some(z) => eq_ci_exec(&r.name, z),
                None => is_sub_exec(cur, &r.name) && is_sub_exec(&r.name, zone) && !eq_ci_exec(&r.name, zone),
            };
            if take {
                let ghost rv = r@;
                let ghost was = child;
                if child.is_none() {
                    child = Some(to_vec(&r.name));
                    proof {
                        lemma_eq_ci_refl(r.name@);
                    }
                }
                let ghost z = child.unwrap()@;
                let ghost ns0 = ns@;
                proof {
                    assert(eq_ci(rv.name, z));
                    assert(is_sub(cur@, z));
                    assert(is_sub(z, zone@));
                    assert(!eq_ci(z, zone@));
                }
                ns.push(r.rdata);
                proof {
                    assert(ns@.len() == ns0.len() + 1);
                    assert forall|j: int| 0 <= j < ns@.len() implies exists|r: RrS| {
                        &&& #[trigger] in_section(m@, Section::Authority, r)
                        &&& r.rtype == TYPE_NS
                        &&& r.rclass == CLASS_IN
                        &&& eq_ci(r.name, z)
                        &&& r.rdata == (#[trigger] ns@[j])@
                    } by {
                        if j < ns0.len() {
                            assert(ns@[j] == ns0[j]);
                        } else {
                            assert(ns@[j]@ == rv.rdata);
                            assert(in_section(m@, Section::Authority, rv));
                            assert(rv.rtype == TYPE_NS && rv.rclass == CLASS_IN && eq_ci(rv.name, z));
                        }
                    }
                    assert(deleg_ok(m@, cur@, zone@, z, ns@));
                }
            }
        }
        i = i + 1;
    }
    match child {
        Some(z) => Some((z, ns)),
        None => None,
    }
}

/// The A and AAAA records of the additional section for one of `ns`, in
/// the zone.
fn glue_for(m: &Message, ns: &Vec<Vec<u8>>, zone: &[u8]) -> (r: Vec<Rr>)
    ensures
        glue_ok(m@, rrs(r@), ns@, zone@),
{
    let n = m.record_count(Section::Additional);
    let mut out: Vec<Rr> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == section_of(m@, Section::Additional).len(),
            i <= n,
            forall|k: int| 0 <= k < out@.len() ==> glue_one(m@, (#[trigger] out@[k])@, ns@, zone@),
        decreases n - i,
    {
        let r = take_record(m, Section::Additional, i);
        if (r.rtype == TYPE_A || r.rtype == TYPE_AAAA) && r.rclass == CLASS_IN && is_sub_exec(&r.name, zone) {
            let mut j: usize = 0;
            let mut hit = false;
            while j < ns.len()
                invariant
                    j <= ns@.len(),
                    hit ==> exists|j: int| 0 <= j < ns@.len() && eq_ci(r.name@, (#[trigger] ns@[j])@),
                decreases ns@.len() - j,
            {
                if eq_ci_exec(&r.name, &ns[j]) {
                    hit = true;
                }
                j = j + 1;
            }
            if hit {
                out.push(r);
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < rrs(out@).len() implies glue_one(m@, #[trigger] rrs(out@)[i], ns@, zone@) by {
            assert(rrs(out@)[i] == out@[i]@);
        }
    }
    out
}

/// What response `m` (taken: `response_ok`) from a server for `zone` says
/// about `qname`/`qtype`. Only records owned by names in `zone` are used.
pub fn classify(m: &Message, qname: &[u8], qtype: u16, zone: &[u8]) -> (o: Outcome)
    ensures
        outcome_ok(o, m@, qname@, qtype, zone@),
{
    let n = m.record_count(Section::Answer);
    if n > 65535 {
        return Outcome::Lame;
    }
    let mut cur: Vec<u8> = to_vec(qname);
    let mut rs: Vec<Rr> = Vec::new();
    let mut steps: usize = 0;
    proof {
        assert(rrs(rs@) =~= Seq::<RrS>::empty());
    }
    while steps <= n
        invariant
            n == section_of(m@, Section::Answer).len(),
            n <= 65535,
            links_only(qname@, qtype, rrs(rs@)),
            chain_end(qname@, qtype, rrs(rs@)) == cur@,
            all_in_zone(rrs(rs@), zone@),
            forall|i: int| 0 <= i < rs@.len() ==> in_section(m@, Section::Answer, #[trigger] rrs(rs@)[i]),
        decreases n + 1 - steps,
    {
        if !is_sub_exec(&cur, zone) {
            break;
        }
        let f = finals_at(m, &cur, qtype, zone);
        if f.len() > 0 {
            let ghost a = rrs(rs@);
            let ghost fv = rrs(f@);
            proof {
                assert(fv.len() > 0);
                assert(fv[0] == rrs(f@)[0]);
                lemma_final_not_link(fv[0], cur@, qtype);
                assert(chain(cur@, qtype, fv));
                assert(chain_links(cur@, qtype, fv) == 0);
                lemma_chain_append(qname@, qtype, a, fv);
            }
            extend_rrs(&mut rs, &f);
            proof {
                assert(rrs(rs@) == a + fv);
                assert forall|i: int| 0 <= i < rs@.len() implies is_sub(#[trigger] rrs(rs@)[i].name, zone@)
                    && in_section(m@, Section::Answer, rrs(rs@)[i]) by {
                    if i >= a.len() {
                        assert(rrs(rs@)[i] == fv[i - a.len()]);
                    } else {
                        assert(rrs(rs@)[i] == a[i]);
                    }
                }
            }
            return Outcome::Answer(rs);
        }
        match link_at(m, &cur, qtype, zone) {
            Some(r) => {
                let ghost a = rrs(rs@);
                let ghost one = seq![r@];
                proof {
                    assert(one.drop_first() =~= Seq::<RrS>::empty());
                    assert(one[0] == r@);
                    assert(chain(r@.rdata, qtype, one.drop_first()));
                    assert(chain_links(r@.rdata, qtype, one.drop_first()) == 0);
                    assert(chain(cur@, qtype, one));
                    assert(chain_links(cur@, qtype, one) == 1);
                    assert(chain_end(r@.rdata, qtype, one.drop_first()) == r@.rdata);
                    assert(chain_end(cur@, qtype, one) == r@.rdata);
                    lemma_chain_append(qname@, qtype, a, one);
                }
                cur = to_vec(&r.rdata);
                let ghost rs0 = rs@;
                let ghost rv = r;
                rs.push(r);
                proof {
                    lemma_rrs_push(rs0, rv);
                    assert(rrs(rs@) =~= a + one);
                    assert forall|i: int| 0 <= i < rs@.len() implies is_sub(#[trigger] rrs(rs@)[i].name, zone@)
                        && in_section(m@, Section::Answer, rrs(rs@)[i]) by {
                        if i < a.len() {
                            assert(rrs(rs@)[i] == a[i]);
                        }
                    }
                }
            },
            None => {
                break;
            },
        }
        steps = steps + 1;
    }
    let code = m.flags() % 16;
    let aa_bit = (m.flags() / 0x0400) % 2 == 1;
    if !is_sub_exec(&cur, zone) {
        if rs.len() > 0 {
            return Outcome::Cname(rs, cur);
        }
        return Outcome::Lame;
    }
    if code == RCODE_NXDOMAIN {
        let soa = soa_for(m, &cur, zone);
        return Outcome::NxDomain(rs, soa);
    }
    if code != RCODE_NOERROR {
        return Outcome::Lame;
    }
    let soa = soa_for(m, &cur, zone);
    if rs.len() > 0 {
        if aa_bit || soa.len() > 0 {
            return Outcome::NoData(rs, soa);
        }
        return Outcome::Cname(rs, cur);
    }
    if aa_bit {
        return Outcome::NoData(rs, soa);
    }
    match delegation(m, &cur, zone) {
        Some((z, ns)) => {
            let glue = glue_for(m, &ns, zone);
            proof {
                assert(rrs(rs@).len() == 0);
                assert(cur@ == qname@);
            }
            Outcome::Referral(z, ns, glue)
        },
        None => {
            if soa.len() > 0 {
                Outcome::NoData(rs, soa)
            } else {
                Outcome::Lame
            }
        },
    }
}

} // verus!
