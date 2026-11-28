//! Iterative resolution (RFC 1034 §5.3.3): from the closest known zone
//! down the referrals to an answer, following CNAMEs, with every query to
//! a server paid for from a budget. Verified, over a trusted transport
//! (`Net`, TRUST.md) and the shared cache (`Shared`, whose contract is the
//! verified `Cache`'s).
//!
//! What is proven, for every response any server sends:
//! - resolution terminates, and sends at most `budget` queries in all,
//!   including the lookups of name server addresses it starts, which nest
//!   at most `depth` deep (the NXNSAttack bound, CVE-2020-12662);
//! - every zone cut it moves to is strictly below the last one and at or
//!   above the name asked (`classify`): no referral loops, no upward or
//!   sideways referrals;
//! - only records in the bailiwick of the server that sent them are used
//!   (`classify`);
//! - the answer is a chain for the question asked (`answer_ok`): CNAME
//!   links from the name asked, at most `MAX_CNAME` of them, then records
//!   of the type asked at the chain's end, every TTL at most `MAX_TTL`.
use crate::accept::response_matches;
use crate::cache::*;
use crate::classify::*;
use crate::name::*;
use crate::reply::build_query;
use crate::rr::*;
use crate::spec::*;
use verilith_dns::parse::parse;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

/// The network and the clock, as the resolver uses them. Implemented in
/// `net.rs` (unverified, TRUST.md).
pub trait Transport: Send + Sync {
    /// Sends `query` to the server at `addr` (4 or 16 bytes) and returns
    /// the response, if one came from that address and port in time.
    fn exchange(&self, addr: &[u8], query: &[u8]) -> Option<Vec<u8>>;
    /// Seconds, monotonic.
    fn now(&self) -> u64;
    /// Unpredictable bits (query IDs and the 0x20 case).
    fn random(&self) -> u64;
}

verus! {

#[verifier::external_body]
pub struct Net {
    pub(crate) t: std::sync::Arc<dyn Transport>,
}

impl Net {
    #[verifier::external_body]
    pub fn exchange(&self, addr: &[u8], query: &[u8]) -> (r: Option<Vec<u8>>) {
        self.t.exchange(addr, query)
    }

    #[verifier::external_body]
    pub fn now(&self) -> (t: u64) {
        self.t.now()
    }

    #[verifier::external_body]
    pub fn random(&self) -> (r: u64) {
        self.t.random()
    }
}

/// The cache, shared by every thread: `Cache`s behind locks. The contracts
/// below are the verified `Cache::lookup` and `Cache::insert`'s; the
/// bodies only pick a shard and lock it.
#[verifier::external_body]
pub struct Shared {
    pub(crate) shards: Vec<std::sync::Mutex<Cache>>,
}

impl Shared {
    #[verifier::external_body]
    pub fn lookup(&self, name: &[u8], qtype: u16, now: u64) -> (r: Option<Hit>)
        ensures
            r matches Some(h) ==> hit_ok(h, name@, qtype),
    {
        let s = &self.shards[crate::shared_shard(self.shards.len(), name)];
        s.lock().unwrap_or_else(|e| e.into_inner()).lookup(name, qtype, now)
    }

    #[verifier::external_body]
    pub fn insert(&self, name: &[u8], qtype: u16, now: u64, ttl: u32, data: Data)
        requires
            data_ok(data, name@, qtype),
    {
        let s = &self.shards[crate::shared_shard(self.shards.len(), name)];
        s.lock().unwrap_or_else(|e| e.into_inner()).insert(name, qtype, now, ttl, data)
    }
}

/// The most name server names whose addresses one referral may make the
/// resolver look up (NXNSAttack: BIND, Unbound and Knot cap this too).
pub const MAX_NS_LOOKUPS: usize = 2;

/// The resolver's answer to a question.
pub struct Answer {
    pub rcode: u16,
    pub answers: Vec<Rr>,
    pub authority: Vec<Rr>,
}

/// What the answer to `qname`/`qtype` may be: a chain for the question,
/// ending in records of the type (NOERROR), or in nothing (NOERROR with no
/// data, NXDOMAIN); or SERVFAIL with no records.
pub open spec fn answer_ok(a: Answer, qname: Seq<u8>, qtype: u16) -> bool {
    &&& a.rcode == RCODE_NOERROR || a.rcode == RCODE_NXDOMAIN || a.rcode == RCODE_SERVFAIL
    &&& chain(qname, qtype, rrs(a.answers@))
    &&& chain_links(qname, qtype, rrs(a.answers@)) <= MAX_CNAME
    &&& a.rcode != RCODE_NOERROR ==> links_only(qname, qtype, rrs(a.answers@))
    &&& a.rcode == RCODE_SERVFAIL ==> a.answers@.len() == 0 && a.authority@.len() == 0
    &&& soa_only(rrs(a.authority@))
    &&& ttls_at_most(rrs(a.answers@), MAX_TTL)
    &&& ttls_at_most(rrs(a.authority@), MAX_TTL)
}

pub fn servfail() -> (a: Answer)
    ensures
        a.rcode == RCODE_SERVFAIL,
        a.answers@.len() == 0,
        a.authority@.len() == 0,
{
    Answer { rcode: RCODE_SERVFAIL, answers: Vec::new(), authority: Vec::new() }
}

/// What one walk down the zones for one name ends with.
pub enum Step {
    /// NOERROR (an answer, or no data) or NXDOMAIN: the records, from the
    /// name walked for, and the SOA.
    Done(u16, Vec<Rr>, Vec<Rr>),
    /// CNAME links, to be followed from the target.
    Cname(Vec<Rr>, Vec<u8>),
    Fail,
}

pub open spec fn step_ok(s: Step, cur: Seq<u8>, qtype: u16) -> bool {
    match s {
        Step::Done(code, rs, soa) => {
            &&& code == RCODE_NOERROR || code == RCODE_NXDOMAIN
            &&& chain(cur, qtype, rrs(rs@))
            &&& code == RCODE_NXDOMAIN ==> links_only(cur, qtype, rrs(rs@))
            &&& soa_only(rrs(soa@))
            &&& ttls_at_most(rrs(rs@), MAX_TTL)
            &&& ttls_at_most(rrs(soa@), MAX_TTL)
        },
        Step::Cname(rs, t) => {
            &&& links_only(cur, qtype, rrs(rs@))
            &&& rs@.len() > 0
            &&& eq_ci(chain_end(cur, qtype, rrs(rs@)), t@)
            &&& ttls_at_most(rrs(rs@), MAX_TTL)
        },
        Step::Fail => true,
    }
}

/// `chain_links(cur, qtype, rs)`, counted.
pub fn count_links(cur: &[u8], qtype: u16, rs: &Vec<Rr>) -> (n: usize)
    ensures
        n == chain_links(cur@, qtype, rrs(rs@)),
{
    let mut c: Vec<u8> = to_vec(cur);
    let mut i: usize = 0;
    proof {
        assert(rrs(rs@).skip(0) =~= rrs(rs@));
    }
    while i < rs.len()
        invariant
            i <= rs@.len(),
            chain_links(cur@, qtype, rrs(rs@)) == i + chain_links(c@, qtype, rrs(rs@).skip(i as int)),
        decreases rs@.len() - i,
    {
        let r = &rs[i];
        let ghost tail = rrs(rs@).skip(i as int);
        proof {
            assert(tail[0] == r@);
            assert(tail.drop_first() =~= rrs(rs@).skip(i + 1));
        }
        if !(r.rtype == TYPE_CNAME && r.rclass == CLASS_IN && qtype != TYPE_CNAME && qtype != TYPE_ANY
            && eq_ci_exec(&r.name, &c)) {
            return i;
        }
        c = to_vec(&r.rdata);
        i = i + 1;
    }
    proof {
        assert(rrs(rs@).skip(i as int).len() == 0);
    }
    i
}

/// The smallest TTL in `rs`, at most `MAX_TTL` (`MAX_TTL` for none).
pub fn min_ttl(rs: &Vec<Rr>) -> (t: u32)
    ensures
        t <= MAX_TTL,
{
    let mut t = MAX_TTL;
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            t <= MAX_TTL,
        decreases rs@.len() - i,
    {
        if rs[i].ttl < t {
            t = rs[i].ttl;
        }
        i = i + 1;
    }
    t
}

/// How long a negative answer may be kept (RFC 2308 §5): the smaller of
/// the SOA's TTL and its MINIMUM field (the last 4 octets of its RDATA);
/// 0, not kept, without an SOA.
pub fn negative_ttl(soa: &Vec<Rr>) -> (t: u32)
    ensures
        t <= MAX_TTL,
{
    if soa.len() == 0 {
        return 0;
    }
    let r = &soa[0];
    let n = r.rdata.len();
    if n < 4 {
        return 0;
    }
    let min = ((r.rdata[n - 4] as u32) * 0x100_0000) + ((r.rdata[n - 3] as u32) * 0x1_0000) + ((r.rdata[n
        - 2] as u32) * 0x100) + r.rdata[n - 1] as u32;
    let t = if r.ttl < min { r.ttl } else { min };
    if t > MAX_TTL { MAX_TTL } else { t }
}

/// The addresses (A and AAAA RDATA) among `rs`.
fn addresses(rs: &Vec<Rr>, out: &mut Vec<Vec<u8>>)
    ensures
        forall|i: int| 0 <= i < old(out)@.len() ==> (#[trigger] final(out)@[i]) == old(out)@[i],
        final(out)@.len() >= old(out)@.len(),
        forall|i: int| old(out)@.len() <= i < final(out)@.len() ==> (#[trigger] final(out)@[i])@.len() == 4
            || final(out)@[i]@.len() == 16,
{
    let ghost o0 = out@;
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            out@.len() >= o0.len(),
            forall|i: int| 0 <= i < o0.len() ==> (#[trigger] out@[i]) == o0[i],
            forall|i: int| o0.len() <= i < out@.len() ==> (#[trigger] out@[i])@.len() == 4 || out@[i]@.len()
                == 16,
        decreases rs@.len() - i,
    {
        let r = &rs[i];
        let n = r.rdata.len();
        if (r.rtype == TYPE_A && n == 4) || (r.rtype == TYPE_AAAA && n == 16) {
            out.push(to_vec(&r.rdata));
        }
        i = i + 1;
    }
}

fn copy_addrs(a: &Vec<Vec<u8>>) -> (r: Vec<Vec<u8>>)
    ensures
        r@.len() == a@.len(),
        forall|i: int| 0 <= i < a@.len() ==> (#[trigger] r@[i])@ == a@[i]@,
{
    let mut out: Vec<Vec<u8>> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] out@[j])@ == a@[j]@,
        decreases a@.len() - i,
    {
        out.push(to_vec(&a[i]));
        i = i + 1;
    }
    out
}

/// The deepest zone at or above `cur` whose servers the cache knows, and
/// their addresses; the root and `roots` if none.
fn closest(roots: &Vec<Vec<u8>>, cache: &Shared, cur: &[u8], now: u64) -> (r: (Vec<u8>, Vec<Vec<u8>>))
    requires
        addrs_ok(roots@),
    ensures
        addrs_ok(r.1@),
{
    let mut off: usize = 0;
    while off < cur.len()
        invariant
            addrs_ok(roots@),
        decreases cur@.len() - off,
    {
        if cur[off] == 0 {
            break;
        }
        let z = slice_subrange(cur, off, cur.len());
        match cache.lookup(z, DELEG, now) {
            Some(Hit { data: Data::Deleg(a), left: _ }) => {
                return (to_vec(z), a);
            },
            _ => {},
        }
        let c = cur[off] as usize;
        if c + 1 >= cur.len() - off {
            break;
        }
        off = off + 1 + c;
    }
    let mut root: Vec<u8> = Vec::new();
    root.push(0);
    let a = copy_addrs(roots);
    proof {
        assert forall|i: int| 0 <= i < a@.len() implies (#[trigger] a@[i])@.len() == 4 || a@[i]@.len() == 16 by {
            assert(a@[i]@ == roots@[i]@);
        }
    }
    (root, a)
}

/// Walks down from the closest known zone toward `cur` until a server
/// answers for it. Every query costs one unit of `budget`.
pub fn iterate(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    cur: &[u8],
    qtype: u16,
    budget: &mut u32,
    depth: u32,
) -> (s: Step)
    requires
        addrs_ok(roots@),
        qtype != DELEG,
    ensures
        step_ok(s, cur@, qtype),
        *final(budget) <= *old(budget),
    decreases depth, 1nat,
{
    let now = net.now();
    let (mut zone, mut servers) = closest(roots, cache, cur, now);
    let mut si: usize = 0;
    while *budget > 0
        invariant
            addrs_ok(roots@),
            addrs_ok(servers@),
            qtype != DELEG,
            *budget <= *old(budget),
        decreases *budget,
    {
        *budget = *budget - 1;
        let ghost b0 = *budget;
        if si >= servers.len() {
            return Step::Fail;
        }
        let id = (net.random() % 65536) as u16;
        let sent = mix_case(cur, net.random());
        let q = match build_query(id, &sent, qtype) {
            Some(q) => q,
            None => {
                return Step::Fail;
            },
        };
        let m = match net.exchange(&servers[si], &q) {
            Some(b) => match parse(&b) {
                Some(m) => m,
                None => {
                    si = si + 1;
                    continue ;
                },
            },
            None => {
                si = si + 1;
                continue ;
            },
        };
        if !response_matches(&m, id, &sent, qtype) {
            si = si + 1;
            continue ;
        }
        let o = classify(&m, &sent, qtype, &zone);
        proof {
            lemma_eq_ci_sym(sent@, cur@);
        }
        match o {
            Outcome::Answer(rs) => {
                let c = clamp_ttls(&rs, MAX_TTL);
                proof {
                    lemma_chain_ttl(sent@, qtype, rrs(rs@), rrs(c@));
                }
                return done_positive(cache, cur, Ghost(sent@), qtype, now, c);
            },
            Outcome::Cname(rs, t) => {
                let c = clamp_ttls(&rs, MAX_TTL);
                proof {
                    lemma_chain_ttl(sent@, qtype, rrs(rs@), rrs(c@));
                    lemma_chain_ci(sent@, cur@, qtype, rrs(c@));
                    lemma_eq_ci_sym(chain_end(sent@, qtype, rrs(c@)), chain_end(cur@, qtype, rrs(c@)));
                }
                return Step::Cname(c, t);
            },
            Outcome::NxDomain(rs, soa) => {
                return done_negative(cache, cur, Ghost(sent@), qtype, now, RCODE_NXDOMAIN, &rs, &soa);
            },
            Outcome::NoData(rs, soa) => {
                return done_negative(cache, cur, Ghost(sent@), qtype, now, RCODE_NOERROR, &rs, &soa);
            },
            Outcome::Referral(z, ns, glue) => {
                let addrs = ns_addrs(roots, net, cache, &ns, &glue, budget, depth);
                if addrs.len() == 0 {
                    si = si + 1;
                    continue ;
                }
                let ttl = min_ttl(&glue);
                cache.insert(&z, DELEG, now, ttl, Data::Deleg(copy_addrs(&addrs)));
                zone = z;
                servers = addrs;
                si = 0;
            },
            Outcome::Lame => {
                si = si + 1;
            },
        }
    }
    Step::Fail
}

/// The addresses of a referral's name servers: the glue, or else (if
/// `depth` allows) those of the first `MAX_NS_LOOKUPS` names, resolved.
fn ns_addrs(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    ns: &Vec<Vec<u8>>,
    glue: &Vec<Rr>,
    budget: &mut u32,
    depth: u32,
) -> (addrs: Vec<Vec<u8>>)
    requires
        addrs_ok(roots@),
    ensures
        addrs@.len() > 0 ==> addrs_ok(addrs@),
        *final(budget) <= *old(budget),
    decreases depth, 0nat,
{
    let mut addrs: Vec<Vec<u8>> = Vec::new();
    addresses(glue, &mut addrs);
    if addrs.len() == 0 && depth > 0 {
        let mut j: usize = 0;
        while j < ns.len() && j < MAX_NS_LOOKUPS
            invariant
                addrs_ok(roots@),
                forall|i: int| 0 <= i < addrs@.len() ==> (#[trigger] addrs@[i])@.len() == 4 || addrs@[i]@.len()
                    == 16,
                *budget <= *old(budget),
                depth > 0,
            decreases ns@.len() - j,
        {
            let a = resolve(roots, net, cache, &ns[j], TYPE_A, budget, depth - 1);
            addresses(&a.answers, &mut addrs);
            if addrs.len() > 0 {
                break;
            }
            j = j + 1;
        }
    }
    addrs
}

fn done_positive(cache: &Shared, cur: &[u8], sent: Ghost<Seq<u8>>, qtype: u16, now: u64, rs: Vec<Rr>) -> (s: Step)
    requires
        positive(sent@, qtype, rrs(rs@)),
        eq_ci(sent@, cur@),
        ttls_at_most(rrs(rs@), MAX_TTL),
        qtype != DELEG,
    ensures
        step_ok(s, cur@, qtype),
{
    proof {
        lemma_chain_ci(sent@, cur@, qtype, rrs(rs@));
    }
    let keep = copy_rrs(&rs);
    cache.insert(cur, qtype, now, min_ttl(&rs), Data::Pos(keep));
    let soa: Vec<Rr> = Vec::new();
    proof {
        assert(rrs(soa@).len() == 0);
    }
    Step::Done(RCODE_NOERROR, rs, soa)
}

fn done_negative(
    cache: &Shared,
    cur: &[u8],
    sent: Ghost<Seq<u8>>,
    qtype: u16,
    now: u64,
    code: u16,
    rs: &Vec<Rr>,
    soa: &Vec<Rr>,
) -> (s: Step)
    requires
        links_only(sent@, qtype, rrs(rs@)),
        forall|i: int| 0 <= i < soa@.len() ==> (#[trigger] rrs(soa@)[i]).rtype == TYPE_SOA,
        eq_ci(sent@, cur@),
        qtype != DELEG,
        code == RCODE_NOERROR || code == RCODE_NXDOMAIN,
    ensures
        step_ok(s, cur@, qtype),
{
    let c = clamp_ttls(rs, MAX_TTL);
    let s = clamp_ttls(soa, MAX_TTL);
    proof {
        lemma_chain_ttl(sent@, qtype, rrs(rs@), rrs(c@));
        lemma_chain_ci(sent@, cur@, qtype, rrs(c@));
        assert forall|i: int| 0 <= i < rrs(s@).len() implies (#[trigger] rrs(s@)[i]).rtype == TYPE_SOA by {
            assert(rrs(soa@)[i].rtype == TYPE_SOA);
        }
    }
    let ttl = negative_ttl(&s);
    cache.insert(cur, qtype, now, ttl, Data::Neg(code, copy_rrs(&c), copy_rrs(&s)));
    Step::Done(code, c, s)
}

/// What the resolver has for `cur` after the cache or a walk: `code` with
/// records from `cur` and the SOA, or (`more`) links to follow from there.
pub open spec fn got_ok(code: u16, rs: Seq<RrS>, soa: Seq<RrS>, more: Option<Vec<u8>>, cur: Seq<u8>, qtype: u16) -> bool {
    &&& code == RCODE_NOERROR || code == RCODE_NXDOMAIN
    &&& chain(cur, qtype, rs)
    &&& code != RCODE_NOERROR ==> links_only(cur, qtype, rs)
    &&& soa_only(soa)
    &&& ttls_at_most(rs, MAX_TTL)
    &&& ttls_at_most(soa, MAX_TTL)
    &&& more matches Some(t) ==> {
        &&& code == RCODE_NOERROR
        &&& links_only(cur, qtype, rs)
        &&& eq_ci(chain_end(cur, qtype, rs), t@)
        &&& soa.len() == 0
    }
}

/// Resolves `qname`/`qtype`: from the cache, or by walking the zones,
/// following CNAMEs. At most `budget` queries are sent in all.
pub fn resolve(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    qname: &[u8],
    qtype: u16,
    budget: &mut u32,
    depth: u32,
) -> (a: Answer)
    requires
        addrs_ok(roots@),
        qtype != DELEG,
    ensures
        answer_ok(a, qname@, qtype),
        *final(budget) <= *old(budget),
    decreases depth, 2nat,
{
    let mut cur: Vec<u8> = to_vec(qname);
    let mut acc: Vec<Rr> = Vec::new();
    let mut links: usize = 0;
    proof {
        assert(rrs(acc@) =~= Seq::<RrS>::empty());
        lemma_eq_ci_refl(qname@);
    }
    loop
        invariant
            addrs_ok(roots@),
            qtype != DELEG,
            links_only(qname@, qtype, rrs(acc@)),
            eq_ci(chain_end(qname@, qtype, rrs(acc@)), cur@),
            links == acc@.len(),
            links <= MAX_CNAME,
            ttls_at_most(rrs(acc@), MAX_TTL),
            *budget <= *old(budget),
        decreases MAX_CNAME - links,
    {
        let now = net.now();
        // (code, records from cur, soa), or links to follow.
        let (code, rs, soa, more) = match cache.lookup(&cur, qtype, now) {
            Some(Hit { data: Data::Pos(rs), left }) => {
                let soa: Vec<Rr> = Vec::new();
                proof {
                    assert(rrs(soa@).len() == 0);
                    assert forall|i: int| 0 <= i < rrs(rs@).len() implies (#[trigger] rrs(rs@)[i]).ttl <= MAX_TTL by {
                        assert(rrs(rs@)[i].ttl <= left);
                    }
                    assert(got_ok(RCODE_NOERROR, rrs(rs@), rrs(soa@), None, cur@, qtype));
                }
                (RCODE_NOERROR, rs, soa, None)
            },
            Some(Hit { data: Data::Neg(code, rs, soa), left }) => {
                proof {
                    assert forall|i: int| 0 <= i < rrs(rs@).len() implies (#[trigger] rrs(rs@)[i]).ttl <= MAX_TTL by {
                        assert(rrs(rs@)[i].ttl <= left);
                    }
                    assert forall|i: int| 0 <= i < rrs(soa@).len() implies (#[trigger] rrs(soa@)[i]).ttl <= MAX_TTL by {
                        assert(rrs(soa@)[i].ttl <= left);
                    }
                    assert(got_ok(code, rrs(rs@), rrs(soa@), None, cur@, qtype));
                }
                (code, rs, soa, None)
            },
            _ => match iterate(roots, net, cache, &cur, qtype, budget, depth) {
                Step::Done(code, rs, soa) => {
                    proof {
                        assert(got_ok(code, rrs(rs@), rrs(soa@), None, cur@, qtype));
                    }
                    (code, rs, soa, None)
                },
                Step::Cname(rs, t) => {
                    let soa: Vec<Rr> = Vec::new();
                    proof {
                        assert(rrs(soa@).len() == 0);
                        assert(got_ok(RCODE_NOERROR, rrs(rs@), rrs(soa@), Some(t), cur@, qtype));
                    }
                    (RCODE_NOERROR, rs, soa, Some(t))
                },
                Step::Fail => {
                    return servfail();
                },
            },
        };
        assert(got_ok(code, rrs(rs@), rrs(soa@), more, cur@, qtype));
        let ghost a = rrs(acc@);
        let ghost end = chain_end(qname@, qtype, a);
        proof {
            lemma_eq_ci_sym(end, cur@);
            lemma_chain_ci(cur@, end, qtype, rrs(rs@));
            lemma_chain_append(qname@, qtype, a, rrs(rs@));
        }
        let n = count_links(&cur, qtype, &rs);
        if n > MAX_CNAME as usize - links {
            return servfail();
        }
        extend_rrs(&mut acc, &rs);
        proof {
            assert forall|i: int| 0 <= i < rrs(acc@).len() implies (#[trigger] rrs(acc@)[i]).ttl <= MAX_TTL by {
                if i < a.len() {
                    assert(rrs(acc@)[i] == a[i]);
                } else {
                    assert(rrs(acc@)[i] == rrs(rs@)[i - a.len()]);
                }
            }
        }
        match more {
            None => {
                return Answer { rcode: code, answers: acc, authority: soa };
            },
            Some(t) => {
                proof {
                    // The links lead from the end of acc's chain to t.
                    lemma_eq_ci_sym(chain_end(end, qtype, rrs(rs@)), chain_end(cur@, qtype, rrs(rs@)));
                    lemma_eq_ci_trans(chain_end(end, qtype, rrs(rs@)), chain_end(cur@, qtype, rrs(rs@)), t@);
                }
                links = links + n;
                cur = t;
            },
        }
    }
}

} // verus!
