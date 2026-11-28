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
use crate::check::*;
use crate::classify::*;
use crate::dspec::*;
use crate::name::*;
use crate::reply::build_query;
use crate::rr::*;
use crate::spec::*;
use crate::trust::validating_x;
use verilith_dns::message::Section;
#[cfg(verus_only)]
use verilith_dns::message::section_of;
use verilith_dns::parse::parse;
use verilith_dns::Message;
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
    /// Wall-clock time, seconds since 1970 modulo 2^32 (RRSIG validity
    /// periods use serial arithmetic, RFC 4034 §3.1.5).
    fn wall(&self) -> u32 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as u32)
            .unwrap_or(0)
    }
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

    #[verifier::external_body]
    pub fn wall(&self) -> (r: u32) {
        self.t.wall()
    }
}

/// The cache, shared by every thread: `Cache`s, each behind a reader-writer
/// lock (vstd's, verified). Lookups take a shard's read lock, so they run
/// in parallel; inserts take its write lock.
pub struct Shared {
    pub(crate) shards: Vec<vstd::rwlock::RwLock<Cache, AnyCache>>,
}

/// The lock invariant: none beyond `Cache`'s own (a type invariant).
pub struct AnyCache;

impl vstd::rwlock::RwLockPredicate<Cache> for AnyCache {
    open spec fn inv(self, c: Cache) -> bool {
        true
    }
}

/// The shard of `n` shards a name's entries live in: any function of the
/// lowercased name would do.
fn shard_of(n: usize, name: &[u8]) -> (i: usize)
    requires
        n > 0,
    ensures
        i < n,
{
    let l = lowered(name);
    (hash(&l, 0) % (n as u64)) as usize
}

impl Shared {
    /// `shards` caches of `sets` sets each.
    pub fn new(shards: usize, sets: usize) -> (s: Shared)
        requires
            0 < sets <= 0x1000_0000,
    {
        let mut v: Vec<vstd::rwlock::RwLock<Cache, AnyCache>> = Vec::new();
        let n = if shards == 0 { 1 } else { shards };
        let mut i: usize = 0;
        while i < n
            invariant
                0 < sets <= 0x1000_0000,
            decreases n - i,
        {
            v.push(vstd::rwlock::RwLock::new(Cache::new(sets), Ghost(AnyCache)));
            i = i + 1;
        }
        Shared { shards: v }
    }

    pub fn lookup(&self, name: &[u8], qtype: u16, now: u64) -> (r: Option<Hit>)
        ensures
            r matches Some(h) ==> hit_ok(h, name@, qtype),
    {
        let n = self.shards.len();
        if n == 0 {
            return None;
        }
        let lock = &self.shards[shard_of(n, name)];
        let h = lock.acquire_read();
        let r = h.borrow().lookup(name, qtype, now);
        h.release_read();
        r
    }

    pub fn insert(&self, name: &[u8], qtype: u16, now: u64, ttl: u32, data: Data)
        requires
            data_ok(data, name@, qtype),
    {
        let n = self.shards.len();
        if n == 0 {
            return;
        }
        let lock = &self.shards[shard_of(n, name)];
        let (mut c, w) = lock.acquire_write();
        c.insert(name, qtype, now, ttl, data);
        w.release_write(c);
    }
}

/// The most name server names whose addresses one referral may make the
/// resolver look up (NXNSAttack: BIND, Unbound and Knot cap this too).
pub const MAX_NS_LOOKUPS: usize = 2;

/// How deep lookups of name server addresses may nest.
pub const NS_DEPTH: u32 = 3;

/// The resolver's answer to a question, with its security status
/// (`dspec::UNCHECKED`, `SECURE`, `INSECURE`) and the evidence for it.
pub struct Answer {
    pub rcode: u16,
    pub answers: Vec<Rr>,
    pub authority: Vec<Rr>,
    pub sec: u8,
    pub ev: Ghost<Ev>,
}

/// What the answer to `qname`/`qtype` may be: a chain for the question,
/// ending in records of the type (NOERROR), or in nothing (NOERROR with no
/// data, NXDOMAIN); or SERVFAIL with no records. Its status is backed by
/// the evidence (`sec_ok`); and when validation was asked for (`valid`)
/// and anchors are configured, it is never left unchecked.
pub open spec fn answer_ok(a: Answer, qname: Seq<u8>, qtype: u16, valid: bool) -> bool {
    &&& a.rcode == RCODE_NOERROR || a.rcode == RCODE_NXDOMAIN || a.rcode == RCODE_SERVFAIL
    &&& chain(qname, qtype, rrs(a.answers@))
    &&& chain_links(qname, qtype, rrs(a.answers@)) <= MAX_CNAME
    &&& a.rcode != RCODE_NOERROR ==> links_only(qname, qtype, rrs(a.answers@))
    &&& a.rcode == RCODE_SERVFAIL ==> a.answers@.len() == 0 && a.authority@.len() == 0 && a.sec == UNCHECKED
    &&& soa_only(rrs(a.authority@))
    &&& ttls_at_most(rrs(a.answers@), MAX_TTL)
    &&& ttls_at_most(rrs(a.authority@), MAX_TTL)
    &&& sec_ok(a.sec, a.ev@, qname, qtype, a.rcode, rrs(a.answers@), rrs(a.authority@))
    &&& (valid && validating() && a.rcode != RCODE_SERVFAIL) ==> a.sec != UNCHECKED
}

pub fn servfail() -> (a: Answer)
    ensures
        a.rcode == RCODE_SERVFAIL,
        a.answers@.len() == 0,
        a.authority@.len() == 0,
        a.sec == UNCHECKED,
{
    Answer { rcode: RCODE_SERVFAIL, answers: Vec::new(), authority: Vec::new(), sec: UNCHECKED, ev: Ghost(ev_empty()) }
}

/// The DNSSEC records of a response, for validation: its RRSIGs and its
/// NSEC and NSEC3 records (answer and authority sections, in the
/// bailiwick), and the zone the server was asked as.
pub struct Raw {
    pub sigs: Vec<Rr>,
    pub ns: Vec<Rr>,
    pub zone: Vec<u8>,
}

fn gather_section(m: &Message, s: Section, zone: &[u8], raw: &mut Raw)
    ensures
        final(raw).zone@ == old(raw).zone@,
{
    let n = m.record_count(s);
    let mut i: usize = 0;
    while i < n
        invariant
            n == section_of(m@, s).len(),
            i <= n,
            raw.zone@ == old(raw).zone@,
        decreases n - i,
    {
        let r = take_record(m, s, i);
        if r.rclass == CLASS_IN && is_sub_exec(&r.name, zone) {
            if r.rtype == TYPE_RRSIG {
                raw.sigs.push(r);
            } else if r.rtype == TYPE_NSEC || r.rtype == TYPE_NSEC3 {
                raw.ns.push(r);
            }
        }
        i = i + 1;
    }
}

fn gather(m: &Message, zone: &[u8]) -> (r: Raw)
    ensures
        r.zone@ == zone@,
{
    let mut raw = Raw { sigs: Vec::new(), ns: Vec::new(), zone: to_vec(zone) };
    gather_section(m, Section::Answer, zone, &mut raw);
    gather_section(m, Section::Authority, zone, &mut raw);
    raw
}

/// What one walk down the zones for one name ends with.
pub enum Step {
    /// NOERROR (an answer, or no data) or NXDOMAIN: the records, from the
    /// name walked for, and the SOA; and the response's DNSSEC records.
    Done(u16, Vec<Rr>, Vec<Rr>, Raw),
    /// CNAME links, to be followed from the target.
    Cname(Vec<Rr>, Vec<u8>, Raw),
    Fail,
}

pub open spec fn step_ok(s: Step, cur: Seq<u8>, qtype: u16) -> bool {
    match s {
        Step::Done(code, rs, soa, _) => {
            &&& code == RCODE_NOERROR || code == RCODE_NXDOMAIN
            &&& chain(cur, qtype, rrs(rs@))
            &&& code == RCODE_NXDOMAIN ==> links_only(cur, qtype, rrs(rs@))
            &&& soa_only(rrs(soa@))
            &&& ttls_at_most(rrs(rs@), MAX_TTL)
            &&& ttls_at_most(rrs(soa@), MAX_TTL)
        },
        Step::Cname(rs, t, _) => {
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
/// their addresses; the root and `roots` if none. With `above`, only zones
/// strictly above `cur` (a DS RRset is the parent's).
fn closest(roots: &Vec<Vec<u8>>, cache: &Shared, cur: &[u8], now: u64, above: bool) -> (r: (Vec<u8>, Vec<Vec<u8>>))
    requires
        addrs_ok(roots@),
    ensures
        addrs_ok(r.1@),
{
    let mut off: usize = 0;
    if above && cur.len() > 0 {
        let c = cur[0] as usize;
        if c + 1 >= cur.len() {
            off = cur.len();
        } else {
            off = 1 + c;
        }
    }
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
/// answers for it. Every query costs one unit of `budget`. Nothing it
/// returns is cached here: the caller validates first.
pub fn iterate(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    cur: &[u8],
    qtype: u16,
    budget: &mut u32,
    depth: u32,
    vd: u32,
) -> (s: Step)
    requires
        addrs_ok(roots@),
        qtype != DELEG,
    ensures
        step_ok(s, cur@, qtype),
        *final(budget) <= *old(budget),
    decreases vd, depth + 1, 2nat,
{
    let now = net.now();
    let ds = qtype == TYPE_DS;
    let (mut zone, mut servers) = closest(roots, cache, cur, now, ds);
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
                    lemma_chain_ci(sent@, cur@, qtype, rrs(c@));
                }
                let soa: Vec<Rr> = Vec::new();
                proof {
                    assert(rrs(soa@).len() == 0);
                }
                return Step::Done(RCODE_NOERROR, c, soa, gather(&m, &zone));
            },
            Outcome::Cname(rs, t) => {
                let c = clamp_ttls(&rs, MAX_TTL);
                proof {
                    lemma_chain_ttl(sent@, qtype, rrs(rs@), rrs(c@));
                    lemma_chain_ci(sent@, cur@, qtype, rrs(c@));
                    lemma_eq_ci_sym(chain_end(sent@, qtype, rrs(c@)), chain_end(cur@, qtype, rrs(c@)));
                }
                return Step::Cname(c, t, gather(&m, &zone));
            },
            Outcome::NxDomain(rs, soa) => {
                return done_negative(cur, Ghost(sent@), qtype, RCODE_NXDOMAIN, &rs, &soa, gather(&m, &zone));
            },
            Outcome::NoData(rs, soa) => {
                return done_negative(cur, Ghost(sent@), qtype, RCODE_NOERROR, &rs, &soa, gather(&m, &zone));
            },
            Outcome::Referral(z, ns, glue) => {
                // A DS query goes to the parent: a referral to the zone
                // itself is no answer.
                if ds && eq_ci_exec(&z, cur) {
                    si = si + 1;
                    continue ;
                }
                let addrs = ns_addrs(roots, net, cache, &ns, &glue, budget, depth, vd);
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
/// The lookups are not validated (an address is only where to ask; what
/// comes back from there is).
fn ns_addrs(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    ns: &Vec<Vec<u8>>,
    glue: &Vec<Rr>,
    budget: &mut u32,
    depth: u32,
    vd: u32,
) -> (addrs: Vec<Vec<u8>>)
    requires
        addrs_ok(roots@),
    ensures
        addrs@.len() > 0 ==> addrs_ok(addrs@),
        *final(budget) <= *old(budget),
    decreases vd, depth + 1, 1nat,
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
            let a = resolve(roots, net, cache, &ns[j], TYPE_A, budget, depth - 1, vd, false);
            addresses(&a.answers, &mut addrs);
            if addrs.len() > 0 {
                break;
            }
            j = j + 1;
        }
    }
    addrs
}

fn done_negative(
    cur: &[u8],
    sent: Ghost<Seq<u8>>,
    qtype: u16,
    code: u16,
    rs: &Vec<Rr>,
    soa: &Vec<Rr>,
    raw: Raw,
) -> (s: Step)
    requires
        links_only(sent@, qtype, rrs(rs@)),
        forall|i: int| 0 <= i < soa@.len() ==> (#[trigger] rrs(soa@)[i]).rtype == TYPE_SOA,
        eq_ci(sent@, cur@),
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
    Step::Done(code, c, s, raw)
}

/// Records validated (or proven insecure) by the evidence, unless
/// unchecked.
pub open spec fn recs_sec(rs: Seq<RrS>, sec: u8, e: Ev) -> bool {
    sec == UNCHECKED || {
        &&& sec == SECURE || sec == INSECURE
        &&& validating()
        &&& ev_ok(e)
        &&& recs_ok(rs, sec, e)
    }
}

proof fn lemma_recs_concat(a: Seq<RrS>, b: Seq<RrS>, sec: u8, e: Ev)
    requires
        recs_ok(a, sec, e),
        recs_ok(b, sec, e),
    ensures
        recs_ok(a + b, sec, e),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies rec_secure(#[trigger] (a + b)[i], e) || (sec == INSECURE
        && rec_insecure((a + b)[i], e)) by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

/// The status of two parts together: unchecked if either is, insecure if
/// either is, else secure.
pub open spec fn join_sec(a: u8, b: u8) -> u8 {
    if a == UNCHECKED || b == UNCHECKED {
        UNCHECKED
    } else if a == INSECURE || b == INSECURE {
        INSECURE
    } else {
        SECURE
    }
}

fn join_sec_x(a: u8, b: u8) -> (r: u8)
    ensures
        r == join_sec(a, b),
{
    if a == UNCHECKED || b == UNCHECKED {
        UNCHECKED
    } else if a == INSECURE || b == INSECURE {
        INSECURE
    } else {
        SECURE
    }
}

/// Moving a step's status into the joined evidence.
proof fn lemma_sec_sub(s: u8, e: Ev, s2: u8, e2: Ev, cur: Seq<u8>, qtype: u16, code: u16, rs: Seq<RrS>, soa: Seq<RrS>)
    requires
        sec_ok(s, e, cur, qtype, code, rs, soa),
        s != UNCHECKED,
        s2 == SECURE || s2 == INSECURE,
        s == INSECURE ==> s2 == INSECURE,
        ev_sub(e, e2),
        ev_ok(e2),
    ensures
        sec_ok(s2, e2, cur, qtype, code, rs, soa),
{
    lemma_recs_sub(rs, s, s2, e, e2);
    lemma_recs_sub(soa, s, s2, e, e2);
    let end = chain_end(cur, qtype, rs);
    if code == RCODE_NXDOMAIN {
        if nx_proven(end, e) {
            assert(nx_proven(end, e2));
        } else {
            assert(name_insecure(end, e2));
        }
    }
    if code == RCODE_NOERROR && links_only(cur, qtype, rs) {
        if nodata_proven(end, qtype, e) {
            assert(nodata_proven(end, qtype, e2));
        } else {
            assert(name_insecure(end, e2));
        }
    }
}

/// A step's status, carried over from the name it was asked for to the
/// whole chain before it.
proof fn lemma_sec_append(sec: u8, e: Ev, qname: Seq<u8>, qtype: u16, code: u16, a: Seq<RrS>, rs: Seq<RrS>, soa: Seq<RrS>)
    requires
        links_only(qname, qtype, a),
        chain(chain_end(qname, qtype, a), qtype, rs),
        sec != UNCHECKED ==> recs_ok(a, sec, e),
        sec_ok(sec, e, chain_end(qname, qtype, a), qtype, code, rs, soa),
    ensures
        sec_ok(sec, e, qname, qtype, code, a + rs, soa),
{
    lemma_chain_append(qname, qtype, a, rs);
    if sec != UNCHECKED {
        lemma_recs_concat(a, rs, sec, e);
    }
}

proof fn lemma_unchecked(qname: Seq<u8>, qtype: u16)
    ensures
        forall|e: Ev, code: u16, rs: Seq<RrS>, soa: Seq<RrS>| #[trigger] sec_ok(UNCHECKED, e, qname, qtype, code, rs, soa),
{
}

proof fn lemma_start(v: bool, e: Ev)
    requires
        v ==> validating(),
        e == ev_empty(),
    ensures
        recs_sec(Seq::empty(), if v { SECURE } else { UNCHECKED }, e),
{
    assert(ev_ok(ev_empty()));
}

/// The status of `a` (the chain so far, to `cur`) and of one more step
/// (`rs`, `soa`), together.
proof fn lemma_combine(
    qname: Seq<u8>,
    qtype: u16,
    a: Seq<RrS>,
    cur: Seq<u8>,
    asec: u8,
    aev: Ev,
    code: u16,
    rs: Seq<RrS>,
    soa: Seq<RrS>,
    last: bool,
    sec: u8,
    e: Ev,
)
    requires
        links_only(qname, qtype, a),
        eq_ci(chain_end(qname, qtype, a), cur),
        chain(cur, qtype, rs),
        recs_sec(a, asec, aev),
        last ==> sec_ok(sec, e, cur, qtype, code, rs, soa),
        !last ==> recs_sec(rs, sec, e),
    ensures
        recs_sec(a + rs, join_sec(asec, sec), ev_join(aev, e)),
        last ==> sec_ok(join_sec(asec, sec), ev_join(aev, e), qname, qtype, code, a + rs, soa),
{
    let end = chain_end(qname, qtype, a);
    let nsec = join_sec(asec, sec);
    let nev = ev_join(aev, e);
    lemma_eq_ci_sym(end, cur);
    lemma_chain_ci(cur, end, qtype, rs);
    lemma_chain_append(qname, qtype, a, rs);
    if nsec != UNCHECKED {
        lemma_join(aev, e);
        lemma_recs_sub(a, asec, nsec, aev, nev);
        if last {
            lemma_sec_sub(sec, e, nsec, nev, cur, qtype, code, rs, soa);
            lemma_sec_ci(nsec, nev, cur, end, qtype, code, rs, soa);
            lemma_sec_append(nsec, nev, qname, qtype, code, a, rs, soa);
        } else {
            lemma_recs_sub(rs, sec, nsec, e, nev);
        }
        lemma_recs_concat(a, rs, nsec, nev);
    }
}

/// What the resolver has for `cur` after the cache or a walk: `code` with
/// records from `cur` and the SOA, or (`more`) links to follow from there;
/// with their status.
pub open spec fn got_ok(
    code: u16,
    rs: Seq<RrS>,
    soa: Seq<RrS>,
    more: Option<Vec<u8>>,
    cur: Seq<u8>,
    qtype: u16,
    sec: u8,
    e: Ev,
    v: bool,
) -> bool {
    &&& code == RCODE_NOERROR || code == RCODE_NXDOMAIN
    &&& chain(cur, qtype, rs)
    &&& code != RCODE_NOERROR ==> links_only(cur, qtype, rs)
    &&& soa_only(soa)
    &&& ttls_at_most(rs, MAX_TTL)
    &&& ttls_at_most(soa, MAX_TTL)
    &&& v ==> sec != UNCHECKED
    &&& more matches Some(t) ==> {
        &&& code == RCODE_NOERROR
        &&& links_only(cur, qtype, rs)
        &&& eq_ci(chain_end(cur, qtype, rs), t@)
        &&& soa.len() == 0
        &&& rs.len() > 0
        &&& recs_sec(rs, sec, e)
    }
    &&& more is None ==> sec_ok(sec, e, cur, qtype, code, rs, soa)
}

/// One step of `resolve` for `cur`: from the cache, or a walk, validated
/// if `v`, and then cached.
fn lookup_step(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    cur: &[u8],
    qtype: u16,
    budget: &mut u32,
    depth: u32,
    vd: u32,
    v: bool,
) -> (r: Option<(u16, Vec<Rr>, Vec<Rr>, Option<Vec<u8>>, u8, Ghost<Ev>)>)
    requires
        addrs_ok(roots@),
        qtype != DELEG,
        qtype != KEYS,
        v ==> validating(),
    ensures
        r matches Some((code, rs, soa, more, sec, e)) ==> got_ok(code, rrs(rs@), rrs(soa@), more, cur@, qtype, sec, e@, v),
        *final(budget) <= *old(budget),
    decreases vd, depth + 1, 3nat,
{
    let now = net.now();
    match cache.lookup(cur, qtype, now) {
        Some(Hit { data: Data::Pos(rs, sec, ev), left }) => {
            if !(v && sec == UNCHECKED) {
                let soa: Vec<Rr> = Vec::new();
                proof {
                    assert(rrs(soa@) =~= Seq::<RrS>::empty());
                    assert forall|i: int| 0 <= i < rrs(rs@).len() implies (#[trigger] rrs(rs@)[i]).ttl <= MAX_TTL by {
                        assert(rrs(rs@)[i].ttl <= left);
                    }
                }
                return Some((RCODE_NOERROR, rs, soa, None, sec, ev));
            }
        },
        Some(Hit { data: Data::Neg(code, rs, soa, sec, ev), left }) => {
            if !(v && sec == UNCHECKED) {
                proof {
                    assert forall|i: int| 0 <= i < rrs(rs@).len() implies (#[trigger] rrs(rs@)[i]).ttl <= MAX_TTL by {
                        assert(rrs(rs@)[i].ttl <= left);
                    }
                    assert forall|i: int| 0 <= i < rrs(soa@).len() implies (#[trigger] rrs(soa@)[i]).ttl <= MAX_TTL by {
                        assert(rrs(soa@)[i].ttl <= left);
                    }
                }
                return Some((code, rs, soa, None, sec, ev));
            }
        },
        _ => {},
    }
    match iterate(roots, net, cache, cur, qtype, budget, depth, vd) {
        Step::Done(code, rs, soa, raw) => {
            let (sec, e) = if v {
                match check_step(roots, net, cache, cur, qtype, code, &rs, &soa, &raw, true, budget, vd) {
                    Some(x) => x,
                    None => {
                        return None;
                    },
                }
            } else {
                (UNCHECKED, Ghost(ev_empty()))
            };
            let n = count_links(cur, qtype, &rs);
            if code == RCODE_NOERROR && n < rs.len() {
                cache.insert(cur, qtype, now, min_ttl(&rs), Data::Pos(copy_rrs(&rs), sec, e));
            } else if code == RCODE_NXDOMAIN || n == rs.len() {
                cache.insert(
                    cur,
                    qtype,
                    now,
                    negative_ttl(&soa),
                    Data::Neg(code, copy_rrs(&rs), copy_rrs(&soa), sec, e),
                );
            }
            Some((code, rs, soa, None, sec, e))
        },
        Step::Cname(rs, t, raw) => {
            let soa: Vec<Rr> = Vec::new();
            proof {
                assert(rrs(soa@) =~= Seq::<RrS>::empty());
            }
            let (sec, e) = if v {
                match check_step(roots, net, cache, cur, qtype, RCODE_NOERROR, &rs, &soa, &raw, false, budget, vd) {
                    Some(x) => x,
                    None => {
                        return None;
                    },
                }
            } else {
                (UNCHECKED, Ghost(ev_empty()))
            };
            Some((RCODE_NOERROR, rs, soa, Some(t), sec, e))
        },
        Step::Fail => None,
    }
}

/// Resolves `qname`/`qtype`: from the cache, or by walking the zones,
/// following CNAMEs. At most `budget` queries are sent in all. With
/// `valid` (and trust anchors configured), every record is validated, or
/// proven to be in an unsigned zone; bogus data is SERVFAIL.
pub fn resolve(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    qname: &[u8],
    qtype: u16,
    budget: &mut u32,
    depth: u32,
    vd: u32,
    valid: bool,
) -> (a: Answer)
    requires
        addrs_ok(roots@),
        qtype != DELEG,
        qtype != KEYS,
    ensures
        answer_ok(a, qname@, qtype, valid),
        *final(budget) <= *old(budget),
    decreases vd, depth + 1, 4nat,
{
    hide(sec_ok);
    hide(recs_sec);
    let v = valid && validating_x();
    let mut cur: Vec<u8> = to_vec(qname);
    let mut acc: Vec<Rr> = Vec::new();
    let mut links: usize = 0;
    let mut asec: u8 = if v { SECURE } else { UNCHECKED };
    let ghost mut aev = ev_empty();
    proof {
        assert(rrs(acc@) =~= Seq::<RrS>::empty());
        lemma_eq_ci_refl(qname@);
        lemma_start(v, aev);
    }
    loop
        invariant
            addrs_ok(roots@),
            qtype != DELEG,
            qtype != KEYS,
            v == (valid && validating()),
            links_only(qname@, qtype, rrs(acc@)),
            eq_ci(chain_end(qname@, qtype, rrs(acc@)), cur@),
            links == acc@.len(),
            links <= MAX_CNAME,
            ttls_at_most(rrs(acc@), MAX_TTL),
            recs_sec(rrs(acc@), asec, aev),
            v ==> asec != UNCHECKED,
            *budget <= *old(budget),
        decreases MAX_CNAME - links,
    {
        let (code, rs, soa, more, sec, e) = match lookup_step(roots, net, cache, &cur, qtype, budget, depth, vd, v) {
            Some(x) => x,
            None => {
                proof {
                    lemma_unchecked(qname@, qtype);
                }
                return servfail();
            },
        };
        let ghost a = rrs(acc@);
        let ghost end = chain_end(qname@, qtype, a);
        proof {
            lemma_eq_ci_sym(end, cur@);
            lemma_chain_ci(cur@, end, qtype, rrs(rs@));
            lemma_chain_append(qname@, qtype, a, rrs(rs@));
        }
        let n = count_links(&cur, qtype, &rs);
        if n > MAX_CNAME as usize - links {
            proof {
                lemma_unchecked(qname@, qtype);
            }
            return servfail();
        }
        // The status and evidence of acc and this step together.
        let nsec = join_sec_x(asec, sec);
        let ghost nev = ev_join(aev, e@);
        proof {
            lemma_combine(qname@, qtype, a, cur@, asec, aev, code, rrs(rs@), rrs(soa@), more is None, sec, e@);
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
                return Answer { rcode: code, answers: acc, authority: soa, sec: nsec, ev: Ghost(nev) };
            },
            Some(t) => {
                proof {
                    // The links lead from the end of acc's chain to t.
                    lemma_eq_ci_sym(chain_end(end, qtype, rrs(rs@)), chain_end(cur@, qtype, rrs(rs@)));
                    lemma_eq_ci_trans(chain_end(end, qtype, rrs(rs@)), chain_end(cur@, qtype, rrs(rs@)), t@);
                }
                links = links + n;
                cur = t;
                asec = nsec;
                proof {
                    aev = nev;
                }
            },
        }
    }
}

} // verus!
