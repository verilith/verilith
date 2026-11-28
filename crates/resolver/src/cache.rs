//! The cache: answers, negative answers (RFC 2308) and delegations, in a
//! fixed number of slots. Its type invariant is that every entry holds a
//! chain for its own question, so whatever it hands back is a well-formed
//! answer to the question asked, and never after its TTL.
use crate::dspec::*;
use crate::name::*;
use crate::rr::*;
use crate::spec::*;
#[cfg(verus_only)]
use crate::trust::{cut_ok, keys_ok, lemma_lower_ci};
use vstd::prelude::*;

verus! {

/// Ways per set: a question can be in one of this many slots.
pub const WAYS: usize = 4;

/// The pseudo-type under which delegations are kept, keyed by zone.
pub const DELEG: u16 = 0;

/// The pseudo-type under which what DNSSEC knows of a zone is kept: its
/// trusted keys, or that it is unsigned. (65535 is reserved, RFC 6895;
/// clients cannot ask for it.)
pub const KEYS: u16 = 65535;

pub enum Data {
    /// A positive answer: CNAME links, then records of the type; its
    /// DNSSEC status and the evidence for it.
    Pos(Vec<Rr>, u8, Ghost<Ev>),
    /// A negative answer: RCODE (NOERROR for no data, NXDOMAIN), the CNAME
    /// links before it, and the zone's SOA; status and evidence.
    Neg(u16, Vec<Rr>, Vec<Rr>, u8, Ghost<Ev>),
    /// The addresses (4 or 16 bytes) of a zone's name servers.
    Deleg(Vec<Vec<u8>>),
    /// A zone's trusted keys, and the chain of trust that makes them so.
    Keys(Vec<Rr>, Ghost<Seq<Link>>),
    /// A zone is at or below this proven unsigned cut.
    Cut(Vec<u8>, Ghost<Unsigned>),
}

pub open spec fn addrs_ok(a: Seq<Vec<u8>>) -> bool {
    &&& a.len() > 0
    &&& forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i])@.len() == 4 || a[i]@.len() == 16
}

pub open spec fn soa_only(rs: Seq<RrS>) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> (#[trigger] rs[i]).rtype == TYPE_SOA
}

/// What an entry for `name`/`qtype` may hold.
pub open spec fn data_ok(d: Data, name: Seq<u8>, qtype: u16) -> bool {
    match d {
        Data::Pos(rs, sec, ev) => {
            &&& qtype != DELEG && qtype != KEYS
            &&& positive(name, qtype, rrs(rs@))
            &&& sec_ok(sec, ev@, name, qtype, RCODE_NOERROR, rrs(rs@), Seq::empty())
        },
        Data::Neg(code, rs, soa, sec, ev) => {
            &&& qtype != DELEG && qtype != KEYS
            &&& code == RCODE_NOERROR || code == RCODE_NXDOMAIN
            &&& links_only(name, qtype, rrs(rs@))
            &&& soa_only(rrs(soa@))
            &&& sec_ok(sec, ev@, name, qtype, code, rrs(rs@), rrs(soa@))
        },
        Data::Deleg(a) => qtype == DELEG && addrs_ok(a@),
        Data::Keys(k, c) => qtype == KEYS && keys_ok(c@, name, rrs(k@)),
        Data::Cut(cut, u) => qtype == KEYS && cut_ok(u@, cut@, name),
    }
}

/// Every TTL in the data is at most `t`.
pub open spec fn data_ttls(d: Data, t: u32) -> bool {
    match d {
        Data::Pos(rs, _, _) => ttls_at_most(rrs(rs@), t),
        Data::Neg(_, rs, soa, _, _) => ttls_at_most(rrs(rs@), t) && ttls_at_most(rrs(soa@), t),
        _ => true,
    }
}

pub struct Entry {
    /// The name, lowercased.
    pub name: Vec<u8>,
    pub qtype: u16,
    pub expires: u64,
    pub data: Data,
}

pub open spec fn entry_ok(e: Entry) -> bool {
    &&& forall|i: int| 0 <= i < e.name@.len() ==> #[trigger] lower(e.name@[i]) == e.name@[i]
    &&& data_ok(e.data, e.name@, e.qtype)
}

/// What the cache hands back: the data with every TTL lowered to the time
/// left, which is at least 1 second and at most `MAX_TTL`.
pub struct Hit {
    pub data: Data,
    pub left: u32,
}

pub open spec fn hit_ok(h: Hit, name: Seq<u8>, qtype: u16) -> bool {
    &&& 1 <= h.left <= MAX_TTL
    &&& data_ok(h.data, name, qtype)
    &&& data_ttls(h.data, h.left)
}

pub struct Cache {
    slots: Vec<Option<Entry>>,
    sets: usize,
}

/// A hash of a key, to pick its set. Any function would be correct; this
/// one spreads names well.
pub fn hash(name: &[u8], qtype: u16) -> (h: u64) {
    let mut h: u64 = 0xcbf2_9ce4 + qtype as u64;
    let mut i: usize = 0;
    while i < name.len()
        invariant
            i <= name@.len(),
        decreases name@.len() - i,
    {
        h = (h % 0x0100_0000_0000_0000) * 131 + name[i] as u64;
        i = i + 1;
    }
    h ^ (h / 0x1_0000_0000)
}

/// `rs` with every TTL at most `t`.
pub fn clamp_ttls(rs: &Vec<Rr>, t: u32) -> (r: Vec<Rr>)
    ensures
        same_but_ttl(rrs(rs@), rrs(r@)),
        ttls_at_most(rrs(r@), t),
{
    let mut out: Vec<Rr> = Vec::with_capacity(rs.len());
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            i <= rs@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let (a, b) = (#[trigger] out@[j]@, rs@[j]@);
                a.name == b.name && a.rtype == b.rtype && a.rclass == b.rclass && a.rdata == b.rdata
                    && a.ttl <= t
            },
        decreases rs@.len() - i,
    {
        let r = &rs[i];
        let ttl = if r.ttl < t { r.ttl } else { t };
        out.push(r.with_ttl(ttl));
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < rrs(out@).len() implies (#[trigger] rrs(out@)[j]).ttl <= t by {
            assert(rrs(out@)[j] == out@[j]@);
        }
        assert forall|j: int| 0 <= j < rrs(rs@).len() implies (#[trigger] rrs(rs@)[j]).name == rrs(out@)[j].name
            && rrs(rs@)[j].rtype == rrs(out@)[j].rtype && rrs(rs@)[j].rclass == rrs(out@)[j].rclass
            && rrs(rs@)[j].rdata == rrs(out@)[j].rdata by {
            assert(rrs(out@)[j] == out@[j]@);
            assert(rrs(rs@)[j] == rs@[j]@);
        }
    }
    out
}

pub proof fn lemma_same_but_ttl_sym(a: Seq<RrS>, b: Seq<RrS>)
    requires
        same_but_ttl(a, b),
    ensures
        same_but_ttl(b, a),
{
}

/// A copy of a list of addresses.
fn copy_addrs(a: &Vec<Vec<u8>>) -> (out: Vec<Vec<u8>>)
    ensures
        out@.len() == a@.len(),
        forall|j: int| 0 <= j < a@.len() ==> (#[trigger] out@[j])@ == a@[j]@,
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

/// The data with TTLs at most `t`, still for the same question.
#[verifier::rlimit(30)]
pub fn clamp_data(d: &Data, name: Ghost<Seq<u8>>, qtype: u16, t: u32) -> (r: Data)
    requires
        data_ok(*d, name@, qtype),
    ensures
        data_ok(r, name@, qtype),
        data_ttls(r, t),
{
    match d {
        Data::Pos(rs, sec, ev) => {
            let c = clamp_ttls(rs, t);
            proof {
                lemma_chain_ttl(name@, qtype, rrs(rs@), rrs(c@));
                lemma_sec_ttl(*sec, ev@, name@, qtype, RCODE_NOERROR, rrs(rs@), rrs(c@), Seq::empty(), Seq::empty());
            }
            Data::Pos(c, *sec, Ghost(ev@))
        },
        Data::Neg(code, rs, soa, sec, ev) => {
            let c = clamp_ttls(rs, t);
            let s = clamp_ttls(soa, t);
            proof {
                lemma_chain_ttl(name@, qtype, rrs(rs@), rrs(c@));
                assert forall|i: int| 0 <= i < rrs(s@).len() implies (#[trigger] rrs(s@)[i]).rtype == TYPE_SOA by {
                    assert(rrs(soa@)[i].rtype == TYPE_SOA);
                }
                lemma_sec_ttl(*sec, ev@, name@, qtype, *code, rrs(rs@), rrs(c@), rrs(soa@), rrs(s@));
            }
            Data::Neg(*code, c, s, *sec, Ghost(ev@))
        },
        Data::Keys(k, ch) => {
            let c = clamp_ttls(k, t);
            proof {
                assert forall|i: int| 0 <= i < rrs(c@).len() implies has_key(ch@.last().keys, #[trigger] rrs(c@)[i].rdata) by {
                    assert(rrs(c@)[i].rdata == rrs(k@)[i].rdata);
                }
            }
            Data::Keys(c, Ghost(ch@))
        },
        Data::Cut(cut, u) => Data::Cut(to_vec(cut), Ghost(u@)),
        Data::Deleg(a) => {
            let out = copy_addrs(a);
            proof {
                assert forall|j: int| 0 <= j < out@.len() implies (#[trigger] out@[j])@.len() == 4
                    || out@[j]@.len() == 16 by {
                    assert(out@[j]@ == a@[j]@);
                }
            }
            Data::Deleg(out)
        },
    }
}

impl Cache {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.sets > 0
        &&& self.slots@.len() == self.sets * WAYS
        &&& forall|i: int| 0 <= i < self.slots@.len() ==> (#[trigger] self.slots@[i] matches Some(e)
            ==> entry_ok(e))
    }

    /// The number of entries the cache can hold, which bounds its memory.
    pub closed spec fn capacity(self) -> nat {
        self.slots@.len()
    }

    /// A cache of `sets` sets of `WAYS` entries.
    pub fn new(sets: usize) -> (c: Cache)
        requires
            0 < sets <= 0x1000_0000,
        ensures
            c.capacity() == sets * WAYS,
    {
        let n = sets * WAYS;
        let mut slots: Vec<Option<Entry>> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                slots@.len() == i,
                forall|j: int| 0 <= j < i ==> (#[trigger] slots@[j]) is None,
            decreases n - i,
        {
            slots.push(None);
            i = i + 1;
        }
        Cache { slots, sets }
    }

    fn set_of(&self, key: &[u8], qtype: u16) -> (s: usize)
        ensures
            s + WAYS <= self.slots@.len() <= usize::MAX,
    {
        proof {
            use_type_invariant(self);
        }
        let _ = self.slots.len();
        let h = hash(key, qtype);
        let x = (h % (self.sets as u64)) as usize;
        let sets = self.sets;
        proof {
            assert(x < sets);
            assert(x * WAYS + WAYS <= sets * WAYS) by (nonlinear_arith)
                requires
                    x < sets,
            ;
        }
        x * WAYS
    }

    /// What the cache holds for `name`/`qtype` at time `now` (seconds), if
    /// it has not expired.
    pub fn lookup(&self, name: &[u8], qtype: u16, now: u64) -> (r: Option<Hit>)
        ensures
            r matches Some(h) ==> hit_ok(h, name@, qtype),
    {
        proof {
            use_type_invariant(self);
        }
        let key = lowered(name);
        let base = self.set_of(&key, qtype);
        let mut w: usize = 0;
        while w < WAYS
            invariant
                base + WAYS <= self.slots@.len() <= usize::MAX,
                eq_ci(key@, name@),
                forall|i: int| 0 <= i < self.slots@.len() ==> (#[trigger] self.slots@[i] matches Some(e)
                    ==> entry_ok(e)),
            decreases WAYS - w,
        {
            match &self.slots[base + w] {
                Some(e) => {
                    if e.qtype == qtype && e.expires > now && bytes_eq(&e.name, &key) {
                        assert(entry_ok(*e));
                        let d = e.expires - now;
                        let left: u32 = if d > MAX_TTL as u64 { MAX_TTL } else { d as u32 };
                        let data = clamp_data(&e.data, Ghost(e.name@), qtype, left);
                        proof {
                            lemma_eq_ci_sym(key@, name@);
                            lemma_data_ci(data, key@, name@, qtype);
                        }
                        return Some(Hit { data, left });
                    }
                },
                None => {},
            }
            w = w + 1;
        }
        None
    }

    /// Keeps `data` for `name`/`qtype` for `ttl` seconds from `now` (at
    /// most `MAX_TTL`), in place of what that question had, or of the
    /// entry of its set that expires first.
    pub fn insert(&mut self, name: &[u8], qtype: u16, now: u64, ttl: u32, data: Data)
        requires
            data_ok(data, name@, qtype),
        ensures
            final(self).capacity() == old(self).capacity(),
    {
        proof {
            use_type_invariant(&*self);
        }
        if now > u64::MAX - (MAX_TTL as u64) || ttl == 0 {
            return;
        }
        let t = if ttl > MAX_TTL { MAX_TTL } else { ttl };
        let key = lowered(name);
        let base = self.set_of(&key, qtype);
        // The slot to use: the question's own, an empty one, or the one
        // that expires first.
        let mut pick: usize = 0;
        let mut pick_exp: u64 = u64::MAX;
        let mut w: usize = 0;
        while w < WAYS
            invariant
                base + WAYS <= self.slots@.len() <= usize::MAX,
                pick < WAYS,
            decreases WAYS - w,
        {
            match &self.slots[base + w] {
                Some(e) => {
                    if e.qtype == qtype && bytes_eq(&e.name, &key) {
                        pick = w;
                        break;
                    }
                    if e.expires < pick_exp {
                        pick = w;
                        pick_exp = e.expires;
                    }
                },
                None => {
                    pick = w;
                    pick_exp = 0;
                },
            }
            w = w + 1;
        }
        proof {
            lemma_data_ci(data, name@, key@, qtype);
            assert forall|i: int| 0 <= i < key@.len() implies #[trigger] lower(key@[i]) == key@[i] by {
                lemma_lower_idem(name@[i]);
            }
        }
        let e = Entry { name: key, qtype, expires: now + t as u64, data };
        assert(entry_ok(e));
        let ghost old_slots = self.slots@;
        let mut taken = Cache::new(1);
        core::mem::swap(self, &mut taken);
        let Cache { mut slots, sets } = taken;
        slots.set(base + pick, Some(e));
        proof {
            assert forall|i: int| 0 <= i < slots@.len() implies (#[trigger] slots@[i] matches Some(e)
                ==> entry_ok(e)) by {
                if i != base + pick {
                    assert(slots@[i] == old_slots[i]);
                }
            }
        }
        *self = Cache { slots, sets };
    }
}

/// Data for a name is data for any name equal to it ignoring case.
pub proof fn lemma_data_ci(d: Data, a: Seq<u8>, b: Seq<u8>, qtype: u16)
    requires
        data_ok(d, a, qtype),
        eq_ci(a, b),
    ensures
        data_ok(d, b, qtype),
{
    match d {
        Data::Pos(rs, sec, ev) => {
            lemma_chain_ci(a, b, qtype, rrs(rs@));
            lemma_sec_ci(sec, ev@, a, b, qtype, RCODE_NOERROR, rrs(rs@), Seq::empty());
        },
        Data::Neg(code, rs, soa, sec, ev) => {
            lemma_chain_ci(a, b, qtype, rrs(rs@));
            lemma_sec_ci(sec, ev@, a, b, qtype, code, rrs(rs@), rrs(soa@));
        },
        Data::Deleg(_) => {},
        Data::Keys(k, c) => {
            lemma_eq_ci_trans(c@.last().zone, a, b);
        },
        Data::Cut(cut, u) => {
            lemma_lower_ci(a, b);
        },
    }
}

/// `recs_ok` does not depend on TTLs.
pub proof fn lemma_recs_ttl(a: Seq<RrS>, b: Seq<RrS>, sec: u8, e: Ev)
    requires
        same_but_ttl(a, b),
        recs_ok(a, sec, e),
    ensures
        recs_ok(b, sec, e),
{
    assert forall|i: int| 0 <= i < b.len() implies rec_secure(#[trigger] b[i], e) || (sec == INSECURE
        && rec_insecure(b[i], e)) by {
        assert(rec_secure(a[i], e) || (sec == INSECURE && rec_insecure(a[i], e)));
        if rec_secure(a[i], e) {
            let (k, j) = choose|k: int, j: int|
                0 <= k < e.signed.len() && 0 <= j < e.signed[k].rs.len() && same_rr(#[trigger] e.signed[k].rs[j], a[i])
                    && wild_ok(e.signed[k], e);
            assert(same_rr(e.signed[k].rs[j], b[i]));
        }
    }
}

pub proof fn lemma_sec_ttl(
    sec: u8,
    e: Ev,
    name: Seq<u8>,
    qtype: u16,
    code: u16,
    a: Seq<RrS>,
    b: Seq<RrS>,
    sa: Seq<RrS>,
    sb: Seq<RrS>,
)
    requires
        same_but_ttl(a, b),
        same_but_ttl(sa, sb),
        sec_ok(sec, e, name, qtype, code, a, sa),
    ensures
        sec_ok(sec, e, name, qtype, code, b, sb),
{
    lemma_chain_ttl(name, qtype, a, b);
    if sec != UNCHECKED {
        lemma_recs_ttl(a, b, sec, e);
        lemma_recs_ttl(sa, sb, sec, e);
    }
}

pub proof fn lemma_sec_ci(sec: u8, e: Ev, a: Seq<u8>, b: Seq<u8>, qtype: u16, code: u16, rs: Seq<RrS>, soa: Seq<RrS>)
    requires
        eq_ci(a, b),
        sec_ok(sec, e, a, qtype, code, rs, soa),
    ensures
        sec_ok(sec, e, b, qtype, code, rs, soa),
{
    lemma_chain_ci(a, b, qtype, rs);
    lemma_lower_ci(chain_end(a, qtype, rs), chain_end(b, qtype, rs));
    let (ea, eb) = (chain_end(a, qtype, rs), chain_end(b, qtype, rs));
    if exists|u: int| 0 <= u < e.unsigned.len() && insecure(#[trigger] e.unsigned[u], anchors(), ea) {
        let u = choose|u: int| 0 <= u < e.unsigned.len() && insecure(#[trigger] e.unsigned[u], anchors(), ea);
        assert(insecure(e.unsigned[u], anchors(), eb));
    }
}

} // verus!
