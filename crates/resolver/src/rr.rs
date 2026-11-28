//! Owned resource records, and the lemmas about chains of them.
use crate::spec::*;
#[cfg(verus_only)]
use crate::name::*;
#[cfg(verus_only)]
use verilith_dns::message::section_of;
use verilith_dns::message::{RecordRef, Section};
use verilith_dns::parse::append;
use verilith_dns::spec::*;
use verilith_dns::Message;
use vstd::prelude::*;

verus! {

/// A resource record, owned. `name` is uncompressed wire form; `rdata` is
/// canonical (verilith-dns: names inside it uncompressed).
pub struct Rr {
    pub name: Vec<u8>,
    pub rtype: u16,
    pub rclass: u16,
    pub ttl: u32,
    pub rdata: Vec<u8>,
}

impl View for Rr {
    type V = RrS;

    open spec fn view(&self) -> RrS {
        RrS { name: self.name@, rtype: self.rtype, rclass: self.rclass, ttl: self.ttl, rdata: self.rdata@ }
    }
}

pub open spec fn rrs(v: Seq<Rr>) -> Seq<RrS> {
    Seq::new(v.len(), |i: int| v[i]@)
}

/// `x` is a record of section `s` of `m`.
pub open spec fn in_section(m: SpecMessage, s: Section, x: RrS) -> bool {
    exists|i: int| 0 <= i < section_of(m, s).len() && rr_of(#[trigger] section_of(m, s)[i]) == x
}

pub fn to_vec(s: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == s@,
{
    let mut v: Vec<u8> = Vec::new();
    append(&mut v, s);
    proof {
        assert(v@ =~= s@);
    }
    v
}

pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

impl Rr {
    pub fn copy(&self) -> (r: Rr)
        ensures
            r@ == self@,
    {
        Rr { name: to_vec(&self.name), rtype: self.rtype, rclass: self.rclass, ttl: self.ttl, rdata: to_vec(&self.rdata) }
    }

    pub fn with_ttl(&self, ttl: u32) -> (r: Rr)
        ensures
            r@ == (RrS { ttl, ..self@ }),
    {
        Rr { name: to_vec(&self.name), rtype: self.rtype, rclass: self.rclass, ttl, rdata: to_vec(&self.rdata) }
    }
}

/// Copies record `i` of section `s`.
pub fn take_record(m: &Message, s: Section, i: usize) -> (r: Rr)
    requires
        i < section_of(m@, s).len(),
    ensures
        r@ == rr_of(section_of(m@, s)[i as int]),
        in_section(m@, s, r@),
{
    let rr = m.record(s, i).unwrap();
    let r = Rr { name: to_vec(rr.name), rtype: rr.rtype, rclass: rr.rclass, ttl: rr.ttl, rdata: to_vec(rr.rdata) };
    proof {
        assert(rr_of(section_of(m@, s)[i as int]) == r@);
    }
    r
}

pub fn copy_rrs(v: &Vec<Rr>) -> (r: Vec<Rr>)
    ensures
        rrs(r@) == rrs(v@),
{
    let mut out: Vec<Rr> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] out@[j])@ == v@[j]@,
        decreases v@.len() - i,
    {
        out.push(v[i].copy());
        i = i + 1;
    }
    proof {
        assert(rrs(out@) =~= rrs(v@));
    }
    out
}

/// Appends copies of `b` to `a`.
pub fn extend_rrs(a: &mut Vec<Rr>, b: &Vec<Rr>)
    ensures
        rrs(final(a)@) == rrs(old(a)@) + rrs(b@),
{
    let ghost a0 = rrs(a@);
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b@.len(),
            a@.len() == a0.len() + i,
            forall|j: int| 0 <= j < a0.len() ==> (#[trigger] a@[j])@ == a0[j],
            forall|j: int| 0 <= j < i ==> (#[trigger] a@[a0.len() + j])@ == b@[j]@,
        decreases b@.len() - i,
    {
        a.push(b[i].copy());
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies (#[trigger] a@[a0.len() + j])@ == b@[j]@ by {}
        }
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < rrs(a@).len() implies #[trigger] rrs(a@)[j] == (a0 + rrs(b@))[j] by {
            if j >= a0.len() {
                assert(a@[a0.len() + (j - a0.len())]@ == b@[j - a0.len()]@);
            }
        }
        assert(rrs(a@) =~= a0 + rrs(b@));
    }
}

pub proof fn lemma_rrs_push(v: Seq<Rr>, x: Rr)
    ensures
        rrs(v.push(x)) == rrs(v).push(x@),
{
    assert(rrs(v.push(x)) =~= rrs(v).push(x@));
}

// ---------------------------------------------------------------------------
// Chains
// ---------------------------------------------------------------------------

/// A final record is never a CNAME link, so the two branches of `chain`
/// do not overlap.
pub proof fn lemma_final_not_link(r: RrS, cur: Seq<u8>, qtype: u16)
    requires
        final_rr(r, cur, qtype),
    ensures
        !cname_link(r, cur, qtype),
{
}

/// A chain of links followed by a chain from its end is a chain.
pub proof fn lemma_chain_append(cur: Seq<u8>, qtype: u16, a: Seq<RrS>, b: Seq<RrS>)
    requires
        links_only(cur, qtype, a),
        chain(chain_end(cur, qtype, a), qtype, b),
    ensures
        chain(cur, qtype, a + b),
        chain_links(cur, qtype, a + b) == a.len() + chain_links(chain_end(cur, qtype, a), qtype, b),
        chain_end(cur, qtype, a + b) == chain_end(chain_end(cur, qtype, a), qtype, b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        // chain_links == a.len() > 0, so a[0] is a link.
        assert(cname_link(a[0], cur, qtype));
        let rest = a.drop_first();
        assert((a + b).drop_first() =~= rest + b);
        assert((a + b)[0] == a[0]);
        lemma_chain_append(a[0].rdata, qtype, rest, b);
    }
}

/// Following the chain from a name equal ignoring case gives the same
/// chain, the same number of links, and an end equal ignoring case.
pub proof fn lemma_chain_ci(cur: Seq<u8>, cur2: Seq<u8>, qtype: u16, rs: Seq<RrS>)
    requires
        eq_ci(cur, cur2),
    ensures
        chain(cur, qtype, rs) == chain(cur2, qtype, rs),
        chain_links(cur, qtype, rs) == chain_links(cur2, qtype, rs),
        eq_ci(chain_end(cur, qtype, rs), chain_end(cur2, qtype, rs)),
    decreases rs.len(),
{
    if rs.len() > 0 {
        let r = rs[0];
        if eq_ci(r.name, cur) {
            lemma_eq_ci_trans(r.name, cur, cur2);
        }
        if eq_ci(r.name, cur2) {
            lemma_eq_ci_sym(cur, cur2);
            lemma_eq_ci_trans(r.name, cur2, cur);
        }
        if cname_link(r, cur, qtype) {
            lemma_eq_ci_refl(r.rdata);
            lemma_chain_ci(r.rdata, r.rdata, qtype, rs.drop_first());
        } else {
            assert forall|i: int| 0 <= i < rs.len() implies final_rr(#[trigger] rs[i], cur, qtype)
                == final_rr(rs[i], cur2, qtype) by {
                if eq_ci(rs[i].name, cur) {
                    lemma_eq_ci_trans(rs[i].name, cur, cur2);
                }
                if eq_ci(rs[i].name, cur2) {
                    lemma_eq_ci_sym(cur, cur2);
                    lemma_eq_ci_trans(rs[i].name, cur2, cur);
                }
            }
        }
    }
}

/// Changing TTLs does not change a chain.
pub open spec fn same_but_ttl(a: Seq<RrS>, b: Seq<RrS>) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).name == b[i].name && a[i].rtype == b[i].rtype
        && a[i].rclass == b[i].rclass && a[i].rdata == b[i].rdata
}

pub proof fn lemma_chain_ttl(cur: Seq<u8>, qtype: u16, a: Seq<RrS>, b: Seq<RrS>)
    requires
        same_but_ttl(a, b),
    ensures
        chain(cur, qtype, a) == chain(cur, qtype, b),
        chain_links(cur, qtype, a) == chain_links(cur, qtype, b),
        chain_end(cur, qtype, a) == chain_end(cur, qtype, b),
    decreases a.len(),
{
    if a.len() > 0 {
        assert(a[0].name == b[0].name);
        let (a1, b1) = (a.drop_first(), b.drop_first());
        assert forall|i: int| 0 <= i < a1.len() implies (#[trigger] a1[i]).name == b1[i].name
            && a1[i].rtype == b1[i].rtype && a1[i].rclass == b1[i].rclass && a1[i].rdata == b1[i].rdata by {
            assert(a1[i] == a[i + 1]);
            assert(b1[i] == b[i + 1]);
        }
        if cname_link(a[0], cur, qtype) {
            lemma_chain_ttl(a[0].rdata, qtype, a1, b1);
        } else {
            assert(!cname_link(b[0], cur, qtype));
            if forall|i: int| 0 <= i < a.len() ==> final_rr(#[trigger] a[i], cur, qtype) {
                assert forall|i: int| 0 <= i < b.len() implies final_rr(#[trigger] b[i], cur, qtype) by {
                    assert(final_rr(a[i], cur, qtype));
                }
            }
            if forall|i: int| 0 <= i < b.len() ==> final_rr(#[trigger] b[i], cur, qtype) {
                assert forall|i: int| 0 <= i < a.len() implies final_rr(#[trigger] a[i], cur, qtype) by {
                    assert(final_rr(b[i], cur, qtype));
                }
            }
        }
    }
}

} // verus!
