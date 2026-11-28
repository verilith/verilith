//! Validating what one walk down the zones returned (RFC 4035 §5.3,
//! §5.4): each RRset of the answer and authority sections against the
//! trusted keys of the zone its RRSIG names, or the proof that its zone is
//! unsigned; and for a negative answer, the NSEC or NSEC3 records that
//! deny the name or type. Proven to establish `dspec::sec_ok`.
use crate::cache::*;
use crate::canon::*;
use crate::dspec::*;
use crate::name::*;
use crate::nsec::*;
use crate::resolve::*;
use crate::rr::*;
use crate::sigcheck::*;
use crate::spec::*;
use crate::trust::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// `b` has every element of `a` at the same index.
pub open spec fn ev_prefix(a: Ev, b: Ev) -> bool {
    &&& a.signed.len() <= b.signed.len()
    &&& a.denials.len() <= b.denials.len()
    &&& a.unsigned.len() <= b.unsigned.len()
    &&& forall|k: int| 0 <= k < a.signed.len() ==> #[trigger] a.signed[k] == b.signed[k]
    &&& forall|k: int| 0 <= k < a.denials.len() ==> #[trigger] a.denials[k] == b.denials[k]
    &&& forall|k: int| 0 <= k < a.unsigned.len() ==> #[trigger] a.unsigned[k] == b.unsigned[k]
}

/// `b` has every element of `a`, shifted by the lengths in `o`.
pub open spec fn ev_shifted(a: Ev, b: Ev, o: Ev) -> bool {
    &&& o.signed.len() + a.signed.len() <= b.signed.len()
    &&& o.denials.len() + a.denials.len() <= b.denials.len()
    &&& o.unsigned.len() + a.unsigned.len() <= b.unsigned.len()
    &&& forall|k: int| 0 <= k < a.signed.len() ==> #[trigger] a.signed[k] == b.signed[o.signed.len() + k]
    &&& forall|k: int| 0 <= k < a.denials.len() ==> #[trigger] a.denials[k] == b.denials[o.denials.len() + k]
    &&& forall|k: int| 0 <= k < a.unsigned.len() ==> #[trigger] a.unsigned[k] == b.unsigned[o.unsigned.len() + k]
}

/// What `b` knows, `a` knew: anything proven from `a`'s evidence is
/// proven from `b`'s.
pub open spec fn ev_sub(a: Ev, b: Ev) -> bool {
    &&& forall|r: RrS| #[trigger] rec_secure(r, a) ==> rec_secure(r, b)
    &&& forall|n: Seq<u8>| #[trigger] name_insecure(n, a) ==> name_insecure(n, b)
    &&& forall|n: Seq<u8>| #[trigger] nx_proven(n, a) ==> nx_proven(n, b)
    &&& forall|n: Seq<u8>, t: u16| #[trigger] nodata_proven(n, t, a) ==> nodata_proven(n, t, b)
}

pub proof fn lemma_shift(a: Ev, b: Ev, o: Ev)
    requires
        ev_shifted(a, b, o),
    ensures
        ev_sub(a, b),
{
    let (os, od, ou) = (o.signed.len() as int, o.denials.len() as int, o.unsigned.len() as int);
    assert forall|r: RrS| #[trigger] rec_secure(r, a) implies rec_secure(r, b) by {
        let (k, j) = choose|k: int, j: int|
            0 <= k < a.signed.len() && 0 <= j < a.signed[k].rs.len() && same_rr(#[trigger] a.signed[k].rs[j], r) && wild_ok(
                a.signed[k],
                a,
            );
        let s = a.signed[k];
        assert(b.signed[os + k] == s);
        if expanded(s.rs[0].name, s.sig) {
            let d = choose|d: int|
                0 <= d < a.denials.len() && eq_ci((#[trigger] a.denials[d]).zone, s.zone()) && proves_expansion(
                    a.denials[d].ns,
                    lower_seq(s.rs[0].name),
                    lower_seq(suffix(s.rs[0].name, sig_labels(s.sig.rdata) as nat)),
                    a.denials[d].zone,
                );
            assert(b.denials[od + d] == a.denials[d]);
        }
        assert(wild_ok(b.signed[os + k], b));
        assert(same_rr(b.signed[os + k].rs[j], r));
    }
    assert forall|n: Seq<u8>| #[trigger] name_insecure(n, a) implies name_insecure(n, b) by {
        let u = choose|u: int| 0 <= u < a.unsigned.len() && insecure(#[trigger] a.unsigned[u], anchors(), n);
        assert(b.unsigned[ou + u] == a.unsigned[u]);
    }
    assert forall|n: Seq<u8>| #[trigger] nx_proven(n, a) implies nx_proven(n, b) by {
        let d = choose|d: int| 0 <= d < a.denials.len() && proves_nxdomain((#[trigger] a.denials[d]).ns, lower_seq(n), a.denials[d].zone);
        assert(b.denials[od + d] == a.denials[d]);
    }
    assert forall|n: Seq<u8>, t: u16| #[trigger] nodata_proven(n, t, a) implies nodata_proven(n, t, b) by {
        let d = choose|d: int| 0 <= d < a.denials.len() && proves_nodata((#[trigger] a.denials[d]).ns, lower_seq(n), t, a.denials[d].zone);
        assert(b.denials[od + d] == a.denials[d]);
    }
}

pub proof fn lemma_prefix(a: Ev, b: Ev)
    requires
        ev_prefix(a, b),
    ensures
        ev_sub(a, b),
{
    assert(ev_shifted(a, b, ev_empty()));
    lemma_shift(a, b, ev_empty());
}

pub proof fn lemma_join(a: Ev, b: Ev)
    requires
        ev_ok(a),
        ev_ok(b),
    ensures
        ev_ok(ev_join(a, b)),
        ev_sub(a, ev_join(a, b)),
        ev_sub(b, ev_join(a, b)),
{
    hide(signed_ok);
    hide(denial_ok);
    hide(unsigned_ok);
    let j = ev_join(a, b);
    assert(ev_prefix(a, j));
    lemma_prefix(a, j);
    assert(ev_shifted(b, j, a));
    lemma_shift(b, j, a);
    assert forall|k: int| 0 <= k < j.signed.len() implies signed_ok(#[trigger] j.signed[k], anchors()) by {
        if k < a.signed.len() {
            assert(j.signed[k] == a.signed[k]);
        } else {
            assert(j.signed[k] == b.signed[k - a.signed.len()]);
        }
    }
    assert forall|k: int| 0 <= k < j.denials.len() implies denial_ok(#[trigger] j.denials[k]) by {
        if k < a.denials.len() {
            assert(j.denials[k] == a.denials[k]);
        } else {
            assert(j.denials[k] == b.denials[k - a.denials.len()]);
        }
    }
    assert forall|k: int| 0 <= k < j.unsigned.len() implies unsigned_ok(#[trigger] j.unsigned[k], anchors()) by {
        if k < a.unsigned.len() {
            assert(j.unsigned[k] == a.unsigned[k]);
        } else {
            assert(j.unsigned[k] == b.unsigned[k - a.unsigned.len()]);
        }
    }
}

pub proof fn lemma_recs_sub(rs: Seq<RrS>, sec: u8, sec2: u8, a: Ev, b: Ev)
    requires
        recs_ok(rs, sec, a),
        ev_sub(a, b),
        sec == INSECURE ==> sec2 == INSECURE,
    ensures
        recs_ok(rs, sec2, b),
{
    assert forall|i: int| 0 <= i < rs.len() implies rec_secure(#[trigger] rs[i], b) || (sec2 == INSECURE
        && rec_insecure(rs[i], b)) by {
        if rec_secure(rs[i], a) {
        } else {
            assert(name_insecure(rs[i].name, a));
        }
    }
}

/// The chain's end: the last link's target, or `cur`.
pub fn chain_end_x(cur: &[u8], qtype: u16, rs: &Vec<Rr>) -> (r: Vec<u8>)
    ensures
        r@ == chain_end(cur@, qtype, rrs(rs@)),
{
    let mut c: Vec<u8> = to_vec(cur);
    let mut i: usize = 0;
    proof {
        assert(rrs(rs@).skip(0) =~= rrs(rs@));
    }
    while i < rs.len()
        invariant
            i <= rs@.len(),
            chain_end(cur@, qtype, rrs(rs@)) == chain_end(c@, qtype, rrs(rs@).skip(i as int)),
        decreases rs@.len() - i,
    {
        let r = &rs[i];
        let ghost tail = rrs(rs@).skip(i as int);
        proof {
            assert(tail[0] == r@);
            assert(tail.drop_first() =~= rrs(rs@).skip(i + 1));
        }
        if !(r.rtype == TYPE_CNAME && r.rclass == CLASS_IN && qtype != TYPE_CNAME && qtype != TYPE_ANY && eq_ci_exec(
            &r.name,
            &c,
        )) {
            return c;
        }
        c = to_vec(&r.rdata);
        i = i + 1;
    }
    proof {
        assert(rrs(rs@).skip(i as int).len() == 0);
    }
    c
}

/// What validating one RRset gives.
pub enum RStatus {
    /// Validated; with the denial records that allow a wildcard expansion.
    Secure(Ghost<Signed>, Ghost<Option<Denial>>),
    /// In an unsigned zone: the cut.
    Insecure(Vec<u8>, Ghost<Unsigned>),
    Bogus,
}

pub open spec fn rstatus_ok(s: RStatus, set: Seq<RrS>) -> bool {
    match s {
        RStatus::Secure(sg, d) => {
            &&& signed_ok(sg@, anchors())
            &&& sg@.rs == set
            &&& d@ matches Some(dd) ==> denial_ok(dd)
            &&& expanded(sg@.rs[0].name, sg@.sig) ==> (d@ matches Some(dd) && {
                &&& eq_ci(dd.zone, sg@.zone())
                &&& proves_expansion(
                    dd.ns,
                    lower_seq(sg@.rs[0].name),
                    lower_seq(suffix(sg@.rs[0].name, sig_labels(sg@.sig.rdata) as nat)),
                    dd.zone,
                )
            })
        },
        RStatus::Insecure(cut, u) => {
            &&& unsigned_ok(u@, anchors())
            &&& u@.cut == cut@
            &&& forall|i: int| 0 <= i < set.len() ==> is_sub(lower_seq(#[trigger] set[i].name), cut@)
        },
        RStatus::Bogus => true,
    }
}

/// `n` (as `lower_seq(n)`) is at or below `cut`.
fn under_cut(n: &[u8], cut: &[u8]) -> (b: bool)
    ensures
        b == is_sub(lower_seq(n@), cut@),
{
    let l = lowered(n);
    proof {
        lemma_lowered(n@, l@);
    }
    is_sub_exec(&l, cut)
}

fn all_under(set: &Vec<Rr>, cut: &[u8]) -> (b: bool)
    ensures
        b ==> forall|i: int| 0 <= i < set@.len() ==> is_sub(lower_seq(#[trigger] rrs(set@)[i].name), cut@),
{
    let mut i: usize = 0;
    while i < set.len()
        invariant
            forall|j: int| 0 <= j < i ==> is_sub(lower_seq(#[trigger] rrs(set@)[j].name), cut@),
        decreases set@.len() - i,
    {
        if !under_cut(&set[i].name, cut) {
            return false;
        }
        proof {
            assert(rrs(set@)[i as int] == set@[i as int]@);
        }
        i = i + 1;
    }
    true
}

/// `set` validated with the trusted keys of `signer` (and, for a wildcard
/// expansion, the proof the name itself does not exist).
fn signed_status(set: &Vec<Rr>, raw: &Raw, signer: &Vec<u8>, keys: &Vec<Rr>, c: Ghost<Seq<Link>>, wall: u32) -> (s: RStatus)
    requires
        keys_ok(c@, signer@, rrs(keys@)),
        set@.len() > 0,
    ensures
        rstatus_ok(s, rrs(set@)),
{
    let owner = &set[0].name;
    match validate_with(set, &raw.sigs, signer, keys, c, wall) {
        Some((si, sg)) => {
            let sgs = &raw.sigs[si];
            let ghost s = sg@;
            proof {
                assert(s.rs[0] == set@[0]@);
            }
            let labels = if sgs.rdata.len() > 3 { sgs.rdata[3] } else { 0 };
            if (labels as usize) < sig_label_count_x(owner) {
                // A wildcard expansion: the name itself must not exist.
                let (ns, ev) = validate_ns(&raw.ns, &raw.sigs, signer, keys, c, wall);
                let lo = lowered(owner);
                let so = suffix_x(owner, labels as usize);
                let ce = lowered(slice_subrange(owner.as_slice(), so, owner.len()));
                proof {
                    lemma_lowered(owner@, lo@);
                    lemma_lowered(suffix(owner@, labels as nat), ce@);
                }
                if find_expansion(&ns, &lo, &ce, signer) {
                    let ghost d = Denial { zone: signer@, ns: rrs(ns@), ev: ev@ };
                    proof {
                        lemma_eq_ci_sym(s.zone(), signer@);
                    }
                    return RStatus::Secure(sg, Ghost(Some(d)));
                }
                return RStatus::Bogus;
            }
            proof {
                assert(sgs@ == s.sig);
                assert(!expanded(s.rs[0].name, s.sig));
            }
            RStatus::Secure(sg, Ghost(None))
        },
        None => RStatus::Bogus,
    }
}

/// Validates the RRset `set` with the RRSIGs and NSEC records of `raw`.
fn rrset_status(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    set: &Vec<Rr>,
    raw: &Raw,
    wall: u32,
    budget: &mut u32,
    vd: u32,
) -> (s: RStatus)
    requires
        addrs_ok(roots@),
    ensures
        rstatus_ok(s, rrs(set@)),
        *final(budget) <= *old(budget),
    decreases vd, 0nat, 3nat,
{
    if set.len() == 0 {
        return RStatus::Bogus;
    }
    let owner = &set[0].name;
    let idx = sigs_for(&raw.sigs, owner, set[0].rtype);
    if idx.len() == 0 {
        // Unsigned: only if the zone of the server that sent it is.
        return match zone_status(roots, net, cache, &raw.zone, budget, vd) {
            Status::Unsigned(cut, u) => if all_under(set, &cut) {
                RStatus::Insecure(cut, u)
            } else {
                RStatus::Bogus
            },
            _ => RStatus::Bogus,
        };
    }
    let mut j: usize = 0;
    while j < idx.len()
        invariant
            addrs_ok(roots@),
            set@.len() > 0,
            *budget <= *old(budget),
            forall|i: int| 0 <= i < idx@.len() ==> #[trigger] idx@[i] < raw.sigs@.len(),
        decreases idx@.len() - j,
    {
        let sig = &raw.sigs[idx[j]];
        match signer_of(sig) {
            Some(signer) => {
                match zone_status(roots, net, cache, &signer, budget, vd) {
                    Status::Trusted(keys, c) => {
                        match signed_status(set, raw, &signer, &keys, c, wall) {
                            RStatus::Bogus => {},
                            r => {
                                return r;
                            },
                        }
                    },
                    Status::Unsigned(cut, u) => {
                        if all_under(set, &cut) {
                            return RStatus::Insecure(cut, u);
                        }
                    },
                    Status::Bogus => {},
                }
            },
            None => {},
        }
        j = j + 1;
    }
    RStatus::Bogus
}

/// The records of `all` from `i` on in the RRset of `all[i]`, and their
/// indices.
fn rrset_at(all: &Vec<Rr>, i: usize) -> (r: (Vec<Rr>, Vec<usize>))
    requires
        i < all@.len(),
    ensures
        r.0@.len() == r.1@.len(),
        r.0@.len() > 0,
        r.1@[0] == i,
        forall|x: int| 0 <= x < r.1@.len() ==> #[trigger] r.1@[x] < all@.len() && r.0@[x]@ == all@[r.1@[x] as int]@,
{
    let mut set: Vec<Rr> = Vec::new();
    let mut ix: Vec<usize> = Vec::new();
    set.push(all[i].copy());
    ix.push(i);
    let n = all.len();
    let mut j: usize = i + 1;
    while j < all.len()
        invariant
            i < all@.len(),
            set@.len() == ix@.len(),
            set@.len() > 0,
            ix@[0] == i,
            forall|x: int| 0 <= x < ix@.len() ==> #[trigger] ix@[x] < all@.len() && set@[x]@ == all@[ix@[x] as int]@,
        decreases all@.len() - j,
    {
        if all[j].rtype == all[i].rtype && eq_ci_exec(&all[j].name, &all[i].name) {
            set.push(all[j].copy());
            ix.push(j);
        }
        j = j + 1;
    }
    (set, ix)
}

/// What `check_step` establishes: every record validated, or in a proven
/// unsigned zone (`INSECURE` only); and for a final negative answer, the
/// denial.
pub open spec fn checked(sec: u8, e: Ev, cur: Seq<u8>, qtype: u16, code: u16, rs: Seq<RrS>, soa: Seq<RrS>, fin: bool) -> bool {
    let end = chain_end(cur, qtype, rs);
    &&& sec == SECURE || sec == INSECURE
    &&& validating()
    &&& ev_ok(e)
    &&& recs_ok(rs, sec, e)
    &&& recs_ok(soa, sec, e)
    &&& fin ==> {
        &&& code == RCODE_NXDOMAIN ==> nx_proven(end, e) || (sec == INSECURE && name_insecure(end, e))
        &&& (code == RCODE_NOERROR && links_only(cur, qtype, rs)) ==> nodata_proven(end, qtype, e) || (sec
            == INSECURE && name_insecure(end, e))
    }
}

/// The records of `all` marked done are validated, or (only if `sec` is
/// `INSECURE`) proven unsigned.
pub open spec fn marked_ok(all: Seq<Rr>, done: Seq<bool>, sec: u8, e: Ev) -> bool {
    forall|j: int| 0 <= j < all.len() && done[j] ==> rec_secure(#[trigger] all[j]@, e) || (sec == INSECURE
        && rec_insecure(all[j]@, e))
}

proof fn lemma_add_secure(e0: Ev, s: Signed, d: Option<Denial>, set: Seq<RrS>, all: Seq<Rr>, done: Seq<bool>, sec: u8) -> (e1: Ev)
    requires
        ev_ok(e0),
        signed_ok(s, anchors()),
        s.rs == set,
        d matches Some(dd) ==> denial_ok(dd),
        expanded(s.rs[0].name, s.sig) ==> (d matches Some(dd) && {
            &&& eq_ci(dd.zone, s.zone())
            &&& proves_expansion(
                dd.ns,
                lower_seq(s.rs[0].name),
                lower_seq(suffix(s.rs[0].name, sig_labels(s.sig.rdata) as nat)),
                dd.zone,
            )
        }),
        marked_ok(all, done, sec, e0),
    ensures
        ev_ok(e1),
        ev_sub(e0, e1),
        marked_ok(all, done, sec, e1),
        recs_ok(set, sec, e1),
{
    hide(denial_ok);
    hide(unsigned_ok);
    let e1 = match d {
        Some(dn) => Ev { signed: e0.signed.push(s), denials: e0.denials.push(dn), ..e0 },
        None => Ev { signed: e0.signed.push(s), ..e0 },
    };
    assert(ev_prefix(e0, e1));
    lemma_prefix(e0, e1);
    assert forall|k: int| 0 <= k < e1.signed.len() implies signed_ok(#[trigger] e1.signed[k], anchors()) by {
        if k < e0.signed.len() {
            assert(e1.signed[k] == e0.signed[k]);
        }
    }
    assert forall|k: int| 0 <= k < e1.denials.len() implies denial_ok(#[trigger] e1.denials[k]) by {
        if k < e0.denials.len() {
            assert(e1.denials[k] == e0.denials[k]);
        }
    }
    assert forall|k: int| 0 <= k < e1.unsigned.len() implies unsigned_ok(#[trigger] e1.unsigned[k], anchors()) by {
        assert(e1.unsigned[k] == e0.unsigned[k]);
    }
    let ks = e0.signed.len() as int;
    assert(e1.signed[ks] == s);
    if expanded(s.rs[0].name, s.sig) {
        assert(e1.denials[e0.denials.len() as int] == d.unwrap());
    }
    assert(wild_ok(s, e1));
    assert forall|y: int| 0 <= y < set.len() implies rec_secure(#[trigger] set[y], e1) by {
        assert(same_rr(e1.signed[ks].rs[y], set[y]));
    }
    assert forall|j: int| 0 <= j < all.len() && done[j] implies rec_secure(#[trigger] all[j]@, e1) || (sec
        == INSECURE && rec_insecure(all[j]@, e1)) by {
        if rec_secure(all[j]@, e0) {
        } else {
            assert(name_insecure(all[j]@.name, e0));
        }
    }
    e1
}

proof fn lemma_add_insecure(e0: Ev, u: Unsigned, set: Seq<RrS>, all: Seq<Rr>, done: Seq<bool>, sec: u8) -> (e1: Ev)
    requires
        ev_ok(e0),
        unsigned_ok(u, anchors()),
        forall|i: int| 0 <= i < set.len() ==> is_sub(lower_seq(#[trigger] set[i].name), u.cut),
        marked_ok(all, done, sec, e0),
    ensures
        ev_ok(e1),
        ev_sub(e0, e1),
        marked_ok(all, done, INSECURE, e1),
        recs_ok(set, INSECURE, e1),
{
    hide(denial_ok);
    hide(unsigned_ok);
    let e1 = Ev { unsigned: e0.unsigned.push(u), ..e0 };
    assert(ev_prefix(e0, e1));
    lemma_prefix(e0, e1);
    assert forall|k: int| 0 <= k < e1.unsigned.len() implies unsigned_ok(#[trigger] e1.unsigned[k], anchors()) by {
        if k < e0.unsigned.len() {
            assert(e1.unsigned[k] == e0.unsigned[k]);
        }
    }
    let ku = e0.unsigned.len() as int;
    assert(e1.unsigned[ku] == u);
    assert forall|y: int| 0 <= y < set.len() implies rec_insecure(#[trigger] set[y], e1) by {
        assert(insecure(e1.unsigned[ku], anchors(), set[y].name));
    }
    assert forall|j: int| 0 <= j < all.len() && done[j] implies rec_secure(#[trigger] all[j]@, e1) || rec_insecure(all[j]@, e1) by {
        if rec_secure(all[j]@, e0) {
        } else {
            assert(name_insecure(all[j]@.name, e0));
        }
    }
    e1
}

/// Marks the records `ix` of `all` (copied in `set`, which is validated)
/// done.
fn mark_done(done: &mut Vec<bool>, ix: &Vec<usize>, set: &Vec<Rr>, all: &Vec<Rr>, i: usize, sec: Ghost<u8>, e: Ghost<Ev>)
    requires
        i < all@.len(),
        set@.len() == ix@.len(),
        old(done)@.len() == all@.len(),
        forall|j: int| 0 <= j < i ==> old(done)@[j],
        marked_ok(all@, old(done)@, sec@, e@),
        forall|y: int| 0 <= y < ix@.len() ==> #[trigger] ix@[y] < all@.len() && set@[y]@ == all@[ix@[y] as int]@,
        recs_ok(rrs(set@), sec@, e@),
        ix@.len() > 0,
        ix@[0] == i,
    ensures
        final(done)@.len() == all@.len(),
        forall|j: int| 0 <= j <= i ==> final(done)@[j],
        marked_ok(all@, final(done)@, sec@, e@),
{
    let mut x: usize = 0;
    while x < ix.len()
        invariant
            i < all@.len(),
            x <= ix@.len(),
            set@.len() == ix@.len(),
            done@.len() == all@.len(),
            forall|j: int| 0 <= j < i ==> done@[j],
            x > 0 ==> done@[i as int],
            ix@[0] == i,
            marked_ok(all@, done@, sec@, e@),
            forall|y: int| 0 <= y < ix@.len() ==> #[trigger] ix@[y] < all@.len() && set@[y]@ == all@[ix@[y] as int]@,
            recs_ok(rrs(set@), sec@, e@),
        decreases ix@.len() - x,
    {
        let ghost d0 = done@;
        proof {
            assert(rrs(set@)[x as int] == set@[x as int]@);
            assert(ix@[x as int] < all@.len());
        }
        done.set(ix[x], true);
        proof {
            assert forall|j: int| 0 <= j < all@.len() && done@[j] implies rec_secure(#[trigger] all@[j]@, e@) || (sec@
                == INSECURE && rec_insecure(all@[j]@, e@)) by {
                if j != ix@[x as int] as int {
                    assert(d0[j]);
                }
            }
        }
        x = x + 1;
    }
}

/// Validates the records of `all` (the answer and authority records of
/// one response), adding to the evidence.
fn check_records(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    all: &Vec<Rr>,
    raw: &Raw,
    wall: u32,
    budget: &mut u32,
    vd: u32,
) -> (r: Option<(u8, Ghost<Ev>)>)
    requires
        addrs_ok(roots@),
    ensures
        r matches Some((sec, e)) ==> (sec == SECURE || sec == INSECURE) && ev_ok(e@) && recs_ok(rrs(all@), sec, e@),
        *final(budget) <= *old(budget),
    decreases vd, 0nat, 4nat,
{
    let ghost mut e = ev_empty();
    let mut sec = SECURE;
    let mut done: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < all.len()
        invariant
            i <= all@.len(),
            done@.len() == i,
            forall|j: int| 0 <= j < i ==> !done@[j],
        decreases all@.len() - i,
    {
        done.push(false);
        i = i + 1;
    }
    let mut i: usize = 0;
    while i < all.len()
        invariant
            addrs_ok(roots@),
            i <= all@.len(),
            done@.len() == all@.len(),
            sec == SECURE || sec == INSECURE,
            ev_ok(e),
            forall|j: int| 0 <= j < i ==> done@[j],
            marked_ok(all@, done@, sec, e),
            *budget <= *old(budget),
        decreases all@.len() - i,
    {
        if !done[i] {
            let (set, ix) = rrset_at(all, i);
            let ghost e0 = e;
            match rrset_status(roots, net, cache, &set, raw, wall, budget, vd) {
                RStatus::Secure(sg, d) => {
                    proof {
                        e = lemma_add_secure(e0, sg@, d@, rrs(set@), all@, done@, sec);
                    }
                },
                RStatus::Insecure(cut, u) => {
                    proof {
                        e = lemma_add_insecure(e0, u@, rrs(set@), all@, done@, sec);
                    }
                    sec = INSECURE;
                },
                RStatus::Bogus => {
                    return None;
                },
            }
            mark_done(&mut done, &ix, &set, all, i, Ghost(sec), Ghost(e));
        }
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < rrs(all@).len() implies rec_secure(#[trigger] rrs(all@)[j], e) || (sec
            == INSECURE && rec_insecure(rrs(all@)[j], e)) by {
            assert(rrs(all@)[j] == all@[j]@);
            assert(done@[j]);
            assert(rec_secure(all@[j]@, e) || (sec == INSECURE && rec_insecure(all@[j]@, e)));
        }
    }
    Some((sec, Ghost(e)))
}

/// `all` is `rs` then `soa`, copied.
fn concat(rs: &Vec<Rr>, soa: &Vec<Rr>) -> (all: Vec<Rr>)
    ensures
        rrs(all@) == rrs(rs@) + rrs(soa@),
{
    let mut all = copy_rrs(rs);
    extend_rrs(&mut all, soa);
    all
}

proof fn lemma_recs_split(a: Seq<RrS>, b: Seq<RrS>, sec: u8, e: Ev)
    requires
        recs_ok(a + b, sec, e),
    ensures
        recs_ok(a, sec, e),
        recs_ok(b, sec, e),
{
    assert forall|i: int| 0 <= i < a.len() implies rec_secure(#[trigger] a[i], e) || (sec == INSECURE && rec_insecure(a[i], e)) by {
        assert((a + b)[i] == a[i]);
    }
    assert forall|i: int| 0 <= i < b.len() implies rec_secure(#[trigger] b[i], e) || (sec == INSECURE && rec_insecure(b[i], e)) by {
        assert((a + b)[a.len() + i] == b[i]);
    }
}

proof fn lemma_add_unsigned(e: Ev, u: Unsigned) -> (e1: Ev)
    requires
        ev_ok(e),
        unsigned_ok(u, anchors()),
    ensures
        ev_ok(e1),
        ev_sub(e, e1),
        e1 == (Ev { unsigned: e.unsigned.push(u), ..e }),
{
    hide(denial_ok);
    hide(unsigned_ok);
    let e1 = Ev { unsigned: e.unsigned.push(u), ..e };
    assert(ev_prefix(e, e1));
    lemma_prefix(e, e1);
    assert forall|k: int| 0 <= k < e1.unsigned.len() implies unsigned_ok(#[trigger] e1.unsigned[k], anchors()) by {
        if k < e.unsigned.len() {
            assert(e1.unsigned[k] == e.unsigned[k]);
        }
    }
    e1
}

proof fn lemma_add_denial(e: Ev, d: Denial) -> (e1: Ev)
    requires
        ev_ok(e),
        denial_ok(d),
    ensures
        ev_ok(e1),
        ev_sub(e, e1),
        e1 == (Ev { denials: e.denials.push(d), ..e }),
{
    hide(denial_ok);
    hide(unsigned_ok);
    let e1 = Ev { denials: e.denials.push(d), ..e };
    assert(ev_prefix(e, e1));
    lemma_prefix(e, e1);
    assert forall|k: int| 0 <= k < e1.denials.len() implies denial_ok(#[trigger] e1.denials[k]) by {
        if k < e.denials.len() {
            assert(e1.denials[k] == e.denials[k]);
        }
    }
    e1
}

/// Validates one walk's result: records `rs` from `cur` (a chain) and
/// `soa`, with RCODE `code`; for the walk that ends the answer (`fin`),
/// the denial of the name or type as well. `None`: bogus.
pub fn check_step(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    cur: &[u8],
    qtype: u16,
    code: u16,
    rs: &Vec<Rr>,
    soa: &Vec<Rr>,
    raw: &Raw,
    fin: bool,
    budget: &mut u32,
    vd: u32,
) -> (r: Option<(u8, Ghost<Ev>)>)
    requires
        addrs_ok(roots@),
        validating(),
        chain(cur@, qtype, rrs(rs@)),
    ensures
        r matches Some((sec, e)) ==> checked(sec, e@, cur@, qtype, code, rrs(rs@), rrs(soa@), fin),
        *final(budget) <= *old(budget),
    decreases vd, 0nat, 5nat,
{
    let wall = net.wall();
    let all = concat(rs, soa);
    let (mut sec, e0) = match check_records(roots, net, cache, &all, raw, wall, budget, vd) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let ghost mut e = e0@;
    proof {
        lemma_recs_split(rrs(rs@), rrs(soa@), sec, e);
    }
    let nl = count_links(cur, qtype, rs);
    let neg = code == RCODE_NXDOMAIN || (code == RCODE_NOERROR && nl == rs.len());
    if !fin || !neg {
        return Some((sec, Ghost(e)));
    }
    let end = chain_end_x(cur, qtype, rs);
    let le = lowered(&end);
    proof {
        lemma_lowered(end@, le@);
    }
    let pz = match ns_signer(&raw.ns, &raw.sigs) {
        Some(p) => p,
        None => to_vec(&raw.zone),
    };
    match zone_status(roots, net, cache, &pz, budget, vd) {
        Status::Trusted(keys, c) => {
            let (ns, ev) = validate_ns(&raw.ns, &raw.sigs, &pz, &keys, c, wall);
            let ok = if code == RCODE_NXDOMAIN {
                find_nxdomain(&ns, &le, &pz)
            } else {
                find_nodata(&ns, &le, qtype, &pz)
            };
            if !ok {
                return None;
            }
            let ghost d = Denial { zone: pz@, ns: rrs(ns@), ev: ev@ };
            proof {
                let e1 = lemma_add_denial(e, d);
                lemma_recs_sub(rrs(rs@), sec, sec, e, e1);
                lemma_recs_sub(rrs(soa@), sec, sec, e, e1);
                let k = e.denials.len() as int;
                assert(e1.denials[k] == d);
                if code == RCODE_NXDOMAIN {
                    assert(nx_proven(end@, e1));
                } else {
                    assert(nodata_proven(end@, qtype, e1));
                }
                e = e1;
            }
            Some((sec, Ghost(e)))
        },
        Status::Unsigned(cut, u) => {
            if !is_sub_exec(&le, &cut) {
                return None;
            }
            proof {
                let e1 = lemma_add_unsigned(e, u@);
                lemma_recs_sub(rrs(rs@), sec, INSECURE, e, e1);
                lemma_recs_sub(rrs(soa@), sec, INSECURE, e, e1);
                let k = e.unsigned.len() as int;
                assert(e1.unsigned[k] == u@);
                assert(insecure(e1.unsigned[k], anchors(), end@));
                assert(name_insecure(end@, e1));
                e = e1;
            }
            sec = INSECURE;
            Some((sec, Ghost(e)))
        },
        Status::Bogus => None,
    }
}

} // verus!
