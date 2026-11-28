//! The chain of trust (RFC 4035 §5): what a zone's keys are, validated
//! from the trust anchors down, or the proof that the zone is unsigned.
//! Proven: every key handed out as trusted is in a DNSKEY RRset at the end
//! of a `dspec::chain_ok` chain, and every zone said to be unsigned is at
//! or below a cut `dspec::unsigned_ok` proves.
use crate::cache::*;
use crate::canon::*;
use crate::dspec::*;
use crate::name::*;
use crate::nsec::*;
use crate::resolve::*;
use crate::rr::*;
use crate::sigcheck::*;
use crate::spec::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// What the validator knows of a zone: its trusted keys (DNSKEY records)
/// and the chain that makes them trusted, or that it is at or below an
/// unsigned cut, or nothing usable (bogus).
pub enum Status {
    Trusted(Vec<Rr>, Ghost<Seq<Link>>),
    Unsigned(Vec<u8>, Ghost<Unsigned>),
    Bogus,
}

/// Every key of `keys` is in the zone's DNSKEY RRset at the end of a chain
/// of trust.
pub open spec fn keys_ok(c: Seq<Link>, zone: Seq<u8>, keys: Seq<RrS>) -> bool {
    &&& chain_ok(c, anchors())
    &&& eq_ci(c.last().zone, zone)
    &&& forall|i: int| 0 <= i < keys.len() ==> has_key(c.last().keys, #[trigger] keys[i].rdata)
}

/// `zone` (any spelling) is at or below the proven unsigned cut `u`.
pub open spec fn cut_ok(u: Unsigned, cut: Seq<u8>, zone: Seq<u8>) -> bool {
    unsigned_ok(u, anchors()) && u.cut == cut && is_sub(lower_seq(zone), cut)
}

pub open spec fn status_ok(s: Status, zone: Seq<u8>) -> bool {
    match s {
        Status::Trusted(keys, c) => keys_ok(c@, zone, rrs(keys@)),
        Status::Unsigned(cut, u) => cut_ok(u@, cut@, zone),
        Status::Bogus => true,
    }
}

pub proof fn lemma_lower_ci(a: Seq<u8>, b: Seq<u8>)
    requires
        eq_ci(a, b),
    ensures
        lower_seq(a) == lower_seq(b),
{
    assert(lower_seq(a) =~= lower_seq(b));
}

pub proof fn lemma_lowered(w: Seq<u8>, r: Seq<u8>)
    requires
        r.len() == w.len(),
        forall|i: int| 0 <= i < w.len() ==> #[trigger] r[i] == lower(w[i]),
    ensures
        r == lower_seq(w),
{
    assert(r =~= lower_seq(w));
}

/// `rrset_signed` holds for any spelling of the zone.
pub proof fn lemma_signed_zone_ci(rs: Seq<RrS>, sig: RrS, key: Seq<u8>, z1: Seq<u8>, z2: Seq<u8>, now: u32)
    requires
        rrset_signed(rs, sig, key, z1, now),
        eq_ci(z1, z2),
    ensures
        rrset_signed(rs, sig, key, z2, now),
{
    lemma_eq_ci_trans(sig_signer(sig.rdata), z1, z2);
    lemma_is_sub_ci(rs[0].name, z1, z2);
    lemma_eq_ci_sym(z1, z2);
    if eq_ci(rs[0].name, z2) {
        lemma_eq_ci_trans(rs[0].name, z2, z1);
    }
    if eq_ci(rs[0].name, z1) {
        lemma_eq_ci_trans(rs[0].name, z1, z2);
    }
}

pub proof fn lemma_ds_ci(ds: Seq<u8>, o1: Seq<u8>, o2: Seq<u8>, key: Seq<u8>)
    requires
        ds_matches(ds, o1, key),
        eq_ci(o1, o2),
    ensures
        ds_matches(ds, o2, key),
{
    lemma_lower_ci(o1, o2);
}

/// The RRSIGs of `sigs` that may cover the RRset `owner`/`t`, by index.
pub fn sigs_for(sigs: &Vec<Rr>, owner: &[u8], t: u16) -> (r: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i] < sigs@.len(),
{
    let mut out: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < sigs.len()
        invariant
            i <= sigs@.len(),
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] < sigs@.len(),
        decreases sigs@.len() - i,
    {
        let s = &sigs[i];
        if s.rtype == TYPE_RRSIG && s.rdata.len() >= 19 && u16_at_x(&s.rdata, 0) == t && eq_ci_exec(&s.name, owner) {
            out.push(i);
        }
        i = i + 1;
    }
    out
}

/// The signer's name of an RRSIG, if well formed.
pub fn signer_of(sig: &Rr) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(s) ==> sig_wf(sig@.rdata) && s@ == sig_signer(sig@.rdata),
{
    let rd = &sig.rdata;
    if rd.len() < 19 {
        return None;
    }
    match name_len_x(rd, 18) {
        Some(l) => Some(to_vec(slice_subrange(rd.as_slice(), 18, 18 + l))),
        None => None,
    }
}

/// Tries every key of `keys` whose algorithm and tag the RRSIG names.
pub fn try_keys(rs: &Vec<Rr>, sig: &Rr, keys: &Vec<Rr>, zone: &[u8], now: u32) -> (r: Option<usize>)
    ensures
        r matches Some(k) ==> k < keys@.len() && rrset_signed(rrs(rs@), sig@, keys@[k as int]@.rdata, zone@, now),
{
    let rd = &sig.rdata;
    if rd.len() < 19 {
        return None;
    }
    let tag = u16_at_x(rd, 16);
    let mut k: usize = 0;
    while k < keys.len()
        invariant
            rd@.len() >= 19,
        decreases keys@.len() - k,
    {
        let kd = &keys[k].rdata;
        if kd.len() > 4 && kd[3] == rd[2] && key_tag(kd) == tag && rrset_valid(rs, sig, kd, zone, now) {
            return Some(k);
        }
        k = k + 1;
    }
    None
}

/// The RRset `rs` validated with RRSIGs from `sigs` and the trusted keys
/// of `zone`: the evidence, if one RRSIG and one key validate it.
pub fn validate_with(rs: &Vec<Rr>, sigs: &Vec<Rr>, zone: &[u8], keys: &Vec<Rr>, c: Ghost<Seq<Link>>, now: u32) -> (r:
    Option<(usize, Ghost<Signed>)>)
    requires
        keys_ok(c@, zone@, rrs(keys@)),
    ensures
        r matches Some((i, s)) ==> {
            &&& s@.chain == c@
            &&& i < sigs@.len()
            &&& signed_ok(s@, anchors())
            &&& s@.rs == rrs(rs@)
            &&& s@.sig == sigs@[i as int]@
            &&& eq_ci(s@.zone(), zone@)
        },
{
    if rs.len() == 0 {
        return None;
    }
    let idx = sigs_for(sigs, &rs[0].name, rs[0].rtype);
    let mut j: usize = 0;
    while j < idx.len()
        invariant
            keys_ok(c@, zone@, rrs(keys@)),
            forall|i: int| 0 <= i < idx@.len() ==> #[trigger] idx@[i] < sigs@.len(),
        decreases idx@.len() - j,
    {
        let sig = &sigs[idx[j]];
        match signer_of(sig) {
            Some(sn) => {
                if eq_ci_exec(&sn, zone) {
                    match try_keys(rs, sig, keys, zone, now) {
                        Some(k) => {
                            let ghost s = Signed { rs: rrs(rs@), sig: sig@, key: keys@[k as int]@.rdata, chain: c@, now };
                            proof {
                                assert(rrs(keys@)[k as int] == keys@[k as int]@);
                                assert(has_key(c@.last().keys, s.key));
                                lemma_eq_ci_sym(c@.last().zone, zone@);
                                lemma_signed_zone_ci(rrs(rs@), sig@, s.key, zone@, c@.last().zone, now);
                            }
                            return Some((idx[j], Ghost(s)));
                        },
                        None => {},
                    }
                }
            },
            None => {},
        }
        j = j + 1;
    }
    None
}

proof fn lemma_singletons(v: Seq<RrS>, ev: Seq<Signed>, zone: Seq<u8>)
    requires
        ev.len() == v.len(),
        forall|k: int| 0 <= k < ev.len() ==> signed_ok(#[trigger] ev[k], anchors()) && eq_ci(ev[k].zone(), zone)
            && ev[k].rs == seq![v[k]],
    ensures
        all_validated(v, ev, anchors(), zone),
{
    hide(signed_ok);
    hide(eq_ci);
    assert forall|x: int| 0 <= x < v.len() implies in_validated(ev, #[trigger] v[x]) by {
        assert(ev[x].rs == seq![v[x]]);
        assert(ev[x].rs.len() == 1);
        assert(ev[x].rs[0] == v[x]);
        assert(0 <= x < ev.len() && 0 <= 0int < ev[x].rs.len() && v[x] == ev[x].rs[0int]);
    }
    assert forall|k: int| 0 <= k < ev.len() implies signed_ok(#[trigger] ev[k], anchors()) && eq_ci(ev[k].zone(), zone) by {}
}

/// The NSEC and NSEC3 records of `ns` that validate with `zone`'s keys,
/// each an RRset of its own (an owner has one NSEC, RFC 4034 §4).
pub fn validate_ns(ns: &Vec<Rr>, sigs: &Vec<Rr>, zone: &[u8], keys: &Vec<Rr>, c: Ghost<Seq<Link>>, now: u32) -> (r: (
    Vec<Rr>,
    Ghost<Seq<Signed>>,
))
    requires
        keys_ok(c@, zone@, rrs(keys@)),
    ensures
        all_validated(rrs(r.0@), r.1@, anchors(), zone@),
        r.1@.len() == r.0@.len(),
{
    let mut out: Vec<Rr> = Vec::new();
    let ghost mut ev: Seq<Signed> = Seq::empty();
    let mut i: usize = 0;
    while i < ns.len()
        invariant
            keys_ok(c@, zone@, rrs(keys@)),
            ev.len() == out@.len(),
            forall|k: int| 0 <= k < ev.len() ==> signed_ok(#[trigger] ev[k], anchors()) && eq_ci(ev[k].zone(), zone@)
                && ev[k].rs == seq![rrs(out@)[k]],
        decreases ns@.len() - i,
    {
        let r = &ns[i];
        if r.rtype == TYPE_NSEC || r.rtype == TYPE_NSEC3 {
            let mut one: Vec<Rr> = Vec::new();
            one.push(r.copy());
            match validate_with(&one, sigs, zone, keys, c, now) {
                Some((_, s)) => {
                    let ghost o = out@;
                    out.push(r.copy());
                    proof {
                        assert(rrs(one@) =~= seq![rrs(out@)[o.len() as int]]);
                        ev = ev.push(s@);
                        assert forall|k: int| 0 <= k < ev.len() implies signed_ok(#[trigger] ev[k], anchors()) && eq_ci(
                            ev[k].zone(),
                            zone@,
                        ) && ev[k].rs == seq![rrs(out@)[k]] by {
                            if k < o.len() {
                                assert(out@[k] == o[k]);
                                assert(rrs(out@)[k] == rrs(o)[k]);
                            }
                        }
                    }
                },
                None => {},
            }
        }
        i = i + 1;
    }
    proof {
        lemma_singletons(rrs(out@), ev, zone@);
    }
    (out, Ghost(ev))
}

/// The signer of the first RRSIG over an NSEC or NSEC3 in `ns`.
pub fn ns_signer(ns: &Vec<Rr>, sigs: &Vec<Rr>) -> Option<Vec<u8>> {
    let mut i: usize = 0;
    while i < ns.len()
        decreases ns@.len() - i,
    {
        let r = &ns[i];
        if r.rtype == TYPE_NSEC || r.rtype == TYPE_NSEC3 {
            let idx = sigs_for(sigs, &r.name, r.rtype);
            if idx.len() > 0 {
                return signer_of(&sigs[idx[0]]);
            }
        }
        i = i + 1;
    }
    None
}

pub fn is_root(z: &[u8]) -> (r: bool)
    ensures
        r ==> z@ == root(),
{
    let r = z.len() == 1 && z[0] == 0;
    proof {
        if r {
            assert(z@ =~= root());
        }
    }
    r
}

/// The status a strict ancestor's status gives `z`: unsigned if `z` is
/// below the ancestor's unsigned cut, else bogus.
fn inherit(p: Status, z: &[u8]) -> (s: Status)
    requires
        p matches Status::Unsigned(cut, u) ==> unsigned_ok(u@, anchors()) && u@.cut == cut@,
    ensures
        status_ok(s, z@),
{
    match p {
        Status::Unsigned(cut, u) => {
            let lz = lowered(z);
            proof {
                lemma_lowered(z@, lz@);
            }
            if is_sub_exec(&lz, &cut) {
                Status::Unsigned(cut, u)
            } else {
                Status::Bogus
            }
        },
        _ => Status::Bogus,
    }
}

/// The trusted keys of the root: its DNSKEY RRset, validated by a key the
/// configured anchors identify.
fn root_keys(roots: &Vec<Vec<u8>>, net: &Net, cache: &Shared, budget: &mut u32, vd: u32) -> (s: Status)
    requires
        addrs_ok(roots@),
        vd > 0,
    ensures
        status_ok(s, root()),
        *final(budget) <= *old(budget),
    decreases vd, 0nat, 1nat,
{
    let mut rootn: Vec<u8> = Vec::new();
    rootn.push(0);
    proof {
        assert(rootn@ =~= root());
    }
    let (krs, kraw) = match iterate(roots, net, cache, &rootn, TYPE_DNSKEY, budget, NS_DEPTH, vd - 1) {
        Step::Done(code, rs, _, raw) => {
            if code != RCODE_NOERROR {
                return Status::Bogus;
            }
            (rs, raw)
        },
        _ => {
            return Status::Bogus;
        },
    };
    if !rrset_ok_x(&krs) || krs[0].rtype != TYPE_DNSKEY || !eq_ci_exec(&krs[0].name, &rootn) {
        return Status::Bogus;
    }
    proof {
        assert(rrs(krs@)[0] == krs@[0]@);
    }
    let now = net.wall();
    let anc = anchors_x();
    let idx = sigs_for(&kraw.sigs, &rootn, TYPE_DNSKEY);
    let mut a: usize = 0;
    while a < anc.len()
        invariant
            views(anc@) == anchors(),
            *budget <= *old(budget),
            rootn@ == root(),
            rrset_ok(rrs(krs@)),
            rrs(krs@)[0].rtype == TYPE_DNSKEY,
            eq_ci(rrs(krs@)[0].name, root()),
            forall|i: int| 0 <= i < idx@.len() ==> #[trigger] idx@[i] < kraw.sigs@.len(),
        decreases anc@.len() - a,
    {
        let mut k: usize = 0;
        while k < krs.len()
            invariant
                views(anc@) == anchors(),
                *budget <= *old(budget),
                a < anc@.len(),
                rootn@ == root(),
                rrset_ok(rrs(krs@)),
                rrs(krs@)[0].rtype == TYPE_DNSKEY,
                eq_ci(rrs(krs@)[0].name, root()),
                forall|i: int| 0 <= i < idx@.len() ==> #[trigger] idx@[i] < kraw.sigs@.len(),
            decreases krs@.len() - k,
        {
            let kd = &krs[k].rdata;
            if ds_match_x(&anc[a], &rootn, kd) {
                let mut j: usize = 0;
                while j < idx.len()
                    invariant
                        views(anc@) == anchors(),
                        *budget <= *old(budget),
                        a < anc@.len(),
                        k < krs@.len(),
                        kd@ == krs@[k as int]@.rdata,
                        ds_matches(anc@[a as int]@, root(), kd@),
                        rootn@ == root(),
                        rrset_ok(rrs(krs@)),
                        rrs(krs@)[0].rtype == TYPE_DNSKEY,
                        eq_ci(rrs(krs@)[0].name, root()),
                        forall|i: int| 0 <= i < idx@.len() ==> #[trigger] idx@[i] < kraw.sigs@.len(),
                    decreases idx@.len() - j,
                {
                    let sig = &kraw.sigs[idx[j]];
                    if rrset_valid(&krs, sig, kd, &rootn, now) {
                        let ghost l = Link {
                            zone: root(),
                            keys: rrs(krs@),
                            ksk: kd@,
                            ksig: sig@,
                            ds: Seq::empty(),
                            dssig: sig@,
                            dskey: kd@,
                            now,
                            ds_now: now,
                        };
                        let ghost c = seq![l];
                        proof {
                            assert(rrs(krs@)[k as int] == krs@[k as int]@);
                            assert(has_key(l.keys, l.ksk));
                            assert(keys_selfsigned(l));
                            assert(views(anc@)[a as int] == anc@[a as int]@);
                            assert(anchored(l, anchors()));
                            assert(chain_ok(c, anchors()));
                            assert forall|i: int| 0 <= i < rrs(krs@).len() implies has_key(c.last().keys, #[trigger] rrs(krs@)[i].rdata) by {
                                assert(c.last().keys[i] == rrs(krs@)[i]);
                            }
                            lemma_eq_ci_refl(root());
                        }
                        let ttl = min_ttl(&krs);
                        let keep = copy_rrs(&krs);
                        proof {
                            assert forall|i: int| 0 <= i < rrs(keep@).len() implies has_key(c.last().keys, #[trigger] rrs(keep@)[i].rdata) by {
                                assert(rrs(keep@)[i] == rrs(krs@)[i]);
                            }
                        }
                        cache.insert(&rootn, KEYS, net.now(), ttl, Data::Keys(keep, Ghost(c)));
                        return Status::Trusted(krs, Ghost(c));
                    }
                    j = j + 1;
                }
            }
            k = k + 1;
        }
        a = a + 1;
    }
    Status::Bogus
}

/// What is known of zone `z`: from the cache, from the anchors (the root),
/// or from its DS RRset in the parent (or the proof there is none) and its
/// DNSKEY RRset. At most `budget` queries; `vd` bounds how many zones up
/// the chain may be followed.
#[verifier::rlimit(40)]
pub fn zone_status(roots: &Vec<Vec<u8>>, net: &Net, cache: &Shared, z: &[u8], budget: &mut u32, vd: u32) -> (s:
    Status)
    requires
        addrs_ok(roots@),
    ensures
        status_ok(s, z@),
        *final(budget) <= *old(budget),
    decreases vd, 0nat, 2nat,
{
    if vd == 0 {
        return Status::Bogus;
    }
    let now = net.now();
    match cache.lookup(z, KEYS, now) {
        Some(Hit { data: Data::Keys(k, c), left: _ }) => {
            return Status::Trusted(k, c);
        },
        Some(Hit { data: Data::Cut(cut, u), left: _ }) => {
            return Status::Unsigned(cut, u);
        },
        _ => {},
    }
    if is_root(z) {
        let s = root_keys(roots, net, cache, budget, vd);
        return s;
    }
    let wall = net.wall();
    let lz = lowered(z);
    proof {
        lemma_lowered(z@, lz@);
        lemma_eq_ci_refl(lz@);
    }
    // The DS RRset, or the proof it does not exist, from the parent.
    let (code, rs, raw) = match iterate(roots, net, cache, z, TYPE_DS, budget, NS_DEPTH, vd - 1) {
        Step::Done(code, rs, _, raw) => (code, rs, raw),
        _ => {
            return Status::Bogus;
        },
    };
    let s = if code == RCODE_NOERROR && rs.len() > 0 {
        ds_path(roots, net, cache, z, &lz, &rs, &raw, budget, vd, wall)
    } else {
        denial_path(roots, net, cache, z, &lz, &raw, budget, vd, wall)
    };
    match &s {
        Status::Unsigned(cut, u) => {
            let ghost uv = u@;
            proof {
                lemma_lower_ci(lz@, z@);
            }
            cache.insert(&lz, KEYS, now, MAX_TTL, Data::Cut(to_vec(cut), Ghost(u@)));
        },
        _ => {},
    }
    s
}

/// The status of `z` when the parent's servers have no signed answer:
/// `z` is unsigned only if the zone they serve is (and `z` is below its
/// unsigned cut).
fn via_server_zone(roots: &Vec<Vec<u8>>, net: &Net, cache: &Shared, z: &[u8], raw: &Raw, budget: &mut u32, vd: u32) -> (s: Status)
    requires
        addrs_ok(roots@),
        vd > 0,
    ensures
        status_ok(s, z@),
        *final(budget) <= *old(budget),
    decreases vd, 0nat, 0nat,
{
    if eq_ci_exec(&raw.zone, z) || !is_sub_exec(z, &raw.zone) {
        return Status::Bogus;
    }
    let p = zone_status(roots, net, cache, &raw.zone, budget, vd - 1);
    inherit(p, z)
}

/// The chain of trust `pc` (the parent's), extended by zone `z`: its DS
/// RRset `s` (validated with the parent's keys), whose `d`th DS identifies
/// key `kd` (the `k`th of the DNSKEY RRset `krs`), which signs `krs`.
proof fn lemma_extend_chain(
    pc: Seq<Link>,
    s: Signed,
    krs: Seq<RrS>,
    k: int,
    kd: Seq<u8>,
    sig: RrS,
    d: int,
    z: Seq<u8>,
    lz: Seq<u8>,
    wall: u32,
) -> (c: Seq<Link>)
    requires
        signed_ok(s, anchors()),
        s.chain == pc,
        s.rs.len() > 0,
        s.rs[0].rtype == TYPE_DS,
        eq_ci(z, s.rs[0].name),
        0 <= d < s.rs.len(),
        ds_matches(s.rs[d].rdata, z, kd),
        krs.len() > 0,
        krs[0].rtype == TYPE_DNSKEY,
        eq_ci(krs[0].name, z),
        0 <= k < krs.len(),
        krs[k].rdata == kd,
        rrset_signed(krs, sig, kd, z, wall),
        eq_ci(lz, z),
    ensures
        keys_ok(c, lz, krs),
        keys_ok(c, z, krs),
{
    let l = Link {
        zone: s.rs[0].name,
        keys: krs,
        ksk: kd,
        ksig: sig,
        ds: s.rs,
        dssig: s.sig,
        dskey: s.key,
        now: wall,
        ds_now: s.now,
    };
    let c = pc.push(l);
    let p = pc.last();
    assert(has_key(l.keys, l.ksk));
    lemma_signed_zone_ci(l.keys, l.ksig, l.ksk, z, l.zone, wall);
    lemma_eq_ci_trans(l.keys[0].name, z, l.zone);
    assert(keys_selfsigned(l));
    lemma_ds_ci(s.rs[d].rdata, z, l.zone, kd);
    assert(ds_matches(l.ds[d].rdata, l.zone, l.ksk));
    lemma_eq_ci_refl(l.zone);
    assert(delegated(p, l));
    assert forall|i: int| 0 <= i < c.len() implies keys_selfsigned(#[trigger] c[i]) by {
        if i < pc.len() {
            assert(c[i] == pc[i]);
        }
    }
    assert forall|i: int| 0 < i < c.len() implies delegated(c[i - 1], #[trigger] c[i]) by {
        if i < pc.len() {
            assert(c[i] == pc[i]);
            assert(c[i - 1] == pc[i - 1]);
        } else {
            assert(c[i - 1] == p);
        }
    }
    assert(c[0] == pc[0]);
    assert(chain_ok(c, anchors()));
    lemma_eq_ci_sym(z, l.zone);
    assert forall|i: int| 0 <= i < krs.len() implies has_key(c.last().keys, #[trigger] krs[i].rdata) by {
        assert(c.last().keys[i] == krs[i]);
    }
    lemma_eq_ci_trans(c.last().zone, z, lz);
    c
}

/// Some DS of `rs` names an algorithm and digest type both supported.
fn any_usable(rs: &Vec<Rr>) -> (r: bool)
    ensures
        !r ==> forall|j: int| 0 <= j < rs@.len() ==> !ds_usable(#[trigger] rrs(rs@)[j].rdata),
{
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            i <= rs@.len(),
            forall|j: int| 0 <= j < i ==> !ds_usable(#[trigger] rrs(rs@)[j].rdata),
        decreases rs@.len() - i,
    {
        let d = &rs[i].rdata;
        proof {
            assert(rrs(rs@)[i as int] == rs@[i as int]@);
        }
        if d.len() >= 4 && alg_supported_x(d[2]) && digest_supported_x(d[3]) {
            return true;
        }
        i = i + 1;
    }
    false
}

/// A validated DS RRset with no usable DS: the zone is unsigned.
proof fn lemma_unusable(s: Signed, pc: Seq<Link>, rs: Seq<RrS>, p: Seq<u8>, z: Seq<u8>, lz: Seq<u8>) -> (u: Unsigned)
    requires
        signed_ok(s, anchors()),
        s.rs == rs,
        rs.len() > 0,
        rs[0].rtype == TYPE_DS,
        eq_ci(s.zone(), p),
        eq_ci(z, s.rs[0].name),
        eq_ci(lz, z),
        lz == lower_seq(z),
        is_sub(lz, p),
        !eq_ci(lz, p),
        forall|j: int| 0 <= j < rs.len() ==> !ds_usable(#[trigger] rs[j].rdata),
    ensures
        cut_ok(u, lz, z),
{
    let u = Unsigned { cut: lz, parent: p, ns: Seq::empty(), ev: seq![s] };
    lemma_eq_ci_sym(s.zone(), p);
    lemma_eq_ci_sym(z, lz);
    lemma_eq_ci_sym(z, s.rs[0].name);
    lemma_eq_ci_trans(s.rs[0].name, z, lz);
    assert(u.ev[0] == s);
    assert(all_validated(u.ns, u.ev, anchors(), u.parent));
    assert(unsigned_ok(u, anchors()));
    lemma_is_sub_self(lz, lz);
    u
}

/// `z` has a DS RRset `rs` (answer records from the parent's servers).
#[verifier::rlimit(50)]
fn ds_path(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    z: &[u8],
    lz: &Vec<u8>,
    rs: &Vec<Rr>,
    raw: &Raw,
    budget: &mut u32,
    vd: u32,
    wall: u32,
) -> (s: Status)
    requires
        addrs_ok(roots@),
        vd > 0,
        lz@ == lower_seq(z@),
        eq_ci(lz@, z@),
    ensures
        status_ok(s, z@),
        *final(budget) <= *old(budget),
    decreases vd, 0nat, 1nat,
{
    if !rrset_ok_x(rs) || rs[0].rtype != TYPE_DS || !eq_ci_exec(&rs[0].name, z) {
        return Status::Bogus;
    }
    proof {
        assert(rrs(rs@)[0] == rs@[0]@);
    }
    let idx = sigs_for(&raw.sigs, &rs[0].name, TYPE_DS);
    if idx.len() == 0 {
        return via_server_zone(roots, net, cache, z, raw, budget, vd);
    }
    let p = match signer_of(&raw.sigs[idx[0]]) {
        Some(p) => p,
        None => {
            return Status::Bogus;
        },
    };
    if eq_ci_exec(&p, z) || !is_sub_exec(z, &p) {
        return Status::Bogus;
    }
    let (pk, pc) = match zone_status(roots, net, cache, &p, budget, vd - 1) {
        Status::Trusted(k, c) => (k, c),
        other => {
            return inherit(other, z);
        },
    };
    let (_, sd) = match validate_with(rs, &raw.sigs, &p, &pk, pc, wall) {
        Some(x) => x,
        None => {
            return Status::Bogus;
        },
    };
    let ghost s = sd@;
    proof {
        assert(s.rs[0] == rs@[0]@);
        lemma_eq_ci_sym(rs@[0]@.name, z@);
        lemma_eq_ci_trans(z@, rs@[0]@.name, s.rs[0].name);
    }
    // Any DS this resolver can use? If none, the zone is treated as
    // unsigned (RFC 4035 §5.2).
    if !any_usable(rs) {
        if !is_sub_exec(lz, &p) || eq_ci_exec(lz, &p) {
            return Status::Bogus;
        }
        let ghost mut u = Unsigned { cut: lz@, parent: p@, ns: Seq::empty(), ev: seq![s] };
        proof {
            u = lemma_unusable(s, pc@, rrs(rs@), p@, z@, lz@);
        }
        return Status::Unsigned(to_vec(lz), Ghost(u));
    }
    // The zone's DNSKEY RRset, from its own servers.
    let (krs, kraw) = match iterate(roots, net, cache, z, TYPE_DNSKEY, budget, NS_DEPTH, vd - 1) {
        Step::Done(code, krs, _, kraw) => {
            if code != RCODE_NOERROR {
                return Status::Bogus;
            }
            (krs, kraw)
        },
        _ => {
            return Status::Bogus;
        },
    };
    if !rrset_ok_x(&krs) || krs[0].rtype != TYPE_DNSKEY || !eq_ci_exec(&krs[0].name, z) {
        return Status::Bogus;
    }
    proof {
        assert(rrs(krs@)[0] == krs@[0]@);
    }
    match ds_keys(rs, Ghost(s), pc, &krs, &kraw.sigs, z, lz, wall) {
        Some(c) => {
            let ttl = min_ttl(&krs);
            let dttl = min_ttl(rs);
            let keep = copy_rrs(&krs);
            proof {
                assert forall|i: int| 0 <= i < rrs(keep@).len() implies has_key(c@.last().keys, #[trigger] rrs(keep@)[i].rdata) by {
                    assert(rrs(keep@)[i] == rrs(krs@)[i]);
                }
            }
            cache.insert(lz, KEYS, net.now(), if ttl < dttl { ttl } else { dttl }, Data::Keys(keep, c));
            Status::Trusted(krs, c)
        },
        None => Status::Bogus,
    }
}

/// The chain of trust to `z`, if a DS of `rs` (validated: `s`) identifies
/// a key of `krs` that signs `krs` (with an RRSIG of `ksigs`).
fn ds_keys(
    rs: &Vec<Rr>,
    sg: Ghost<Signed>,
    pc: Ghost<Seq<Link>>,
    krs: &Vec<Rr>,
    ksigs: &Vec<Rr>,
    z: &[u8],
    lz: &Vec<u8>,
    wall: u32,
) -> (r: Option<Ghost<Seq<Link>>>)
    requires
        rrset_ok(rrs(krs@)),
        rrs(krs@)[0].rtype == TYPE_DNSKEY,
        eq_ci(rrs(krs@)[0].name, z@),
        signed_ok(sg@, anchors()),
        sg@.rs == rrs(rs@),
        sg@.chain == pc@,
        eq_ci(z@, sg@.rs[0].name),
        sg@.rs.len() > 0,
        sg@.rs[0].rtype == TYPE_DS,
        lz@ == lower_seq(z@),
        eq_ci(lz@, z@),
    ensures
        r matches Some(c) ==> keys_ok(c@, lz@, rrs(krs@)) && keys_ok(c@, z@, rrs(krs@)),
{
    let ghost s = sg@;
    proof {
        assert(krs@.len() > 0);
        assert(rrs(krs@)[0] == krs@[0]@);
    }
    let kidx = sigs_for(ksigs, &krs[0].name, TYPE_DNSKEY);
    let mut d: usize = 0;
    while d < rs.len()
        invariant
            rrset_ok(rrs(krs@)),
            rrs(krs@)[0].rtype == TYPE_DNSKEY,
            eq_ci(rrs(krs@)[0].name, z@),
            signed_ok(s, anchors()),
            s.rs == rrs(rs@),
            s.chain == pc@,
            eq_ci(z@, s.rs[0].name),
            s.rs.len() > 0,
            s.rs[0].rtype == TYPE_DS,
            lz@ == lower_seq(z@),
            eq_ci(lz@, z@),
            forall|i: int| 0 <= i < kidx@.len() ==> #[trigger] kidx@[i] < ksigs@.len(),
        decreases rs@.len() - d,
    {
        let dd = &rs[d].rdata;
        let mut k: usize = 0;
        while k < krs.len()
            invariant
                d < rs@.len(),
                dd@ == rs@[d as int]@.rdata,
                rrset_ok(rrs(krs@)),
                rrs(krs@)[0].rtype == TYPE_DNSKEY,
                eq_ci(rrs(krs@)[0].name, z@),
                signed_ok(s, anchors()),
                s.rs == rrs(rs@),
                s.chain == pc@,
                eq_ci(z@, s.rs[0].name),
                s.rs.len() > 0,
                s.rs[0].rtype == TYPE_DS,
                lz@ == lower_seq(z@),
                eq_ci(lz@, z@),
                    forall|i: int| 0 <= i < kidx@.len() ==> #[trigger] kidx@[i] < ksigs@.len(),
            decreases krs@.len() - k,
        {
            let kd = &krs[k].rdata;
            if kd.len() >= 4 && dd.len() >= 4 && key_tag(kd) == u16_at_x(dd, 0) && ds_match_x(dd, z, kd) {
                let mut j: usize = 0;
                while j < kidx.len()
                    invariant
                        d < rs@.len(),
                        k < krs@.len(),
                        dd@ == rs@[d as int]@.rdata,
                        kd@ == krs@[k as int]@.rdata,
                        ds_matches(dd@, z@, kd@),
                        rrset_ok(rrs(krs@)),
                        rrs(krs@)[0].rtype == TYPE_DNSKEY,
                        eq_ci(rrs(krs@)[0].name, z@),
                        signed_ok(s, anchors()),
                        s.rs == rrs(rs@),
                        s.chain == pc@,
                        eq_ci(z@, s.rs[0].name),
                        s.rs.len() > 0,
                        s.rs[0].rtype == TYPE_DS,
                        lz@ == lower_seq(z@),
                        eq_ci(lz@, z@),
                                    forall|i: int| 0 <= i < kidx@.len() ==> #[trigger] kidx@[i] < ksigs@.len(),
                    decreases kidx@.len() - j,
                {
                    let sig = &ksigs[kidx[j]];
                    proof {
                        assert(rrs(krs@)[k as int] == krs@[k as int]@);
                        assert(rrs(rs@)[d as int] == rs@[d as int]@);
                    }
                    if rrset_valid(krs, sig, kd, z, wall) {
                        let ghost mut c: Seq<Link> = Seq::empty();
                        proof {
                            c = lemma_extend_chain(pc@, s, rrs(krs@), k as int, kd@, sig@, d as int, z@, lz@, wall);
                        }
                        return Some(Ghost(c));
                    }
                    j = j + 1;
                }
            }
            k = k + 1;
        }
        d = d + 1;
    }
    None
}


/// `z` has no DS according to the parent's servers: unsigned if signed
/// NSEC or NSEC3 records of the parent prove it is a delegation without
/// one, or if the parent is itself unsigned.
fn denial_path(
    roots: &Vec<Vec<u8>>,
    net: &Net,
    cache: &Shared,
    z: &[u8],
    lz: &Vec<u8>,
    raw: &Raw,
    budget: &mut u32,
    vd: u32,
    wall: u32,
) -> (s: Status)
    requires
        addrs_ok(roots@),
        vd > 0,
        lz@ == lower_seq(z@),
        eq_ci(lz@, z@),
    ensures
        status_ok(s, z@),
        *final(budget) <= *old(budget),
    decreases vd, 0nat, 1nat,
{
    let p = match ns_signer(&raw.ns, &raw.sigs) {
        Some(p) => p,
        None => {
            return via_server_zone(roots, net, cache, z, raw, budget, vd);
        },
    };
    if eq_ci_exec(&p, lz) || !is_sub_exec(lz, &p) {
        return Status::Bogus;
    }
    let (pk, pc) = match zone_status(roots, net, cache, &p, budget, vd - 1) {
        Status::Trusted(k, c) => (k, c),
        other => {
            return inherit(other, z);
        },
    };
    let (ns, ev) = validate_ns(&raw.ns, &raw.sigs, &p, &pk, pc, wall);
    if ns.len() == 0 || !find_unsigned(&ns, lz, &p) {
        return Status::Bogus;
    }
    let ghost u = Unsigned { cut: lz@, parent: p@, ns: rrs(ns@), ev: ev@ };
    proof {
        assert(unsigned_ok(u, anchors()));
        lemma_is_sub_self(lz@, lz@);
        lemma_eq_ci_refl(lz@);
    }
    Status::Unsigned(to_vec(lz), Ghost(u))
}

} // verus!

/// The configured trust anchors (trusted: set once, before the resolver
/// starts; see `TRUST.md`).
static ANCHORS: std::sync::OnceLock<Vec<Vec<u8>>> = std::sync::OnceLock::new();

/// Sets the trust anchors (DS RDATA for the root zone); empty turns
/// validation off. They are fixed for the life of the process (`anchors()`
/// is one value, and cached evidence depends on it): only the first call,
/// before any is read, has an effect. Returns whether the anchors in force
/// are `a`.
pub fn set_anchors(a: Vec<Vec<u8>>) -> bool {
    let want = a.clone();
    let _ = ANCHORS.set(a);
    ANCHORS.get() == Some(&want)
}

verus! {

#[verifier::external_body]
pub fn anchors_x() -> (r: &'static Vec<Vec<u8>>)
    ensures
        views(r@) == anchors(),
{
    ANCHORS.get_or_init(Vec::new)
}

/// Validation is on.
pub fn validating_x() -> (r: bool)
    ensures
        r == validating(),
{
    anchors_x().len() > 0
}

} // verus!
