//! Server authentication, proven against `spec_server_auth.rs`: the host
//! name check against the leaf's subjectAltName, name constraints, and the
//! path check (`check_server_chain`), which accepts only chains
//! `server_chain_ok` accepts.
use crate::client::*;
use crate::crypto::*;
#[cfg(verus_only)]
use crate::messages::chain_view;
use crate::spec_client::*;
use crate::spec_server_auth::*;
use alloc::vec::Vec;
#[cfg(verus_only)]
use verilith_x509::cert::{spec_alt_names, spec_basic_constraints, spec_ext_key_usage, spec_key_usage, spec_name_constraints};
#[cfg(verus_only)]
use verilith_x509::ext::nc_lists_wf;
use verilith_x509::iter::{SubtreeIter, GeneralNameIter};
use verilith_x509::spec::*;
use verilith_x509::{Certificate, GeneralName, Time};
use vstd::prelude::*;

verus! {

fn lower_x(c: u8) -> (r: u8)
    ensures
        r == lower(c),
{
    if 65 <= c && c <= 90 {
        c + 32
    } else {
        c
    }
}

/// `eq_ci(a[s..], b)`.
fn eq_ci_at(a: &[u8], s: usize, b: &[u8]) -> (r: bool)
    requires
        s <= a@.len(),
    ensures
        r == eq_ci(a@.skip(s as int), b@),
{
    if a.len() - s != b.len() {
        return false;
    }
    let al = a.len();
    let mut i: usize = 0;
    while i < b.len()
        invariant
            al == a@.len(),
            s <= a@.len(),
            a@.len() - s == b@.len(),
            s + b@.len() == a@.len(),
            i <= b@.len(),
            forall|j: int| 0 <= j < i ==> lower(#[trigger] a@.skip(s as int)[j]) == lower(b@[j]),
        decreases b@.len() - i,
    {
        if lower_x(a[s + i]) != lower_x(b[i]) {
            proof {
                assert(a@.skip(s as int)[i as int] == a@[s + i]);
            }
            return false;
        }
        proof {
            assert(a@.skip(s as int)[i as int] == a@[s + i]);
        }
        i = i + 1;
    }
    true
}

/// `has_byte(s[from..], c)`.
fn has_byte_from(s: &[u8], from: usize, c: u8) -> (r: bool)
    requires
        from <= s@.len(),
    ensures
        r == holds_byte(s@.skip(from as int), c),
{
    let mut i = from;
    while i < s.len()
        invariant
            from <= i <= s@.len(),
            forall|j: int| from <= j < i ==> s@[j] != c,
        decreases s@.len() - i,
    {
        if s[i] == c {
            proof {
                assert(s@.skip(from as int)[i - from] == c);
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        if holds_byte(s@.skip(from as int), c) {
            let j = choose|j: int| 0 <= j < s@.skip(from as int).len() && s@.skip(from as int)[j] == c;
            assert(s@[from + j] == c);
        }
    }
    false
}

/// `dns_matches(pat, host)`.
pub fn dns_matches_x(pat: &[u8], host: &[u8]) -> (r: bool)
    ensures
        r == dns_matches(pat@, host@),
{
    assert(pat@.skip(0) =~= pat@);
    assert(host@.skip(0) =~= host@);
    if eq_ci_at(pat, 0, host) {
        return true;
    }
    if pat.len() < 2 || pat[0] != 42 || pat[1] != 46 {
        return false;
    }
    let ghost suffix = pat@.skip(1);
    let sl = pat.len() - 1;
    proof {
        assert(pat@.skip(1).skip(1) =~= pat@.skip(2));
    }
    if !has_byte_from(pat, 2, 46) {
        return false;
    }
    if host.len() < sl + 1 {
        return false;
    }
    let k = host.len() - sl;
    proof {
        assert(tail(host@, sl as int) =~= host@.skip(k as int));
    }
    let sfx = vstd::slice::slice_subrange(pat, 1, pat.len());
    proof {
        assert(sfx@ =~= suffix);
    }
    if !eq_ci_at(host, k, sfx) {
        return false;
    }
    let mut i: usize = 0;
    while i < k
        invariant
            i <= k,
            k <= host@.len(),
            k == host@.len() - pat@.skip(1).len(),
            !eq_ci(pat@, host@),
            forall|j: int| 0 <= j < i ==> host@[j] != 46u8,
        decreases k - i,
    {
        if host[i] == 46 {
            proof {
                assert(host@[i as int] == 46u8);
            }
            return false;
        }
        i = i + 1;
    }
    true
}

/// `host_matches(c, host)`: a dNSName of the subjectAltName matches.
#[verifier::rlimit(40)]
pub fn host_matches_x(c: &Certificate, host: &[u8]) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r == host_matches(c@, host@),
{
    let mut it = match c.subject_alt_names() {
        None => return false,
        Some(i) => i,
    };
    let ghost all = it.remaining@;
    assert(all.skip(0) =~= all);
    loop
        invariant
            it.inv(),
            spec_alt_names(c@, CE_SUBJECT_ALT_NAME) == Some(all),
            all.len() >= it.remaining@.len(),
            it.remaining@ == all.skip(all.len() - it.remaining@.len()),
            forall|i: int|
                0 <= i < all.len() - it.remaining@.len() ==> !(#[trigger] all[i] matches SpecGeneralName::Dns(d)
                    && dns_matches(d, host@)),
        decreases it.remaining@.len(),
    {
        let ghost before = it.remaining@;
        let ghost done = all.len() - before.len();
        match it.next() {
            None => {
                proof {
                    assert(before.len() == 0);
                }
                return false;
            },
            Some(g) => {
                proof {
                    assert(all[done] == before[0]);
                    assert(it.remaining@ =~= all.skip(all.len() - it.remaining@.len()));
                }
                match g {
                    GeneralName::Dns(d) => {
                        if dns_matches_x(d, host) {
                            proof {
                                assert(all[done] == SpecGeneralName::Dns(d@));
                            }
                            return true;
                        }
                        proof {
                            assert(all[done] == SpecGeneralName::Dns(d@));
                        }
                    },
                    _ => {
                        proof {
                            assert(!(all[done] is Dns));
                        }
                    },
                }
            },
        }
    }
}

/// `dns_within(base, host)`.
pub fn dns_within_x(base: &[u8], host: &[u8]) -> (r: bool)
    ensures
        r == dns_within(base@, host@),
{
    let n = base.len();
    if n == 0 {
        return true;
    }
    assert(host@.skip(0) =~= host@);
    if base[0] == 46 {
        if host.len() <= n {
            return false;
        }
        proof {
            assert(tail(host@, n as int) =~= host@.skip(host.len() - n));
        }
        return eq_ci_at(host, host.len() - n, base);
    }
    if eq_ci_at(host, 0, base) {
        return true;
    }
    if host.len() <= n {
        return false;
    }
    if host[host.len() - n - 1] != 46 {
        return false;
    }
    proof {
        assert(tail(host@, n as int) =~= host@.skip(host.len() - n));
    }
    eq_ci_at(host, host.len() - n, base)
}

proof fn lemma_some_step(l: Seq<SpecGeneralName>, d: int, host: Seq<u8>)
    requires
        0 <= d < l.len(),
    ensures
        some_dns(l.take(d + 1)) == (some_dns(l.take(d)) || l[d] is Dns),
        some_within(l.take(d + 1), host) == (some_within(l.take(d), host) || (l[d] matches SpecGeneralName::Dns(x)
            && dns_within(x, host))),
{
    let a = l.take(d);
    let b = l.take(d + 1);
    assert forall|i: int| 0 <= i < d implies #[trigger] b[i] == a[i] by {}
    assert(b[d] == l[d]);
    if some_dns(a) {
        let i = choose|i: int| 0 <= i < a.len() && #[trigger] a[i] is Dns;
        assert(b[i] is Dns);
    }
    if l[d] is Dns {
        assert(b[d] is Dns);
    }
    if some_dns(b) {
        let i = choose|i: int| 0 <= i < b.len() && #[trigger] b[i] is Dns;
        if i < d {
            assert(a[i] is Dns);
        }
    }
    if some_within(a, host) {
        let i = choose|i: int| 0 <= i < a.len() && (#[trigger] a[i] matches SpecGeneralName::Dns(x) && dns_within(x, host));
        assert(b[i] == a[i]);
    }
    if l[d] matches SpecGeneralName::Dns(x) && dns_within(x, host) {
        assert(b[d] == l[d]);
    }
    if some_within(b, host) {
        let i = choose|i: int| 0 <= i < b.len() && (#[trigger] b[i] matches SpecGeneralName::Dns(x) && dns_within(x, host));
        if i < d {
            assert(a[i] == b[i]);
        }
    }
}

/// Walks a GeneralSubtrees list: whether it has a dNSName subtree, and
/// whether one holds `host`.
fn scan_subtrees(l: &[u8], host: &[u8]) -> (r: (bool, bool))
    requires
        parse_subtrees(l@) is Some,
    ensures
        r.0 == some_dns(parse_subtrees(l@).unwrap()),
        r.1 == some_within(parse_subtrees(l@).unwrap(), host@),
{
    let mut it = SubtreeIter::new(l);
    let ghost all = it.remaining@;
    assert(all.skip(0) =~= all);
    assert(all.take(0) =~= Seq::<SpecGeneralName>::empty());
    let mut any = false;
    let mut hit = false;
    loop
        invariant
            it.inv(),
            all == parse_subtrees(l@).unwrap(),
            all.len() >= it.remaining@.len(),
            it.remaining@ == all.skip(all.len() - it.remaining@.len()),
            any == some_dns(all.take(all.len() - it.remaining@.len())),
            hit == some_within(all.take(all.len() - it.remaining@.len()), host@),
        decreases it.remaining@.len(),
    {
        let ghost before = it.remaining@;
        let ghost done = all.len() - before.len();
        match it.next() {
            None => {
                proof {
                    assert(before.len() == 0);
                    assert(all.take(all.len() as int) =~= all);
                }
                return (any, hit);
            },
            Some(g) => {
                proof {
                    assert(all[done] == before[0]);
                    assert(it.remaining@ =~= all.skip(all.len() - it.remaining@.len()));
                    lemma_some_step(all, done, host@);
                }
                match g {
                    GeneralName::Dns(d) => {
                        let w = dns_within_x(d, host);
                        proof {
                            assert(all[done] == SpecGeneralName::Dns(d@));
                        }
                        any = true;
                        hit = hit || w;
                    },
                    _ => {
                        proof {
                            assert(!(all[done] is Dns));
                        }
                    },
                }
            },
        }
    }
}

/// `nc_allows(c, host)`.
pub fn nc_allows_x(c: &Certificate, host: &[u8]) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r == nc_allows(c@, host@),
{
    let nc = match c.name_constraints() {
        None => return true,
        Some(n) => n,
    };
    proof {
        assert(nc_lists_wf(nc));
    }
    match nc.permitted {
        Some(p) => {
            let (any, hit) = scan_subtrees(p, host);
            if any && !hit {
                return false;
            }
        },
        None => {},
    }
    match nc.excluded {
        Some(e) => {
            let (_, hit) = scan_subtrees(e, host);
            if hit {
                return false;
            }
        },
        None => {},
    }
    true
}

fn known_critical_srv_x(oid: &[u8]) -> (r: bool)
    ensures
        r ==> known_critical_srv(oid@),
{
    if oid.len() == 3 && oid[0] == 0x55 && oid[1] == 0x1d && oid[2] == 30 {
        proof {
            assert(oid@ =~= oid_ce(30));
        }
        return true;
    }
    known_critical_x(oid)
}

/// Every critical extension of `c` is one the server path check processes.
fn critical_known_srv_x(c: &Certificate) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r ==> critical_known_srv(c@),
{
    let mut it = c.extensions();
    let ghost all = c@.tbs.extensions;
    assert(all.skip(0) =~= all);
    loop
        invariant
            it.inv(),
            all == c@.tbs.extensions,
            all.len() >= it.remaining@.len(),
            it.remaining@ == all.skip(all.len() - it.remaining@.len()),
            forall|i: int|
                0 <= i < all.len() - it.remaining@.len() && (#[trigger] all[i]).critical ==> known_critical_srv(
                    all[i].oid,
                ),
        decreases it.remaining@.len(),
    {
        let ghost before = it.remaining@;
        let ghost done = all.len() - before.len();
        match it.next() {
            None => {
                proof {
                    assert(before.len() == 0);
                }
                return true;
            },
            Some(e) => {
                proof {
                    assert(all[done] == before[0]);
                    assert(it.remaining@ =~= all.skip(all.len() - it.remaining@.len()));
                }
                if e.critical && !known_critical_srv_x(e.oid) {
                    return false;
                }
            },
        }
    }
}

/// The OID contents `oid` is id-kp-serverAuth or anyExtendedKeyUsage.
fn server_purpose_x(oid: &[u8]) -> (r: bool)
    ensures
        r == (oid@ == oid_server_auth() || oid@ == oid_any_eku()),
{
    let sa: [u8; 8] = [0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01];
    let any: [u8; 4] = [0x55, 0x1d, 0x25, 0x00];
    proof {
        assert(sa@ =~= oid_server_auth());
        assert(any@ =~= oid_any_eku());
    }
    eq_bytes(oid, &sa) || eq_bytes(oid, &any)
}

/// extendedKeyUsage, if present, allows server authentication.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn eku_server_x(c: &Certificate) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r == eku_server(c@),
{
    let mut it = match c.ext_key_usage() {
        None => return true,
        Some(i) => i,
    };
    let ghost all = it.remaining@;
    assert(all.skip(0) =~= all);
    loop
        invariant
            it.inv(),
            spec_ext_key_usage(c@) == Some(all),
            all.len() >= it.remaining@.len(),
            it.remaining@ == all.skip(all.len() - it.remaining@.len()),
            forall|i: int|
                0 <= i < all.len() - it.remaining@.len() ==> #[trigger] all[i] != oid_server_auth() && all[i]
                    != oid_any_eku(),
        decreases it.remaining@.len(),
    {
        let ghost before = it.remaining@;
        let ghost done = all.len() - before.len();
        match it.next() {
            None => {
                proof {
                    assert(before.len() == 0);
                    assert(!all.contains(oid_server_auth()));
                    assert(!all.contains(oid_any_eku()));
                }
                return false;
            },
            Some(o) => {
                proof {
                    assert(all[done] == before[0]);
                    assert(it.remaining@ =~= all.skip(all.len() - it.remaining@.len()));
                }
                if server_purpose_x(o) {
                    proof {
                        if o@ == oid_server_auth() {
                            assert(all[done] == oid_server_auth());
                        } else {
                            assert(all[done] == oid_any_eku());
                        }
                    }
                    return true;
                }
            },
        }
    }
}

/// `srv_leaf_ok`: the leaf may authenticate a server named `host` at `now`.
pub fn srv_leaf_ok_x(c: &Certificate, now: &Time, host: &[u8]) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r ==> srv_leaf_ok(c@, now@, host@),
{
    reveal(srv_leaf_ok);
    if !time_le_x(&c.tbs.not_before, now) || !time_le_x(now, &c.tbs.not_after) {
        return false;
    }
    if !critical_known_srv_x(c) {
        return false;
    }
    match c.basic_constraints() {
        Some(b) => {
            if b.ca {
                return false;
            }
        },
        None => {},
    }
    match c.key_usage() {
        Some(m) => {
            if m % 2 != 1 {
                return false;
            }
        },
        None => {},
    }
    eku_server_x(c) && host_matches_x(c, host)
}

/// `srv_ca_ok`: `c` may issue certificates with `below` intermediates
/// under it, for `host`, at `now`.
pub fn srv_ca_ok_x(c: &Certificate, now: &Time, below: usize, host: &[u8]) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r ==> srv_ca_ok(c@, now@, below as int, host@),
{
    reveal(srv_ca_ok);
    if !time_le_x(&c.tbs.not_before, now) || !time_le_x(now, &c.tbs.not_after) {
        return false;
    }
    if !critical_known_srv_x(c) {
        return false;
    }
    match c.basic_constraints() {
        Some(b) => {
            if !b.ca {
                return false;
            }
            match b.path_len {
                Some(n) => {
                    if below as u64 > n {
                        return false;
                    }
                },
                None => {},
            }
        },
        None => return false,
    }
    match c.key_usage() {
        Some(m) => {
            if (m / 32) % 2 != 1 {
                return false;
            }
        },
        None => {},
    }
    eku_server_x(c) && nc_allows_x(c, host)
}

/// `chain[0..=i]` is a server path so far.
#[verifier::opaque]
pub open spec fn srv_prefix_ok(chain: Seq<Seq<u8>>, i: int, now: SpecTime, host: Seq<u8>) -> bool {
    &&& forall|t: int| 0 <= t <= i ==> parses(#[trigger] chain[t])
    &&& srv_leaf_ok(cert_of(chain[0]), now, host)
    &&& forall|t: int| 1 <= t <= i ==> srv_ca_ok(cert_of(#[trigger] chain[t]), now, t - 1, host)
    &&& forall|t: int| 0 <= t < i ==> issued(cert_of(#[trigger] chain[t]), cert_of(chain[t + 1]))
}

proof fn lemma_srv_prefix_start(chain: Seq<Seq<u8>>, now: SpecTime, host: Seq<u8>)
    requires
        chain.len() > 0,
        parses(chain[0]),
        srv_leaf_ok(cert_of(chain[0]), now, host),
    ensures
        srv_prefix_ok(chain, 0, now, host),
{
    reveal(srv_prefix_ok);
}

proof fn lemma_srv_prefix_extend(chain: Seq<Seq<u8>>, i: int, now: SpecTime, host: Seq<u8>)
    requires
        0 <= i,
        i + 1 < chain.len(),
        srv_prefix_ok(chain, i, now, host),
        parses(chain[i + 1]),
        issued(cert_of(chain[i]), cert_of(chain[i + 1])),
        srv_ca_ok(cert_of(chain[i + 1]), now, i, host),
    ensures
        srv_prefix_ok(chain, i + 1, now, host),
{
    reveal(srv_prefix_ok);
    assert forall|t: int| 1 <= t <= i + 1 implies srv_ca_ok(cert_of(#[trigger] chain[t]), now, t - 1, host) by {
        if t <= i {
        }
    }
    assert forall|t: int| 0 <= t < i + 1 implies issued(cert_of(#[trigger] chain[t]), cert_of(chain[t + 1])) by {
        if t < i {
        }
    }
}

proof fn lemma_srv_prefix_done(chain: Seq<Seq<u8>>, i: int, roots: Seq<Seq<u8>>, j: int, now: SpecTime, host: Seq<u8>)
    requires
        0 <= i < chain.len(),
        i < MAX_DEPTH,
        0 <= j < roots.len(),
        srv_prefix_ok(chain, i, now, host),
        parses(roots[j]),
        issued(cert_of(chain[i]), cert_of(roots[j])),
    ensures
        server_chain_ok(chain, roots, now, host),
{
    reveal(srv_prefix_ok);
    assert(srv_path_ok(chain, i, roots[j], now, host));
}

/// The server path check: `Ok` only if `chain` (leaf first) leads, as
/// sent, to one of `roots` at `now`, and names `host`
/// (`server_chain_ok`). The alert otherwise: bad_certificate for a
/// certificate that does not parse, is not valid now, does not name the
/// host, or may not stand where it is; unknown_ca if the chain reaches no
/// trust anchor.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn check_server_chain<P: Provider>(prov: &P, chain: &Vec<Vec<u8>>, roots: &Vec<Vec<u8>>, now: &Time, host: &[u8]) -> (r: Result<(), u8>)
    requires
        chain@.len() > 0,
    ensures
        r is Ok ==> server_chain_ok(chain_view(chain@), chain_view(roots@), now@, host@),
{
    let ghost cv = chain_view(chain@);
    let ghost rv = chain_view(roots@);
    let first = match verilith_x509::parse(chain[0].as_slice()) {
        Some(c) => c,
        None => return Err(BAD_CERTIFICATE),
    };
    if !srv_leaf_ok_x(&first, now, host) {
        return Err(BAD_CERTIFICATE);
    }
    proof {
        assert(cv[0] == chain@[0]@);
        lemma_cert_of(cv[0], first@);
        lemma_srv_prefix_start(cv, now@, host@);
    }
    let mut cur = first;
    let mut i: usize = 0;
    while i < MAX_DEPTH
        invariant
            i < MAX_DEPTH,
            i < chain@.len(),
            cv == chain_view(chain@),
            rv == chain_view(roots@),
            cur.tbs.wf(),
            parses(cv[i as int]) && cert_of(cv[i as int]) == cur@,
            srv_prefix_ok(cv, i as int, now@, host@),
        decreases MAX_DEPTH - i,
    {
        match find_root(prov, &cur, roots) {
            Some(j) => {
                proof {
                    assert(rv[j as int] == roots@[j as int]@);
                    lemma_srv_prefix_done(cv, i as int, rv, j as int, now@, host@);
                }
                return Ok(());
            },
            None => {},
        }
        if i + 1 >= chain.len() || i + 1 >= MAX_DEPTH {
            return Err(UNKNOWN_CA);
        }
        let next = match verilith_x509::parse(chain[i + 1].as_slice()) {
            Some(c) => c,
            None => return Err(BAD_CERTIFICATE),
        };
        if !issued_x(prov, &cur, &next) {
            return Err(BAD_CERTIFICATE);
        }
        if !srv_ca_ok_x(&next, now, i, host) {
            return Err(BAD_CERTIFICATE);
        }
        proof {
            assert(cv[i + 1] == chain@[i + 1]@);
            lemma_cert_of(cv[i + 1], next@);
            lemma_srv_prefix_extend(cv, i as int, now@, host@);
        }
        cur = next;
        i = i + 1;
    }
    Err(UNKNOWN_CA)
}

} // verus!
