//! Client authentication, proven against `spec_client.rs`: the
//! CertificateRequest the server sends, the client's Certificate parsed
//! exactly as `parse_client_certificate` says, the content its
//! CertificateVerify signs, and the path check (`check_chain`), which
//! accepts only chains `chain_ok` accepts.
use crate::crypto::*;
use crate::messages::*;
use crate::keys::*;
use crate::spec::*;
use crate::spec_client::*;
use crate::spec_server::*;
use alloc::vec::Vec;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
#[cfg(verus_only)]
use verilith_x509::cert::{spec_basic_constraints, spec_ext_key_usage, spec_key_usage};
use verilith_x509::iter::{ExtensionIter, OidIter};
use verilith_x509::spec::*;
use verilith_x509::{Certificate, Time};
use vstd::prelude::*;

verus! {

proof fn lemma_scheme_list_push(s: Seq<u16>, x: u16)
    ensures
        scheme_list(s.push(x)) == scheme_list(s) + be2(x as nat),
{
    assert(s.push(x).drop_last() =~= s);
}

/// Appends a CertificateRequest asking for `sigs` (§4.3.2).
pub fn certificate_request_x(out: &mut Vec<u8>, sigs: &[u16])
    requires
        0 < sigs@.len() <= 1000,
    ensures
        final(out)@ == old(out)@ + certificate_request(sigs@),
        certificate_request(sigs@).len() == 2 * sigs@.len() + 13,
{
    let n = sigs.len();
    let ghost o = out@;
    put1(out, 13);
    put3(out, 2 * n + 9);
    put1(out, 0);
    put2(out, 2 * n + 6);
    put2(out, 13);
    put2(out, 2 * n + 2);
    put2(out, 2 * n);
    let ghost o1 = out@;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == sigs@.len(),
            n <= 1000,
            out@ == o1 + scheme_list(sigs@.take(i as int)),
        decreases n - i,
    {
        proof {
            lemma_scheme_list_push(sigs@.take(i as int), sigs@[i as int]);
            assert(sigs@.take(i as int).push(sigs@[i as int]) =~= sigs@.take(i as int + 1));
        }
        put2(out, sigs[i] as usize);
        i = i + 1;
    }
    proof {
        assert(sigs@.take(n as int) =~= sigs@);
        let e = ext(13, be2(2 * sigs@.len()) + scheme_list(sigs@));
        assert(scheme_list(sigs@).len() == 2 * n) by {
            lemma_scheme_list_len(sigs@);
        }
        assert(e.len() == 2 * n + 6);
        assert(out@ =~= o + hs_msg(13, seq![0u8] + be2(e.len()) + e));
    }
}

proof fn lemma_scheme_list_len(s: Seq<u16>)
    ensures
        scheme_list(s).len() == 2 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_scheme_list_len(s.drop_last());
    }
}

/// Appends what a client's CertificateVerify signs, for transcript hash
/// `th`.
pub fn client_cv_content_x(out: &mut Vec<u8>, th: &Secret)
    requires
        th.wf(),
    ensures
        final(out)@ == old(out)@ + client_cv_content(th@),
{
    let label: [u8; 33] = [
        84, 76, 83, 32, 49, 46, 51, 44, 32, 99, 108, 105, 101, 110, 116, 32, 67, 101, 114, 116,
        105, 102, 105, 99, 97, 116, 101, 86, 101, 114, 105, 102, 121,
    ];
    let ghost o = out@;
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            out@ == o + Seq::new(i as nat, |j: int| 0x20u8),
        decreases 64 - i,
    {
        out.push(0x20);
        assert(out@ =~= o + Seq::new(i as nat + 1, |j: int| 0x20u8));
        i = i + 1;
    }
    put(out, &label);
    put1(out, 0);
    put(out, th.as_slice());
    reveal(client_cv_content);
    assert(label@ =~= client_cv_label());
    assert(final(out)@ =~= old(out)@ + client_cv_content(th@));
}

/// The certificates of `l`, then `cert_list(rest)`.
pub open spec fn then_list(l: Seq<Seq<u8>>, rest: Result<Seq<Seq<u8>>, u8>) -> Result<Seq<Seq<u8>>, u8> {
    match rest {
        Ok(t) => Ok(l + t),
        Err(a) => Err(a),
    }
}

/// The certificates of a client's Certificate message body
/// (`parse_client_certificate`), or the alert.
#[verifier::rlimit(40)]
pub fn parse_client_certificate_x(body: &[u8]) -> (r: Result<Vec<Vec<u8>>, u8>)
    ensures
        match r {
            Ok(v) => parse_client_certificate(body@) == Ok::<Seq<Seq<u8>>, u8>(chain_view(v@)),
            Err(a) => parse_client_certificate(body@) == Err::<Seq<Seq<u8>>, u8>(a),
        },
{
    let n = body.len();
    if n < 1 || n - 1 < body[0] as usize + 3 {
        return Err(DECODE_ERROR_ALERT);
    }
    let c = body[0] as usize;
    let l = ((body[1 + c] as usize) * 256 + body[2 + c] as usize) * 256 + body[3 + c] as usize;
    if l != n - (1 + c + 3) {
        return Err(DECODE_ERROR_ALERT);
    }
    if c != 0 {
        return Err(ILLEGAL_PARAMETER_ALERT);
    }
    let ghost b0 = body@.skip(4);
    assert(parse_client_certificate(body@) == cert_list(b0));
    let mut v: Vec<Vec<u8>> = Vec::new();
    let mut off: usize = 4;
    while off < n
        invariant
            4 <= off <= n,
            n == body@.len(),
            b0 == body@.skip(4),
            parse_client_certificate(body@) == cert_list(b0),
            cert_list(b0) == then_list(chain_view(v@), cert_list(body@.skip(off as int))),
        decreases n - off,
    {
        let ghost b = body@.skip(off as int);
        assert(b.len() == n - off);
        if n - off < 3 {
            proof {
                assert(cert_list(b) == Err::<Seq<Seq<u8>>, u8>(DECODE_ERROR_ALERT));
            }
            return Err(DECODE_ERROR_ALERT);
        }
        let k = ((body[off] as usize) * 256 + body[off + 1] as usize) * 256 + body[off + 2] as usize;
        proof {
            assert(k == be24(b, 0));
        }
        if k == 0 || n - off < 3 + k + 2 {
            proof {
                assert(cert_list(b) == Err::<Seq<Seq<u8>>, u8>(DECODE_ERROR_ALERT));
            }
            return Err(DECODE_ERROR_ALERT);
        }
        let e = (body[off + 3 + k] as usize) * 256 + body[off + 4 + k] as usize;
        proof {
            assert(e == be16(b, 3 + k as int));
        }
        if n - off < 3 + k + 2 + e {
            proof {
                assert(cert_list(b) == Err::<Seq<Seq<u8>>, u8>(DECODE_ERROR_ALERT));
            }
            return Err(DECODE_ERROR_ALERT);
        }
        if e != 0 {
            proof {
                assert(cert_list(b) == Err::<Seq<Seq<u8>>, u8>(UNSUPPORTED_EXTENSION));
            }
            return Err(UNSUPPORTED_EXTENSION);
        }
        let cert = vstd::slice::slice_subrange(body, off + 3, off + 3 + k);
        let mut cv: Vec<u8> = Vec::new();
        put(&mut cv, cert);
        let ghost v0 = v@;
        v.push(cv);
        proof {
            assert(cv@ =~= b.subrange(3, 3 + k as int));
            assert(b.skip(3 + k as int + 2) =~= body@.skip(off + 3 + k + 2));
            assert(chain_view(v@) =~= chain_view(v0) + seq![cv@]);
            match cert_list(b.skip(3 + k as int + 2)) {
                Ok(t) => {
                    assert(chain_view(v0) + (seq![cv@] + t) =~= chain_view(v0) + seq![cv@] + t);
                },
                Err(_) => {},
            }
        }
        off = off + 3 + k + 2;
    }
    proof {
        assert(body@.skip(n as int) =~= Seq::<u8>::empty());
        assert(chain_view(v@) + Seq::<Seq<u8>>::empty() =~= chain_view(v@));
    }
    Ok(v)
}

/// `a` is no later than `b`.
fn time_le_x(a: &Time, b: &Time) -> (r: bool)
    ensures
        r == time_le(a@, b@),
{
    if a.year != b.year {
        a.year < b.year
    } else if a.month != b.month {
        a.month < b.month
    } else if a.day != b.day {
        a.day < b.day
    } else if a.hour != b.hour {
        a.hour < b.hour
    } else if a.minute != b.minute {
        a.minute < b.minute
    } else {
        a.second <= b.second
    }
}

fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
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

/// Whether OID contents `oid` is one of the critical extensions the path
/// check processes.
fn known_critical_x(oid: &[u8]) -> (r: bool)
    ensures
        r == known_critical(oid@),
{
    if oid.len() != 3 || oid[0] != 0x55 || oid[1] != 0x1d {
        proof {
            if oid@.len() == 3 {
                assert(oid@ != oid_ce(15) && oid@ != oid_ce(17) && oid@ != oid_ce(19) && oid@ != oid_ce(37)) by {
                    assert(oid_ce(15)[0] == 0x55 && oid_ce(15)[1] == 0x1d);
                    assert(oid_ce(17)[0] == 0x55 && oid_ce(17)[1] == 0x1d);
                    assert(oid_ce(19)[0] == 0x55 && oid_ce(19)[1] == 0x1d);
                    assert(oid_ce(37)[0] == 0x55 && oid_ce(37)[1] == 0x1d);
                }
            }
        }
        return false;
    }
    let x = oid[2];
    proof {
        assert(oid@ =~= oid_ce(x));
        assert(oid_ce(x) == oid_ce(15) ==> x == 15) by {
            assert(oid_ce(x)[2] == x);
            assert(oid_ce(15)[2] == 15);
        }
        assert(oid_ce(x) == oid_ce(17) ==> x == 17) by {
            assert(oid_ce(x)[2] == x);
            assert(oid_ce(17)[2] == 17);
        }
        assert(oid_ce(x) == oid_ce(19) ==> x == 19) by {
            assert(oid_ce(x)[2] == x);
            assert(oid_ce(19)[2] == 19);
        }
        assert(oid_ce(x) == oid_ce(37) ==> x == 37) by {
            assert(oid_ce(x)[2] == x);
            assert(oid_ce(37)[2] == 37);
        }
    }
    x == 15 || x == 17 || x == 19 || x == 37
}

/// Every critical extension of `c` is one the path check processes.
fn critical_known_x(c: &Certificate) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r ==> critical_known(c@),
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
                0 <= i < all.len() - it.remaining@.len() && (#[trigger] all[i]).critical ==> known_critical(all[i].oid),
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
                if e.critical && !known_critical_x(e.oid) {
                    return false;
                }
            },
        }
    }
}

/// The OID contents `oid` is id-kp-clientAuth or anyExtendedKeyUsage.
fn client_purpose_x(oid: &[u8]) -> (r: bool)
    ensures
        r == (oid@ == oid_client_auth() || oid@ == oid_any_eku()),
{
    let ca: [u8; 8] = [0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x02];
    let any: [u8; 4] = [0x55, 0x1d, 0x25, 0x00];
    proof {
        assert(ca@ =~= oid_client_auth());
        assert(any@ =~= oid_any_eku());
    }
    eq_bytes(oid, &ca) || eq_bytes(oid, &any)
}

/// extendedKeyUsage, if present, allows client authentication.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn eku_client_x(c: &Certificate) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r == eku_client(c@),
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
                0 <= i < all.len() - it.remaining@.len() ==> #[trigger] all[i] != oid_client_auth() && all[i]
                    != oid_any_eku(),
        decreases it.remaining@.len(),
    {
        let ghost before = it.remaining@;
        let ghost done = all.len() - before.len();
        match it.next() {
            None => {
                proof {
                    assert(before.len() == 0);
                    assert(!all.contains(oid_client_auth()));
                    assert(!all.contains(oid_any_eku()));
                }
                return false;
            },
            Some(o) => {
                proof {
                    assert(all[done] == before[0]);
                    assert(it.remaining@ =~= all.skip(all.len() - it.remaining@.len()));
                }
                if client_purpose_x(o) {
                    proof {
                        if o@ == oid_client_auth() {
                            assert(all[done] == oid_client_auth());
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

/// `leaf_ok`: the leaf may authenticate a client at `now`.
pub fn leaf_ok_x(c: &Certificate, now: &Time) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r ==> leaf_ok(c@, now@),
{
    reveal(leaf_ok);
    if !time_le_x(&c.tbs.not_before, now) || !time_le_x(now, &c.tbs.not_after) {
        return false;
    }
    if !critical_known_x(c) {
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
    eku_client_x(c)
}

/// `ca_ok`: `c` may issue certificates with `below` intermediates under
/// it, at `now`.
pub fn ca_ok_x(c: &Certificate, now: &Time, below: usize) -> (r: bool)
    requires
        c.tbs.wf(),
    ensures
        r ==> ca_ok(c@, now@, below as int),
{
    reveal(ca_ok);
    if !time_le_x(&c.tbs.not_before, now) || !time_le_x(now, &c.tbs.not_after) {
        return false;
    }
    if !critical_known_x(c) {
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
    eku_client_x(c)
}

/// `issued(child, parent)`, the names compared as DER bytes (equal bytes
/// are equal names).
fn issued_x<P: Provider>(prov: &P, child: &Certificate, parent: &Certificate) -> (r: bool)
    requires
        child.tbs.wf(),
        parent.tbs.wf(),
    ensures
        r ==> issued(child@, parent@),
{
    reveal(issued);
    if !eq_bytes(child.tbs.issuer.raw, parent.tbs.subject.raw) {
        return false;
    }
    prov.verify_cert_sig(&child.tbs.signature, &parent.tbs.spki, child.tbs_der, child.signature)
}

/// The trust anchor in `roots` that issued `c`, if any.
fn find_root<P: Provider>(prov: &P, c: &Certificate, roots: &Vec<Vec<u8>>) -> (r: Option<usize>)
    requires
        c.tbs.wf(),
    ensures
        r matches Some(j) ==> j < roots@.len() && parses(roots@[j as int]@)
            && issued(c@, cert_of(roots@[j as int]@)),
{
    let mut j: usize = 0;
    while j < roots.len()
        invariant
            j <= roots@.len(),
            c.tbs.wf(),
        decreases roots@.len() - j,
    {
        match verilith_x509::parse(roots[j].as_slice()) {
            Some(rc) => {
                if issued_x(prov, c, &rc) {
                    proof {
                        lemma_cert_of(roots@[j as int]@, rc@);
                    }
                    return Some(j);
                }
            },
            None => {},
        }
        j = j + 1;
    }
    None
}

/// `chain[0..=i]` is a path so far: each certificate parses, the leaf
/// and each intermediate may stand where they are, and each was issued by
/// the next.
#[verifier::opaque]
pub open spec fn prefix_ok(chain: Seq<Seq<u8>>, i: int, now: SpecTime) -> bool {
    &&& forall|t: int| 0 <= t <= i ==> parses(#[trigger] chain[t])
    &&& leaf_ok(cert_of(chain[0]), now)
    &&& forall|t: int| 1 <= t <= i ==> ca_ok(cert_of(#[trigger] chain[t]), now, t - 1)
    &&& forall|t: int| 0 <= t < i ==> issued(cert_of(#[trigger] chain[t]), cert_of(chain[t + 1]))
}

/// What `verilith_x509::parse` gave is `cert_of`.
pub proof fn lemma_cert_of(der: Seq<u8>, c: SpecCertificate)
    requires
        parse_certificate(der) == Some(c),
    ensures
        parses(der),
        cert_of(der) == c,
{
    reveal(parses);
    reveal(cert_of);
}

proof fn lemma_prefix_start(chain: Seq<Seq<u8>>, now: SpecTime)
    requires
        chain.len() > 0,
        parses(chain[0]),
        leaf_ok(cert_of(chain[0]), now),
    ensures
        prefix_ok(chain, 0, now),
{
    reveal(prefix_ok);
}

proof fn lemma_prefix_extend(chain: Seq<Seq<u8>>, i: int, now: SpecTime)
    requires
        0 <= i,
        i + 1 < chain.len(),
        prefix_ok(chain, i, now),
        parses(chain[i + 1]),
        issued(cert_of(chain[i]), cert_of(chain[i + 1])),
        ca_ok(cert_of(chain[i + 1]), now, i),
    ensures
        prefix_ok(chain, i + 1, now),
{
    reveal(prefix_ok);
    assert forall|t: int| 1 <= t <= i + 1 implies ca_ok(cert_of(#[trigger] chain[t]), now, t - 1) by {
        if t <= i {
        }
    }
    assert forall|t: int| 0 <= t < i + 1 implies issued(cert_of(#[trigger] chain[t]), cert_of(chain[t + 1])) by {
        if t < i {
        }
    }
}

proof fn lemma_prefix_done(chain: Seq<Seq<u8>>, i: int, roots: Seq<Seq<u8>>, j: int, now: SpecTime)
    requires
        0 <= i < chain.len(),
        i < MAX_DEPTH,
        0 <= j < roots.len(),
        prefix_ok(chain, i, now),
        parses(roots[j]),
        issued(cert_of(chain[i]), cert_of(roots[j])),
    ensures
        chain_ok(chain, roots, now),
{
    reveal(prefix_ok);
    assert(path_ok(chain, i, roots[j], now));
}

/// The path check: `Ok` only if `chain` (leaf first) leads, as sent, to
/// one of `roots` at `now` (`chain_ok`). The alert otherwise: bad_certificate
/// for a certificate that does not parse, is not valid now, or may not
/// stand where it is; unknown_ca if the chain reaches no trust anchor.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn check_chain<P: Provider>(prov: &P, chain: &Vec<Vec<u8>>, roots: &Vec<Vec<u8>>, now: &Time) -> (r: Result<(), u8>)
    requires
        chain@.len() > 0,
    ensures
        r is Ok ==> chain_ok(chain_view(chain@), chain_view(roots@), now@),
{
    let ghost cv = chain_view(chain@);
    let ghost rv = chain_view(roots@);
    let first = match verilith_x509::parse(chain[0].as_slice()) {
        Some(c) => c,
        None => return Err(BAD_CERTIFICATE),
    };
    if !leaf_ok_x(&first, now) {
        return Err(BAD_CERTIFICATE);
    }
    proof {
        assert(cv[0] == chain@[0]@);
        lemma_cert_of(cv[0], first@);
        lemma_prefix_start(cv, now@);
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
            prefix_ok(cv, i as int, now@),
        decreases MAX_DEPTH - i,
    {
        match find_root(prov, &cur, roots) {
            Some(j) => {
                proof {
                    assert(rv[j as int] == roots@[j as int]@);
                    lemma_prefix_done(cv, i as int, rv, j as int, now@);
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
        if !ca_ok_x(&next, now, i) {
            return Err(BAD_CERTIFICATE);
        }
        proof {
            assert(cv[i + 1] == chain@[i + 1]@);
            lemma_cert_of(cv[i + 1], next@);
            lemma_prefix_extend(cv, i as int, now@);
        }
        cur = next;
        i = i + 1;
    }
    Err(UNKNOWN_CA)
}

} // verus!
