//! The specification of how a TLS client authenticates a server: the
//! server's certificate path, checked against the client's trust anchors
//! (RFC 5280 §6.1, narrowed as described below), and the server's
//! identity, the host name the client asked for, checked against the
//! leaf's subjectAltName (RFC 9525 §6.3, §6.4). Trusted: read it against
//! the RFCs.
//!
//! The path check (`server_chain_ok`) is `spec_client::chain_ok`'s, with
//! the purpose turned around and the name added:
//!
//! - the path is the server's list as sent, leaf first, up to the first
//!   certificate a trust anchor issued; no reordering, at most
//!   `MAX_DEPTH` certificates; anything after it is ignored;
//! - names chain by equality of the parsed Names (the code compares their
//!   DER bytes, which is stricter);
//! - every certificate on the path is within its validity period at the
//!   provider's clock; trust anchors are taken as they are (RFC 5280
//!   §6.1.1(d)), their own validity, extensions and name constraints
//!   unchecked;
//! - an intermediate must be a CA, within its pathLenConstraint, with
//!   keyCertSign if it has keyUsage; the leaf must not be a CA and must have
//!   digitalSignature if it has keyUsage; every certificate on the path must
//!   allow id-kp-serverAuth if it has extendedKeyUsage (EKU chaining, as in
//!   the Web PKI);
//! - a critical extension other than basicConstraints, keyUsage,
//!   extendedKeyUsage, subjectAltName and nameConstraints rejects the
//!   certificate (§4.2);
//! - name constraints (§4.2.1.10) are applied to the one name the client
//!   authenticates, the host name: within some permitted dNSName subtree of
//!   each intermediate that has any, and within none of its excluded dNSName
//!   subtrees. Other names in the leaf, and constraints of other name forms,
//!   do not decide anything here, because they are not the identity the
//!   connection is for;
//! - the host name must match a dNSName of the leaf's subjectAltName
//!   (RFC 9525 §6.3), ASCII case-insensitively; a wildcard is only a whole
//!   left-most label `*`, matching exactly one non-empty label, and only
//!   with at least two labels after it (§6.3, rule 2). There is no fallback
//!   to the subject's common name (§6.3: a client MUST NOT seek a match in
//!   the CN when the certificate has subjectAltName; this check requires
//!   subjectAltName). The host is a DNS name (`spec::valid_host_name`): IP
//!   addresses are not taken;
//! - signatures are the provider's (`crypto::x509_signed`).
use crate::crypto::*;
use crate::spec::*;
use crate::spec_client::*;
#[cfg(verus_only)]
use verilith_x509::cert::{spec_alt_names, spec_basic_constraints, spec_ext_key_usage, spec_key_usage, spec_name_constraints};
use verilith_x509::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Names (RFC 9525 §6.3, RFC 5280 §4.2.1.10, §7.2)
// ---------------------------------------------------------------------------

/// ASCII lower case.
pub open spec fn lower(c: u8) -> u8 {
    if 65 <= c <= 90 {
        (c + 32) as u8
    } else {
        c
    }
}

/// Equal, ASCII case-insensitively (RFC 9525 §6.3: "comparison ... MUST
/// be performed in a case-insensitive manner"; host names are ASCII).
pub open spec fn eq_ci(a: Seq<u8>, b: Seq<u8>) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> lower(#[trigger] a[i]) == lower(b[i])
}

/// `s` holds the byte `c`.
pub open spec fn holds_byte(s: Seq<u8>, c: u8) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

/// The last `n` bytes of `s`.
pub open spec fn tail(s: Seq<u8>, n: int) -> Seq<u8> {
    s.skip(s.len() - n)
}

/// A dNSName of the certificate, `pat`, matches `host` (RFC 9525 §6.3):
/// equal, or `*.` then a suffix with at least two labels, matching every
/// label of `host` but its first, which is not empty.
pub open spec fn dns_matches(pat: Seq<u8>, host: Seq<u8>) -> bool {
    ||| eq_ci(pat, host)
    ||| {
        let suffix = pat.skip(1);
        let k = host.len() - suffix.len();
        &&& pat.len() >= 2
        &&& pat[0] == 42u8
        &&& pat[1] == 46u8
        &&& holds_byte(suffix.skip(1), 46u8)
        &&& k >= 1
        &&& eq_ci(tail(host, suffix.len() as int), suffix)
        &&& forall|i: int| 0 <= i < k ==> host[i] != 46u8
    }
}

/// The leaf's subjectAltName has a dNSName that matches `host`.
pub open spec fn host_matches(c: SpecCertificate, host: Seq<u8>) -> bool {
    spec_alt_names(c, CE_SUBJECT_ALT_NAME) matches Some(l) && exists|i: int|
        0 <= i < l.len() && (#[trigger] l[i] matches SpecGeneralName::Dns(d) && dns_matches(d, host))
}

/// `host` is within the dNSName subtree `base` (RFC 5280 §4.2.1.10: any
/// name made by adding zero or more labels to the left of `base`; a base
/// that starts with a period, as some CAs write it, needs at least one
/// label added; an empty base is every name).
pub open spec fn dns_within(base: Seq<u8>, host: Seq<u8>) -> bool {
    ||| base.len() == 0
    ||| base[0] == 46u8 && host.len() > base.len() && eq_ci(tail(host, base.len() as int), base)
    ||| base[0] != 46u8 && eq_ci(host, base)
    ||| base[0] != 46u8 && host.len() > base.len() && host[host.len() - base.len() - 1] == 46u8 && eq_ci(
        tail(host, base.len() as int),
        base,
    )
}

/// Some dNSName subtree in `l` holds `host`.
pub open spec fn some_within(l: Seq<SpecGeneralName>, host: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < l.len() && (#[trigger] l[i] matches SpecGeneralName::Dns(d) && dns_within(d, host))
}

/// `l` has a dNSName subtree.
pub open spec fn some_dns(l: Seq<SpecGeneralName>) -> bool {
    exists|i: int| 0 <= i < l.len() && #[trigger] l[i] is Dns
}

/// `c`'s name constraints allow `host`: if it has permitted dNSName
/// subtrees, one holds `host`; none of its excluded dNSName subtrees does.
pub open spec fn nc_allows(c: SpecCertificate, host: Seq<u8>) -> bool {
    match spec_name_constraints(c) {
        None => true,
        Some(nc) => {
            &&& (nc.permitted matches Some(p) && some_dns(p)) ==> some_within(nc.permitted.unwrap(), host)
            &&& nc.excluded is Some ==> !some_within(nc.excluded.unwrap(), host)
        },
    }
}

// ---------------------------------------------------------------------------
// The path (RFC 5280 §6.1, narrowed: see the module's comment)
// ---------------------------------------------------------------------------

/// id-kp-serverAuth (1.3.6.1.5.5.7.3.1), as OID contents.
pub open spec fn oid_server_auth() -> Seq<u8> {
    seq![0x2bu8, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01]
}

/// extendedKeyUsage, if present, allows TLS server authentication.
pub open spec fn eku_server(c: SpecCertificate) -> bool {
    match spec_ext_key_usage(c) {
        None => true,
        Some(l) => l.contains(oid_server_auth()) || l.contains(oid_any_eku()),
    }
}

/// The critical extensions the server path check processes:
/// `spec_client::known_critical`'s and nameConstraints.
pub open spec fn known_critical_srv(oid: Seq<u8>) -> bool {
    known_critical(oid) || oid == oid_ce(30)
}

pub open spec fn critical_known_srv(c: SpecCertificate) -> bool {
    forall|i: int|
        0 <= i < c.tbs.extensions.len() && (#[trigger] c.tbs.extensions[i]).critical ==> known_critical_srv(
            c.tbs.extensions[i].oid,
        )
}

/// The server's leaf: in its validity period, no unknown critical
/// extension, not a CA, digitalSignature if it has keyUsage, serverAuth if
/// it has extendedKeyUsage, and a subjectAltName dNSName for `host`.
#[verifier::opaque]
pub open spec fn srv_leaf_ok(c: SpecCertificate, now: SpecTime, host: Seq<u8>) -> bool {
    &&& within(c, now)
    &&& critical_known_srv(c)
    &&& !(spec_basic_constraints(c) matches Some(b) && b.ca)
    &&& spec_key_usage(c) matches Some(m) ==> m % 2 == 1
    &&& eku_server(c)
    &&& host_matches(c, host)
}

/// An intermediate with `below` intermediates under it: in its validity
/// period, no unknown critical extension, a CA whose pathLenConstraint
/// allows `below`, keyCertSign if it has keyUsage, serverAuth if it has
/// extendedKeyUsage, and name constraints that allow `host`.
#[verifier::opaque]
pub open spec fn srv_ca_ok(c: SpecCertificate, now: SpecTime, below: int, host: Seq<u8>) -> bool {
    &&& within(c, now)
    &&& critical_known_srv(c)
    &&& spec_basic_constraints(c) matches Some(b) && b.ca && (b.path_len matches Some(n) ==> below <= n)
    &&& spec_key_usage(c) matches Some(m) ==> (m / 32) % 2 == 1
    &&& eku_server(c)
    &&& nc_allows(c, host)
}

/// `chain[0..=k]` is a path for `host` to trust anchor `root` at `now`.
pub open spec fn srv_path_ok(chain: Seq<Seq<u8>>, k: int, root: Seq<u8>, now: SpecTime, host: Seq<u8>) -> bool {
    &&& 0 <= k < chain.len()
    &&& k < MAX_DEPTH
    &&& forall|i: int| 0 <= i <= k ==> parses(#[trigger] chain[i])
    &&& parses(root)
    &&& srv_leaf_ok(cert_of(chain[0]), now, host)
    &&& forall|i: int| 1 <= i <= k ==> srv_ca_ok(cert_of(#[trigger] chain[i]), now, i - 1, host)
    &&& forall|i: int| 0 <= i < k ==> issued(cert_of(#[trigger] chain[i]), cert_of(chain[i + 1]))
    &&& issued(cert_of(chain[k]), cert_of(root))
}

/// The server's chain leads, as sent, to one of the trust anchors, and
/// names `host`.
pub open spec fn server_chain_ok(chain: Seq<Seq<u8>>, roots: Seq<Seq<u8>>, now: SpecTime, host: Seq<u8>) -> bool {
    exists|k: int, j: int| 0 <= j < roots.len() && #[trigger] srv_path_ok(chain, k, roots[j], now, host)
}

} // verus!
