//! The specification of client authentication: the CertificateRequest a
//! server sends (RFC 8446 §4.3.2), the client's Certificate and
//! CertificateVerify (§4.4.2, §4.4.3), and the check of the client's
//! certificate path against the server's trust anchors (RFC 5280 §6.1,
//! narrowed as described below). Trusted: read it against the RFCs.
//!
//! With client authentication on, a full handshake goes:
//!
//! ```text
//!   ServerHello
//!   {EncryptedExtensions}
//!   {CertificateRequest}   signature_algorithms only, empty context
//!   {Certificate}
//!   {CertificateVerify}
//!   {Finished}
//!                          <- {Certificate}        the client's chain
//!                          <- {CertificateVerify}  if the chain is not empty
//!                          <- {Finished}           over all of the above
//! ```
//!
//! The server never resumes and never issues tickets while client
//! authentication is on, so it never takes 0-RTT data then either (a
//! resumed connection would have no certificate to show).
//!
//! The path check (`chain_ok`) is RFC 5280's basic path validation for one
//! path, with these choices, each the conservative one:
//!
//! - the path is the client's list as sent, leaf first, up to the first
//!   certificate a trust anchor issued; no reordering, at most
//!   `MAX_DEPTH` certificates; anything after that certificate is ignored;
//! - names chain by equality of the parsed Names (RFC 5280 §7.1 allows more
//!   matches; the code is stricter still, and compares their DER bytes);
//! - every certificate on the path, the leaf included, must be within its
//!   validity period at the time the provider's clock gives
//!   (`Provider::now_utc`); trust anchors are taken as they are, with no
//!   check of their own validity or extensions (RFC 5280 §6.1.1(d));
//! - an intermediate must be a CA (basicConstraints cA), within its
//!   pathLenConstraint, with keyCertSign if it has keyUsage;
//! - the leaf must not be a CA, must have digitalSignature if it has
//!   keyUsage, and, like every intermediate on the path, must allow
//!   id-kp-clientAuth if it has extendedKeyUsage (RFC 5280 §4.2.1.12; the
//!   "EKU chaining" rule of the Web PKI);
//! - a certificate with a critical extension other than basicConstraints,
//!   keyUsage, extendedKeyUsage and subjectAltName is rejected (§4.2):
//!   name constraints and policies are not processed, so a certificate
//!   that makes them critical is not accepted;
//! - signatures are the provider's (`crypto::x509_signed`).
use crate::crypto::*;
use crate::spec::*;
use crate::spec_keys::*;
use crate::spec_server::*;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
#[cfg(verus_only)]
use verilith_x509::cert::{spec_basic_constraints, spec_ext_key_usage, spec_key_usage};
use verilith_x509::spec::*;
use vstd::prelude::*;

verus! {

/// The AlertDescription codes client authentication adds (§6).
pub const BAD_CERTIFICATE: u8 = 42;

pub const UNKNOWN_CA: u8 = 48;

pub const UNSUPPORTED_EXTENSION: u8 = 110;

pub const CERTIFICATE_REQUIRED: u8 = 116;

/// The longest path checked, trust anchor not counted.
pub const MAX_DEPTH: usize = 8;

/// What a server asks of clients: the signature schemes it takes in their
/// CertificateVerify, its trust anchors (DER certificates), and whether a
/// client must send a certificate.
pub struct SpecClientCfg {
    pub sigs: Seq<u16>,
    pub roots: Seq<Seq<u8>>,
    pub required: bool,
}

// ---------------------------------------------------------------------------
// CertificateRequest (§4.3.2)
// ---------------------------------------------------------------------------

/// A list of scheme_list, each big-endian.
pub open spec fn scheme_list(s: Seq<u16>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        scheme_list(s.drop_last()) + be2(s.last() as nat)
    }
}

/// CertificateRequest: an empty certificate_request_context and one
/// extension, signature_algorithms (§4.2.3) with `sigs`.
pub open spec fn certificate_request(sigs: Seq<u16>) -> Seq<u8> {
    let e = ext(13, be2(2 * sigs.len()) + scheme_list(sigs));
    hs_msg(13, seq![0u8] + be2(e.len()) + e)
}

/// The CertificateRequest a configuration sends, if any.
#[verifier::opaque]
pub open spec fn cr_msg(c: Option<SpecClientCfg>) -> Seq<u8> {
    match c {
        Some(a) => certificate_request(a.sigs),
        None => Seq::empty(),
    }
}

// ---------------------------------------------------------------------------
// The client's Certificate (§4.4.2)
// ---------------------------------------------------------------------------

/// The `certificate_list` contents: each entry is `cert_data<1..2^24-1>`
/// then `extensions<0..2^16-1>`. The server's CertificateRequest asked for
/// no certificate extension, so the client may send none (§4.4.2: they
/// must answer the CertificateRequest's); one is `unsupported_extension`
/// (§4.2).
pub open spec fn cert_list(b: Seq<u8>) -> Result<Seq<Seq<u8>>, u8>
    decreases b.len(),
{
    if b.len() == 0 {
        Ok(Seq::empty())
    } else if b.len() < 3 {
        Err(DECODE_ERROR_ALERT)
    } else {
        let n = be24(b, 0) as int;
        if n == 0 || b.len() < 3 + n + 2 {
            Err(DECODE_ERROR_ALERT)
        } else {
            let e = be16(b, 3 + n) as int;
            if b.len() < 3 + n + 2 + e {
                Err(DECODE_ERROR_ALERT)
            } else if e != 0 {
                Err(UNSUPPORTED_EXTENSION)
            } else {
                match cert_list(b.skip(3 + n + 2)) {
                    Ok(l) => Ok(seq![b.subrange(3, 3 + n)] + l),
                    Err(a) => Err(a),
                }
            }
        }
    }
}

pub const DECODE_ERROR_ALERT: u8 = 50;

pub const ILLEGAL_PARAMETER_ALERT: u8 = 47;

/// The body of a client's Certificate message: `certificate_request_context`
/// (which must be the CertificateRequest's, empty: else
/// `illegal_parameter`), then `certificate_list<0..2^24-1>`, exactly. The
/// certificates, leaf first, or the alert.
pub open spec fn parse_client_certificate(body: Seq<u8>) -> Result<Seq<Seq<u8>>, u8> {
    if body.len() < 1 || body.len() < 1 + body[0] as int + 3 {
        Err(DECODE_ERROR_ALERT)
    } else if be24(body, 1 + body[0] as int) != body.len() - (1 + body[0] as int + 3) {
        Err(DECODE_ERROR_ALERT)
    } else if body[0] != 0 {
        Err(ILLEGAL_PARAMETER_ALERT)
    } else {
        cert_list(body.skip(4))
    }
}

// ---------------------------------------------------------------------------
// The client's CertificateVerify (§4.4.3)
// ---------------------------------------------------------------------------

/// "TLS 1.3, client CertificateVerify"
pub open spec fn client_cv_label() -> Seq<u8> {
    seq![
        84u8, 76, 83, 32, 49, 46, 51, 44, 32, 99, 108, 105, 101, 110, 116, 32, 67, 101, 114, 116,
        105, 102, 105, 99, 97, 116, 101, 86, 101, 114, 105, 102, 121,
    ]
}

/// What a client's CertificateVerify signs: 64 spaces, the context string,
/// a zero byte, and the transcript hash `th` (through the client's
/// Certificate).
#[verifier::opaque]
pub open spec fn client_cv_content(th: Seq<u8>) -> Seq<u8> {
    Seq::new(64, |i: int| 0x20u8) + client_cv_label() + seq![0u8] + th
}

// ---------------------------------------------------------------------------
// The path check (RFC 5280 §6.1, narrowed: see the module's comment)
// ---------------------------------------------------------------------------

/// Whether `der` is one certificate (`verilith_x509`'s spec). Opaque, like
/// `cert_of`, only to keep the proofs fast.
#[verifier::opaque]
pub open spec fn parses(der: Seq<u8>) -> bool {
    parse_certificate(der) is Some
}

/// The certificate `der` encodes (only meaningful when it parses).
#[verifier::opaque]
pub open spec fn cert_of(der: Seq<u8>) -> SpecCertificate {
    parse_certificate(der).unwrap()
}

/// `a` is no later than `b`.
pub open spec fn time_le(a: SpecTime, b: SpecTime) -> bool {
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

/// `now` is within the certificate's validity period (§4.1.2.5: both ends
/// included).
pub open spec fn within(c: SpecCertificate, now: SpecTime) -> bool {
    time_le(c.tbs.not_before, now) && time_le(now, c.tbs.not_after)
}

/// The critical extensions this check processes: keyUsage,
/// subjectAltName (which needs no processing: §4.2.1.6 makes it critical
/// when the subject is empty), basicConstraints, extendedKeyUsage.
pub open spec fn known_critical(oid: Seq<u8>) -> bool {
    oid == oid_ce(15) || oid == oid_ce(17) || oid == oid_ce(19) || oid == oid_ce(37)
}

pub open spec fn critical_known(c: SpecCertificate) -> bool {
    forall|i: int|
        0 <= i < c.tbs.extensions.len() && (#[trigger] c.tbs.extensions[i]).critical ==> known_critical(
            c.tbs.extensions[i].oid,
        )
}

/// id-kp-clientAuth (1.3.6.1.5.5.7.3.2), as OID contents.
pub open spec fn oid_client_auth() -> Seq<u8> {
    seq![0x2bu8, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x02]
}

/// anyExtendedKeyUsage (2.5.29.37.0).
pub open spec fn oid_any_eku() -> Seq<u8> {
    seq![0x55u8, 0x1d, 0x25, 0x00]
}

/// extendedKeyUsage, if present, allows TLS client authentication.
pub open spec fn eku_client(c: SpecCertificate) -> bool {
    match spec_ext_key_usage(c) {
        None => true,
        Some(l) => l.contains(oid_client_auth()) || l.contains(oid_any_eku()),
    }
}

/// The leaf: in its validity period, no unknown critical extension, not a
/// CA, digitalSignature if it has keyUsage (bit 0), and clientAuth if it
/// has extendedKeyUsage.
#[verifier::opaque]
pub open spec fn leaf_ok(c: SpecCertificate, now: SpecTime) -> bool {
    &&& within(c, now)
    &&& critical_known(c)
    &&& !(spec_basic_constraints(c) matches Some(b) && b.ca)
    &&& spec_key_usage(c) matches Some(m) ==> m % 2 == 1
    &&& eku_client(c)
}

/// An intermediate with `below` intermediates under it on the path: in its
/// validity period, no unknown critical extension, a CA whose
/// pathLenConstraint allows `below`, keyCertSign if it has keyUsage (bit
/// 5), and clientAuth if it has extendedKeyUsage.
#[verifier::opaque]
pub open spec fn ca_ok(c: SpecCertificate, now: SpecTime, below: int) -> bool {
    &&& within(c, now)
    &&& critical_known(c)
    &&& spec_basic_constraints(c) matches Some(b) && b.ca && (b.path_len matches Some(n) ==> below <= n)
    &&& spec_key_usage(c) matches Some(m) ==> (m / 32) % 2 == 1
    &&& eku_client(c)
}

/// `parent` issued `child`: the names chain and the provider says
/// `parent`'s key signed `child`'s TBSCertificate with `child`'s signature
/// algorithm.
#[verifier::opaque]
pub open spec fn issued(child: SpecCertificate, parent: SpecCertificate) -> bool {
    &&& child.tbs.issuer == parent.tbs.subject
    &&& x509_signed(child.tbs.signature, parent.tbs.spki, child.tbs_der, child.signature)
}

/// `chain[0..=k]` is a path to trust anchor `root` at `now`.
pub open spec fn path_ok(chain: Seq<Seq<u8>>, k: int, root: Seq<u8>, now: SpecTime) -> bool {
    &&& 0 <= k < chain.len()
    &&& k < MAX_DEPTH
    &&& forall|i: int| 0 <= i <= k ==> parses(#[trigger] chain[i])
    &&& parses(root)
    &&& leaf_ok(cert_of(chain[0]), now)
    &&& forall|i: int| 1 <= i <= k ==> ca_ok(cert_of(#[trigger] chain[i]), now, i - 1)
    &&& forall|i: int| 0 <= i < k ==> issued(cert_of(#[trigger] chain[i]), cert_of(chain[i + 1]))
    &&& issued(cert_of(chain[k]), cert_of(root))
}

/// The client's chain leads, as sent, to one of the trust anchors.
pub open spec fn chain_ok(chain: Seq<Seq<u8>>, roots: Seq<Seq<u8>>, now: SpecTime) -> bool {
    exists|k: int, j: int| 0 <= j < roots.len() && #[trigger] path_ok(chain, k, roots[j], now)
}

// ---------------------------------------------------------------------------
// Client authentication as it went
// ---------------------------------------------------------------------------

/// What the client sent in answer to the CertificateRequest: its
/// Certificate message, the certificates in it, and (if there were any)
/// its CertificateVerify's scheme and signature; and the time the path
/// was checked at.
pub struct SpecClientAuth {
    pub cert_msg: Seq<u8>,
    pub chain: Seq<Seq<u8>>,
    pub scheme: u16,
    pub sig: Seq<u8>,
    pub now: SpecTime,
}

impl SpecClientAuth {
    /// The client's messages before its Finished: Certificate, then
    /// CertificateVerify unless the chain was empty.
    pub open spec fn msgs(self) -> Seq<u8> {
        if self.chain.len() == 0 {
            self.cert_msg
        } else {
            self.cert_msg + certificate_verify(self.scheme, self.sig)
        }
    }

    /// The answer is one RFC 8446 allows (and the configuration takes),
    /// after transcript `th` (..server Finished), with hash `a`:
    ///
    /// - the Certificate is a well-formed handshake message of type 11
    ///   whose certificates (`parse_client_certificate`) are `chain`;
    /// - an empty chain only if a certificate is not required (§4.4.2.4);
    /// - otherwise the chain is a path to a trust anchor (`chain_ok`), and
    ///   the CertificateVerify uses a scheme the server asked for (§4.4.3)
    ///   and is the leaf's key's signature over §4.4.3's content for the
    ///   transcript through the Certificate.
    pub open spec fn ok(self, c: SpecClientCfg, a: HashAlg, th: Seq<u8>) -> bool {
        &&& is_msg(self.cert_msg, 11)
        &&& parse_client_certificate(self.cert_msg.skip(4)) == Ok::<Seq<Seq<u8>>, u8>(self.chain)
        &&& self.chain.len() == 0 ==> !c.required
        &&& self.chain.len() > 0 ==> {
            &&& chain_ok(self.chain, c.roots, self.now)
            &&& c.sigs.contains(self.scheme)
            &&& tls_signed(
                self.scheme,
                cert_of(self.chain[0]).tbs.spki,
                client_cv_content(hash(a, th + self.cert_msg)),
                self.sig,
            )
        }
    }
}

} // verus!
