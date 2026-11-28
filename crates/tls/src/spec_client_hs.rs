//! The specification of a TLS 1.3 client's handshake (RFC 8446 §2, §4,
//! Appendix A.1): the ClientHello it sends, what it takes from the server
//! (ServerHello or HelloRetryRequest, EncryptedExtensions,
//! CertificateRequest, Certificate, CertificateVerify, Finished), and what
//! it sends back. Trusted: read it against the RFC.
//!
//! A full handshake, from the client's side:
//!
//! ```text
//!   ClientHello            key shares for the first `shares` groups
//!                          -> [HelloRetryRequest]   (§4.1.4)
//!   [ClientHello]          the same, with the one share asked for and
//!                          the cookie, if any
//!                          -> ServerHello
//!                          -> {EncryptedExtensions}
//!                          -> {CertificateRequest}  optional
//!                          -> {Certificate}
//!                          -> {CertificateVerify}
//!                          -> {Finished}
//!   [change_cipher_spec]   middlebox compatibility (Appendix D.4)
//!   {Certificate}          empty, if asked for one
//!   {Finished}
//!   [application data]     both ways
//! ```
//!
//! The client does not offer PSKs or 0-RTT, ECH, or client certificates
//! (it answers a CertificateRequest with an empty Certificate, §4.4.2.4).
//! Where RFC 8446 leaves a choice to the client, this spec makes the
//! strict one and says so.
use crate::crypto::*;
use crate::spec::*;
use crate::spec_client::*;
use crate::spec_keys::*;
use crate::spec_server::*;
use crate::spec_server_auth::*;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use verilith_x509::spec::SpecTime;
use vstd::prelude::*;

verus! {

/// The AlertDescription codes the client adds (§6).
pub const UNEXPECTED_MESSAGE_A: u8 = 10;

pub const DECRYPT_ERROR_A: u8 = 51;

pub const PROTOCOL_VERSION_A: u8 = 70;

pub const MISSING_EXTENSION_A: u8 = 109;

/// The longest HelloRetryRequest cookie the client echoes (its own limit,
/// so that ClientHello2 fits in one record).
pub const MAX_COOKIE: usize = 4096;

/// What a client offers and trusts: its cipher suites, groups (the first
/// `shares` of them get a key share in the first ClientHello), signature
/// schemes, ALPN protocols, and trust anchors (DER certificates).
pub struct SpecCliCfg {
    pub suites: Seq<u16>,
    pub groups: Seq<u16>,
    pub shares: nat,
    pub sigs: Seq<u16>,
    pub alpn: Seq<Seq<u8>>,
    pub roots: Seq<Seq<u8>>,
}

// ---------------------------------------------------------------------------
// ClientHello (§4.1.2)
// ---------------------------------------------------------------------------

/// A vector of u16s with its 2-byte length (§3.4).
pub open spec fn list16(s: Seq<u16>) -> Seq<u8> {
    be2(2 * s.len()) + scheme_list(s)
}

/// `KeyShareEntry`s (§4.2.8): group, then a 2-byte length and the share.
pub open spec fn ks_entries(sh: Seq<(u16, Seq<u8>)>) -> Seq<u8>
    decreases sh.len(),
{
    if sh.len() == 0 {
        Seq::empty()
    } else {
        ks_entries(sh.drop_last()) + be2(sh.last().0 as nat) + be2(sh.last().1.len()) + sh.last().1
    }
}

/// The groups of key shares.
pub open spec fn share_groups(sh: Seq<(u16, Seq<u8>)>) -> Seq<u16> {
    sh.map_values(|p: (u16, Seq<u8>)| p.0)
}

/// The share for group `g` (the first, if there were two).
pub open spec fn share_of(sh: Seq<(u16, Seq<u8>)>, g: u16) -> Seq<u8>
    decreases sh.len(),
{
    if sh.len() == 0 {
        Seq::empty()
    } else if sh[0].0 == g {
        sh[0].1
    } else {
        share_of(sh.drop_first(), g)
    }
}

/// `ProtocolName`s (RFC 7301 §3.1), each with its 1-byte length.
pub open spec fn alpn_names(a: Seq<Seq<u8>>) -> Seq<u8>
    decreases a.len(),
{
    if a.len() == 0 {
        Seq::empty()
    } else {
        alpn_names(a.drop_last()) + seq![a.last().len() as u8] + a.last()
    }
}

/// server_name (RFC 6066 §3): one host_name.
pub open spec fn sni_ext(host: Seq<u8>) -> Seq<u8> {
    ext(0, be2(host.len() + 3) + seq![0u8] + be2(host.len()) + host)
}

/// application_layer_protocol_negotiation, if the client has protocols.
pub open spec fn ch_alpn_ext(a: Seq<Seq<u8>>) -> Seq<u8> {
    if a.len() == 0 {
        Seq::empty()
    } else {
        ext(16, be2(alpn_names(a).len()) + alpn_names(a))
    }
}

/// cookie (§4.2.2), echoed from a HelloRetryRequest.
pub open spec fn cookie_ext(cookie: Option<Seq<u8>>) -> Seq<u8> {
    match cookie {
        None => Seq::empty(),
        Some(k) => ext(44, be2(k.len()) + k),
    }
}

/// The ClientHello's extensions: server_name, supported_versions (TLS 1.3
/// only), supported_groups, signature_algorithms, key_share, then ALPN and
/// the cookie when there are any.
pub open spec fn ch_exts(c: SpecCliCfg, host: Seq<u8>, shares: Seq<(u16, Seq<u8>)>, cookie: Option<Seq<u8>>) -> Seq<u8> {
    sni_ext(host) + ext(43, seq![2u8, 3u8, 4u8]) + ext(10, list16(c.groups)) + ext(13, list16(c.sigs)) + ext(
        51,
        be2(ks_entries(shares).len()) + ks_entries(shares),
    ) + ch_alpn_ext(c.alpn) + cookie_ext(cookie)
}

/// A ClientHello (§4.1.2): legacy_version 0x0303, `random`,
/// legacy_session_id `sid` (32 random bytes: middlebox compatibility,
/// Appendix D.4), the cipher suites, the null compression method, the
/// extensions.
#[verifier::opaque]
pub open spec fn client_hello(
    c: SpecCliCfg,
    host: Seq<u8>,
    random: Seq<u8>,
    sid: Seq<u8>,
    shares: Seq<(u16, Seq<u8>)>,
    cookie: Option<Seq<u8>>,
) -> Seq<u8> {
    let e = ch_exts(c, host, shares, cookie);
    hs_msg(
        1,
        seq![3u8, 3u8] + random + seq![sid.len() as u8] + sid + list16(c.suites) + seq![1u8, 0u8] + be2(e.len()) + e,
    )
}

// ---------------------------------------------------------------------------
// ServerHello and HelloRetryRequest (§4.1.3, §4.1.4)
// ---------------------------------------------------------------------------

/// The fields of a ServerHello body.
pub struct SpecSh {
    pub legacy_version: nat,
    pub random: Seq<u8>,
    pub sid: Seq<u8>,
    pub suite: u16,
    pub compression: u8,
    pub exts: Seq<u8>,
}

/// A ServerHello body's syntax: legacy_version, random, a
/// legacy_session_id_echo of at most 32 bytes, cipher_suite,
/// legacy_compression_method and the extensions vector, exactly.
pub open spec fn parse_sh(b: Seq<u8>) -> Option<SpecSh> {
    if b.len() < 35 || b[34] > 32 {
        None
    } else {
        let l = b[34] as int;
        if b.len() < 40 + l || b.len() != 40 + l + be16(b, 38 + l) {
            None
        } else {
            Some(
                SpecSh {
                    legacy_version: be16(b, 0),
                    random: b.subrange(2, 34),
                    sid: b.subrange(35, 35 + l),
                    suite: be16(b, 35 + l) as u16,
                    compression: b[37 + l],
                    exts: b.skip(40 + l),
                },
            )
        }
    }
}

/// The extensions of a ServerHello or HelloRetryRequest the client takes:
/// the data of supported_versions, key_share and (in a HelloRetryRequest)
/// cookie.
pub struct ShExts {
    pub version: Option<Seq<u8>>,
    pub key_share: Option<Seq<u8>>,
    pub cookie: Option<Seq<u8>>,
}

pub open spec fn no_sh_exts() -> ShExts {
    ShExts { version: None, key_share: None, cookie: None }
}

/// Reads extensions `b` into `acc`, front to back: decode_error for bad
/// syntax, illegal_parameter for a second extension of a type (§4.2),
/// unsupported_extension for any other type (§4.2: the client offered
/// nothing else a ServerHello may answer; cookie only in a
/// HelloRetryRequest).
pub open spec fn sh_ext_scan(b: Seq<u8>, acc: ShExts, hrr: bool) -> Result<ShExts, u8>
    decreases b.len(),
{
    if b.len() == 0 {
        Ok(acc)
    } else if b.len() < 4 || b.len() < 4 + be16(b, 2) {
        Err(DECODE_ERROR_ALERT)
    } else {
        let t = be16(b, 0);
        let d = b.subrange(4, 4 + be16(b, 2) as int);
        let rest = b.skip(4 + be16(b, 2) as int);
        if t == 43 {
            if acc.version is Some {
                Err(ILLEGAL_PARAMETER_ALERT)
            } else {
                sh_ext_scan(rest, ShExts { version: Some(d), ..acc }, hrr)
            }
        } else if t == 51 {
            if acc.key_share is Some {
                Err(ILLEGAL_PARAMETER_ALERT)
            } else {
                sh_ext_scan(rest, ShExts { key_share: Some(d), ..acc }, hrr)
            }
        } else if t == 44 && hrr {
            if acc.cookie is Some {
                Err(ILLEGAL_PARAMETER_ALERT)
            } else {
                sh_ext_scan(rest, ShExts { cookie: Some(d), ..acc }, hrr)
            }
        } else {
            Err(UNSUPPORTED_EXTENSION)
        }
    }
}

/// What a ServerHello message comes to.
pub enum SpecShOut {
    /// A ServerHello: the suite, and the group and share of its key_share.
    Hello { suite: u16, group: u16, share: Seq<u8> },
    /// A HelloRetryRequest: the suite, the group asked for, the cookie.
    Retry { suite: u16, group: Option<u16>, cookie: Option<Seq<u8>> },
}

/// The ServerHello `m`, for a ClientHello with session id `sid` and key
/// shares for `offered`, or the alert:
///
/// - TLS 1.3 only: no supported_versions is a TLS 1.2 (or older) server,
///   `protocol_version`; supported_versions must select 0x0304 and
///   legacy_version be 0x0303 (§4.1.3, §4.2.1), else `illegal_parameter`;
/// - the session id echoed, the compression method 0, and a suite the
///   client offered (§4.1.3), else `illegal_parameter`;
/// - a HelloRetryRequest (the special random) asks for a group the client
///   offered and sent no share for (§4.1.4), with a cookie of at least one
///   byte; at least one of the two, else `illegal_parameter`; a cookie
///   over `MAX_COOKIE` bytes is `illegal_parameter` too (this client's
///   limit);
/// - a ServerHello has key_share (else `missing_extension`) with one
///   non-empty share for an offered group (else `illegal_parameter`,
///   §4.2.8).
#[verifier::opaque]
pub open spec fn read_sh(c: SpecCliCfg, sid: Seq<u8>, offered: Seq<u16>, m: Seq<u8>) -> Result<SpecShOut, u8> {
    match parse_sh(m.skip(4)) {
        None => Err(DECODE_ERROR_ALERT),
        Some(s) => {
            let hrr = s.random == hrr_random();
            match sh_ext_scan(s.exts, no_sh_exts(), hrr) {
                Err(a) => Err(a),
                Ok(x) => if x.version is None {
                    Err(PROTOCOL_VERSION_A)
                } else if x.version != Some(seq![3u8, 4u8]) || s.legacy_version != 0x0303 || s.sid != sid
                    || s.compression != 0 || !c.suites.contains(s.suite) {
                    Err(ILLEGAL_PARAMETER_ALERT)
                } else if hrr {
                    let g: Result<Option<u16>, u8> = match x.key_share {
                        None => Ok(None),
                        Some(d) => if d.len() != 2 {
                            Err(DECODE_ERROR_ALERT)
                        } else if !c.groups.contains(be16(d, 0) as u16) || offered.contains(be16(d, 0) as u16) {
                            Err(ILLEGAL_PARAMETER_ALERT)
                        } else {
                            Ok(Some(be16(d, 0) as u16))
                        },
                    };
                    let k: Result<Option<Seq<u8>>, u8> = match x.cookie {
                        None => Ok(None),
                        Some(d) => if d.len() < 3 || be16(d, 0) != d.len() - 2 {
                            Err(DECODE_ERROR_ALERT)
                        } else if d.len() - 2 > MAX_COOKIE {
                            Err(ILLEGAL_PARAMETER_ALERT)
                        } else {
                            Ok(Some(d.skip(2)))
                        },
                    };
                    match (g, k) {
                        (Err(a), _) => Err(a),
                        (_, Err(a)) => Err(a),
                        (Ok(None), Ok(None)) => Err(ILLEGAL_PARAMETER_ALERT),
                        (Ok(gg), Ok(kk)) => Ok(SpecShOut::Retry { suite: s.suite, group: gg, cookie: kk }),
                    }
                } else {
                    match x.key_share {
                        None => Err(MISSING_EXTENSION_A),
                        Some(d) => if d.len() <= 4 || be16(d, 2) != d.len() - 4 {
                            Err(DECODE_ERROR_ALERT)
                        } else if !offered.contains(be16(d, 0) as u16) {
                            Err(ILLEGAL_PARAMETER_ALERT)
                        } else {
                            Ok(SpecShOut::Hello { suite: s.suite, group: be16(d, 0) as u16, share: d.skip(4) })
                        },
                    }
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------
// EncryptedExtensions (§4.3.1), CertificateRequest (§4.3.2),
// CertificateVerify (§4.4.3)
// ---------------------------------------------------------------------------

/// What the client takes from EncryptedExtensions: whether server_name and
/// supported_groups came, and the ALPN protocol chosen.
pub struct EeExts {
    pub sni: bool,
    pub groups: bool,
    pub alpn: Option<Seq<u8>>,
}

/// Reads EncryptedExtensions' extensions `b` into `acc`, front to back:
/// server_name (empty, RFC 6066 §3), supported_groups (§4.2.7: the client
/// may ignore its contents) and ALPN (exactly one protocol, one the client
/// offered, RFC 7301 §3.1) are the ones it answers; a second of a type is
/// `illegal_parameter`; any other type, and ALPN when the client offered
/// none, is `unsupported_extension` (§4.2).
pub open spec fn ee_scan(c: SpecCliCfg, b: Seq<u8>, acc: EeExts) -> Result<EeExts, u8>
    decreases b.len(),
{
    if b.len() == 0 {
        Ok(acc)
    } else if b.len() < 4 || b.len() < 4 + be16(b, 2) {
        Err(DECODE_ERROR_ALERT)
    } else {
        let t = be16(b, 0);
        let d = b.subrange(4, 4 + be16(b, 2) as int);
        let rest = b.skip(4 + be16(b, 2) as int);
        if t == 0 {
            if acc.sni {
                Err(ILLEGAL_PARAMETER_ALERT)
            } else if d.len() != 0 {
                Err(DECODE_ERROR_ALERT)
            } else {
                ee_scan(c, rest, EeExts { sni: true, ..acc })
            }
        } else if t == 10 {
            if acc.groups {
                Err(ILLEGAL_PARAMETER_ALERT)
            } else {
                ee_scan(c, rest, EeExts { groups: true, ..acc })
            }
        } else if t == 16 && c.alpn.len() > 0 {
            if acc.alpn is Some {
                Err(ILLEGAL_PARAMETER_ALERT)
            } else if d.len() < 4 || be16(d, 0) != d.len() - 2 || d[2] as int != d.len() - 3 {
                Err(DECODE_ERROR_ALERT)
            } else if !c.alpn.contains(d.skip(3)) {
                Err(ILLEGAL_PARAMETER_ALERT)
            } else {
                ee_scan(c, rest, EeExts { alpn: Some(d.skip(3)), ..acc })
            }
        } else {
            Err(UNSUPPORTED_EXTENSION)
        }
    }
}

/// EncryptedExtensions `m`: the ALPN protocol chosen, if any, or the alert.
#[verifier::opaque]
pub open spec fn read_ee(c: SpecCliCfg, m: Seq<u8>) -> Result<Option<Seq<u8>>, u8> {
    let b = m.skip(4);
    if b.len() < 2 || be16(b, 0) != b.len() - 2 {
        Err(DECODE_ERROR_ALERT)
    } else {
        match ee_scan(c, b.skip(2), EeExts { sni: false, groups: false, alpn: None }) {
            Ok(x) => Ok(x.alpn),
            Err(a) => Err(a),
        }
    }
}

/// A CertificateRequest `m` the client takes: its syntax (a
/// certificate_request_context and the extensions vector, exactly), and an
/// empty context, as in a handshake (§4.3.2), else `illegal_parameter`.
/// The extensions are not interpreted: the client sends no certificate.
#[verifier::opaque]
pub open spec fn read_cr(m: Seq<u8>) -> Result<(), u8> {
    let b = m.skip(4);
    if b.len() < 3 || b.len() != 3 + b[0] as int + be16(b, 1 + b[0] as int) {
        Err(DECODE_ERROR_ALERT)
    } else if b[0] != 0 {
        Err(ILLEGAL_PARAMETER_ALERT)
    } else {
        Ok(())
    }
}

/// The client's answer to a CertificateRequest: a Certificate with the
/// (empty) context and no certificates (§4.4.2.4).
pub open spec fn empty_certificate() -> Seq<u8> {
    hs_msg(11, seq![0u8, 0u8, 0u8, 0u8])
}

/// A CertificateVerify body's syntax: scheme, then the signature with its
/// 2-byte length, exactly.
pub open spec fn read_cv(m: Seq<u8>) -> Option<(u16, Seq<u8>)> {
    let b = m.skip(4);
    if b.len() < 4 || be16(b, 2) != b.len() - 4 {
        None
    } else {
        Some((be16(b, 0) as u16, b.skip(4)))
    }
}

// ---------------------------------------------------------------------------
// The handshake
// ---------------------------------------------------------------------------

/// The HelloRetryRequest, and what the client did about it.
pub struct SpecRetry {
    pub hrr: Seq<u8>,
    pub group: Option<u16>,
    pub cookie: Option<Seq<u8>>,
    /// The key shares of ClientHello2.
    pub shares: Seq<(u16, Seq<u8>)>,
}

/// A client handshake as it went: what the client sent, what it got, and
/// what its cryptography gave it.
pub struct SpecCliHs {
    pub random: Seq<u8>,
    pub sid: Seq<u8>,
    /// ClientHello1's key shares.
    pub shares: Seq<(u16, Seq<u8>)>,
    pub retry: Option<SpecRetry>,
    pub sh: Seq<u8>,
    pub suite: u16,
    pub group: u16,
    pub server_share: Seq<u8>,
    pub dhe: Seq<u8>,
    pub ee: Seq<u8>,
    pub alpn: Option<Seq<u8>>,
    pub cr: Option<Seq<u8>>,
    pub cert: Seq<u8>,
    pub chain: Seq<Seq<u8>>,
    pub now: SpecTime,
    pub cv: Seq<u8>,
    pub scheme: u16,
    pub sig: Seq<u8>,
    pub sfin: Seq<u8>,
}

impl SpecCliHs {
    pub open spec fn alg(self) -> HashAlg {
        suite_hash(self.suite)
    }

    pub open spec fn ch1(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        client_hello(c, host, self.random, self.sid, self.shares, None)
    }

    /// The key shares of the last ClientHello.
    pub open spec fn last_shares(self) -> Seq<(u16, Seq<u8>)> {
        match self.retry {
            None => self.shares,
            Some(r) => r.shares,
        }
    }

    /// The last ClientHello.
    pub open spec fn ch(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        match self.retry {
            None => self.ch1(c, host),
            Some(r) => client_hello(c, host, self.random, self.sid, r.shares, r.cookie),
        }
    }

    /// The transcript before the last ClientHello (§4.4.1).
    pub open spec fn prefix(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        match self.retry {
            None => Seq::empty(),
            Some(r) => message_hash(self.alg(), self.ch1(c, host)) + r.hrr,
        }
    }

    /// ..ServerHello.
    #[verifier::opaque]
    pub open spec fn th_sh(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        self.prefix(c, host) + self.ch(c, host) + self.sh
    }

    pub open spec fn cr_msg(self) -> Seq<u8> {
        match self.cr {
            Some(m) => m,
            None => Seq::empty(),
        }
    }

    /// ..Certificate.
    #[verifier::opaque]
    pub open spec fn th_cert(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        self.th_sh(c, host) + self.ee + self.cr_msg() + self.cert
    }

    /// ..CertificateVerify.
    #[verifier::opaque]
    pub open spec fn th_cv(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        self.th_cert(c, host) + self.cv
    }

    /// ..server Finished.
    #[verifier::opaque]
    pub open spec fn th_sfin(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        self.th_cv(c, host) + self.sfin
    }

    /// What the client sends before its Finished: an empty Certificate if
    /// the server asked for one.
    pub open spec fn client_msgs(self) -> Seq<u8> {
        if self.cr is Some {
            empty_certificate()
        } else {
            Seq::empty()
        }
    }

    /// ..the client's Certificate.
    #[verifier::opaque]
    pub open spec fn th_client(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        self.th_sfin(c, host) + self.client_msgs()
    }

    pub open spec fn psk(self) -> Seq<u8> {
        zeros(hash_len(self.alg()))
    }

    #[verifier::opaque]
    pub open spec fn c_hs(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        client_hs_traffic(self.alg(), self.psk(), self.dhe, self.th_sh(c, host))
    }

    #[verifier::opaque]
    pub open spec fn s_hs(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        server_hs_traffic(self.alg(), self.psk(), self.dhe, self.th_sh(c, host))
    }

    #[verifier::opaque]
    pub open spec fn c_ap(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        client_ap_traffic(self.alg(), self.psk(), self.dhe, self.th_sfin(c, host))
    }

    #[verifier::opaque]
    pub open spec fn s_ap(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        server_ap_traffic(self.alg(), self.psk(), self.dhe, self.th_sfin(c, host))
    }

    /// The server's Finished, as it must be.
    pub open spec fn server_finished(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        finished(verify_data(self.alg(), self.s_hs(c, host), self.th_cv(c, host)))
    }

    /// The client's Finished.
    #[verifier::opaque]
    pub open spec fn client_finished(self, c: SpecCliCfg, host: Seq<u8>) -> Seq<u8> {
        finished(verify_data(self.alg(), self.c_hs(c, host), self.th_client(c, host)))
    }

    /// Through ServerHello, the handshake followed the RFC:
    ///
    /// - ClientHello1 is `client_hello` with a fresh 32-byte random and
    ///   session id and a key share for each of the first `shares` groups;
    /// - if the server sent a HelloRetryRequest, it is one `read_sh`
    ///   takes, for the suite then used, and ClientHello2 has the one share
    ///   it asked for (or the same shares, if it asked only for the
    ///   cookie) and its cookie;
    /// - the ServerHello is one `read_sh` takes for the shares of the last
    ///   ClientHello, with this suite, group and share, and is not a
    ///   second HelloRetryRequest;
    /// - the shared secret is the key exchange of the client's share for
    ///   that group and the server's (`crypto::key_exchange`, client's
    ///   share first, as on the server's side).
    #[verifier::opaque]
    pub open spec fn sh_ok(self, c: SpecCliCfg, host: Seq<u8>) -> bool {
        &&& self.random.len() == 32
        &&& self.sid.len() == 32
        &&& share_groups(self.shares) == c.groups.take(c.shares as int)
        &&& match self.retry {
            None => true,
            Some(r) => {
                &&& is_msg(r.hrr, 2)
                &&& read_sh(c, self.sid, share_groups(self.shares), r.hrr) == Ok::<SpecShOut, u8>(
                    SpecShOut::Retry { suite: self.suite, group: r.group, cookie: r.cookie },
                )
                &&& match r.group {
                    Some(g) => r.shares.len() == 1 && r.shares[0].0 == g,
                    None => r.shares == self.shares,
                }
            },
        }
        &&& is_msg(self.sh, 2)
        &&& read_sh(c, self.sid, share_groups(self.last_shares()), self.sh) == Ok::<SpecShOut, u8>(
            SpecShOut::Hello { suite: self.suite, group: self.group, share: self.server_share },
        )
        &&& key_exchange(self.group, share_of(self.last_shares(), self.group), self.server_share, self.dhe)
    }

    /// EncryptedExtensions is one `read_ee` takes, with this ALPN
    /// protocol; a CertificateRequest, if any, one `read_cr` takes.
    #[verifier::opaque]
    pub open spec fn ee_ok(self, c: SpecCliCfg) -> bool {
        &&& is_msg(self.ee, 8)
        &&& read_ee(c, self.ee) == Ok::<Option<Seq<u8>>, u8>(self.alpn)
        &&& self.cr matches Some(m) ==> is_msg(m, 13) && read_cr(m) is Ok
    }

    /// The server's Certificate holds a chain (not empty, §4.4.2.4) that
    /// leads to a trust anchor and names `host` (`server_chain_ok`), at
    /// the time `now` the client checked it.
    #[verifier::opaque]
    pub open spec fn cert_ok(self, c: SpecCliCfg, host: Seq<u8>) -> bool {
        &&& is_msg(self.cert, 11)
        &&& parse_client_certificate(self.cert.skip(4)) == Ok::<Seq<Seq<u8>>, u8>(self.chain)
        &&& self.chain.len() > 0
        &&& server_chain_ok(self.chain, c.roots, self.now, host)
    }

    /// The server's CertificateVerify uses a scheme the client offered,
    /// and is the leaf's key's signature over §4.4.3's content (the server
    /// label) for the transcript through the Certificate.
    #[verifier::opaque]
    pub open spec fn cv_ok(self, c: SpecCliCfg, host: Seq<u8>) -> bool {
        &&& self.cv == certificate_verify(self.scheme, self.sig)
        &&& c.sigs.contains(self.scheme)
        &&& tls_signed(
            self.scheme,
            cert_of(self.chain[0]).tbs.spki,
            cv_content(hash(self.alg(), self.th_cert(c, host))),
            self.sig,
        )
    }

    /// The handshake followed the RFC, and the server is `host`: all of the
    /// above, and the server's Finished is the one §4.4.4 gives for the
    /// transcript through its CertificateVerify, under its handshake
    /// traffic secret.
    pub open spec fn valid(self, c: SpecCliCfg, host: Seq<u8>) -> bool {
        &&& self.sh_ok(c, host)
        &&& self.ee_ok(c)
        &&& self.cert_ok(c, host)
        &&& self.cv_ok(c, host)
        &&& self.sfin == self.server_finished(c, host)
    }
}

} // verus!
