//! The specification of what a TLS 1.3 server sends (RFC 8446 §4), and of
//! its record framing (§5). Trusted: read it against the RFC.
//!
//! The server this crate implements does a full handshake with a
//! certificate, no PSK, no 0-RTT and no client certificate. What it sends:
//!
//! ```text
//!   [HelloRetryRequest]   if no key share fits (§4.1.4)
//!   ServerHello
//!   {EncryptedExtensions} under the server handshake keys
//!   {Certificate}
//!   {CertificateVerify}
//!   {Finished}
//!   [application data]    under the server application keys, once the
//!                         client's Finished has been checked
//! ```
use crate::crypto::*;
use crate::spec::*;
use crate::spec_keys::*;
use vstd::prelude::*;

verus! {

/// Two bytes, big-endian.
pub open spec fn be2(n: nat) -> Seq<u8> {
    seq![((n / 256) % 256) as u8, (n % 256) as u8]
}

/// Three bytes, big-endian.
pub open spec fn be3(n: nat) -> Seq<u8> {
    seq![((n / 65536) % 256) as u8, ((n / 256) % 256) as u8, (n % 256) as u8]
}

/// A handshake message (§4): type, 24-bit length, body.
pub open spec fn hs_msg(t: u8, body: Seq<u8>) -> Seq<u8> {
    seq![t] + be3(body.len()) + body
}

/// An extension (§4.2): type, 16-bit length, data.
pub open spec fn ext(t: u16, data: Seq<u8>) -> Seq<u8> {
    be2(t as nat) + be2(data.len()) + data
}

/// The `random` of a HelloRetryRequest (§4.1.3): SHA-256 of
/// "HelloRetryRequest".
pub open spec fn hrr_random() -> Seq<u8> {
    seq![
        0xcfu8, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11, 0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8,
        0x91, 0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e, 0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8,
        0x33, 0x9c,
    ]
}

/// The body of a ServerHello (§4.1.3): legacy_version 0x0303, random,
/// legacy_session_id_echo, cipher_suite, legacy_compression_method 0,
/// extensions.
pub open spec fn server_hello_body(random: Seq<u8>, sid: Seq<u8>, suite: u16, exts: Seq<u8>) -> Seq<u8> {
    seq![3u8, 3u8] + random + seq![sid.len() as u8] + sid + be2(suite as nat) + seq![0u8] + be2(
        exts.len(),
    ) + exts
}

/// supported_versions in a ServerHello: `selected_version` 0x0304
/// (§4.2.1).
pub open spec fn ext_version() -> Seq<u8> {
    ext(43, seq![3u8, 4u8])
}

/// A ServerHello (§4.1.3) with supported_versions, and key_share with the
/// server's share for `group` (§4.2.8, `KeyShareServerHello`).
pub open spec fn server_hello(random: Seq<u8>, sid: Seq<u8>, suite: u16, group: u16, share: Seq<u8>) -> Seq<u8> {
    hs_msg(
        2,
        server_hello_body(
            random,
            sid,
            suite,
            ext_version() + ext(51, be2(group as nat) + be2(share.len()) + share),
        ),
    )
}

/// A HelloRetryRequest (§4.1.4): a ServerHello with the special random,
/// supported_versions, and key_share with `selected_group`
/// (`KeyShareHelloRetryRequest`). No cookie: the server keeps its state.
pub open spec fn hello_retry_request(sid: Seq<u8>, suite: u16, group: u16) -> Seq<u8> {
    hs_msg(2, server_hello_body(hrr_random(), sid, suite, ext_version() + ext(51, be2(group as nat))))
}

/// `message_hash` (§4.4.1): what replaces ClientHello1 in the transcript
/// after a HelloRetryRequest.
pub open spec fn message_hash(a: HashAlg, ch1: Seq<u8>) -> Seq<u8> {
    hs_msg(254, hash(a, ch1))
}

/// EncryptedExtensions (§4.3.1), with application_layer_protocol_negotiation
/// holding the one protocol chosen (RFC 7301 §3.1), if one was.
pub open spec fn encrypted_extensions(alpn: Option<Seq<u8>>) -> Seq<u8> {
    match alpn {
        None => hs_msg(8, be2(0)),
        Some(p) => {
            let e = ext(16, be2(p.len() + 1) + seq![p.len() as u8] + p);
            hs_msg(8, be2(e.len()) + e)
        },
    }
}

/// The `certificate_list` entries (§4.4.2) of a chain of DER
/// certificates, each with no extensions.
pub open spec fn cert_entries(chain: Seq<Seq<u8>>) -> Seq<u8>
    decreases chain.len(),
{
    if chain.len() == 0 {
        Seq::empty()
    } else {
        cert_entries(chain.drop_last()) + be3(chain.last().len()) + chain.last() + seq![0u8, 0u8]
    }
}

/// Certificate (§4.4.2): empty certificate_request_context, the chain.
pub open spec fn certificate(chain: Seq<Seq<u8>>) -> Seq<u8> {
    hs_msg(11, seq![0u8] + be3(cert_entries(chain).len()) + cert_entries(chain))
}

/// "TLS 1.3, server CertificateVerify"
pub open spec fn cv_label() -> Seq<u8> {
    seq![
        84u8, 76, 83, 32, 49, 46, 51, 44, 32, 115, 101, 114, 118, 101, 114, 32, 67, 101, 114, 116,
        105, 102, 105, 99, 97, 116, 101, 86, 101, 114, 105, 102, 121,
    ]
}

/// What a server's CertificateVerify signs (§4.4.3): 64 spaces, the
/// context string, a zero byte, and the transcript hash `th`.
#[verifier::opaque]
pub open spec fn cv_content(th: Seq<u8>) -> Seq<u8> {
    Seq::new(64, |i: int| 0x20u8) + cv_label() + seq![0u8] + th
}

/// CertificateVerify (§4.4.3).
pub open spec fn certificate_verify(scheme: u16, sig: Seq<u8>) -> Seq<u8> {
    hs_msg(15, be2(scheme as nat) + be2(sig.len()) + sig)
}

/// Finished (§4.4.4).
pub open spec fn finished(vd: Seq<u8>) -> Seq<u8> {
    hs_msg(20, vd)
}

/// KeyUpdate (§4.6.3); `request` 1 is update_requested.
pub open spec fn key_update(request: u8) -> Seq<u8> {
    hs_msg(24, seq![request])
}

// ---------------------------------------------------------------------------
// Cipher suites (§B.4)
// ---------------------------------------------------------------------------

/// The suites this crate runs: TLS_AES_128_GCM_SHA256,
/// TLS_AES_256_GCM_SHA384, TLS_CHACHA20_POLY1305_SHA256.
pub open spec fn known_suite(s: u16) -> bool {
    s == 0x1301 || s == 0x1302 || s == 0x1303
}

pub open spec fn suite_hash(s: u16) -> HashAlg {
    if s == 0x1302 {
        HashAlg::Sha384
    } else {
        HashAlg::Sha256
    }
}

pub open spec fn suite_key_len(s: u16) -> nat {
    if s == 0x1301 {
        16
    } else {
        32
    }
}

// ---------------------------------------------------------------------------
// Records (§5.1)
// ---------------------------------------------------------------------------

/// A plaintext record of `ct` holding `frag` (at most 2^14 bytes).
pub open spec fn plain_record(ct: u8, frag: Seq<u8>) -> Seq<u8> {
    seq![ct, 3u8, 3u8] + be2(frag.len()) + frag
}

/// The dummy change_cipher_spec record of middlebox compatibility mode
/// (Appendix D.4).
pub open spec fn ccs_record() -> Seq<u8> {
    seq![20u8, 3u8, 3u8, 0u8, 1u8, 1u8]
}

/// An alert (§6): level fatal (2), or warning (1) for close_notify.
pub open spec fn alert_body(code: u8) -> Seq<u8> {
    seq![if code == 0 { 1u8 } else { 2u8 }, code]
}

// ---------------------------------------------------------------------------
// The handshake (§2, §4)
// ---------------------------------------------------------------------------

/// A server's configuration: its preferences (as `spec::negotiate` takes
/// them) and its certificate chain.
pub struct SpecCfg {
    pub suites: Seq<u16>,
    pub groups: Seq<u16>,
    pub sigs: Seq<u16>,
    pub alpn: Seq<u8>,
    pub chain: Seq<Seq<u8>>,
}

/// Whether `m` is one handshake message of type `t` (§4).
pub open spec fn is_msg(m: Seq<u8>, t: u8) -> bool {
    m.len() >= 4 && m[0] == t && be24(m, 1) == m.len() - 4
}

/// The bytes of a span.
pub open spec fn bytes(b: Seq<u8>, sp: (int, int)) -> Seq<u8> {
    b.subrange(sp.0, sp.1)
}

/// What `spec::negotiate` makes of a ClientHello message, if it parses.
#[verifier::opaque]
pub open spec fn outcome(c: SpecCfg, ch: Seq<u8>) -> Option<SpecOutcome> {
    match parse_client_hello(ch.skip(4)) {
        Ok(s) => Some(negotiate(ch.skip(4), s, c.suites, c.groups, c.sigs, c.alpn)),
        Err(_) => None,
    }
}

/// A ClientHello message's legacy_session_id.
#[verifier::opaque]
pub open spec fn session_id(ch: Seq<u8>) -> Seq<u8> {
    match parse_client_hello(ch.skip(4)) {
        Ok(s) => bytes(ch.skip(4), s.outer.session_id),
        Err(_) => Seq::empty(),
    }
}

/// A handshake as it went: the messages, and what the server's
/// cryptography gave it (its random, its key share, the shared secret, its
/// signature).
pub struct SpecHs {
    /// ClientHello1 and the HelloRetryRequest, if there was one.
    pub retry: Option<(Seq<u8>, Seq<u8>)>,
    pub ch: Seq<u8>,
    pub choice: SpecChoice,
    pub random: Seq<u8>,
    pub share: Seq<u8>,
    pub dhe: Seq<u8>,
    pub sig: Seq<u8>,
}

impl SpecHs {
    pub open spec fn alg(self) -> HashAlg {
        suite_hash(self.choice.suite)
    }

    /// The transcript before ClientHello (§4.4.1): after a
    /// HelloRetryRequest, `message_hash` of ClientHello1, then the
    /// HelloRetryRequest.
    pub open spec fn prefix(self) -> Seq<u8> {
        match self.retry {
            None => Seq::empty(),
            Some((ch1, hrr)) => message_hash(self.alg(), ch1) + hrr,
        }
    }

    pub open spec fn server_hello(self) -> Seq<u8> {
        server_hello(
            self.random,
            session_id(self.ch),
            self.choice.suite,
            self.choice.group,
            self.share,
        )
    }

    pub open spec fn alpn(self, c: SpecCfg) -> Option<Seq<u8>> {
        match self.choice.alpn {
            None => None,
            Some((ours, _)) => Some(bytes(c.alpn, ours)),
        }
    }

    /// ClientHello..ServerHello.
    pub open spec fn th_sh(self) -> Seq<u8> {
        self.prefix() + self.ch + self.server_hello()
    }

    /// ..Certificate.
    pub open spec fn th_cert(self, c: SpecCfg) -> Seq<u8> {
        self.th_sh() + encrypted_extensions(self.alpn(c)) + certificate(c.chain)
    }

    pub open spec fn certificate_verify(self) -> Seq<u8> {
        certificate_verify(self.choice.signature_scheme, self.sig)
    }

    /// ..CertificateVerify.
    pub open spec fn th_cv(self, c: SpecCfg) -> Seq<u8> {
        self.th_cert(c) + self.certificate_verify()
    }

    pub open spec fn c_hs(self) -> Seq<u8> {
        client_hs_traffic(self.alg(), self.dhe, self.th_sh())
    }

    pub open spec fn s_hs(self) -> Seq<u8> {
        server_hs_traffic(self.alg(), self.dhe, self.th_sh())
    }

    /// The server's Finished.
    pub open spec fn server_finished(self, c: SpecCfg) -> Seq<u8> {
        finished(verify_data(self.alg(), self.s_hs(), self.th_cv(c)))
    }

    /// ..server Finished.
    pub open spec fn th_sfin(self, c: SpecCfg) -> Seq<u8> {
        self.th_cv(c) + self.server_finished(c)
    }

    /// What the server sends under its handshake keys:
    /// EncryptedExtensions, Certificate, CertificateVerify, Finished.
    pub open spec fn flight(self, c: SpecCfg) -> Seq<u8> {
        encrypted_extensions(self.alpn(c)) + certificate(c.chain) + self.certificate_verify()
            + self.server_finished(c)
    }

    /// The client's Finished, as it must be.
    pub open spec fn client_finished(self, c: SpecCfg) -> Seq<u8> {
        finished(verify_data(self.alg(), self.c_hs(), self.th_sfin(c)))
    }

    pub open spec fn c_ap(self, c: SpecCfg) -> Seq<u8> {
        client_ap_traffic(self.alg(), self.dhe, self.th_sfin(c))
    }

    pub open spec fn s_ap(self, c: SpecCfg) -> Seq<u8> {
        server_ap_traffic(self.alg(), self.dhe, self.th_sfin(c))
    }

    /// The handshake followed the RFC, given the configuration:
    ///
    /// - if there was a HelloRetryRequest, ClientHello1 negotiated a retry
    ///   (`spec::negotiate`) for this suite and group, and the
    ///   HelloRetryRequest says so, echoing ClientHello1's session id;
    /// - ClientHello negotiated `choice`, with the same suite and group as
    ///   the HelloRetryRequest if there was one (§4.1.4);
    /// - the shared secret is the key exchange of the client's share for the
    ///   group and the server's share (`crypto::key_exchange`), and the
    ///   CertificateVerify signature is over §4.4.3's content for the
    ///   transcript through Certificate (`crypto::signed`).
    #[verifier::opaque]
    pub open spec fn valid(self, c: SpecCfg) -> bool {
        &&& self.random.len() == 32
        &&& match self.retry {
            None => true,
            Some((ch1, hrr)) => is_msg(ch1, 1) && outcome(c, ch1) == Some(
                SpecOutcome::Retry { suite: self.choice.suite, group: self.choice.group },
            ) && hrr == hello_retry_request(session_id(ch1), self.choice.suite, self.choice.group),
        }
        &&& is_msg(self.ch, 1)
        &&& outcome(c, self.ch) == Some(SpecOutcome::Accept(self.choice))
        &&& key_exchange(self.choice.group, bytes(self.ch.skip(4), self.choice.share), self.share, self.dhe)
        &&& signed(
            self.choice.signature_scheme,
            cv_content(hash(self.alg(), self.th_cert(c))),
            self.sig,
        )
    }
}

/// The traffic secret after `n` KeyUpdates (§7.2).
pub open spec fn updated(a: HashAlg, s: Seq<u8>, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        s
    } else {
        next_traffic_secret(a, updated(a, s, (n - 1) as nat))
    }
}

} // verus!
