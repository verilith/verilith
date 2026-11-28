//! The server: a sans-IO TLS 1.3 server connection (§2, §4, Appendix
//! A.2), for a full handshake with a certificate.
//!
//! `ServerConn::read_record` takes one record from the client and appends
//! whatever the server sends in answer to `out`; `write` protects
//! application data. The proofs show, of every connection:
//!
//! - it is only ever in one of the states of Appendix A.2 (`Phase`), and
//!   moves between them only as the RFC allows;
//! - once `Connected`, the handshake was `SpecHs::valid` (each ClientHello
//!   negotiated, by `spec::negotiate`, exactly the parameters used; the
//!   HelloRetryRequest, if any, asked for them), and the client's Finished
//!   was exactly the one RFC 8446 defines for that transcript;
//! - everything the server sent in the handshake is exactly
//!   `spec_server.rs`'s messages, protected (§5.2) under the keys the key
//!   schedule (§7) gives for that transcript;
//! - application data is delivered only once `Connected`, and only from a
//!   record that opened under the client's application traffic keys.
use crate::client::*;
use crate::crypto::*;
use crate::ct::{ct_eq, declassify};
use crate::ech::*;
use crate::hello::*;
use crate::keys::*;
use crate::messages::*;
use crate::negotiate::*;
use crate::protect::*;
use crate::record::*;
use crate::spec::*;
use crate::spec_client::*;
use verilith_x509::spec::SpecTime;
use crate::spec_keys::*;
use crate::spec_ech::*;
use crate::spec_record::*;
use crate::spec_server::*;
use alloc::sync::Arc;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// The largest handshake message accepted, ClientHello included.
pub const MAX_MESSAGE: usize = 65536;

/// How many bytes of 0-RTT data a server that does not take it skips
/// (§4.2.10).
pub const EARLY_SKIP: usize = 65536;

/// The AlertDescription codes this module sends (§6).
pub const UNEXPECTED_MESSAGE: u8 = 10;

pub const BAD_RECORD_MAC: u8 = 20;

pub const RECORD_OVERFLOW: u8 = 22;

pub const ILLEGAL_PARAMETER: u8 = 47;

pub const DECODE_ERROR: u8 = 50;

pub const DECRYPT_ERROR: u8 = 51;

pub const INTERNAL_ERROR: u8 = 80;

pub fn suite_hash_x(s: u16) -> (r: HashAlg)
    ensures
        r == suite_hash(s),
{
    if s == 0x1302 {
        HashAlg::Sha384
    } else {
        HashAlg::Sha256
    }
}

pub fn suite_key_len_x(s: u16) -> (r: usize)
    ensures
        r == suite_key_len(s),
        r == 16 || r == 32,
{
    if s == 0x1301 {
        16
    } else {
        32
    }
}

/// A server's configuration.
pub struct Config {
    pub(crate) suites: Vec<u16>,
    pub(crate) groups: Vec<u16>,
    pub(crate) sigs: Vec<u16>,
    pub(crate) alpn: Vec<u8>,
    pub(crate) cert: Vec<u8>,
    pub(crate) chain: Ghost<Seq<Seq<u8>>>,
    /// Session tickets to send after each handshake, if the provider
    /// issues them.
    pub(crate) tickets: u8,
    /// Their lifetime, in seconds.
    pub(crate) lifetime: u32,
    /// The most 0-RTT data a ticket allows (0: no 0-RTT).
    pub(crate) max_early: u32,
    /// Client authentication, if the server asks for client certificates.
    pub(crate) client: Option<ClientAuth>,
    /// The CertificateRequest it sends then (empty otherwise).
    pub(crate) cr: Vec<u8>,
    /// The ECHConfigList the provider has keys for (empty: no ECH).
    pub(crate) ech_list: Vec<u8>,
}

/// What a server asks of clients' certificates (`spec_client.rs`).
pub struct ClientAuth {
    /// The signature schemes taken in a client's CertificateVerify.
    pub(crate) sigs: Vec<u16>,
    /// The trust anchors, DER certificates.
    pub(crate) roots: Vec<Vec<u8>>,
    /// Whether a client must send a certificate.
    pub(crate) required: bool,
}

impl ClientAuth {
    pub closed spec fn view(&self) -> SpecClientCfg {
        SpecClientCfg { sigs: self.sigs@, roots: chain_view(self.roots@), required: self.required }
    }
}

pub closed spec fn client_view(c: Option<ClientAuth>) -> Option<SpecClientCfg> {
    match c {
        Some(a) => Some(a.view()),
        None => None,
    }
}

impl Config {
    pub closed spec fn view(&self) -> SpecCfg {
        SpecCfg {
            suites: self.suites@,
            groups: self.groups@,
            sigs: self.sigs@,
            alpn: self.alpn@,
            chain: self.chain@,
            client: client_view(self.client),
            ech_list: self.ech_list@,
        }
    }

    pub closed spec fn wf(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.suites@.len() ==> known_suite(#[trigger] self.suites@[i])
        &&& self.cert@ == certificate(self.chain@)
        &&& self.cert@.len() < 0x100_0000
        &&& self.cr@ == cr_msg(self@.client)
        &&& self.cr@.len() < 0x1_0000
        &&& self.ech_list@.len() <= 4096
    }

    /// Whether the server asks clients for certificates.
    pub fn has_client_auth(&self) -> (r: bool)
        ensures
            r == (self@.client is Some),
    {
        self.client.is_some()
    }

    /// The view, field by field (for the QUIC handshake in `quic.rs`).
    pub(crate) proof fn lemma_view(&self)
        ensures
            self@.suites == self.suites@,
            self@.groups == self.groups@,
            self@.sigs == self.sigs@,
            self@.alpn == self.alpn@,
    {
    }

    /// A configuration: the cipher suites, groups and signature schemes the
    /// server takes, most preferred first; its ALPN protocols in wire form
    /// (`protocol_name_list`'s contents, empty for none); and its
    /// certificate chain, leaf first, DER. `None` if a suite is not one
    /// this crate runs, or the chain does not fit in a message.
    pub fn new(suites: Vec<u16>, groups: Vec<u16>, sigs: Vec<u16>, alpn: Vec<u8>, chain: &Vec<Vec<u8>>) -> (r:
        Option<Config>)
        ensures
            r matches Some(c) ==> c.wf() && c@ == (SpecCfg {
                suites: suites@,
                groups: groups@,
                sigs: sigs@,
                alpn: alpn@,
                chain: chain_view(chain@),
                client: None,
                ech_list: Seq::empty(),
            }),
    {
        let mut i: usize = 0;
        while i < suites.len()
            invariant
                i <= suites@.len(),
                forall|j: int| 0 <= j < i ==> known_suite(#[trigger] suites@[j]),
            decreases suites@.len() - i,
        {
            let s = suites[i];
            if !(s == 0x1301 || s == 0x1302 || s == 0x1303) {
                return None;
            }
            i = i + 1;
        }
        let cert = match certificate_x(chain) {
            Some(c) => c,
            None => return None,
        };
        proof {
            reveal(cr_msg);
        }
        Some(Config {
            suites,
            groups,
            sigs,
            alpn,
            cert,
            chain: Ghost(chain_view(chain@)),
            tickets: 2,
            lifetime: 21600,
            max_early: 0,
            client: None,
            cr: Vec::new(),
            ech_list: Vec::new(),
        })
    }

    /// Asks every client for a certificate (RFC 8446 §4.3.2) and checks the
    /// chain it sends against the trust anchors `roots` (DER certificates;
    /// `spec_client::chain_ok`) and its CertificateVerify against `sigs`,
    /// the signature schemes taken, most preferred first. With `required`,
    /// a client that sends no certificate is refused (certificate_required);
    /// without, it connects unauthenticated. While client authentication is
    /// on, the server neither resumes sessions nor issues tickets, so it
    /// takes no 0-RTT data either. `false` (and nothing changes) if `sigs`
    /// is empty or longer than 1000.
    pub fn set_client_auth(&mut self, sigs: Vec<u16>, roots: Vec<Vec<u8>>, required: bool) -> (r: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            r ==> final(self)@ == (SpecCfg {
                client: Some(SpecClientCfg { sigs: sigs@, roots: chain_view(roots@), required }),
                ..old(self)@
            }),
            !r ==> final(self)@ == old(self)@,
    {
        if sigs.len() == 0 || sigs.len() > 1000 {
            return false;
        }
        let mut cr: Vec<u8> = Vec::new();
        certificate_request_x(&mut cr, sigs.as_slice());
        assert(cr@ =~= certificate_request(sigs@));
        proof {
            reveal(cr_msg);
        }
        self.client = Some(ClientAuth { sigs, roots, required });
        self.cr = cr;
        assert(self.suites@ == old(self).suites@);
        true
    }

    /// How many session tickets to send after each handshake (2 unless
    /// set; 0 for none), and their lifetime in seconds (6 hours unless set;
    /// at most a week, §4.6.1).
    pub fn set_tickets(&mut self, count: u8, lifetime: u32)
        ensures
            final(self)@ == old(self)@,
            old(self).wf() ==> final(self).wf(),
    {
        self.tickets = count;
        self.lifetime = if lifetime > 604800 { 604800 } else { lifetime };
        assert(self.suites@ == old(self).suites@);
    }

    /// Takes up to `max` bytes of 0-RTT data on a resumption (RFC 8446
    /// §4.2.10; 0, the default, for none), and says so in the tickets it
    /// issues. Early data can be replayed: the provider's anti-replay
    /// (`Provider::claim_early`) takes each ClientHello's at most once, and
    /// the application should act on early requests only when replaying
    /// them is harmless (RFC 8470).
    /// Does Encrypted Client Hello (RFC 9849) with the provider's ECH
    /// keys: `list` is their ECHConfigList (length prefix included), sent
    /// as retry_configs to a client whose ECH the server did not accept.
    /// `false` (and no change) if it is longer than 4096 bytes.
    pub fn set_ech(&mut self, list: Vec<u8>) -> (r: bool)
        ensures
            old(self).wf() ==> final(self).wf(),
            r ==> final(self)@ == (SpecCfg { ech_list: list@, ..old(self)@ }),
            !r ==> final(self)@ == old(self)@,
    {
        if list.len() > 4096 {
            return false;
        }
        self.ech_list = list;
        true
    }

    pub fn set_early_data(&mut self, max: u32)
        ensures
            final(self)@ == old(self)@,
            old(self).wf() ==> final(self).wf(),
    {
        self.max_early = max;
        assert(self.suites@ == old(self).suites@);
    }
}

/// Where a connection is (Appendix A.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    /// Waiting for the ClientHello.
    Start,
    /// HelloRetryRequest sent: waiting for the second ClientHello.
    Retried,
    /// The server's flight sent: waiting for the client's Finished.
    WaitFinished,
    /// The handshake is over: application data both ways.
    Connected,
    /// Closed, by an alert either way or close_notify.
    Closed,
}

enum State<K: AeadKey> {
    Start,
    WaitCh2 { tr: Transcript, suite: u16, group: u16 },
    /// `tx` is under the server's application key from its Finished on,
    /// so that it can answer 0-RTT data at once ("0.5-RTT", §4.4.4);
    /// `early`, while 0-RTT data is coming, is under the client's early
    /// key, and `rx` its handshake key after that.
    WaitFinished {
        suite: u16,
        rx: Protect<K>,
        tx: Protect<K>,
        early: Option<Protect<K>>,
        expect: Secret,
        c_ap: Secret,
        s_ap: Secret,
        /// resumption_master_secret, if the server will send tickets.
        res: Option<Secret>,
    },
    /// The server asked for a certificate (client authentication): waiting
    /// for the client's Certificate, then (`got_cert`, the chain checked)
    /// its CertificateVerify. `tr` is the transcript so far; `tx` is under
    /// the server's application key, as in WaitFinished.
    WaitClientAuth {
        suite: u16,
        rx: Protect<K>,
        tx: Protect<K>,
        tr: Transcript,
        c_hs: Secret,
        c_ap: Secret,
        s_ap: Secret,
        got_cert: bool,
    },
    Connected { suite: u16, rx: Protect<K>, tx: Protect<K>, c_sec: Secret, s_sec: Secret },
    Closed,
}

/// What a record from the client came to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Event {
    /// Nothing for the caller.
    Nothing,
    /// The client's Finished checked out: application data can flow.
    HandshakeDone,
    /// Application data: the first `n` bytes of the record's body.
    Data(usize),
    /// 0-RTT application data (§4.2.10): the first `n` bytes of the
    /// record's body. It may be a replay (§8); RFC 8470 says what is safe
    /// to do with it.
    EarlyData(usize),
    /// The client sent close_notify.
    Closed,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// The server sent this alert (it is at the end of `out`) and closed.
    Sent(u8),
    /// The client sent this alert.
    Received(u8),
    /// The connection is closed.
    Closed,
    /// `out` is too long to append to.
    OutputFull,
}

/// `p` protects with the traffic key and IV of `secret` for `suite`.
pub open spec fn keys_are<K: AeadKey>(p: Protect<K>, suite: u16, secret: Seq<u8>) -> bool {
    &&& p.suite() == suite
    &&& p.key() == traffic_key(suite_hash(suite), secret, suite_key_len(suite))
    &&& p.iv() == traffic_iv(suite_hash(suite), secret)
}

pub(crate) proof fn lemma_be3(m: Seq<u8>)
    requires
        m.len() >= 4,
        be24(m, 1) == m.len() - 4,
    ensures
        m == hs_msg(m[0], m.skip(4)),
{
    let (a, b, c) = (m[1] as nat, m[2] as nat, m[3] as nat);
    let n = (a * 256 + b) * 256 + c;
    assert(n / 65536 == a && (n / 256) % 256 == b && n % 256 == c) by (nonlinear_arith)
        requires
            a < 256,
            b < 256,
            c < 256,
            n == (a * 256 + b) * 256 + c,
    ;
    assert(m =~= hs_msg(m[0], m.skip(4)));
}

/// A CertificateVerify message read as its scheme and signature.
proof fn lemma_cv_msg(m: Seq<u8>, scheme: u16, sig: Seq<u8>)
    requires
        is_msg(m, 15),
        m.len() >= 8,
        scheme as nat == m[4] as nat * 256 + m[5] as nat,
        m[6] as nat * 256 + m[7] as nat == m.len() - 8,
        sig == m.skip(8),
    ensures
        m == certificate_verify(scheme, sig),
{
    lemma_be3(m);
    let (a, b) = (m[4] as nat, m[5] as nat);
    let (c, d) = (m[6] as nat, m[7] as nat);
    assert(((a * 256 + b) / 256) % 256 == a && (a * 256 + b) % 256 == b) by (nonlinear_arith)
        requires
            a < 256,
            b < 256,
    ;
    assert(((c * 256 + d) / 256) % 256 == c && (c * 256 + d) % 256 == d) by (nonlinear_arith)
        requires
            c < 256,
            d < 256,
    ;
    assert(sig.len() == c * 256 + d);
    assert(m.skip(4) =~= be2(scheme as nat) + be2(sig.len()) + sig);
}

/// `x` is in `s`.
fn has_u16(s: &[u16], x: u16) -> (r: bool)
    ensures
        r == s@.contains(x),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            forall|j: int| 0 <= j < i ==> s@[j] != x,
        decreases s@.len() - i,
    {
        if s[i] == x {
            assert(s@[i as int] == x);
            return true;
        }
        i = i + 1;
    }
    false
}

/// A handshake with the client's answer to the CertificateRequest added:
/// everything up to the server's Finished is the same, and the client's
/// Finished covers the answer.
proof fn lemma_with_client(h: SpecHs, a: SpecClientAuth, c: SpecCfg)
    ensures
        ({
            let h2 = SpecHs { client: Some(a), ..h };
            &&& h2.valid(c) == h.valid(c)
            &&& h2.alg() == h.alg()
            &&& h2.c_hs() == h.c_hs()
            &&& h2.s_hs() == h.s_hs()
            &&& h2.c_ap(c) == h.c_ap(c)
            &&& h2.s_ap(c) == h.s_ap(c)
            &&& h2.c_early() == h.c_early()
            &&& h2.th_sfin(c) == h.th_sfin(c)
            &&& h2.th_eoed(c) == h.th_eoed(c)
            &&& h2.client_finished(c) == finished(verify_data(h.alg(), h.c_hs(), h.th_eoed(c) + a.msgs()))
            &&& h2.client_ok(c) == (c.client matches Some(cc) && a.ok(cc, h.alg(), h.th_eoed(c)))
        }),
{
    reveal(SpecHs::early_ok);
    reveal(SpecHs::th_eoed);
    reveal(SpecHs::c_early);
    reveal(SpecHs::valid);
    reveal(SpecHs::resume_ok);
    reveal(SpecHs::server_hello);
    reveal(SpecHs::th_sh);
    reveal(SpecHs::th_cert);
    reveal(SpecHs::th_cv);
    reveal(SpecHs::c_hs);
    reveal(SpecHs::s_hs);
    reveal(SpecHs::server_finished);
    reveal(SpecHs::th_sfin);
    reveal(SpecHs::client_finished);
    reveal(SpecHs::th_client);
    reveal(SpecHs::client_ok);
    reveal(SpecHs::c_ap);
    reveal(SpecHs::s_ap);
    reveal(SpecHs::ech_ok);
}

/// A handshake message of a short enough body is one.
pub(crate) proof fn lemma_is_msg(t: u8, b: Seq<u8>)
    requires
        b.len() < 0x100_0000,
    ensures
        is_msg(hs_msg(t, b), t),
{
    let n = b.len();
    let m = hs_msg(t, b);
    let (x, y, z) = ((n / 65536) % 256, (n / 256) % 256, n % 256);
    assert((x * 256 + y) * 256 + z == n) by (nonlinear_arith)
        requires
            n < 0x100_0000,
            x == (n / 65536) % 256,
            y == (n / 256) % 256,
            z == n % 256,
    ;
    assert(m[1] as nat == x && m[2] as nat == y && m[3] as nat == z);
}

/// The handshake traffic secrets and keys for PSK `psk`, shared secret
/// `dhe` and transcript `th_sh` (ClientHello..ServerHello), whose hash is
/// `th`.
fn hs_keys(suite: u16, psk: &[u8], dhe: &[u8], th: &Secret, Ghost(th_sh): Ghost<Seq<u8>>) -> (r: (
    Secret,
    Secret,
    Secret,
))
    requires
        th.wf(),
        th@ == hash(suite_hash(suite), th_sh),
        th@.len() == hash_len(suite_hash(suite)),
    ensures
        r.0.wf() && r.0@ == handshake_secret(suite_hash(suite), psk@, dhe@),
        r.1.wf() && r.1@ == client_hs_traffic(suite_hash(suite), psk@, dhe@, th_sh),
        r.2.wf() && r.2@ == server_hs_traffic(suite_hash(suite), psk@, dhe@, th_sh),
{
    let a = suite_hash_x(suite);
    let hs = handshake_secret_x(a, psk, dhe);
    let (c_hs, s_hs) = hs_traffic_x(a, &hs, th, Ghost(psk@), Ghost(dhe@), Ghost(th_sh));
    (hs, c_hs, s_hs)
}

/// Record protection with the traffic key and IV of `sec`, from sequence
/// number 0.
fn protect_of<P: Provider>(prov: &P, suite: u16, sec: &Secret) -> (r: Protect<P::Key>)
    requires
        sec.wf(),
    ensures
        keys_are(r, suite, sec@),
        r.seq() == 0,
{
    let a = suite_hash_x(suite);
    let kl = suite_key_len_x(suite);
    let (k, iv) = traffic_keys_x(a, sec, kl);
    Protect::new(prov.aead_key(suite, k.as_slice()), &iv)
}

/// The server's flight after ServerHello: EncryptedExtensions,
/// Certificate, CertificateVerify (signed by `prov`) and Finished, added
/// to the transcript as they are made.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn server_flight<P: Provider>(
    prov: &mut P,
    cfg: &Config,
    scheme: u16,
    alpn: Option<&[u8]>,
    tp: Option<&[u8]>,
    early: bool,
    retry: Option<&[u8]>,
    tr: &mut Transcript,
    s_hs: &Secret,
) -> (r: Option<(Vec<u8>, Ghost<Seq<u8>>)>)
    requires
        cfg.wf(),
        old(tr).wf(),
        s_hs.wf(),
        alpn matches Some(p) ==> p@.len() <= 255,
        tp matches Some(t) ==> t@.len() <= 60000,
        retry matches Some(l) ==> l@.len() <= 4096,
    ensures
        final(tr).wf(),
        final(tr).alg() == old(tr).alg(),
        r matches Some((fl, sig)) ==> {
            let a = old(tr).alg();
            let ee = encrypted_extensions(
                opt_view(alpn),
                opt_view(tp),
                early,
                opt_view(retry),
            );
            let cr = cr_msg(cfg@.client);
            let cert = certificate(cfg@.chain);
            let th_cert = old(tr).data() + ee + cr + cert;
            let cv = certificate_verify(scheme, sig@);
            let sf = finished(verify_data(a, s_hs@, th_cert + cv));
            &&& signed(scheme, cv_content(hash(a, th_cert)), sig@)
            &&& fl@ == ee + cr + cert + cv + sf
            &&& final(tr).data() == th_cert + cv + sf
            &&& fl@.len() < 0x100_0000 + 0x4_0000
        },
{
    let a = tr.alg_x();
    let ghost t0 = tr.data();
    let mut fl: Vec<u8> = Vec::new();
    encrypted_extensions_x(&mut fl, alpn, tp, early, retry);
    let ghost ee = fl@;
    if cfg.cr.len() > 0 {
        put(&mut fl, cfg.cr.as_slice());
    }
    proof {
        assert(fl@ =~= ee + cfg.cr@);
    }
    put(&mut fl, cfg.cert.as_slice());
    tr.update(fl.as_slice());
    let ghost th_cert = tr.data();
    let th2 = tr.hash();
    let mut cvc: Vec<u8> = Vec::new();
    cv_content_x(&mut cvc, &th2);
    let mut sig: Vec<u8> = Vec::new();
    if !prov.sign(scheme, cvc.as_slice(), &mut sig) {
        return None;
    }
    if sig.len() > 65531 {
        return None;
    }
    proof {
        assert(sig@.skip(0) =~= sig@);
        assert(th_cert =~= t0 + ee + cfg.cr@ + cfg.cert@);
    }
    let mut cv: Vec<u8> = Vec::new();
    certificate_verify_x(&mut cv, scheme, sig.as_slice());
    tr.update(cv.as_slice());
    let ghost th_cv = tr.data();
    let th3 = tr.hash();
    let svd = verify_data_x(a, s_hs, &th3, Ghost(th_cv));
    let mut sf: Vec<u8> = Vec::new();
    finished_x(&mut sf, &svd);
    tr.update(sf.as_slice());
    put(&mut fl, cv.as_slice());
    put(&mut fl, sf.as_slice());
    proof {
        assert(fl@ =~= ee + cfg.cr@ + cfg.cert@ + cv@ + sf@);
        assert(tr.data() =~= th_cert + cv@ + sf@);
    }
    Some((fl, Ghost(sig@)))
}

/// The server's flight when resuming: EncryptedExtensions and Finished.
fn resumed_flight(alpn: Option<&[u8]>, tp: Option<&[u8]>, early: bool, retry: Option<&[u8]>, tr: &mut Transcript, s_hs: &Secret) -> (r: Vec<u8>)
    requires
        old(tr).wf(),
        s_hs.wf(),
        alpn matches Some(p) ==> p@.len() <= 255,
        tp matches Some(t) ==> t@.len() <= 60000,
        retry matches Some(l) ==> l@.len() <= 4096,
    ensures
        final(tr).wf(),
        final(tr).alg() == old(tr).alg(),
        ({
            let a = old(tr).alg();
            let ee = encrypted_extensions(
                opt_view(alpn),
                opt_view(tp),
                early,
                opt_view(retry),
            );
            let sf = finished(verify_data(a, s_hs@, old(tr).data() + ee));
            &&& r@ == ee + sf
            &&& final(tr).data() == old(tr).data() + ee + sf
            &&& r@.len() < 0x1_0000
        }),
{
    let a = tr.alg_x();
    let ghost t0 = tr.data();
    let mut fl: Vec<u8> = Vec::new();
    encrypted_extensions_x(&mut fl, alpn, tp, early, retry);
    let ghost ee = fl@;
    tr.update(fl.as_slice());
    let th = tr.hash();
    let svd = verify_data_x(a, s_hs, &th, Ghost(tr.data()));
    let mut sf: Vec<u8> = Vec::new();
    finished_x(&mut sf, &svd);
    tr.update(sf.as_slice());
    put(&mut fl, sf.as_slice());
    proof {
        assert(fl@ =~= ee + sf@);
        assert(tr.data() =~= t0 + ee + sf@);
    }
    fl
}

/// The resumed handshake's flight `fl`, as `resumed_flight` makes it.
#[verifier::opaque]
pub open spec fn short_flight(a: HashAlg, th_sh: Seq<u8>, th_sfin: Seq<u8>, fl: Seq<u8>, ee: Seq<u8>, s_hs: Seq<u8>) -> bool {
    let sf = finished(verify_data(a, s_hs, th_sh + ee));
    &&& fl == ee + sf
    &&& th_sfin == th_sh + ee + sf
}

proof fn lemma_short_flight(cc: SpecCfg, h: SpecHs, a: HashAlg, th_sh: Seq<u8>, th_sfin: Seq<u8>, fl: Seq<u8>, ee: Seq<u8>, s_hs: Seq<u8>)
    requires
        a == h.alg(),
        ee == h.ee(cc),
        s_hs == server_hs_traffic(h.alg(), h.psk(), h.dhe, th_sh),
        short_flight(a, th_sh, th_sfin, fl, ee, s_hs),
    ensures
        ({
            let a = h.alg();
            let ee = h.ee(cc);
            let sf = finished(verify_data(a, server_hs_traffic(a, h.psk(), h.dhe, th_sh), th_sh + ee));
            &&& fl == ee + sf
            &&& th_sfin == th_sh + ee + sf
        }),
{
    reveal(short_flight);
}

/// The full handshake's flight `fl`, as `server_flight` makes it: after
/// `th_sh`, EncryptedExtensions `ee`, the CertificateRequest if any,
/// Certificate, CertificateVerify (`sig` with `scheme`) and Finished, the
/// transcript then `th_sfin`.
#[verifier::opaque]
pub open spec fn full_flight(cc: SpecCfg, a: HashAlg, scheme: u16, sig: Seq<u8>, th_sh: Seq<u8>, th_sfin: Seq<u8>, fl: Seq<u8>, ee: Seq<u8>, s_hs: Seq<u8>) -> bool {
    let cr = cr_msg(cc.client);
    let cert = certificate(cc.chain);
    let th_cert = th_sh + ee + cr + cert;
    let cv = certificate_verify(scheme, sig);
    let sf = finished(verify_data(a, s_hs, th_cert + cv));
    &&& signed(scheme, cv_content(hash(a, th_cert)), sig)
    &&& fl == ee + cr + cert + cv + sf
    &&& th_sfin == th_cert + cv + sf
}

/// The full handshake's flight, as `server_flight` made it, in the terms
/// of the handshake `h` (kept apart from `prepare`, whose context is large).
proof fn lemma_full_flight(
    cc: SpecCfg,
    h: SpecHs,
    a: HashAlg,
    scheme: u16,
    sig: Seq<u8>,
    th_sh: Seq<u8>,
    th_sfin: Seq<u8>,
    fl: Seq<u8>,
    ee: Seq<u8>,
    s_hs: Seq<u8>,
)
    requires
        a == h.alg(),
        scheme == h.choice.signature_scheme,
        sig == h.sig,
        ee == h.ee(cc),
        s_hs == server_hs_traffic(h.alg(), h.psk(), h.dhe, th_sh),
        full_flight(cc, a, scheme, sig, th_sh, th_sfin, fl, ee, s_hs),
    ensures
        ({
            let a = h.alg();
            let ee = h.ee(cc);
            let cert = certificate(cc.chain);
            let th_cert = th_sh + ee + cr_msg(cc.client) + cert;
            let cv = certificate_verify(h.choice.signature_scheme, h.sig);
            let sf = finished(verify_data(a, server_hs_traffic(a, h.psk(), h.dhe, th_sh), th_cert + cv));
            &&& signed(h.choice.signature_scheme, cv_content(hash(a, th_cert)), h.sig)
            &&& fl == ee + cr_msg(cc.client) + cert + cv + sf
            &&& th_sfin == th_cert + cv + sf
        }),
{
    reveal(full_flight);
}

/// The handshake `accept` made is valid, and its messages and secrets are
/// `SpecHs`'s.
#[verifier::spinoff_prover]
proof fn lemma_accept_spec(
    cc: SpecCfg,
    hsv: SpecHs,
    m: Seq<u8>,
    pre: Seq<u8>,
    sh: Seq<u8>,
    th_sh: Seq<u8>,
    th_sfin: Seq<u8>,
    fl: Seq<u8>,
    peer: Seq<u8>,
    alpn: Option<&[u8]>,
    sid: Seq<u8>,
)
    requires
        hsv.ch == m,
        hsv.random.len() == 32,
        is_msg(m, 1),
        outcome(cc, m) == Some(SpecOutcome::Accept(hsv.choice)),
        match hsv.retry {
            None => true,
            Some((ch1, hrr)) => is_msg(ch1, 1) && outcome(cc, ch1) == Some(
                SpecOutcome::Retry { suite: hsv.choice.suite, group: hsv.choice.group },
            ) && hrr == hello_retry_request(session_id(ch1), hsv.choice.suite, hsv.choice.group),
        },
        pre == match hsv.retry {
            None => Seq::<u8>::empty(),
            Some((ch1, hrr)) => message_hash(hsv.alg(), ch1) + hrr,
        },
        match hsv.resumed {
            None => true,
            Some(r) => resumption_ok(m, pre, hsv.alg(), r),
        },
        peer == bytes(m.skip(4), hsv.choice.share),
        key_exchange(hsv.choice.group, peer, hsv.share, hsv.dhe),
        sid == session_id(m),
        sh == server_hello(hsv.random, sid, hsv.choice.suite, hsv.choice.group, hsv.share, hsv.resumed is Some),
        th_sh == pre + m + sh,
        hsv.alpn(cc) == opt_view(alpn),
        hsv.early ==> early_allowed(cc, m, hsv.retry, hsv.choice, hsv.resumed),
        hsv.client is None,
        cc.client is Some ==> hsv.resumed is None,
        hsv.ech_ok(cc),
        hsv.resumed is None ==> ({
            let a = hsv.alg();
            let ee = hsv.ee(cc);
            let cert = certificate(cc.chain);
            let th_cert = th_sh + ee + cr_msg(cc.client) + cert;
            let cv = certificate_verify(hsv.choice.signature_scheme, hsv.sig);
            let sf = finished(verify_data(a, server_hs_traffic(a, hsv.psk(), hsv.dhe, th_sh), th_cert + cv));
            &&& signed(hsv.choice.signature_scheme, cv_content(hash(a, th_cert)), hsv.sig)
            &&& fl == ee + cr_msg(cc.client) + cert + cv + sf
            &&& th_sfin == th_cert + cv + sf
        }),
        hsv.resumed is Some ==> ({
            let a = hsv.alg();
            let ee = hsv.ee(cc);
            let sf = finished(verify_data(a, server_hs_traffic(a, hsv.psk(), hsv.dhe, th_sh), th_sh + ee));
            &&& fl == ee + sf
            &&& th_sfin == th_sh + ee + sf
        }),
    ensures
        hsv.valid(cc),
        sh == hsv.server_hello(),
        th_sh == hsv.th_sh(),
        th_sfin == hsv.th_sfin(cc),
        fl == hsv.flight(cc),
        hsv.c_hs() == client_hs_traffic(hsv.alg(), hsv.psk(), hsv.dhe, th_sh),
        hsv.s_hs() == server_hs_traffic(hsv.alg(), hsv.psk(), hsv.dhe, th_sh),
        hsv.th_eoed(cc) == (if hsv.early { th_sfin + end_of_early_data() } else { th_sfin }),
        hsv.th_client(cc) == hsv.th_eoed(cc),
        hsv.client_ok(cc) == (cc.client is None),
        hsv.client_finished(cc) == finished(verify_data(hsv.alg(), client_hs_traffic(hsv.alg(), hsv.psk(), hsv.dhe, th_sh), hsv.th_eoed(cc))),
        hsv.c_ap(cc) == client_ap_traffic(hsv.alg(), hsv.psk(), hsv.dhe, th_sfin),
        hsv.s_ap(cc) == server_ap_traffic(hsv.alg(), hsv.psk(), hsv.dhe, th_sfin),
        hsv.res_master(cc) == resumption_master(hsv.alg(), hsv.psk(), hsv.dhe, hsv.th_eoed(cc) + hsv.client_finished(cc)),
        hsv.c_early() == client_early_traffic(hsv.alg(), hsv.psk(), m),
{
    reveal(SpecHs::early_ok);
    reveal(SpecHs::th_eoed);
    reveal(SpecHs::c_early);
    reveal(SpecHs::valid);
    reveal(SpecHs::resume_ok);
    reveal(SpecHs::server_hello);
    reveal(SpecHs::th_sh);
    reveal(SpecHs::th_cert);
    reveal(SpecHs::th_cv);
    reveal(SpecHs::c_hs);
    reveal(SpecHs::s_hs);
    reveal(SpecHs::server_finished);
    reveal(SpecHs::th_sfin);
    reveal(SpecHs::flight);
    reveal(SpecHs::client_finished);
    reveal(SpecHs::c_ap);
    reveal(SpecHs::s_ap);
    reveal(SpecHs::res_master);
    reveal(SpecHs::th_client);
    reveal(SpecHs::client_ok);
    assert(hsv.client_msgs() =~= Seq::<u8>::empty());
    assert(hsv.th_client(cc) =~= hsv.th_eoed(cc));
    assert(th_sh == hsv.th_sh());
    assert(pre == hsv.prefix());
    if hsv.resumed is None {
        let th_cert = th_sh + hsv.ee(cc) + cr_msg(cc.client) + certificate(cc.chain);
        assert(th_cert == hsv.th_cert(cc));
        assert(th_cert + hsv.certificate_verify() == hsv.th_cv(cc));
    } else {
        assert(th_sh + hsv.ee(cc) == hsv.th_cv(cc));
    }
    assert(th_sfin =~= hsv.th_sfin(cc));
    assert(fl =~= hsv.flight(cc));
}

/// What `accept` sends and keeps, computed before anything is sent.
pub(crate) struct Prep {
    pub(crate) sh: Vec<u8>,
    pub(crate) fl: Vec<u8>,
    /// The client's and the server's handshake traffic secrets.
    pub(crate) c_hs: Secret,
    pub(crate) s_hs: Secret,
    pub(crate) expect: Secret,
    pub(crate) c_ap: Secret,
    pub(crate) s_ap: Secret,
    pub(crate) res: Option<Secret>,
    /// client_early_traffic_secret, when 0-RTT data is taken.
    pub(crate) c_early: Option<Secret>,
    /// The transcript through the server's Finished, for the client's
    /// Certificate and CertificateVerify to follow.
    pub(crate) tr: Transcript,
    pub(crate) hs: Ghost<SpecHs>,
}

#[verifier::opaque]
pub(crate) open spec fn prep_ok(
    p: Prep,
    cc: SpecCfg,
    m: Seq<u8>,
    retry: Option<(Seq<u8>, Seq<u8>)>,
    choice: SpecChoice,
    resumed: Option<SpecResume>,
    tp: Option<Seq<u8>>,
    early: bool,
    ech: Option<(Seq<u8>, Seq<u8>)>,
    ech_retry: bool,
) -> bool {
    let h = p.hs@;
    &&& h.valid(cc)
    &&& h.early == early
    &&& h.ech == ech
    &&& h.ech_retry == ech_retry
    &&& p.c_early is Some == early
    &&& p.c_early matches Some(k) ==> k.wf() && k@ == h.c_early()
    &&& h.retry == retry
    &&& h.resumed == resumed
    &&& h.ch == m
    &&& h.choice == choice
    &&& h.tp == tp
    &&& h.client is None
    &&& p.tr.wf() && p.tr.alg() == suite_hash(choice.suite) && p.tr.data() == h.th_sfin(cc)
    &&& p.sh@ == h.server_hello()
    &&& p.sh@.len() < 65536
    &&& p.fl@ == h.flight(cc)
    &&& p.fl@.len() < 0x100_0000 + 0x4_0000
    &&& p.c_hs.wf() && p.c_hs@ == h.c_hs()
    &&& p.s_hs.wf() && p.s_hs@ == h.s_hs()
    &&& p.expect.wf() && finished(p.expect@) == h.client_finished(cc)
    &&& p.expect@.len() == hash_len(suite_hash(choice.suite))
    &&& p.c_ap.wf() && p.c_ap@ == h.c_ap(cc)
    &&& p.s_ap.wf() && p.s_ap@ == h.s_ap(cc)
    &&& p.res matches Some(rm) ==> rm.wf() && rm@ == h.res_master(cc)
}

/// The server's side of the key exchange, its random, and ServerHello.
fn exchange<P: Provider>(prov: &mut P, peer: &[u8], sid: &[u8], suite: u16, group: u16, psk: bool, zero_tail: bool) -> (r: Result<
    (Vec<u8>, [u8; 64], usize, [u8; 32], Vec<u8>),
    u8,
>)
    requires
        sid@.len() <= 32,
    ensures
        r matches Ok((share, shared, dn, random, sh)) ==> {
            &&& dn <= 64
            &&& key_exchange(group, peer@, share@, shared@.take(dn as int))
            &&& sh@ == server_hello(random@, sid@, suite, group, share@, psk)
            &&& sh@.len() < 65536
            &&& share@.len() <= 16000
            &&& zero_tail ==> random@.skip(24) == zeros(8)
        },
{
    let mut share: Vec<u8> = Vec::new();
    let mut shared = [0u8; 64];
    let dn = match prov.key_exchange(group, peer, &mut share, &mut shared) {
        Some(n) => n,
        None => return Err(ILLEGAL_PARAMETER),
    };
    if share.len() > 16000 {
        return Err(INTERNAL_ERROR);
    }
    assert(share@.skip(0) =~= share@);
    let mut random = [0u8; 32];
    prov.random(&mut random);
    if zero_tail {
        // ECH: the last 8 bytes become the acceptance confirmation, over
        // a ServerHello with them zero (RFC 9849 §7.2).
        let mut k: usize = 24;
        while k < 32
            invariant
                24 <= k <= 32,
                forall|j: int| 24 <= j < k ==> random@[j] == 0,
            decreases 32 - k,
        {
            random[k] = 0;
            k = k + 1;
        }
        assert(random@.skip(24) =~= zeros(8));
    }
    let mut sh: Vec<u8> = Vec::new();
    server_hello_x(&mut sh, &random, sid, suite, group, share.as_slice(), psk);
    Ok((share, shared, dn, random, sh))
}

/// The client's 0-RTT traffic secret over transcript `tr`, when `early`.
fn early_key(a: HashAlg, pk: &Secret, tr: &Transcript, early: bool) -> (r: Option<Secret>)
    requires
        pk.wf(),
        tr.wf(),
        tr.alg() == a,
    ensures
        r is Some == early,
        r matches Some(k) ==> k.wf() && k@ == client_early_traffic(a, pk@, tr.data()),
{
    if early {
        let th_ch = tr.hash();
        Some(early_traffic_x(a, pk.as_slice(), &th_ch, Ghost(tr.data())))
    } else {
        None
    }
}

/// Adds the EndOfEarlyData message to `tr`, when `early`.
fn eoed_update(tr: &mut Transcript, early: bool)
    requires
        old(tr).wf(),
    ensures
        final(tr).wf(),
        final(tr).alg() == old(tr).alg(),
        final(tr).data() == if early { old(tr).data() + end_of_early_data() } else { old(tr).data() },
{
    if early {
        let eoed: [u8; 4] = [5, 0, 0, 0];
        proof {
            assert(eoed@ =~= end_of_early_data());
        }
        tr.update(&eoed);
    }
}

/// The keys after the server's Finished, over transcript `tr` (to it):
/// the application traffic secrets; the client Finished's verify_data,
/// over EndOfEarlyData too if `early` (§4.4.1); and, if `res`, the
/// resumption master secret.
fn late_keys(
    a: HashAlg,
    hs: &Secret,
    c_hs: &Secret,
    Ghost(psk): Ghost<Seq<u8>>,
    Ghost(dhe): Ghost<Seq<u8>>,
    tr: Transcript,
    early: bool,
    res: bool,
) -> (r: (Secret, Secret, Secret, Option<Secret>))
    requires
        hs.wf(),
        hs@ == handshake_secret(a, psk, dhe),
        c_hs.wf(),
        tr.wf(),
        tr.alg() == a,
    ensures
        ({
            let (c_ap, s_ap, expect, rm) = r;
            let te = if early { tr.data() + end_of_early_data() } else { tr.data() };
            &&& c_ap.wf() && c_ap@ == client_ap_traffic(a, psk, dhe, tr.data())
            &&& s_ap.wf() && s_ap@ == server_ap_traffic(a, psk, dhe, tr.data())
            &&& expect.wf() && expect@ == verify_data(a, c_hs@, te)
            &&& expect@.len() == hash_len(a)
            &&& rm is Some == res
            &&& rm matches Some(k) ==> k.wf() && k@ == resumption_master(a, psk, dhe, te + finished(expect@))
        }),
{
    let mut tr = tr;
    let th4 = tr.hash();
    let ms = master_secret_x(a, hs, Ghost(psk), Ghost(dhe));
    let (c_ap, s_ap, _exp) = ap_traffic_x(a, &ms, &th4, Ghost(psk), Ghost(dhe), Ghost(tr.data()));
    eoed_update(&mut tr, early);
    let th4e = tr.hash();
    let expect = verify_data_x(a, c_hs, &th4e, Ghost(tr.data()));
    let rm = if res {
        let mut cf: Vec<u8> = Vec::new();
        finished_x(&mut cf, &expect);
        assert(cf@ =~= finished(expect@));
        tr.update(cf.as_slice());
        let th5 = tr.hash();
        Some(resumption_master_x(a, &ms, &th5, Ghost(psk), Ghost(dhe), Ghost(tr.data())))
    } else {
        None
    };
    (c_ap, s_ap, expect, rm)
}

/// ClientHelloInner says it is one: it was decrypted (§7.1).
proof fn lemma_ech_inner(m: Seq<u8>, pt: Seq<u8>, im: Seq<u8>, s: SpecHello)
    requires
        ech_unsealed(m, pt, im),
        parse_client_hello(im.skip(4)) == Ok::<SpecHello, SpecAlert>(s),
        s.ech matches Some((a, b)) && ech_inner(im.skip(4), a, b),
    ensures
        ech_decrypted(m, pt, im),
{
    reveal(ech_decrypted);
}

proof fn lemma_ech_ok(cc: SpecCfg, hsv: SpecHs, m: Seq<u8>, random0: Seq<u8>, sh0: Seq<u8>, sid: Seq<u8>)
    requires
        hsv.ch == m,
        sid == session_id(m),
        hsv.ech matches Some((outer, pt)) ==> {
            &&& hsv.retry is None
            &&& ech_decrypted(outer, pt, m)
            &&& cc.ech_list.len() > 0
            &&& !hsv.ech_retry
            &&& hsv.random.take(24) + zeros(8) == random0
            &&& hsv.random.skip(24) == ech_confirm(hsv.alg(), m.subrange(6, 38), m + sh0)
            &&& sh0 == server_hello(random0, sid, hsv.choice.suite, hsv.choice.group, hsv.share, hsv.resumed is Some)
        },
        hsv.ech_retry ==> hsv.ech is None && cc.ech_list.len() > 0 && (parse_client_hello(m.skip(4)) matches Ok(s) && s.ech is Some),
    ensures
        hsv.ech_ok(cc),
{
    reveal(SpecHs::ech_ok);
}

/// ECH accepted: ServerHello.random's last 8 bytes, zero in `random`,
/// become the acceptance confirmation over ClientHelloInner `m` and the
/// ServerHello `sh` with them zero (RFC 9849 §7.2); and that ServerHello
/// again with the new random.
fn ech_finish(a: HashAlg, m: &[u8], random: [u8; 32], sh: &Vec<u8>, sid: &[u8], suite: u16, group: u16, share: &[u8], psk: bool) -> (r: Option<([u8; 32], Vec<u8>)>)
    requires
        sid@.len() <= 32,
        share@.len() <= 16000,
        random@.skip(24) == zeros(8),
        sh@ == server_hello(random@, sid@, suite, group, share@, psk),
    ensures
        r matches Some((r2, sh2)) ==> {
            &&& r2@.take(24) + zeros(8) == random@
            &&& r2@.skip(24) == ech_confirm(a, m@.subrange(6, 38), m@ + sh@)
            &&& sh2@ == server_hello(r2@, sid@, suite, group, share@, psk)
            &&& sh2@.len() < 65536
        },
{
    if m.len() < 38 {
        return None;
    }
    let mut t2 = Transcript::new(a);
    t2.update(m);
    t2.update(sh.as_slice());
    let th = t2.hash();
    proof {
        assert(Seq::<u8>::empty() + m@ + sh@ =~= m@ + sh@);
        assert(hash_len(a) <= 255);
    }
    let conf = ech_confirm_x(a, vstd::slice::slice_subrange(m, 6, 38), &th, Ghost(m@ + sh@));
    let cs = conf.as_slice();
    let mut r2 = random;
    let mut k: usize = 0;
    while k < 8
        invariant
            k <= 8,
            cs@.len() == 8,
            forall|j: int| 0 <= j < 24 ==> r2@[j] == random@[j],
            forall|j: int| 0 <= j < k ==> r2@[24 + j] == cs@[j],
        decreases 8 - k,
    {
        r2[24 + k] = cs[k];
        k = k + 1;
    }
    proof {
        assert(r2@.take(24) + zeros(8) =~= random@);
        assert(r2@.skip(24) =~= cs@);
    }
    let mut sh2: Vec<u8> = Vec::new();
    server_hello_x(&mut sh2, &r2, sid, suite, group, share, psk);
    Some((r2, sh2))
}

/// ECH (RFC 9849 §7.1) on ClientHelloOuter `body`: `Ok(None)` if the
/// server's keys do not open it (ECH declined), else ClientHelloInner
/// (a message) and the EncodedClientHelloInner it was decoded from;
/// `Err` with the alert for a malformed extension or inner.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn open_ech<P: Provider>(prov: &mut P, m: &[u8], body: &[u8], h: &ClientHello, Ghost(s): Ghost<SpecHello>) -> (r: Result<Option<(Vec<u8>, Ghost<Seq<u8>>)>, u8>)
    requires
        is_msg(m@, 1),
        body@ == m@.skip(4),
        parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s),
        h.models(s),
    ensures
        r matches Ok(Some((inner, pt))) ==> ech_unsealed(m@, pt@, inner@) && is_msg(inner@, 1),
{
    let sp = match h.ech {
        Some(sp) => sp,
        None => return Err(INTERNAL_ERROR),
    };
    if !(sp.start < sp.end && sp.end <= body.len()) {
        return Err(DECODE_ERROR);
    }
    let xs = h.extensions;
    let sid = h.session_id;
    if !(xs.start <= xs.end && xs.end <= body.len() && sid.start <= sid.end && sid.end <= body.len()) {
        return Err(INTERNAL_ERROR);
    }
    if body[sp.start] != 0 {
        // An inner ECHClientHello in ClientHelloOuter (§7.1).
        return Err(ILLEGAL_PARAMETER);
    }
    let eo = match ech_outer_x(body, sp.start, sp.end) {
        Some(x) => x,
        None => return Err(DECODE_ERROR),
    };
    let aad = outer_aad_x(body, eo.payload);
    let mut pt: Vec<u8> = Vec::new();
    if !prov.ech_open(eo.config_id, eo.kdf, eo.aead, eo.enc.of(body), aad.as_slice(), eo.payload.of(body), &mut pt) {
        return Ok(None);
    }
    proof {
        assert(parse_exts(body@, xs.start as int, xs.end as int) == Some(s.outer.exts));
    }
    let ib = match decode_inner_x(pt.as_slice(), body, xs.start, xs.end, sid, Ghost(s.outer.exts)) {
        Some(v) => v,
        None => return Err(ILLEGAL_PARAMETER),
    };
    if ib.len() >= 0x10000 {
        return Err(ILLEGAL_PARAMETER);
    }
    let mut inner: Vec<u8> = Vec::with_capacity(ib.len() + 4);
    put1(&mut inner, 1);
    put3(&mut inner, ib.len());
    put(&mut inner, ib.as_slice());
    proof {
        assert(inner@ =~= hs_msg(1, ib@));
        assert(inner@.skip(4) =~= ib@);
        lemma_is_msg(1, ib@);
        reveal(ech_unsealed);
    }
    // The inner must say it is one (§7.1), else illegal_parameter;
    // checked by the caller once it is parsed.
    Ok(Some((inner, Ghost(pt@))))
}

#[verifier::spinoff_prover]
#[verifier::rlimit(1000)]
pub(crate) fn prepare<P: Provider>(
    prov: &mut P,
    cfg: &Config,
    m: &[u8],
    body: &[u8],
    sid: &[u8],
    c: Choice,
    tr: Transcript,
    Ghost(retry): Ghost<Option<(Seq<u8>, Seq<u8>)>>,
    Ghost(choice): Ghost<SpecChoice>,
    psk: Option<Secret>,
    Ghost(resumed): Ghost<Option<SpecResume>>,
    tp: Option<&[u8]>,
    early: bool,
    Ghost(ech): Ghost<Option<(Seq<u8>, Seq<u8>)>>,
    ech_on: bool,
    ech_retry: bool,
) -> (r: Result<Prep, u8>)
        requires
            cfg.wf(),
            is_msg(m@, 1),
            body@ == m@.skip(4),
            sid@ == session_id(m@),
            sid@.len() <= 32,
            known_suite(c.suite),
            choice.suite == c.suite && choice.group == c.group && choice.share == c.share@
                && choice.signature_scheme == c.signature_scheme && choice.alpn == ov2(c.alpn),
            outcome(cfg@, m@) == Some(SpecOutcome::Accept(choice)),
            match retry {
                None => true,
                Some((ch1, hrr)) => is_msg(ch1, 1) && outcome(cfg@, ch1) == Some(
                    SpecOutcome::Retry { suite: c.suite, group: c.group },
                ) && hrr == hello_retry_request(session_id(ch1), c.suite, c.group),
            },
            tr.wf(),
            tr.alg() == suite_hash(c.suite),
            tr.data() == match retry {
                None => Seq::<u8>::empty(),
                Some((ch1, hrr)) => message_hash(suite_hash(c.suite), ch1) + hrr,
            },
            psk is Some == resumed is Some,
            psk matches Some(k) ==> k.wf() && k@ == resumed.unwrap().psk,
            resumed matches Some(rs) ==> resumption_ok(m@, tr.data(), suite_hash(c.suite), rs),
            tp matches Some(t) ==> t@.len() <= 60000,
            early ==> early_allowed(cfg@, m@, retry, choice, resumed),
            resumed is Some ==> cfg@.client is None,
            ech_on == ech is Some,
            ech matches Some((outer, pt)) ==> retry is None && ech_decrypted(outer, pt, m@) && cfg@.ech_list.len() > 0 && !ech_retry,
            ech_retry ==> ech is None && cfg@.ech_list.len() > 0 && (parse_client_hello(m@.skip(4)) matches Ok(s) && s.ech is Some),
            ech_retry ==> tp is None,
    ensures
        r matches Ok(p) ==> prep_ok(p, cfg@, m@, retry, choice, resumed, opt_view(tp), early, ech, ech_retry),
{
        let mut tr = tr;
        let suite = c.suite;
        let a = suite_hash_x(suite);
        if !(c.share.start <= c.share.end && c.share.end <= body.len()) {
            return Err(INTERNAL_ERROR);
        }
        let peer = c.share.of(body);
        let alpn: Option<&[u8]> = match c.alpn {
            None => None,
            Some((ours, _)) => {
                if !(ours.start <= ours.end && ours.end <= cfg.alpn.len() && ours.end - ours.start <= 255) {
                    return Err(INTERNAL_ERROR);
                }
                Some(ours.of(cfg.alpn.as_slice()))
            },
        };
        let resuming = psk.is_some();
        let zero = Secret::zeros_of(a);
        let pk: Secret = match psk {
            Some(k) => k,
            None => zero,
        };
        let (share, shared, dn, random, sh) = match exchange(prov, peer, sid, suite, c.group, resuming, ech_on) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        let ghost random0 = random@;
        let ghost sh0 = sh@;
        let (random, sh) = if ech_on {
            match ech_finish(a, m, random, &sh, sid, suite, c.group, share.as_slice(), resuming) {
                Some(x) => x,
                None => return Err(INTERNAL_ERROR),
            }
        } else {
            (random, sh)
        };
        let retry_l: Option<&[u8]> = if ech_retry { Some(cfg.ech_list.as_slice()) } else { None };
        let dhe = vstd::slice::slice_subrange(vstd::array::array_as_slice(&shared), 0, dn);
        assert(dhe@ =~= shared@.take(dn as int));
        let ghost pre = tr.data();
        tr.update(m);
        // 0-RTT data is protected under a key over the ClientHello alone.
        let c_early = early_key(a, &pk, &tr, early);
        let ghost th_ch = tr.data();
        tr.update(sh.as_slice());
        let ghost th_sh = tr.data();
        let th = tr.hash();
        let (hs, c_hs, s_hs) = hs_keys(suite, pk.as_slice(), dhe, &th, Ghost(th_sh));
        let (fl, Ghost(sig)) = if resuming {
            let f = resumed_flight(alpn, tp, early, retry_l, &mut tr, &s_hs);
            proof {
                reveal(short_flight);
                assert(short_flight(suite_hash(c.suite), th_sh, tr.data(), f@,
                    encrypted_extensions(opt_view(alpn), opt_view(tp), early, opt_view(retry_l)), s_hs@));
            }
            (f, Ghost(Seq::<u8>::empty()))
        } else {
            match server_flight(prov, cfg, c.signature_scheme, alpn, tp, early, retry_l, &mut tr, &s_hs) {
                Some(x) => {
                    proof {
                        reveal(full_flight);
                        assert(full_flight(cfg@, suite_hash(c.suite), c.signature_scheme, x.1@, th_sh, tr.data(), x.0@,
                            encrypted_extensions(opt_view(alpn), opt_view(tp), early, opt_view(retry_l)), s_hs@));
                    }
                    x
                },
                None => return Err(INTERNAL_ERROR),
            }
        };
        let ghost th_sfin = tr.data();
        let tr_sfin = tr;
        // No tickets with client authentication: a resumption would have no
        // certificate to show.
        let want_res = cfg.tickets > 0 && prov.tickets() && !cfg.has_client_auth();
        let (c_ap, s_ap, expect, res) = late_keys(a, &hs, &c_hs, Ghost(pk@), Ghost(dhe@), tr, early, want_res);
        let ghost th_eoed = if early { th_sfin + end_of_early_data() } else { th_sfin };
        let ghost tpv = opt_view(tp);
        let ghost hsv = SpecHs { retry, ch: m@, choice, random: random@, share: share@, dhe: dhe@, sig, resumed, tp: tpv, early, ech, ech_retry, client: None };
        proof {
            assert(hsv.ee(cfg@) == encrypted_extensions(opt_view(alpn), opt_view(tp), early, opt_view(retry_l)));
            lemma_ech_ok(cfg@, hsv, m@, random0, sh0, sid@);
            assert(pk@ == hsv.psk());
            if early {
                lemma_early_no_retry(cfg@, m@, retry, choice, resumed);
            }
            assert(early ==> retry is None && pre == Seq::<u8>::empty() && th_ch =~= m@);
            assert(hsv.tp == opt_view(tp));
            assert(hsv.alpn(cfg@) == opt_view(alpn));
            assert(hsv.client is None);
            assert(cfg@.client is Some ==> hsv.resumed is None);
            if resumed is None {
                lemma_full_flight(cfg@, hsv, suite_hash(c.suite), c.signature_scheme, sig, th_sh, th_sfin, fl@, encrypted_extensions(opt_view(alpn), opt_view(tp), early, opt_view(retry_l)), s_hs@);
            } else {
                lemma_short_flight(cfg@, hsv, suite_hash(c.suite), th_sh, th_sfin, fl@, encrypted_extensions(opt_view(alpn), opt_view(tp), early, opt_view(retry_l)), s_hs@);
            }
            lemma_accept_spec(cfg@, hsv, m@, pre, sh@, th_sh, th_sfin, fl@, peer@, alpn, sid@);
            assert(cfg.cert@ == certificate(cfg@.chain));
        }
        proof {
            assert(c_hs@ == hsv.c_hs());
            assert(s_hs@ == hsv.s_hs());
            assert(hsv.th_eoed(cfg@) == th_eoed);
            assert(expect@ == verify_data(suite_hash(c.suite), c_hs@, th_eoed));
            assert(finished(expect@) == hsv.client_finished(cfg@));
            assert(c_ap@ == hsv.c_ap(cfg@));
            assert(s_ap@ == hsv.s_ap(cfg@));
        }
        proof {
            assert(tr_sfin.data() == hsv.th_sfin(cfg@));
            reveal(prep_ok);
            assert(sh@.len() < 65536);
        }
        Ok(Prep { sh, fl, c_hs, s_hs, expect, c_ap, s_ap, res, c_early, tr: tr_sfin, hs: Ghost(hsv) })
}

/// The next traffic secret after `sec` (§7.2) and its protection.
fn rekey<P: Provider>(prov: &P, suite: u16, sec: &Secret) -> (r: (Secret, Protect<P::Key>))
    requires
        sec.wf(),
    ensures
        r.0.wf(),
        r.0@ == next_traffic_secret(suite_hash(suite), sec@),
        keys_are(r.1, suite, r.0@),
{
    let a = suite_hash_x(suite);
    let kl = suite_key_len_x(suite);
    let s2 = next_traffic_secret_x(a, sec);
    let (k, iv) = traffic_keys_x(a, &s2, kl);
    let p = Protect::new(prov.aead_key(suite, k.as_slice()), &iv);
    (s2, p)
}


/// Whether `b[s..e]` holds byte `v`.
fn has_byte(b: &[u8], s: usize, e: usize, v: u8) -> (r: bool)
    requires
        s <= e <= b@.len(),
    ensures
        r == b@.subrange(s as int, e as int).contains(v),
{
    let mut i = s;
    while i < e
        invariant
            s <= i <= e <= b@.len(),
            forall|j: int| s <= j < i ==> b@[j] != v,
        decreases e - i,
    {
        if b[i] == v {
            proof {
                assert(b@.subrange(s as int, e as int)[i - s] == v);
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        if b@.subrange(s as int, e as int).contains(v) {
            let k = choose|k: int| 0 <= k < e - s && b@.subrange(s as int, e as int)[k] == v;
            assert(b@[s + k] == v);
        }
    }
    false
}

/// The big-endian u64 at `b[i..i + 8]`.
fn be8_at(b: &[u8], i: usize) -> (r: u64)
    requires
        i + 8 <= b@.len(),
{
    let hi = (b[i] as u32) * 0x100_0000 + (b[i + 1] as u32) * 0x1_0000 + (b[i + 2] as u32) * 0x100 + b[i + 3] as u32;
    let lo = (b[i + 4] as u32) * 0x100_0000 + (b[i + 5] as u32) * 0x1_0000 + (b[i + 6] as u32) * 0x100 + b[i + 7] as u32;
    (hi as u64) * 0x1_0000_0000 + lo as u64
}

/// The big-endian u32 at `b[i..i + 4]`.
fn be4_at_x(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r as nat == be4_at(b@, i as int),
{
    let a0 = b[i] as u32;
    let a1 = b[i + 1] as u32;
    let a2 = b[i + 2] as u32;
    let a3 = b[i + 3] as u32;
    proof {
        assert(a0 * 256 + a1 <= 65535) by (nonlinear_arith)
            requires a0 < 256, a1 < 256;
        assert((a0 * 256 + a1) * 256 + a2 <= 0xff_ffff) by (nonlinear_arith)
            requires a0 * 256 + a1 <= 65535, a2 < 256;
        assert(((a0 * 256 + a1) * 256 + a2) * 256 + a3 <= 0xffff_ffff) by (nonlinear_arith)
            requires (a0 * 256 + a1) * 256 + a2 <= 0xff_ffff, a3 < 256;
    }
    ((a0 * 256 + a1) * 256 + a2) * 256 + a3
}

/// What a resumption's ticket says about 0-RTT data, and what the
/// provider's anti-replay needs to judge it.
pub(crate) struct ResumeInfo {
    /// The ticket's max_early_data_size (0: no 0-RTT data).
    pub(crate) max_early: u32,
    /// The ALPN protocol of the connection that issued the ticket.
    pub(crate) alpn: Vec<u8>,
    /// When the ticket was issued (seconds), and its ticket_age_add.
    pub(crate) issued: u64,
    pub(crate) age_add: u32,
    /// The client's obfuscated_ticket_age for it.
    pub(crate) obf_age: u32,
    /// The first PSK binder: unique to the ClientHello.
    pub(crate) binder: Vec<u8>,
}

/// The resumption ClientHello `m` (body `body`, parsed as `h`) offers, if
/// the server takes it, and its PSK: `tr` is the transcript before `m`,
/// `suite` the suite negotiated. A ticket the server cannot open, for
/// another suite, or too old gives a full handshake (§4.2.11: the server
/// may decline a PSK); a wrong binder is an error (decrypt_error).
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn try_resume<P: Provider>(
    prov: &mut P,
    cfg: &Config,
    m: &[u8],
    body: &[u8],
    h: &ClientHello,
    Ghost(s): Ghost<SpecHello>,
    suite: u16,
    tr: &Transcript,
) -> (r: Result<Option<(Secret, Ghost<SpecResume>, ResumeInfo)>, u8>)
    requires
        is_msg(m@, 1),
        body@ == m@.skip(4),
        parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s),
        h.models(s),
        tr.wf(),
        tr.alg() == suite_hash(suite),
        known_suite(suite),
    ensures
        r matches Ok(Some((k, g, info))) ==> {
            &&& k.wf() && k@ == g@.psk && resumption_ok(m@, tr.data(), suite_hash(suite), g@)
            &&& ticket_suite_psk(g@.state) matches Some((ts, _)) && ts == suite
            &&& info.max_early as nat == ticket_early(g@.state).0
            &&& info.alpn@ == ticket_early(g@.state).1
            &&& cfg@.client is None
        },
{
    // With client authentication every handshake is a full one.
    if cfg.tickets == 0 || !prov.tickets() || cfg.has_client_auth() {
        return Ok(None);
    }
    let mp = match h.psk_modes {
        Some(x) => x,
        None => return Ok(None),
    };
    let (ids, bds) = match h.pre_shared_key {
        Some(x) => x,
        None => return Ok(None),
    };
    if !(mp.start <= mp.end && mp.end <= body.len() && ids.end <= body.len() && bds.end <= body.len()
        && bds.start >= 2 && bds.start <= bds.end) {
        return Ok(None);
    }
    if !has_byte(body, mp.start, mp.end, 1) {
        return Ok(None);
    }
    let id = match vec16_x(body, ids.start, ids.end) {
        Some(x) => x,
        None => return Ok(None),
    };
    let bd = match vec8_x(body, bds.start, bds.end) {
        Some(x) => x,
        None => return Ok(None),
    };
    let ident = id.of(body);
    let mut st: Vec<u8> = Vec::new();
    if !prov.open_ticket(ident, &mut st) {
        return Ok(None);
    }
    let n = st.len();
    if n < 16 || st[0] != 2 || !(st[15] == 32 || st[15] == 48) {
        return Ok(None);
    }
    let l = st[15] as usize;
    if n < 16 + l + 5 || n != 16 + l + 5 + st[16 + l + 4] as usize {
        return Ok(None);
    }
    let ts = (st[1] as u16) * 256 + st[2] as u16;
    if ts != suite {
        return Ok(None);
    }
    let a = suite_hash_x(suite);
    let issued = be8_at(st.as_slice(), 3);
    let now = prov.now();
    if now < issued || now - issued > cfg.lifetime as u64 {
        return Ok(None);
    }
    let rest = vstd::slice::slice_subrange(st.as_slice(), 16, 16 + l);
    let psk = Secret::from_slice(rest, l);
    proof {
        assert(psk@ =~= st@.subrange(16, 16 + l));
        assert(ticket_shaped(st@));
        assert(ticket_suite_psk(st@) == Some((ts, st@.subrange(16, 16 + l))));
    }
    let max_early = be4_at_x(st.as_slice(), 16 + l);
    let alpn_v = vstd::slice::slice_subrange(st.as_slice(), 16 + l + 5, n);
    let mut alpn: Vec<u8> = Vec::new();
    put(&mut alpn, alpn_v);
    let age_add = be4_at_x(st.as_slice(), 11);
    proof {
        assert(alpn@ =~= st@.skip(16 + l + 5));
    }
    // The binder: verify_data under binder_key over the transcript up to
    // the binders list (§4.2.11.2).
    let cut = 4 + bds.start - 2;
    let part = vstd::slice::slice_subrange(m, 0, cut);
    let mut t2 = *tr;
    t2.update(part);
    let th = t2.hash();
    let bk = binder_key_x(a, psk.as_slice());
    let vd = verify_data_x(a, &bk, &th, Ghost(t2.data()));
    if !declassify(ct_eq(vd.as_slice(), bd.of(body))) {
        return Err(DECRYPT_ERROR);
    }
    let ghost g = SpecResume { identity: ident@, state: st@, psk: psk@ };
    proof {
        assert(part@ =~= m@.take(4 + bds.start - 2));
        assert(ov(h.psk_modes) == s.psk_modes);
        assert(ov2(h.pre_shared_key) == s.pre_shared_key);
    }
    // obfuscated_ticket_age follows the first identity (§4.2.11).
    let obf_age = if id.end <= ids.end && ids.end - id.end >= 4 { be4_at_x(body, id.end) } else { 0 };
    let mut binder: Vec<u8> = Vec::new();
    put(&mut binder, bd.of(body));
    let info = ResumeInfo { max_early, alpn, issued, age_add, obf_age, binder };
    Ok(Some((psk, Ghost(g), info)))
}

/// The lifetime and `ticket_age_add` of a ticket, when it was issued, and
/// the ticket.
pub struct TicketSent {
    pub lifetime: u32,
    pub age_add: u32,
    pub time: u64,
    pub ticket: Seq<u8>,
}

/// A NewSessionTicket (§4.6.1) with nonce `[i]` for
/// resumption_master_secret `rm`: the ticket, sealed by the provider,
/// holds the PSK RFC 8446 derives for it. `None` if the provider could not
/// seal one.
#[verifier::spinoff_prover]
pub(crate) fn make_ticket<P: Provider>(
    prov: &mut P,
    suite: u16,
    lifetime: u32,
    i: u8,
    rm: &Secret,
    max_early: u32,
    alpn: &[u8],
) -> (r: Option<(Vec<u8>, Ghost<TicketSent>)>)
    requires
        rm.wf(),
        alpn@.len() <= 255,
    ensures
        r matches Some((nst, t)) ==> {
            let nonce = seq![i];
            &&& t@.lifetime == lifetime
            &&& nst@ == new_session_ticket(t@.lifetime, t@.age_add, nonce, t@.ticket, max_early)
            &&& nst@.len() <= 500
            &&& ticket_issued(t@.ticket, ticket_state(suite, t@.time, t@.age_add, ticket_psk(suite_hash(suite), rm@, nonce), max_early, alpn@))
        },
{
    let a = suite_hash_x(suite);
    let nonce: [u8; 1] = [i];
    let psk = ticket_psk_x(a, rm, &nonce);
    let mut rnd = [0u8; 32];
    prov.random(&mut rnd);
    let age_add = ((rnd[0] as u32) << 24u32) | ((rnd[1] as u32) << 16u32) | ((rnd[2] as u32) << 8u32) | (rnd[3] as u32);
    let time = prov.now();
    let mut st: Vec<u8> = Vec::new();
    ticket_state_x(&mut st, suite, time, age_add, &psk, max_early, alpn);
    let mut ticket: Vec<u8> = Vec::new();
    proof {
        assert(st@.len() <= 330);
    }
    if !prov.seal_ticket(st.as_slice(), &mut ticket) {
        return None;
    }
    assert(ticket@.skip(0) =~= ticket@);
    if ticket.len() > 460 {
        return None;
    }
    let mut nst: Vec<u8> = Vec::new();
    new_session_ticket_x(&mut nst, lifetime, age_add, &nonce, ticket.as_slice(), max_early);
    proof {
        assert(nonce@ =~= seq![i]);
    }
    if nst.len() > 500 {
        return None;
    }
    Some((nst, Ghost(TicketSent { lifetime, age_add, time, ticket: ticket@ })))
}

/// Sends a NewSessionTicket (`make_ticket`) protected by `tx`. `false` if
/// the provider could not seal one, and nothing is sent.
#[verifier::spinoff_prover]
fn issue_ticket<P: Provider>(
    prov: &mut P,
    suite: u16,
    lifetime: u32,
    i: u8,
    rm: &Secret,
    max_early: u32,
    alpn: &[u8],
    tx: &mut Protect<P::Key>,
    out: &mut Vec<u8>,
) -> (r: (bool, Ghost<TicketSent>))
    requires
        rm.wf(),
        alpn@.len() <= 255,
        old(out)@.len() + 0x20000 <= usize::MAX,
    ensures
        final(tx).suite() == old(tx).suite(),
        final(tx).key() == old(tx).key(),
        final(tx).iv() == old(tx).iv(),
        final(out)@.take(old(out)@.len() as int) == old(out)@,
        old(out)@.len() <= final(out)@.len() <= old(out)@.len() + 1024,
        r.0 ==> {
            let t = r.1@;
            let nonce = seq![i];
            &&& t.lifetime == lifetime
            &&& final(out)@ == old(out)@ + seal_record(
                old(tx).suite(),
                old(tx).key(),
                old(tx).iv(),
                old(tx).seq(),
                22,
                new_session_ticket(t.lifetime, t.age_add, nonce, t.ticket, max_early),
            )
            &&& ticket_issued(t.ticket, ticket_state(suite, t.time, t.age_add, ticket_psk(suite_hash(suite), rm@, nonce), max_early, alpn@))
        },
        !r.0 ==> final(out)@ == old(out)@,
{
    let ghost none = TicketSent { lifetime, age_add: 0, time: 0, ticket: Seq::empty() };
    proof {
        assert(out@.take(out@.len() as int) =~= out@);
    }
    let (nst, t) = match make_ticket(prov, suite, lifetime, i, rm, max_early, alpn) {
        Some(x) => x,
        None => return (false, Ghost(none)),
    };
    let ghost o = out@;
    if !tx.seal(22, nst.as_slice(), out) {
        return (false, Ghost(none));
    }
    proof {
        assert(out@.take(o.len() as int) =~= o);
    }
    (true, t)
}

/// A server connection, with its cryptography `P`.
pub struct ServerConn<P: Provider> {
    cfg: Arc<Config>,
    prov: P,
    state: State<P::Key>,
    /// A handshake message that has not all arrived.
    buf: Vec<u8>,
    /// 0-RTT bytes left to skip.
    skip: usize,
    /// 0-RTT bytes left to take, when they are taken.
    early_left: u32,
    /// 0-RTT data was taken in this handshake (`handshake().early`).
    early_taken: bool,
    /// The ALPN protocol chosen, a span of the configuration's list.
    alpn_sel: Option<Span>,
    /// With client authentication, the client's certificates, leaf first,
    /// once its chain checked out (empty if it sent none).
    peer: Vec<Vec<u8>>,
    /// The client's Certificate message, and the time its chain was checked
    /// at.
    cmsg: Ghost<Seq<u8>>,
    cnow: Ghost<SpecTime>,
    hs: Ghost<SpecHs>,
    ch1: Ghost<Seq<u8>>,
    hrr: Ghost<Seq<u8>>,
    fin: Ghost<Seq<u8>>,
    nrx: Ghost<nat>,
    ntx: Ghost<nat>,
}

impl<P: Provider> ServerConn<P> {
    pub closed spec fn config(&self) -> SpecCfg {
        (*self.cfg)@
    }

    pub closed spec fn phase(&self) -> Phase {
        match self.state {
            State::Start => Phase::Start,
            State::WaitCh2 { .. } => Phase::Retried,
            State::WaitFinished { .. } => Phase::WaitFinished,
            State::WaitClientAuth { .. } => Phase::WaitFinished,
            State::Connected { .. } => Phase::Connected,
            State::Closed => Phase::Closed,
        }
    }

    /// Waiting for the client's Certificate or CertificateVerify.
    pub closed spec fn in_client_auth(&self) -> bool {
        self.state is WaitClientAuth
    }

    /// The client's Certificate has come (and its chain checked out).
    pub closed spec fn got_cert(&self) -> bool {
        match self.state {
            State::WaitClientAuth { got_cert, .. } => got_cert,
            _ => false,
        }
    }

    /// The client's certificates, leaf first, once checked.
    pub closed spec fn peer_chain(&self) -> Seq<Seq<u8>> {
        chain_view(self.peer@)
    }

    /// The handshake, once the server has sent its flight.
    pub closed spec fn handshake(&self) -> SpecHs {
        self.hs@
    }

    /// The client's Finished, once checked.
    pub closed spec fn client_finished(&self) -> Seq<u8> {
        self.fin@
    }

    /// The client's current traffic secret, its KeyUpdates so far, and
    /// the sequence number of its next record.
    pub closed spec fn rx_secret(&self) -> Seq<u8> {
        match self.state {
            State::Connected { c_sec, .. } => c_sec@,
            _ => Seq::empty(),
        }
    }

    pub closed spec fn rx_updates(&self) -> nat {
        self.nrx@
    }

    pub closed spec fn rx_seq(&self) -> u64 {
        match self.state {
            State::Connected { rx, .. } => rx.seq(),
            _ => 0,
        }
    }

    /// The server's current traffic secret and next sequence number.
    pub closed spec fn tx_secret(&self) -> Seq<u8> {
        match self.state {
            State::Connected { s_sec, .. } => s_sec@,
            State::WaitFinished { s_ap, .. } => s_ap@,
            State::WaitClientAuth { s_ap, .. } => s_ap@,
            _ => Seq::empty(),
        }
    }

    pub closed spec fn tx_seq(&self) -> u64 {
        match self.state {
            State::Connected { tx, .. } => tx.seq(),
            State::WaitFinished { tx, .. } => tx.seq(),
            State::WaitClientAuth { tx, .. } => tx.seq(),
            _ => 0,
        }
    }

    /// 0-RTT data is still coming (the client's EndOfEarlyData has not).
    pub closed spec fn in_early(&self) -> bool {
        match self.state {
            State::WaitFinished { early, .. } => early is Some,
            _ => false,
        }
    }

    /// The sequence number of the next 0-RTT record.
    pub closed spec fn early_seq(&self) -> u64 {
        match self.state {
            State::WaitFinished { early: Some(p), .. } => p.seq(),
            _ => 0,
        }
    }

    pub closed spec fn tx_updates(&self) -> nat {
        self.ntx@
    }

    /// Client authentication, if on, is over and went as `spec_client.rs`
    /// says, and `peer` is the client's chain.
    pub closed spec fn client_done(&self) -> bool {
        &&& self.hs@.client_ok(self.config())
        &&& self.hs@.client matches Some(a) ==> chain_view(self.peer@) == a.chain
    }

    pub closed spec fn hs_ok(&self) -> bool {
        &&& self.hs@.valid(self.config())
        &&& known_suite(self.hs@.choice.suite)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& (*self.cfg).wf()
        &&& self.buf@.len() <= MAX_MESSAGE + 4
        &&& match self.state {
            State::Start => true,
            State::WaitCh2 { tr, suite, group } => {
                &&& tr.wf()
                &&& tr.alg() == suite_hash(suite)
                &&& known_suite(suite)
                &&& is_msg(self.ch1@, 1)
                &&& outcome(self.config(), self.ch1@) == Some(SpecOutcome::Retry { suite, group })
                &&& self.hrr@ == hello_retry_request(session_id(self.ch1@), suite, group)
                &&& tr.data() == message_hash(suite_hash(suite), self.ch1@) + self.hrr@
            },
            State::WaitFinished { suite, rx, tx, early, expect, c_ap, s_ap, res } => {
                let h = self.hs@;
                let c = self.config();
                &&& self.hs_ok()
                &&& suite == h.choice.suite
                &&& self.early_taken == h.early
                &&& keys_are(rx, suite, h.c_hs())
                &&& keys_are(tx, suite, h.s_ap(c))
                &&& early matches Some(p) ==> h.early && keys_are(p, suite, h.c_early())
                &&& expect.wf() && finished(expect@) == h.client_finished(c)
                &&& expect@.len() == hash_len(suite_hash(suite))
                &&& c_ap.wf() && c_ap@ == h.c_ap(c)
                &&& s_ap.wf() && s_ap@ == h.s_ap(c)
                &&& res matches Some(rm) ==> rm.wf() && rm@ == h.res_master(c)
                &&& self.client_done()
            },
            State::WaitClientAuth { suite, rx, tx, tr, c_hs, c_ap, s_ap, got_cert } => {
                let h = self.hs@;
                let c = self.config();
                &&& self.hs_ok()
                &&& suite == h.choice.suite
                &&& c.client is Some
                &&& h.client is None
                &&& !h.early
                &&& !self.early_taken
                &&& keys_are(rx, suite, h.c_hs())
                &&& keys_are(tx, suite, h.s_ap(c))
                &&& c_hs.wf() && c_hs@ == h.c_hs()
                &&& c_ap.wf() && c_ap@ == h.c_ap(c)
                &&& s_ap.wf() && s_ap@ == h.s_ap(c)
                &&& tr.wf() && tr.alg() == suite_hash(suite)
                &&& !got_cert ==> tr.data() == h.th_eoed(c)
                &&& got_cert ==> {
                    &&& tr.data() == h.th_eoed(c) + self.cmsg@
                    &&& is_msg(self.cmsg@, 11)
                    &&& parse_client_certificate(self.cmsg@.skip(4)) == Ok::<Seq<Seq<u8>>, u8>(chain_view(self.peer@))
                    &&& self.peer@.len() > 0
                    &&& chain_ok(chain_view(self.peer@), c.client.unwrap().roots, self.cnow@)
                }
            },
            State::Connected { suite, rx, tx, c_sec, s_sec } => {
                let h = self.hs@;
                let c = self.config();
                &&& self.hs_ok()
                &&& suite == h.choice.suite
                &&& self.client_done()
                &&& self.fin@ == h.client_finished(c)
                &&& c_sec.wf() && c_sec@ == updated(suite_hash(suite), h.c_ap(c), self.nrx@)
                &&& s_sec.wf() && s_sec@ == updated(suite_hash(suite), h.s_ap(c), self.ntx@)
                &&& keys_are(rx, suite, c_sec@)
                &&& keys_are(tx, suite, s_sec@)
            },
            State::Closed => true,
        }
    }

    /// Once connected, the handshake was valid and the client's Finished
    /// was the one RFC 8446 gives for it.
    pub proof fn lemma_connected(&self)
        requires
            self.wf(),
            self.phase() == Phase::Connected,
        ensures
            self.handshake().valid(self.config()),
            self.client_finished() == self.handshake().client_finished(self.config()),
            self.rx_secret() == updated(
                self.handshake().alg(),
                self.handshake().c_ap(self.config()),
                self.rx_updates(),
            ),
            self.handshake().client_ok(self.config()),
            self.handshake().client matches Some(a) ==> self.peer_chain() == a.chain,
    {
    }

    pub fn new(cfg: Arc<Config>, prov: P) -> (r: Self)
        requires
            (*cfg).wf(),
        ensures
            r.wf(),
            r.phase() == Phase::Start,
            r.config() == (*cfg)@,
    {
        ServerConn {
            cfg,
            prov,
            state: State::Start,
            buf: Vec::new(),
            skip: 0,
            early_left: 0,
            early_taken: false,
            alpn_sel: None,
            peer: Vec::new(),
            cmsg: Ghost(Seq::empty()),
            cnow: Ghost(arbitrary()),
            hs: Ghost(arbitrary()),
            ch1: Ghost(Seq::empty()),
            hrr: Ghost(Seq::empty()),
            fin: Ghost(Seq::empty()),
            nrx: Ghost(0),
            ntx: Ghost(0),
        }
    }

    pub fn is_connected(&self) -> (r: bool)
        ensures
            r == (self.phase() == Phase::Connected),
    {
        match self.state {
            State::Connected { .. } => true,
            _ => false,
        }
    }

    /// The server's sending keys once connected, for a caller that hands
    /// record protection to the kernel (kTLS): the suite, the traffic key
    /// and IV of the server's current traffic secret, and the sequence
    /// number of its next record. Records sealed with them from that
    /// number on are the ones `write` would make from here. A caller that
    /// hands them over must send nothing more this connection protects
    /// with the same keys (`write`, `close`, or what `read_record` answers
    /// with), since its sequence numbers no longer count what was sent.
    pub fn tx_keys(&self) -> (r: Option<(u16, Secret, Secret, u64)>)
        requires
            self.wf(),
        ensures
            r is Some <==> self.phase() == Phase::Connected,
            r matches Some((s, k, iv, seq)) ==> {
                &&& s == self.handshake().choice.suite
                &&& known_suite(s)
                &&& k.wf() && iv.wf()
                &&& k@ == traffic_key(suite_hash(s), self.tx_secret(), suite_key_len(s))
                &&& k@.len() == suite_key_len(s)
                &&& iv@ == traffic_iv(suite_hash(s), self.tx_secret())
                &&& iv@.len() == 12
                &&& seq == self.tx_seq()
            },
    {
        match &self.state {
            State::Connected { suite, tx, s_sec, .. } => {
                let (k, iv) = traffic_keys_x(suite_hash_x(*suite), s_sec, suite_key_len_x(*suite));
                Some((*suite, k, iv, tx.seq_x()))
            },
            _ => None,
        }
    }

    /// Sends alert `code` (under the server's current keys once it has
    /// some) and closes.
    fn fail(&mut self, code: u8, out: &mut Vec<u8>) -> (r: Error)
        requires
            old(self).wf(),
            old(out)@.len() <= usize::MAX / 2,
        ensures
            final(self).wf(),
            final(self).phase() == Phase::Closed,
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            r == Error::Sent(code),
    {
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        // A refused client has no identity (its certificates are kept from
        // its Certificate on, before its CertificateVerify is checked).
        self.peer = Vec::new();
        let body: [u8; 2] = [2, code];
        let ghost o = out@;
        match st {
            State::WaitFinished { mut tx, .. } => {
                tx.seal(21, &body, out);
            },
            State::WaitClientAuth { mut tx, .. } => {
                tx.seal(21, &body, out);
            },
            State::Connected { mut tx, .. } => {
                tx.seal(21, &body, out);
            },
            _ => {
                plain_header_x(out, 21, 2);
                put(out, &body);
            },
        }
        assert(out@.take(o.len() as int) =~= o);
        Error::Sent(code)
    }

    /// An alert from the client, `a` its body.
    fn on_alert(&mut self, a: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(out)@.len() <= usize::MAX / 2,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == old(self).phase() || final(self).phase() == Phase::Closed,
            r matches Ok(e) ==> !(e is HandshakeDone) && !(e is Data) && !(e is EarlyData),
    {
        if a.len() != 2 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        assert(out@.take(out@.len() as int) =~= out@);
        if a[1] == 90 {
            // user_canceled: a close_notify should follow.
            return Ok(Event::Nothing);
        }
        self.state = State::Closed;
        if a[1] == 0 {
            Ok(Event::Closed)
        } else {
            Err(Error::Received(a[1]))
        }
    }

    /// Sends a HelloRetryRequest for ClientHello1 `m`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn send_hrr(&mut self, m: &[u8], sid: &[u8], suite: u16, group: u16, early: bool, out: &mut Vec<u8>) -> (r:
        Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::Start,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 1),
            outcome(old(self).config(), m@) == Some(SpecOutcome::Retry { suite, group }),
            sid@ == session_id(m@),
            sid@.len() <= 32,
            known_suite(suite),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).phase() == Phase::Retried,
            r matches Ok(e) && e is Nothing,
            final(out)@ == old(out)@ + plain_record(22, hello_retry_request(sid@, suite, group)) + (if sid@.len()
                > 0 {
                ccs_record()
            } else {
                Seq::empty()
            }),
    {
        let a = suite_hash_x(suite);
        let mut t1 = Transcript::new(a);
        t1.update(m);
        let h1 = t1.hash();
        assert(t1.data() =~= m@);
        let mut tr = Transcript::new(a);
        let mut mh: Vec<u8> = Vec::new();
        message_hash_x(&mut mh, &h1);
        tr.update(mh.as_slice());
        let mut hrr: Vec<u8> = Vec::new();
        hello_retry_request_x(&mut hrr, sid, suite, group);
        tr.update(hrr.as_slice());
        let ghost o = out@;
        plain_header_x(out, 22, hrr.len());
        put(out, hrr.as_slice());
        let ccs: [u8; 6] = [20, 3, 3, 0, 1, 1];
        if sid.len() > 0 {
            put(out, &ccs);
        }
        proof {
            assert(ccs@ =~= ccs_record());
            assert(tr.data() =~= message_hash(a, m@) + hrr@);
            if sid@.len() > 0 {
                assert(out@ =~= o + plain_record(22, hello_retry_request(sid@, suite, group)) + ccs_record());
            } else {
                assert(out@ =~= o + plain_record(22, hello_retry_request(sid@, suite, group)) + Seq::<u8>::empty());
            }
        }
        self.ch1 = Ghost(m@);
        self.hrr = Ghost(hrr@);
        self.skip = if early { EARLY_SKIP } else { 0 };
        self.state = State::WaitCh2 { tr, suite, group };
        Ok(Event::Nothing)
    }


    /// Sends ServerHello and the server's flight for ClientHello `m`
    /// (body `body`, negotiated as `c`), `tr` being the transcript before
    /// it.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(80)]
    fn accept(
        &mut self,
        cfg: &Config,
        m: &[u8],
        body: &[u8],
        sid: &[u8],
        c: Choice,
        tr: Transcript,
        retried: bool,
        Ghost(retry): Ghost<Option<(Seq<u8>, Seq<u8>)>>,
        Ghost(choice): Ghost<SpecChoice>,
        h: &ClientHello,
        Ghost(s): Ghost<SpecHello>,
        Ghost(ech): Ghost<Option<(Seq<u8>, Seq<u8>)>>,
        ech_on: bool,
        ech_retry: bool,
        out: &mut Vec<u8>,
    ) -> (r: Result<Event, Error>)
        requires
            parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s),
            h.models(s),
            old(self).wf(),
            old(self).phase() == Phase::Start || old(self).phase() == Phase::Retried,
            cfg.wf(),
            ech_on == ech is Some,
            ech matches Some((outer, pt)) ==> retry is None && ech_decrypted(outer, pt, m@) && cfg@.ech_list.len() > 0 && !ech_retry,
            ech_retry ==> ech is None && cfg@.ech_list.len() > 0 && s.ech is Some,
            cfg@ == old(self).config(),
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 1),
            body@ == m@.skip(4),
            sid@ == session_id(m@),
            sid@.len() <= 32,
            known_suite(c.suite),
            choice.suite == c.suite && choice.group == c.group && choice.share == c.share@
                && choice.signature_scheme == c.signature_scheme && choice.alpn == ov2(c.alpn),
            outcome(cfg@, m@) == Some(SpecOutcome::Accept(choice)),
            retried == retry is Some,
            match retry {
                None => true,
                Some((ch1, hrr)) => is_msg(ch1, 1) && outcome(cfg@, ch1) == Some(
                    SpecOutcome::Retry { suite: c.suite, group: c.group },
                ) && hrr == hello_retry_request(session_id(ch1), c.suite, c.group),
            },
            tr.wf(),
            tr.alg() == suite_hash(c.suite),
            tr.data() == match retry {
                None => Seq::<u8>::empty(),
                Some((ch1, hrr)) => message_hash(suite_hash(c.suite), ch1) + hrr,
            },
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).phase() == Phase::WaitFinished || final(self).phase() == Phase::Closed,
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            r matches Ok(e) ==> e is Nothing,
            final(self).phase() == Phase::WaitFinished ==> final(self).handshake().retry == retry && final(self).handshake().ch == m@
                && final(self).handshake().ech == ech,
    {
        let rs = match try_resume(&mut self.prov, cfg, m, body, h, Ghost(s), c.suite, &tr) {
            Ok(x) => x,
            Err(code) => return Err(self.fail(code, out)),
        };
        let (psk, Ghost(resumed), info) = match rs {
            Some((k, g, i)) => (Some(k), Ghost(Some(g@)), Some(i)),
            None => (None, Ghost(None), None),
        };
        // 0-RTT data (§4.2.10): only on a resumption with no
        // HelloRetryRequest, from a ticket that allows it, for the same
        // ALPN protocol, and only if the provider's anti-replay takes this
        // ClientHello (asked last: it uses up the ClientHello).
        let chosen: &[u8] = match c.alpn {
            None => &[],
            Some((ours, _)) => {
                if !(ours.start <= ours.end && ours.end <= cfg.alpn.len()) {
                    return Err(self.fail(INTERNAL_ERROR, out));
                }
                ours.of(cfg.alpn.as_slice())
            },
        };
        proof {
            assert(chosen@ == alpn_or_empty(cfg@, choice));
        }
        let mut early = false;
        // Never with client authentication (no resumption then either).
        if h.early_data && !retried && cfg.max_early > 0 && !cfg.has_client_auth() {
            match &info {
                Some(i) => {
                    if i.max_early > 0 && ct_eq(i.alpn.as_slice(), chosen) {
                        early = self.prov.claim_early(m, i.binder.as_slice(), i.obf_age, i.issued, i.age_add);
                    }
                },
                None => {},
            }
        }
        proof {
            if early {
                assert(retry is None);
                assert(body@ == m@.skip(4));
                assert(s.early_data);
                reveal(early_allowed);
                assert(early_allowed(cfg@, m@, retry, choice, resumed));
            }
        }
        let p = match prepare(&mut self.prov, cfg, m, body, sid, c, tr, Ghost(retry), Ghost(choice), psk, Ghost(resumed), None, early, Ghost(ech), ech_on, ech_retry) {
            Ok(p) => p,
            Err(code) => return Err(self.fail(code, out)),
        };
        // verus! expands the `Ghost(..)` field, and rustc 1.100 then flags the rest.
        #[allow(non_shorthand_field_patterns)]
        let Prep { sh, fl, c_hs, s_hs, expect, c_ap, s_ap, res, c_early, tr, hs: Ghost(hsv) } = p;
        let tr_sfin = tr;
        proof {
            reveal(prep_ok);
        }
        let suite = c.suite;
        let rx = protect_of(&self.prov, suite, &c_hs);
        let mut tx = protect_of(&self.prov, suite, &s_hs);
        let ghost o = out@;
        plain_header_x(out, 22, sh.len());
        put(out, sh.as_slice());
        let ccs: [u8; 6] = [20, 3, 3, 0, 1, 1];
        if sid.len() > 0 && !retried {
            put(out, &ccs);
        }
        let ghost o2 = out@;
        let ghost ccs_v = if sid@.len() > 0 && !retried {
            ccs_record()
        } else {
            Seq::<u8>::empty()
        };
        proof {
            assert(ccs@ =~= ccs_record());
            assert(o2 =~= o + plain_record(22, sh@) + ccs_v);
            assert(chunks(fl@.len()) <= fl@.len());
        }
        let ok = tx.seal_all(22, fl.as_slice(), out);
        assert(ok);
        proof {
            assert(out@.take(o.len() as int) =~= o);
        }
        if retried || early {
            self.skip = 0;
        }
        self.early_left = if early { cfg.max_early } else { 0 };
        self.early_taken = early;
        self.alpn_sel = match c.alpn {
            Some((ours, _)) => Some(ours),
            None => None,
        };
        // From its Finished on, the server sends under its application key.
        let tx_ap = protect_of(&self.prov, suite, &s_ap);
        let ep = match c_early {
            Some(k) => Some(protect_of(&self.prov, suite, &k)),
            None => None,
        };
        if cfg.has_client_auth() {
            proof {
                reveal(SpecHs::th_eoed);
            }
            self.enter_wait_client_auth(Ghost(hsv), suite, rx, tx_ap, tr_sfin, c_hs, c_ap, s_ap);
        } else {
            proof {
                reveal(SpecHs::client_ok);
            }
            self.enter_wait_finished(Ghost(hsv), suite, rx, tx_ap, ep, expect, c_ap, s_ap, res);
        }
        Ok(Event::Nothing)
    }

    fn enter_wait_client_auth(
        &mut self,
        Ghost(hsv): Ghost<SpecHs>,
        suite: u16,
        rx: Protect<P::Key>,
        tx: Protect<P::Key>,
        tr: Transcript,
        c_hs: Secret,
        c_ap: Secret,
        s_ap: Secret,
    )
        requires
            (*old(self).cfg).wf(),
            old(self).buf@.len() <= MAX_MESSAGE + 4,
            hsv.valid(old(self).config()),
            known_suite(suite),
            suite == hsv.choice.suite,
            old(self).config().client is Some,
            hsv.client is None,
            !hsv.early,
            !old(self).early_taken,
            keys_are(rx, suite, hsv.c_hs()),
            keys_are(tx, suite, hsv.s_ap(old(self).config())),
            c_hs.wf() && c_hs@ == hsv.c_hs(),
            c_ap.wf() && c_ap@ == hsv.c_ap(old(self).config()),
            s_ap.wf() && s_ap@ == hsv.s_ap(old(self).config()),
            tr.wf() && tr.alg() == suite_hash(suite),
            tr.data() == hsv.th_eoed(old(self).config()),
        ensures
            final(self).wf(),
            final(self).phase() == Phase::WaitFinished,
            final(self).in_client_auth(),
            final(self).handshake() == hsv,
            final(self).config() == old(self).config(),
    {
        self.hs = Ghost(hsv);
        self.state = State::WaitClientAuth { suite, rx, tx, tr, c_hs, c_ap, s_ap, got_cert: false };
    }

    /// Where client authentication is: 0 not waiting for it, 1 waiting for
    /// the client's Certificate, 2 for its CertificateVerify.
    fn client_stage_x(&self) -> (r: u8)
        ensures
            r == 0 <==> !self.in_client_auth(),
            r == 1 <==> self.in_client_auth() && !self.got_cert(),
            r == 2 <==> self.in_client_auth() && self.got_cert(),
    {
        match self.state {
            State::WaitClientAuth { got_cert, .. } => if got_cert { 2 } else { 1 },
            _ => 0,
        }
    }

    fn in_client_auth_x(&self) -> (r: bool)
        ensures
            r == self.in_client_auth(),
    {
        match self.state {
            State::WaitClientAuth { .. } => true,
            _ => false,
        }
    }

    /// The client's Certificate `m` (§4.4.2), answering the
    /// CertificateRequest: an empty one, if a certificate is not required,
    /// ends client authentication; otherwise its chain must check out
    /// (`check_chain`), and its CertificateVerify comes next.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(80)]
    fn on_client_certificate(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).in_client_auth(),
            !old(self).got_cert(),
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 11),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::WaitFinished || final(self).phase() == Phase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        let cfa = self.cfg.clone();
        let cfg: &Config = &*cfa;
        let ca = match &cfg.client {
            Some(a) => a,
            None => {
                proof {
                    assert(false);
                }
                return Err(self.fail(INTERNAL_ERROR, out));
            },
        };
        let ghost cc = ca.view();
        assert(self.config().client == Some(cc));
        let body = vstd::slice::slice_subrange(m, 4, m.len());
        assert(body@ =~= m@.skip(4));
        let chain = match parse_client_certificate_x(body) {
            Ok(v) => v,
            Err(a) => return Err(self.fail(a, out)),
        };
        if chain.len() == 0 && ca.required {
            return Err(self.fail(CERTIFICATE_REQUIRED, out));
        }
        let now = self.prov.now_utc();
        if chain.len() > 0 {
            match check_chain(&self.prov, &chain, &ca.roots, &now) {
                Ok(()) => {},
                Err(a) => return Err(self.fail(a, out)),
            }
        }
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            State::WaitClientAuth { suite, rx, tx, mut tr, c_hs, c_ap, s_ap, got_cert } => {
                let ghost h = self.hs@;
                let ghost c = self.config();
                tr.update(m);
                if chain.len() == 0 {
                    // No certificate, and none required: no CertificateVerify
                    // follows, and the client's Finished is next.
                    let a = suite_hash_x(suite);
                    let th = tr.hash();
                    let expect = verify_data_x(a, &c_hs, &th, Ghost(tr.data()));
                    let ghost ca_s = SpecClientAuth { cert_msg: m@, chain: Seq::empty(), scheme: 0, sig: Seq::empty(), now: now@ };
                    let ghost h2 = SpecHs { client: Some(ca_s), ..h };
                    proof {
                        lemma_with_client(h, ca_s, c);
                        assert(chain_view(chain@) =~= Seq::<Seq<u8>>::empty());
                        assert(ca_s.msgs() == m@);
                        assert(ca_s.ok(cc, h.alg(), h.th_eoed(c)));
                        assert(tr.data() == h.th_eoed(c) + ca_s.msgs());
                    }
                    self.peer = chain;
                    self.enter_wait_finished(Ghost(h2), suite, rx, tx, None, expect, c_ap, s_ap, None);
                    Ok(Event::Nothing)
                } else {
                    self.peer = chain;
                    self.cmsg = Ghost(m@);
                    self.cnow = Ghost(now@);
                    self.state = State::WaitClientAuth { suite, rx, tx, tr, c_hs, c_ap, s_ap, got_cert: true };
                    assert(out@.take(out@.len() as int) =~= out@);
                    Ok(Event::Nothing)
                }
            },
            _ => {
                proof {
                    assert(false);
                }
                Err(Error::Closed)
            },
        }
    }

    /// The client's CertificateVerify `m` (§4.4.3): a scheme the server
    /// asked for, and the leaf's key's signature over the transcript
    /// through the client's Certificate; then the client's Finished is
    /// next.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(80)]
    fn on_client_cv(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).in_client_auth(),
            old(self).got_cert(),
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 15),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::WaitFinished || final(self).phase() == Phase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        let cfa = self.cfg.clone();
        let cfg: &Config = &*cfa;
        let ca = match &cfg.client {
            Some(a) => a,
            None => {
                proof {
                    assert(false);
                }
                return Err(self.fail(INTERNAL_ERROR, out));
            },
        };
        let ghost cc = ca.view();
        assert(self.config().client == Some(cc));
        let n = m.len();
        if n < 8 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        let scheme = (m[4] as u16) * 256 + m[5] as u16;
        let sl = (m[6] as usize) * 256 + m[7] as usize;
        if sl != n - 8 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        if !has_u16(ca.sigs.as_slice(), scheme) {
            return Err(self.fail(ILLEGAL_PARAMETER, out));
        }
        if self.peer.len() == 0 {
            return Err(self.fail(INTERNAL_ERROR, out));
        }
        let sig = vstd::slice::slice_subrange(m, 8, n);
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            State::WaitClientAuth { suite, rx, tx, mut tr, c_hs, c_ap, s_ap, got_cert } => {
                let ghost h = self.hs@;
                let ghost c = self.config();
                let th = tr.hash();
                let mut content: Vec<u8> = Vec::new();
                client_cv_content_x(&mut content, &th);
                let ok = match verilith_x509::parse(self.peer[0].as_slice()) {
                    Some(leaf) => {
                        let v = self.prov.verify_tls_sig(scheme, &leaf.tbs.spki, content.as_slice(), sig);
                        proof {
                            lemma_cert_of(self.peer@[0]@, leaf@);
                            assert(v ==> tls_signed(scheme, cert_of(self.peer@[0]@).tbs.spki, content@, sig@));
                        }
                        v
                    },
                    None => false,
                };
                if !ok {
                    self.state = State::WaitClientAuth { suite, rx, tx, tr, c_hs, c_ap, s_ap, got_cert };
                    return Err(self.fail(DECRYPT_ERROR, out));
                }
                tr.update(m);
                let a = suite_hash_x(suite);
                let th2 = tr.hash();
                let expect = verify_data_x(a, &c_hs, &th2, Ghost(tr.data()));
                let ghost ca_s = SpecClientAuth {
                    cert_msg: self.cmsg@,
                    chain: chain_view(self.peer@),
                    scheme,
                    sig: sig@,
                    now: self.cnow@,
                };
                let ghost h2 = SpecHs { client: Some(ca_s), ..h };
                proof {
                    lemma_cv_msg(m@, scheme, sig@);
                    lemma_with_client(h, ca_s, c);
                    assert(chain_view(self.peer@)[0] == self.peer@[0]@);
                    assert(ca_s.msgs() == self.cmsg@ + m@);
                    assert(ca_s.ok(cc, h.alg(), h.th_eoed(c)));
                    assert(tr.data() =~= h.th_eoed(c) + ca_s.msgs());
                }
                self.enter_wait_finished(Ghost(h2), suite, rx, tx, None, expect, c_ap, s_ap, None);
                Ok(Event::Nothing)
            },
            _ => {
                proof {
                    assert(false);
                }
                Err(Error::Closed)
            },
        }
    }


    fn enter_wait_finished(
        &mut self,
        Ghost(hsv): Ghost<SpecHs>,
        suite: u16,
        rx: Protect<P::Key>,
        tx: Protect<P::Key>,
        early: Option<Protect<P::Key>>,
        expect: Secret,
        c_ap: Secret,
        s_ap: Secret,
        res: Option<Secret>,
    )
        requires
            res matches Some(rm) ==> rm.wf() && rm@ == hsv.res_master(old(self).config()),
            (*old(self).cfg).wf(),
            old(self).buf@.len() <= MAX_MESSAGE + 4,
            hsv.valid(old(self).config()),
            known_suite(suite),
            suite == hsv.choice.suite,
            keys_are(rx, suite, hsv.c_hs()),
            keys_are(tx, suite, hsv.s_ap(old(self).config())),
            old(self).early_taken == hsv.early,
            early matches Some(p) ==> hsv.early && keys_are(p, suite, hsv.c_early()),
            expect.wf() && finished(expect@) == hsv.client_finished(old(self).config()),
            expect@.len() == hash_len(suite_hash(suite)),
            c_ap.wf() && c_ap@ == hsv.c_ap(old(self).config()),
            s_ap.wf() && s_ap@ == hsv.s_ap(old(self).config()),
            hsv.client_ok(old(self).config()),
            hsv.client matches Some(a) ==> chain_view(old(self).peer@) == a.chain,
        ensures
            final(self).wf(),
            final(self).phase() == Phase::WaitFinished,
            final(self).handshake() == hsv,
            final(self).config() == old(self).config(),
    {
        self.hs = Ghost(hsv);
        self.state = State::WaitFinished { suite, rx, tx, early, expect, c_ap, s_ap, res };
    }

    /// The handshake on ClientHelloInner `im`, decrypted from
    /// ClientHelloOuter `m`. `None`: it would need a HelloRetryRequest,
    /// which this server does not do under ECH, so ECH is declined and
    /// nothing has changed.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    fn on_inner_hello(&mut self, cfg: &Config, m: &[u8], im: &[u8], Ghost(pt): Ghost<Seq<u8>>, out: &mut Vec<u8>) -> (r: Option<Result<Event, Error>>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::Start,
            cfg.wf(),
            cfg@ == old(self).config(),
            cfg@.ech_list.len() > 0,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 1),
            ech_unsealed(m@, pt, im@),
            is_msg(im@, 1),
        ensures
            r is None ==> *final(self) == *old(self) && final(out)@ == old(out)@,
            r is Some ==> {
                &&& final(self).wf()
                &&& final(self).config() == old(self).config()
                &&& final(out)@.take(old(out)@.len() as int) == old(out)@
                &&& r matches Some(Ok(e)) ==> e is Nothing
                &&& final(self).phase() == Phase::WaitFinished || final(self).phase() == Phase::Closed
                &&& final(self).phase() == Phase::WaitFinished ==> (final(self).handshake().ech matches Some((o, _)) && o == m@)
            },
    {
        if im.len() < 4 {
            return Some(Err(self.fail(INTERNAL_ERROR, out)));
        }
        let body = vstd::slice::slice_subrange(im, 4, im.len());
        proof {
            assert(body@ =~= im@.skip(4));
        }
        let h = match ClientHello::parse(body) {
            Ok(h) => h,
            Err(a) => return Some(Err(self.fail(a.code(), out))),
        };
        let ghost s = choose|s: SpecHello| parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s) && h.models(s);
        let inner_ok = match h.ech {
            Some(sp) => sp.start <= sp.end && sp.end <= body.len() && ech_inner_x(body, sp.start, sp.end),
            None => false,
        };
        if !inner_ok {
            return Some(Err(self.fail(ILLEGAL_PARAMETER, out)));
        }
        proof {
            lemma_ech_inner(m@, pt, im@, s);
        }
        let o = crate::negotiate::negotiate(body, &h, cfg.suites.as_slice(), cfg.groups.as_slice(), cfg.sigs.as_slice(), cfg.alpn.as_slice());
        proof {
            reveal(outcome);
            reveal(session_id);
            assert(o@ == crate::spec::negotiate(body@, s, cfg@.suites, cfg@.groups, cfg@.sigs, cfg@.alpn));
            assert(outcome(cfg@, im@) == Some(o@));
        }
        let c = match o {
            Outcome::Reject(a) => return Some(Err(self.fail(a.code(), out))),
            Outcome::Retry { .. } => return None,
            Outcome::Accept(c) => c,
        };
        let sp = h.session_id;
        if !(sp.start <= sp.end && sp.end <= body.len() && sp.end - sp.start <= 32) {
            return Some(Err(self.fail(DECODE_ERROR, out)));
        }
        let sid = sp.of(body);
        proof {
            reveal(session_id);
            assert(sid@ == session_id(im@));
        }
        if !(c.suite == 0x1301 || c.suite == 0x1302 || c.suite == 0x1303) {
            return Some(Err(self.fail(INTERNAL_ERROR, out)));
        }
        self.skip = if h.early_data { EARLY_SKIP } else { 0 };
        let ghost choice = match o@ {
            SpecOutcome::Accept(x) => x,
            _ => arbitrary(),
        };
        let tr = Transcript::new(suite_hash_x(c.suite));
        Some(self.accept(cfg, im, body, sid, c, tr, false, Ghost(None), Ghost(choice), &h, Ghost(s), Ghost(Some((m@, pt))), true, false, out))
    }

    /// A ClientHello message `m`, in `Start` or `Retried`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    fn on_client_hello(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::Start || old(self).phase() == Phase::Retried,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 1),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            r matches Ok(e) ==> e is Nothing,
            final(self).phase() == Phase::WaitFinished || final(self).phase() == Phase::Closed || (old(
                self,
            ).phase() == Phase::Start && final(self).phase() == Phase::Retried),
            final(self).phase() == Phase::WaitFinished ==> final(self).handshake().ch == m@ || (final(self).handshake().ech matches Some((o, _)) && o == m@),
    {
        let cfg_arc = self.cfg.clone();
        let cfg: &Config = &*cfg_arc;
        let body = vstd::slice::slice_subrange(m, 4, m.len());
        proof {
            assert(body@ =~= m@.skip(4));
        }
        let h = match ClientHello::parse(body) {
            Ok(h) => h,
            Err(a) => return Err(self.fail(a.code(), out)),
        };
        let ghost s = choose|s: SpecHello| parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s) && h.models(s);
        let o = crate::negotiate::negotiate(body, &h, cfg.suites.as_slice(), cfg.groups.as_slice(), cfg.sigs.as_slice(), cfg.alpn.as_slice());
        proof {
            reveal(outcome);
            reveal(session_id);
            assert(o@ == crate::spec::negotiate(body@, s, cfg@.suites, cfg@.groups, cfg@.sigs, cfg@.alpn));
            assert(outcome(cfg@, m@) == Some(o@));
        }
        let sp = h.session_id;
        if !(sp.start <= sp.end && sp.end <= body.len() && sp.end - sp.start <= 32) {
            return Err(self.fail(DECODE_ERROR, out));
        }
        let sid = sp.of(body);
        proof {
            reveal(session_id);
            assert(sid@ == session_id(m@));
        }
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            State::Start => {
                self.state = State::Start;
                // Encrypted Client Hello (RFC 9849 §7.1): if the client's
                // ECH opens, the handshake is ClientHelloInner's.
                let ech_cfg = cfg.ech_list.len() > 0;
                if ech_cfg && h.ech.is_some() {
                    match open_ech(&mut self.prov, m, body, &h, Ghost(s)) {
                        Err(code) => return Err(self.fail(code, out)),
                        Ok(Some((inner, gpt))) => {
                            let ghost pt = gpt@;
                            match self.on_inner_hello(cfg, m, inner.as_slice(), Ghost(pt), out) {
                                Some(r) => return r,
                                // ClientHelloInner would need a
                                // HelloRetryRequest: ECH is declined.
                                None => {},
                            }
                        },
                        Ok(None) => {},
                    }
                }
                let ech_retry = ech_cfg && h.ech.is_some();
                match o {
                    Outcome::Reject(a) => Err(self.fail(a.code(), out)),
                    Outcome::Retry { suite, group } => {
                        if !(suite == 0x1301 || suite == 0x1302 || suite == 0x1303) {
                            return Err(self.fail(INTERNAL_ERROR, out));
                        }
                        self.send_hrr(m, sid, suite, group, h.early_data, out)
                    },
                    Outcome::Accept(c) => {
                        if !(c.suite == 0x1301 || c.suite == 0x1302 || c.suite == 0x1303) {
                            return Err(self.fail(INTERNAL_ERROR, out));
                        }
                        self.skip = if h.early_data { EARLY_SKIP } else { 0 };
                        let ghost choice = match o@ {
                            SpecOutcome::Accept(x) => x,
                            _ => arbitrary(),
                        };
                        let tr = Transcript::new(suite_hash_x(c.suite));
                        self.accept(cfg, m, body, sid, c, tr, false, Ghost(None), Ghost(choice), &h, Ghost(s), Ghost(None), false, ech_retry, out)
                    },
                }
            },
            State::WaitCh2 { tr, suite, group } => {
                let ghost ch1 = self.ch1@;
                let ghost hrr = self.hrr@;
                self.state = State::WaitCh2 { tr, suite, group };
                match o {
                    Outcome::Accept(c) => {
                        if c.suite != suite || c.group != group {
                            return Err(self.fail(ILLEGAL_PARAMETER, out));
                        }
                        let ghost choice = match o@ {
                            SpecOutcome::Accept(x) => x,
                            _ => arbitrary(),
                        };
                        let mut st2 = State::Closed;
                        core::mem::swap(&mut self.state, &mut st2);
                        let tr = match st2 {
                            State::WaitCh2 { tr, .. } => tr,
                            _ => {
                                proof { assert(false); }
                                Transcript::new(suite_hash_x(c.suite))
                            },
                        };
                        self.state = State::Start;
                        let ech_retry = cfg.ech_list.len() > 0 && h.ech.is_some();
                        self.accept(cfg, m, body, sid, c, tr, true, Ghost(Some((ch1, hrr))), Ghost(choice), &h, Ghost(s), Ghost(None), false, ech_retry, out)
                    },
                    Outcome::Retry { .. } => Err(self.fail(ILLEGAL_PARAMETER, out)),
                    Outcome::Reject(a) => Err(self.fail(a.code(), out)),
                }
            },
            _ => {
                proof { assert(false); }
                Err(Error::Closed)
            },
        }
    }

    /// Which state: 0 Start, 1 Retried, 2 WaitFinished, 3 Connected, 4 Closed.
    fn phase_x(&self) -> (r: u8)
        ensures
            r == 0 <==> self.phase() == Phase::Start,
            r == 1 <==> self.phase() == Phase::Retried,
            r == 2 <==> self.phase() == Phase::WaitFinished,
            r == 3 <==> self.phase() == Phase::Connected,
            r == 4 <==> self.phase() == Phase::Closed,
    {
        match self.state {
            State::Start => 0,
            State::WaitCh2 { .. } => 1,
            State::WaitFinished { .. } => 2,
            State::WaitClientAuth { .. } => 2,
            State::Connected { .. } => 3,
            State::Closed => 4,
        }
    }

    /// The client's Finished `m`.
    #[verifier::spinoff_prover]
    fn on_finished(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::WaitFinished,
            !old(self).in_client_auth(),
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 20),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::Connected || final(self).phase() == Phase::Closed,
            final(self).phase() == Phase::Connected ==> (r matches Ok(e) && e is HandshakeDone),
            r matches Ok(e) ==> e is HandshakeDone && final(self).phase() == Phase::Connected,
    {
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            State::WaitFinished { suite, rx, tx, early, expect, c_ap, s_ap, res } => {
                let n = expect.len();
                if m.len() != 4 + n {
                    self.state = State::WaitFinished { suite, rx, tx, early, expect, c_ap, s_ap, res };
                    return Err(self.fail(DECODE_ERROR, out));
                }
                let got = vstd::slice::slice_subrange(m, 4, m.len());
                if !declassify(ct_eq(got, expect.as_slice())) {
                    self.state = State::WaitFinished { suite, rx, tx, early, expect, c_ap, s_ap, res };
                    return Err(self.fail(DECRYPT_ERROR, out));
                }
                proof {
                    assert(m@.skip(4) =~= expect@);
                    lemma_be3(m@);
                }
                let a = suite_hash_x(suite);
                let kl = suite_key_len_x(suite);
                let (ck, civ) = traffic_keys_x(a, &c_ap, kl);
                let rx2 = Protect::new(self.prov.aead_key(suite, ck.as_slice()), &civ);
                let mut tx2 = tx;
                let ghost o = out@;
                let max_early = self.cfg.max_early;
                let cfa = self.cfg.clone();
                let alpn: &[u8] = match self.alpn_sel {
                    Some(sp) => {
                        let ab = cfa.alpn.as_slice();
                        if sp.start <= sp.end && sp.end <= ab.len() && sp.end - sp.start <= 255 {
                            sp.of(ab)
                        } else {
                            &[]
                        }
                    },
                    None => &[],
                };
                match res {
                    Some(rm) => {
                        let k = self.cfg.tickets;
                        let lifetime = self.cfg.lifetime;
                        let mut i: u8 = 0;
                        while i < k
                            invariant
                                rm.wf(),
                                alpn@.len() <= 255,
                                o.len() <= usize::MAX / 2,
                                out@.len() <= o.len() + 1024 * (i as int),
                                out@.take(o.len() as int) == o,
                                out@.len() >= o.len(),
                                keys_are(tx2, suite, s_ap@),
                            decreases k - i,
                        {
                            let ghost o2 = out@;
                            let (ok, _) = issue_ticket(&mut self.prov, suite, lifetime, i, &rm, max_early, alpn, &mut tx2, out);
                            proof {
                                assert(out@.take(o.len() as int) =~= o2.take(o.len() as int));
                            }
                            if !ok {
                                break;
                            }
                            i = i + 1;
                        }
                    },
                    None => {},
                }
                self.fin = Ghost(m@);
                self.nrx = Ghost(0);
                self.ntx = Ghost(0);
                self.skip = 0;
                self.state = State::Connected { suite, rx: rx2, tx: tx2, c_sec: c_ap, s_sec: s_ap };
                proof {
                    assert(updated(a, c_ap@, 0) == c_ap@);
                    assert(updated(a, s_ap@, 0) == s_ap@);
                }
                Ok(Event::HandshakeDone)
            },
            _ => {
                proof {
                    assert(false);
                }
                Err(Error::Closed)
            },
        }
    }

    /// A KeyUpdate `m` (§4.6.3).
    #[verifier::spinoff_prover]
    fn on_key_update(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::Connected,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 24),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::Connected || final(self).phase() == Phase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        if m.len() != 5 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        let req = m[4];
        if req > 1 {
            return Err(self.fail(ILLEGAL_PARAMETER, out));
        }
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            State::Connected { suite, rx, tx, c_sec, s_sec } => {
                let ghost a = suite_hash(suite);
                let mut tx = tx;
                let mut s_sec = s_sec;
                let ghost o = out@;
                if req == 1 {
                    // update_requested: answer with update_not_requested
                    // under the current keys, then move on.
                    let ku: [u8; 5] = [24, 0, 0, 1, 0];
                    if !tx.seal(22, &ku, out) {
                        self.state = State::Connected { suite, rx, tx, c_sec, s_sec };
                        return Err(self.fail(INTERNAL_ERROR, out));
                    }
                    let (s2, tx2) = rekey(&self.prov, suite, &s_sec);
                    tx = tx2;
                    s_sec = s2;
                    self.ntx = Ghost(self.ntx@ + 1);
                }
                let (c2, rx2) = rekey(&self.prov, suite, &c_sec);
                self.nrx = Ghost(self.nrx@ + 1);
                self.state = State::Connected { suite, rx: rx2, tx, c_sec: c2, s_sec };
                proof {
                    assert(out@.take(o.len() as int) =~= o);
                }
                Ok(Event::Nothing)
            },
            _ => {
                proof {
                    assert(false);
                }
                Err(Error::Closed)
            },
        }
    }

    /// One whole handshake message `m`.
    fn dispatch(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() != Phase::Closed,
            old(out)@.len() <= usize::MAX / 2,
            m@.len() >= 4,
            be24(m@, 1) == m@.len() - 4,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::Connected ==> old(self).phase() == Phase::Connected
                || old(self).phase() == Phase::WaitFinished,
            final(self).phase() == Phase::WaitFinished ==> old(self).phase() == Phase::Start
                || old(self).phase() == Phase::Retried || old(self).phase() == Phase::WaitFinished,
            final(self).phase() == Phase::Retried ==> old(self).phase() == Phase::Start,
            final(self).phase() == Phase::Start ==> false,
            r matches Ok(e) ==> (e is Nothing || (e is HandshakeDone && old(self).phase()
                == Phase::WaitFinished && final(self).phase() == Phase::Connected)),
    {
        let t = m[0];
        let ph = self.phase_x();
        let stage = self.client_stage_x();
        if ph <= 1 && t == 1 {
            self.on_client_hello(m, out)
        } else if ph == 2 && stage == 0 && t == 20 {
            self.on_finished(m, out)
        } else if ph == 2 && stage == 1 && t == 11 {
            self.on_client_certificate(m, out)
        } else if ph == 2 && stage == 2 && t == 15 {
            self.on_client_cv(m, out)
        } else if ph == 3 && t == 24 {
            self.on_key_update(m, out)
        } else {
            Err(self.fail(UNEXPECTED_MESSAGE, out))
        }
    }

    /// A fragment of handshake messages (§5.1: they may span records, but
    /// not a change of keys). Every message this server takes is followed
    /// by a change of keys, or by its answer, except the client's
    /// Certificate and CertificateVerify, which may share a record with
    /// what follows them.
    fn on_handshake(&mut self, frag: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() != Phase::Closed,
            old(out)@.len() <= usize::MAX / 2,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::Connected ==> old(self).phase() == Phase::Connected
                || old(self).phase() == Phase::WaitFinished,
            final(self).phase() == Phase::WaitFinished ==> old(self).phase() == Phase::Start
                || old(self).phase() == Phase::Retried || old(self).phase() == Phase::WaitFinished,
            final(self).phase() == Phase::Retried ==> old(self).phase() == Phase::Start
                || old(self).phase() == Phase::Retried,
            final(self).phase() == Phase::Start ==> old(self).phase() == Phase::Start,
            r matches Ok(e) ==> (e is Nothing || (e is HandshakeDone && old(self).phase()
                == Phase::WaitFinished && final(self).phase() == Phase::Connected)),
    {
        if self.buf.len() == 0 {
            match handshake_length(frag) {
                Some(l) => {
                    if l <= MAX_MESSAGE && l == frag.len() - 4 {
                        return self.dispatch(frag, out);
                    }
                    if l <= MAX_MESSAGE && l < frag.len() - 4 && !self.in_client_auth_x() {
                        return Err(self.fail(UNEXPECTED_MESSAGE, out));
                    }
                    if l > MAX_MESSAGE {
                        return Err(self.fail(UNEXPECTED_MESSAGE, out));
                    }
                },
                None => {},
            }
        }
        if frag.len() > MAX_MESSAGE + 4 - self.buf.len() {
            return Err(self.fail(UNEXPECTED_MESSAGE, out));
        }
        put(&mut self.buf, frag);
        self.drain(out)
    }

    /// The whole handshake messages at the front of `buf`, in order.
    fn drain(&mut self, out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() != Phase::Closed,
            old(out)@.len() <= usize::MAX / 2,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::Connected ==> old(self).phase() == Phase::Connected
                || old(self).phase() == Phase::WaitFinished,
            final(self).phase() == Phase::WaitFinished ==> old(self).phase() == Phase::Start
                || old(self).phase() == Phase::Retried || old(self).phase() == Phase::WaitFinished,
            final(self).phase() == Phase::Retried ==> old(self).phase() == Phase::Start
                || old(self).phase() == Phase::Retried,
            final(self).phase() == Phase::Start ==> old(self).phase() == Phase::Start,
            r matches Ok(e) ==> (e is Nothing || (e is HandshakeDone && old(self).phase()
                == Phase::WaitFinished && final(self).phase() == Phase::Connected)),
    {
        let ghost p0 = self.phase();
        let ghost o = out@;
        // Whether a message of this record has been taken already; then
        // what is sent goes through `tmp`, so that `out` only grows.
        let mut again = false;
        loop
            invariant
                self.wf(),
                self.config() == old(self).config(),
                p0 == old(self).phase(),
                p0 != Phase::Closed,
                o == old(out)@,
                o.len() <= usize::MAX / 2,
                o.len() <= out@.len(),
                out@.take(o.len() as int) == o,
                !again ==> out@ == o,
                again ==> p0 == Phase::WaitFinished && self.phase() == Phase::WaitFinished,
                !again ==> self.phase() == p0,
            decreases self.buf@.len(),
        {
            match handshake_length(self.buf.as_slice()) {
                None => {
                    return Ok(Event::Nothing);
                },
                Some(l) => {
                    if l > MAX_MESSAGE || l < self.buf.len() - 4 && !self.in_client_auth_x() {
                        return Err(self.fail_append(UNEXPECTED_MESSAGE, out));
                    }
                    if l > self.buf.len() - 4 {
                        return Ok(Event::Nothing);
                    }
                    let mut m: Vec<u8> = Vec::new();
                    core::mem::swap(&mut m, &mut self.buf);
                    let k = 4 + l;
                    let more = k < m.len();
                    let mut rest: Vec<u8> = Vec::new();
                    if more {
                        put(&mut rest, vstd::slice::slice_subrange(m.as_slice(), k, m.len()));
                    }
                    let msg = vstd::slice::slice_subrange(m.as_slice(), 0, k);
                    assert(msg@.len() == k);
                    assert(be24(msg@, 1) == be24(m@, 1));
                    if !more && !again {
                        return self.dispatch(msg, out);
                    }
                    let mut tmp: Vec<u8> = Vec::new();
                    let r = self.dispatch(msg, &mut tmp);
                    let ghost o2 = out@;
                    put(out, tmp.as_slice());
                    proof {
                        assert(out@.take(o.len() as int) =~= o2.take(o.len() as int));
                    }
                    if !more {
                        return r;
                    }
                    match r {
                        Err(e) => return Err(e),
                        Ok(_) => {},
                    }
                    // More follows in this record: only after the client's
                    // Certificate or CertificateVerify, which leave the
                    // server waiting for more.
                    if self.phase_x() != 2 {
                        return Err(self.fail_append(UNEXPECTED_MESSAGE, out));
                    }
                    self.buf = rest;
                    again = true;
                },
            }
        }
    }

    /// `fail`, its alert appended to `out` whatever its length.
    fn fail_append(&mut self, code: u8, out: &mut Vec<u8>) -> (r: Error)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).phase() == Phase::Closed,
            final(self).config() == old(self).config(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            r == Error::Sent(code),
    {
        let mut tmp: Vec<u8> = Vec::new();
        let e = self.fail(code, &mut tmp);
        let ghost o = out@;
        put(out, tmp.as_slice());
        assert(out@.take(o.len() as int) =~= o);
        e
    }

    /// Opens a protected record under the client's current keys.
    #[verifier::spinoff_prover]
    fn open_rec(&mut self, hdr: &[u8; 5], body: &mut [u8]) -> (r: Result<(u8, usize), RecErr>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::WaitFinished || old(self).phase() == Phase::Connected,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).phase() == old(self).phase(),
            final(self).handshake() == old(self).handshake(),
            final(self).rx_secret() == old(self).rx_secret(),
            final(self).rx_updates() == old(self).rx_updates(),
            final(self).tx_secret() == old(self).tx_secret(),
            final(self).tx_seq() == old(self).tx_seq(),
            final(self).tx_updates() == old(self).tx_updates(),
            final(self).client_finished() == old(self).client_finished(),
            old(self).phase() == Phase::Connected ==> {
                let s = old(self).handshake().choice.suite;
                let a = suite_hash(s);
                let sec = old(self).rx_secret();
                let o = open_record(s, traffic_key(a, sec, suite_key_len(s)), traffic_iv(a, sec), old(self).rx_seq(), hdr@, old(body)@);
                match r {
                    Ok((ct, n)) => n < final(body)@.len() && o == Ok::<(u8, Seq<u8>), SpecRecErr>((ct, final(body)@.take(n as int))),
                    Err(e) => o == Err::<(u8, Seq<u8>), SpecRecErr>(e.spec()),
                }
            },
            r matches Ok((ct, n)) ==> n < final(body)@.len(),
    {
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            State::WaitFinished { suite, mut rx, tx, early, expect, c_ap, s_ap, res } => {
                let r = rx.open(hdr, body);
                self.state = State::WaitFinished { suite, rx, tx, early, expect, c_ap, s_ap, res };
                r
            },
            State::Connected { suite, mut rx, tx, c_sec, s_sec } => {
                let r = rx.open(hdr, body);
                self.state = State::Connected { suite, rx, tx, c_sec, s_sec };
                r
            },
            State::WaitClientAuth { suite, mut rx, tx, tr, c_hs, c_ap, s_ap, got_cert } => {
                let r = rx.open(hdr, body);
                self.state = State::WaitClientAuth { suite, rx, tx, tr, c_hs, c_ap, s_ap, got_cert };
                r
            },
            _ => {
                proof {
                    assert(false);
                }
                Err(RecErr::BadMac)
            },
        }
    }

    fn in_early_x(&self) -> (r: bool)
        ensures
            r == self.in_early(),
    {
        match &self.state {
            State::WaitFinished { early, .. } => early.is_some(),
            _ => false,
        }
    }

    fn early_hs_x(&self) -> (r: bool)
        requires
            self.wf(),
            self.phase() == Phase::WaitFinished,
        ensures
            r == self.handshake().early,
    {
        // The early key is made when, and only when, 0-RTT data is taken;
        // after EndOfEarlyData, `early_left` is what remains of it.
        self.early_taken
    }

    /// A record while 0-RTT data is coming (§4.2.10): application data
    /// under the client's early key, up to the ticket's allowance, until
    /// EndOfEarlyData, after which the client's handshake key applies.
    #[verifier::spinoff_prover]
    fn read_early(&mut self, hdr: &[u8; 5], body: &mut [u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::WaitFinished,
            old(self).in_early(),
            old(out)@.len() <= usize::MAX / 2,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::WaitFinished || final(self).phase() == Phase::Closed,
            r matches Ok(e) ==> (e is Nothing || e is EarlyData || e is Closed),
            r matches Ok(Event::EarlyData(n)) ==> {
                let s = old(self).handshake().choice.suite;
                let a = suite_hash(s);
                let sec = old(self).handshake().c_early();
                &&& final(self).phase() == Phase::WaitFinished
                &&& old(self).handshake().early
                &&& n < final(body)@.len()
                &&& open_record(s, traffic_key(a, sec, suite_key_len(s)), traffic_iv(a, sec), old(self).early_seq(), hdr@, old(body)@)
                    == Ok::<(u8, Seq<u8>), SpecRecErr>((23u8, final(body)@.take(n as int)))
            },
    {
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            State::WaitFinished { suite, rx, tx, early: Some(mut ep), expect, c_ap, s_ap, res } => {
                let r = ep.open(hdr, body);
                match r {
                    Err(e) => {
                        self.state = State::WaitFinished { suite, rx, tx, early: Some(ep), expect, c_ap, s_ap, res };
                        let code = match e {
                            RecErr::BadMac => BAD_RECORD_MAC,
                            RecErr::Overflow => RECORD_OVERFLOW,
                            RecErr::NoType => UNEXPECTED_MESSAGE,
                            RecErr::Exhausted => INTERNAL_ERROR,
                        };
                        Err(self.fail(code, out))
                    },
                    Ok((ict, k)) => {
                        if ict == 23 {
                            if k as u64 > self.early_left as u64 {
                                // More than max_early_data_size (§4.2.10).
                                self.state = State::WaitFinished { suite, rx, tx, early: Some(ep), expect, c_ap, s_ap, res };
                                return Err(self.fail(UNEXPECTED_MESSAGE, out));
                            }
                            self.early_left = self.early_left - k as u32;
                            self.state = State::WaitFinished { suite, rx, tx, early: Some(ep), expect, c_ap, s_ap, res };
                            assert(out@.take(out@.len() as int) =~= out@);
                            Ok(Event::EarlyData(k))
                        } else if ict == 22 && k == 4 && body[0] == 5 && body[1] == 0 && body[2] == 0 && body[3] == 0
                            && self.buf.len() == 0 {
                            // EndOfEarlyData, alone in its record (a key
                            // change follows it): the handshake key next.
                            self.state = State::WaitFinished { suite, rx, tx, early: None, expect, c_ap, s_ap, res };
                            assert(out@.take(out@.len() as int) =~= out@);
                            Ok(Event::Nothing)
                        } else if ict == 21 {
                            self.state = State::WaitFinished { suite, rx, tx, early: Some(ep), expect, c_ap, s_ap, res };
                            let content = vstd::slice::slice_subrange(&*body, 0, k);
                            self.on_alert(content, out)
                        } else {
                            self.state = State::WaitFinished { suite, rx, tx, early: Some(ep), expect, c_ap, s_ap, res };
                            Err(self.fail(UNEXPECTED_MESSAGE, out))
                        }
                    },
                }
            },
            other => {
                self.state = other;
                proof {
                    assert(false);
                }
                Err(Error::Closed)
            },
        }
    }

    /// One record from the client: its header and body. What the server
    /// sends in answer is appended to `out`.
    pub fn read_record(&mut self, hdr: &[u8; 5], body: &mut [u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == Phase::Connected ==> old(self).phase() == Phase::Connected
                || old(self).phase() == Phase::WaitFinished,
            final(self).phase() == Phase::WaitFinished ==> old(self).phase() != Phase::Connected
                && old(self).phase() != Phase::Closed,
            final(self).phase() == Phase::Retried ==> old(self).phase() == Phase::Start
                || old(self).phase() == Phase::Retried,
            final(self).phase() == Phase::Start ==> old(self).phase() == Phase::Start,
            old(self).phase() == Phase::Closed ==> (r matches Err(e) && e is Closed),
            r matches Ok(e) && e is HandshakeDone ==> old(self).phase() == Phase::WaitFinished
                && final(self).phase() == Phase::Connected,
            r matches Ok(e) && e is Data ==> old(self).phase() == Phase::Connected
                && final(self).phase() == Phase::Connected,
            r matches Ok(Event::EarlyData(n)) ==> {
                let s = old(self).handshake().choice.suite;
                let a = suite_hash(s);
                let sec = old(self).handshake().c_early();
                &&& old(self).phase() == Phase::WaitFinished && final(self).phase() == Phase::WaitFinished
                &&& old(self).handshake().early && old(self).in_early()
                &&& n < final(body)@.len()
                &&& open_record(s, traffic_key(a, sec, suite_key_len(s)), traffic_iv(a, sec), old(self).early_seq(), hdr@, old(body)@)
                    == Ok::<(u8, Seq<u8>), SpecRecErr>((23u8, final(body)@.take(n as int)))
            },
            r matches Ok(Event::Data(n)) ==> {
                let s = old(self).handshake().choice.suite;
                let a = suite_hash(s);
                let sec = old(self).rx_secret();
                &&& n < final(body)@.len()
                &&& open_record(s, traffic_key(a, sec, suite_key_len(s)), traffic_iv(a, sec), old(self).rx_seq(), hdr@, old(body)@)
                    == Ok::<(u8, Seq<u8>), SpecRecErr>((23u8, final(body)@.take(n as int)))
            },
    {
        let ph = self.phase_x();
        if ph == 4 {
            return Err(Error::Closed);
        }
        if out.len() > usize::MAX / 2 {
            return Err(Error::OutputFull);
        }
        let n = body.len();
        let ln = (hdr[3] as usize) * 256 + hdr[4] as usize;
        if ln != n {
            return Err(self.fail(DECODE_ERROR, out));
        }
        if n > 16640 {
            return Err(self.fail(RECORD_OVERFLOW, out));
        }
        let ct = hdr[0];
        if ph <= 2 && ct == 20 {
            // A change_cipher_spec, which middlebox compatibility mode sends
            // and §5 says to drop, between ClientHello and Finished.
            if ph >= 1 && n == 1 && body[0] == 1 && self.buf.len() == 0 {
                assert(out@.take(out@.len() as int) =~= out@);
                return Ok(Event::Nothing);
            }
            return Err(self.fail(UNEXPECTED_MESSAGE, out));
        }
        if ph <= 2 && ct == 21 {
            if n > 16384 {
                return Err(self.fail(RECORD_OVERFLOW, out));
            }
            return self.on_alert(body, out);
        }
        if ph <= 1 {
            if ct == 22 {
                if n > 16384 {
                    return Err(self.fail(RECORD_OVERFLOW, out));
                }
                if n == 0 {
                    return Err(self.fail(UNEXPECTED_MESSAGE, out));
                }
                return self.on_handshake(body, out);
            }
            if ct == 23 && ph == 1 && self.skip >= n {
                // 0-RTT data after a HelloRetryRequest (§4.2.10).
                self.skip = self.skip - n;
                assert(out@.take(out@.len() as int) =~= out@);
                return Ok(Event::Nothing);
            }
            return Err(self.fail(UNEXPECTED_MESSAGE, out));
        }
        if ct != 23 {
            return Err(self.fail(UNEXPECTED_MESSAGE, out));
        }
        if ph == 2 && self.in_early_x() {
            return self.read_early(hdr, body, out);
        }
        let res = self.open_rec(hdr, body);
        match res {
            Err(e) => {
                if ph == 2 && matches!(e, RecErr::BadMac) && self.skip >= n {
                    // 0-RTT data the server did not take (§4.2.10).
                    self.skip = self.skip - n;
                    assert(out@.take(out@.len() as int) =~= out@);
                    return Ok(Event::Nothing);
                }
                let code = match e {
                    RecErr::BadMac => BAD_RECORD_MAC,
                    RecErr::Overflow => RECORD_OVERFLOW,
                    RecErr::NoType => UNEXPECTED_MESSAGE,
                    RecErr::Exhausted => INTERNAL_ERROR,
                };
                Err(self.fail(code, out))
            },
            Ok((ict, k)) => {
                self.skip = 0;
                let content = vstd::slice::slice_subrange(&*body, 0, k);
                if ict == 22 {
                    if k == 0 {
                        return Err(self.fail(UNEXPECTED_MESSAGE, out));
                    }
                    self.on_handshake(content, out)
                } else if ict == 21 {
                    self.on_alert(content, out)
                } else if ict == 23 && ph == 3 && self.buf.len() == 0 {
                    assert(out@.take(out@.len() as int) =~= out@);
                    Ok(Event::Data(k))
                } else {
                    Err(self.fail(UNEXPECTED_MESSAGE, out))
                }
            },
        }
    }

    /// Protects application data `data` into `out`.
    pub fn write(&mut self, data: &[u8], out: &mut Vec<u8>) -> (r: Result<(), Error>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).phase() == old(self).phase(),
            r is Ok ==> (old(self).phase() == Phase::Connected || (old(self).phase() == Phase::WaitFinished
                && old(self).handshake().early)) && {
                let s = old(self).handshake().choice.suite;
                let a = suite_hash(s);
                let sec = old(self).tx_secret();
                final(out)@ == old(out)@ + seal_chunks(s, traffic_key(a, sec, suite_key_len(s)), traffic_iv(a, sec), old(self).tx_seq(), 23, data@)
            },
            r is Err ==> final(out)@ == old(out)@,
    {
        if out.len() > usize::MAX / 4 || data.len() > usize::MAX / 4 {
            return Err(Error::OutputFull);
        }
        let half = match &self.state {
            State::WaitFinished { .. } => self.early_hs_x(),
            _ => false,
        };
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            State::Connected { suite, rx, mut tx, c_sec, s_sec } => {
                proof {
                    assert(out@.len() + data@.len() + 22 * (data@.len() / 16384 + 1) + 16384 + 32 <= usize::MAX) by (nonlinear_arith)
                        requires out@.len() <= usize::MAX / 4, data@.len() <= usize::MAX / 4, usize::MAX >= 0xffff_ffff;
                }
                let ok = tx.seal_all(23, data, out);
                self.state = State::Connected { suite, rx, tx, c_sec, s_sec };
                if ok { Ok(()) } else { Err(Error::OutputFull) }
            },
            State::WaitFinished { suite, rx, mut tx, early, expect, c_ap, s_ap, res } => {
                // 0.5-RTT data (§4.4.4): an answer to 0-RTT data, before
                // the client's Finished. Only when 0-RTT data was taken.
                if !half {
                    self.state = State::WaitFinished { suite, rx, tx, early, expect, c_ap, s_ap, res };
                    return Err(Error::Closed);
                }
                proof {
                    assert(out@.len() + data@.len() + 22 * (data@.len() / 16384 + 1) + 16384 + 32 <= usize::MAX) by (nonlinear_arith)
                        requires out@.len() <= usize::MAX / 4, data@.len() <= usize::MAX / 4, usize::MAX >= 0xffff_ffff;
                }
                let ok = tx.seal_all(23, data, out);
                self.state = State::WaitFinished { suite, rx, tx, early, expect, c_ap, s_ap, res };
                if ok { Ok(()) } else { Err(Error::OutputFull) }
            },
            other => {
                self.state = other;
                Err(Error::Closed)
            },
        }
    }

    /// Sends close_notify and closes.
    pub fn close(&mut self, out: &mut Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).phase() == Phase::Closed,
            final(self).config() == old(self).config(),
    {
        if out.len() > usize::MAX / 2 {
            self.state = State::Closed;
            return;
        }
        let mut st = State::Closed;
        core::mem::swap(&mut self.state, &mut st);
        let body: [u8; 2] = [1, 0];
        match st {
            State::Connected { mut tx, .. } => {
                tx.seal(21, &body, out);
            },
            State::WaitFinished { mut tx, .. } => {
                tx.seal(21, &body, out);
            },
            State::WaitClientAuth { mut tx, .. } => {
                tx.seal(21, &body, out);
            },
            _ => {
                plain_header_x(out, 21, 2);
                put(out, &body);
            },
        }
    }

    /// With client authentication, the client's certificates, leaf first,
    /// once its chain and CertificateVerify checked out (empty if it sent
    /// none, or before). Once connected, `lemma_connected` says what they
    /// are.
    pub fn peer_certificates(&self) -> (r: &[Vec<u8>])
        ensures
            chain_view(r@) == self.peer_chain(),
    {
        self.peer.as_slice()
    }

    /// Whether this handshake took the client's 0-RTT data.
    pub fn early_accepted(&self) -> bool {
        self.early_taken
    }

    /// The ALPN protocol chosen, once the server has sent its flight.
    pub fn alpn(&self) -> Option<&[u8]> {
        match self.alpn_sel {
            Some(sp) => {
                let a = self.cfg.alpn.as_slice();
                if sp.start <= sp.end && sp.end <= a.len() {
                    Some(sp.of(a))
                } else {
                    None
                }
            },
            None => None,
        }
    }
}

} // verus!
