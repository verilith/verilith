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
use crate::crypto::*;
use crate::hello::*;
use crate::keys::*;
use crate::messages::*;
use crate::negotiate::*;
use crate::protect::*;
use crate::record::*;
use crate::spec::*;
use crate::spec_keys::*;
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
}

impl Config {
    pub closed spec fn view(&self) -> SpecCfg {
        SpecCfg {
            suites: self.suites@,
            groups: self.groups@,
            sigs: self.sigs@,
            alpn: self.alpn@,
            chain: self.chain@,
        }
    }

    pub closed spec fn wf(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.suites@.len() ==> known_suite(#[trigger] self.suites@[i])
        &&& self.cert@ == certificate(self.chain@)
        &&& self.cert@.len() < 0x100_0000
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
        Some(Config { suites, groups, sigs, alpn, cert, chain: Ghost(chain_view(chain@)), tickets: 2, lifetime: 21600 })
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
    WaitFinished {
        suite: u16,
        rx: Protect<K>,
        tx: Protect<K>,
        expect: Secret,
        c_ap: Secret,
        s_ap: Secret,
        /// resumption_master_secret, if the server will send tickets.
        res: Option<Secret>,
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

proof fn lemma_or_xor(acc: u8, x: u8, y: u8)
    ensures
        ((acc | (x ^ y)) == 0) == (acc == 0 && x == y),
{
    assert(((acc | (x ^ y)) == 0) == (acc == 0 && x == y)) by (bit_vector);
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
    tr: &mut Transcript,
    s_hs: &Secret,
) -> (r: Option<(Vec<u8>, Ghost<Seq<u8>>)>)
    requires
        cfg.wf(),
        old(tr).wf(),
        s_hs.wf(),
        alpn matches Some(p) ==> p@.len() <= 255,
        tp matches Some(t) ==> t@.len() <= 60000,
    ensures
        final(tr).wf(),
        final(tr).alg() == old(tr).alg(),
        r matches Some((fl, sig)) ==> {
            let a = old(tr).alg();
            let ee = encrypted_extensions(
                opt_view(alpn),
                opt_view(tp),
            );
            let cert = certificate(cfg@.chain);
            let th_cert = old(tr).data() + ee + cert;
            let cv = certificate_verify(scheme, sig@);
            let sf = finished(verify_data(a, s_hs@, th_cert + cv));
            &&& signed(scheme, cv_content(hash(a, th_cert)), sig@)
            &&& fl@ == ee + cert + cv + sf
            &&& final(tr).data() == th_cert + cv + sf
            &&& fl@.len() < 0x100_0000 + 0x3_0000
        },
{
    let a = tr.alg_x();
    let ghost t0 = tr.data();
    let mut fl: Vec<u8> = Vec::new();
    encrypted_extensions_x(&mut fl, alpn, tp);
    let ghost ee = fl@;
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
        assert(th_cert =~= t0 + ee + cfg.cert@);
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
        assert(fl@ =~= ee + cfg.cert@ + cv@ + sf@);
        assert(tr.data() =~= th_cert + cv@ + sf@);
    }
    Some((fl, Ghost(sig@)))
}

/// The server's flight when resuming: EncryptedExtensions and Finished.
fn resumed_flight(alpn: Option<&[u8]>, tp: Option<&[u8]>, tr: &mut Transcript, s_hs: &Secret) -> (r: Vec<u8>)
    requires
        old(tr).wf(),
        s_hs.wf(),
        alpn matches Some(p) ==> p@.len() <= 255,
        tp matches Some(t) ==> t@.len() <= 60000,
    ensures
        final(tr).wf(),
        final(tr).alg() == old(tr).alg(),
        ({
            let a = old(tr).alg();
            let ee = encrypted_extensions(
                opt_view(alpn),
                opt_view(tp),
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
    encrypted_extensions_x(&mut fl, alpn, tp);
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
        hsv.resumed is None ==> ({
            let a = hsv.alg();
            let ee = encrypted_extensions(hsv.alpn(cc), hsv.tp);
            let cert = certificate(cc.chain);
            let th_cert = th_sh + ee + cert;
            let cv = certificate_verify(hsv.choice.signature_scheme, hsv.sig);
            let sf = finished(verify_data(a, server_hs_traffic(a, hsv.psk(), hsv.dhe, th_sh), th_cert + cv));
            &&& signed(hsv.choice.signature_scheme, cv_content(hash(a, th_cert)), hsv.sig)
            &&& fl == ee + cert + cv + sf
            &&& th_sfin == th_cert + cv + sf
        }),
        hsv.resumed is Some ==> ({
            let a = hsv.alg();
            let ee = encrypted_extensions(hsv.alpn(cc), hsv.tp);
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
        hsv.client_finished(cc) == finished(verify_data(hsv.alg(), client_hs_traffic(hsv.alg(), hsv.psk(), hsv.dhe, th_sh), th_sfin)),
        hsv.c_ap(cc) == client_ap_traffic(hsv.alg(), hsv.psk(), hsv.dhe, th_sfin),
        hsv.s_ap(cc) == server_ap_traffic(hsv.alg(), hsv.psk(), hsv.dhe, th_sfin),
        hsv.res_master(cc) == resumption_master(hsv.alg(), hsv.psk(), hsv.dhe, th_sfin + hsv.client_finished(cc)),
{
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
    assert(th_sh == hsv.th_sh());
    assert(pre == hsv.prefix());
    if hsv.resumed is None {
        let th_cert = th_sh + encrypted_extensions(hsv.alpn(cc), hsv.tp) + certificate(cc.chain);
        assert(th_cert == hsv.th_cert(cc));
        assert(th_cert + hsv.certificate_verify() == hsv.th_cv(cc));
    } else {
        assert(th_sh + encrypted_extensions(hsv.alpn(cc), hsv.tp) == hsv.th_cv(cc));
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
) -> bool {
    let h = p.hs@;
    &&& h.valid(cc)
    &&& h.retry == retry
    &&& h.resumed == resumed
    &&& h.ch == m
    &&& h.choice == choice
    &&& h.tp == tp
    &&& p.sh@ == h.server_hello()
    &&& p.sh@.len() < 65536
    &&& p.fl@ == h.flight(cc)
    &&& p.fl@.len() < 0x100_0000 + 0x3_0000
    &&& p.c_hs.wf() && p.c_hs@ == h.c_hs()
    &&& p.s_hs.wf() && p.s_hs@ == h.s_hs()
    &&& p.expect.wf() && finished(p.expect@) == h.client_finished(cc)
    &&& p.expect@.len() == hash_len(suite_hash(choice.suite))
    &&& p.c_ap.wf() && p.c_ap@ == h.c_ap(cc)
    &&& p.s_ap.wf() && p.s_ap@ == h.s_ap(cc)
    &&& p.res matches Some(rm) ==> rm.wf() && rm@ == h.res_master(cc)
}

/// The server's side of the key exchange, its random, and ServerHello.
fn exchange<P: Provider>(prov: &mut P, peer: &[u8], sid: &[u8], suite: u16, group: u16, psk: bool) -> (r: Result<
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
    let mut sh: Vec<u8> = Vec::new();
    server_hello_x(&mut sh, &random, sid, suite, group, share.as_slice(), psk);
    Ok((share, shared, dn, random, sh))
}

#[verifier::spinoff_prover]
#[verifier::rlimit(600)]
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
    ensures
        r matches Ok(p) ==> prep_ok(p, cfg@, m@, retry, choice, resumed, opt_view(tp)),
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
        let (share, shared, dn, random, sh) = match exchange(prov, peer, sid, suite, c.group, resuming) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        let dhe = vstd::slice::slice_subrange(vstd::array::array_as_slice(&shared), 0, dn);
        assert(dhe@ =~= shared@.take(dn as int));
        let ghost pre = tr.data();
        tr.update(m);
        tr.update(sh.as_slice());
        let ghost th_sh = tr.data();
        let th = tr.hash();
        let (hs, c_hs, s_hs) = hs_keys(suite, pk.as_slice(), dhe, &th, Ghost(th_sh));
        let (fl, Ghost(sig)) = if resuming {
            (resumed_flight(alpn, tp, &mut tr, &s_hs), Ghost(Seq::<u8>::empty()))
        } else {
            match server_flight(prov, cfg, c.signature_scheme, alpn, tp, &mut tr, &s_hs) {
                Some(x) => x,
                None => return Err(INTERNAL_ERROR),
            }
        };
        let ghost th_sfin = tr.data();
        let th4 = tr.hash();
        let expect = verify_data_x(a, &c_hs, &th4, Ghost(th_sfin));
        let ms = master_secret_x(a, &hs, Ghost(pk@), Ghost(dhe@));
        let (c_ap, s_ap, _exp) = ap_traffic_x(a, &ms, &th4, Ghost(pk@), Ghost(dhe@), Ghost(th_sfin));
        let res = if cfg.tickets > 0 && prov.tickets() {
            let mut cf: Vec<u8> = Vec::new();
            finished_x(&mut cf, &expect);
            tr.update(cf.as_slice());
            let th5 = tr.hash();
            Some(resumption_master_x(a, &ms, &th5, Ghost(pk@), Ghost(dhe@), Ghost(tr.data())))
        } else {
            None
        };
        let ghost tpv = opt_view(tp);
        let ghost hsv = SpecHs { retry, ch: m@, choice, random: random@, share: share@, dhe: dhe@, sig, resumed, tp: tpv };
        proof {
            assert(pk@ == hsv.psk());
            assert(hsv.tp == opt_view(tp));
            assert(hsv.alpn(cfg@) == opt_view(alpn));
            lemma_accept_spec(cfg@, hsv, m@, pre, sh@, th_sh, th_sfin, fl@, peer@, alpn, sid@);
            assert(cfg.cert@ == certificate(cfg@.chain));
        }
        proof {
            assert(c_hs@ == hsv.c_hs());
            assert(s_hs@ == hsv.s_hs());
            assert(finished(expect@) == hsv.client_finished(cfg@));
            assert(c_ap@ == hsv.c_ap(cfg@));
            assert(s_ap@ == hsv.s_ap(cfg@));
        }
        proof {
            reveal(prep_ok);
            assert(sh@.len() < 65536);
        }
        Ok(Prep { sh, fl, c_hs, s_hs, expect, c_ap, s_ap, res, hs: Ghost(hsv) })
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

/// Whether `a` and `b` are equal, in time that depends only on their
/// lengths.
pub(crate) fn ct_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    let n = a.len();
    if b.len() != n {
        return false;
    }
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            (acc == 0) == (forall|j: int| 0 <= j < i ==> a@[j] == b@[j]),
        decreases n - i,
    {
        proof {
            lemma_or_xor(acc, a@[i as int], b@[i as int]);
        }
        acc = acc | (a[i] ^ b[i]);
        i = i + 1;
    }
    proof {
        if acc == 0 {
            assert(a@ =~= b@);
        }
    }
    acc == 0
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
) -> (r: Result<Option<(Secret, Ghost<SpecResume>)>, u8>)
    requires
        is_msg(m@, 1),
        body@ == m@.skip(4),
        parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s),
        h.models(s),
        tr.wf(),
        tr.alg() == suite_hash(suite),
        known_suite(suite),
    ensures
        r matches Ok(Some((k, g))) ==> k.wf() && k@ == g@.psk && resumption_ok(m@, tr.data(), suite_hash(suite), g@),
{
    if cfg.tickets == 0 || !prov.tickets() {
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
    if n < 16 || st[0] != 1 || !(st[15] == 32 || st[15] == 48) || n != 16 + st[15] as usize {
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
    let rest = vstd::slice::slice_subrange(st.as_slice(), 16, n);
    let psk = Secret::from_slice(rest, n - 16);
    proof {
        assert(psk@ =~= st@.skip(16));
        assert(ticket_suite_psk(st@) == Some((ts, st@.skip(16))));
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
    if !ct_eq(vd.as_slice(), bd.of(body)) {
        return Err(DECRYPT_ERROR);
    }
    let ghost g = SpecResume { identity: ident@, state: st@, psk: psk@ };
    proof {
        assert(part@ =~= m@.take(4 + bds.start - 2));
        assert(ov(h.psk_modes) == s.psk_modes);
        assert(ov2(h.pre_shared_key) == s.pre_shared_key);
    }
    Ok(Some((psk, Ghost(g))))
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
) -> (r: Option<(Vec<u8>, Ghost<TicketSent>)>)
    requires
        rm.wf(),
    ensures
        r matches Some((nst, t)) ==> {
            let nonce = seq![i];
            &&& t@.lifetime == lifetime
            &&& nst@ == new_session_ticket(t@.lifetime, t@.age_add, nonce, t@.ticket)
            &&& nst@.len() <= 234
            &&& ticket_issued(t@.ticket, ticket_state(suite, t@.time, t@.age_add, ticket_psk(suite_hash(suite), rm@, nonce)))
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
    ticket_state_x(&mut st, suite, time, age_add, &psk);
    let mut ticket: Vec<u8> = Vec::new();
    proof {
        assert(st@.len() <= 64);
    }
    if !prov.seal_ticket(st.as_slice(), &mut ticket) {
        return None;
    }
    assert(ticket@.skip(0) =~= ticket@);
    if ticket.len() > 200 {
        return None;
    }
    let mut nst: Vec<u8> = Vec::new();
    new_session_ticket_x(&mut nst, lifetime, age_add, &nonce, ticket.as_slice());
    proof {
        assert(nonce@ =~= seq![i]);
    }
    if nst.len() > 234 {
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
    tx: &mut Protect<P::Key>,
    out: &mut Vec<u8>,
) -> (r: (bool, Ghost<TicketSent>))
    requires
        rm.wf(),
        old(out)@.len() + 0x20000 <= usize::MAX,
    ensures
        final(tx).suite() == old(tx).suite(),
        final(tx).key() == old(tx).key(),
        final(tx).iv() == old(tx).iv(),
        final(out)@.take(old(out)@.len() as int) == old(out)@,
        old(out)@.len() <= final(out)@.len() <= old(out)@.len() + 256,
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
                new_session_ticket(t.lifetime, t.age_add, nonce, t.ticket),
            )
            &&& ticket_issued(t.ticket, ticket_state(suite, t.time, t.age_add, ticket_psk(suite_hash(suite), rm@, nonce)))
        },
        !r.0 ==> final(out)@ == old(out)@,
{
    let ghost none = TicketSent { lifetime, age_add: 0, time: 0, ticket: Seq::empty() };
    proof {
        assert(out@.take(out@.len() as int) =~= out@);
    }
    let (nst, t) = match make_ticket(prov, suite, lifetime, i, rm) {
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
    /// The ALPN protocol chosen, a span of the configuration's list.
    alpn_sel: Option<Span>,
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
            State::Connected { .. } => Phase::Connected,
            State::Closed => Phase::Closed,
        }
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
            _ => Seq::empty(),
        }
    }

    pub closed spec fn tx_seq(&self) -> u64 {
        match self.state {
            State::Connected { tx, .. } => tx.seq(),
            _ => 0,
        }
    }

    pub closed spec fn tx_updates(&self) -> nat {
        self.ntx@
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
            State::WaitFinished { suite, rx, tx, expect, c_ap, s_ap, res } => {
                let h = self.hs@;
                let c = self.config();
                &&& self.hs_ok()
                &&& suite == h.choice.suite
                &&& keys_are(rx, suite, h.c_hs())
                &&& keys_are(tx, suite, h.s_hs())
                &&& expect.wf() && finished(expect@) == h.client_finished(c)
                &&& expect@.len() == hash_len(suite_hash(suite))
                &&& c_ap.wf() && c_ap@ == h.c_ap(c)
                &&& s_ap.wf() && s_ap@ == h.s_ap(c)
                &&& res matches Some(rm) ==> rm.wf() && rm@ == h.res_master(c)
            },
            State::Connected { suite, rx, tx, c_sec, s_sec } => {
                let h = self.hs@;
                let c = self.config();
                &&& self.hs_ok()
                &&& suite == h.choice.suite
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
            alpn_sel: None,
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
        let body: [u8; 2] = [2, code];
        let ghost o = out@;
        match st {
            State::WaitFinished { mut tx, .. } => {
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
            r matches Ok(e) ==> !(e is HandshakeDone) && !(e is Data),
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
        out: &mut Vec<u8>,
    ) -> (r: Result<Event, Error>)
        requires
            parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s),
            h.models(s),
            old(self).wf(),
            old(self).phase() == Phase::Start || old(self).phase() == Phase::Retried,
            cfg.wf(),
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
            final(self).phase() == Phase::WaitFinished ==> final(self).handshake().retry == retry && final(self).handshake().ch == m@,
    {
        let rs = match try_resume(&mut self.prov, cfg, m, body, h, Ghost(s), c.suite, &tr) {
            Ok(x) => x,
            Err(code) => return Err(self.fail(code, out)),
        };
        let (psk, Ghost(resumed)) = match rs {
            Some((k, g)) => (Some(k), Ghost(Some(g@))),
            None => (None, Ghost(None)),
        };
        let p = match prepare(&mut self.prov, cfg, m, body, sid, c, tr, Ghost(retry), Ghost(choice), psk, Ghost(resumed), None) {
            Ok(p) => p,
            Err(code) => return Err(self.fail(code, out)),
        };
        let Prep { sh, fl, c_hs, s_hs, expect, c_ap, s_ap, res, hs: Ghost(hsv) } = p;
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
        if retried {
            self.skip = 0;
        }
        self.alpn_sel = match c.alpn {
            Some((ours, _)) => Some(ours),
            None => None,
        };
        self.enter_wait_finished(Ghost(hsv), suite, rx, tx, expect, c_ap, s_ap, res);
        Ok(Event::Nothing)
    }


    fn enter_wait_finished(
        &mut self,
        Ghost(hsv): Ghost<SpecHs>,
        suite: u16,
        rx: Protect<P::Key>,
        tx: Protect<P::Key>,
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
            keys_are(tx, suite, hsv.s_hs()),
            expect.wf() && finished(expect@) == hsv.client_finished(old(self).config()),
            expect@.len() == hash_len(suite_hash(suite)),
            c_ap.wf() && c_ap@ == hsv.c_ap(old(self).config()),
            s_ap.wf() && s_ap@ == hsv.s_ap(old(self).config()),
        ensures
            final(self).wf(),
            final(self).phase() == Phase::WaitFinished,
            final(self).handshake() == hsv,
            final(self).config() == old(self).config(),
    {
        self.hs = Ghost(hsv);
        self.state = State::WaitFinished { suite, rx, tx, expect, c_ap, s_ap, res };
    }

    /// A ClientHello message `m`, in `Start` or `Retried`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
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
            final(self).phase() == Phase::WaitFinished ==> final(self).handshake().ch == m@,
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
                        self.accept(cfg, m, body, sid, c, tr, false, Ghost(None), Ghost(choice), &h, Ghost(s), out)
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
                        self.accept(cfg, m, body, sid, c, tr, true, Ghost(Some((ch1, hrr))), Ghost(choice), &h, Ghost(s), out)
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
            State::WaitFinished { suite, rx, tx, expect, c_ap, s_ap, res } => {
                let n = expect.len();
                if m.len() != 4 + n {
                    self.state = State::WaitFinished { suite, rx, tx, expect, c_ap, s_ap, res };
                    return Err(self.fail(DECODE_ERROR, out));
                }
                let got = vstd::slice::slice_subrange(m, 4, m.len());
                if !ct_eq(got, expect.as_slice()) {
                    self.state = State::WaitFinished { suite, rx, tx, expect, c_ap, s_ap, res };
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
                let (sk, siv) = traffic_keys_x(a, &s_ap, kl);
                let mut tx2 = Protect::new(self.prov.aead_key(suite, sk.as_slice()), &siv);
                let ghost o = out@;
                match res {
                    Some(rm) => {
                        let k = self.cfg.tickets;
                        let lifetime = self.cfg.lifetime;
                        let mut i: u8 = 0;
                        while i < k
                            invariant
                                rm.wf(),
                                o.len() <= usize::MAX / 2,
                                out@.len() <= o.len() + 256 * (i as int),
                                out@.take(o.len() as int) == o,
                                out@.len() >= o.len(),
                                keys_are(tx2, suite, s_ap@),
                            decreases k - i,
                        {
                            let ghost o2 = out@;
                            let (ok, _) = issue_ticket(&mut self.prov, suite, lifetime, i, &rm, &mut tx2, out);
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
                || old(self).phase() == Phase::Retried,
            final(self).phase() == Phase::Retried ==> old(self).phase() == Phase::Start,
            final(self).phase() == Phase::Start ==> false,
            r matches Ok(e) ==> (e is Nothing || (e is HandshakeDone && old(self).phase()
                == Phase::WaitFinished && final(self).phase() == Phase::Connected)),
    {
        let t = m[0];
        let ph = self.phase_x();
        if ph <= 1 && t == 1 {
            self.on_client_hello(m, out)
        } else if ph == 2 && t == 20 {
            self.on_finished(m, out)
        } else if ph == 3 && t == 24 {
            self.on_key_update(m, out)
        } else {
            Err(self.fail(UNEXPECTED_MESSAGE, out))
        }
    }

    /// A fragment of handshake messages (§5.1: they may span records, but
    /// not a change of keys, and every message this server takes is
    /// followed by one, or by its answer).
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
                    if l <= MAX_MESSAGE && l < frag.len() - 4 {
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
        match handshake_length(self.buf.as_slice()) {
            None => {
                assert(out@.take(out@.len() as int) =~= out@);
                Ok(Event::Nothing)
            },
            Some(l) => {
                if l > MAX_MESSAGE || l < self.buf.len() - 4 {
                    return Err(self.fail(UNEXPECTED_MESSAGE, out));
                }
                if l > self.buf.len() - 4 {
                    assert(out@.take(out@.len() as int) =~= out@);
                    return Ok(Event::Nothing);
                }
                let mut m: Vec<u8> = Vec::new();
                core::mem::swap(&mut m, &mut self.buf);
                self.dispatch(m.as_slice(), out)
            },
        }
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
            State::WaitFinished { suite, mut rx, tx, expect, c_ap, s_ap, res } => {
                let r = rx.open(hdr, body);
                self.state = State::WaitFinished { suite, rx, tx, expect, c_ap, s_ap, res };
                r
            },
            State::Connected { suite, mut rx, tx, c_sec, s_sec } => {
                let r = rx.open(hdr, body);
                self.state = State::Connected { suite, rx, tx, c_sec, s_sec };
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
            r is Ok ==> old(self).phase() == Phase::Connected && {
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
            _ => {
                plain_header_x(out, 21, 2);
                put(out, &body);
            },
        }
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
