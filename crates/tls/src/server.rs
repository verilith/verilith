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
    suites: Vec<u16>,
    groups: Vec<u16>,
    sigs: Vec<u16>,
    alpn: Vec<u8>,
    cert: Vec<u8>,
    chain: Ghost<Seq<Seq<u8>>>,
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
        Some(Config { suites, groups, sigs, alpn, cert, chain: Ghost(chain_view(chain@)) })
    }
}

/// Where a connection is (Appendix A.2).
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
    WaitFinished { suite: u16, rx: Protect<K>, tx: Protect<K>, expect: Secret, c_ap: Secret, s_ap: Secret },
    Connected { suite: u16, rx: Protect<K>, tx: Protect<K>, c_sec: Secret, s_sec: Secret },
    Closed,
}

/// What a record from the client came to.
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

proof fn lemma_be3(m: Seq<u8>)
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

/// The handshake traffic secrets and keys for shared secret `dhe` and
/// transcript `th_sh` (ClientHello..ServerHello), whose hash is `th`.
fn hs_keys<P: Provider>(prov: &P, suite: u16, dhe: &[u8], th: &Secret, Ghost(th_sh): Ghost<Seq<u8>>) -> (r: (
    Secret,
    Secret,
    Secret,
    Protect<P::Key>,
    Protect<P::Key>,
))
    requires
        th.wf(),
        th@ == hash(suite_hash(suite), th_sh),
        th@.len() == hash_len(suite_hash(suite)),
    ensures
        r.0.wf() && r.0@ == handshake_secret(suite_hash(suite), dhe@),
        r.1.wf() && r.1@ == client_hs_traffic(suite_hash(suite), dhe@, th_sh),
        r.2.wf() && r.2@ == server_hs_traffic(suite_hash(suite), dhe@, th_sh),
        keys_are(r.3, suite, r.1@),
        keys_are(r.4, suite, r.2@),
        r.4.seq() == 0,
{
    let a = suite_hash_x(suite);
    let kl = suite_key_len_x(suite);
    let hs = handshake_secret_x(a, dhe);
    let (c_hs, s_hs) = hs_traffic_x(a, &hs, th, Ghost(dhe@), Ghost(th_sh));
    let (ck, civ) = traffic_keys_x(a, &c_hs, kl);
    let rx = Protect::new(prov.aead_key(suite, ck.as_slice()), &civ);
    let (sk, siv) = traffic_keys_x(a, &s_hs, kl);
    let tx = Protect::new(prov.aead_key(suite, sk.as_slice()), &siv);
    (hs, c_hs, s_hs, rx, tx)
}

/// The server's flight after ServerHello: EncryptedExtensions,
/// Certificate, CertificateVerify (signed by `prov`) and Finished, added
/// to the transcript as they are made.
fn server_flight<P: Provider>(
    prov: &mut P,
    cfg: &Config,
    scheme: u16,
    alpn: Option<&[u8]>,
    tr: &mut Transcript,
    s_hs: &Secret,
) -> (r: Option<(Vec<u8>, Ghost<Seq<u8>>)>)
    requires
        cfg.wf(),
        old(tr).wf(),
        s_hs.wf(),
        alpn matches Some(p) ==> p@.len() <= 255,
    ensures
        final(tr).wf(),
        final(tr).alg() == old(tr).alg(),
        r matches Some((fl, sig)) ==> {
            let a = old(tr).alg();
            let ee = encrypted_extensions(
                match alpn {
                    Some(p) => Some(p@),
                    None => None,
                },
            );
            let cert = certificate(cfg@.chain);
            let th_cert = old(tr).data() + ee + cert;
            let cv = certificate_verify(scheme, sig@);
            let sf = finished(verify_data(a, s_hs@, th_cert + cv));
            &&& signed(scheme, cv_content(hash(a, th_cert)), sig@)
            &&& fl@ == ee + cert + cv + sf
            &&& final(tr).data() == th_cert + cv + sf
            &&& fl@.len() < 0x100_0000 + 0x2_0000
        },
{
    let a = tr.alg_x();
    let ghost t0 = tr.data();
    let mut fl: Vec<u8> = Vec::new();
    encrypted_extensions_x(&mut fl, alpn);
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
        peer == bytes(m.skip(4), hsv.choice.share),
        key_exchange(hsv.choice.group, peer, hsv.share, hsv.dhe),
        sid == session_id(m),
        sh == server_hello(hsv.random, sid, hsv.choice.suite, hsv.choice.group, hsv.share),
        th_sh == pre + m + sh,
        hsv.alpn(cc) == match alpn {
            Some(p) => Some(p@),
            None => None,
        },
        ({
            let a = hsv.alg();
            let ee = encrypted_extensions(hsv.alpn(cc));
            let cert = certificate(cc.chain);
            let th_cert = th_sh + ee + cert;
            let cv = certificate_verify(hsv.choice.signature_scheme, hsv.sig);
            let sf = finished(verify_data(a, server_hs_traffic(a, hsv.dhe, th_sh), th_cert + cv));
            &&& signed(hsv.choice.signature_scheme, cv_content(hash(a, th_cert)), hsv.sig)
            &&& fl == ee + cert + cv + sf
            &&& th_sfin == th_cert + cv + sf
        }),
    ensures
        hsv.valid(cc),
        sh == hsv.server_hello(),
        th_sh == hsv.th_sh(),
        th_sfin == hsv.th_sfin(cc),
        fl == hsv.flight(cc),
{
    reveal(SpecHs::valid);
    assert(th_sh == hsv.th_sh());
    let th_cert = th_sh + encrypted_extensions(hsv.alpn(cc)) + certificate(cc.chain);
    assert(th_cert == hsv.th_cert(cc));
    assert(th_cert + hsv.certificate_verify() == hsv.th_cv(cc));
    assert(th_sfin =~= hsv.th_sfin(cc));
    assert(fl =~= hsv.flight(cc));
}

/// What `accept` sends and keeps, computed before anything is sent.
struct Prep<K: AeadKey> {
    sh: Vec<u8>,
    fl: Vec<u8>,
    rx: Protect<K>,
    tx: Protect<K>,
    expect: Secret,
    c_ap: Secret,
    s_ap: Secret,
    hs: Ghost<SpecHs>,
}

#[verifier::opaque]
spec fn prep_ok<K: AeadKey>(p: Prep<K>, cc: SpecCfg, m: Seq<u8>, retry: Option<(Seq<u8>, Seq<u8>)>, choice: SpecChoice) -> bool {
    let h = p.hs@;
    &&& h.valid(cc)
    &&& h.retry == retry
    &&& h.ch == m
    &&& h.choice == choice
    &&& p.sh@ == h.server_hello()
    &&& p.sh@.len() < 65536
    &&& p.fl@ == h.flight(cc)
    &&& p.fl@.len() < 0x100_0000 + 0x2_0000
    &&& keys_are(p.rx, choice.suite, h.c_hs())
    &&& keys_are(p.tx, choice.suite, h.s_hs())
    &&& p.tx.seq() == 0
    &&& p.expect.wf() && finished(p.expect@) == h.client_finished(cc)
    &&& p.expect@.len() == hash_len(suite_hash(choice.suite))
    &&& p.c_ap.wf() && p.c_ap@ == h.c_ap(cc)
    &&& p.s_ap.wf() && p.s_ap@ == h.s_ap(cc)
}

/// The server's side of the key exchange, its random, and ServerHello.
fn exchange<P: Provider>(prov: &mut P, peer: &[u8], sid: &[u8], suite: u16, group: u16) -> (r: Result<
    (Vec<u8>, [u8; 64], usize, [u8; 32], Vec<u8>),
    u8,
>)
    requires
        sid@.len() <= 32,
    ensures
        r matches Ok((share, shared, dn, random, sh)) ==> {
            &&& dn <= 64
            &&& key_exchange(group, peer@, share@, shared@.take(dn as int))
            &&& sh@ == server_hello(random@, sid@, suite, group, share@)
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
    server_hello_x(&mut sh, &random, sid, suite, group, share.as_slice());
    Ok((share, shared, dn, random, sh))
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
fn prepare<P: Provider>(
    prov: &mut P,
    cfg: &Config,
    m: &[u8],
    body: &[u8],
    sid: &[u8],
    c: Choice,
    tr: Transcript,
    Ghost(retry): Ghost<Option<(Seq<u8>, Seq<u8>)>>,
    Ghost(choice): Ghost<SpecChoice>,
) -> (r: Result<Prep<P::Key>, u8>)
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
    ensures
        r matches Ok(p) ==> prep_ok(p, cfg@, m@, retry, choice),
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
        let (share, shared, dn, random, sh) = match exchange(prov, peer, sid, suite, c.group) {
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
        let (hs, c_hs, s_hs, rx, mut tx) = hs_keys(&*prov, suite, dhe, &th, Ghost(th_sh));
        let (fl, Ghost(sig)) = match server_flight(prov, cfg, c.signature_scheme, alpn, &mut tr, &s_hs) {
            Some(x) => x,
            None => return Err(INTERNAL_ERROR),
        };
        let ghost th_sfin = tr.data();
        let th4 = tr.hash();
        let expect = verify_data_x(a, &c_hs, &th4, Ghost(th_sfin));
        let ms = master_secret_x(a, &hs, Ghost(dhe@));
        let (c_ap, s_ap, _exp) = ap_traffic_x(a, &ms, &th4, Ghost(dhe@), Ghost(th_sfin));
        let ghost hsv = SpecHs { retry, ch: m@, choice, random: random@, share: share@, dhe: dhe@, sig };
        proof {
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
        Ok(Prep { sh, fl, rx, tx, expect, c_ap, s_ap, hs: Ghost(hsv) })
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
            State::WaitFinished { suite, rx, tx, expect, c_ap, s_ap } => {
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
        out: &mut Vec<u8>,
    ) -> (r: Result<Event, Error>)
        requires
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
        let p = match prepare(&mut self.prov, cfg, m, body, sid, c, tr, Ghost(retry), Ghost(choice)) {
            Ok(p) => p,
            Err(code) => return Err(self.fail(code, out)),
        };
        let Prep { sh, fl, rx, mut tx, expect, c_ap, s_ap, hs: Ghost(hsv) } = p;
        proof {
            reveal(prep_ok);
        }
        let suite = c.suite;
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
        self.enter_wait_finished(Ghost(hsv), suite, rx, tx, expect, c_ap, s_ap);
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
    )
        requires
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
        self.state = State::WaitFinished { suite, rx, tx, expect, c_ap, s_ap };
    }
}

} // verus!
