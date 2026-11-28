//! The client: a sans-IO TLS 1.3 client connection (§2, §4, Appendix
//! A.1), for a full handshake that authenticates the server by its
//! certificate.
//!
//! `ClientConn::new` writes the ClientHello; `read_record` takes one record
//! from the server and appends whatever the client sends in answer to
//! `out`; `write` protects application data. The proofs show, of every
//! connection:
//!
//! - it is only ever in one of the states of Appendix A.1 (`CPhase`), and
//!   moves between them only forward;
//! - once `Connected`, the handshake was `SpecCliHs::valid`: the
//!   ClientHellos are `spec_client_hs::client_hello`, the ServerHello (and
//!   HelloRetryRequest) are ones `read_sh` takes, the EncryptedExtensions
//!   one `read_ee` takes, the server's chain leads to a trust anchor and
//!   names the host (`server_chain_ok`), its CertificateVerify is the
//!   leaf's key's signature over this transcript, and its Finished is the
//!   one RFC 8446 defines for it (compared in constant time);
//! - the client's Finished is the one RFC 8446 defines for the
//!   transcript, sealed under its handshake keys;
//! - application data is delivered only once `Connected`, and only from a
//!   record that opened under the server's application traffic keys
//!   (after however many KeyUpdates); `write` seals under the client's.
use crate::client::*;
use crate::client_hs::*;
use crate::crypto::*;
use crate::ct::{ct_eq, declassify};
use crate::keys::*;
use crate::spec_keys::*;
use crate::messages::*;
use crate::negotiate::valid_host_name_x;
use crate::protect::*;
use crate::record::*;
#[cfg(verus_only)]
use crate::server::{keys_are, lemma_be3, lemma_cv_msg};
use crate::server::{Error, Event, hs_keys, protect_of, rekey, suite_hash_x, suite_key_len_x, MAX_MESSAGE,
    BAD_RECORD_MAC, DECODE_ERROR, DECRYPT_ERROR, ILLEGAL_PARAMETER, INTERNAL_ERROR, RECORD_OVERFLOW, UNEXPECTED_MESSAGE};
use crate::server_auth::*;
use crate::spec::*;
use crate::spec_client::*;
use crate::spec_client_hs::*;
use crate::spec_keys::*;
use crate::spec_record::*;
use crate::spec_server::*;
use crate::spec_server_auth::*;
use alloc::sync::Arc;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// Where a client connection is (Appendix A.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CPhase {
    /// ClientHello sent (a second one, after a HelloRetryRequest):
    /// waiting for the ServerHello.
    WaitHello,
    /// ServerHello taken: waiting for the server's encrypted flight.
    WaitFlight,
    /// The handshake is over: application data both ways.
    Connected,
    /// Closed, by an alert either way or close_notify.
    Closed,
}

/// The handshake keys and transcript, from ServerHello on. `stage`: 0
/// waiting for EncryptedExtensions, 1 for CertificateRequest or
/// Certificate, 2 for Certificate (after a CertificateRequest), 3 for
/// CertificateVerify, 4 for Finished.
struct Flight<K: AeadKey> {
    suite: u16,
    tr: Transcript,
    rx: Protect<K>,
    tx: Protect<K>,
    c_hs: Secret,
    s_hs: Secret,
    hsec: Secret,
    stage: u8,
    /// The server sent a CertificateRequest.
    cr: bool,
}

enum CState<K: AeadKey> {
    WaitSh,
    WaitSh2 { suite: u16, tr: Transcript },
    Flight { f: Flight<K> },
    Connected { suite: u16, rx: Protect<K>, tx: Protect<K>, c_sec: Secret, s_sec: Secret },
    Closed,
}

/// The groups of a list of key shares.
fn groups_of(v: &Vec<(u16, Vec<u8>)>) -> (r: Vec<u16>)
    ensures
        r@ == share_groups(shares_view(v@)),
{
    let mut r: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            r@ == share_groups(shares_view(v@)).take(i as int),
        decreases v@.len() - i,
    {
        r.push(v[i].0);
        proof {
            assert(share_groups(shares_view(v@)).take(i as int + 1) =~= share_groups(shares_view(v@)).take(i as int).push(
                v@[i as int].0,
            ));
        }
        i = i + 1;
    }
    assert(share_groups(shares_view(v@)).take(v@.len() as int) =~= share_groups(shares_view(v@)));
    r
}

/// The share for `g` in `v` (`share_of`).
fn share_of_x(v: &Vec<(u16, Vec<u8>)>, g: u16) -> (r: &[u8])
    ensures
        r@ == share_of(shares_view(v@), g),
{
    let ghost sv = shares_view(v@);
    let mut i: usize = 0;
    assert(sv.skip(0) =~= sv);
    while i < v.len()
        invariant
            i <= v@.len(),
            sv == shares_view(v@),
            share_of(sv, g) == share_of(sv.skip(i as int), g),
        decreases v@.len() - i,
    {
        proof {
            assert(sv.skip(i as int)[0] == sv[i as int]);
            assert(sv.skip(i as int).drop_first() =~= sv.skip(i as int + 1));
        }
        if v[i].0 == g {
            return v[i].1.as_slice();
        }
        i = i + 1;
    }
    let e: &[u8] = &[];
    assert(e@ =~= Seq::<u8>::empty());
    e
}

/// A ServerHello's fields don't change when the later ones do.
proof fn lemma_frame_sh(a: SpecCliHs, b: SpecCliHs, c: SpecCliCfg, h: Seq<u8>)
    requires
        a.random == b.random,
        a.sid == b.sid,
        a.shares == b.shares,
        a.retry == b.retry,
        a.sh == b.sh,
        a.suite == b.suite,
        a.group == b.group,
        a.server_share == b.server_share,
        a.dhe == b.dhe,
    ensures
        a.sh_ok(c, h) == b.sh_ok(c, h),
        a.th_sh(c, h) == b.th_sh(c, h),
        a.c_hs(c, h) == b.c_hs(c, h),
        a.s_hs(c, h) == b.s_hs(c, h),
{
    reveal(SpecCliHs::sh_ok);
    reveal(SpecCliHs::th_sh);
    reveal(SpecCliHs::c_hs);
    reveal(SpecCliHs::s_hs);
}

/// Whether `sig` is a CertificateVerify signature with `scheme` by the
/// key of the certificate `leaf` over §4.4.3's content for transcript
/// hash `th`.
fn cv_sig_ok<P: Provider>(prov: &P, leaf: &[u8], scheme: u16, th: &Secret, sig: &[u8]) -> (r: bool)
    requires
        th.wf(),
    ensures
        r ==> parses(leaf@) && tls_signed(scheme, cert_of(leaf@).tbs.spki, cv_content(th@), sig@),
{
    let mut content: Vec<u8> = Vec::new();
    cv_content_x(&mut content, th);
    match verilith_x509::parse(leaf) {
        Some(c) => {
            let v = prov.verify_tls_sig(scheme, &c.tbs.spki, content.as_slice(), sig);
            proof {
                lemma_cert_of(leaf@, c@);
            }
            v
        },
        None => false,
    }
}

/// The CertificateVerify step: what holds of the handshake before it
/// holds after, and the transcript moves on.
proof fn lemma_cv_step(h: SpecCliHs, h2: SpecCliHs, c: SpecCliCfg, host: Seq<u8>, d0: Seq<u8>)
    requires
        h2 == (SpecCliHs { cv: h2.cv, scheme: h2.scheme, sig: h2.sig, ..h }),
        h.sh_ok(c, host),
        h.ee_ok(c),
        h.cert_ok(c, host),
        d0 == h.th_cert(c, host),
        h2.cv == certificate_verify(h2.scheme, h2.sig),
        c.sigs.contains(h2.scheme),
        tls_signed(h2.scheme, cert_of(h.chain[0]).tbs.spki, cv_content(hash(h.alg(), d0)), h2.sig),
    ensures
        h2.sh_ok(c, host),
        h2.ee_ok(c),
        h2.cert_ok(c, host),
        h2.cv_ok(c, host),
        h2.th_sh(c, host) == h.th_sh(c, host),
        h2.c_hs(c, host) == h.c_hs(c, host),
        h2.s_hs(c, host) == h.s_hs(c, host),
        d0 + h2.cv == h2.th_cv(c, host),
        h2.chain == h.chain,
        h2.alpn == h.alpn,
{
    lemma_frame_sh(h, h2, c, host);
    reveal(SpecCliHs::ee_ok);
    reveal(SpecCliHs::cert_ok);
    reveal(SpecCliHs::th_cert);
    reveal(SpecCliHs::th_cv);
    reveal(SpecCliHs::cv_ok);
}

/// The server's Finished step.
proof fn lemma_fin_step(h: SpecCliHs, h2: SpecCliHs, c: SpecCliCfg, host: Seq<u8>)
    requires
        h2 == (SpecCliHs { sfin: h2.sfin, ..h }),
    ensures
        h2.sh_ok(c, host) == h.sh_ok(c, host),
        h2.ee_ok(c) == h.ee_ok(c),
        h2.cert_ok(c, host) == h.cert_ok(c, host),
        h2.cv_ok(c, host) == h.cv_ok(c, host),
        h2.th_cv(c, host) == h.th_cv(c, host),
        h2.c_hs(c, host) == h.c_hs(c, host),
        h2.s_hs(c, host) == h.s_hs(c, host),
        h2.server_finished(c, host) == h.server_finished(c, host),
        h2.th_sfin(c, host) == h.th_cv(c, host) + h2.sfin,
        h2.th_client(c, host) == h2.th_sfin(c, host) + h2.client_msgs(),
        h2.c_ap(c, host) == client_ap_traffic(h.alg(), h.psk(), h.dhe, h2.th_sfin(c, host)),
        h2.s_ap(c, host) == server_ap_traffic(h.alg(), h.psk(), h.dhe, h2.th_sfin(c, host)),
        h2.client_finished(c, host) == finished(verify_data(h.alg(), h.c_hs(c, host), h2.th_client(c, host))),
{
    lemma_frame_sh(h, h2, c, host);
    reveal(SpecCliHs::ee_ok);
    reveal(SpecCliHs::cert_ok);
    reveal(SpecCliHs::th_cert);
    reveal(SpecCliHs::th_cv);
    reveal(SpecCliHs::cv_ok);
    reveal(SpecCliHs::th_sfin);
    reveal(SpecCliHs::th_client);
    reveal(SpecCliHs::c_ap);
    reveal(SpecCliHs::s_ap);
    reveal(SpecCliHs::client_finished);
}

/// How far along the handshake a phase is.
pub open spec fn rank(p: CPhase) -> nat {
    match p {
        CPhase::WaitHello => 0,
        CPhase::WaitFlight => 1,
        CPhase::Connected => 2,
        CPhase::Closed => 3,
    }
}

/// One client connection.
pub struct ClientConn<P: ClientCrypto> {
    cfg: Arc<ClientConfig>,
    host: Vec<u8>,
    prov: P,
    state: CState<P::Key>,
    /// A handshake message that has not all arrived.
    buf: Vec<u8>,
    random: [u8; 32],
    sid: [u8; 32],
    /// The key shares of the last ClientHello.
    shares: Vec<(u16, Vec<u8>)>,
    ch1: Vec<u8>,
    /// The server's certificates, leaf first, once checked.
    peer: Vec<Vec<u8>>,
    alpn: Option<Vec<u8>>,
    ccs_sent: bool,
    hs: Ghost<SpecCliHs>,
    fin: Ghost<Seq<u8>>,
    nrx: Ghost<nat>,
    ntx: Ghost<nat>,
}

impl<P: ClientCrypto> ClientConn<P> {
    pub closed spec fn config(&self) -> SpecCliCfg {
        (*self.cfg)@
    }

    pub closed spec fn server_name(&self) -> Seq<u8> {
        self.host@
    }

    pub closed spec fn phase(&self) -> CPhase {
        match self.state {
            CState::WaitSh => CPhase::WaitHello,
            CState::WaitSh2 { .. } => CPhase::WaitHello,
            CState::Flight { .. } => CPhase::WaitFlight,
            CState::Connected { .. } => CPhase::Connected,
            CState::Closed => CPhase::Closed,
        }
    }

    /// The handshake, as far as it went.
    pub closed spec fn handshake(&self) -> SpecCliHs {
        self.hs@
    }

    /// The client's Finished, once sent.
    pub closed spec fn client_finished(&self) -> Seq<u8> {
        self.fin@
    }

    /// The server's certificates, leaf first, once checked.
    pub closed spec fn peer_chain(&self) -> Seq<Seq<u8>> {
        chain_view(self.peer@)
    }

    /// The server's current traffic secret, its KeyUpdates so far, and the
    /// sequence number of its next record.
    pub closed spec fn rx_secret(&self) -> Seq<u8> {
        match self.state {
            CState::Connected { s_sec, .. } => s_sec@,
            _ => Seq::empty(),
        }
    }

    pub closed spec fn rx_updates(&self) -> nat {
        self.nrx@
    }

    pub closed spec fn rx_seq(&self) -> u64 {
        match self.state {
            CState::Connected { rx, .. } => rx.seq(),
            _ => 0,
        }
    }

    /// The client's current traffic secret and next sequence number.
    pub closed spec fn tx_secret(&self) -> Seq<u8> {
        match self.state {
            CState::Connected { c_sec, .. } => c_sec@,
            _ => Seq::empty(),
        }
    }

    pub closed spec fn tx_updates(&self) -> nat {
        self.ntx@
    }

    pub closed spec fn tx_seq(&self) -> u64 {
        match self.state {
            CState::Connected { tx, .. } => tx.seq(),
            _ => 0,
        }
    }

    /// In the flight: what is next (0 EncryptedExtensions, 1
    /// CertificateRequest or Certificate, 2 Certificate, 3
    /// CertificateVerify, 4 Finished).
    pub closed spec fn stage(&self) -> u8 {
        match self.state {
            CState::Flight { f } => f.stage,
            _ => 0,
        }
    }

    closed spec fn base_ok(&self) -> bool {
        &&& (*self.cfg).wf()
        &&& valid_host_name(self.host@)
        &&& self.buf@.len() <= MAX_MESSAGE + 4
        &&& self.hs@.random == self.random@
        &&& self.hs@.sid == self.sid@
    }

    closed spec fn flight_ok(&self, f: Flight<P::Key>) -> bool {
        let h = self.hs@;
        let c = self.config();
        let host = self.host@;
        let a = suite_hash(f.suite);
        &&& h.sh_ok(c, host)
        &&& known_suite(f.suite)
        &&& h.suite == f.suite
        &&& f.tr.wf()
        &&& f.tr.alg() == a
        &&& keys_are(f.rx, f.suite, h.s_hs(c, host))
        &&& keys_are(f.tx, f.suite, h.c_hs(c, host))
        &&& f.tx.seq() == 0
        &&& f.c_hs.wf() && f.c_hs@ == h.c_hs(c, host)
        &&& f.s_hs.wf() && f.s_hs@ == h.s_hs(c, host)
        &&& f.hsec.wf() && f.hsec@ == handshake_secret(a, h.psk(), h.dhe)
        &&& f.stage <= 4
        &&& f.stage == 0 ==> f.tr.data() == h.th_sh(c, host)
        &&& f.stage >= 1 ==> h.ee_ok(c) && self.alpn_ok() && (f.cr <==> h.cr is Some)
        &&& f.stage == 1 ==> h.cr is None && f.tr.data() == h.th_sh(c, host) + h.ee
        &&& f.stage == 2 ==> h.cr is Some && f.tr.data() == h.th_sh(c, host) + h.ee + h.cr_msg()
        &&& f.stage >= 3 ==> h.cert_ok(c, host) && chain_view(self.peer@) == h.chain
        &&& f.stage == 3 ==> f.tr.data() == h.th_cert(c, host)
        &&& f.stage == 4 ==> h.cv_ok(c, host) && f.tr.data() == h.th_cv(c, host)
    }

    closed spec fn alpn_ok(&self) -> bool {
        match self.alpn {
            None => self.hs@.alpn is None,
            Some(v) => self.hs@.alpn == Some(v@),
        }
    }

    pub closed spec fn wf(&self) -> bool {
        let h = self.hs@;
        let c = self.config();
        let host = self.host@;
        &&& self.base_ok()
        &&& match self.state {
            CState::WaitSh => {
                &&& h.retry is None
                &&& self.ch1@ == h.ch1(c, host)
                &&& shares_wf(self.shares@)
                &&& shares_view(self.shares@) == h.shares
                &&& share_groups(h.shares) == c.groups.take(c.shares as int)
            },
            CState::WaitSh2 { suite, tr } => {
                &&& h.retry matches Some(r) && {
                    &&& is_msg(r.hrr, 2)
                    &&& read_sh(c, h.sid, share_groups(h.shares), r.hrr) == Ok::<SpecShOut, u8>(
                        SpecShOut::Retry { suite, group: r.group, cookie: r.cookie },
                    )
                    &&& match r.group {
                        Some(g) => r.shares.len() == 1 && r.shares[0].0 == g,
                        None => r.shares == h.shares,
                    }
                    &&& shares_view(self.shares@) == r.shares
                    &&& tr.data() == message_hash(suite_hash(suite), h.ch1(c, host)) + r.hrr + h.ch(c, host)
                }
                &&& shares_wf(self.shares@)
                &&& h.random.len() == 32
                &&& h.sid.len() == 32
                &&& share_groups(h.shares) == c.groups.take(c.shares as int)
                &&& known_suite(suite)
                &&& tr.wf()
                &&& tr.alg() == suite_hash(suite)
            },
            CState::Flight { f } => self.flight_ok(f),
            CState::Connected { suite, rx, tx, c_sec, s_sec } => {
                let a = suite_hash(suite);
                &&& h.valid(c, host)
                &&& known_suite(suite)
                &&& h.suite == suite
                &&& self.alpn_ok()
                &&& chain_view(self.peer@) == h.chain
                &&& self.fin@ == h.client_finished(c, host)
                &&& c_sec.wf() && c_sec@ == updated(a, h.c_ap(c, host), self.ntx@)
                &&& s_sec.wf() && s_sec@ == updated(a, h.s_ap(c, host), self.nrx@)
                &&& keys_are(rx, suite, s_sec@)
                &&& keys_are(tx, suite, c_sec@)
            },
            CState::Closed => true,
        }
    }

    /// Once connected, the handshake was valid for this configuration and
    /// server name, the client's Finished was the one RFC 8446 gives for
    /// it, and the keys are the key schedule's.
    pub proof fn lemma_connected(&self)
        requires
            self.wf(),
            self.phase() == CPhase::Connected,
        ensures
            self.handshake().valid(self.config(), self.server_name()),
            server_chain_ok(self.handshake().chain, self.config().roots, self.handshake().now, self.server_name()),
            self.peer_chain() == self.handshake().chain,
            self.client_finished() == self.handshake().client_finished(self.config(), self.server_name()),
            self.rx_secret() == updated(
                self.handshake().alg(),
                self.handshake().s_ap(self.config(), self.server_name()),
                self.rx_updates(),
            ),
            self.tx_secret() == updated(
                self.handshake().alg(),
                self.handshake().c_ap(self.config(), self.server_name()),
                self.tx_updates(),
            ),
    {
        reveal(SpecCliHs::cert_ok);
    }

    /// A connection to `host` (a DNS name, `spec::valid_host_name`): its
    /// ClientHello is appended to `out` as one plaintext record. `None` if
    /// the host name is not a valid DNS name, or the provider could not
    /// make a key share.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    pub fn new(cfg: Arc<ClientConfig>, host: &[u8], prov: P, out: &mut Vec<u8>) -> (r: Option<Self>)
        requires
            (*cfg).wf(),
        ensures
            r matches Some(conn) ==> {
                &&& conn.wf()
                &&& conn.phase() == CPhase::WaitHello
                &&& conn.config() == (*cfg)@
                &&& conn.server_name() == host@
                &&& final(out)@ == old(out)@ + plain_record(22, conn.handshake().ch1(conn.config(), host@))
            },
            r is None ==> final(out)@ == old(out)@,
    {
        if !valid_host_name_x(host) {
            return None;
        }
        let mut prov = prov;
        let mut random = [0u8; 32];
        prov.random(&mut random);
        let mut sid = [0u8; 32];
        prov.random(&mut sid);
        let k = cfg.shares;
        let mut shares: Vec<(u16, Vec<u8>)> = Vec::new();
        let mut i: usize = 0;
        while i < k
            invariant
                (*cfg).wf(),
                k == cfg.shares,
                i <= k,
                shares@.len() == i,
                forall|j: int| 0 <= j < i ==> 1 <= (#[trigger] shares@[j]).1@.len() <= MAX_SHARE,
                share_groups(shares_view(shares@)) == cfg.groups@.take(i as int),
            decreases k - i,
        {
            let g = cfg.groups[i];
            let s = match prov.client_share(g) {
                Some(s) => s,
                None => return None,
            };
            if s.len() < 1 || s.len() > MAX_SHARE {
                return None;
            }
            let ghost s0 = shares@;
            shares.push((g, s));
            proof {
                assert(shares_view(shares@) =~= shares_view(s0).push((g, s@)));
                assert(share_groups(shares_view(shares@)) =~= cfg.groups@.take(i as int + 1));
                assert forall|j: int| 0 <= j < i + 1 implies 1 <= (#[trigger] shares@[j]).1@.len() <= MAX_SHARE by {
                    if j < i {
                        assert(shares@[j] == s0[j]);
                    }
                }
            }
            i = i + 1;
        }
        let mut hv: Vec<u8> = Vec::new();
        put(&mut hv, host);
        let ch1 = client_hello_x(&*cfg, host, &random, &sid, &shares, None);
        plain_header_x(out, 22, ch1.len());
        put(out, ch1.as_slice());
        let ghost hs0: SpecCliHs = arbitrary();
        let ghost hs = SpecCliHs { random: random@, sid: sid@, shares: shares_view(shares@), retry: None, ..hs0 };
        let conn = ClientConn {
            cfg,
            host: hv,
            prov,
            state: CState::WaitSh,
            buf: Vec::new(),
            random,
            sid,
            shares,
            ch1,
            peer: Vec::new(),
            alpn: None,
            ccs_sent: false,
            hs: Ghost(hs),
            fin: Ghost(Seq::empty()),
            nrx: Ghost(0),
            ntx: Ghost(0),
        };
        proof {
            assert(opt_view(None) == None::<Seq<u8>>);
            assert(final(out)@ =~= old(out)@ + plain_record(22, conn.hs@.ch1(conn.config(), host@)));
        }
        Some(conn)
    }

    pub fn phase_x(&self) -> (r: CPhase)
        ensures
            r == self.phase(),
    {
        match &self.state {
            CState::WaitSh => CPhase::WaitHello,
            CState::WaitSh2 { .. } => CPhase::WaitHello,
            CState::Flight { .. } => CPhase::WaitFlight,
            CState::Connected { .. } => CPhase::Connected,
            CState::Closed => CPhase::Closed,
        }
    }

    pub fn is_connected(&self) -> (r: bool)
        ensures
            r == (self.phase() == CPhase::Connected),
    {
        match self.state {
            CState::Connected { .. } => true,
            _ => false,
        }
    }

    /// Sends alert `code` (under the client's handshake or application
    /// keys once it has them) and closes.
    fn fail(&mut self, code: u8, out: &mut Vec<u8>) -> (r: Error)
        requires
            old(self).base_ok(),
            old(out)@.len() <= usize::MAX / 2,
        ensures
            final(self).wf(),
            final(self).phase() == CPhase::Closed,
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            r == Error::Sent(code),
    {
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        self.peer = Vec::new();
        let body: [u8; 2] = [2, code];
        let ghost o = out@;
        match st {
            CState::Flight { mut f } => {
                f.tx.seal(21, &body, out);
            },
            CState::Connected { mut tx, .. } => {
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

    /// `fail`, whatever `out`'s length.
    fn fail_append(&mut self, code: u8, out: &mut Vec<u8>) -> (r: Error)
        requires
            old(self).base_ok(),
        ensures
            final(self).wf(),
            final(self).phase() == CPhase::Closed,
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
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

    /// An alert from the server, `a` its body.
    fn on_alert(&mut self, a: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(out)@.len() <= usize::MAX / 2,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == old(self).phase() || final(self).phase() == CPhase::Closed,
            r matches Ok(e) ==> e is Nothing || e is Closed,
    {
        if a.len() != 2 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        assert(out@.take(out@.len() as int) =~= out@);
        if a[1] == 90 {
            // user_canceled: a close_notify should follow.
            return Ok(Event::Nothing);
        }
        self.state = CState::Closed;
        self.peer = Vec::new();
        if a[1] == 0 {
            Ok(Event::Closed)
        } else {
            Err(Error::Received(a[1]))
        }
    }

    /// A HelloRetryRequest `m` in answer to ClientHello1 (§4.1.4): sends
    /// ClientHello2, with the one share asked for (or the same shares) and
    /// the cookie, after a change_cipher_spec (Appendix D.4).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(80)]
    fn on_hrr(&mut self, m: &[u8], suite: u16, group: Option<u16>, cookie: Option<&[u8]>, out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).state is WaitSh,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 2),
            read_sh(old(self).config(), old(self).hs@.sid, share_groups(old(self).hs@.shares), m@) == Ok::<SpecShOut, u8>(
                SpecShOut::Retry { suite, group, cookie: opt_view(cookie) },
            ),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == CPhase::WaitHello || final(self).phase() == CPhase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        let ghost h = self.hs@;
        let ghost c = self.config();
        let ghost host = self.host@;
        proof {
            reveal(read_sh);
            assert(c.suites.contains(suite));
            let j = choose|j: int| 0 <= j < c.suites.len() && c.suites[j] == suite;
            assert(known_suite((*self.cfg).suites@[j]));
        }
        if cookie.is_some() {
            proof {
                assert(cookie.unwrap()@.len() <= MAX_COOKIE);
            }
        }
        let a = suite_hash_x(suite);
        let mut t1 = Transcript::new(a);
        t1.update(self.ch1.as_slice());
        let h1 = t1.hash();
        let mut mh: Vec<u8> = Vec::new();
        message_hash_x(&mut mh, &h1);
        let mut tr = Transcript::new(a);
        tr.update(mh.as_slice());
        tr.update(m);
        let shares2: Vec<(u16, Vec<u8>)> = match group {
            Some(g) => {
                let s = match self.prov.client_share(g) {
                    Some(s) => s,
                    None => return Err(self.fail(INTERNAL_ERROR, out)),
                };
                if s.len() < 1 || s.len() > MAX_SHARE {
                    return Err(self.fail(INTERNAL_ERROR, out));
                }
                let mut v: Vec<(u16, Vec<u8>)> = Vec::new();
                v.push((g, s));
                v
            },
            None => {
                let mut v: Vec<(u16, Vec<u8>)> = Vec::new();
                core::mem::swap(&mut v, &mut self.shares);
                v
            },
        };
        let ch2 = client_hello_x(&*self.cfg, self.host.as_slice(), &self.random, &self.sid, &shares2, cookie);
        tr.update(ch2.as_slice());
        let ghost o = out@;
        if !self.ccs_sent {
            plain_header_x(out, 20, 1);
            put1(out, 1);
            self.ccs_sent = true;
        }
        plain_header_x(out, 22, ch2.len());
        put(out, ch2.as_slice());
        let ghost rt = SpecRetry { hrr: m@, group, cookie: opt_view(cookie), shares: shares_view(shares2@) };
        self.hs = Ghost(SpecCliHs { retry: Some(rt), suite, ..h });
        self.shares = shares2;
        self.state = CState::WaitSh2 { suite, tr };
        proof {
            assert(out@.take(o.len() as int) =~= o);
            assert(self.hs@.ch1(c, host) == h.ch1(c, host));
            assert(mh@ == message_hash(suite_hash(suite), h.ch1(c, host)));
            assert(tr.data() =~= message_hash(suite_hash(suite), h.ch1(c, host)) + m@ + self.hs@.ch(c, host));
            match group {
                Some(g) => {
                    assert(rt.shares.len() == 1);
                },
                None => {},
            }
        }
        Ok(Event::Nothing)
    }

    /// A ServerHello `m` (or a HelloRetryRequest, after ClientHello1):
    /// the key exchange, the handshake secrets, and on to the flight.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(120)]
    fn on_server_hello(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == CPhase::WaitHello,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 2),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == CPhase::WaitHello ==> old(self).state is WaitSh,
            final(self).phase() != CPhase::Connected,
            r matches Ok(e) ==> e is Nothing,
    {
        let ghost h = self.hs@;
        let ghost c = self.config();
        let ghost host = self.host@;
        let offered = groups_of(&self.shares);
        let cfa = self.cfg.clone();
        let res = read_sh_x(&*cfa, vstd::array::array_as_slice(&self.sid), offered.as_slice(), m);
        let retried = match self.state {
            CState::WaitSh2 { .. } => true,
            _ => false,
        };
        let (suite, group, share) = match res {
            Err(a) => return Err(self.fail(a, out)),
            Ok(ShOut::Retry { suite, group, cookie }) => {
                if retried {
                    return Err(self.fail(UNEXPECTED_MESSAGE, out));
                }
                return self.on_hrr(m, suite, group, cookie, out);
            },
            Ok(ShOut::Hello { suite, group, share }) => (suite, group, share),
        };
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        let mut tr = match st {
            CState::WaitSh2 { suite: s2, tr } => {
                if s2 != suite {
                    return Err(self.fail(ILLEGAL_PARAMETER, out));
                }
                tr
            },
            CState::WaitSh => {
                proof {
                    reveal(read_sh);
                    let j = choose|j: int| 0 <= j < c.suites.len() && c.suites[j] == suite;
                    assert(known_suite((*self.cfg).suites@[j]));
                }
                let mut t = Transcript::new(suite_hash_x(suite));
                t.update(self.ch1.as_slice());
                t
            },
            _ => {
                proof {
                    assert(false);
                }
                return Err(self.fail(INTERNAL_ERROR, out));
            },
        };
        let ours = share_of_x(&self.shares, group);
        let mut dh = [0u8; 64];
        let n = match self.prov.client_shared(group, ours, share, &mut dh) {
            Some(n) => n,
            None => return Err(self.fail(ILLEGAL_PARAMETER, out)),
        };
        let dhe = vstd::slice::slice_subrange(vstd::array::array_as_slice(&dh), 0, n);
        tr.update(m);
        let a = suite_hash_x(suite);
        let th = tr.hash();
        let z = Secret::zeros_of(a);
        let ghost h2 = SpecCliHs { sh: m@, suite, group, server_share: share@, dhe: dhe@, ..h };
        proof {
            reveal(SpecCliHs::th_sh);
            reveal(SpecCliHs::sh_ok);
            assert(dhe@ =~= dh@.take(n as int));
            assert(h2.last_shares() == shares_view(self.shares@));
            assert(tr.data() =~= h2.th_sh(c, host));
            assert(h2.sh_ok(c, host));
        }
        let (hsec, c_hs, s_hs) = hs_keys(suite, z.as_slice(), dhe, &th, Ghost(tr.data()));
        let rx = protect_of(&self.prov, suite, &s_hs);
        let tx = protect_of(&self.prov, suite, &c_hs);
        proof {
            reveal(SpecCliHs::c_hs);
            reveal(SpecCliHs::s_hs);
            assert(z@ == h2.psk());
        }
        self.hs = Ghost(h2);
        proof {
            let a2 = suite_hash(suite);
            assert(known_suite(suite));
            assert(tr.wf() && tr.alg() == a2);
            assert(keys_are(rx, suite, h2.s_hs(c, host)));
            assert(keys_are(tx, suite, h2.c_hs(c, host)));
            assert(tx.seq() == 0);
            assert(hsec@ == handshake_secret(a2, h2.psk(), h2.dhe));
            assert(tr.data() == h2.th_sh(c, host));
        }
        self.state = CState::Flight { f: Flight { suite, tr, rx, tx, c_hs, s_hs, hsec, stage: 0, cr: false } };
        assert(self.base_ok());
        assert(self.flight_ok(Flight { suite, tr, rx, tx, c_hs, s_hs, hsec, stage: 0, cr: false }));
        assert(out@.take(out@.len() as int) =~= out@);
        Ok(Event::Nothing)
    }

    fn rank_x(&self) -> (r: u8)
        ensures
            r == rank(self.phase()),
    {
        match &self.state {
            CState::WaitSh => 0,
            CState::WaitSh2 { .. } => 0,
            CState::Flight { .. } => 1,
            CState::Connected { .. } => 2,
            CState::Closed => 3,
        }
    }

    fn stage_x(&self) -> (r: u8)
        ensures
            r == self.stage(),
    {
        match &self.state {
            CState::Flight { f } => f.stage,
            _ => 0,
        }
    }

    /// EncryptedExtensions `m` (§4.3.1).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    fn on_ee(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == CPhase::WaitFlight,
            old(self).stage() == 0,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 8),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == CPhase::WaitFlight || final(self).phase() == CPhase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        let ghost h = self.hs@;
        let ghost c = self.config();
        let ghost host = self.host@;
        let cfa = self.cfg.clone();
        let al = match read_ee_x(&*cfa, m) {
            Err(a) => return Err(self.fail(a, out)),
            Ok(al) => al,
        };
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            CState::Flight { mut f } => {
                f.tr.update(m);
                f.stage = 1;
                f.cr = false;
                self.alpn = match al {
                    Some(p) => {
                        let mut v: Vec<u8> = Vec::new();
                        put(&mut v, p);
                        Some(v)
                    },
                    None => None,
                };
                let ghost h2 = SpecCliHs { ee: m@, alpn: opt_view(al), cr: None, ..h };
                proof {
                    lemma_frame_sh(h, h2, c, host);
                    reveal(SpecCliHs::ee_ok);
                }
                self.hs = Ghost(h2);
                self.state = CState::Flight { f };
                assert(out@.take(out@.len() as int) =~= out@);
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

    /// A CertificateRequest `m` (§4.3.2), answered later with an empty
    /// Certificate.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    fn on_cr(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == CPhase::WaitFlight,
            old(self).stage() == 1,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 13),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == CPhase::WaitFlight || final(self).phase() == CPhase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        let ghost h = self.hs@;
        let ghost c = self.config();
        let ghost host = self.host@;
        let rc = read_cr_x(m);
        match rc {
            Err(a) => return Err(self.fail(a, out)),
            Ok(_) => {},
        }
        assert(read_cr(m@) is Ok);
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            CState::Flight { mut f } => {
                f.tr.update(m);
                f.stage = 2;
                f.cr = true;
                let ghost h2 = SpecCliHs { cr: Some(m@), ..h };
                proof {
                    lemma_frame_sh(h, h2, c, host);
                    assert(h.ee_ok(c));
                    reveal(SpecCliHs::ee_ok);
                    assert(is_msg(h2.ee, 8));
                    assert(read_ee(c, h2.ee) == Ok::<Option<Seq<u8>>, u8>(h2.alpn));
                    assert(read_cr(m@) is Ok);
                    assert(h2.ee_ok(c));
                    assert(h2.cr_msg() == m@);
                    assert(f.tr.data() == h2.th_sh(c, host) + h2.ee + h2.cr_msg());
                }
                self.hs = Ghost(h2);
                self.state = CState::Flight { f };
                assert(self.alpn_ok());
                assert(self.flight_ok(f));
                assert(out@.take(out@.len() as int) =~= out@);
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

    /// The server's Certificate `m` (§4.4.2): its chain, checked
    /// (`check_server_chain`).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(80)]
    fn on_certificate(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == CPhase::WaitFlight,
            old(self).stage() == 1 || old(self).stage() == 2,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 11),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == CPhase::WaitFlight || final(self).phase() == CPhase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        let ghost h = self.hs@;
        let ghost c = self.config();
        let ghost host = self.host@;
        let body = vstd::slice::slice_subrange(m, 4, m.len());
        assert(body@ =~= m@.skip(4));
        let chain = match parse_client_certificate_x(body) {
            Ok(v) => v,
            Err(a) => return Err(self.fail(a, out)),
        };
        if chain.len() == 0 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        let now = self.prov.now_utc();
        let cfa = self.cfg.clone();
        match check_server_chain(&self.prov, &chain, &cfa.roots, &now, self.host.as_slice()) {
            Ok(()) => {},
            Err(a) => return Err(self.fail(a, out)),
        }
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            CState::Flight { mut f } => {
                f.tr.update(m);
                f.stage = 3;
                let ghost h2 = SpecCliHs { cert: m@, chain: chain_view(chain@), now: now@, ..h };
                proof {
                    lemma_frame_sh(h, h2, c, host);
                    reveal(SpecCliHs::ee_ok);
                    reveal(SpecCliHs::cert_ok);
                    reveal(SpecCliHs::th_cert);
                    if h.cr is None {
                        assert(h.cr_msg() == Seq::<u8>::empty());
                        assert(f.tr.data() =~= h2.th_cert(c, host));
                    } else {
                        assert(f.tr.data() =~= h2.th_cert(c, host));
                    }
                }
                self.peer = chain;
                self.hs = Ghost(h2);
                self.state = CState::Flight { f };
                assert(out@.take(out@.len() as int) =~= out@);
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

    /// The server's CertificateVerify `m` (§4.4.3): a scheme the client
    /// offered, and the leaf's key's signature over the transcript through
    /// the Certificate.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    fn on_cv(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == CPhase::WaitFlight,
            old(self).stage() == 3,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 15),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == CPhase::WaitFlight || final(self).phase() == CPhase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        let ghost h = self.hs@;
        let ghost c = self.config();
        let ghost host = self.host@;
        let n = m.len();
        if n < 8 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        let scheme = (m[4] as u16) * 256 + m[5] as u16;
        let sl = (m[6] as usize) * 256 + m[7] as usize;
        if sl != n - 8 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        if !has_u16_x(self.cfg.sigs.as_slice(), scheme) {
            return Err(self.fail(ILLEGAL_PARAMETER, out));
        }
        if self.peer.len() == 0 {
            return Err(self.fail(INTERNAL_ERROR, out));
        }
        let sig = vstd::slice::slice_subrange(m, 8, n);
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            CState::Flight { mut f } => {
                let th = f.tr.hash();
                let ok = cv_sig_ok(&self.prov, self.peer[0].as_slice(), scheme, &th, sig);
                if !ok {
                    self.state = CState::Flight { f };
                    return Err(self.fail(DECRYPT_ERROR, out));
                }
                let ghost d0 = f.tr.data();
                f.tr.update(m);
                f.stage = 4;
                let ghost h2 = SpecCliHs { cv: m@, scheme, sig: sig@, ..h };
                proof {
                    lemma_cv_msg(m@, scheme, sig@);
                    assert(chain_view(self.peer@)[0] == self.peer@[0]@);
                    lemma_cv_step(h, h2, c, host, d0);
                }
                self.hs = Ghost(h2);
                self.state = CState::Flight { f };
                assert(out@.take(out@.len() as int) =~= out@);
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

    /// The server's Finished `m` (§4.4.4), checked in constant time; then
    /// the client's flight: change_cipher_spec (if not sent already), an
    /// empty Certificate if the server asked for one, and the client's
    /// Finished, under its handshake keys.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    fn on_finished(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == CPhase::WaitFlight,
            old(self).stage() == 4,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 20),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == CPhase::Connected || final(self).phase() == CPhase::Closed,
            r matches Ok(e) ==> e is HandshakeDone && final(self).phase() == CPhase::Connected,
            final(self).phase() == CPhase::Connected ==> (r matches Ok(e) && e is HandshakeDone),
    {
        let ghost h = self.hs@;
        let ghost c = self.config();
        let ghost host = self.host@;
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        let mut f = match st {
            CState::Flight { f } => f,
            _ => {
                proof {
                    assert(false);
                }
                return Err(self.fail(INTERNAL_ERROR, out));
            },
        };
        let suite = f.suite;
        let a = suite_hash_x(suite);
        let th = f.tr.hash();
        let expect = verify_data_x(a, &f.s_hs, &th, Ghost(f.tr.data()));
        if m.len() != 4 + expect.len() {
            self.state = CState::Flight { f };
            return Err(self.fail(DECODE_ERROR, out));
        }
        let got = vstd::slice::slice_subrange(m, 4, m.len());
        if !declassify(ct_eq(got, expect.as_slice())) {
            self.state = CState::Flight { f };
            return Err(self.fail(DECRYPT_ERROR, out));
        }
        let ghost h2 = SpecCliHs { sfin: m@, ..h };
        proof {
            assert(m@.skip(4) =~= expect@);
            lemma_be3(m@);
            lemma_fin_step(h, h2, c, host);
            assert(m@ == h.server_finished(c, host));
        }
        f.tr.update(m);
        let th2 = f.tr.hash();
        let ms = master_secret_x(a, &f.hsec, Ghost(h.psk()), Ghost(h.dhe));
        let (c_ap, s_ap, _) = ap_traffic_x(a, &ms, &th2, Ghost(h.psk()), Ghost(h.dhe), Ghost(f.tr.data()));
        let ghost o = out@;
        if !self.ccs_sent {
            plain_header_x(out, 20, 1);
            put1(out, 1);
            self.ccs_sent = true;
        }
        let mut tx = f.tx;
        if f.cr {
            let ec: [u8; 8] = [11, 0, 0, 4, 0, 0, 0, 0];
            proof {
                assert(ec@ =~= empty_certificate());
            }
            tx.seal(22, &ec, out);
            f.tr.update(&ec);
        }
        proof {
            assert(f.tr.data() =~= h2.th_client(c, host));
        }
        let th3 = f.tr.hash();
        let vd = verify_data_x(a, &f.c_hs, &th3, Ghost(f.tr.data()));
        let mut fm: Vec<u8> = Vec::new();
        finished_x(&mut fm, &vd);
        proof {
            assert(fm@.len() <= 4 + 48);
        }
        tx.seal(22, fm.as_slice(), out);
        let rx2 = protect_of(&self.prov, suite, &s_ap);
        let tx2 = protect_of(&self.prov, suite, &c_ap);
        self.hs = Ghost(h2);
        self.fin = Ghost(fm@);
        self.nrx = Ghost(0);
        self.ntx = Ghost(0);
        self.state = CState::Connected { suite, rx: rx2, tx: tx2, c_sec: c_ap, s_sec: s_ap };
        proof {
            assert(out@.take(o.len() as int) =~= o);
            assert(updated(suite_hash(suite), c_ap@, 0) == c_ap@);
            assert(updated(suite_hash(suite), s_ap@, 0) == s_ap@);
            assert(h2.valid(c, host));
        }
        Ok(Event::HandshakeDone)
    }

    /// A KeyUpdate `m` (§4.6.3).
    #[verifier::spinoff_prover]
    fn on_key_update(&mut self, m: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() == CPhase::Connected,
            old(out)@.len() <= usize::MAX / 2,
            is_msg(m@, 24),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            final(self).phase() == CPhase::Connected || final(self).phase() == CPhase::Closed,
            r matches Ok(e) ==> e is Nothing,
    {
        if m.len() != 5 {
            return Err(self.fail(DECODE_ERROR, out));
        }
        let req = m[4];
        if req > 1 {
            return Err(self.fail(ILLEGAL_PARAMETER, out));
        }
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            CState::Connected { suite, rx, tx, c_sec, s_sec } => {
                let mut tx = tx;
                let mut c_sec = c_sec;
                let ghost o = out@;
                if req == 1 {
                    // update_requested: answer with update_not_requested
                    // under the current keys, then move on.
                    let ku: [u8; 5] = [24, 0, 0, 1, 0];
                    if !tx.seal(22, &ku, out) {
                        self.state = CState::Connected { suite, rx, tx, c_sec, s_sec };
                        return Err(self.fail(INTERNAL_ERROR, out));
                    }
                    let (c2, tx2) = rekey(&self.prov, suite, &c_sec);
                    tx = tx2;
                    c_sec = c2;
                    self.ntx = Ghost(self.ntx@ + 1);
                }
                let (s2, rx2) = rekey(&self.prov, suite, &s_sec);
                self.nrx = Ghost(self.nrx@ + 1);
                self.state = CState::Connected { suite, rx: rx2, tx, c_sec, s_sec: s2 };
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
            old(self).phase() != CPhase::Closed,
            old(out)@.len() <= usize::MAX / 2,
            m@.len() >= 4,
            be24(m@, 1) == m@.len() - 4,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            rank(final(self).phase()) >= rank(old(self).phase()),
            r matches Ok(e) ==> (e is Nothing || (e is HandshakeDone && old(self).phase() == CPhase::WaitFlight
                && final(self).phase() == CPhase::Connected)),
            final(self).phase() == CPhase::Connected && old(self).phase() != CPhase::Connected ==> (r matches Ok(e)
                && e is HandshakeDone),
    {
        let t = m[0];
        let ph = self.rank_x();
        let stage = self.stage_x();
        if ph == 0 && t == 2 {
            self.on_server_hello(m, out)
        } else if ph == 1 && stage == 0 && t == 8 {
            self.on_ee(m, out)
        } else if ph == 1 && stage == 1 && t == 13 {
            self.on_cr(m, out)
        } else if ph == 1 && (stage == 1 || stage == 2) && t == 11 {
            self.on_certificate(m, out)
        } else if ph == 1 && stage == 3 && t == 15 {
            self.on_cv(m, out)
        } else if ph == 1 && stage == 4 && t == 20 {
            self.on_finished(m, out)
        } else if ph == 2 && t == 4 {
            // NewSessionTicket: this client does not resume, so it keeps
            // none (§4.6.1 lets a client ignore them).
            assert(out@.take(out@.len() as int) =~= out@);
            Ok(Event::Nothing)
        } else if ph == 2 && t == 24 {
            self.on_key_update(m, out)
        } else {
            Err(self.fail(UNEXPECTED_MESSAGE, out))
        }
    }

    /// A fragment of handshake messages (§5.1: they may span records, but
    /// not a change of keys, so ServerHello, Finished and KeyUpdate must
    /// each end their record).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    fn on_handshake(&mut self, frag: &[u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
            old(self).phase() != CPhase::Closed,
            old(out)@.len() <= usize::MAX / 2,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            rank(final(self).phase()) >= rank(old(self).phase()),
            r matches Ok(e) ==> (e is Nothing || (e is HandshakeDone && old(self).phase() == CPhase::WaitFlight
                && final(self).phase() == CPhase::Connected)),
    {
        let ghost p0 = self.phase();
        let r0 = self.rank_x();
        let ghost o = out@;
        if frag.len() > MAX_MESSAGE + 4 - self.buf.len() {
            return Err(self.fail(UNEXPECTED_MESSAGE, out));
        }
        put(&mut self.buf, frag);
        assert(out@.take(o.len() as int) =~= o);
        loop
            invariant
                self.wf(),
                self.config() == old(self).config(),
                self.server_name() == old(self).server_name(),
                p0 == old(self).phase(),
                self.phase() != CPhase::Closed,
                rank(self.phase()) >= rank(p0),
                o == old(out)@,
                out@.len() >= o.len(),
                out@.take(o.len() as int) == o,
                self.phase() == p0,
                r0 == rank(p0),
            decreases self.buf@.len(),
        {
            let l = match handshake_length(self.buf.as_slice()) {
                None => return Ok(Event::Nothing),
                Some(l) => l,
            };
            if l > MAX_MESSAGE {
                return Err(self.fail_append(UNEXPECTED_MESSAGE, out));
            }
            if l > self.buf.len() - 4 {
                return Ok(Event::Nothing);
            }
            if out.len() > usize::MAX / 2 {
                return Err(self.fail_append(INTERNAL_ERROR, out));
            }
            let mut mv: Vec<u8> = Vec::new();
            core::mem::swap(&mut mv, &mut self.buf);
            let k = 4 + l;
            let mut rest: Vec<u8> = Vec::new();
            put(&mut rest, vstd::slice::slice_subrange(mv.as_slice(), k, mv.len()));
            let msg = vstd::slice::slice_subrange(mv.as_slice(), 0, k);
            assert(be24(msg@, 1) == be24(mv@, 1));
            let t = msg[0];
            if (t == 2 || t == 20 || t == 24) && rest.len() > 0 {
                return Err(self.fail_append(UNEXPECTED_MESSAGE, out));
            }
            let ghost out0 = out@;
            let r = self.dispatch(msg, out);
            self.buf = rest;
            proof {
                assert(out@.take(o.len() as int) =~= out0.take(o.len() as int));
            }
            match r {
                Err(e) => return Err(e),
                Ok(Event::HandshakeDone) => return Ok(Event::HandshakeDone),
                Ok(_) => {},
            }
            if self.buf.len() == 0 {
                return Ok(Event::Nothing);
            }
            if self.rank_x() != r0 {
                // Only ServerHello moves the phase on and keeps going, and
                // it ends its record: never here.
                return Err(self.fail_append(UNEXPECTED_MESSAGE, out));
            }
        }
    }

    /// Opens a protected record under the server's current keys.
    #[verifier::spinoff_prover]
    fn open_rec(&mut self, hdr: &[u8; 5], body: &mut [u8]) -> (r: Result<(u8, usize), RecErr>)
        requires
            old(self).wf(),
            old(self).phase() == CPhase::WaitFlight || old(self).phase() == CPhase::Connected,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(self).phase() == old(self).phase(),
            final(self).stage() == old(self).stage(),
            final(self).handshake() == old(self).handshake(),
            final(self).rx_secret() == old(self).rx_secret(),
            final(self).rx_updates() == old(self).rx_updates(),
            final(self).tx_secret() == old(self).tx_secret(),
            final(self).tx_seq() == old(self).tx_seq(),
            final(self).tx_updates() == old(self).tx_updates(),
            old(self).phase() == CPhase::Connected ==> {
                let s = old(self).handshake().suite;
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
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            CState::Flight { mut f } => {
                let r = f.rx.open(hdr, body);
                self.state = CState::Flight { f };
                r
            },
            CState::Connected { suite, mut rx, tx, c_sec, s_sec } => {
                let r = rx.open(hdr, body);
                self.state = CState::Connected { suite, rx, tx, c_sec, s_sec };
                r
            },
            other => {
                self.state = other;
                proof {
                    assert(false);
                }
                Err(RecErr::BadMac)
            },
        }
    }

    /// One record from the server: its header and body. What the client
    /// sends in answer is appended to `out`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    pub fn read_record(&mut self, hdr: &[u8; 5], body: &mut [u8], out: &mut Vec<u8>) -> (r: Result<Event, Error>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.take(old(out)@.len() as int) == old(out)@,
            rank(final(self).phase()) >= rank(old(self).phase()),
            old(self).phase() == CPhase::Closed ==> (r matches Err(e) && e is Closed),
            r matches Ok(e) && e is HandshakeDone ==> old(self).phase() == CPhase::WaitFlight
                && final(self).phase() == CPhase::Connected,
            r matches Ok(Event::Data(n)) ==> {
                let s = old(self).handshake().suite;
                let a = suite_hash(s);
                let sec = old(self).rx_secret();
                &&& old(self).phase() == CPhase::Connected
                &&& final(self).phase() == CPhase::Connected
                &&& n < final(body)@.len()
                &&& open_record(s, traffic_key(a, sec, suite_key_len(s)), traffic_iv(a, sec), old(self).rx_seq(), hdr@, old(body)@)
                    == Ok::<(u8, Seq<u8>), SpecRecErr>((23u8, final(body)@.take(n as int)))
            },
            r matches Ok(e) ==> !(e is EarlyData),
    {
        let ph = self.rank_x();
        if ph == 3 {
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
        if ct == 20 {
            // change_cipher_spec, which §5 says to drop between the first
            // ClientHello and the server's Finished, if it is the single
            // byte 1.
            if ph <= 1 && n == 1 && body[0] == 1 && self.buf.len() == 0 {
                assert(out@.take(out@.len() as int) =~= out@);
                return Ok(Event::Nothing);
            }
            return Err(self.fail(UNEXPECTED_MESSAGE, out));
        }
        if ct == 21 && ph <= 1 {
            if n > 16384 {
                return Err(self.fail(RECORD_OVERFLOW, out));
            }
            return self.on_alert(body, out);
        }
        if ph == 0 {
            if ct == 22 {
                if n > 16384 {
                    return Err(self.fail(RECORD_OVERFLOW, out));
                }
                if n == 0 {
                    return Err(self.fail(UNEXPECTED_MESSAGE, out));
                }
                return self.on_handshake(body, out);
            }
            return Err(self.fail(UNEXPECTED_MESSAGE, out));
        }
        if ct != 23 {
            return Err(self.fail(UNEXPECTED_MESSAGE, out));
        }
        let res = self.open_rec(hdr, body);
        match res {
            Err(e) => {
                let code = match e {
                    RecErr::BadMac => BAD_RECORD_MAC,
                    RecErr::Overflow => RECORD_OVERFLOW,
                    RecErr::NoType => UNEXPECTED_MESSAGE,
                    RecErr::Exhausted => INTERNAL_ERROR,
                };
                Err(self.fail(code, out))
            },
            Ok((ict, k)) => {
                let content = vstd::slice::slice_subrange(&*body, 0, k);
                if ict == 22 {
                    if k == 0 {
                        return Err(self.fail(UNEXPECTED_MESSAGE, out));
                    }
                    self.on_handshake(content, out)
                } else if ict == 21 {
                    self.on_alert(content, out)
                } else if ict == 23 && ph == 2 && self.buf.len() == 0 {
                    assert(out@.take(out@.len() as int) =~= out@);
                    Ok(Event::Data(k))
                } else {
                    Err(self.fail(UNEXPECTED_MESSAGE, out))
                }
            },
        }
    }

    /// Protects application data `data` into `out`, once connected.
    pub fn write(&mut self, data: &[u8], out: &mut Vec<u8>) -> (r: Result<(), Error>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
            final(self).phase() == old(self).phase(),
            r is Ok ==> old(self).phase() == CPhase::Connected && {
                let s = old(self).handshake().suite;
                let a = suite_hash(s);
                let sec = old(self).tx_secret();
                final(out)@ == old(out)@ + seal_chunks(s, traffic_key(a, sec, suite_key_len(s)), traffic_iv(a, sec), old(self).tx_seq(), 23, data@)
            },
            r is Err ==> final(out)@ == old(out)@,
    {
        if out.len() > usize::MAX / 4 || data.len() > usize::MAX / 4 {
            return Err(Error::OutputFull);
        }
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            CState::Connected { suite, rx, mut tx, c_sec, s_sec } => {
                proof {
                    assert(out@.len() + data@.len() + 22 * (data@.len() / 16384 + 1) + 16384 + 32 <= usize::MAX) by (nonlinear_arith)
                        requires out@.len() <= usize::MAX / 4, data@.len() <= usize::MAX / 4, usize::MAX >= 0xffff_ffff;
                }
                let ok = tx.seal_all(23, data, out);
                self.state = CState::Connected { suite, rx, tx, c_sec, s_sec };
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
            final(self).phase() == CPhase::Closed,
            final(self).config() == old(self).config(),
            final(self).server_name() == old(self).server_name(),
    {
        if out.len() > usize::MAX / 2 {
            self.state = CState::Closed;
            return;
        }
        let mut st = CState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        let body: [u8; 2] = [1, 0];
        match st {
            CState::Connected { mut tx, .. } => {
                tx.seal(21, &body, out);
            },
            CState::Flight { mut f } => {
                f.tx.seal(21, &body, out);
            },
            _ => {
                plain_header_x(out, 21, 2);
                put(out, &body);
            },
        }
    }

    /// The server's certificates, leaf first, once checked (empty before).
    /// Once connected, `lemma_connected` says what they are.
    pub fn peer_certificates(&self) -> (r: &[Vec<u8>])
        ensures
            chain_view(r@) == self.peer_chain(),
    {
        self.peer.as_slice()
    }

    /// The ALPN protocol the server chose, once its EncryptedExtensions
    /// came.
    pub fn alpn(&self) -> (r: Option<&[u8]>)
        ensures
            self.wf() && self.phase() == CPhase::Connected ==> opt_view(r) == self.handshake().alpn,
    {
        match &self.alpn {
            Some(v) => Some(v.as_slice()),
            None => None,
        }
    }

    /// The suite, client traffic key and IV, and next sequence number, once
    /// connected (for a caller that hands sending to the kernel, kTLS).
    pub fn tx_keys(&self) -> (r: Option<(u16, Secret, Secret, u64)>)
        requires
            self.wf(),
        ensures
            r is Some <==> self.phase() == CPhase::Connected,
            r matches Some((s, k, iv, seq)) ==> {
                &&& s == self.handshake().suite
                &&& k@ == traffic_key(suite_hash(s), self.tx_secret(), suite_key_len(s))
                &&& iv@ == traffic_iv(suite_hash(s), self.tx_secret())
                &&& seq == self.tx_seq()
            },
    {
        match &self.state {
            CState::Connected { suite, tx, c_sec, .. } => {
                let (k, iv) = traffic_keys_x(suite_hash_x(*suite), c_sec, suite_key_len_x(*suite));
                Some((*suite, k, iv, tx.seq_x()))
            },
            _ => None,
        }
    }
}

} // verus!
