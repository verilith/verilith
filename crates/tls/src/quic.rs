//! TLS 1.3 for QUIC (RFC 9001 §4): the server handshake of `server.rs`
//! with QUIC's framing in place of TLS records. Handshake messages arrive
//! and leave as the bytes of CRYPTO frames at an encryption level, the
//! transport protects packets with keys derived from the traffic secrets
//! this module exposes (`keys::quic_keys_x`), and EncryptedExtensions
//! carries the server's transport parameters.
//!
//! The handshake is `server.rs`'s, proven the same way and with the same
//! specification (`spec_server::SpecHs`): ClientHello negotiation,
//! HelloRetryRequest, resumption, the server's flight, the key schedule
//! and the client's Finished. What QUIC changes (§8) is checked here:
//!
//! - the client must send quic_transport_parameters (§8.2,
//!   `missing_extension`), and its contents are exposed as
//!   `peer_params`, exactly the extension's data (`quic_tp_of`);
//! - ALPN is required (§8.1, `no_application_protocol`);
//! - a non-empty legacy_session_id is a PROTOCOL_VIOLATION (§8.4), so no
//!   ChangeCipherSpec is ever sent;
//! - no 0-RTT: early_data is never accepted, so 0-RTT packets are simply
//!   undecryptable;
//! - no KeyUpdate message (§6): key updates are the transport's; any
//!   handshake message at the 1-RTT level from the client is
//!   `unexpected_message`.
//!
//! Each message must arrive at the level RFC 9001 §4.1.4 puts it at:
//! ClientHello at Initial, the client's Finished at Handshake; anything
//! else is `unexpected_message`. TLS alerts become CRYPTO_ERROR
//! (0x100 + alert, §4.8).
use crate::crypto::*;
use crate::ct::{ct_eq, declassify};
use crate::hello::*;
use crate::keys::*;
use crate::messages::*;
use crate::negotiate::*;
use crate::record::*;
use crate::server::*;
use crate::spec::*;
use crate::spec_keys::*;
use crate::spec_server::*;
use alloc::sync::Arc;
use alloc::vec::Vec;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// QUIC transport error codes this module reports (RFC 9000 §20.1).
pub const PROTOCOL_VIOLATION: u64 = 0x0a;

/// CRYPTO_ERROR: 0x100 plus the TLS alert (§4.8).
pub const CRYPTO_ERROR: u64 = 0x100;

pub const MISSING_EXTENSION: u8 = 109;

pub const NO_APPLICATION_PROTOCOL: u8 = 120;

/// Encryption levels (§4.1.4), numbered as the packet number spaces of
/// RFC 9002 §A.2 with 0-RTT, which a server never sends, as 1.
pub const INITIAL: u8 = 0;

pub const HANDSHAKE: u8 = 2;

pub const ONE_RTT: u8 = 3;

/// The data of the extension of type `t` in the extensions `b[pos..end]`
/// (§4.2), if there is one: the first one, and `parse_client_hello` has
/// already rejected a ClientHello with two of one type.
pub open spec fn ext_find(b: Seq<u8>, pos: int, end: int, t: u16) -> Option<(int, int)>
    decreases end - pos,
{
    if pos < 0 || pos + 4 > end || end > b.len() {
        None
    } else {
        let n = be16(b, pos + 2);
        if pos + 4 + n > end {
            None
        } else if be16(b, pos) == t as nat {
            Some((pos + 4, pos + 4 + n))
        } else {
            ext_find(b, pos + 4 + n, end, t)
        }
    }
}

/// The quic_transport_parameters a ClientHello message `ch` carries.
pub open spec fn quic_tp_of(ch: Seq<u8>) -> Option<Seq<u8>> {
    let b = ch.skip(4);
    match parse_client_hello(b) {
        Ok(s) => match ext_find(b, s.outer.extensions.0, s.outer.extensions.1, EXT_QUIC_TP) {
            Some(sp) => Some(bytes(b, sp)),
            None => None,
        },
        Err(_) => None,
    }
}

/// Finds extension `t` in `b[pos..end]`.
fn ext_find_x(b: &[u8], pos: usize, end: usize, t: u16) -> (r: Option<(usize, usize)>)
    requires
        pos <= end <= b@.len(),
    ensures
        match r {
            Some((s, e)) => ext_find(b@, pos as int, end as int, t) == Some((s as int, e as int)) && s <= e
                <= end,
            None => ext_find(b@, pos as int, end as int, t) is None,
        },
{
    let mut p = pos;
    while end - p >= 4
        invariant
            pos <= p <= end <= b@.len(),
            ext_find(b@, pos as int, end as int, t) == ext_find(b@, p as int, end as int, t),
        decreases end - p,
    {
        let typ = (b[p] as usize) * 256 + b[p + 1] as usize;
        let n = (b[p + 2] as usize) * 256 + b[p + 3] as usize;
        if n > end - p - 4 {
            return None;
        }
        if typ == t as usize {
            return Some((p + 4, p + 4 + n));
        }
        p = p + 4 + n;
    }
    None
}

/// Parses ClientHello `m` (body `body`) and negotiates with `cfg`; or the
/// alert to send.
#[verifier::spinoff_prover]
fn parse_negotiate(cfg: &Config, m: &[u8], body: &[u8]) -> (r: Result<(ClientHello, Outcome, Ghost<SpecHello>), u8>)
    requires
        body@ == m@.skip(4),
        is_msg(m@, 1),
    ensures
        r matches Ok((h, o, s)) ==> {
            &&& parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s@)
            &&& h.models(s@)
            &&& outcome(cfg@, m@) == Some(o@)
        },
{
    let h = match ClientHello::parse(body) {
        Ok(h) => h,
        Err(a) => return Err(a.code()),
    };
    let ghost s = choose|s: SpecHello| parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s) && h.models(s);
    let o = crate::negotiate::negotiate(body, &h, cfg.suites.as_slice(), cfg.groups.as_slice(), cfg.sigs.as_slice(), cfg.alpn.as_slice());
    proof {
        reveal(outcome);
        cfg.lemma_view();
        assert(o@ == crate::spec::negotiate(body@, s, cfg@.suites, cfg@.groups, cfg@.sigs, cfg@.alpn));
        assert(outcome(cfg@, m@) == Some(o@));
    }
    Ok((h, o, Ghost(s)))
}

/// The client's quic_transport_parameters, from its ClientHello `m`.
fn client_tp(m: &[u8], body: &[u8], h: &ClientHello, Ghost(s): Ghost<SpecHello>) -> (r: Option<Vec<u8>>)
    requires
        body@ == m@.skip(4),
        parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s),
        h.models(s),
    ensures
        r matches Some(v) ==> quic_tp_of(m@) == Some(v@),
{
    let xs = h.extensions;
    if !(xs.start <= xs.end && xs.end <= body.len()) {
        return None;
    }
    match ext_find_x(body, xs.start, xs.end, EXT_QUIC_TP) {
        Some((a, b)) => {
            let mut v: Vec<u8> = Vec::new();
            put(&mut v, slice_subrange(body, a, b));
            Some(v)
        },
        None => None,
    }
}

/// Handshake bytes to send, by encryption level: the contents of the
/// CRYPTO frames the transport sends at that level, in order.
pub struct Out {
    pub initial: Vec<u8>,
    pub handshake: Vec<u8>,
    pub one_rtt: Vec<u8>,
}

impl Out {
    pub fn new() -> (r: Out)
        ensures
            r.initial@.len() == 0 && r.handshake@.len() == 0 && r.one_rtt@.len() == 0,
    {
        Out { initial: Vec::new(), handshake: Vec::new(), one_rtt: Vec::new() }
    }

    pub open spec fn small(&self) -> bool {
        &&& self.initial@.len() <= usize::MAX / 4
        &&& self.handshake@.len() <= usize::MAX / 4
        &&& self.one_rtt@.len() <= usize::MAX / 4
    }

    /// `self` extends `o` at every level.
    pub open spec fn extends(&self, o: &Out) -> bool {
        &&& prefix(o.initial@, self.initial@)
        &&& prefix(o.handshake@, self.handshake@)
        &&& prefix(o.one_rtt@, self.one_rtt@)
    }
}

/// `a` is a prefix of `b`.
pub open spec fn prefix(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() <= b.len() && forall|i: int| 0 <= i < a.len() ==> a[i] == b[i]
}

/// What a call to `read` came to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Event {
    Nothing,
    /// ServerHello and the server's flight were written: the Handshake
    /// secrets and the server's 1-RTT secret are ready (`hs_secrets`,
    /// `ap_secrets`).
    Accepted,
    /// The client's Finished checked out: the handshake is complete, the
    /// client's 1-RTT secret can be used, and session tickets, if any, are
    /// in `one_rtt`.
    Done,
}

enum QState {
    Start,
    WaitCh2 { tr: Transcript, suite: u16, group: u16 },
    WaitFinished { suite: u16, c_hs: Secret, s_hs: Secret, expect: Secret, c_ap: Secret, s_ap: Secret, res: Option<Secret> },
    Connected { suite: u16, c_ap: Secret, s_ap: Secret },
    Closed,
}

/// A QUIC server's TLS handshake, with its cryptography `P`.
pub struct QuicServer<P: Provider> {
    cfg: Arc<Config>,
    prov: P,
    state: QState,
    /// Our transport parameters, encoded.
    tp: Vec<u8>,
    /// The client's, once its ClientHello is in.
    peer_tp: Vec<u8>,
    /// A handshake message that has not all arrived.
    buf: Vec<u8>,
    alpn_sel: Option<Span>,
    hs: Ghost<SpecHs>,
    ch1: Ghost<Seq<u8>>,
    hrr: Ghost<Seq<u8>>,
    fin: Ghost<Seq<u8>>,
}

impl<P: Provider> QuicServer<P> {
    pub closed spec fn config(&self) -> SpecCfg {
        (*self.cfg)@
    }

    pub closed spec fn phase(&self) -> Phase {
        match self.state {
            QState::Start => Phase::Start,
            QState::WaitCh2 { .. } => Phase::Retried,
            QState::WaitFinished { .. } => Phase::WaitFinished,
            QState::Connected { .. } => Phase::Connected,
            QState::Closed => Phase::Closed,
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

    /// Our transport parameters.
    pub closed spec fn params(&self) -> Seq<u8> {
        self.tp@
    }

    /// The client's transport parameters, once its ClientHello is in.
    pub closed spec fn peer_params_v(&self) -> Seq<u8> {
        self.peer_tp@
    }

    pub closed spec fn hs_ok(&self) -> bool {
        &&& self.hs@.valid(self.config())
        &&& known_suite(self.hs@.choice.suite)
        &&& self.hs@.tp == Some(self.tp@)
        &&& session_id(self.hs@.ch).len() == 0
        &&& self.hs@.choice.alpn is Some
        &&& quic_tp_of(self.hs@.ch) == Some(self.peer_tp@)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& (*self.cfg).wf()
        &&& self.buf@.len() <= MAX_MESSAGE + 4
        &&& self.tp@.len() <= 60000
        &&& match self.state {
            QState::Start => true,
            QState::WaitCh2 { tr, suite, group } => {
                &&& tr.wf()
                &&& tr.alg() == suite_hash(suite)
                &&& known_suite(suite)
                &&& is_msg(self.ch1@, 1)
                &&& outcome(self.config(), self.ch1@) == Some(SpecOutcome::Retry { suite, group })
                &&& self.hrr@ == hello_retry_request(session_id(self.ch1@), suite, group)
                &&& tr.data() == message_hash(suite_hash(suite), self.ch1@) + self.hrr@
            },
            QState::WaitFinished { suite, c_hs, s_hs, expect, c_ap, s_ap, res } => {
                let h = self.hs@;
                let c = self.config();
                &&& self.hs_ok()
                &&& suite == h.choice.suite
                &&& c_hs.wf() && c_hs@ == h.c_hs()
                &&& s_hs.wf() && s_hs@ == h.s_hs()
                &&& expect.wf() && finished(expect@) == h.client_finished(c)
                &&& expect@.len() == hash_len(suite_hash(suite))
                &&& c_ap.wf() && c_ap@ == h.c_ap(c)
                &&& s_ap.wf() && s_ap@ == h.s_ap(c)
                &&& res matches Some(rm) ==> rm.wf() && rm@ == h.res_master(c)
            },
            QState::Connected { suite, c_ap, s_ap } => {
                let h = self.hs@;
                let c = self.config();
                &&& self.hs_ok()
                &&& suite == h.choice.suite
                &&& self.fin@ == h.client_finished(c)
                &&& c_ap.wf() && c_ap@ == h.c_ap(c)
                &&& s_ap.wf() && s_ap@ == h.s_ap(c)
            },
            QState::Closed => true,
        }
    }

    /// Once connected, the handshake was valid, carried our transport
    /// parameters and the client's, and the client's Finished was the one
    /// RFC 8446 gives for it.
    pub proof fn lemma_connected(&self)
        requires
            self.wf(),
            self.phase() == Phase::Connected,
        ensures
            self.handshake().valid(self.config()),
            self.handshake().tp == Some(self.params()),
            quic_tp_of(self.handshake().ch) == Some(self.peer_params_v()),
            self.client_finished() == self.handshake().client_finished(self.config()),
    {
    }

    /// A handshake for a connection whose transport parameters, encoded,
    /// are `tp`.
    pub fn new(cfg: Arc<Config>, prov: P, tp: Vec<u8>) -> (r: Option<Self>)
        requires
            (*cfg).wf(),
        ensures
            r matches Some(q) ==> q.wf() && q.phase() == Phase::Start && q.config() == (*cfg)@ && q.params()
                == tp@,
            r is Some ==> (*cfg)@.client is None,
    {
        // No client authentication over QUIC.
        if tp.len() > 60000 || cfg.has_client_auth() {
            return None;
        }
        Some(
            QuicServer {
                cfg,
                prov,
                state: QState::Start,
                tp,
                peer_tp: Vec::new(),
                buf: Vec::new(),
                alpn_sel: None,
                hs: Ghost(arbitrary()),
                ch1: Ghost(Seq::empty()),
                hrr: Ghost(Seq::empty()),
                fin: Ghost(Seq::empty()),
            },
        )
    }

    pub fn is_connected(&self) -> (r: bool)
        ensures
            r == (self.phase() == Phase::Connected),
    {
        match self.state {
            QState::Connected { .. } => true,
            _ => false,
        }
    }

    /// The cipher suite, once negotiated.
    pub fn suite(&self) -> (r: Option<u16>)
        requires
            self.wf(),
        ensures
            (self.phase() == Phase::WaitFinished || self.phase() == Phase::Connected) ==> r == Some(
                self.handshake().choice.suite,
            ),
            r matches Some(s) ==> known_suite(s),
    {
        match self.state {
            QState::WaitFinished { suite, .. } => Some(suite),
            QState::Connected { suite, .. } => Some(suite),
            _ => None,
        }
    }

    /// The client's and the server's handshake traffic secrets, while the
    /// server waits for the client's Finished.
    pub fn hs_secrets(&self) -> (r: Option<(&Secret, &Secret)>)
        requires
            self.wf(),
        ensures
            r is Some <==> self.phase() == Phase::WaitFinished,
            r matches Some((c, s)) ==> c.wf() && s.wf() && c@ == self.handshake().c_hs() && s@
                == self.handshake().s_hs(),
    {
        match &self.state {
            QState::WaitFinished { c_hs, s_hs, .. } => Some((c_hs, s_hs)),
            _ => None,
        }
    }

    /// The client's and the server's first application traffic secrets,
    /// once the server has sent its flight. The client's must not be used
    /// before the handshake is complete (§5.7).
    pub fn ap_secrets(&self) -> (r: Option<(&Secret, &Secret)>)
        requires
            self.wf(),
        ensures
            r is Some <==> (self.phase() == Phase::WaitFinished || self.phase() == Phase::Connected),
            r matches Some((c, s)) ==> c.wf() && s.wf() && c@ == self.handshake().c_ap(self.config()) && s@
                == self.handshake().s_ap(self.config()),
    {
        match &self.state {
            QState::WaitFinished { c_ap, s_ap, .. } => Some((c_ap, s_ap)),
            QState::Connected { c_ap, s_ap, .. } => Some((c_ap, s_ap)),
            _ => None,
        }
    }

    /// The client's transport parameters, encoded.
    pub fn peer_params(&self) -> (r: &[u8])
        ensures
            r@ == self.peer_params_v(),
    {
        self.peer_tp.as_slice()
    }

    /// The ALPN protocol chosen.
    pub fn alpn(&self) -> Option<&[u8]> {
        match self.alpn_sel {
            Some(sp) => {
                if sp.start <= sp.end && sp.end <= self.cfg.alpn.len() {
                    Some(slice_subrange(self.cfg.alpn.as_slice(), sp.start, sp.end))
                } else {
                    None
                }
            },
            None => None,
        }
    }

    /// Fails the handshake with TLS alert `code`.
    fn fail(&mut self, code: u8) -> (r: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).phase() == Phase::Closed,
            final(self).config() == old(self).config(),
            final(self).handshake() == old(self).handshake(),
            r == CRYPTO_ERROR + code as u64,
    {
        self.state = QState::Closed;
        CRYPTO_ERROR + code as u64
    }

    /// A HelloRetryRequest for ClientHello1 `m`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn send_hrr(&mut self, m: &[u8], suite: u16, group: u16, out: &mut Out)
        requires
            old(self).wf(),
            old(self).phase() == Phase::Start,
            old(out).small(),
            is_msg(m@, 1),
            outcome(old(self).config(), m@) == Some(SpecOutcome::Retry { suite, group }),
            session_id(m@).len() == 0,
            known_suite(suite),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(self).phase() == Phase::Retried,
            final(out).initial@ == old(out).initial@ + hello_retry_request(Seq::empty(), suite, group),
            final(out).handshake@ == old(out).handshake@,
            final(out).one_rtt@ == old(out).one_rtt@,
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
        let e: [u8; 0] = [];
        let es = vstd::array::array_as_slice(&e);
        proof {
            assert(es@ =~= Seq::<u8>::empty());
            assert(es@ == session_id(m@));
        }
        hello_retry_request_x(&mut hrr, es, suite, group);
        tr.update(hrr.as_slice());
        put(&mut out.initial, hrr.as_slice());
        proof {
            assert(tr.data() =~= message_hash(a, m@) + hrr@);
        }
        self.ch1 = Ghost(m@);
        self.hrr = Ghost(hrr@);
        self.state = QState::WaitCh2 { tr, suite, group };
    }

    /// ServerHello and the server's flight for ClientHello `m`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(80)]
    fn accept(
        &mut self,
        cfg: &Config,
        m: &[u8],
        body: &[u8],
        c: Choice,
        tr: Transcript,
        Ghost(retry): Ghost<Option<(Seq<u8>, Seq<u8>)>>,
        Ghost(choice): Ghost<SpecChoice>,
        h: &ClientHello,
        Ghost(s): Ghost<SpecHello>,
        peer_tp: Vec<u8>,
        out: &mut Out,
    ) -> (r: Result<Event, u64>)
        requires
            parse_client_hello(body@) == Ok::<SpecHello, SpecAlert>(s),
            h.models(s),
            old(self).wf(),
            old(self).phase() == Phase::Start || old(self).phase() == Phase::Retried,
            cfg.wf(),
            cfg@ == old(self).config(),
            old(out).small(),
            is_msg(m@, 1),
            body@ == m@.skip(4),
            session_id(m@).len() == 0,
            known_suite(c.suite),
            c.alpn is Some,
            choice.suite == c.suite && choice.group == c.group && choice.share == c.share@
                && choice.signature_scheme == c.signature_scheme && choice.alpn == ov2(c.alpn),
            outcome(cfg@, m@) == Some(SpecOutcome::Accept(choice)),
            quic_tp_of(m@) == Some(peer_tp@),
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
            final(out).extends(&*old(out)),
            final(out).one_rtt@ == old(out).one_rtt@,
            r matches Ok(e) ==> e is Accepted && final(self).phase() == Phase::WaitFinished,
            r is Err ==> final(self).phase() == Phase::Closed,
            final(self).phase() == Phase::WaitFinished ==> {
                let hs = final(self).handshake();
                &&& hs.retry == retry
                &&& hs.ch == m@
                &&& final(out).initial@ == old(out).initial@ + hs.server_hello()
                &&& final(out).handshake@ == old(out).handshake@ + hs.flight(final(self).config())
            },
            final(self).phase() == Phase::Closed ==> final(out).initial@ == old(out).initial@
                && final(out).handshake@ == old(out).handshake@,
    {
        proof {
            reveal(session_id);
        }
        let e: [u8; 0] = [];
        let sid = vstd::array::array_as_slice(&e);
        assert(sid@ =~= session_id(m@));
        let rs = match try_resume(&mut self.prov, cfg, m, body, h, Ghost(s), c.suite, &tr) {
            Ok(x) => x,
            Err(code) => return Err(self.fail(code)),
        };
        let (psk, Ghost(resumed)) = match rs {
            Some((k, g, _)) => (Some(k), Ghost(Some(g@))),
            None => (None, Ghost(None)),
        };
        let p = match prepare(
            &mut self.prov,
            cfg,
            m,
            body,
            sid,
            c,
            tr,
            Ghost(retry),
            Ghost(choice),
            psk,
            Ghost(resumed),
            Some(self.tp.as_slice()),
            false,
            Ghost(None),
            false,
            false,
        ) {
            Ok(p) => p,
            Err(code) => return Err(self.fail(code)),
        };
        let Prep { sh, fl, c_hs, s_hs, expect, c_ap, s_ap, res, c_early: _, tr: _, hs: Ghost(hsv) } = p;
        proof {
            reveal(prep_ok);
        }
        put(&mut out.initial, sh.as_slice());
        put(&mut out.handshake, fl.as_slice());
        self.alpn_sel = match c.alpn {
            Some((ours, _)) => Some(ours),
            None => None,
        };
        self.peer_tp = peer_tp;
        self.hs = Ghost(hsv);
        self.state = QState::WaitFinished { suite: c.suite, c_hs, s_hs, expect, c_ap, s_ap, res };
        Ok(Event::Accepted)
    }

    /// A ClientHello message `m`, in `Start` or `Retried`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(150)]
    fn on_client_hello(&mut self, m: &[u8], out: &mut Out) -> (r: Result<Event, u64>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::Start || old(self).phase() == Phase::Retried,
            old(out).small(),
            is_msg(m@, 1),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out).extends(&*old(out)),
            final(out).one_rtt@ == old(out).one_rtt@,
            r matches Ok(e) ==> (e is Nothing && final(self).phase() == Phase::Retried) || (e is Accepted
                && final(self).phase() == Phase::WaitFinished),
            final(self).phase() == Phase::WaitFinished || final(self).phase() == Phase::Closed || (old(
                self,
            ).phase() == Phase::Start && final(self).phase() == Phase::Retried),
            final(self).phase() == Phase::WaitFinished ==> {
                let hs = final(self).handshake();
                &&& hs.ch == m@
                &&& final(out).initial@ == old(out).initial@ + hs.server_hello()
                &&& final(out).handshake@ == old(out).handshake@ + hs.flight(final(self).config())
            },
            final(self).phase() == Phase::Retried ==> final(out).handshake@ == old(out).handshake@,
            final(self).phase() == Phase::Closed ==> final(out).initial@ == old(out).initial@
                && final(out).handshake@ == old(out).handshake@,
            r is Err ==> final(self).phase() == Phase::Closed,
    {
        let cfg_arc = self.cfg.clone();
        let cfg: &Config = &*cfg_arc;
        let body = vstd::slice::slice_subrange(m, 4, m.len());
        proof {
            assert(body@ =~= m@.skip(4));
        }
        let (h, o, Ghost(s)) = match parse_negotiate(cfg, m, body) {
            Ok(x) => x,
            Err(code) => return Err(self.fail(code)),
        };
        // §8.4: no middlebox compatibility mode over QUIC.
        let sp = h.session_id;
        if sp.start != sp.end {
            self.state = QState::Closed;
            return Err(PROTOCOL_VIOLATION);
        }
        proof {
            reveal(session_id);
            assert(session_id(m@) =~= Seq::<u8>::empty());
        }
        // §8.2: quic_transport_parameters is required.
        let peer_tp: Vec<u8> = match client_tp(m, body, &h, Ghost(s)) {
            Some(v) => v,
            None => return Err(self.fail(MISSING_EXTENSION)),
        };
        let mut st = QState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            QState::Start => {
                self.state = QState::Start;
                match o {
                    Outcome::Reject(a) => Err(self.fail(a.code())),
                    Outcome::Retry { suite, group } => {
                        if !(suite == 0x1301 || suite == 0x1302 || suite == 0x1303) {
                            return Err(self.fail(INTERNAL_ERROR));
                        }
                        self.send_hrr(m, suite, group, out);
                        Ok(Event::Nothing)
                    },
                    Outcome::Accept(c) => {
                        if !(c.suite == 0x1301 || c.suite == 0x1302 || c.suite == 0x1303) {
                            return Err(self.fail(INTERNAL_ERROR));
                        }
                        if c.alpn.is_none() {
                            return Err(self.fail(NO_APPLICATION_PROTOCOL));
                        }
                        let ghost choice = match o@ {
                            SpecOutcome::Accept(x) => x,
                            _ => arbitrary(),
                        };
                        let tr = Transcript::new(suite_hash_x(c.suite));
                        self.accept(cfg, m, body, c, tr, Ghost(None), Ghost(choice), &h, Ghost(s), peer_tp, out)
                    },
                }
            },
            QState::WaitCh2 { tr, suite, group } => {
                let ghost ch1 = self.ch1@;
                let ghost hrr = self.hrr@;
                match o {
                    Outcome::Accept(c) => {
                        if c.suite != suite || c.group != group {
                            return Err(self.fail(ILLEGAL_PARAMETER));
                        }
                        if c.alpn.is_none() {
                            return Err(self.fail(NO_APPLICATION_PROTOCOL));
                        }
                        let ghost choice = match o@ {
                            SpecOutcome::Accept(x) => x,
                            _ => arbitrary(),
                        };
                        self.state = QState::Start;
                        self.accept(cfg, m, body, c, tr, Ghost(Some((ch1, hrr))), Ghost(choice), &h, Ghost(s), peer_tp, out)
                    },
                    Outcome::Retry { .. } => Err(self.fail(ILLEGAL_PARAMETER)),
                    Outcome::Reject(a) => Err(self.fail(a.code())),
                }
            },
            _ => {
                proof {
                    assert(false);
                }
                Err(PROTOCOL_VIOLATION)
            },
        }
    }

    /// The client's Finished `m`.
    #[verifier::spinoff_prover]
    fn on_finished(&mut self, m: &[u8], out: &mut Out) -> (r: Result<Event, u64>)
        requires
            old(self).wf(),
            old(self).phase() == Phase::WaitFinished,
            old(out).small(),
            is_msg(m@, 20),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out).extends(&*old(out)),
            final(out).initial@ == old(out).initial@,
            final(out).handshake@ == old(out).handshake@,
            final(self).phase() == Phase::Connected || final(self).phase() == Phase::Closed,
            final(self).phase() == Phase::Connected <==> r is Ok,
            final(self).phase() == Phase::Closed ==> final(out).one_rtt@ == old(out).one_rtt@,
            r matches Ok(e) ==> e is Done,
            final(self).handshake() == old(self).handshake(),
    {
        let mut st = QState::Closed;
        core::mem::swap(&mut self.state, &mut st);
        match st {
            QState::WaitFinished { suite, c_hs, s_hs, expect, c_ap, s_ap, res } => {
                let n = expect.len();
                if m.len() != 4 + n {
                    return Err(self.fail(DECODE_ERROR));
                }
                let got = vstd::slice::slice_subrange(m, 4, m.len());
                if !declassify(ct_eq(got, expect.as_slice())) {
                    return Err(self.fail(DECRYPT_ERROR));
                }
                proof {
                    assert(m@.skip(4) =~= expect@);
                    lemma_be3(m@);
                }
                let ghost o = out.one_rtt@;
                match res {
                    Some(rm) => {
                        let k = self.cfg.tickets;
                        let lifetime = self.cfg.lifetime;
                        let mut i: u8 = 0;
                        while i < k
                            invariant
                                rm.wf(),
                                o.len() <= usize::MAX / 4,
                                out.one_rtt@.len() <= o.len() + 512 * (i as int),
                                prefix(o, out.one_rtt@),
                                out.initial@ == old(out).initial@,
                                out.handshake@ == old(out).handshake@,
                            decreases k - i,
                        {
                            let ghost o2 = out.one_rtt@;
                            match make_ticket(&mut self.prov, suite, lifetime, i, &rm, 0, &[]) {
                                Some((nst, _)) => {
                                    put(&mut out.one_rtt, nst.as_slice());
                                },
                                None => break,
                            }
                            i = i + 1;
                        }
                    },
                    None => {},
                }
                self.fin = Ghost(m@);
                self.state = QState::Connected { suite, c_ap, s_ap };
                Ok(Event::Done)
            },
            _ => {
                proof {
                    assert(false);
                }
                Err(PROTOCOL_VIOLATION)
            },
        }
    }

    /// One whole handshake message `m`, at `level`.
    #[verifier::spinoff_prover]
    fn dispatch(&mut self, level: u8, m: &[u8], out: &mut Out) -> (r: Result<Event, u64>)
        requires
            old(self).wf(),
            old(self).phase() != Phase::Closed,
            old(out).small(),
            m@.len() >= 4,
            be24(m@, 1) == m@.len() - 4,
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out).extends(&*old(out)),
            step_ok(old(self).phase(), final(self).phase(), r),
            out_ok(old(self).phase(), final(self).phase(), &*old(out), &*final(out), final(self).handshake(), final(self).config()),
            old(self).phase() == Phase::WaitFinished || old(self).phase() == Phase::Connected
                ==> final(self).handshake() == old(self).handshake(),
            r is Err ==> final(self).phase() == Phase::Closed,
    {
        let t = m[0];
        let ph = match self.state {
            QState::Start => 0u8,
            QState::WaitCh2 { .. } => 1u8,
            QState::WaitFinished { .. } => 2u8,
            QState::Connected { .. } => 3u8,
            QState::Closed => 4u8,
        };
        if ph <= 1 && t == 1 && level == INITIAL {
            self.on_client_hello(m, out)
        } else if ph == 2 && t == 20 && level == HANDSHAKE {
            self.on_finished(m, out)
        } else {
            Err(self.fail(UNEXPECTED_MESSAGE))
        }
    }

    /// Handshake bytes the client sent at encryption level `level`, in
    /// order: the contents of its CRYPTO frames at that level, reassembled
    /// by the transport. On an error the connection is closed with that
    /// transport error code.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    pub fn read(&mut self, level: u8, data: &[u8], out: &mut Out) -> (r: Result<Event, u64>)
        requires
            old(self).wf(),
            old(out).small(),
        ensures
            final(self).wf(),
            final(self).config() == old(self).config(),
            final(out).extends(&*old(out)),
            step_ok(old(self).phase(), final(self).phase(), r),
            out_ok(old(self).phase(), final(self).phase(), &*old(out), &*final(out), final(self).handshake(), final(self).config()),
            old(self).phase() == Phase::WaitFinished || old(self).phase() == Phase::Connected
                ==> final(self).handshake() == old(self).handshake(),
            r is Err ==> final(self).phase() == Phase::Closed,
    {
        if let QState::Closed = self.state {
            return Err(PROTOCOL_VIOLATION);
        }
        if data.len() == 0 {
            return Ok(Event::Nothing);
        }
        if self.buf.len() == 0 {
            match handshake_length(data) {
                Some(l) => {
                    if l <= MAX_MESSAGE && l == data.len() - 4 {
                        return self.dispatch(level, data, out);
                    }
                    if l <= MAX_MESSAGE && l < data.len() - 4 {
                        return Err(self.fail(UNEXPECTED_MESSAGE));
                    }
                    if l > MAX_MESSAGE {
                        return Err(self.fail(UNEXPECTED_MESSAGE));
                    }
                },
                None => {},
            }
        }
        if data.len() > MAX_MESSAGE + 4 - self.buf.len() {
            return Err(self.fail(UNEXPECTED_MESSAGE));
        }
        put(&mut self.buf, data);
        match handshake_length(self.buf.as_slice()) {
            None => Ok(Event::Nothing),
            Some(l) => {
                if l > MAX_MESSAGE || l < self.buf.len() - 4 {
                    return Err(self.fail(UNEXPECTED_MESSAGE));
                }
                if l > self.buf.len() - 4 {
                    return Ok(Event::Nothing);
                }
                let mut m: Vec<u8> = Vec::new();
                core::mem::swap(&mut m, &mut self.buf);
                self.dispatch(level, m.as_slice(), out)
            },
        }
    }
}

/// How a call may move the handshake: only forward, along Appendix A.2,
/// with the event saying where it went.
pub open spec fn step_ok(a: Phase, b: Phase, r: Result<Event, u64>) -> bool {
    &&& b == Phase::Start ==> a == Phase::Start
    &&& b == Phase::Retried ==> a == Phase::Start || a == Phase::Retried
    &&& b == Phase::WaitFinished ==> a == Phase::Start || a == Phase::Retried || a == Phase::WaitFinished
    &&& b == Phase::Connected ==> a == Phase::WaitFinished || a == Phase::Connected
    &&& r matches Ok(e) ==> match e {
        Event::Nothing => a == b || (a == Phase::Start && b == Phase::Retried),
        Event::Accepted => (a == Phase::Start || a == Phase::Retried) && b == Phase::WaitFinished,
        Event::Done => a == Phase::WaitFinished && b == Phase::Connected,
    }
}

/// What a call may write: on accepting a ClientHello, ServerHello at
/// Initial and the server's flight at Handshake, exactly as `SpecHs` gives
/// them; on a HelloRetryRequest, only at Initial; on the client's Finished
/// (session tickets), only at 1-RTT; otherwise nothing.
pub open spec fn out_ok(a: Phase, b: Phase, o: &Out, f: &Out, hs: SpecHs, c: SpecCfg) -> bool {
    if (a == Phase::Start || a == Phase::Retried) && b == Phase::WaitFinished {
        &&& f.initial@ == o.initial@ + hs.server_hello()
        &&& f.handshake@ == o.handshake@ + hs.flight(c)
        &&& f.one_rtt@ == o.one_rtt@
    } else if a == Phase::WaitFinished && b == Phase::Connected {
        &&& f.initial@ == o.initial@
        &&& f.handshake@ == o.handshake@
    } else if a == Phase::Start && b == Phase::Retried {
        &&& f.handshake@ == o.handshake@
        &&& f.one_rtt@ == o.one_rtt@
    } else {
        &&& f.initial@ == o.initial@
        &&& f.handshake@ == o.handshake@
        &&& f.one_rtt@ == o.one_rtt@
    }
}

} // verus!
