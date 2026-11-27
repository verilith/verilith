//! One server connection: packet number spaces, the handshake, frames,
//! streams, flow control, loss recovery and timers. Every decision with a
//! specification is made by a verified component: header and frame
//! parsing (`verilith_quic::packet`, `frame`), packet and header
//! protection (`verilith_tls::quic_packet`), the TLS handshake
//! (`verilith_tls::quic`), sent and received packet tracking, RTT,
//! congestion control (`sent`, `recv`, `rtt`, `cc`), flow control and
//! stream states (`flow`, `streams`) and the anti-amplification limit
//! (`amplification`). This file connects them.
use crate::buf::SendBuf;
use verilith_quic::reasm::{Reassembly, MAX_WINDOW};
use bytes::Bytes;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use verilith_quic::allowed::{self, Level};
use verilith_quic::amplification::Budget;
use verilith_quic::cc::NewReno;
use verilith_quic::cubic::Cubic;
use verilith_quic::flow::{RecvCredit, SendCredit};
use verilith_quic::frame::{self, Frame};
use verilith_quic::keyphase::{Gen, KeyPhase};
use verilith_quic::packet::{self, Header};
use verilith_quic::params::{self, TransportParameters};
use verilith_quic::pktbuf::{self, put_frame};
use verilith_quic::reclog::{self, RecLog};
use verilith_quic::recv::Received;
use verilith_quic::rtt::Rtt;
use verilith_quic::schedule::KeySchedule;
use verilith_quic::sent::{Done, Sent};
use verilith_quic::timers::{self, Due, Timers};
use verilith_quic::streams::{RecvState, RecvStream, SendState, SendStream, StreamIds, Use};
use verilith_tls::crypto::Provider;
use verilith_tls::keys::{initial_secrets_x, Secret};
use verilith_tls::quic::{Event as TlsEvent, Out, QuicServer, HANDSHAKE, INITIAL, ONE_RTT};
use verilith_tls::quic_packet::{keys, unmask, update, Aead};

/// The length of the connection IDs this server issues.
pub const CID_LEN: usize = 8;

// Transport error codes (RFC 9000 §20.1).
pub const NO_ERROR: u64 = 0x00;
pub const INTERNAL_ERROR: u64 = 0x01;
pub const FLOW_CONTROL_ERROR: u64 = 0x03;
pub const STREAM_STATE_ERROR: u64 = 0x05;
pub const FRAME_ENCODING_ERROR: u64 = 0x07;
pub const TRANSPORT_PARAMETER_ERROR: u64 = 0x08;
pub const PROTOCOL_VIOLATION: u64 = 0x0a;
pub const CRYPTO_BUFFER_EXCEEDED: u64 = 0x0d;
pub const APPLICATION_ERROR: u64 = 0x0c;

const INITIAL_SUITE: u16 = 0x1301;
/// The most CRYPTO data buffered out of order at one level.
const MAX_CRYPTO_BUFFER: usize = 64 * 1024;
/// Frames recorded per packet are packed in a token with the count in the
/// low byte.
const MAX_FRAMES: usize = 255;
/// The most bytes one batch for segmentation offload may hold: a UDP
/// payload's maximum over IPv4.
pub const GSO_BYTES: usize = 65507;

/// A datagram this close to full still starts a batch for segmentation
/// offload.
const BATCH_SLACK: usize = 32;

/// The server's settings.
pub struct Config<P> {
    /// The TLS configuration (certificates, ALPN, tickets).
    pub tls: Arc<verilith_tls::server::Config>,
    /// Makes each connection's cryptography provider.
    pub provider: Arc<dyn Fn() -> P + Send + Sync>,
    /// max_idle_timeout, milliseconds.
    pub idle_timeout_ms: u64,
    /// The connection's receive window (initial_max_data).
    pub max_data: u64,
    /// Each stream's receive window.
    pub stream_window: u64,
    /// Streams the client may open.
    pub max_streams_bidi: u64,
    pub max_streams_uni: u64,
    /// The largest UDP payload sent at first. Paths must carry 1200 bytes
    /// (§14); more is found by probing.
    pub max_datagram: usize,
    /// Path MTU discovery (§14.3, DPLPMTUD of RFC 8899 in a simple form):
    /// once the handshake is confirmed, a PING padded to the next size of
    /// [`PROBE_STEPS`] is sent (up to three times if lost); when
    /// acknowledged, it becomes the largest payload sent, and the next
    /// step is probed, up to this size. Not above the peer's
    /// max_udp_payload_size; 0 turns it off. The socket must not fragment
    /// (DF set), or a probe the path cannot carry arrives in fragments.
    pub probe_datagram: usize,
    /// Bytes written to streams and not yet acknowledged, across the
    /// connection.
    pub send_buffer: usize,
    /// max_ack_delay, milliseconds.
    pub max_ack_delay_ms: u64,
    /// The congestion controller: CUBIC (RFC 9438) when true, else NewReno
    /// (RFC 9002 §7).
    pub cubic: bool,
}

impl<P> Config<P> {
    pub fn new(tls: Arc<verilith_tls::server::Config>, provider: Arc<dyn Fn() -> P + Send + Sync>) -> Config<P> {
        Config {
            tls,
            provider,
            idle_timeout_ms: 30_000,
            max_data: 16 << 20,
            stream_window: 1 << 20,
            max_streams_bidi: 100,
            max_streams_uni: 100,
            max_datagram: 1200,
            probe_datagram: 1452,
            send_buffer: 8 << 20,
            max_ack_delay_ms: 25,
            cubic: true,
        }
    }
}

/// What happened, for the application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// The handshake completed.
    Connected,
    /// The peer opened streams: call `accept`.
    Opened { bidi: bool },
    /// A stream has data, its end, or a reset to read.
    Readable(u64),
    /// A stream can take more data.
    Writable(u64),
    /// The peer asked us to stop sending on a stream (STOP_SENDING).
    Stopped { id: u64, code: u64 },
    /// The connection is closed (by either side, or idle); after this
    /// nothing more happens.
    Closed { code: u64, app: bool, remote: bool },
}

/// Why a stream operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamError {
    /// No such stream, or not in this direction.
    Unknown,
    /// Nothing to read now, or no room to write.
    Blocked,
    /// The peer reset the stream (reading) or stopped it (writing).
    Reset(u64),
    /// The stream was already finished or reset.
    Closed,
}

/// A datagram (batch) to send.
#[derive(Debug, Clone, Copy)]
pub struct Transmit {
    /// Bytes written to the buffer.
    pub size: usize,
    /// For segmentation offload: every datagram but the last is this
    /// size. `None` for a single datagram.
    pub segment_size: Option<usize>,
}

/// The sizes path MTU discovery probes on its way to
/// [`Config::probe_datagram`]: a 1500-byte Ethernet MTU and a 9000-byte
/// jumbo frame, less IPv6 and UDP headers. Then the configured size
/// itself (on loopback, 65487 fits Linux's 65536-byte MTU).
pub const PROBE_STEPS: [usize; 2] = [1452, 8952];

/// Path MTU discovery's state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Pmtu {
    /// A probe should be sent (after `fails` were lost).
    Due { fails: u8 },
    /// A probe is in flight in packet `pn`.
    Sent { pn: u64, fails: u8 },
    Done,
}

/// What a sent packet carried, to act on when it is acknowledged or lost.
#[derive(Clone, Copy, Debug)]
enum Rec {
    Ack,
    Ping,
    Crypto { off: u64, len: u32 },
    Stream { id: u64, off: u64, len: u32, fin: bool },
    Reset { id: u64 },
    Stop { id: u64 },
    MaxData,
    MaxStreamData { id: u64 },
    MaxStreams { bidi: bool },
    HandshakeDone,
    Close,
}

type Keys<P> = (Aead<<P as Provider>::Key>, <P as Provider>::Hp);

/// One packet number space (§12.3).
struct Space<P: Provider> {
    rx: Option<Keys<P>>,
    tx: Option<Keys<P>>,
    sent: Sent,
    recv: Received,
    crypto_out: SendBuf,
    crypto_in: Reassembly,
    /// The records of packets sent (verified `reclog`).
    recs: RecLog<Rec>,
    /// Probe packets to send (§6.2.4).
    probes: u8,
    /// An ACK frame is owed.
    ack_owed: bool,
    /// The loss timer (§6.1.2).
    loss_time: Option<u64>,
}

impl<P: Provider> Space<P> {
    fn new() -> Space<P> {
        Space {
            rx: None,
            tx: None,
            sent: Sent::new(),
            recv: Received::new(),
            crypto_out: SendBuf::default(),
            crypto_in: Reassembly::new(MAX_CRYPTO_BUFFER as u64),
            recs: RecLog::new(),
            probes: 0,
            ack_owed: false,
            loss_time: None,
        }
    }

    fn rec_index(&self) -> u64 {
        self.recs.next_index()
    }
}

struct SendSide {
    st: SendStream,
    buf: SendBuf,
    /// RESET_STREAM to send: (code, final size, whether in flight or sent).
    reset: Option<(u64, u64, bool)>,
    /// The peer's STOP_SENDING code.
    stopped: Option<u64>,
    /// Whether the app was told it may write.
    want_writable: bool,
    /// The offset after the last new byte sent: the stream's flow control
    /// usage.
    sent_new: u64,
}

struct RecvSide {
    st: RecvStream,
    asm: Reassembly,
    /// The limit last advertised (initial or MAX_STREAM_DATA).
    advertised: u64,
    /// A MAX_STREAM_DATA is owed.
    send_max: bool,
    /// The peer's RESET_STREAM code.
    reset: Option<u64>,
    /// STOP_SENDING to send: (code, sent).
    stop: Option<(u64, bool)>,
    /// The app read everything (through the FIN) or the reset.
    done: bool,
}

struct Stream {
    send: Option<SendSide>,
    recv: Option<RecvSide>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum State {
    Handshake,
    Established,
    /// We sent CONNECTION_CLOSE; until the time.
    Closing(u64),
    /// The peer sent one; until the time.
    Draining(u64),
    Closed,
}

/// A server connection.
pub struct Connection<P: Provider> {
    cfg: Arc<Config<P>>,
    prov: P,
    tls: QuicServer<P>,
    state: State,
    spaces: [Space<P>; 3],
    /// Our connection ID, and the client's.
    pub(crate) local_cid: [u8; CID_LEN],
    remote_cid: Vec<u8>,
    /// The client's first Destination Connection ID.
    pub(crate) odcid: Vec<u8>,
    budget: Budget,
    rtt: Rtt,
    cc: Cc,
    pto_count: u32,
    /// The peer's transport parameters, once known.
    peer_max_ack_delay: u64,
    peer_ack_exponent: u64,
    peer_idle: u64,
    peer_max_udp: u64,
    /// The largest UDP payload we send now.
    mtu: usize,
    /// Path MTU discovery.
    pmtu: Pmtu,
    /// Flow control: what we may send, and what the peer may.
    tx_credit: SendCredit,
    rx_credit: RecvCredit,
    rx_advertised: u64,
    /// Bytes the application read, across streams.
    read_total: u64,
    send_max_data: bool,
    /// The peer's initial_max_stream_data_bidi_local, _bidi_remote, _uni.
    peer_stream_data: (u64, u64, u64),
    ids: Option<StreamIds>,
    streams: IdMap<Stream>,
    /// Streams with data or frames to send, round-robin, and the set of
    /// them.
    sendq: VecDeque<u64>,
    queued: IdSet,
    /// Scratch for ACK processing.
    scratch_rs: Vec<(u64, u64)>,
    scratch_done: Vec<Done>,
    /// Peer-opened streams not yet accepted.
    accept_bidi: VecDeque<u64>,
    accept_uni: VecDeque<u64>,
    /// MAX_STREAMS owed.
    send_max_streams: [bool; 2],
    streams_allowed: [u64; 2],
    streams_closed: [u64; 2],
    send_handshake_done: bool,
    path_response: Option<[u8; 8]>,
    events: VecDeque<Event>,
    /// Unacknowledged stream bytes across the connection.
    buffered: usize,
    /// 1-RTT key phase: our current phase bit; the next receive keys and
    /// both secrets.
    /// The 1-RTT key generation (verified `keyphase`).
    kp: KeyPhase,
    rx_next: Option<Aead<P::Key>>,
    rx_prev: Option<Aead<P::Key>>,
    secrets: Option<(Secret, Secret)>,
    suite: u16,
    /// Idle timer: the last packet received, or first ack-eliciting sent
    /// after it.
    idle_from: u64,
    /// The close to send: (code, app, frame type, sent this round).
    close: Option<(u64, bool)>,
    close_owed: bool,
    /// When an ack-eliciting packet last went out.
    last_eliciting: u64,
    /// Which spaces' keys are installed and discarded (verified
    /// `schedule`).
    ks: KeySchedule,
    /// Bytes of the client's first Initial's Source Connection ID, for
    /// checking initial_source_connection_id (§7.3).
    client_scid: Vec<u8>,
    /// 1-RTT packets that arrived before the handshake completed.
    early: Vec<(Vec<u8>, usize)>,
    replay_early: bool,
}

/// Adds stream `id` to the send queue, once.
macro_rules! queue {
    ($s:expr, $id:expr) => {
        if $s.queued.insert($id) {
            $s.sendq.push_back($id);
        }
    };
}

/// A hasher for stream IDs: they are small integers the peer can only
/// open in order within its stream limit, so a multiply spreads them.
#[derive(Default, Clone, Copy)]
pub struct IdHasher(u64);

impl std::hash::Hasher for IdHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, b: &[u8]) {
        for &x in b {
            self.0 = (self.0.rotate_left(8) ^ x as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (x ^ (x >> 29)).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    }
}

type IdMap<V> = HashMap<u64, V, std::hash::BuildHasherDefault<IdHasher>>;
type IdSet = std::collections::HashSet<u64, std::hash::BuildHasherDefault<IdHasher>>;

fn vlen(v: u64) -> usize {
    if v < 64 {
        1
    } else if v < 16384 {
        2
    } else if v < 1 << 30 {
        4
    } else {
        8
    }
}


const LEVELS: [u8; 3] = [INITIAL, HANDSHAKE, ONE_RTT];

impl<P: Provider> Connection<P> {
    /// A connection for a client Initial packet with Destination
    /// Connection ID `odcid` and Source Connection ID `scid`, received at
    /// `now`; `local_cid` is ours.
    pub fn new(cfg: Arc<Config<P>>, now: u64, odcid: &[u8], scid: &[u8], local_cid: [u8; CID_LEN]) -> Option<Connection<P>> {
        let prov = (cfg.provider)();
        // Our transport parameters (§18.2).
        let mut tp = TransportParameters::new();
        tp.original_dcid = Some(odcid);
        tp.initial_scid = Some(&local_cid);
        tp.max_idle_timeout = Some(cfg.idle_timeout_ms);
        tp.initial_max_data = Some(cfg.max_data);
        let w = cfg.stream_window.clamp(1, MAX_WINDOW);
        tp.initial_max_stream_data_bidi_remote = Some(w);
        tp.initial_max_stream_data_bidi_local = Some(w);
        tp.initial_max_stream_data_uni = Some(w);
        tp.initial_max_streams_bidi = Some(cfg.max_streams_bidi);
        tp.initial_max_streams_uni = Some(cfg.max_streams_uni);
        tp.max_ack_delay = Some(cfg.max_ack_delay_ms);
        tp.max_udp_payload_size = Some(65527);
        tp.disable_active_migration = true;
        let mut tpb = Vec::new();
        params::encode(&tp, &mut tpb);
        let tls = QuicServer::new(cfg.tls.clone(), (cfg.provider)(), tpb)?;
        let (c, s) = initial_secrets_x(odcid);
        let mut spaces = [Space::new(), Space::new(), Space::new()];
        spaces[0].rx = Some(keys(&prov, INITIAL_SUITE, &c));
        spaces[0].tx = Some(keys(&prov, INITIAL_SUITE, &s));
        let mds = cfg.max_datagram.clamp(1200, 65527) as u64;
        Some(Connection {
            prov,
            tls,
            state: State::Handshake,
            spaces,
            local_cid,
            remote_cid: scid.to_vec(),
            odcid: odcid.to_vec(),
            budget: Budget::new(false),
            rtt: Rtt::new(),
            cc: if cfg.cubic { Cc::Cubic(Cubic::new(mds)) } else { Cc::Reno(NewReno::new(mds)) },
            pto_count: 0,
            peer_max_ack_delay: 25_000,
            peer_ack_exponent: 3,
            peer_idle: 0,
            peer_max_udp: 65527,
            mtu: mds as usize,
            pmtu: if cfg.probe_datagram > mds as usize { Pmtu::Due { fails: 0 } } else { Pmtu::Done },
            tx_credit: SendCredit::new(0),
            rx_credit: RecvCredit::new(cfg.max_data),
            rx_advertised: cfg.max_data,
            read_total: 0,
            send_max_data: false,
            peer_stream_data: (0, 0, 0),
            ids: None,
            streams: IdMap::default(),
            sendq: VecDeque::new(),
            queued: IdSet::default(),
            scratch_rs: Vec::new(),
            scratch_done: Vec::new(),
            accept_bidi: VecDeque::new(),
            accept_uni: VecDeque::new(),
            send_max_streams: [false; 2],
            streams_allowed: [cfg.max_streams_bidi, cfg.max_streams_uni],
            streams_closed: [0; 2],
            send_handshake_done: false,
            path_response: None,
            events: VecDeque::new(),
            buffered: 0,
            kp: KeyPhase::new(),
            rx_next: None,
            rx_prev: None,
            secrets: None,
            suite: INITIAL_SUITE,
            idle_from: now,
            close: None,
            close_owed: false,
            last_eliciting: now,
            ks: KeySchedule::new(),
            client_scid: scid.to_vec(),
            early: Vec::new(),
            replay_early: false,
            cfg,
        })
    }

    /// The handshake has not completed.
    pub fn is_handshaking(&self) -> bool {
        !self.ks.complete()
    }

    /// The connection is gone: drop it.
    pub fn is_closed(&self) -> bool {
        self.state == State::Closed
    }

    /// The negotiated ALPN protocol.
    pub fn alpn(&self) -> Option<&[u8]> {
        self.tls.alpn()
    }

    /// The next event.
    pub fn poll(&mut self) -> Option<Event> {
        self.events.pop_front()
    }

    // -----------------------------------------------------------------
    // Receiving
    // -----------------------------------------------------------------

    /// A datagram arrived (§12.2: one or more coalesced packets).
    pub fn handle_datagram(&mut self, now: u64, data: &mut [u8]) {
        if self.state == State::Closed {
            return;
        }
        self.budget.on_received(data.len() as u64);
        if let State::Draining(_) = self.state {
            return;
        }
        let mut p = 0;
        while p < data.len() {
            let Some((h, e)) = packet::parse_header(data, p, CID_LEN) else { break };
            let (space, end, dcid_ok) = match h {
                Header::Long { first, dcid, len, .. } => {
                    if len as usize > data.len() - e {
                        break;
                    }
                    let end = e + len as usize;
                    let s = match (first >> 4) & 3 {
                        0 => Some(0),
                        2 => Some(1),
                        _ => None,
                    };
                    let ok = dcid == &self.local_cid[..] || (s == Some(0) && dcid == &self.odcid[..]);
                    (s, end, ok)
                }
                Header::Short { dcid, .. } => (Some(2), data.len(), dcid == &self.local_cid[..]),
                _ => break,
            };
            if let Some(s) = space {
                if dcid_ok {
                    let pn_off = e - p;
                    self.handle_packet(now, s, &mut data[p..end], pn_off);
                }
            }
            p = end;
            if self.state == State::Closed {
                return;
            }
        }
        if self.replay_early {
            self.replay_early = false;
            for (mut pkt, pn_off) in std::mem::take(&mut self.early) {
                self.handle_packet(now, 2, &mut pkt, pn_off);
            }
        }
    }

    fn handle_packet(&mut self, now: u64, s: usize, pkt: &mut [u8], pn_off: usize) {
        if s == 2 && !self.ks.complete() {
            // §5.7 of RFC 9001: no 1-RTT before the handshake completes;
            // a few are kept to process once it does.
            if self.early.len() < 4 {
                self.early.push((pkt.to_vec(), pn_off));
            }
            return;
        }
        if !self.ks.may_open(s) {
            return;
        }
        let Some((_, hp)) = self.spaces[s].rx.as_ref() else { return };
        let Some((n, t)) = unmask(hp, pkt, pn_off) else { return };
        let expected = match self.spaces[s].recv.largest() {
            Some(l) => l + 1,
            None => 0,
        };
        let pn = packet::decode_pn(expected.min(verilith_quic::recv::PN_LIMIT - 1), t, n);
        let hdr = pn_off + n;
        let first = pkt[0];
        let bit = first & 0x04 != 0;
        // Which generation's keys (§6.3 of RFC 9001, verified `keyphase`).
        let g = if s == 2 { self.kp.select(bit, pn) } else { Gen::Current };
        let res = match g {
            Gen::Current => match self.spaces[s].rx.as_ref() {
                Some((aead, _)) => aead.open(pn, pkt, hdr),
                None => None,
            },
            Gen::Prev => self.rx_prev.as_ref().and_then(|prev| prev.open(pn, pkt, hdr)),
            Gen::Next => {
                if self.rx_next.is_none() {
                    self.prepare_next();
                }
                let r = match &self.rx_next {
                    Some(next) => next.open(pn, pkt, hdr),
                    None => None,
                };
                if r.is_some() {
                    self.on_peer_key_update(bit, pn);
                }
                r
            }
        };
        let Some(len) = res else { trace(format_args!("rx s{s} pn{pn} undecryptable")); return };
        trace(format_args!("rx s{s} pn{pn} len{len}"));
        // Reserved bits (§17.2, §17.3.1), checked after decryption.
        let reserved = if s == 2 { first & 0x18 } else { first & 0x0c };
        if reserved != 0 {
            self.close_err(now, PROTOCOL_VIOLATION);
            return;
        }
        if self.spaces[s].recv.is_dup(pn) {
            return;
        }
        if s == 1 && self.ks.on_handshake_packet() {
            // §4.9.1 of RFC 9001: the server discards Initial keys on its
            // first Handshake packet, and the address is validated (§8.1).
            self.discard(0);
            self.budget.validate();
        }
        self.idle_from = now;
        let payload = &pkt[hdr..hdr + len];
        let eliciting = match self.handle_frames(now, s, payload) {
            Ok(e) => e,
            Err(code) => {
                self.close_err(now, code);
                return;
            }
        };
        if self.ks.discarded(s) {
            return;
        }
        self.spaces[s].recv.insert(pn, now, eliciting);
        if eliciting {
            self.spaces[s].ack_owed = true;
        }
        if let State::Closing(_) = self.state {
            self.close_owed = true;
        }
    }

    fn prepare_next(&mut self) {
        if let Some((c, _)) = &self.secrets {
            let (_, a) = update(&self.prov, self.suite, c);
            self.rx_next = Some(a);
        }
    }

    /// The peer moved to the next key phase with packet `pn` (§6.2): we
    /// follow, for receiving and sending.
    fn on_peer_key_update(&mut self, bit: bool, pn: u64) {
        if self.secrets.is_none() || !self.kp.on_update(bit, pn) {
            return;
        }
        let Some((c, sv)) = self.secrets.take() else { return };
        let (c2, _) = update(&self.prov, self.suite, &c);
        let (s2, tx) = update(&self.prov, self.suite, &sv);
        let next = self.rx_next.take().expect("prepared");
        let sp = &mut self.spaces[2];
        let (old, hp) = sp.rx.take().expect("1-RTT keys");
        sp.rx = Some((next, hp));
        self.rx_prev = Some(old);
        if let Some((_, hp)) = sp.tx.take() {
            sp.tx = Some((tx, hp));
        }
        self.secrets = Some((c2, s2));
        // The generation after, ready before the peer uses it, so that
        // opening a packet takes the same time either way (§6.3, §9.5).
        self.prepare_next();
    }

    /// Discards a space's keys and state (§4.9 of RFC 9001, §6.4 of RFC
    /// 9002).
    fn discard(&mut self, s: usize) {
        let sp = &mut self.spaces[s];
        sp.rx = None;
        sp.tx = None;
        sp.sent.discard();
        sp.recs.clear();
        sp.loss_time = None;
        sp.probes = 0;
        sp.ack_owed = false;
        sp.crypto_out = SendBuf::default();
        self.pto_count = 0;
    }

    fn handle_frames(&mut self, now: u64, s: usize, payload: &[u8]) -> Result<bool, u64> {
        let mut p = 0;
        let mut eliciting = false;
        if payload.is_empty() {
            return Err(PROTOCOL_VIOLATION);
        }
        while p < payload.len() {
            let Some((f, next)) = frame::parse(payload, p) else { return Err(FRAME_ENCODING_ERROR) };
            trace(format_args!("  frame 0x{:02x}", payload[p]));
            p = next;
            // Table 3 (§12.4), and the frames only a server sends (verified
            // `allowed`).
            let level = [Level::Initial, Level::Handshake, Level::OneRtt][s];
            if !allowed::allowed(&f, level) || !allowed::server_receives(&f) {
                return Err(PROTOCOL_VIOLATION);
            }
            if allowed::ack_eliciting(&f) {
                eliciting = true;
            }
            match f {
                Frame::Padding(_) | Frame::Ping => {}
                Frame::Ack(a) => {
                    let mut rs = std::mem::take(&mut self.scratch_rs);
                    rs.clear();
                    rs.push((a.largest - a.first, a.largest));
                    let mut it = a.ranges();
                    while let Some(r) = it.next() {
                        rs.push(r);
                    }
                    let delay = if s == 2 { a.delay.checked_shl(self.peer_ack_exponent as u32).unwrap_or(u64::MAX) } else { 0 };
                    let r = self.on_ack(now, s, &rs, delay);
                    self.scratch_rs = rs;
                    r?;
                }
                Frame::Crypto { offset, data } => self.on_crypto(now, s, offset, data)?,
                Frame::Stream { id, offset, fin, data, .. } => self.on_stream(id, offset, data, fin)?,
                Frame::ResetStream { id, err, final_size } => self.on_reset(id, err, final_size)?,
                Frame::StopSending { id, err } => {
                    self.open_for(id, Use::PeerReceives)?;
                    if let Some(Stream { send: Some(snd), .. }) = self.streams.get_mut(&id) {
                        if snd.stopped.is_none() {
                            snd.stopped = Some(err);
                            self.events.push_back(Event::Stopped { id, code: err });
                        }
                    }
                }
                Frame::MaxData(m) => {
                    let blocked = self.tx_credit.available() == 0;
                    self.tx_credit.on_max(m);
                    if blocked && self.tx_credit.available() > 0 {
                        self.wake_writers();
                    }
                }
                Frame::MaxStreamData { id, max } => {
                    self.open_for(id, Use::PeerReceives)?;
                    if let Some(Stream { send: Some(snd), .. }) = self.streams.get_mut(&id) {
                        snd.st.on_max_stream_data(max);
                        if snd.buf.has_pending() {
                            queue!(self, id);
                        }
                    }
                }
                Frame::MaxStreams { bidi, max } => {
                    if let Some(ids) = &mut self.ids {
                        ids.on_max_streams(bidi, max);
                    }
                }
                Frame::DataBlocked(_) | Frame::StreamsBlocked { .. } => {}
                Frame::StreamDataBlocked { id, .. } => {
                    self.open_for(id, Use::PeerSends)?;
                }
                Frame::NewConnectionId { retire, seq, .. } => {
                    if retire > seq {
                        return Err(FRAME_ENCODING_ERROR);
                    }
                }
                Frame::RetireConnectionId(seq) => {
                    // We issued only sequence number 0, which the peer is
                    // using (§19.16).
                    if seq > 0 {
                        return Err(PROTOCOL_VIOLATION);
                    }
                }
                Frame::PathChallenge(d) => {
                    let mut b = [0u8; 8];
                    b.copy_from_slice(d);
                    self.path_response = Some(b);
                }
                Frame::PathResponse(_) => {}
                Frame::ConnectionClose { app, err, .. } => {
                    let pto = self.pto_duration(2);
                    self.state = State::Draining(now + 3 * pto);
                    self.events.push_back(Event::Closed { code: err, app, remote: true });
                    return Ok(false);
                }
                // Refused above.
                Frame::NewToken(_) | Frame::HandshakeDone => return Err(PROTOCOL_VIOLATION),
            }
        }
        Ok(eliciting)
    }

    fn on_ack(&mut self, now: u64, s: usize, rs: &[(u64, u64)], delay: u64) -> Result<(), u64> {
        let mut done = std::mem::take(&mut self.scratch_done);
        done.clear();
        let sp = &mut self.spaces[s];
        let info = match sp.sent.on_ack(rs, &mut done) {
            Ok(i) => i,
            Err(_) => {
                self.scratch_done = done;
                return Err(PROTOCOL_VIOLATION);
            }
        };
        if let Some((largest, eliciting)) = info.largest_new {
            if eliciting && largest == rs[0].1 {
                if let Some(d) = done.iter().find(|d| d.pn == largest) {
                    let sample = now.saturating_sub(d.packet.time);
                    let max_delay = if s == 2 { self.peer_max_ack_delay } else { 0 };
                    self.rtt.update(sample, delay, max_delay, self.ks.complete());
                }
            }
        }
        if !done.is_empty() && info.eliciting {
            self.pto_count = 0;
        }
        for d in &done {
            if s == 2 && matches!(self.pmtu, Pmtu::Sent { pn, .. } if pn == d.pn) {
                // The path carries the probe's size.
                let size = (d.packet.size as usize).clamp(self.mtu, 65527);
                self.mtu = size;
                if size as u64 > self.cc.mds() {
                    self.cc.raise_mds(size as u64);
                }
                // On to the next step (Done if there is none).
                self.pmtu = Pmtu::Due { fails: 0 };
                trace(format_args!("mtu {size}"));
            }
            if d.packet.in_flight {
                self.cc.on_ack(d.packet.time, (d.packet.size as u64).min(self.cc.mds()), now, self.rtt.smoothed);
            }
            self.on_recs(s, d.packet.token, true);
        }
        self.scratch_done = done;
        self.detect_lost(now, s);
        Ok(())
    }

    fn detect_lost(&mut self, now: u64, s: usize) {
        let mut lost = std::mem::take(&mut self.scratch_done);
        lost.clear();
        let loss_delay = self.rtt.loss_delay();
        let pc = self.rtt.persistent(if s == 2 { self.peer_max_ack_delay.min(verilith_quic::rtt::MAX_RTT) } else { 0 });
        let sp = &mut self.spaces[s];
        let r = sp.sent.detect_lost(now, loss_delay, pc, &mut lost);
        sp.loss_time = r.timer;
        let mut latest_lost = None;
        for d in &lost {
            trace(format_args!("lost s{s} pn{} size{}", d.pn, d.packet.size));
            if s == 2 {
                if let Pmtu::Sent { pn, fails } = self.pmtu {
                    if pn == d.pn {
                        // A lost probe says nothing about congestion
                        // (§14.4).
                        self.pmtu = if fails >= 2 { Pmtu::Done } else { Pmtu::Due { fails: fails + 1 } };
                        self.on_recs(s, d.packet.token, false);
                        continue;
                    }
                }
            }
            if d.packet.in_flight {
                latest_lost = Some(latest_lost.map_or(d.packet.time, |t: u64| t.max(d.packet.time)));
            }
            self.on_recs(s, d.packet.token, false);
        }
        self.scratch_done = lost;
        if let Some(t) = latest_lost {
            self.cc.on_congestion(t, now);
            trace(format_args!("congestion cwnd{}", self.cc.cwnd()));
        }
        if r.persistent && self.rtt.sampled {
            self.cc.on_persistent();
        }
    }

    /// A packet's frames were acknowledged (`acked`) or lost.
    fn on_recs(&mut self, s: usize, token: u64, acked: bool) {
        let (start, count) = reclog::unpack(token);
        for k in start..start + count {
            let Some(rec) = self.spaces[s].recs.take(k) else { continue };
            self.on_rec(s, rec, acked);
        }
        self.spaces[s].recs.trim();
    }

    fn on_rec(&mut self, s: usize, rec: Rec, acked: bool) {
        match rec {
            Rec::Ack | Rec::Ping | Rec::Close => {}
            Rec::Crypto { off, len } => {
                let sp = &mut self.spaces[s];
                if acked {
                    sp.crypto_out.on_ack(off, len as usize, false);
                } else {
                    sp.crypto_out.on_lost(off, len as usize, false);
                }
            }
            Rec::Stream { id, off, len, fin } => {
                let Some(st) = self.streams.get_mut(&id) else { return };
                let Some(snd) = &mut st.send else { return };
                if snd.reset.is_some() {
                    return;
                }
                if acked {
                    let before = snd.buf.unacked();
                    snd.buf.on_ack(off, len as usize, fin);
                    let freed = before - snd.buf.unacked();
                    let finished = snd.buf.all_acked() && snd.st.get_state() == SendState::DataSent;
                    if finished {
                        snd.st.on_all_acked();
                    }
                    let wake = freed > 0 && snd.want_writable;
                    if wake {
                        snd.want_writable = false;
                    }
                    self.buffered -= freed;
                    if wake {
                        self.events.push_back(Event::Writable(id));
                    }
                    if finished {
                        self.maybe_remove(id);
                    }
                } else {
                    snd.buf.on_lost(off, len as usize, fin);
                    queue!(self, id);
                }
            }
            Rec::Reset { id } => {
                let Some(st) = self.streams.get_mut(&id) else { return };
                let Some(snd) = &mut st.send else { return };
                if acked {
                    if snd.st.get_state() == SendState::ResetSent {
                        snd.st.on_reset_acked();
                    }
                    self.maybe_remove(id);
                } else if let Some((c, f, _)) = snd.reset {
                    snd.reset = Some((c, f, false));
                    queue!(self, id);
                }
            }
            Rec::Stop { id } => {
                if !acked {
                    if let Some(Stream { recv: Some(r), .. }) = self.streams.get_mut(&id) {
                        if let Some((c, _)) = r.stop {
                            if r.st.get_state() == RecvState::Recv || r.st.get_state() == RecvState::SizeKnown {
                                r.stop = Some((c, false));
                                queue!(self, id);
                            }
                        }
                    }
                }
            }
            Rec::MaxData => {
                if !acked {
                    self.send_max_data = true;
                }
            }
            Rec::MaxStreamData { id } => {
                if !acked {
                    if let Some(Stream { recv: Some(r), .. }) = self.streams.get_mut(&id) {
                        if r.st.get_state() == RecvState::Recv {
                            r.send_max = true;
                            queue!(self, id);
                        }
                    }
                }
            }
            Rec::MaxStreams { bidi } => {
                if !acked {
                    self.send_max_streams[if bidi { 0 } else { 1 }] = true;
                }
            }
            Rec::HandshakeDone => {
                if !acked {
                    self.send_handshake_done = true;
                }
            }
        }
    }

    fn on_crypto(&mut self, now: u64, s: usize, offset: u64, data: &[u8]) -> Result<(), u64> {
        {
            let sp = &mut self.spaces[s];
            if offset + data.len() as u64 > verilith_quic::reasm::OFFSET_LIMIT || !sp.crypto_in.insert(offset, data) {
                return Err(CRYPTO_BUFFER_EXCEEDED);
            }
        }
        let level = LEVELS[s];
        loop {
            let chunk = self.spaces[s].crypto_in.peek();
            if chunk.is_empty() {
                break;
            }
            let n = chunk.len();
            let mut out = Out::new();
            let r = self.tls.read(level, chunk, &mut out);
            self.spaces[s].crypto_in.consume(n);
            for (i, d) in [&out.initial, &out.handshake, &out.one_rtt].into_iter().enumerate() {
                if !d.is_empty() && !self.ks.discarded(i) {
                    self.spaces[i].crypto_out.write(d);
                }
            }
            match r {
                Err(code) => return Err(code),
                Ok(TlsEvent::Nothing) => {}
                Ok(TlsEvent::Accepted) => self.on_accepted()?,
                Ok(TlsEvent::Done) => self.on_done(now),
            }
        }
        Ok(())
    }

    /// The server's flight is written: Handshake keys, the server's 1-RTT
    /// keys, and the client's transport parameters.
    fn on_accepted(&mut self) -> Result<(), u64> {
        if !self.ks.on_server_flight() {
            return Err(INTERNAL_ERROR);
        }
        let suite = self.tls.suite().ok_or(INTERNAL_ERROR)?;
        self.suite = suite;
        let (c, s) = self.tls.hs_secrets().ok_or(INTERNAL_ERROR)?;
        self.spaces[1].rx = Some(keys(&self.prov, suite, c));
        self.spaces[1].tx = Some(keys(&self.prov, suite, s));
        let (c, s) = self.tls.ap_secrets().ok_or(INTERNAL_ERROR)?;
        let c = Secret::from_slice(c.as_slice(), c.len());
        let s = Secret::from_slice(s.as_slice(), s.len());
        self.spaces[2].tx = Some(keys(&self.prov, suite, &s));
        self.spaces[2].rx = Some(keys(&self.prov, suite, &c));
        self.secrets = Some((c, s));
        // The client's transport parameters (§7.4, §18.2).
        let tpb = self.tls.peer_params().to_vec();
        let tp = params::parse(&tpb).ok_or(TRANSPORT_PARAMETER_ERROR)?;
        if !params::client_ok(&tp) {
            return Err(TRANSPORT_PARAMETER_ERROR);
        }
        if tp.initial_scid != Some(&self.client_scid[..]) {
            return Err(TRANSPORT_PARAMETER_ERROR);
        }
        let g = |v: Option<u64>, d: u64| v.unwrap_or(d);
        let ade = g(tp.ack_delay_exponent, 3);
        let mad = g(tp.max_ack_delay, 25);
        if ade > 20 || mad >= 1 << 14 {
            return Err(TRANSPORT_PARAMETER_ERROR);
        }
        self.peer_ack_exponent = ade;
        self.peer_max_ack_delay = mad * 1000;
        self.peer_idle = g(tp.max_idle_timeout, 0);
        self.peer_max_udp = g(tp.max_udp_payload_size, 65527);
        if self.peer_max_udp < 1200 {
            return Err(TRANSPORT_PARAMETER_ERROR);
        }
        self.tx_credit = SendCredit::new(g(tp.initial_max_data, 0));
        let lim = verilith_quic::spec::MAX_STREAMS_LIMIT;
        let pb = g(tp.initial_max_streams_bidi, 0).min(lim);
        let pu = g(tp.initial_max_streams_uni, 0).min(lim);
        self.peer_stream_data = (
            g(tp.initial_max_stream_data_bidi_local, 0),
            g(tp.initial_max_stream_data_bidi_remote, 0),
            g(tp.initial_max_stream_data_uni, 0),
        );
        self.ids = Some(StreamIds::new(true, self.cfg.max_streams_bidi.min(lim), self.cfg.max_streams_uni.min(lim), pb, pu));
        Ok(())
    }

    fn on_done(&mut self, now: u64) {
        // §4.9.2 of RFC 9001: the server's handshake is confirmed now, and
        // Handshake keys are discarded.
        if !self.ks.on_complete() {
            return;
        }
        self.state = State::Established;
        self.send_handshake_done = true;
        self.discard(1);
        self.events.push_back(Event::Connected);
        self.replay_early = true;
        let _ = now;
    }

    /// The stream a frame from the peer is about, creating the streams it
    /// opens; `None` if it is already closed and forgotten.
    #[allow(dead_code)]
    fn stream_for(&mut self, id: u64, u: Use) -> Result<Option<&mut Stream>, u64> {
        self.open_for(id, u)?;
        Ok(self.streams.get_mut(&id))
    }

    fn open_for(&mut self, id: u64, u: Use) -> Result<(), u64> {
        let Some(ids) = &mut self.ids else { return Err(PROTOCOL_VIOLATION) };
        let n = ids.on_frame(id, u)?;
        if n > 0 {
            // Streams of this type up to `id` are opened (§3.2).
            let bidi = id & 2 == 0;
            let last = id / 4;
            for k in (last + 1 - n)..=last {
                let sid = k * 4 + (id & 3);
                self.create_peer_stream(sid, bidi);
            }
            self.events.push_back(Event::Opened { bidi });
        }
        Ok(())
    }

    /// Each stream's receive window (at most [`MAX_WINDOW`]).
    fn stream_window(&self) -> u64 {
        self.cfg.stream_window.clamp(1, MAX_WINDOW)
    }

    fn create_peer_stream(&mut self, id: u64, bidi: bool) {
        let w = self.stream_window();
        let recv = Some(RecvSide {
            st: RecvStream::new(w),
            asm: Reassembly::new(w),
            advertised: w,
            send_max: false,
            reset: None,
            stop: None,
            done: false,
        });
        let send = if bidi { Some(self.new_send(self.peer_stream_data.0)) } else { None };
        self.streams.insert(id, Stream { send, recv });
        if bidi {
            self.accept_bidi.push_back(id);
        } else {
            self.accept_uni.push_back(id);
        }
    }

    fn new_send(&self, max: u64) -> SendSide {
        SendSide {
            st: SendStream::new(max.min(verilith_quic::spec::VARINT_MAX)),
            buf: SendBuf::default(),
            reset: None,
            stopped: None,
            want_writable: false,
            sent_new: 0,
        }
    }

    fn on_stream(&mut self, id: u64, offset: u64, data: &[u8], fin: bool) -> Result<(), u64> {
        let len = data.len() as u64;
        trace(format_args!("stream {id} off{offset} len{len} fin{fin}"));
        if offset + len > verilith_quic::spec::VARINT_MAX {
            return Err(FRAME_ENCODING_ERROR);
        }
        self.open_for(id, Use::PeerSends)?;
        let Some(st) = self.streams.get_mut(&id) else { return Ok(()) };
        let Some(r) = &mut st.recv else { return Err(STREAM_STATE_ERROR) };
        r.st.on_stream(&mut self.rx_credit, offset, len, fin)?;
        if r.reset.is_some() || r.stop.is_some() {
            return Ok(());
        }
        let before = r.asm.contiguous();
        // Flow control (above) keeps the data within the window.
        if !r.asm.insert(offset, data) {
            return Err(FLOW_CONTROL_ERROR);
        }
        let size_known_all = matches!(r.st.get_final_size(), Some(f) if r.asm.contiguous() == f);
        if size_known_all && r.st.get_state() == RecvState::SizeKnown {
            r.st.on_all_received();
        }
        if r.asm.contiguous() > before || size_known_all {
            self.events.push_back(Event::Readable(id));
        }
        Ok(())
    }

    fn on_reset(&mut self, id: u64, err: u64, final_size: u64) -> Result<(), u64> {
        self.open_for(id, Use::PeerSends)?;
        let Some(st) = self.streams.get_mut(&id) else { return Ok(()) };
        let Some(r) = &mut st.recv else { return Err(STREAM_STATE_ERROR) };
        r.st.on_reset(&mut self.rx_credit, final_size)?;
        if r.reset.is_none() && !r.done {
            r.reset = Some(err);
            self.events.push_back(Event::Readable(id));
        }
        Ok(())
    }

    fn wake_writers(&mut self) {
        let ids: Vec<u64> = self
            .streams
            .iter_mut()
            .filter_map(|(&id, s)| match &mut s.send {
                Some(snd) if snd.want_writable => {
                    snd.want_writable = false;
                    Some(id)
                }
                _ => None,
            })
            .collect();
        for id in ids {
            self.events.push_back(Event::Writable(id));
        }
    }

    // -----------------------------------------------------------------
    // The application's side of streams
    // -----------------------------------------------------------------

    /// A stream the peer opened, not yet accepted.
    pub fn accept(&mut self, bidi: bool) -> Option<u64> {
        if bidi { self.accept_bidi.pop_front() } else { self.accept_uni.pop_front() }
    }

    /// Opens a stream of ours; `None` if the peer's limit is reached.
    pub fn open(&mut self, bidi: bool) -> Option<u64> {
        let id = self.ids.as_mut()?.open(!bidi)?;
        let (_, remote, uni) = self.peer_stream_data;
        let send = Some(self.new_send(if bidi { remote } else { uni }));
        let recv = if bidi {
            let w = self.stream_window();
            Some(RecvSide { st: RecvStream::new(w), asm: Reassembly::new(w), advertised: w, send_max: false, reset: None, stop: None, done: false })
        } else {
            None
        };
        self.streams.insert(id, Stream { send, recv });
        Some(id)
    }

    /// Reads up to `max` bytes of stream `id` into `out`. `Ok((n, fin))`:
    /// `n` bytes, and `fin` once the stream's end is reached.
    pub fn read(&mut self, id: u64, out: &mut Vec<u8>, max: usize) -> Result<(usize, bool), StreamError> {
        let w = self.stream_window();
        let Some(Stream { recv: Some(r), .. }) = self.streams.get_mut(&id) else { return Err(StreamError::Unknown) };
        if r.done {
            return Err(StreamError::Closed);
        }
        if let Some(code) = r.reset {
            r.done = true;
            if r.st.get_state() == RecvState::ResetRecvd {
                r.st.on_reset_read();
            }
            self.maybe_remove(id);
            return Err(StreamError::Reset(code));
        }
        let n = r.asm.read_into(out, max);
        let fin = matches!(r.st.get_final_size(), Some(f) if r.asm.read_offset() == f);
        if n == 0 && !fin {
            return Err(StreamError::Blocked);
        }
        // Flow control credit: raise the stream's limit, and the
        // connection's, once half the window is consumed (§4.2).
        if !fin && r.st.get_state() == RecvState::Recv && r.asm.read_offset() + w - r.advertised >= w / 2 {
            let m = r.asm.read_offset() + w;
            if m < verilith_quic::spec::VARINT_LIMIT {
                r.st.raise(m);
                r.advertised = m;
                r.send_max = true;
                queue!(self, id);
            }
        }
        if fin {
            r.done = true;
            if r.st.get_state() == RecvState::DataRecvd {
                r.st.on_read_all();
            }
        }
        self.conn_read(n as u64);
        if fin {
            self.maybe_remove(id);
        }
        Ok((n, fin))
    }

    fn conn_read(&mut self, n: u64) {
        self.read_total += n;
        let w = self.cfg.max_data;
        if self.read_total + w - self.rx_advertised >= w / 2 {
            let m = self.read_total + w;
            if m < verilith_quic::spec::VARINT_LIMIT {
                self.rx_credit.raise(m);
                self.rx_advertised = m;
                self.send_max_data = true;
            }
        }
    }

    /// Writes to stream `id`: returns how many bytes it took (all of
    /// `data`, unless the connection's send buffer is full).
    pub fn write(&mut self, id: u64, data: &[u8]) -> Result<usize, StreamError> {
        let room = self.cfg.send_buffer.saturating_sub(self.buffered);
        let Some(Stream { send: Some(snd), .. }) = self.streams.get_mut(&id) else { return Err(StreamError::Unknown) };
        if let Some(code) = snd.stopped {
            return Err(StreamError::Reset(code));
        }
        if snd.reset.is_some() || snd.buf.fin() {
            return Err(StreamError::Closed);
        }
        let n = data.len().min(room);
        trace(format_args!("write {id} {n}"));
        if n == 0 && !data.is_empty() {
            snd.want_writable = true;
            return Err(StreamError::Blocked);
        }
        snd.buf.write(&data[..n]);
        if n < data.len() {
            snd.want_writable = true;
        }
        self.buffered += n;
        queue!(self, id);
        Ok(n)
    }

    /// [`Connection::write`] for a shared buffer: what of `data` fits is
    /// kept as it is, not copied, when it is large ([`crate::buf::SHARE_MIN`]).
    /// The same send-buffer limit applies: returns how many bytes were taken.
    pub fn write_bytes(&mut self, id: u64, data: &Bytes) -> Result<usize, StreamError> {
        let room = self.cfg.send_buffer.saturating_sub(self.buffered);
        let Some(Stream { send: Some(snd), .. }) = self.streams.get_mut(&id) else { return Err(StreamError::Unknown) };
        if let Some(code) = snd.stopped {
            return Err(StreamError::Reset(code));
        }
        if snd.reset.is_some() || snd.buf.fin() {
            return Err(StreamError::Closed);
        }
        let n = data.len().min(room);
        trace(format_args!("write {id} {n}"));
        if n == 0 && !data.is_empty() {
            snd.want_writable = true;
            return Err(StreamError::Blocked);
        }
        snd.buf.write_bytes(data.slice(..n));
        if n < data.len() {
            snd.want_writable = true;
        }
        self.buffered += n;
        queue!(self, id);
        Ok(n)
    }

    /// Ends stream `id` after the data written.
    pub fn finish(&mut self, id: u64) -> Result<(), StreamError> {
        let Some(Stream { send: Some(snd), .. }) = self.streams.get_mut(&id) else { return Err(StreamError::Unknown) };
        if snd.reset.is_some() || snd.buf.fin() {
            return Err(StreamError::Closed);
        }
        snd.buf.set_fin();
        queue!(self, id);
        Ok(())
    }

    /// Abandons sending on stream `id` (RESET_STREAM).
    pub fn reset(&mut self, id: u64, code: u64) -> Result<(), StreamError> {
        let Some(Stream { send: Some(snd), .. }) = self.streams.get_mut(&id) else { return Err(StreamError::Unknown) };
        if snd.reset.is_some() {
            return Err(StreamError::Closed);
        }
        let s = snd.st.get_state();
        if s != SendState::Ready && s != SendState::Send && s != SendState::DataSent {
            return Err(StreamError::Closed);
        }
        let fs = snd.st.reset();
        self.buffered -= snd.buf.unacked();
        snd.buf.clear();
        snd.reset = Some((code, fs, false));
        queue!(self, id);
        Ok(())
    }

    /// Asks the peer to stop sending on stream `id` (STOP_SENDING); data
    /// that arrives after is discarded.
    pub fn stop(&mut self, id: u64, code: u64) -> Result<(), StreamError> {
        let Some(Stream { recv: Some(r), .. }) = self.streams.get_mut(&id) else { return Err(StreamError::Unknown) };
        if r.stop.is_some() || r.done {
            return Err(StreamError::Closed);
        }
        let n = r.asm.available();
        r.asm.consume(n);
        r.done = true;
        let st = r.st.get_state();
        if st == RecvState::Recv || st == RecvState::SizeKnown {
            r.stop = Some((code, false));
            queue!(self, id);
        }
        self.conn_read(n as u64);
        self.maybe_remove(id);
        Ok(())
    }

    /// Forgets a stream both of whose sides are done (§3.3), and lets the
    /// peer open another (MAX_STREAMS).
    fn maybe_remove(&mut self, id: u64) {
        let Some(st) = self.streams.get(&id) else { return };
        let send_done = match &st.send {
            None => true,
            Some(s) => {
                let state = s.st.get_state();
                state == SendState::DataRecvd || state == SendState::ResetRecvd
            }
        };
        let recv_done = match &st.recv {
            None => true,
            Some(r) => r.done && r.stop.map_or(true, |(_, sent)| sent),
        };
        if !(send_done && recv_done) {
            return;
        }
        self.streams.remove(&id);
        // A peer's stream: allow one more (§4.6).
        if id & 1 == 0 {
            let k = if id & 2 == 0 { 0 } else { 1 };
            self.streams_closed[k] += 1;
            let lim = if k == 0 { self.cfg.max_streams_bidi } else { self.cfg.max_streams_uni };
            let target = self.streams_closed[k] + lim;
            if target - self.streams_allowed[k] >= (lim / 2).max(1) && target <= verilith_quic::spec::MAX_STREAMS_LIMIT {
                self.streams_allowed[k] = target;
                if let Some(ids) = &mut self.ids {
                    ids.allow(k == 0, target);
                }
                self.send_max_streams[k] = true;
            }
        }
    }

    /// Closes the connection with an application error code.
    pub fn close(&mut self, now: u64, code: u64) {
        if matches!(self.state, State::Closing(_) | State::Draining(_) | State::Closed) {
            return;
        }
        self.close = Some((code, true));
        self.enter_closing(now);
        self.events.push_back(Event::Closed { code, app: true, remote: false });
    }

    fn close_err(&mut self, now: u64, code: u64) {
        if matches!(self.state, State::Closing(_) | State::Draining(_) | State::Closed) {
            return;
        }
        self.close = Some((code, false));
        self.enter_closing(now);
        self.events.push_back(Event::Closed { code, app: false, remote: false });
    }

    fn enter_closing(&mut self, now: u64) {
        let pto = self.pto_duration(2);
        self.state = State::Closing(timers::add_sat(now, 3 * pto));
        self.close_owed = true;
    }

    // -----------------------------------------------------------------
    // Timers
    // -----------------------------------------------------------------

    fn pto_duration(&self, s: usize) -> u64 {
        let mad = if s == 2 { self.peer_max_ack_delay.min(verilith_quic::rtt::MAX_RTT) } else { 0 };
        self.rtt.pto(mad)
    }

    /// The idle timeout (§10.1), verified `timers::idle_timeout`.
    fn idle_timeout(&self) -> Option<u64> {
        timers::idle_timeout(self.cfg.idle_timeout_ms, self.peer_idle, self.pto_duration(2))
    }

    /// When the PTO fires, and for which space (§6.2.1).
    fn pto_time(&self) -> Option<(u64, usize)> {
        let mut last = [None; 3];
        let mut dur = [0; 3];
        for s in 0..3 {
            let sp = &self.spaces[s];
            if !self.ks.may_send(s) || sp.tx.is_none() || (s == 2 && !self.ks.complete()) {
                continue;
            }
            last[s] = sp.sent.eliciting_in_flight();
            dur[s] = self.pto_duration(s);
        }
        timers::pto_deadline(&last, &dur, self.pto_count)
    }

    /// The armed timers.
    fn timers(&self) -> Timers {
        let sp = &self.spaces[2];
        Timers {
            idle: self.idle_timeout().map(|d| timers::add_sat(self.idle_from, d)),
            loss: [self.spaces[0].loss_time, self.spaces[1].loss_time, self.spaces[2].loss_time],
            pto: self.pto_time(),
            // The amplification limit blocks probes too (§6.2.2.1).
            can_send: self.budget.allowance() > 0,
            // A delayed ACK (§13.2.1).
            ack: if sp.ack_owed && sp.recv.ack_pending() {
                Some(timers::add_sat(sp.recv.largest_time(), self.cfg.max_ack_delay_ms.saturating_mul(1000)))
            } else {
                None
            },
        }
    }

    /// The next time `handle_timeout` must be called.
    pub fn poll_timeout(&self) -> Option<u64> {
        match self.state {
            State::Closed => None,
            State::Closing(t) | State::Draining(t) => Some(t),
            _ => timers::next(&self.timers()),
        }
    }

    /// Runs the timers due at `now`.
    pub fn handle_timeout(&mut self, now: u64) {
        trace(format_args!("timeout {now} pto{:?} count{} allow{}", self.pto_time(), self.pto_count, self.budget.allowance()));
        match self.state {
            State::Closed => return,
            State::Closing(t) | State::Draining(t) => {
                if now >= t {
                    self.state = State::Closed;
                }
                return;
            }
            _ => {}
        }
        match timers::due(&self.timers(), now) {
            Due::Nothing => {}
            Due::Idle => {
                self.state = State::Closed;
                self.events.push_back(Event::Closed { code: NO_ERROR, app: false, remote: false });
            }
            Due::Loss(s) => self.detect_lost(now, s),
            Due::Pto(s) => {
                self.pto_count = self.pto_count.saturating_add(1);
                // Send two probes; data still unacknowledged goes again
                // (§6.2.4).
                self.spaces[s].probes = 2;
                self.requeue(s);
                // Before the handshake completes, probe both handshake
                // spaces (§6.2.4: "an endpoint MAY send ... in other
                // packet number spaces").
                if s == 0 && self.ks.may_send(1) && self.spaces[1].tx.is_some() {
                    self.spaces[1].probes = 1;
                    self.requeue(1);
                }
            }
        }
    }

    /// Queues the frames of every outstanding ack-eliciting packet of space
    /// `s` to be sent again, as probes.
    fn requeue(&mut self, s: usize) {
        let mut tokens = Vec::new();
        self.spaces[s].sent.outstanding(64, &mut tokens);
        for token in tokens {
            let (start, count) = reclog::unpack(token);
            for k in start..start + count {
                let Some(r) = self.spaces[s].recs.get(k) else { continue };
                // Requeue as if lost; the record stays for the packet's ACK.
                match r {
                    Rec::Crypto { .. } | Rec::Stream { .. } | Rec::HandshakeDone | Rec::MaxData | Rec::MaxStreamData { .. } => {
                        self.on_rec(s, r, false)
                    }
                    _ => {}
                }
            }
        }
    }

    // -----------------------------------------------------------------
    // Sending
    // -----------------------------------------------------------------

    fn max_datagram(&self) -> usize {
        (self.mtu as u64).min(self.peer_max_udp).max(1200) as usize
    }

    /// The size path MTU discovery probes next: the first step above
    /// what the path is known to carry, or the configured size.
    fn probe_size(&self) -> usize {
        let cap = (self.cfg.probe_datagram as u64).min(self.peer_max_udp).min(65527) as usize;
        PROBE_STEPS.iter().copied().find(|&s| s > self.mtu && s < cap).unwrap_or(cap)
    }

    /// Sends the path MTU probe as a datagram of its own, if it is due and
    /// the window has room: its size, or 0.
    fn build_mtu_probe(&mut self, now: u64, buf: &mut Vec<u8>) -> usize {
        let Pmtu::Due { fails } = self.pmtu else { return 0 };
        let size = self.probe_size();
        if size <= self.mtu {
            self.pmtu = Pmtu::Done;
            return 0;
        }
        if !self.ks.complete() || self.state != State::Established || self.spaces[2].tx.is_none() {
            return 0;
        }
        let inflight: u64 = self.spaces.iter().map(|s| s.sent.bytes_in_flight()).sum();
        if !self.cc.can_send(inflight, size as u64) || self.budget.allowance() < size as u64 {
            return 0;
        }
        let start = buf.len();
        // A probe (PING if nothing else goes), outside the window, which
        // was checked above.
        self.spaces[2].probes += 1;
        let cwnd_room = self.cc.room(inflight) as usize;
        let Some(p) = self.build_packet(now, 2, buf, size, cwnd_room) else {
            self.spaces[2].probes = self.spaces[2].probes.saturating_sub(1);
            buf.truncate(start);
            return 0;
        };
        let pad = pktbuf::pad(buf.len() - start + 16, size, false, Some(size), size);
        let pn = p.pn;
        self.seal(now, buf, p, pad);
        self.pmtu = Pmtu::Sent { pn, fails };
        if self.last_eliciting <= self.idle_from {
            self.idle_from = now;
        }
        self.last_eliciting = now;
        let n = buf.len() - start;
        self.budget.on_sent(n as u64);
        trace(format_args!("mtu probe pn{pn} size{n}"));
        n
    }

    /// Writes datagrams to send into `buf` (cleared first): up to `max`
    /// of them, all but the last of the same size.
    pub fn poll_transmit(&mut self, now: u64, max: usize, buf: &mut Vec<u8>) -> Option<Transmit> {
        buf.clear();
        let n = self.build_mtu_probe(now, buf);
        if n > 0 {
            return Some(Transmit { size: n, segment_size: None });
        }
        let mds = self.max_datagram();
        let mut seg = None;
        let mut count = 0;
        while count < max.max(1) {
            let limit = seg.unwrap_or(mds);
            // A batch for segmentation offload is one UDP payload of at
            // most 65507 bytes (Linux: and at most 64 segments).
            if count > 0 && buf.len() + limit > GSO_BYTES {
                break;
            }
            let n = self.build_datagram(now, buf, limit, seg);
            if n == 0 {
                break;
            }
            count += 1;
            if seg.is_none() {
                // Frames seldom fill a datagram to the byte: one within
                // a few bytes of full sets the batch's size, and the
                // ones after are padded to it.
                if n + BATCH_SLACK < mds {
                    break;
                }
                seg = Some(n);
            } else if n < limit {
                break;
            }
            if !matches!(self.state, State::Handshake | State::Established) {
                break;
            }
        }
        if count == 0 {
            return None;
        }
        Some(Transmit { size: buf.len(), segment_size: if count > 1 { seg } else { None } })
    }

    /// Builds one datagram at the end of `buf`, at most `limit` bytes, and
    /// padded to `fill` if it comes within [`BATCH_SLACK`] of it: returns
    /// its size (0: nothing to send).
    fn build_datagram(&mut self, now: u64, buf: &mut Vec<u8>, limit: usize, fill: Option<usize>) -> usize {
        let start = buf.len();
        let allowance = self.budget.allowance().min(limit as u64) as usize;
        if allowance < 64 {
            return 0;
        }
        match self.state {
            State::Closed | State::Draining(_) => return 0,
            State::Closing(_) => {
                if !self.close_owed {
                    return 0;
                }
                self.close_owed = false;
                return self.build_close(now, buf, allowance);
            }
            _ => {}
        }
        let mut pending: Option<Pending> = None;
        let mut has_initial_eliciting = false;
        let mut any_eliciting = false;
        for s in 0..3 {
            if !self.ks.may_send(s) || self.spaces[s].tx.is_none() {
                continue;
            }
            if !self.wants_send(now, s) {
                continue;
            }
            let room = allowance - (buf.len() - start);
            // Header (at most 1 + 4 + 21 + 21 + 1 + 2 + 4) and tag.
            if room < 70 {
                break;
            }
            if let Some(p) = pending.take() {
                self.seal(now, buf, p, 0);
            }
            let room = allowance - (buf.len() - start);
            let cwnd_room = self.cc.room(self.spaces.iter().map(|s| s.sent.bytes_in_flight()).sum());
            if let Some(p) = self.build_packet(now, s, buf, room, cwnd_room as usize) {
                if p.eliciting {
                    any_eliciting = true;
                    if s == 0 {
                        has_initial_eliciting = true;
                    }
                }
                pending = Some(p);
            }
        }
        let Some(p) = pending else { return buf.len() - start };
        // §14.1: a datagram with an ack-eliciting Initial is padded to 1200.
        let size = buf.len() - start + 16;
        let pad = pktbuf::pad(size, allowance, has_initial_eliciting, fill, BATCH_SLACK);
        self.seal(now, buf, p, pad);
        if any_eliciting {
            if self.last_eliciting <= self.idle_from {
                self.idle_from = now;
            }
            self.last_eliciting = now;
        }
        let n = buf.len() - start;
        self.budget.on_sent(n as u64);
        n
    }

    /// Whether space `s` has anything to send now.
    fn wants_send(&self, now: u64, s: usize) -> bool {
        let sp = &self.spaces[s];
        if sp.probes > 0 || sp.crypto_out.has_pending() {
            return true;
        }
        if sp.ack_owed && sp.recv.ack_pending() {
            if s != 2 || sp.recv.ack_now() || now >= sp.recv.largest_time().saturating_add(self.cfg.max_ack_delay_ms * 1000) {
                return true;
            }
        }
        if s == 2 {
            if self.send_handshake_done || self.send_max_data || self.send_max_streams[0] || self.send_max_streams[1] || self.path_response.is_some() {
                return true;
            }
            if !self.sendq.is_empty() {
                let inflight: u64 = self.spaces.iter().map(|s| s.sent.bytes_in_flight()).sum();
                return self.cc.can_send(inflight, 1);
            }
        }
        false
    }

    /// Writes the header and frames of a packet in space `s` (unsealed).
    fn build_packet(&mut self, now: u64, s: usize, buf: &mut Vec<u8>, room: usize, cwnd_room: usize) -> Option<Pending> {
        let hdr_start = buf.len();
        let pn = self.spaces[s].sent.next_pn();
        let pn_len = packet::pn_len(pn, self.spaces[s].sent.largest_acked());
        // Header.
        let mut len_pos = None;
        if s < 2 {
            let ty = if s == 0 { 0 } else { 2 };
            buf.push(0xc0 | (ty << 4) | (pn_len as u8 - 1));
            buf.extend_from_slice(&1u32.to_be_bytes());
            buf.push(self.remote_cid.len() as u8);
            buf.extend_from_slice(&self.remote_cid);
            buf.push(CID_LEN as u8);
            buf.extend_from_slice(&self.local_cid);
            if s == 0 {
                buf.push(0); // token length
            }
            len_pos = Some(buf.len());
            buf.extend_from_slice(&[0x40, 0]);
        } else {
            buf.push(0x40 | if self.kp.phase() { 0x04 } else { 0 } | (pn_len as u8 - 1));
            buf.extend_from_slice(&self.remote_cid);
        }
        let pn_off = buf.len();
        buf.extend_from_slice(&pn.to_be_bytes()[8 - pn_len..]);
        let payload_start = buf.len();
        // The payload may use what is left, less the tag; ack-eliciting
        // frames also only what congestion control allows (§7), unless
        // probing (verified `packet_ends`).
        let probing = self.spaces[s].probes > 0;
        let Some((end, end_e)) = pktbuf::packet_ends(hdr_start, room, cwnd_room, probing, 16) else {
            buf.truncate(hdr_start);
            return None;
        };
        if end <= payload_start + 4 {
            buf.truncate(hdr_start);
            return None;
        }
        let rec_start = self.spaces[s].rec_index();
        let mut nrec = 0usize;
        let mut eliciting = false;
        // Congestion control limits ack-eliciting packets (§7): a full
        // window leaves room only for ACKs.
        let may_elicit = probing || cwnd_room >= 100;
        // ACK.
        if self.spaces[s].ack_owed && self.spaces[s].recv.largest().is_some() {
            if self.write_ack(now, s, buf, end) {
                self.spaces[s].recs.push(Rec::Ack);
                nrec += 1;
                self.spaces[s].ack_owed = false;
                self.spaces[s].recv.on_ack_sent();
            }
        }
        if may_elicit {
            // HANDSHAKE_DONE and flow control.
            if s == 2 {
                if self.send_handshake_done && put_frame(buf, end_e, 0x1e, &[], 0) {
                    self.send_handshake_done = false;
                    self.spaces[2].recs.push(Rec::HandshakeDone);
                    nrec += 1;
                    eliciting = true;
                }
                if let Some(d) = self.path_response {
                    if put_frame(buf, end_e, 0x1b, &[], 8) {
                        buf.extend_from_slice(&d);
                        self.path_response = None;
                        self.spaces[2].recs.push(Rec::Ping);
                        nrec += 1;
                        eliciting = true;
                    }
                }
                if self.send_max_data && put_frame(buf, end_e, 0x10, &[self.rx_advertised], 0) {
                    self.send_max_data = false;
                    self.spaces[2].recs.push(Rec::MaxData);
                    nrec += 1;
                    eliciting = true;
                }
                for k in 0..2 {
                    if self.send_max_streams[k]
                        && put_frame(buf, end_e, if k == 0 { 0x12 } else { 0x13 }, &[self.streams_allowed[k]], 0)
                    {
                        self.send_max_streams[k] = false;
                        self.spaces[2].recs.push(Rec::MaxStreams { bidi: k == 0 });
                        nrec += 1;
                        eliciting = true;
                    }
                }
            }
            // CRYPTO.
            while nrec < MAX_FRAMES - 1 {
                let avail = end_e.saturating_sub(buf.len());
                let sp = &self.spaces[s];
                let Some((off, n0, _)) = sp.crypto_out.next(avail.saturating_sub(1 + 8 + 2), u64::MAX) else { break };
                let hl = 1 + vlen(off) + vlen(n0 as u64);
                if avail < hl + 1 {
                    break;
                }
                let n = n0.min(avail - hl);
                if n == 0 || !put_frame(buf, end_e, 0x06, &[off, n as u64], n) {
                    break;
                }
                sp.crypto_out.get(off, n, buf);
                let sp = &mut self.spaces[s];
                sp.crypto_out.sent(off, n, false);
                sp.recs.push(Rec::Crypto { off, len: n as u32 });
                nrec += 1;
                eliciting = true;
            }
            // Streams.
            if s == 2 {
                self.write_streams(buf, end_e, &mut nrec, &mut eliciting);
            }
        }
        // A probe with nothing to send: PING (§6.2.4).
        if self.spaces[s].probes > 0 {
            if !eliciting && put_frame(buf, end, 0x01, &[], 0) {
                self.spaces[s].recs.push(Rec::Ping);
                nrec += 1;
                eliciting = true;
            }
            self.spaces[s].probes -= 1;
        }
        if nrec == 0 {
            buf.truncate(hdr_start);
            return None;
        }
        // Room for the header protection sample (§5.4.2 of RFC 9001).
        while buf.len() - pn_off < 4 {
            buf.push(0);
        }
        Some(Pending { s, pn, hdr_start, pn_off, payload_start, len_pos, token: reclog::pack(rec_start, nrec as u64), eliciting })
    }

    fn write_ack(&mut self, now: u64, s: usize, buf: &mut Vec<u8>, end: usize) -> bool {
        let mut gaps = Vec::new();
        let sp = &self.spaces[s];
        let (largest, first) = sp.recv.ack_fields(32, &mut gaps);
        let delay = if s == 2 { now.saturating_sub(sp.recv.largest_time()) >> 3 } else { 0 };
        let mut need = 1 + vlen(largest) + vlen(delay) + vlen(gaps.len() as u64) + vlen(first);
        let mut k = 0;
        while k < gaps.len() {
            let (g, l) = gaps[k];
            if buf.len() + need + vlen(g) + vlen(l) > end {
                break;
            }
            need += vlen(g) + vlen(l);
            k += 1;
        }
        if buf.len() + need > end {
            return false;
        }
        let mut f = [0u64; 4 + 2 * 32];
        f[..4].copy_from_slice(&[largest, delay, k as u64, first]);
        for (j, &(g, l)) in gaps[..k.min(32)].iter().enumerate() {
            f[4 + 2 * j] = g;
            f[5 + 2 * j] = l;
        }
        put_frame(buf, end, 0x02, &f[..4 + 2 * k.min(32)], 0)
    }

    fn write_streams(&mut self, buf: &mut Vec<u8>, end: usize, nrec: &mut usize, eliciting: &mut bool) {
        let mut tries = self.sendq.len();
        while tries > 0 && *nrec < MAX_FRAMES - 4 && end - buf.len() > 24 {
            tries -= 1;
            let Some(id) = self.sendq.pop_front() else { break };
            self.queued.remove(&id);
            let Some(st) = self.streams.get_mut(&id) else { continue };
            let mut again = false;
            // Receive-side control frames.
            if let Some(r) = &mut st.recv {
                if let Some((code, false)) = r.stop {
                    if put_frame(buf, end, 0x05, &[id, code], 0) {
                        r.stop = Some((code, true));
                        self.spaces[2].recs.push(Rec::Stop { id });
                        *nrec += 1;
                        *eliciting = true;
                    } else {
                        again = true;
                    }
                }
                if r.send_max && put_frame(buf, end, 0x11, &[id, r.advertised], 0) {
                    r.send_max = false;
                    self.spaces[2].recs.push(Rec::MaxStreamData { id });
                    *nrec += 1;
                    *eliciting = true;
                }
            }
            if let Some(snd) = &mut st.send {
                if let Some((code, fs, false)) = snd.reset {
                    if put_frame(buf, end, 0x04, &[id, code, fs], 0) {
                        snd.reset = Some((code, fs, true));
                        self.spaces[2].recs.push(Rec::Reset { id });
                        *nrec += 1;
                        *eliciting = true;
                    } else {
                        again = true;
                    }
                } else if snd.reset.is_none() {
                    // Data: lost ranges first, then new data within both
                    // flow control limits.
                    let avail = end - buf.len();
                    let hmax = 1 + vlen(id) + 8 + 2;
                    if avail > hmax {
                        let new_room = snd.st.available(&self.tx_credit);
                        let limit = snd.buf.end().min(snd.sent_new + new_room);
                        if let Some((off, n0, _)) = snd.buf.next(avail - hmax, limit) {
                            let hl = 1 + vlen(id) + if off > 0 { vlen(off) } else { 0 } + vlen(n0 as u64);
                            let n = n0.min(avail - hl);
                            let fin = snd.buf.fin() && off + n as u64 == snd.buf.end();
                            let new = (off + n as u64).saturating_sub(snd.sent_new);
                            let ty = 0x08 | if off > 0 { 0x04 } else { 0 } | 0x02 | if fin { 1 } else { 0 };
                            let f = [id, off, n as u64];
                            let f = if off > 0 { &f[..] } else { &[id, n as u64][..] };
                            if (new > 0 || n > 0 || fin) && put_frame(buf, end, ty, f, n) {
                                snd.buf.get(off, n, buf);
                                snd.buf.sent(off, n, fin);
                                let state = snd.st.get_state();
                                if (new > 0 || fin) && (state == SendState::Ready || state == SendState::Send) {
                                    snd.st.send(&mut self.tx_credit, new, fin && off + n as u64 == snd.buf.end());
                                    snd.sent_new += new;
                                }
                                self.spaces[2].recs.push(Rec::Stream { id, off, len: n as u32, fin });
                                *nrec += 1;
                                *eliciting = true;
                            }
                        }
                    }
                    if snd.buf.has_pending() {
                        let blocked = snd.buf.next(1500, snd.sent_new + snd.st.available(&self.tx_credit)).is_none();
                        if !blocked {
                            again = true;
                        }
                    }
                }
            }
            if again {
                queue!(self, id);
            }
        }
    }

    /// Seals the pending packet, after `pad` bytes of PADDING, and records
    /// it as sent.
    fn seal(&mut self, now: u64, buf: &mut Vec<u8>, p: Pending, pad: usize) {
        buf.resize(buf.len() + pad, 0);
        let payload_len = buf.len() - p.pn_off + 16;
        if let Some(lp) = p.len_pos {
            let v = 0x4000u16 | payload_len as u16;
            buf[lp..lp + 2].copy_from_slice(&v.to_be_bytes());
        }
        let size = buf.len() - p.hdr_start + 16;
        let sp = &mut self.spaces[p.s];
        let (aead, hp) = sp.tx.as_ref().expect("keys");
        aead.seal(hp, p.pn, buf, p.hdr_start, p.pn_off, p.payload_start);
        let in_flight = p.eliciting || pad > 0;
        let r = sp.sent.on_sent(now, size as u32, p.eliciting, in_flight, p.token);
        trace(format_args!("tx s{} pn{} size{} el{} t{}", p.s, p.pn, size, p.eliciting, now));
        debug_assert_eq!(r, Some(p.pn));
    }

    fn build_close(&mut self, now: u64, buf: &mut Vec<u8>, room: usize) -> usize {
        let start = buf.len();
        let Some((code, app)) = self.close else { return 0 };
        for s in 0..3 {
            if !self.ks.may_send(s) || self.spaces[s].tx.is_none() {
                continue;
            }
            if s == 2 && !self.ks.complete() {
                continue;
            }
            if room - (buf.len() - start) < 80 {
                break;
            }
            let hdr_start = buf.len();
            let pn = self.spaces[s].sent.next_pn();
            let pn_len = packet::pn_len(pn, self.spaces[s].sent.largest_acked());
            let mut len_pos = None;
            if s < 2 {
                let ty = if s == 0 { 0 } else { 2 };
                buf.push(0xc0 | (ty << 4) | (pn_len as u8 - 1));
                buf.extend_from_slice(&1u32.to_be_bytes());
                buf.push(self.remote_cid.len() as u8);
                buf.extend_from_slice(&self.remote_cid);
                buf.push(CID_LEN as u8);
                buf.extend_from_slice(&self.local_cid);
                if s == 0 {
                    buf.push(0);
                }
                len_pos = Some(buf.len());
                buf.extend_from_slice(&[0x40, 0]);
            } else {
                buf.push(0x40 | if self.kp.phase() { 0x04 } else { 0 } | (pn_len as u8 - 1));
                buf.extend_from_slice(&self.remote_cid);
            }
            let pn_off = buf.len();
            buf.extend_from_slice(&pn.to_be_bytes()[8 - pn_len..]);
            let payload_start = buf.len();
            // §10.2.3: an application close outside 1-RTT becomes
            // APPLICATION_ERROR.
            // The frame, with an empty reason phrase, before the tag.
            let end = start + room - 16;
            let ok = if app && s == 2 {
                put_frame(buf, end, 0x1d, &[code, 0], 0)
            } else {
                put_frame(buf, end, 0x1c, &[if app { APPLICATION_ERROR } else { code }, 0, 0], 0)
            };
            if !ok {
                buf.truncate(hdr_start);
                break;
            }
            let rec_start = self.spaces[s].rec_index();
            self.spaces[s].recs.push(Rec::Close);
            while buf.len() - pn_off < 4 {
                buf.push(0);
            }
            let p = Pending { s, pn, hdr_start, pn_off, payload_start, len_pos, token: reclog::pack(rec_start, 1), eliciting: false };
            self.seal(now, buf, p, 0);
        }
        let n = buf.len() - start;
        self.budget.on_sent(n as u64);
        n
    }
}

/// A packet written but not yet sealed.
struct Pending {
    s: usize,
    pn: u64,
    hdr_start: usize,
    pn_off: usize,
    payload_start: usize,
    len_pos: Option<usize>,
    token: u64,
    eliciting: bool,
}


/// Debug tracing to stderr, with `VQ_TRACE` set (read once).
fn trace(a: std::fmt::Arguments) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var_os("VQ_TRACE").is_some()) {
        eprintln!("{a}");
    }
}

/// The congestion controller, either verified one.
#[derive(Debug, Clone, Copy)]
enum Cc {
    Reno(NewReno),
    Cubic(Cubic),
}

impl Cc {
    fn mds(&self) -> u64 {
        match self {
            Cc::Reno(c) => c.mds,
            Cc::Cubic(c) => c.mds,
        }
    }

    fn cwnd(&self) -> u64 {
        match self {
            Cc::Reno(c) => c.cwnd,
            Cc::Cubic(c) => c.cwnd,
        }
    }

    fn can_send(&self, in_flight: u64, size: u64) -> bool {
        match self {
            Cc::Reno(c) => c.can_send(in_flight, size),
            Cc::Cubic(c) => c.can_send(in_flight, size),
        }
    }

    fn room(&self, in_flight: u64) -> u64 {
        match self {
            Cc::Reno(c) => c.room(in_flight),
            Cc::Cubic(c) => c.room(in_flight),
        }
    }

    /// `size` is at most the max_datagram_size; `srtt` in microseconds.
    fn on_ack(&mut self, sent: u64, size: u64, now: u64, srtt: u64) {
        match self {
            Cc::Reno(c) => c.on_ack(sent, size, false),
            Cc::Cubic(c) => c.on_ack(sent, size, false, now, srtt.min(0xFFFF_FFFF)),
        }
    }

    fn on_congestion(&mut self, sent: u64, now: u64) {
        match self {
            Cc::Reno(c) => c.on_congestion(sent, now),
            Cc::Cubic(c) => c.on_congestion(sent, now),
        }
    }

    fn on_persistent(&mut self) {
        match self {
            Cc::Reno(c) => c.on_persistent(),
            Cc::Cubic(c) => c.on_persistent(),
        }
    }

    fn raise_mds(&mut self, mds: u64) {
        match self {
            Cc::Reno(c) => c.raise_mds(mds),
            Cc::Cubic(c) => c.raise_mds(mds),
        }
    }
}
