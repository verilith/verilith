//! HTTP/3 (RFC 9114), one QUIC endpoint per worker (DESIGN.md, "HTTP/3").
//!
//! QUIC itself (packets, TLS 1.3, loss recovery, congestion control) comes
//! from one of two sans-I/O backends, picked by the [`QuicConfig`]:
//!
//! - verilith-quic-conn, the default: its wire format, flow control,
//!   stream states, loss recovery and congestion control are
//!   verilith-quic's (verified), and its handshake and packet protection
//!   are verilith-tls's (verified), with aws-lc's cryptography. The
//!   connection logic joining them is plain Rust for now (that crate's
//!   README).
//! - quinn-proto with rustls, trusted (TRUST.md), kept to compare
//!   (`--h3-backend quinn`).
//!
//! Everything HTTP/3 is verified: each stream's bytes go through
//! verilith-h3's `Reader` (frame syntax and order, with the RFC's error
//! codes), field sections through verilith-qpack's decoder and encoder, and
//! frames are written by verilith-h3's encoders. This file connects them:
//! it accepts streams, dispatches requests to the handler like HTTP/2 does,
//! and writes the responses, over either backend through the [`Quic`]
//! trait. It is not verified; it is tested in `tests/h3.rs`, on both
//! backends.
//!
//! QPACK runs without a dynamic table in either direction (our SETTINGS
//! advertise capacity 0 and no blocked streams, and our encoder uses none),
//! so no section ever blocks and the QPACK streams carry nothing but what
//! the peer chooses to send on them.
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

type IdHasher = std::hash::BuildHasherDefault<crate::h2::IdHash>;
use std::hash::Hash;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};
use std::sync::Arc;
use std::time::{Duration, Instant};

use bytes::{Buf, Bytes, BytesMut};
use quinn_proto::{
    ConnectionHandle, DatagramEvent, Dir, Endpoint, EndpointConfig, ReadError, ServerConfig, StreamEvent, StreamId,
    TransportConfig, VarInt, WriteError,
};
use verilith_h3::consts::*;
use verilith_h3::{Event as Ev, Reader, Settings, Src, UniKind, UniSeen};
use verilith_http::Header;
use verilith_http::parse::Span;
use verilith_qpack::encoder::Encoder;
use verilith_qpack::{Decoder, Fields, Res};
use verilith_quic_conn as vq;
use verilith_tls_aws_lc::{AwsLc, SigningKey, GROUPS, SUITES};

use crate::h1::{Ctx, Out};
use crate::h2::{request_fields_ok, HList, Reply, ReplyBody};
use crate::sys;
use crate::{Handler, Request, Response};

const QPACK_DECOMPRESSION_FAILED: u64 = 0x200;
const QPACK_ENCODER_STREAM_ERROR: u64 = 0x201;
const QPACK_DECODER_STREAM_ERROR: u64 = 0x202;
const H3_INTERNAL_ERROR: u64 = 0x102;

/// Limits on one HTTP/3 connection.
#[derive(Clone, Copy, Debug)]
pub struct Limits3 {
    /// Concurrent request streams a client may open.
    pub max_streams: u32,
    /// Largest field section (SETTINGS_MAX_FIELD_SECTION_SIZE), and the
    /// largest HEADERS frame buffered.
    pub max_field_section: u64,
    /// Largest request body buffered for a handler.
    pub max_body: usize,
    /// Each stream's receive window, and the connection's (QUIC flow
    /// control).
    pub stream_window: u32,
    pub window: u32,
    /// Bytes QUIC may hold unacknowledged for one connection.
    pub send_window: u64,
    /// The largest UDP payload the verilith backend probes for: it starts
    /// at 1200, the minimum QUIC requires of paths (RFC 9000 §14), and
    /// moves up to this once a probe of this size is acknowledged. 1452
    /// fills a 1500-byte Ethernet MTU over IPv6, quinn's default upper
    /// bound too.
    pub max_udp_payload: u16,
}

impl Default for Limits3 {
    fn default() -> Self {
        Limits3 {
            max_streams: 256,
            max_field_section: 64 * 1024,
            max_body: 1 << 20,
            stream_window: 1 << 20,
            window: 8 << 20,
            send_window: 8 << 20,
            max_udp_payload: 1452,
        }
    }
}

/// Which QUIC implementation serves HTTP/3.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Backend {
    Quinn,
    #[default]
    Verilith,
}

/// A QUIC server configuration, for one backend.
#[derive(Clone)]
pub enum QuicConfig {
    Quinn(Arc<ServerConfig>),
    Verilith(Arc<vq::Config<AwsLc>>),
}

impl std::fmt::Debug for QuicConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            QuicConfig::Quinn(_) => "QuicConfig::Quinn",
            QuicConfig::Verilith(_) => "QuicConfig::Verilith",
        })
    }
}

/// The QUIC server configuration (TLS 1.3, ALPN `h3`) for this
/// certificate chain and key, PEM files (the key PKCS#8), on the default
/// backend (verilith-quic-conn).
pub fn server_config(cert: &str, key: &str, limits: Limits3) -> std::io::Result<QuicConfig> {
    server_config_on(Backend::default(), cert, key, limits)
}

/// [`server_config`], on `backend`.
pub fn server_config_on(backend: Backend, cert: &str, key: &str, limits: Limits3) -> std::io::Result<QuicConfig> {
    use rustls::pki_types::pem::PemObject;
    use rustls::pki_types::{CertificateDer, PrivateKeyDer};
    let e = |e: rustls::pki_types::pem::Error| std::io::Error::other(e.to_string());
    let certs = CertificateDer::pem_file_iter(cert).map_err(e)?.collect::<Result<Vec<_>, _>>().map_err(e)?;
    let key = PrivateKeyDer::from_pem_file(key).map_err(e)?;
    server_config_der_on(backend, certs, key, limits)
}

/// [`server_config`], from DER.
pub fn server_config_der(
    certs: Vec<rustls::pki_types::CertificateDer<'static>>,
    key: rustls::pki_types::PrivateKeyDer<'static>,
    limits: Limits3,
) -> std::io::Result<QuicConfig> {
    server_config_der_on(Backend::default(), certs, key, limits)
}

/// [`server_config_der`], on `backend`.
pub fn server_config_der_on(
    backend: Backend,
    certs: Vec<rustls::pki_types::CertificateDer<'static>>,
    key: rustls::pki_types::PrivateKeyDer<'static>,
    limits: Limits3,
) -> std::io::Result<QuicConfig> {
    match backend {
        Backend::Quinn => quinn_config(certs, key, limits),
        Backend::Verilith => verilith_config(certs, key, limits),
    }
}

fn quinn_config(
    certs: Vec<rustls::pki_types::CertificateDer<'static>>,
    key: rustls::pki_types::PrivateKeyDer<'static>,
    limits: Limits3,
) -> std::io::Result<QuicConfig> {
    let o = |e: &dyn std::fmt::Display| std::io::Error::other(e.to_string());
    let mut c = rustls::ServerConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .map_err(|e| o(&e))?
        .with_no_client_auth()
        .with_single_cert(certs, key)
        .map_err(|e| o(&e))?;
    c.alpn_protocols = vec![b"h3".to_vec()];
    c.send_tls13_tickets = 2;
    c.ticketer = rustls::crypto::aws_lc_rs::Ticketer::new().map_err(|e| o(&e))?;
    let q = quinn_proto::crypto::rustls::QuicServerConfig::try_from(c).map_err(|e| o(&e))?;
    let mut s = ServerConfig::with_crypto(Arc::new(q));
    let mut t = TransportConfig::default();
    t.max_concurrent_bidi_streams(VarInt::from_u32(limits.max_streams))
        // Control, QPACK encoder and decoder, and a few the peer may add.
        .max_concurrent_uni_streams(VarInt::from_u32(8))
        .stream_receive_window(VarInt::from_u32(limits.stream_window))
        .receive_window(VarInt::from_u32(limits.window))
        .send_window(limits.send_window)
        .max_idle_timeout(Some(VarInt::from_u32(30_000).into()))
        // Datagrams are not used (no SETTINGS_H3_DATAGRAM).
        .datagram_receive_buffer_size(None);
    s.transport_config(Arc::new(t));
    Ok(QuicConfig::Quinn(Arc::new(s)))
}

fn verilith_config(
    certs: Vec<rustls::pki_types::CertificateDer<'static>>,
    key: rustls::pki_types::PrivateKeyDer<'static>,
    limits: Limits3,
) -> std::io::Result<QuicConfig> {
    let bad = |m: &str| std::io::Error::new(std::io::ErrorKind::InvalidInput, m.to_string());
    let rustls::pki_types::PrivateKeyDer::Pkcs8(k) = key else { return Err(bad("the key is not PKCS#8")) };
    let key = SigningKey::from_pkcs8(k.secret_pkcs8_der()).ok_or_else(|| bad("the key is not PKCS#8 ECDSA, Ed25519 or RSA"))?;
    let chain: Vec<Vec<u8>> = certs.iter().map(|c| c.to_vec()).collect();
    let tls = verilith_tls::server::Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(), b"\x02h3".to_vec(), &chain)
        .ok_or_else(|| bad("the certificate chain is empty or too long"))?;
    let key = Arc::new(key);
    let mut c = vq::Config::new(Arc::new(tls), Arc::new(move || AwsLc::shared(key.clone())));
    c.idle_timeout_ms = 30_000;
    c.max_data = u64::from(limits.window);
    c.stream_window = u64::from(limits.stream_window);
    c.max_streams_bidi = u64::from(limits.max_streams);
    c.max_streams_uni = 8;
    c.send_buffer = limits.send_window as usize;
    c.max_datagram = 1200;
    c.probe_datagram = usize::from(limits.max_udp_payload);
    Ok(QuicConfig::Verilith(Arc::new(c)))
}

// ---------------------------------------------------------------------
// What HTTP/3 needs from a QUIC connection.

/// An application event, the same for both backends.
enum QEv<Id> {
    Opened { bidi: bool },
    Readable(Id),
    Writable(Id),
    Stopped(Id),
    Other,
}

/// How a read ended, after appending what was readable.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Read {
    /// More may come.
    Open,
    /// The stream's end was reached.
    Fin,
    /// The peer reset the stream.
    Reset,
    /// No such stream to read (unknown, or already read to its end).
    Gone,
}

/// A QUIC connection's streams, as the HTTP/3 code uses them.
trait Quic {
    type Id: Copy + Eq + Hash + Into<u64>;
    fn next_event(&mut self) -> Option<QEv<Self::Id>>;
    fn accept(&mut self, bidi: bool) -> Option<Self::Id>;
    fn open_uni(&mut self) -> Option<Self::Id>;
    /// Appends what stream `id` has to `out`.
    fn read(&mut self, id: Self::Id, out: &mut Vec<u8>) -> Read;
    /// Writes as much of `out` as the stream takes, consuming it from the
    /// front: `Ok((chunks fully written, bytes))`, or `Err(true)` when
    /// blocked with nothing taken, `Err(false)` when the stream is gone.
    fn write(&mut self, id: Self::Id, out: &mut [Bytes]) -> Result<(usize, usize), bool>;
    fn finish(&mut self, id: Self::Id);
    fn reset(&mut self, id: Self::Id, code: u64);
    fn stop(&mut self, id: Self::Id, code: u64);
    fn handshaking(&self) -> bool;
}

fn is_bidi(id: u64) -> bool {
    id & 2 == 0
}

impl Quic for quinn_proto::Connection {
    type Id = StreamId;

    fn next_event(&mut self) -> Option<QEv<StreamId>> {
        Some(match self.poll()? {
            quinn_proto::Event::Stream(StreamEvent::Opened { dir }) => QEv::Opened { bidi: dir == Dir::Bi },
            quinn_proto::Event::Stream(StreamEvent::Readable { id }) => QEv::Readable(id),
            quinn_proto::Event::Stream(StreamEvent::Writable { id }) => QEv::Writable(id),
            quinn_proto::Event::Stream(StreamEvent::Stopped { id, .. }) => QEv::Stopped(id),
            _ => QEv::Other,
        })
    }

    fn accept(&mut self, bidi: bool) -> Option<StreamId> {
        self.streams().accept(if bidi { Dir::Bi } else { Dir::Uni })
    }

    fn open_uni(&mut self) -> Option<StreamId> {
        self.streams().open(Dir::Uni)
    }

    fn read(&mut self, id: StreamId, out: &mut Vec<u8>) -> Read {
        let mut rs = self.recv_stream(id);
        let Ok(mut chunks) = rs.read(true) else { return Read::Gone };
        let r = loop {
            match chunks.next(usize::MAX) {
                Ok(Some(ch)) => out.extend_from_slice(&ch.bytes),
                Ok(None) => break Read::Fin,
                Err(ReadError::Blocked) => break Read::Open,
                Err(ReadError::Reset(_)) => break Read::Reset,
            }
        };
        let _ = chunks.finalize();
        r
    }

    fn write(&mut self, id: StreamId, out: &mut [Bytes]) -> Result<(usize, usize), bool> {
        match self.send_stream(id).write_chunks(out) {
            Ok(w) => Ok((w.chunks, w.bytes)),
            Err(WriteError::Blocked) => Err(true),
            Err(_) => Err(false),
        }
    }

    fn finish(&mut self, id: StreamId) {
        let _ = self.send_stream(id).finish();
    }

    fn reset(&mut self, id: StreamId, code: u64) {
        let _ = self.send_stream(id).reset(VarInt::from_u64(code).unwrap_or(VarInt::from_u32(0)));
    }

    fn stop(&mut self, id: StreamId, code: u64) {
        let _ = self.recv_stream(id).stop(VarInt::from_u64(code).unwrap_or(VarInt::from_u32(0)));
    }

    fn handshaking(&self) -> bool {
        self.is_handshaking()
    }
}

impl Quic for vq::Connection<AwsLc> {
    type Id = u64;

    fn next_event(&mut self) -> Option<QEv<u64>> {
        Some(match self.poll()? {
            vq::Event::Opened { bidi } => QEv::Opened { bidi },
            vq::Event::Readable(id) => QEv::Readable(id),
            vq::Event::Writable(id) => QEv::Writable(id),
            vq::Event::Stopped { id, .. } => QEv::Stopped(id),
            _ => QEv::Other,
        })
    }

    fn accept(&mut self, bidi: bool) -> Option<u64> {
        vq::Connection::accept(self, bidi)
    }

    fn open_uni(&mut self) -> Option<u64> {
        self.open(false)
    }

    fn read(&mut self, id: u64, out: &mut Vec<u8>) -> Read {
        let mut any = false;
        loop {
            match vq::Connection::read(self, id, out, usize::MAX) {
                Ok((_, true)) => return Read::Fin,
                Ok(_) => any = true,
                Err(vq::StreamError::Blocked) => return Read::Open,
                Err(vq::StreamError::Reset(_)) => return Read::Reset,
                Err(_) => return if any { Read::Open } else { Read::Gone },
            }
        }
    }

    fn write(&mut self, id: u64, out: &mut [Bytes]) -> Result<(usize, usize), bool> {
        let (mut chunks, mut bytes) = (0, 0);
        for b in out.iter_mut() {
            // Shared, not copied, when large: the response body.
            match vq::Connection::write_bytes(self, id, b) {
                Ok(n) => {
                    bytes += n;
                    if n < b.len() {
                        b.advance(n);
                        break;
                    }
                    *b = Bytes::new();
                    chunks += 1;
                }
                Err(vq::StreamError::Blocked) if bytes == 0 => return Err(true),
                Err(vq::StreamError::Blocked) => break,
                Err(_) => return Err(false),
            }
        }
        Ok((chunks, bytes))
    }

    fn finish(&mut self, id: u64) {
        let _ = vq::Connection::finish(self, id);
    }

    fn reset(&mut self, id: u64, code: u64) {
        let _ = vq::Connection::reset(self, id, code);
    }

    fn stop(&mut self, id: u64, code: u64) {
        let _ = vq::Connection::stop(self, id, code);
    }

    fn handshaking(&self) -> bool {
        self.is_handshaking()
    }
}

// ---------------------------------------------------------------------
// HTTP/3 state.

/// A request stream.
struct Req {
    r: Reader,
    /// The decoded field section, as spans into `arena`.
    arena: Vec<u8>,
    fields: Vec<Header>,
    body: Vec<u8>,
    got_headers: bool,
    /// The body went over the limit: answer 413 once it ends.
    too_big: bool,
    reply: Option<Reply>,
    /// The response's frames, not yet all taken by QUIC: the HEADERS frame
    /// and DATA frame header, then the body.
    out: [Bytes; 2],
    /// `out[..next]` is written.
    next: usize,
    /// The response is complete in `out` (the stream is finished once it
    /// is all written).
    answered: bool,
}

impl Req {
    fn new(limits: &Limits3) -> Box<Req> {
        Box::new(Req {
            r: Reader::new_request(true, limits.max_field_section),
            arena: Vec::new(),
            fields: Vec::new(),
            body: Vec::new(),
            got_headers: false,
            too_big: false,
            reply: None,
            out: [Bytes::new(), Bytes::new()],
            next: 0,
            answered: false,
        })
    }

    fn reset(&mut self, limits: &Limits3) {
        self.r = Reader::new_request(true, limits.max_field_section);
        self.arena.clear();
        self.fields.clear();
        self.body.clear();
        self.got_headers = false;
        self.too_big = false;
        self.out = [Bytes::new(), Bytes::new()];
        self.next = 0;
        self.answered = false;
    }
}

/// A unidirectional stream the peer opened.
struct Uni {
    r: Reader,
    kind: Option<UniKind>,
    /// Past the stream type of a QPACK or unknown stream: the bytes are
    /// QPACK instructions (or discarded).
    raw: bool,
}

/// One connection's HTTP/3 state.
struct App<Id> {
    dec: Decoder,
    enc: Encoder,
    seen: UniSeen,
    /// Our control stream, once opened.
    ctrl: Option<Id>,
    /// Keyed by stream ID with h2's multiply-and-fold hash: SipHash
    /// cost 2% of the CPU in h3-plaintext.
    uni: HashMap<Id, Uni, IdHasher>,
    reqs: HashMap<Id, Box<Req>, IdHasher>,
    pool: Vec<Box<Req>>,
    /// Scratch for decoded field lines.
    lines: Fields,
    /// Scratch for one encoded field section.
    section: Vec<u8>,
    /// Scratch for a stream's bytes.
    input: Vec<u8>,
    /// The highest request stream accepted, for GOAWAY.
    requests: u64,
}

impl<Id> App<Id> {
    fn new(limits: &Limits3) -> App<Id> {
        App {
            dec: Decoder::new(0, 0, limits.max_field_section).expect("QPACK decoder"),
            enc: Encoder::new(0, 0, 0).expect("QPACK encoder"),
            seen: UniSeen { control: false, encoder: false, decoder: false },
            ctrl: None,
            uni: HashMap::default(),
            reqs: HashMap::default(),
            pool: Vec::new(),
            lines: Fields::new(),
            section: Vec::new(),
            input: Vec::new(),
            requests: 0,
        }
    }
}

/// A connection error: the connection is closed with this code.
struct Close(u64);

// ---------------------------------------------------------------------
// The endpoint.

/// One worker's HTTP/3 endpoint: a UDP socket, a QUIC endpoint and the
/// connections on it.
pub struct H3 {
    pub(crate) fd: i32,
    back: Back,
    timers: BinaryHeap<Reverse<(Instant, usize)>>,
    limits: Limits3,
    /// Datagrams are received into the spare capacity of this buffer and
    /// split off it, so quinn holds them without a copy.
    rbuf: BytesMut,
    sbuf: Vec<u8>,
    dirty: Vec<usize>,
    gso: bool,
}

enum Back {
    Quinn { endpoint: Endpoint, conns: Vec<Option<Box<QConn>>> },
    Verilith { server: vq::Server<AwsLc, VConn>, epoch: Instant },
}

struct QConn {
    q: quinn_proto::Connection,
    app: App<StreamId>,
    /// The timer last scheduled for this connection.
    deadline: Option<Instant>,
}

struct VConn {
    app: App<u64>,
    /// Where the connection's first datagram came from: replies go there
    /// (no migration).
    peer: SocketAddrV4,
    deadline: Option<Instant>,
}

/// Datagrams per `sendmsg` with segmentation offload.
const BATCH: usize = 16;
const RECV_ROOM: usize = 64 * 1024;

impl H3 {
    pub fn new(fd: i32, cfg: QuicConfig, limits: Limits3) -> H3 {
        let back = match cfg {
            QuicConfig::Quinn(cfg) => {
                Back::Quinn { endpoint: Endpoint::new(Arc::new(EndpointConfig::default()), Some(cfg), true, None), conns: Vec::new() }
            }
            QuicConfig::Verilith(cfg) => Back::Verilith { server: vq::Server::new(cfg), epoch: Instant::now() },
        };
        H3 {
            fd,
            back,
            timers: BinaryHeap::new(),
            limits,
            rbuf: BytesMut::new(),
            sbuf: Vec::with_capacity(BATCH * 1500),
            dirty: Vec::new(),
            gso: sys::UDP_SEGMENT.is_some(),
        }
    }

    fn deadline(&mut self, ch: usize) -> Option<Instant> {
        match &mut self.back {
            Back::Quinn { conns, .. } => conns.get(ch)?.as_ref()?.deadline,
            Back::Verilith { server, .. } => server.get(ch)?.1.deadline,
        }
    }

    /// Milliseconds to the next timer, if any.
    pub fn timeout_ms(&mut self, now: Instant) -> Option<i32> {
        while let Some(Reverse((t, ch))) = self.timers.peek().copied() {
            if self.deadline(ch) != Some(t) {
                self.timers.pop();
                continue;
            }
            let d = t.saturating_duration_since(now);
            // Round up: waking early only to sleep again costs a poll.
            return Some(d.as_millis().min(1000) as i32 + (d.subsec_nanos() % 1_000_000 != 0) as i32);
        }
        None
    }

    /// Runs the timers that are due.
    pub fn on_timers<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) {
        let now = Instant::now();
        while let Some(Reverse((t, ch))) = self.timers.peek().copied() {
            if t > now {
                break;
            }
            self.timers.pop();
            if self.deadline(ch) != Some(t) {
                continue;
            }
            match &mut self.back {
                Back::Quinn { conns, .. } => {
                    if let Some(Some(c)) = conns.get_mut(ch) {
                        c.deadline = None;
                        c.q.handle_timeout(now);
                    }
                }
                Back::Verilith { server, epoch } => {
                    let us = micros(*epoch, now);
                    if let Some((q, c)) = server.get(ch) {
                        c.deadline = None;
                        q.handle_timeout(us);
                    }
                }
            }
            self.dirty.push(ch);
        }
        self.drive_dirty(h, ctx, now);
    }

    /// Reads every datagram waiting on the socket, then drives the
    /// connections they were for.
    pub fn on_readable<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) {
        let now = Instant::now();
        loop {
            if self.rbuf.capacity() - self.rbuf.len() < RECV_ROOM {
                self.rbuf = BytesMut::with_capacity(16 * RECV_ROOM);
            }
            let Some((n, ip, port, seg)) = sys::recv_gro(self.fd, &mut self.rbuf.spare_capacity_mut()[..RECV_ROOM]) else {
                break;
            };
            // SAFETY: recv_gro initialized the first `n` bytes.
            unsafe { self.rbuf.set_len(n) };
            let mut all = self.rbuf.split_to(n);
            let remote = SocketAddrV4::new(Ipv4Addr::from(ip), port);
            while !all.is_empty() {
                let data = all.split_to(seg.min(all.len()));
                self.on_datagram(now, remote, data);
            }
        }
        self.drive_dirty(h, ctx, now);
    }

    fn on_datagram(&mut self, now: Instant, remote: SocketAddrV4, mut data: BytesMut) {
        self.sbuf.clear();
        match &mut self.back {
            Back::Quinn { endpoint, conns } => match endpoint.handle(now, SocketAddr::V4(remote), None, None, data, &mut self.sbuf) {
                Some(DatagramEvent::NewConnection(incoming)) => {
                    self.sbuf.clear();
                    match endpoint.accept(incoming, now, &mut self.sbuf, None) {
                        Ok((ch, q)) => {
                            let i = ch.0;
                            if conns.len() <= i {
                                conns.resize_with(i + 1, || None);
                            }
                            conns[i] = Some(Box::new(QConn { q, app: App::new(&self.limits), deadline: None }));
                            self.dirty.push(i);
                        }
                        Err(e) => {
                            if let Some(t) = e.response {
                                send(self.fd, &self.sbuf[..t.size], t.destination, t.segment_size, &mut self.gso);
                            }
                        }
                    }
                }
                Some(DatagramEvent::ConnectionEvent(ch, ev)) => {
                    if let Some(Some(c)) = conns.get_mut(ch.0) {
                        c.q.handle_event(ev);
                        self.dirty.push(ch.0);
                    }
                }
                Some(DatagramEvent::Response(t)) => {
                    send(self.fd, &self.sbuf[..t.size], t.destination, t.segment_size, &mut self.gso)
                }
                None => {}
            },
            Back::Verilith { server, epoch } => {
                let limits = &self.limits;
                let make = || VConn { app: App::new(limits), peer: remote, deadline: None };
                match server.handle_with(micros(*epoch, now), &mut data, &mut self.sbuf, make) {
                    vq::Datagram::Conn(i) => self.dirty.push(i),
                    vq::Datagram::Response(n) => {
                        send(self.fd, &self.sbuf[..n], SocketAddr::V4(remote), None, &mut self.gso)
                    }
                    vq::Datagram::Dropped => {}
                }
            }
        }
    }

    fn drive_dirty<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx, now: Instant) {
        let mut dirty = std::mem::take(&mut self.dirty);
        dirty.sort_unstable();
        dirty.dedup();
        for &ch in &dirty {
            self.drive(ch, h, ctx, now);
        }
        dirty.clear();
        self.dirty = dirty;
    }

    /// Everything a connection has to do after its state changed: the
    /// application events, the packets to send, and its timer (and for
    /// quinn, its endpoint events).
    fn drive<H: Handler + ?Sized>(&mut self, ch: usize, h: &H, ctx: &Ctx, now: Instant) {
        let limits = self.limits;
        let max = if self.gso { BATCH } else { 1 };
        let deadline = match &mut self.back {
            Back::Quinn { endpoint, conns } => {
                let Some(Some(c)) = conns.get_mut(ch) else { return };
                if exchange(endpoint, ch, &mut c.q) {
                    conns[ch] = None;
                    return;
                }
                if let Err(Close(code)) = app_events(&mut c.q, &mut c.app, h, ctx, &limits) {
                    c.q.close(now, VarInt::from_u64(code).unwrap_or(VarInt::from_u32(0x101)), Bytes::new());
                }
                loop {
                    self.sbuf.clear();
                    let Some(t) = c.q.poll_transmit(now, max, &mut self.sbuf) else { break };
                    send(self.fd, &self.sbuf[..t.size], t.destination, t.segment_size, &mut self.gso);
                }
                if exchange(endpoint, ch, &mut c.q) {
                    conns[ch] = None;
                    return;
                }
                let d = c.q.poll_timeout();
                if d == c.deadline {
                    return;
                }
                c.deadline = d;
                d
            }
            Back::Verilith { server, epoch } => {
                let us = micros(*epoch, now);
                let Some((q, c)) = server.get(ch) else { return };
                if let Err(Close(code)) = app_events(q, &mut c.app, h, ctx, &limits) {
                    q.close(us, code);
                }
                loop {
                    self.sbuf.clear();
                    let Some(t) = q.poll_transmit(us, max, &mut self.sbuf) else { break };
                    send(self.fd, &self.sbuf[..t.size], SocketAddr::V4(c.peer), t.segment_size, &mut self.gso);
                }
                if q.is_closed() {
                    server.reap(ch);
                    return;
                }
                let d = q.poll_timeout().map(|t| *epoch + Duration::from_micros(t));
                if d == c.deadline {
                    return;
                }
                c.deadline = d;
                d
            }
        };
        if let Some(t) = deadline {
            self.timers.push(Reverse((t, ch)));
        }
    }
}

fn micros(epoch: Instant, now: Instant) -> u64 {
    now.saturating_duration_since(epoch).as_micros() as u64
}

fn send(fd: i32, buf: &[u8], to: SocketAddr, segment: Option<usize>, gso: &mut bool) {
    let SocketAddr::V4(d) = to else { return };
    sys::send_to(fd, buf, d.ip().octets(), d.port(), segment.unwrap_or(buf.len()), gso);
}

/// Passes events between a quinn connection and its endpoint. True once
/// the connection is drained (gone).
fn exchange(endpoint: &mut Endpoint, ch: usize, q: &mut quinn_proto::Connection) -> bool {
    while let Some(ev) = q.poll_endpoint_events() {
        let drained = ev.is_drained();
        if let Some(back) = endpoint.handle_event(ConnectionHandle(ch), ev) {
            q.handle_event(back);
        }
        if drained {
            return true;
        }
    }
    false
}

// ---------------------------------------------------------------------
// HTTP/3 over a connection.

/// Handles a connection's application events; opens our control stream
/// once the handshake is done.
fn app_events<Q: Quic, H: Handler + ?Sized>(q: &mut Q, c: &mut App<Q::Id>, h: &H, ctx: &Ctx, limits: &Limits3) -> Result<(), Close> {
    while let Some(ev) = q.next_event() {
        match ev {
            QEv::Opened { bidi: true } => accept_requests(q, c, h, ctx, limits)?,
            QEv::Opened { bidi: false } => accept_uni(q, c, limits)?,
            QEv::Readable(id) => {
                if is_bidi(id.into()) {
                    read_request(q, c, id, h, ctx, limits)?
                } else {
                    read_uni(q, c, id)?
                }
            }
            QEv::Writable(id) => write_out(q, c, id, limits),
            QEv::Stopped(id) => {
                // The client no longer wants the response.
                q.reset(id, H3_REQUEST_CANCELLED);
                if let Some(mut r) = c.reqs.remove(&id) {
                    r.reset(limits);
                    c.pool.push(r);
                }
            }
            QEv::Other => {}
        }
    }
    if c.ctrl.is_none() && !q.handshaking() {
        open_control(q, c, limits)?;
    }
    Ok(())
}

/// Our control stream: its type, then SETTINGS (§6.2.1).
fn open_control<Q: Quic>(q: &mut Q, c: &mut App<Q::Id>, limits: &Limits3) -> Result<(), Close> {
    let Some(id) = q.open_uni() else { return Ok(()) };
    c.ctrl = Some(id);
    let s = Settings {
        qpack_max_table_capacity: None,
        max_field_section_size: Some(limits.max_field_section),
        qpack_blocked_streams: None,
        enable_connect_protocol: None,
        h3_datagram: None,
    };
    let mut b = [0u8; 64];
    let at = verilith_h3::write_var(&mut b, 0, STREAM_CONTROL).expect("fits");
    let end = verilith_h3::write_settings(&mut b, at, &s).expect("fits");
    // A new stream's send buffer always takes a few bytes; if it did not,
    // the peer would never see our SETTINGS.
    match q.write(id, &mut [Bytes::copy_from_slice(&b[..end])]) {
        Ok((1, _)) => Ok(()),
        _ => Err(Close(H3_INTERNAL_ERROR)),
    }
}

fn accept_uni<Q: Quic>(q: &mut Q, c: &mut App<Q::Id>, limits: &Limits3) -> Result<(), Close> {
    while let Some(id) = q.accept(false) {
        c.uni.insert(id, Uni { r: Reader::new_uni(true, limits.max_field_section), kind: None, raw: false });
        read_uni(q, c, id)?;
    }
    Ok(())
}

/// The pieces a read is handled in: what was read, then (at the end) the
/// end of the stream.
fn pieces(input: &[u8], fin: bool) -> impl Iterator<Item = (&[u8], bool)> {
    [(input, false), (&[][..], true)].into_iter().take(1 + fin as usize)
}

fn read_uni<Q: Quic>(q: &mut Q, c: &mut App<Q::Id>, id: Q::Id) -> Result<(), Close> {
    let Some(u) = c.uni.get_mut(&id) else { return Ok(()) };
    c.input.clear();
    let got = q.read(id, &mut c.input);
    if got == Read::Gone {
        return Ok(());
    }
    // A reset QPACK or control stream ends like a finished one.
    let mut res = Ok(());
    let mut discard = false;
    for (mut input, fin) in pieces(&c.input, got != Read::Open) {
        while !u.raw {
            let (ev, used) = u.r.next(input, fin);
            match ev {
                Ev::Need | Ev::End => break,
                Ev::Error(code) => {
                    res = Err(Close(code));
                    break;
                }
                Ev::StreamType(t) => {
                    let k = verilith_h3::uni_kind(t);
                    match verilith_h3::uni_open(c.seen, k) {
                        Ok(s) => c.seen = s,
                        Err(code) => {
                            res = Err(Close(code));
                            break;
                        }
                    }
                    u.kind = Some(k);
                }
                Ev::Handoff => u.raw = true,
                // SETTINGS: ours use no dynamic table and no extensions, so
                // nothing the client says changes what we send. GOAWAY,
                // MAX_PUSH_ID, CANCEL_PUSH: no server push, nothing to do.
                _ => {}
            }
            input = &input[used..];
        }
        if res.is_err() {
            break;
        }
        if u.raw {
            let ok = match u.kind {
                Some(UniKind::QpackEncoder) => {
                    let mut ready = Vec::new();
                    c.dec.feed_encoder(input, &mut ready) || {
                        res = Err(Close(QPACK_ENCODER_STREAM_ERROR));
                        false
                    }
                }
                Some(UniKind::QpackDecoder) => {
                    c.enc.feed_decoder(input) || {
                        res = Err(Close(QPACK_DECODER_STREAM_ERROR));
                        false
                    }
                }
                _ => {
                    discard = true;
                    false
                }
            };
            if !ok {
                break;
            }
            if fin {
                if let Some(k) = u.kind {
                    if let Err(code) = verilith_h3::uni_closed(k) {
                        res = Err(Close(code));
                    }
                }
            }
        }
    }
    if discard {
        // An unknown stream type: abort reading (§6.2).
        q.stop(id, H3_STREAM_CREATION_ERROR);
        c.uni.remove(&id);
    }
    res
}

fn accept_requests<Q: Quic, H: Handler + ?Sized>(q: &mut Q, c: &mut App<Q::Id>, h: &H, ctx: &Ctx, limits: &Limits3) -> Result<(), Close> {
    while let Some(id) = q.accept(true) {
        let r = match c.pool.pop() {
            Some(r) => r,
            None => Req::new(limits),
        };
        c.reqs.insert(id, r);
        c.requests = c.requests.max(id.into());
        read_request(q, c, id, h, ctx, limits)?;
    }
    Ok(())
}

fn read_request<Q: Quic, H: Handler + ?Sized>(
    q: &mut Q,
    c: &mut App<Q::Id>,
    id: Q::Id,
    h: &H,
    ctx: &Ctx,
    limits: &Limits3,
) -> Result<(), Close> {
    let Some(req) = c.reqs.get_mut(&id) else { return Ok(()) };
    c.input.clear();
    let got = q.read(id, &mut c.input);
    if got == Read::Gone {
        return Ok(());
    }
    let mut ended = false;
    let mut reset = got == Read::Reset;
    let mut res = Ok(());
    if !reset {
        'pieces: for (mut input, fin) in pieces(&c.input, got == Read::Fin) {
            loop {
                let (ev, used) = req.r.next(input, fin);
                match ev {
                    Ev::Need => break,
                    Ev::End => {
                        ended = true;
                        break 'pieces;
                    }
                    Ev::Error(code) => {
                        res = Err(Close(code));
                        break 'pieces;
                    }
                    Ev::Headers(src) => {
                        let sec: &[u8] = match src {
                            Src::Input(a, b) => &input[a..b],
                            Src::Buf(off) => &req.r.buffered()[off..],
                        };
                        match c.dec.decode(id.into(), sec, &mut c.lines) {
                            Res::Done => {}
                            // A field section over our SETTINGS: refuse the
                            // request (§4.2.2).
                            Res::TooBig => {
                                reset = true;
                                break 'pieces;
                            }
                            Res::Blocked | Res::Bad => {
                                res = Err(Close(QPACK_DECOMPRESSION_FAILED));
                                break 'pieces;
                            }
                        }
                        if !req.got_headers {
                            req.got_headers = true;
                            for i in 0..c.lines.len() {
                                let (n, v, _) = c.lines.get(i);
                                let ns = req.arena.len();
                                req.arena.extend_from_slice(n);
                                let vs = req.arena.len();
                                req.arena.extend_from_slice(v);
                                req.fields.push(Header { name: Span { start: ns, end: vs }, value: Span { start: vs, end: req.arena.len() } });
                            }
                        }
                        // A second HEADERS frame is the trailers: ignored.
                    }
                    Ev::Data(a, b) => {
                        if req.body.len() + (b - a) > limits.max_body {
                            req.too_big = true;
                        } else if !req.too_big {
                            req.body.extend_from_slice(&input[a..b]);
                        }
                    }
                    _ => {}
                }
                input = &input[used..];
            }
        }
    }
    if res.is_err() {
        return res;
    }
    if reset {
        q.reset(id, H3_REQUEST_REJECTED);
        q.stop(id, H3_REQUEST_REJECTED);
        if let Some(mut r) = c.reqs.remove(&id) {
            r.reset(limits);
            c.pool.push(r);
        }
        return Ok(());
    }
    if ended {
        if !request_fields_ok(&req.arena, &req.fields) {
            // Malformed (§4.1.2): a stream error.
            q.reset(id, H3_MESSAGE_ERROR);
            if let Some(mut r) = c.reqs.remove(&id) {
                r.reset(limits);
                c.pool.push(r);
            }
            return Ok(());
        }
        dispatch(c, id, h, ctx);
        write_out(q, c, id, limits);
    }
    Ok(())
}

/// Calls the handler and frames its response: HEADERS (the QPACK-encoded
/// section), then one DATA frame with the body.
fn dispatch<Id: Copy + Eq + Hash + Into<u64>, H: Handler + ?Sized>(c: &mut App<Id>, id: Id, h: &H, ctx: &Ctx) {
    let Some(req) = c.reqs.get_mut(&id) else { return };
    let a = &req.arena;
    let get = |n: &[u8]| req.fields.iter().find(|f| f.name.of(a) == n).map(|f| f.value.of(a)).unwrap_or(b"");
    let method = get(b":method");
    let target = get(b":path");
    let request = Request { method, target, minor: 1, buf: a, headers: &req.fields, body: &req.body, early: false, peer: None };
    let mut reply = req.reply.take().unwrap_or(Reply { status: 0, fields: HList::default(), body: ReplyBody::None, sent_headers: false, off: 0 });
    // A reused stream's reply keeps its buffers, not its fields.
    reply.fields.clear();
    reply.status = 0;
    reply.sent_headers = false;
    reply.off = 0;
    let mut scratch = crate::out::Wire::empty();
    let mut res = Response { out: &mut scratch, ctx, sent: false, close: false, head: method == b"HEAD", h2: Some(&mut reply) };
    if req.too_big {
        res.error(413);
    } else {
        h.handle(&request, &mut res);
    }
    if !res.sent {
        res.error(500);
    }
    drop(res);
    let st = [b'0' + (reply.status / 100) as u8, b'0' + (reply.status / 10 % 10) as u8, b'0' + (reply.status % 10) as u8];
    c.lines.clear();
    c.lines.push(b":status", &st, false);
    for (n, v) in reply.fields.iter().chain(ctx.own_h2.iter()) {
        c.lines.push(n, v, n == b"set-cookie");
    }
    c.section.clear();
    c.enc.encode(id.into(), &c.lines, &mut c.section);
    let body = match std::mem::replace(&mut reply.body, ReplyBody::None) {
        ReplyBody::None => Bytes::new(),
        ReplyBody::Owned(v) => Bytes::from(v),
        ReplyBody::Shared(a) => Bytes::from_owner(a),
        ReplyBody::Slice(a, s, n) => Bytes::from_owner(a).slice(s..s + n),
    };
    let mut head = Vec::with_capacity(c.section.len() + 16);
    let mut b = [0u8; 16];
    let n = verilith_h3::write_header(&mut b, 0, HEADERS, c.section.len() as u64).expect("fits");
    head.extend_from_slice(&b[..n]);
    head.extend_from_slice(&c.section);
    if !body.is_empty() {
        let n = verilith_h3::write_header(&mut b, 0, DATA, body.len() as u64).expect("fits");
        head.extend_from_slice(&b[..n]);
    }
    req.out = [Bytes::from(head), body];
    req.next = 0;
    req.answered = true;
    req.reply = Some(reply);
}

/// Gives QUIC what it will take of a response; finishes the stream once
/// it has all of it.
fn write_out<Q: Quic>(q: &mut Q, c: &mut App<Q::Id>, id: Q::Id, limits: &Limits3) {
    let Some(req) = c.reqs.get_mut(&id) else { return };
    if !req.answered {
        return;
    }
    while req.next < 2 {
        if req.out[req.next].is_empty() {
            req.next += 1;
            continue;
        }
        match q.write(id, &mut req.out[req.next..]) {
            Ok((chunks, bytes)) => {
                req.next += chunks;
                if bytes == 0 {
                    return;
                }
            }
            Err(true) => return,
            Err(false) => break,
        }
    }
    q.finish(id);
    if let Some(mut r) = c.reqs.remove(&id) {
        r.reset(limits);
        if c.pool.len() < 64 {
            c.pool.push(r);
        }
    }
}
