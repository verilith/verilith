//! HTTP/3 (RFC 9114), one QUIC endpoint per worker (DESIGN.md, "HTTP/3").
//!
//! QUIC itself is verilith-quic-conn, sans I/O: its wire format, flow
//! control, stream states, loss recovery and congestion control are
//! verilith-quic's (verified), and its handshake and packet protection are
//! verilith-tls's (verified), with aws-lc's cryptography. The connection
//! logic joining them is that crate's (its README says what of it is
//! verified).
//!
//! Everything HTTP/3 is verified: what each stream's bytes mean is
//! [`crate::h3core`]'s (on verilith-h3's `Reader`: frame syntax and order,
//! with the RFC's error codes; the request lifecycle, Content-Length, the
//! critical streams, the response framing and our SETTINGS), field
//! sections go through verilith-qpack's decoder and encoder, and the flood
//! budget is `h3core::Budget`. This file connects them: it accepts
//! streams, hands their bytes to the core, decodes the sections the core
//! points at, dispatches requests to the handler like HTTP/2 does, and
//! writes the responses, through the [`Quic`] trait. It is
//! trusted for that plumbing (TRUST.md) and tested in `tests/h3.rs`.
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
use verilith_h3::consts::*;
use verilith_h3::{Src, UniKind, UniSeen};
use verilith_http::Header;
use verilith_http::parse::Span;
use verilith_qpack::encoder::Encoder;
use verilith_qpack::{Decoder, Fields, Res};
use verilith_quic_conn as vq;
use verilith_tls_aws_lc::{AwsLc, SigningKey, GROUPS, SUITES};

use crate::h1::Ctx;
use crate::h3core::{self, Act, Budget, Req3, UAct, Uni3};
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
    /// Request streams a client may abandon (reset before their end, or
    /// have refused) for each request it completes, beyond `2 *
    /// max_streams`; past that the connection is closed with
    /// H3_EXCESSIVE_LOAD (`h3core::Budget`).
    pub abandoned_per_request: u32,
    /// The largest UDP payload the verilith backend probes for: it starts
    /// at 1200, the minimum QUIC requires of paths (RFC 9000 §14), and
    /// steps up through 1452 (a 1500-byte Ethernet MTU over IPv6) and 8952
    /// (a 9000-byte jumbo frame) to this, as each probe is acknowledged.
    /// The socket sets DF, so a probe the path cannot carry is lost, not
    /// fragmented. 65487 fits loopback's 65536-byte MTU over IPv6: there,
    /// as with nginx, a 64 KiB response is one datagram, not 45.
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
            abandoned_per_request: 100,
            max_udp_payload: 65487,
        }
    }
}

/// A QUIC server configuration.
#[derive(Clone)]
pub struct QuicConfig(Arc<vq::Config<AwsLc>>);

impl std::fmt::Debug for QuicConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("QuicConfig")
    }
}

/// The QUIC server configuration (TLS 1.3, ALPN `h3`) for this
/// certificate chain and key, PEM files (the key PKCS#8).
pub fn server_config(cert: &str, key: &str, limits: Limits3) -> std::io::Result<QuicConfig> {
    use crate::tls::pem_blocks;
    let chain = pem_blocks(&std::fs::read(cert)?, "CERTIFICATE");
    let keys = pem_blocks(&std::fs::read(key)?, "PRIVATE KEY");
    let key = keys.first().ok_or_else(|| std::io::Error::other("no PKCS#8 \"PRIVATE KEY\" block in the key file"))?;
    server_config_der(chain, key, limits)
}

/// [`server_config`], from a certificate chain (DER, leaf first) and a
/// PKCS#8 key (DER).
pub fn server_config_der(chain: Vec<Vec<u8>>, key_pkcs8: &[u8], limits: Limits3) -> std::io::Result<QuicConfig> {
    let bad = |m: &str| std::io::Error::new(std::io::ErrorKind::InvalidInput, m.to_string());
    let key = SigningKey::from_pkcs8(key_pkcs8).ok_or_else(|| bad("the key is not PKCS#8 ECDSA, Ed25519 or RSA"))?;
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
    Ok(QuicConfig(Arc::new(c)))
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
    /// What the stream's bytes mean (verified).
    core: Req3,
    /// The decoded field section, as spans into `arena`.
    arena: Vec<u8>,
    fields: Vec<Header>,
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
            core: Req3::new(limits.max_field_section, limits.max_body),
            arena: Vec::new(),
            fields: Vec::new(),
            reply: None,
            out: [Bytes::new(), Bytes::new()],
            next: 0,
            answered: false,
        })
    }

    fn reset(&mut self, limits: &Limits3) {
        self.core.reset(limits.max_field_section, limits.max_body);
        self.arena.clear();
        self.fields.clear();
        self.out = [Bytes::new(), Bytes::new()];
        self.next = 0;
        self.answered = false;
    }
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
    uni: HashMap<Id, Uni3, IdHasher>,
    reqs: HashMap<Id, Box<Req>, IdHasher>,
    pool: Vec<Box<Req>>,
    /// Scratch for decoded field lines.
    lines: Fields,
    /// Scratch for one encoded field section.
    section: Vec<u8>,
    /// Scratch for a stream's bytes.
    input: Vec<u8>,
    /// Requests abandoned against requests completed.
    budget: Budget,
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
            budget: Budget::new(2 * u64::from(limits.max_streams), u64::from(limits.abandoned_per_request)),
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
    server: vq::Server<AwsLc, VConn>,
    /// The connections' clock starts here.
    epoch: Instant,
    timers: BinaryHeap<Reverse<(Instant, usize)>>,
    limits: Limits3,
    /// Datagrams are received into the spare capacity of this buffer.
    rbuf: BytesMut,
    sbuf: Vec<u8>,
    dirty: Vec<usize>,
    gso: bool,
}

struct VConn {
    app: App<u64>,
    /// Where the connection's first datagram came from: replies go there
    /// (no migration).
    peer: SocketAddrV4,
    deadline: Option<Instant>,
}

/// Datagrams per `sendmsg` with segmentation offload: Linux's limit
/// (UDP_MAX_SEGMENTS), and verilith-quic-conn also keeps a batch within
/// one UDP payload. 16 sent a 64 KiB response in three or four batches,
/// against nginx-quic's one or two, and the extra sends and receives
/// left the server waiting on the client.
const BATCH: usize = 64;
const RECV_ROOM: usize = 64 * 1024;
/// Bytes one connection sends at a time, before it next hears from its
/// peer (RFC 9002 §7.7: a sender should limit bursts; it does not pace).
/// Linux gives a socket 208 KiB of receive buffer by default, and h2load,
/// like most clients, keeps it: a 1 MiB window sent at once in 64 KiB
/// datagrams lost its tail there, and each such loss waited for a probe
/// timeout. 128 KiB stays within it.
const BURST: usize = 128 * 1024;

impl H3 {
    pub fn new(fd: i32, cfg: QuicConfig, limits: Limits3) -> H3 {
        H3 {
            fd,
            server: vq::Server::new(cfg.0),
            epoch: Instant::now(),
            timers: BinaryHeap::new(),
            limits,
            rbuf: BytesMut::new(),
            sbuf: Vec::with_capacity(BATCH * 1500),
            dirty: Vec::new(),
            gso: sys::UDP_SEGMENT.is_some(),
        }
    }

    fn deadline(&mut self, ch: usize) -> Option<Instant> {
        self.server.get(ch)?.1.deadline
    }

    /// Milliseconds to the next timer, if any, rounded up.
    pub fn timeout_ms(&mut self, now: Instant) -> Option<i32> {
        self.timeout_us(now).map(|us| us.div_ceil(1000) as i32)
    }

    /// Microseconds to the next timer, if any (at most a second), rounded
    /// up: waking early only to sleep again costs a poll. Loss detection
    /// on a fast path waits a fraction of a millisecond (RFC 9002 §6.1.2:
    /// 9/8 of the RTT), so rounding to milliseconds would leave the
    /// connection idle for most of that millisecond.
    pub fn timeout_us(&mut self, now: Instant) -> Option<u64> {
        while let Some(Reverse((t, ch))) = self.timers.peek().copied() {
            if self.deadline(ch) != Some(t) {
                self.timers.pop();
                continue;
            }
            let d = t.saturating_duration_since(now);
            return Some((d.as_micros() as u64 + !d.subsec_nanos().is_multiple_of(1000) as u64).min(1_000_000));
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
            let us = micros(self.epoch, now);
            if let Some((q, c)) = self.server.get(ch) {
                c.deadline = None;
                q.handle_timeout(us);
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
        let limits = &self.limits;
        let make = || VConn { app: App::new(limits), peer: remote, deadline: None };
        match self.server.handle_with(micros(self.epoch, now), &mut data, &mut self.sbuf, make) {
            vq::Datagram::Conn(i) => self.dirty.push(i),
            vq::Datagram::Response(n) => send(self.fd, &self.sbuf[..n], SocketAddr::V4(remote), None, &mut self.gso),
            vq::Datagram::Dropped => {}
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
    /// application events, the packets to send, and its timer.
    fn drive<H: Handler + ?Sized>(&mut self, ch: usize, h: &H, ctx: &Ctx, now: Instant) {
        let limits = self.limits;
        let max = if self.gso { BATCH } else { 1 };
        let deadline = {
            let (server, epoch) = (&mut self.server, self.epoch);
            let us = micros(epoch, now);
            let Some((q, c)) = server.get(ch) else { return };
            if let Err(Close(code)) = app_events(q, &mut c.app, h, ctx, &limits) {
                q.close(us, code);
            }
            // At most BURST bytes now: the rest goes as acknowledgments
            // arrive (or a timer fires), so that a burst of a whole
            // window does not overflow the client's socket buffer.
            let mut burst = 0;
            while burst < BURST {
                self.sbuf.clear();
                let Some(t) = q.poll_transmit(us, max, &mut self.sbuf) else { break };
                burst += t.size;
                send(self.fd, &self.sbuf[..t.size], SocketAddr::V4(c.peer), t.segment_size, &mut self.gso);
            }
            if q.is_closed() {
                server.reap(ch);
                return;
            }
            let d = q.poll_timeout().map(|t| epoch + Duration::from_micros(t));
            if d == c.deadline {
                return;
            }
            c.deadline = d;
            d
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
                    if !c.budget.spend() {
                        return Err(Close(H3_EXCESSIVE_LOAD));
                    }
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

/// Our control stream: its type, then SETTINGS (§6.2.1), as
/// `h3core::control_preamble` proves.
fn open_control<Q: Quic>(q: &mut Q, c: &mut App<Q::Id>, limits: &Limits3) -> Result<(), Close> {
    let Some(id) = q.open_uni() else { return Ok(()) };
    c.ctrl = Some(id);
    let mut b = [0u8; 64];
    let end = h3core::control_preamble(limits.max_field_section, &mut b);
    if end == 0 {
        return Err(Close(H3_INTERNAL_ERROR));
    }
    // A new stream's send buffer always takes a few bytes; if it did not,
    // the peer would never see our SETTINGS.
    match q.write(id, &mut [Bytes::copy_from_slice(&b[..end])]) {
        Ok((1, _)) => Ok(()),
        _ => Err(Close(H3_INTERNAL_ERROR)),
    }
}

fn accept_uni<Q: Quic>(q: &mut Q, c: &mut App<Q::Id>, limits: &Limits3) -> Result<(), Close> {
    while let Some(id) = q.accept(false) {
        c.uni.insert(id, Uni3::new(limits.max_field_section));
        read_uni(q, c, id)?;
    }
    Ok(())
}

fn read_uni<Q: Quic>(q: &mut Q, c: &mut App<Q::Id>, id: Q::Id) -> Result<(), Close> {
    let Some(u) = c.uni.get_mut(&id) else { return Ok(()) };
    c.input.clear();
    let got = q.read(id, &mut c.input);
    if got == Read::Gone {
        return Ok(());
    }
    // A reset QPACK or control stream ends like a finished one.
    match u.step(&mut c.seen, &c.input, got != Read::Open) {
        UAct::Need => Ok(()),
        UAct::Close(code) => Err(Close(code)),
        UAct::Discard => {
            // An unknown stream type: abort reading (§6.2).
            q.stop(id, H3_STREAM_CREATION_ERROR);
            c.uni.remove(&id);
            Ok(())
        }
        UAct::Raw(from) => {
            let input = &c.input[from..];
            match u.kind() {
                Some(UniKind::QpackEncoder) => {
                    let mut ready = Vec::new();
                    if !c.dec.feed_encoder(input, &mut ready) {
                        return Err(Close(QPACK_ENCODER_STREAM_ERROR));
                    }
                }
                Some(UniKind::QpackDecoder) => {
                    if !c.enc.feed_decoder(input) {
                        return Err(Close(QPACK_DECODER_STREAM_ERROR));
                    }
                }
                _ => {}
            }
            Ok(())
        }
    }
}

fn accept_requests<Q: Quic, H: Handler + ?Sized>(q: &mut Q, c: &mut App<Q::Id>, h: &H, ctx: &Ctx, limits: &Limits3) -> Result<(), Close> {
    while let Some(id) = q.accept(true) {
        let r = match c.pool.pop() {
            Some(r) => r,
            None => Req::new(limits),
        };
        c.reqs.insert(id, r);
        read_request(q, c, id, h, ctx, limits)?;
    }
    Ok(())
}

/// How a read of a request stream ended.
enum Verdict {
    /// More is to come.
    Wait,
    /// The request is complete.
    Ready,
    /// Refuse the stream with this code (reset and stop reading it).
    Refuse(u64),
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
    let mut verdict = Verdict::Wait;
    if got == Read::Reset {
        verdict = Verdict::Refuse(H3_REQUEST_REJECTED);
    } else {
        let fin = got == Read::Fin;
        let mut at = 0;
        'steps: loop {
            let trailers = match req.core.step(&c.input, &mut at, fin) {
                Act::Need | Act::Done => break,
                Act::Close(code) => return Err(Close(code)),
                // Malformed (§4.1.2): a stream error.
                Act::Malformed => {
                    verdict = Verdict::Refuse(H3_MESSAGE_ERROR);
                    break;
                }
                Act::Ready => {
                    verdict = Verdict::Ready;
                    break;
                }
                Act::Headers(src) => (false, src),
                Act::Trailers(src) => (true, src),
            };
            let sec: &[u8] = match trailers.1 {
                Src::Input(a, b) => &c.input[a..b],
                Src::Buf(off) => &req.core.buffered()[off..],
            };
            match c.dec.decode(id.into(), sec, &mut c.lines) {
                Res::Done => {}
                // A field section over our SETTINGS: refuse the request
                // (§4.2.2).
                Res::TooBig => {
                    verdict = Verdict::Refuse(H3_REQUEST_REJECTED);
                    break;
                }
                Res::Blocked | Res::Bad => return Err(Close(QPACK_DECOMPRESSION_FAILED)),
            }
            if trailers.0 {
                // Decoded for their errors; not passed on.
                continue;
            }
            for i in 0..c.lines.len() {
                let (n, v, _) = c.lines.get(i);
                if n == b"content-length" && !req.core.declare_cl(v) {
                    verdict = Verdict::Refuse(H3_MESSAGE_ERROR);
                    break 'steps;
                }
                let ns = req.arena.len();
                req.arena.extend_from_slice(n);
                let vs = req.arena.len();
                req.arena.extend_from_slice(v);
                req.fields.push(Header { name: Span { start: ns, end: vs }, value: Span { start: vs, end: req.arena.len() } });
            }
        }
    }
    match verdict {
        Verdict::Wait => Ok(()),
        Verdict::Refuse(code) => refuse(q, c, id, code, limits),
        Verdict::Ready => {
            if !request_fields_ok(&req.arena, &req.fields) {
                // Malformed (§4.1.2): a stream error.
                return refuse(q, c, id, H3_MESSAGE_ERROR, limits);
            }
            c.budget.earn();
            if !dispatch(c, id, h, ctx) {
                q.reset(id, H3_INTERNAL_ERROR);
                drop_req(c, id, limits);
                return Ok(());
            }
            write_out(q, c, id, limits);
            Ok(())
        }
    }
}

/// Resets a request stream and stops reading it, as a stream error; the
/// peer's budget pays for it.
fn refuse<Q: Quic>(q: &mut Q, c: &mut App<Q::Id>, id: Q::Id, code: u64, limits: &Limits3) -> Result<(), Close> {
    q.reset(id, code);
    q.stop(id, code);
    drop_req(c, id, limits);
    if !c.budget.spend() {
        return Err(Close(H3_EXCESSIVE_LOAD));
    }
    Ok(())
}

fn drop_req<Id: Eq + Hash>(c: &mut App<Id>, id: Id, limits: &Limits3) {
    if let Some(mut r) = c.reqs.remove(&id) {
        r.reset(limits);
        if c.pool.len() < 64 {
            c.pool.push(r);
        }
    }
}

/// Calls the handler and frames its response: HEADERS (the QPACK-encoded
/// section), then one DATA frame with the body.
fn dispatch<Id: Copy + Eq + Hash + Into<u64>, H: Handler + ?Sized>(c: &mut App<Id>, id: Id, h: &H, ctx: &Ctx) -> bool {
    let Some(req) = c.reqs.get_mut(&id) else { return false };
    let a = &req.arena;
    let get = |n: &[u8]| req.fields.iter().find(|f| f.name.of(a) == n).map(|f| f.value.of(a)).unwrap_or(b"");
    let method = get(b":method");
    let target = get(b":path");
    let request = Request { method, target, minor: 1, buf: a, headers: &req.fields, body: req.core.body(), early: false, peer: None };
    let mut reply = req.reply.take().unwrap_or(Reply { status: 0, fields: HList::default(), body: ReplyBody::None, sent_headers: false, off: 0 });
    // A reused stream's reply keeps its buffers, not its fields.
    reply.fields.clear();
    reply.status = 0;
    reply.sent_headers = false;
    reply.off = 0;
    let mut scratch = crate::out::Wire::empty();
    let mut res = Response { out: &mut scratch, ctx, sent: false, close: false, head: method == b"HEAD", h2: Some(&mut reply) };
    if req.core.too_big() {
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
    // HEADERS, then one DATA frame with the body: `h3core::frame_head`
    // and `lemma_response_rt`.
    let mut head = Vec::with_capacity(c.section.len() + 16);
    let framed = h3core::frame_head(&mut head, &c.section, body.len());
    req.reply = Some(reply);
    if !framed {
        return false;
    }
    req.out = [Bytes::from(head), body];
    req.next = 0;
    req.answered = true;
    true
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
    drop_req(c, id, limits);
}
