//! HTTP/3 (RFC 9114), one QUIC endpoint per worker (DESIGN.md, "HTTP/3").
//!
//! QUIC itself (packets, TLS 1.3, loss recovery, congestion control) is
//! quinn-proto, sans I/O and trusted (TRUST.md). Everything HTTP/3 is
//! verified: each stream's bytes go through verilith-h3's `Reader` (frame
//! syntax and order, with the RFC's error codes), field sections through
//! verilith-qpack's decoder and encoder, and frames are written by
//! verilith-h3's encoders. This file connects them: it accepts streams,
//! dispatches requests to the handler like HTTP/2 does, and writes the
//! responses. It is not verified; it is tested in `tests/h3.rs`.
//!
//! QPACK runs without a dynamic table in either direction (our SETTINGS
//! advertise capacity 0 and no blocked streams, and our encoder uses none),
//! so no section ever blocks and the QPACK streams carry nothing but what
//! the peer chooses to send on them.
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};
use std::sync::Arc;
use std::time::Instant;

use bytes::{Bytes, BytesMut};
use quinn_proto::{
    ConnectionHandle, DatagramEvent, Dir, Endpoint, EndpointConfig, Event, ReadError, ServerConfig, StreamEvent,
    StreamId, TransportConfig, VarInt, WriteError,
};
use verilith_h3::consts::*;
use verilith_h3::{Event as Ev, Reader, Settings, Src, UniKind, UniSeen};
use verilith_http::Header;
use verilith_http::parse::Span;
use verilith_qpack::encoder::Encoder;
use verilith_qpack::{Decoder, Fields, Res};

use crate::h1::{Ctx, Out};
use crate::h2::{request_fields_ok, HList, Reply, ReplyBody};
use crate::sys;
use crate::{Handler, Request, Response};

const QPACK_DECOMPRESSION_FAILED: u64 = 0x200;
const QPACK_ENCODER_STREAM_ERROR: u64 = 0x201;
const QPACK_DECODER_STREAM_ERROR: u64 = 0x202;

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
    /// Bytes quinn may hold unacknowledged for one connection.
    pub send_window: u64,
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
        }
    }
}

/// The QUIC server configuration (TLS 1.3 by rustls with aws-lc, ALPN
/// `h3`) for this certificate chain and key, PEM files.
pub fn server_config(cert: &str, key: &str, limits: Limits3) -> std::io::Result<Arc<ServerConfig>> {
    use rustls::pki_types::pem::PemObject;
    use rustls::pki_types::{CertificateDer, PrivateKeyDer};
    let e = |e: rustls::pki_types::pem::Error| std::io::Error::other(e.to_string());
    let certs = CertificateDer::pem_file_iter(cert).map_err(e)?.collect::<Result<Vec<_>, _>>().map_err(e)?;
    let key = PrivateKeyDer::from_pem_file(key).map_err(e)?;
    server_config_der(certs, key, limits)
}

/// [`server_config`], from DER.
pub fn server_config_der(
    certs: Vec<rustls::pki_types::CertificateDer<'static>>,
    key: rustls::pki_types::PrivateKeyDer<'static>,
    limits: Limits3,
) -> std::io::Result<Arc<ServerConfig>> {
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
    Ok(Arc::new(s))
}

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
    /// The response's frames, not yet all taken by quinn: the HEADERS frame
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

struct Conn3 {
    q: quinn_proto::Connection,
    dec: Decoder,
    enc: Encoder,
    seen: UniSeen,
    /// Our control stream, once opened.
    ctrl: Option<StreamId>,
    uni: HashMap<StreamId, Uni>,
    reqs: HashMap<StreamId, Box<Req>>,
    pool: Vec<Box<Req>>,
    /// The timer last scheduled for this connection.
    deadline: Option<Instant>,
    /// Scratch for decoded field lines.
    lines: Fields,
    /// Scratch for one encoded field section.
    section: Vec<u8>,
    /// The highest request stream accepted, for GOAWAY.
    requests: u64,
}

/// A connection error: the connection is closed with this code.
struct Close(u64);

/// One worker's HTTP/3 endpoint: a UDP socket, quinn's endpoint and the
/// connections on it.
pub struct H3 {
    pub(crate) fd: i32,
    endpoint: Endpoint,
    conns: Vec<Option<Box<Conn3>>>,
    timers: BinaryHeap<Reverse<(Instant, usize)>>,
    limits: Limits3,
    /// Datagrams are received into the spare capacity of this buffer and
    /// split off it, so quinn holds them without a copy.
    rbuf: BytesMut,
    sbuf: Vec<u8>,
    dirty: Vec<usize>,
    gso: bool,
}

/// Datagrams per `sendmsg` with segmentation offload.
const BATCH: usize = 16;
const RECV_ROOM: usize = 64 * 1024;

impl H3 {
    pub fn new(fd: i32, cfg: Arc<ServerConfig>, limits: Limits3) -> H3 {
        let endpoint = Endpoint::new(Arc::new(EndpointConfig::default()), Some(cfg), true, None);
        H3 {
            fd,
            endpoint,
            conns: Vec::new(),
            timers: BinaryHeap::new(),
            limits,
            rbuf: BytesMut::new(),
            sbuf: Vec::with_capacity(BATCH * 1500),
            dirty: Vec::new(),
            gso: sys::UDP_SEGMENT.is_some(),
        }
    }

    /// Milliseconds to the next timer, if any.
    pub fn timeout_ms(&mut self, now: Instant) -> Option<i32> {
        while let Some(Reverse((t, ch))) = self.timers.peek().copied() {
            let live = matches!(self.conns.get(ch), Some(Some(c)) if c.deadline == Some(t));
            if !live {
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
            if let Some(Some(c)) = self.conns.get_mut(ch) {
                if c.deadline == Some(t) {
                    c.deadline = None;
                    c.q.handle_timeout(now);
                    self.dirty.push(ch);
                }
            }
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
            let remote = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::from(ip), port));
            while !all.is_empty() {
                let data = all.split_to(seg.min(all.len()));
                self.on_datagram(now, remote, data);
            }
        }
        self.drive_dirty(h, ctx, now);
    }

    fn on_datagram(&mut self, now: Instant, remote: SocketAddr, data: BytesMut) {
        {
            self.sbuf.clear();
            match self.endpoint.handle(now, remote, None, None, data, &mut self.sbuf) {
                Some(DatagramEvent::NewConnection(incoming)) => {
                    self.sbuf.clear();
                    match self.endpoint.accept(incoming, now, &mut self.sbuf, None) {
                        Ok((ch, q)) => {
                            let i = ch.0;
                            if self.conns.len() <= i {
                                self.conns.resize_with(i + 1, || None);
                            }
                            self.conns[i] = Some(Box::new(Conn3 {
                                q,
                                dec: Decoder::new(0, 0, self.limits.max_field_section).expect("QPACK decoder"),
                                enc: Encoder::new(0, 0, 0).expect("QPACK encoder"),
                                seen: UniSeen { control: false, encoder: false, decoder: false },
                                ctrl: None,
                                uni: HashMap::new(),
                                reqs: HashMap::new(),
                                pool: Vec::new(),
                                deadline: None,
                                lines: Fields::new(),
                                section: Vec::new(),
                                requests: 0,
                            }));
                            self.dirty.push(i);
                        }
                        Err(e) => {
                            if let Some(t) = e.response {
                                self.transmit(&t);
                            }
                        }
                    }
                }
                Some(DatagramEvent::ConnectionEvent(ch, ev)) => {
                    if let Some(Some(c)) = self.conns.get_mut(ch.0) {
                        c.q.handle_event(ev);
                        self.dirty.push(ch.0);
                    }
                }
                Some(DatagramEvent::Response(t)) => self.transmit(&t),
                None => {}
            }
        }
    }

    fn transmit(&mut self, t: &quinn_proto::Transmit) {
        let SocketAddr::V4(d) = t.destination else { return };
        let seg = t.segment_size.unwrap_or(t.size);
        sys::send_to(self.fd, &self.sbuf[..t.size], d.ip().octets(), d.port(), seg, &mut self.gso);
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

    /// Everything a connection has to do after its state changed: quinn's
    /// endpoint events, the application events, the packets to send, and
    /// its timer.
    fn drive<H: Handler + ?Sized>(&mut self, ch: usize, h: &H, ctx: &Ctx, now: Instant) {
        let Some(Some(c)) = self.conns.get_mut(ch) else { return };
        let limits = self.limits;
        if exchange(&mut self.endpoint, ch, c) {
            self.conns[ch] = None;
            return;
        }
        while let Some(ev) = c.q.poll() {
            let r = match ev {
                Event::Stream(StreamEvent::Opened { dir: Dir::Bi }) => accept_requests(c, h, ctx, &limits),
                Event::Stream(StreamEvent::Opened { dir: Dir::Uni }) => accept_uni(c, &limits),
                Event::Stream(StreamEvent::Readable { id }) => {
                    if id.dir() == Dir::Bi {
                        read_request(c, id, h, ctx, &limits)
                    } else {
                        read_uni(c, id)
                    }
                }
                Event::Stream(StreamEvent::Writable { id }) => {
                    write_out(c, id, &limits);
                    Ok(())
                }
                Event::Stream(StreamEvent::Stopped { id, .. }) => {
                    // The client no longer wants the response.
                    let _ = c.q.send_stream(id).reset(VarInt::from_u64(H3_REQUEST_CANCELLED).unwrap());
                    if let Some(mut r) = c.reqs.remove(&id) {
                        r.reset(&limits);
                        c.pool.push(r);
                    }
                    Ok(())
                }
                _ => Ok(()),
            };
            if let Err(Close(code)) = r {
                c.q.close(now, VarInt::from_u64(code).unwrap_or(VarInt::from_u32(0x101)), Bytes::new());
                break;
            }
        }
        if c.ctrl.is_none() && !c.q.is_handshaking() {
            open_control(c, &limits);
        }
        loop {
            self.sbuf.clear();
            let max = if self.gso { BATCH } else { 1 };
            let Some(t) = c.q.poll_transmit(now, max, &mut self.sbuf) else { break };
            let SocketAddr::V4(d) = t.destination else { continue };
            let seg = t.segment_size.unwrap_or(t.size);
            sys::send_to(self.fd, &self.sbuf[..t.size], d.ip().octets(), d.port(), seg, &mut self.gso);
        }
        if exchange(&mut self.endpoint, ch, c) {
            self.conns[ch] = None;
            return;
        }
        let d = c.q.poll_timeout();
        if d != c.deadline {
            c.deadline = d;
            if let Some(t) = d {
                self.timers.push(Reverse((t, ch)));
            }
        }
    }
}

/// Passes events between a connection and the endpoint. True once the
/// connection is drained (gone).
fn exchange(endpoint: &mut Endpoint, ch: usize, c: &mut Conn3) -> bool {
    while let Some(ev) = c.q.poll_endpoint_events() {
        let drained = ev.is_drained();
        if let Some(back) = endpoint.handle_event(ConnectionHandle(ch), ev) {
            c.q.handle_event(back);
        }
        if drained {
            return true;
        }
    }
    false
}

/// Our control stream: its type, then SETTINGS (§6.2.1).
fn open_control(c: &mut Conn3, limits: &Limits3) {
    let Some(id) = c.q.streams().open(Dir::Uni) else { return };
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
    // A new stream's send buffer always takes a few bytes.
    let _ = c.q.send_stream(id).write(&b[..end]);
}

fn accept_uni(c: &mut Conn3, limits: &Limits3) -> Result<(), Close> {
    while let Some(id) = c.q.streams().accept(Dir::Uni) {
        c.uni.insert(id, Uni { r: Reader::new_uni(true, limits.max_field_section), kind: None, raw: false });
        read_uni(c, id)?;
    }
    Ok(())
}

fn read_uni(c: &mut Conn3, id: StreamId) -> Result<(), Close> {
    let Some(u) = c.uni.get_mut(&id) else { return Ok(()) };
    let mut rs = c.q.recv_stream(id);
    let Ok(mut chunks) = rs.read(true) else { return Ok(()) };
    let mut res = Ok(());
    let mut discard = false;
    loop {
        let (bytes, fin) = match chunks.next(usize::MAX) {
            Ok(Some(ch)) => (ch.bytes, false),
            Ok(None) => (Bytes::new(), true),
            Err(ReadError::Blocked) => break,
            Err(ReadError::Reset(_)) => (Bytes::new(), true),
        };
        let mut input: &[u8] = &bytes;
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
        if fin {
            break;
        }
    }
    let _ = chunks.finalize();
    if discard {
        // An unknown stream type: abort reading (§6.2).
        let _ = c.q.recv_stream(id).stop(VarInt::from_u64(H3_STREAM_CREATION_ERROR).unwrap());
        c.uni.remove(&id);
    }
    res
}

fn accept_requests<H: Handler + ?Sized>(c: &mut Conn3, h: &H, ctx: &Ctx, limits: &Limits3) -> Result<(), Close> {
    while let Some(id) = c.q.streams().accept(Dir::Bi) {
        let r = match c.pool.pop() {
            Some(r) => r,
            None => Req::new(limits),
        };
        c.reqs.insert(id, r);
        c.requests = c.requests.max(u64::from(id));
        read_request(c, id, h, ctx, limits)?;
    }
    Ok(())
}

fn read_request<H: Handler + ?Sized>(c: &mut Conn3, id: StreamId, h: &H, ctx: &Ctx, limits: &Limits3) -> Result<(), Close> {
    let Some(req) = c.reqs.get_mut(&id) else { return Ok(()) };
    let mut rs = c.q.recv_stream(id);
    let Ok(mut chunks) = rs.read(true) else { return Ok(()) };
    let mut ended = false;
    let mut reset = false;
    let mut res = Ok(());
    'chunks: loop {
        let (bytes, fin) = match chunks.next(usize::MAX) {
            Ok(Some(ch)) => (ch.bytes, false),
            Ok(None) => (Bytes::new(), true),
            Err(ReadError::Blocked) => break,
            Err(ReadError::Reset(_)) => {
                reset = true;
                break;
            }
        };
        let mut input: &[u8] = &bytes;
        loop {
            let (ev, used) = req.r.next(input, fin);
            match ev {
                Ev::Need => break,
                Ev::End => {
                    ended = true;
                    break 'chunks;
                }
                Ev::Error(code) => {
                    res = Err(Close(code));
                    break 'chunks;
                }
                Ev::Headers(src) => {
                    let sec: &[u8] = match src {
                        Src::Input(a, b) => &input[a..b],
                        Src::Buf(off) => &req.r.buffered()[off..],
                    };
                    match c.dec.decode(u64::from(id), sec, &mut c.lines) {
                        Res::Done => {}
                        // A field section over our SETTINGS: refuse the
                        // request (§4.2.2).
                        Res::TooBig => {
                            reset = true;
                            break 'chunks;
                        }
                        Res::Blocked | Res::Bad => {
                            res = Err(Close(QPACK_DECOMPRESSION_FAILED));
                            break 'chunks;
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
        if fin {
            break;
        }
    }
    let _ = chunks.finalize();
    if res.is_err() {
        return res;
    }
    if reset {
        let _ = c.q.send_stream(id).reset(VarInt::from_u64(H3_REQUEST_REJECTED).unwrap());
        let _ = c.q.recv_stream(id).stop(VarInt::from_u64(H3_REQUEST_REJECTED).unwrap());
        if let Some(mut r) = c.reqs.remove(&id) {
            r.reset(limits);
            c.pool.push(r);
        }
        return Ok(());
    }
    if ended {
        if !request_fields_ok(&req.arena, &req.fields) {
            // Malformed (§4.1.2): a stream error.
            let _ = c.q.send_stream(id).reset(VarInt::from_u64(H3_MESSAGE_ERROR).unwrap());
            if let Some(mut r) = c.reqs.remove(&id) {
                r.reset(limits);
                c.pool.push(r);
            }
            return Ok(());
        }
        dispatch(c, id, h, ctx);
        write_out(c, id, limits);
    }
    Ok(())
}

/// Calls the handler and frames its response: HEADERS (the QPACK-encoded
/// section), then one DATA frame with the body.
fn dispatch<H: Handler + ?Sized>(c: &mut Conn3, id: StreamId, h: &H, ctx: &Ctx) {
    let Some(req) = c.reqs.get_mut(&id) else { return };
    let a = &req.arena;
    let get = |n: &[u8]| req.fields.iter().find(|f| f.name.of(a) == n).map(|f| f.value.of(a)).unwrap_or(b"");
    let method = get(b":method");
    let target = get(b":path");
    let request = Request { method, target, minor: 1, buf: a, headers: &req.fields, body: &req.body };
    let mut reply = req.reply.take().unwrap_or(Reply { status: 0, fields: HList::default(), body: ReplyBody::None, sent_headers: false, off: 0 });
    // A reused stream's reply keeps its buffers, not its fields.
    reply.fields.clear();
    reply.status = 0;
    reply.sent_headers = false;
    reply.off = 0;
    let mut scratch = Out::new();
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
    c.enc.encode(u64::from(id), &c.lines, &mut c.section);
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

/// Gives quinn what it will take of a response; finishes the stream once
/// it has all of it.
fn write_out(c: &mut Conn3, id: StreamId, limits: &Limits3) {
    let Some(req) = c.reqs.get_mut(&id) else { return };
    if !req.answered {
        return;
    }
    let mut s = c.q.send_stream(id);
    while req.next < 2 {
        if req.out[req.next].is_empty() {
            req.next += 1;
            continue;
        }
        match s.write_chunks(&mut req.out[req.next..]) {
            Ok(w) => {
                req.next += w.chunks;
                if w.bytes == 0 {
                    return;
                }
            }
            Err(WriteError::Blocked) => return,
            Err(_) => break,
        }
    }
    let _ = s.finish();
    if let Some(mut r) = c.reqs.remove(&id) {
        r.reset(limits);
        if c.pool.len() < 64 {
            c.pool.push(r);
        }
    }
}
