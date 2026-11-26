//! The HTTP/2 connection engine, sans I/O (DESIGN.md, "HTTP/2").
//!
//! Frames are read by verilith-h2's verified parser and written by its
//! verified serializer; header blocks are decoded by verilith-hpack's
//! verified decoder, whose split-invariance theorem is what CONTINUATION
//! needs. This file is the connection layer on top: stream states,
//! flow control, SETTINGS, and scheduling. It is not yet verified (that is
//! DESIGN.md's milestone 6); it is tested in `tests/h2.rs`.
//!
//! Responses are encoded with HPACK representations that need no dynamic
//! table on the encoder's side: `:status` from the static table, and
//! literals without indexing for the rest. A verified encoder with a
//! dynamic table is being written in verilith-hpack and will replace this.
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use verilith_h2::{Frame, Parsed};
use verilith_hpack::{Decoder, Feed};
use verilith_http::Header;
use verilith_http::parse::Span;

use crate::h1::{Ctx, Next, Out};
use crate::{Handler, Request, Response};

pub const PREFACE: &[u8; 24] = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";

// Error codes (§7).
const NO_ERROR: u32 = 0x0;
const PROTOCOL_ERROR: u32 = 0x1;
const FLOW_CONTROL_ERROR: u32 = 0x3;
const STREAM_CLOSED: u32 = 0x5;
const FRAME_SIZE_ERROR: u32 = 0x6;
const REFUSED_STREAM: u32 = 0x7;
const COMPRESSION_ERROR: u32 = 0x9;
const ENHANCE_YOUR_CALM: u32 = 0xb;

// Settings (§6.5.2).
const S_HEADER_TABLE_SIZE: u16 = 0x1;
const S_ENABLE_PUSH: u16 = 0x2;
const S_MAX_CONCURRENT_STREAMS: u16 = 0x3;
const S_INITIAL_WINDOW_SIZE: u16 = 0x4;
const S_MAX_FRAME_SIZE: u16 = 0x5;

const MAX_WINDOW: i64 = (1 << 31) - 1;

/// Limits on one HTTP/2 connection.
#[derive(Clone, Copy, Debug)]
pub struct Limits2 {
    pub max_streams: u32,
    /// The receive window advertised for each stream, and for the
    /// connection.
    pub window: u32,
    /// Largest header block (all its fragments, and decoded fields).
    pub max_header_block: usize,
    /// Largest request body buffered for a handler.
    pub max_body: usize,
    /// Control frames (PING, SETTINGS, RST_STREAM, empty frames) a peer may
    /// send per request before the connection is closed with
    /// ENHANCE_YOUR_CALM: the flood defences of DESIGN.md.
    pub control_per_request: u32,
}

impl Default for Limits2 {
    fn default() -> Self {
        Limits2 { max_streams: 256, window: 1 << 20, max_header_block: 64 * 1024, max_body: 1 << 20, control_per_request: 100 }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum St {
    /// Receiving the request (open).
    Open,
    /// The request is complete (half-closed remote); the response is
    /// being sent.
    HalfClosed,
}

struct Stream {
    st: St,
    /// The decoded header fields, as spans into `arena`.
    arena: Vec<u8>,
    fields: Vec<Header>,
    body: Vec<u8>,
    /// What we may still send on this stream.
    send_window: i64,
    /// Bytes received on this stream since our last WINDOW_UPDATE for it.
    unacked: u32,
    /// The response: an encoded header block, and a body to send.
    reply: Option<Reply>,
}

/// A response waiting to be framed.
pub struct Reply {
    pub(crate) block: Vec<u8>,
    pub(crate) body: ReplyBody,
    pub(crate) sent_headers: bool,
    pub(crate) off: usize,
}

pub(crate) enum ReplyBody {
    None,
    Owned(Vec<u8>),
    Shared(Arc<[u8]>),
}

impl ReplyBody {
    fn bytes(&self) -> &[u8] {
        match self {
            ReplyBody::None => &[],
            ReplyBody::Owned(v) => v,
            ReplyBody::Shared(a) => a,
        }
    }
}

/// A header block being received (HEADERS then CONTINUATION).
struct Block {
    stream: u32,
    end_stream: bool,
    len: usize,
}

pub struct Conn2 {
    rbuf: Vec<u8>,
    start: usize,
    end: usize,
    preface: bool,
    out: Out,
    dec: Decoder,
    streams: HashMap<u32, Stream>,
    /// Streams with a response to send, in round-robin order.
    ready: VecDeque<u32>,
    /// The highest client stream opened.
    last_stream: u32,
    block: Option<Block>,
    /// Peer settings.
    peer_max_frame: u32,
    peer_initial_window: i64,
    /// What we may still send on the connection.
    conn_send_window: i64,
    /// Received on the connection since our last WINDOW_UPDATE.
    conn_unacked: u32,
    /// Flood accounting: control frames received, and requests handled.
    control: u64,
    requests: u64,
    closing: bool,
    limits: Limits2,
}

impl Conn2 {
    pub fn new(limits: Limits2) -> Conn2 {
        let mut c = Conn2 {
            rbuf: vec![0; 64 * 1024],
            start: 0,
            end: 0,
            preface: false,
            out: Out::new(),
            dec: Decoder::new().expect("HPACK tables"),
            streams: HashMap::new(),
            ready: VecDeque::new(),
            last_stream: 0,
            block: None,
            peer_max_frame: 16384,
            peer_initial_window: 65535,
            conn_send_window: 65535,
            conn_unacked: 0,
            control: 0,
            requests: 0,
            closing: false,
            limits,
        };
        // Our SETTINGS, then a connection WINDOW_UPDATE up to our window.
        let params = [
            verilith_h2::Setting { id: S_MAX_CONCURRENT_STREAMS, value: limits.max_streams },
            verilith_h2::Setting { id: S_INITIAL_WINDOW_SIZE, value: limits.window },
            verilith_h2::Setting { id: S_ENABLE_PUSH, value: 0 },
        ];
        let before = c.out.buf.len();
        let _ = verilith_h2::serialize_settings(&params, 16384, &mut c.out.buf);
        if limits.window > 65535 {
            let _ = verilith_h2::serialize(
                &Frame::WindowUpdate { stream: 0, increment: limits.window - 65535 },
                16384,
                &mut c.out.buf,
            );
        }
        c.out.grew(before);
        c
    }

    pub fn read_buf(&mut self) -> &mut [u8] {
        if self.closing || self.out.queued > 1 << 20 {
            return &mut [];
        }
        if self.start > 0 && (self.end == self.rbuf.len() || self.start == self.end) {
            self.rbuf.copy_within(self.start..self.end, 0);
            self.end -= self.start;
            self.start = 0;
        }
        if self.end == self.rbuf.len() && self.rbuf.len() < 16384 + 9 + 64 * 1024 {
            self.rbuf.resize(self.rbuf.len() + 16384 + 9, 0);
        }
        &mut self.rbuf[self.end..]
    }

    pub fn filled(&mut self, n: usize) {
        self.end += n;
    }

    pub fn eof(&mut self) {
        self.closing = true;
    }

    pub fn closing(&self) -> bool {
        self.closing
    }

    pub fn pending<'a>(&'a self, out: &mut [&'a [u8]]) -> usize {
        self.out.slices(out)
    }

    pub fn pending_len(&self) -> usize {
        self.out.queued
    }

    pub fn wrote(&mut self, n: usize) {
        self.out.advance(n);
    }

    fn goaway(&mut self, code: u32) {
        if self.closing {
            return;
        }
        let before = self.out.buf.len();
        let _ = verilith_h2::serialize(
            &Frame::GoAway { last_stream: self.last_stream, code, debug: &[] },
            16384,
            &mut self.out.buf,
        );
        self.out.grew(before);
        self.closing = true;
    }

    fn frame(&mut self, f: &Frame) {
        let before = self.out.buf.len();
        let _ = verilith_h2::serialize(f, self.peer_max_frame, &mut self.out.buf);
        self.out.grew(before);
    }

    fn rst(&mut self, stream: u32, code: u32) {
        self.frame(&Frame::RstStream { stream, code });
        self.streams.remove(&stream);
    }

    /// Handles every complete frame read, then frames as much response data
    /// as the flow-control windows allow.
    pub fn process<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) -> Next {
        if !self.preface {
            let have = self.end - self.start;
            let n = have.min(PREFACE.len());
            if self.rbuf[self.start..self.start + n] != PREFACE[..n] {
                self.goaway(PROTOCOL_ERROR);
                return Next::Close;
            }
            if have < PREFACE.len() {
                return Next::Read;
            }
            self.start += PREFACE.len();
            self.preface = true;
        }
        while !self.closing {
            // The frame borrows the read buffer, which the frame handlers
            // never touch: take it out of `self` meanwhile.
            let rbuf = std::mem::take(&mut self.rbuf);
            let r = match verilith_h2::parse(&rbuf[self.start..self.end], 16384) {
                Parsed::Incomplete(_) => None,
                Parsed::ConnError(code) => Some((0, Action::Conn(code))),
                Parsed::StreamError { stream, code, len } => Some((len, Action::Rst(stream, code))),
                Parsed::Frame(f, len) => Some((len, self.on_frame(f, ctx))),
            };
            self.rbuf = rbuf;
            let Some((consumed, action)) = r else { break };
            self.start += consumed;
            match action {
                Action::None => {}
                Action::Conn(code) => self.goaway(code),
                Action::Rst(s, code) => self.rst(s, code),
                Action::Dispatch(s) => self.dispatch(h, ctx, s),
            }
            if self.control > 1000 + self.requests * self.limits.control_per_request as u64 {
                self.goaway(ENHANCE_YOUR_CALM);
            }
        }
        if self.start == self.end {
            self.start = 0;
            self.end = 0;
        }
        self.schedule();
        if self.closing { Next::Close } else if self.out.queued > 1 << 20 { Next::Write } else { Next::Read }
    }

    fn on_frame(&mut self, f: Frame, _ctx: &Ctx) -> Action {
        // Inside a header block only its CONTINUATION may come (§6.10).
        if let Some(b) = &self.block {
            match f {
                Frame::Continuation { stream, .. } if stream == b.stream => {}
                _ => return Action::Conn(PROTOCOL_ERROR),
            }
        }
        match f {
            Frame::Settings { ack, params } => {
                self.control += 1;
                if ack {
                    return Action::None;
                }
                for i in 0..params.len() {
                    let p = params.get(i);
                    match p.id {
                        S_INITIAL_WINDOW_SIZE => {
                            let delta = p.value as i64 - self.peer_initial_window;
                            self.peer_initial_window = p.value as i64;
                            for s in self.streams.values_mut() {
                                s.send_window += delta;
                                if s.send_window > MAX_WINDOW {
                                    return Action::Conn(FLOW_CONTROL_ERROR);
                                }
                            }
                        }
                        S_MAX_FRAME_SIZE => self.peer_max_frame = p.value,
                        S_HEADER_TABLE_SIZE => {} // our encoder uses no dynamic table
                        _ => {}
                    }
                }
                self.frame(&Frame::Settings { ack: true, params: verilith_h2::Params::new(&[]).unwrap() });
                Action::None
            }
            Frame::Ping { ack, opaque } => {
                self.control += 1;
                if !ack {
                    self.frame(&Frame::Ping { ack: true, opaque });
                }
                Action::None
            }
            Frame::WindowUpdate { stream, increment } => {
                self.control += 1;
                if stream == 0 {
                    self.conn_send_window += increment as i64;
                    if self.conn_send_window > MAX_WINDOW {
                        return Action::Conn(FLOW_CONTROL_ERROR);
                    }
                } else if let Some(s) = self.streams.get_mut(&stream) {
                    s.send_window += increment as i64;
                    if s.send_window > MAX_WINDOW {
                        return Action::Rst(stream, FLOW_CONTROL_ERROR);
                    }
                } else if stream > self.last_stream {
                    return Action::Conn(PROTOCOL_ERROR); // idle stream (§5.1)
                }
                Action::None
            }
            Frame::Priority { stream, prio } => {
                self.control += 1;
                if prio.dependency == stream {
                    return Action::Rst(stream, PROTOCOL_ERROR); // §5.3.1
                }
                Action::None
            }
            Frame::RstStream { stream, .. } => {
                self.control += 1;
                if stream > self.last_stream {
                    return Action::Conn(PROTOCOL_ERROR);
                }
                self.streams.remove(&stream);
                Action::None
            }
            Frame::GoAway { .. } => {
                self.closing = true;
                Action::None
            }
            Frame::PushPromise { .. } => Action::Conn(PROTOCOL_ERROR), // §8.4: clients don't push
            Frame::Unknown { .. } => Action::None,
            Frame::Headers { stream, end_stream, end_headers, priority, fragment, .. } => {
                if stream % 2 == 0 {
                    return Action::Conn(PROTOCOL_ERROR);
                }
                if let Some(p) = priority {
                    if p.dependency == stream {
                        return Action::Rst(stream, PROTOCOL_ERROR);
                    }
                }
                if stream <= self.last_stream {
                    // Trailers on an open stream, or a reused ID.
                    return match self.streams.get(&stream) {
                        Some(s) if s.st == St::Open && end_stream => {
                            self.block = Some(Block { stream, end_stream, len: 0 });
                            self.header_fragment(fragment, end_headers, true)
                        }
                        Some(_) => Action::Conn(PROTOCOL_ERROR),
                        None => Action::Conn(STREAM_CLOSED),
                    };
                }
                self.last_stream = stream;
                self.block = Some(Block { stream, end_stream, len: 0 });
                let refuse = self.streams.len() as u32 >= self.limits.max_streams;
                if !refuse {
                    self.streams.insert(
                        stream,
                        Stream {
                            st: St::Open,
                            arena: Vec::new(),
                            fields: Vec::new(),
                            body: Vec::new(),
                            send_window: self.peer_initial_window,
                            unacked: 0,
                            reply: None,
                        },
                    );
                }
                let a = self.header_fragment(fragment, end_headers, false);
                if refuse && matches!(a, Action::None | Action::Dispatch(_)) && self.block.is_none() {
                    return Action::Rst(stream, REFUSED_STREAM);
                }
                a
            }
            Frame::Continuation { end_headers, fragment, stream } => {
                if self.block.as_ref().map(|b| b.stream) != Some(stream) {
                    return Action::Conn(PROTOCOL_ERROR);
                }
                self.header_fragment(fragment, end_headers, false)
            }
            Frame::Data { stream, end_stream, pad, data } => {
                let flow = data.len() as u32 + pad.map_or(0, |p| p as u32 + 1);
                self.conn_unacked += flow;
                if self.conn_unacked > self.limits.window {
                    return Action::Conn(FLOW_CONTROL_ERROR);
                }
                if self.conn_unacked >= self.limits.window / 2 {
                    let inc = self.conn_unacked;
                    self.conn_unacked = 0;
                    self.frame(&Frame::WindowUpdate { stream: 0, increment: inc });
                }
                if flow == 0 && !end_stream {
                    self.control += 1;
                }
                let max_body = self.limits.max_body;
                let window = self.limits.window;
                let Some(s) = self.streams.get_mut(&stream) else {
                    return if stream > self.last_stream { Action::Conn(PROTOCOL_ERROR) } else { Action::Rst(stream, STREAM_CLOSED) };
                };
                if s.st != St::Open {
                    return Action::Rst(stream, STREAM_CLOSED);
                }
                s.unacked += flow;
                if s.unacked > window {
                    return Action::Rst(stream, FLOW_CONTROL_ERROR);
                }
                if s.body.len() + data.len() > max_body {
                    return Action::Rst(stream, REFUSED_STREAM);
                }
                s.body.extend_from_slice(data);
                if end_stream {
                    s.st = St::HalfClosed;
                    return Action::Dispatch(stream);
                }
                if s.unacked >= window / 2 {
                    let inc = s.unacked;
                    s.unacked = 0;
                    self.frame(&Frame::WindowUpdate { stream, increment: inc });
                }
                Action::None
            }
        }
    }

    /// Feeds a header block fragment to the decoder; at the block's end,
    /// checks the fields (§8.3) and, with END_STREAM, dispatches.
    fn header_fragment(&mut self, mut frag: &[u8], end_headers: bool, trailers: bool) -> Action {
        let Some(b) = &mut self.block else { return Action::Conn(PROTOCOL_ERROR) };
        b.len += frag.len();
        if b.len > self.limits.max_header_block {
            return Action::Conn(ENHANCE_YOUR_CALM);
        }
        let stream = b.stream;
        let end_stream = b.end_stream;
        loop {
            match self.dec.feed(frag, end_headers) {
                Feed::Bad => return Action::Conn(COMPRESSION_ERROR),
                Feed::More => break,
                Feed::Final => break,
                Feed::Field(n, _never) => {
                    frag = &frag[n..];
                    if trailers {
                        continue;
                    }
                    if let Some(s) = self.streams.get_mut(&stream) {
                        let name = self.dec.name();
                        let value = self.dec.value();
                        if s.arena.len() + name.len() + value.len() > self.limits.max_header_block {
                            return Action::Conn(ENHANCE_YOUR_CALM);
                        }
                        let ns = s.arena.len();
                        s.arena.extend_from_slice(name);
                        let vs = s.arena.len();
                        s.arena.extend_from_slice(value);
                        s.fields.push(Header {
                            name: Span { start: ns, end: vs },
                            value: Span { start: vs, end: s.arena.len() },
                        });
                    }
                }
            }
        }
        if !end_headers {
            return Action::None;
        }
        self.dec.end_block();
        self.block = None;
        let Some(s) = self.streams.get_mut(&stream) else { return Action::None };
        if trailers {
            s.st = St::HalfClosed;
            return Action::Dispatch(stream);
        }
        if !request_fields_ok(&s.arena, &s.fields) {
            return Action::Rst(stream, PROTOCOL_ERROR);
        }
        if end_stream {
            s.st = St::HalfClosed;
            Action::Dispatch(stream)
        } else {
            Action::None
        }
    }

    fn dispatch<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx, id: u32) {
        let Some(s) = self.streams.get_mut(&id) else { return };
        self.requests += 1;
        let a = &s.arena;
        let get = |n: &[u8]| {
            s.fields.iter().find(|f| f.name.of(a) == n).map(|f| f.value.of(a)).unwrap_or(b"")
        };
        let method = get(b":method");
        let target = get(b":path");
        let request = Request { method, target, minor: 1, buf: a, headers: &s.fields, body: &s.body };
        let mut reply = Reply { block: Vec::new(), body: ReplyBody::None, sent_headers: false, off: 0 };
        let mut scratch = Out::new();
        let mut res = Response { out: &mut scratch, ctx, sent: false, close: false, head: method == b"HEAD", h2: Some(&mut reply) };
        h.handle(&request, &mut res);
        if !res.sent {
            res.error(500);
        }
        s.reply = Some(reply);
        self.ready.push_back(id);
    }

    /// Frames responses: HEADERS, then DATA within the windows, round robin
    /// over the streams that have something to send.
    fn schedule(&mut self) {
        let max = self.peer_max_frame.min(16384) as usize;
        let mut rounds = self.ready.len();
        while rounds > 0 {
            rounds -= 1;
            let Some(id) = self.ready.pop_front() else { break };
            let Some(s) = self.streams.get_mut(&id) else { continue };
            let Some(r) = s.reply.as_mut() else { continue };
            let body_len = r.body.bytes().len();
            if !r.sent_headers {
                let end_stream = body_len == 0;
                let before = self.out.buf.len();
                // One HEADERS frame; the block is small, well under any frame size.
                let _ = verilith_h2::serialize(
                    &Frame::Headers { stream: id, end_stream, end_headers: true, pad: None, priority: None, fragment: &r.block },
                    self.peer_max_frame,
                    &mut self.out.buf,
                );
                self.out.grew(before);
                r.sent_headers = true;
                if end_stream {
                    self.streams.remove(&id);
                    continue;
                }
            }
            // DATA frames, as many as the windows allow now.
            loop {
                let left = body_len - r.off;
                let n = left.min(max).min(self.conn_send_window.max(0) as usize).min(s.send_window.max(0) as usize);
                if n == 0 {
                    break;
                }
                let end = n == left;
                let head = verilith_h2::encode_head(n as u32, 0, if end { 1 } else { 0 }, id).unwrap();
                self.out.extend(&head);
                match &r.body {
                    ReplyBody::Shared(a) if n >= 1024 => self.out.share_range(a.clone(), r.off, n),
                    b => {
                        let bytes = &b.bytes()[r.off..r.off + n];
                        self.out.extend(bytes);
                    }
                }
                r.off += n;
                self.conn_send_window -= n as i64;
                s.send_window -= n as i64;
                if end {
                    break;
                }
            }
            if r.off == body_len {
                self.streams.remove(&id);
            } else if s.send_window > 0 && self.conn_send_window > 0 {
                self.ready.push_back(id);
            } else {
                // Blocked on a window: retried when a WINDOW_UPDATE arrives.
                self.ready.push_back(id);
                if self.conn_send_window <= 0 {
                    break;
                }
            }
        }
    }
}

enum Action {
    None,
    Conn(u32),
    Rst(u32, u32),
    Dispatch(u32),
}

/// RFC 9113 §8.3: pseudo-header fields first, exactly one each of
/// `:method`, `:scheme` and `:path` (`:authority` optional; CONNECT is not
/// supported), no other pseudo-headers, no uppercase names, and no
/// connection-specific fields (§8.2.2).
fn request_fields_ok(a: &[u8], fields: &[Header]) -> bool {
    let (mut m, mut s, mut p, mut au) = (0, 0, 0, 0);
    let mut regular = false;
    for f in fields {
        let n = f.name.of(a);
        let v = f.value.of(a);
        if n.is_empty() || n.iter().any(|c| c.is_ascii_uppercase()) {
            return false;
        }
        if v.iter().any(|&c| c == 0 || c == b'\r' || c == b'\n') {
            return false;
        }
        if n[0] == b':' {
            if regular {
                return false;
            }
            match n {
                b":method" => m += 1,
                b":scheme" => s += 1,
                b":path" => {
                    if v.is_empty() {
                        return false;
                    }
                    p += 1
                }
                b":authority" => au += 1,
                _ => return false,
            }
        } else {
            regular = true;
            if matches!(n, b"connection" | b"keep-alive" | b"proxy-connection" | b"transfer-encoding" | b"upgrade") {
                return false;
            }
            if n == b"te" && v != b"trailers" {
                return false;
            }
        }
    }
    m == 1 && s == 1 && p == 1 && au <= 1
}

/// HPACK for a response head without an encoder-side dynamic table:
/// `:status` indexed when the static table has it (RFC 7541 Appendix A),
/// everything else a literal without indexing (§6.2.2) with a new,
/// lowercased name.
pub(crate) fn encode_head(out: &mut Vec<u8>, status: u16, fields: &[(&[u8], &[u8])], extra: &[u8]) {
    match status {
        200 => out.push(0x80 | 8),
        204 => out.push(0x80 | 9),
        206 => out.push(0x80 | 10),
        304 => out.push(0x80 | 11),
        400 => out.push(0x80 | 12),
        404 => out.push(0x80 | 13),
        500 => out.push(0x80 | 14),
        _ => {
            out.push(0x08); // literal without indexing, name = static 8 (:status)
            out.push(3);
            out.extend_from_slice(&[b'0' + (status / 100) as u8, b'0' + (status / 10 % 10) as u8, b'0' + (status % 10) as u8]);
        }
    }
    for (n, v) in fields {
        out.push(0x00);
        hpack_int(out, 0, 7, n.len());
        out.extend(n.iter().map(|c| c.to_ascii_lowercase()));
        hpack_int(out, 0, 7, v.len());
        out.extend_from_slice(v);
    }
    out.extend_from_slice(extra);
}

/// An HPACK integer (RFC 7541 §5.1) with an `n`-bit prefix, OR-ed into the
/// first byte's high bits `hi`.
fn hpack_int(out: &mut Vec<u8>, hi: u8, n: u32, mut v: usize) {
    let max = (1usize << n) - 1;
    if v < max {
        out.push(hi | v as u8);
        return;
    }
    out.push(hi | max as u8);
    v -= max;
    while v >= 128 {
        out.push((v % 128 + 128) as u8);
        v /= 128;
    }
    out.push(v as u8);
}

/// `extra` for [`encode_head`]: a field list encoded once.
pub(crate) fn encode_fields(fields: &[(&[u8], &[u8])]) -> Vec<u8> {
    let mut out = Vec::new();
    for (n, v) in fields {
        out.push(0x00);
        hpack_int(&mut out, 0, 7, n.len());
        out.extend(n.iter().map(|c| c.to_ascii_lowercase()));
        hpack_int(&mut out, 0, 7, v.len());
        out.extend_from_slice(v);
    }
    out
}
