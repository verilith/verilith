//! The HTTP/2 connection engine, sans I/O (DESIGN.md, "HTTP/2").
//!
//! Frames are read by verilith-h2's verified parser and written by its
//! verified serializer; header blocks are decoded by verilith-hpack's
//! verified decoder, whose split-invariance theorem is what CONTINUATION
//! needs. Every decision about a frame is made by the verified core in
//! `h2core.rs`: stream states and the stream table, flow control, SETTINGS,
//! GOAWAY, header block sequencing and the flood budget, with the control
//! frames they call for. This file is the plain-Rust part around it: the
//! read buffer, feeding fragments to the HPACK decoder and collecting the
//! fields, buffering bodies, running handlers, and framing responses
//! (`schedule`). It is tested in `tests/h2.rs`.
//!
//! Response heads are encoded by verilith-hpack's verified encoder, with
//! its dynamic table: its theorem is that each block decodes, from the
//! peer's decoder state, to exactly the fields given. That holds only if
//! blocks reach the peer in the order they were encoded, so a head is
//! encoded when its HEADERS frame is written (`schedule`), not when the
//! handler answers: a stream reset in between never touches the table.
use std::collections::VecDeque;
use std::hash::Hasher;
use std::sync::Arc;

use verilith_h2::{Frame, Parsed};
use verilith_hpack::{Decoder, Encoder, Feed, Header as HHeader};
use verilith_http::Header;
use verilith_http::parse::Span;

pub use crate::h2core::Limits2;
use crate::h2core::{Core, Step, Store, COMPRESSION_ERROR, ENHANCE_YOUR_CALM, INTERNAL_ERROR, PROTOCOL_ERROR, S_HEADER_TABLE_SIZE};
use crate::h1::{Ctx, Next, Out};
use crate::{Handler, Request, Response};

pub const PREFACE: &[u8; 24] = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";

/// A stream's buffers; its state and windows are the core's.
struct Stream {
    /// The decoded header fields, as spans into `arena`.
    arena: Vec<u8>,
    fields: Vec<Header>,
    body: Vec<u8>,
    /// The response: an encoded header block, and a body to send.
    reply: Option<Reply>,
}

impl Store for Box<Stream> {
    fn fresh() -> Self {
        Box::new(Stream { arena: Vec::new(), fields: Vec::new(), body: Vec::new(), reply: None })
    }

    fn recycle(&mut self) {
        self.arena.clear();
        self.fields.clear();
        self.body.clear();
        if let Some(r) = self.reply.as_mut() {
            r.fields.clear();
            // An owned body keeps its buffer for the next reply.
            match &mut r.body {
                ReplyBody::Owned(v) if v.capacity() <= 16 * 1024 => v.clear(),
                b => *b = ReplyBody::None,
            }
        }
    }
}

/// A response waiting to be framed.
pub struct Reply {
    pub(crate) status: u16,
    pub(crate) fields: HList,
    pub(crate) body: ReplyBody,
    pub(crate) sent_headers: bool,
    pub(crate) off: usize,
}

pub(crate) enum ReplyBody {
    None,
    Owned(Vec<u8>),
    Shared(Arc<[u8]>),
    /// `len` bytes of a shared body from `start` (a range request).
    Slice(Arc<[u8]>, usize, usize),
}

impl ReplyBody {
    fn bytes(&self) -> &[u8] {
        match self {
            ReplyBody::None => &[],
            ReplyBody::Owned(v) => v,
            ReplyBody::Shared(a) => a,
            ReplyBody::Slice(a, start, len) => &a[*start..*start + *len],
        }
    }
}

pub struct Conn2 {
    rbuf: Vec<u8>,
    start: usize,
    end: usize,
    preface: bool,
    out: Out,
    dec: Decoder,
    enc: Encoder,
    /// Scratch for one encoded header block.
    hbuf: Vec<u8>,
    /// The allocation of the field list handed to the HPACK encoder, kept
    /// empty between responses so that framing one allocates nothing.
    hs_spare: Vec<HHeader<'static>>,
    /// The verified connection state: streams, windows, settings, budget.
    core: Core<Box<Stream>>,
    /// Streams with a response to send, in round-robin order, with the
    /// slot each was in (a hint: slots move when the table is compacted).
    ready: VecDeque<(u32, usize)>,
    max_header_block: usize,
    /// Requests are being read from 0-RTT data (set by the TLS layer).
    pub(crate) early: bool,
    /// The TLS client's certificate (DER), if it authenticated.
    pub(crate) peer: Option<std::sync::Arc<[u8]>>,
}

impl Conn2 {
    pub fn new(limits: Limits2) -> Conn2 {
        let mut out = Out::new();
        let before = out.buf.len();
        // Our SETTINGS, then a connection WINDOW_UPDATE up to our window.
        let core = Core::new(limits, &mut out.buf);
        out.grew(before);
        Conn2 {
            rbuf: vec![0; 64 * 1024],
            start: 0,
            end: 0,
            preface: false,
            out,
            dec: Decoder::new().expect("HPACK tables"),
            enc: Encoder::new().expect("HPACK tables"),
            hbuf: Vec::new(),
            hs_spare: Vec::new(),
            core,
            ready: VecDeque::new(),
            max_header_block: limits.max_header_block,
            early: false,
            peer: None,
        }
    }

    pub fn read_buf(&mut self) -> &mut [u8] {
        if self.core.closing() || self.out.queued > 1 << 20 {
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
        self.core.eof();
    }

    pub fn closing(&self) -> bool {
        self.core.closing()
    }

    pub fn pending<'a>(&'a self, out: &mut [&'a [u8]]) -> usize {
        self.out.slices(out)
    }

    pub fn pending_io<'a>(&'a self, out: &mut [&'a [u8]], more: &mut bool) -> crate::h1::Io<'a> {
        self.out.slices_io(out, more)
    }

    pub fn pending_len(&self) -> usize {
        self.out.queued
    }

    pub fn wrote(&mut self, n: usize) {
        self.out.advance(n);
    }

    fn conn_error(&mut self, code: u32) {
        let before = self.out.buf.len();
        self.core.conn_error(code, &mut self.out.buf);
        self.out.grew(before);
    }

    /// Handles every complete frame read, then frames as much response data
    /// as the flow-control windows allow.
    pub fn process<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) -> Next {
        if !self.preface {
            let have = self.end - self.start;
            let n = have.min(PREFACE.len());
            if self.rbuf[self.start..self.start + n] != PREFACE[..n] {
                self.conn_error(PROTOCOL_ERROR);
                return Next::Close;
            }
            if have < PREFACE.len() {
                return Next::Read;
            }
            self.start += PREFACE.len();
            self.preface = true;
        }
        while !self.core.closing() {
            // The frame borrows the read buffer, which the frame handlers
            // never touch: take it out of `self` meanwhile.
            let rbuf = std::mem::take(&mut self.rbuf);
            let consumed = match verilith_h2::parse(&rbuf[self.start..self.end], 16384) {
                Parsed::Incomplete(_) => None,
                Parsed::ConnError(code) => {
                    self.conn_error(code);
                    Some(0)
                }
                Parsed::StreamError { stream, code, len } => {
                    let before = self.out.buf.len();
                    self.core.stream_error(stream, code, &mut self.out.buf);
                    self.out.grew(before);
                    Some(len)
                }
                Parsed::Frame(f, len) => {
                    self.frame(&f, h, ctx);
                    Some(len)
                }
            };
            self.rbuf = rbuf;
            let Some(consumed) = consumed else { break };
            self.start += consumed;
        }
        if self.start == self.end {
            self.start = 0;
            self.end = 0;
        }
        self.schedule(ctx);
        if self.core.closing() { Next::Close } else if self.out.queued > 1 << 20 { Next::Write } else { Next::Read }
    }

    /// One frame: the core's decision, then what it leaves to do.
    fn frame<H: Handler + ?Sized>(&mut self, f: &Frame, h: &H, ctx: &Ctx) {
        let before = self.out.buf.len();
        let step = self.core.on_frame(f, &mut self.out.buf);
        self.out.grew(before);
        match step {
            Step::None => {}
            Step::Settings => {
                if let Frame::Settings { params, .. } = f {
                    for i in 0..params.len() {
                        let p = params.get(i);
                        // The encoder keeps to min(this, its 4096-byte
                        // target) and signals any shrink at the next block
                        // (RFC 7541 §4.2).
                        if p.id == S_HEADER_TABLE_SIZE {
                            self.enc.change_settings(p.value);
                        }
                    }
                }
            }
            Step::Fragment { frag, end_headers, keep } => {
                if let Some(at) = self.header_fragment(frag, end_headers, keep) {
                    self.dispatch(h, ctx, at);
                }
            }
            Step::Data { at, data, end } => {
                if let Some(s) = self.core.val(at) {
                    s.body.extend_from_slice(data);
                }
                if end {
                    self.dispatch(h, ctx, at);
                }
            }
            Step::Dispatch { at } => self.dispatch(h, ctx, at),
        }
    }

    /// Feeds a header block fragment to the decoder, keeping the fields on
    /// the stream in slot `keep`; at the block's end, checks them (§8.3)
    /// and tells the core, which may complete the request: the slot of a
    /// request to dispatch.
    fn header_fragment(&mut self, mut frag: &[u8], end_headers: bool, keep: Option<usize>) -> Option<usize> {
        let max_block = self.max_header_block;
        // The stream the fields go to, looked up once per fragment.
        let mut to = match keep {
            Some(at) => self.core.val(at),
            None => None,
        };
        let mut err = 0;
        loop {
            match self.dec.feed(frag, end_headers) {
                Feed::Bad => {
                    err = COMPRESSION_ERROR;
                    break;
                }
                Feed::More => break,
                Feed::Final => break,
                Feed::Field(n, _never) => {
                    frag = &frag[n..];
                    if let Some(s) = to.as_deref_mut() {
                        let name = self.dec.name();
                        let value = self.dec.value();
                        if s.arena.len() + name.len() + value.len() > max_block {
                            err = ENHANCE_YOUR_CALM;
                            break;
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
        let ok = match (end_headers, to) {
            (true, Some(s)) => request_fields_ok(&s.arena, &s.fields),
            _ => true,
        };
        if err != 0 {
            self.conn_error(err);
            return None;
        }
        if !end_headers {
            return None;
        }
        self.dec.end_block();
        let before = self.out.buf.len();
        let step = self.core.end_block(ok, &mut self.out.buf);
        self.out.grew(before);
        match step {
            Step::Dispatch { at } => Some(at),
            _ => None,
        }
    }

    fn dispatch<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx, at: usize) {
        let id = self.core.id(at);
        let early = self.early;
        let peer = self.peer.as_deref();
        let Some(s) = self.core.val(at) else { return };
        let a = &s.arena;
        let get = |n: &[u8]| {
            s.fields.iter().find(|f| f.name.of(a) == n).map(|f| f.value.of(a)).unwrap_or(b"")
        };
        let method = get(b":method");
        let target = get(b":path");
        let request = Request { method, target, minor: 1, buf: a, headers: &s.fields, body: &s.body, early, peer };
        // A reused stream keeps its reply's buffers (cleared on close).
        let mut reply = s.reply.take().unwrap_or(Reply { status: 0, fields: HList::default(), body: ReplyBody::None, sent_headers: false, off: 0 });
        reply.sent_headers = false;
        reply.off = 0;
        let mut scratch = crate::out::Wire::empty();
        let mut res = Response { out: &mut scratch, ctx, sent: false, close: false, head: method == b"HEAD", h2: Some(&mut reply) };
        if crate::early::too_early(early, method) {
            res.too_early();
        } else {
            h.handle(&request, &mut res);
        }
        if !res.sent {
            res.error(500);
        }
        s.reply = Some(reply);
        self.ready.push_back((id, at));
    }

    fn finish(&mut self, at: usize) {
        let before = self.out.buf.len();
        self.core.finish(at, &mut self.out.buf);
        self.out.grew(before);
    }

    /// Frames responses: HEADERS, then DATA within the windows, round robin
    /// over the streams that have something to send. The reply stays in
    /// its stream (moving it costs store-forwarding stalls); it is looked
    /// up again around each charge to the core's windows.
    fn schedule(&mut self, ctx: &Ctx) {
        let peer_max = self.core.max_frame();
        let max = peer_max.min(16384) as usize;
        let mut rounds = self.ready.len();
        while rounds > 0 {
            rounds -= 1;
            let Some((id, hint)) = self.ready.pop_front() else { break };
            let Some(at) = self.core.locate(id, hint) else { continue };
            let Some(r) = self.core.val(at).and_then(|s| s.reply.as_mut()) else { continue };
            let body_len = r.body.bytes().len();
            if !r.sent_headers {
                let end_stream = body_len == 0;
                let st = [b'0' + (r.status / 100) as u8, b'0' + (r.status / 10 % 10) as u8, b'0' + (r.status % 10) as u8];
                // The spare allocation, retyped for this block's borrows
                // (an empty Vec collected in place keeps its buffer).
                let mut hs: Vec<HHeader> = std::mem::take(&mut self.hs_spare).into_iter().collect();
                hs.reserve(r.fields.len() + ctx.own_h2.len() + 1);
                hs.push(HHeader { name: b":status", value: &st, sensitive: false });
                for (n, v) in r.fields.iter().chain(ctx.own_h2.iter()) {
                    // A cookie is a secret an attacker could probe by
                    // compression (RFC 7541 §7.1.3): never indexed.
                    hs.push(HHeader { name: n, value: v, sensitive: n == b"set-cookie" });
                }
                self.hbuf.clear();
                let ok = self.enc.encode(&hs, &mut self.hbuf);
                hs.clear();
                self.hs_spare = hs.into_iter().map(|_| HHeader { name: b"", value: b"", sensitive: false }).collect();
                r.sent_headers = true;
                if !ok {
                    // A name or value over 64 KiB: nothing was encoded, the
                    // table is unchanged.
                    let before = self.out.buf.len();
                    self.core.reset(at, INTERNAL_ERROR, &mut self.out.buf);
                    self.out.grew(before);
                    continue;
                }
                let before = self.out.buf.len();
                // HEADERS, then CONTINUATION, within the peer's frame size.
                let mut frag: &[u8] = &self.hbuf;
                let mut first = true;
                loop {
                    let k = frag.len().min(max);
                    let (a, b) = frag.split_at(k);
                    let last = b.is_empty();
                    let f = if first {
                        Frame::Headers { stream: id, end_stream, end_headers: last, pad: None, priority: None, fragment: a }
                    } else {
                        Frame::Continuation { stream: id, end_headers: last, fragment: a }
                    };
                    let _ = verilith_h2::serialize(&f, peer_max, &mut self.out.buf);
                    first = false;
                    frag = b;
                    if last {
                        break;
                    }
                }
                self.out.grew(before);
                if end_stream {
                    self.finish(at);
                    continue;
                }
            }
            // DATA frames, as many as the windows allow now.
            let mut done = false;
            loop {
                let Some(r) = self.core.val(at).and_then(|s| s.reply.as_mut()) else { break };
                let left = body_len - r.off;
                let n = self.core.take(at, left, max);
                if n == 0 {
                    break;
                }
                let Some(r) = self.core.val(at).and_then(|s| s.reply.as_mut()) else { break };
                let end = n == left;
                let head = verilith_h2::encode_head(n as u32, 0, if end { 1 } else { 0 }, id).unwrap();
                self.out.extend(&head);
                match &r.body {
                    ReplyBody::Shared(a) if n >= 1024 => self.out.share_range(a.clone(), r.off, n),
                    ReplyBody::Slice(a, start, _) if n >= 1024 => self.out.share_range(a.clone(), start + r.off, n),
                    b => {
                        let bytes = &b.bytes()[r.off..r.off + n];
                        self.out.extend(bytes);
                    }
                }
                r.off += n;
                if end {
                    done = true;
                    break;
                }
            }
            if done {
                self.finish(at);
            } else {
                // Blocked on a window: retried when a WINDOW_UPDATE arrives.
                self.ready.push_back((id, at));
                if self.core.conn_avail() == 0 {
                    break;
                }
            }
        }
    }
}

/// RFC 9113 §8.3: pseudo-header fields first, exactly one each of
/// `:method`, `:scheme` and `:path` (`:authority` optional; CONNECT is not
/// supported), no other pseudo-headers, no uppercase names, and no
/// connection-specific fields (§8.2.2).
pub(crate) fn request_fields_ok(a: &[u8], fields: &[Header]) -> bool {
    let (mut m, mut s, mut p, mut au) = (0, 0, 0, 0);
    let mut regular = false;
    for f in fields {
        let n = f.name.of(a);
        let v = f.value.of(a);
        if n.is_empty() || verilith_core::scan::any_upper(n) {
            return false;
        }
        if verilith_core::scan::any_nul_cr_lf(v) {
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

/// Header fields, owned: lowercased names (RFC 9113 §8.2.1) and values,
/// back to back in one buffer.
#[derive(Clone, Default, Debug)]
pub(crate) struct HList {
    bytes: Vec<u8>,
    /// Where each name and each value ends in `bytes`.
    ends: Vec<(u32, u32)>,
}

impl HList {
    pub(crate) fn clear(&mut self) {
        self.bytes.clear();
        self.ends.clear();
    }

    pub(crate) fn push(&mut self, name: &[u8], value: &[u8]) {
        self.bytes.extend(name.iter().map(|c| c.to_ascii_lowercase()));
        let n = self.bytes.len() as u32;
        self.bytes.extend_from_slice(value);
        self.ends.push((n, self.bytes.len() as u32));
    }

    pub(crate) fn extend(&mut self, o: &HList) {
        let base = self.bytes.len() as u32;
        self.bytes.extend_from_slice(&o.bytes);
        self.ends.extend(o.ends.iter().map(|&(a, b)| (a + base, b + base)));
    }

    pub(crate) fn len(&self) -> usize {
        self.ends.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&[u8], &[u8])> {
        let mut at = 0usize;
        self.ends.iter().map(move |&(n, v)| {
            let r = (&self.bytes[at..n as usize], &self.bytes[n as usize..v as usize]);
            at = v as usize;
            r
        })
    }
}

/// The hash of HTTP/3's stream maps (HTTP/2's streams are in the core's
/// sorted table): stream IDs are small integers chosen by the peer, few of
/// them live, so a multiply-and-fold suffices; SipHash cost 6% of the CPU
/// in h2c-plaintext.
#[derive(Default)]
pub(crate) struct IdHash(u64);

impl Hasher for IdHash {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, b: &[u8]) {
        for &x in b {
            self.write_u64(x as u64);
        }
    }
    fn write_u32(&mut self, x: u32) {
        self.write_u64(x as u64);
    }
    fn write_u64(&mut self, x: u64) {
        let h = (self.0 ^ x).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        self.0 = h ^ (h >> 29);
    }
}
