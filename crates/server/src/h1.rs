//! The HTTP/1.1 connection engine, sans I/O.
//!
//! [`Conn`] owns a connection's read and write buffers. The event loop puts
//! bytes into [`Conn::read_buf`], calls [`Conn::process`], and writes what
//! [`Conn::pending`] returns. Every decision about what the bytes mean is
//! made by verified code: verilith-http's head parser, framing decision and
//! chunked decoder, and [`crate::respond`]'s response writer. This file is
//! the glue that sequences them over a connection: where the next request
//! starts, when the connection must close, and in what order responses go
//! out. That sequencing is not yet verified (DESIGN.md, milestone 2); it is
//! tested in `tests/h1.rs` against every way of splitting the input.
use std::collections::VecDeque;
use std::sync::Arc;

use verilith_http::{Body, Chunked, ChunkedDecoder, Header, Status};

use crate::respond::{self, Field, Framing, Prepared};
use crate::{Handler, Request, Response};

/// Limits on one connection.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// Largest request head, and the read buffer's size.
    pub max_head: usize,
    /// Largest request body that is buffered for the handler.
    pub max_body: usize,
    /// Most field lines in a head.
    pub max_headers: usize,
    /// Stop reading while more than this many response bytes wait to be
    /// written.
    pub write_high: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits { max_head: 16 * 1024, max_body: 1 << 20, max_headers: 100, write_high: 256 * 1024 }
    }
}

/// Where a parsed head's parts are, relative to the request's start.
#[derive(Clone, Copy)]
struct HeadInfo {
    method: (usize, usize),
    target: (usize, usize),
    minor: u8,
    head_len: usize,
}

enum Phase {
    /// Waiting for (more of) a head at `start`.
    Head,
    /// A head is parsed; waiting for `need` body bytes after it.
    Length { hd: HeadInfo, need: usize },
    /// A chunked body: `out` decoded bytes after the head, and the decoder
    /// has consumed everything up to `end`.
    Chunked { hd: HeadInfo, out: usize, dec: ChunkedDecoder },
    /// The connection is closing once the write buffer drains.
    Closing,
}

/// What the event loop should do next with this connection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Next {
    /// Keep reading.
    Read,
    /// The write buffer is over its high-water mark: write before reading.
    Write,
    /// Write what is pending, then close.
    Close,
}

pub struct Conn {
    rbuf: Vec<u8>,
    /// The unprocessed bytes are `rbuf[start..end]`.
    start: usize,
    end: usize,
    /// Length of `rbuf[start..end]` at the last Partial parse.
    last_len: usize,
    phase: Phase,
    headers: Vec<Header>,
    wbuf: Out,
    sent_continue: bool,
    limits: Limits,
}

/// The server's own field lines, checked once and rebuilt when `Date`
/// changes (once a second per worker).
pub struct Ctx {
    own: Prepared,
    own_close: Prepared,
    empty: Prepared,
    /// The same fields as HPACK representations, for HTTP/2.
    pub(crate) own_h2: Vec<u8>,
}

impl Ctx {
    /// `None` if `server` or `date` is not a valid field value.
    pub fn new(server: &[u8], date: &[u8]) -> Option<Ctx> {
        let own = [Field { name: b"Server", value: server }, Field { name: b"Date", value: date }];
        let own_close = [own[0], own[1], Field { name: b"Connection", value: b"close" }];
        let own_h2 = crate::h2::encode_fields(&[(b"server", server), (b"date", date)]);
        Some(Ctx { own: Prepared::new(&own)?, own_close: Prepared::new(&own_close)?, empty: Prepared::empty(), own_h2 })
    }
}

impl Conn {
    pub fn new(limits: Limits) -> Conn {
        Conn {
            rbuf: vec![0; limits.max_head],
            start: 0,
            end: 0,
            last_len: 0,
            phase: Phase::Head,
            headers: Vec::with_capacity(16),
            wbuf: Out::new(),
            sent_continue: false,
            limits,
        }
    }

    /// Makes the connection new again, keeping its buffers.
    pub fn reset(&mut self) {
        if self.rbuf.len() > self.limits.max_head {
            self.rbuf.truncate(self.limits.max_head);
            self.rbuf.shrink_to_fit();
        }
        self.start = 0;
        self.end = 0;
        self.last_len = 0;
        self.phase = Phase::Head;
        self.headers.clear();
        self.wbuf.clear();
        self.sent_continue = false;
    }

    /// Room to read into. Empty when the connection should not read now.
    pub fn read_buf(&mut self) -> &mut [u8] {
        if matches!(self.phase, Phase::Closing) || self.wbuf.queued > self.limits.write_high {
            return &mut [];
        }
        if self.end == self.rbuf.len() && self.start > 0 {
            self.rbuf.copy_within(self.start..self.end, 0);
            self.end -= self.start;
            self.start = 0;
        }
        if self.end == self.rbuf.len() {
            // A body larger than the head buffer, buffered for the handler.
            let want = match self.phase {
                Phase::Length { hd, need } => self.start + hd.head_len + need,
                Phase::Chunked { .. } => self.rbuf.len() * 2,
                _ => self.rbuf.len(),
            };
            let cap = self.limits.max_head + self.limits.max_body;
            if want > self.rbuf.len() && self.rbuf.len() < cap {
                self.rbuf.resize(want.min(cap).max(self.rbuf.len()), 0);
            }
        }
        &mut self.rbuf[self.end..]
    }

    /// `n` bytes were read into [`Conn::read_buf`].
    pub fn filled(&mut self, n: usize) {
        self.end += n;
    }

    /// The peer closed its side: nothing more will arrive.
    pub fn eof(&mut self) {
        self.phase = Phase::Closing;
    }

    /// The bytes waiting to be written, as up to `out.len()` slices in
    /// order (for one `writev`). Returns how many slices were filled.
    pub fn pending<'a>(&'a self, out: &mut [&'a [u8]]) -> usize {
        self.wbuf.slices(out)
    }

    /// How many bytes wait to be written.
    pub fn pending_len(&self) -> usize {
        self.wbuf.queued
    }

    /// `n` bytes of [`Conn::pending`] were written.
    pub fn wrote(&mut self, n: usize) {
        self.wbuf.advance(n);
    }

    pub fn closing(&self) -> bool {
        matches!(self.phase, Phase::Closing)
    }

    /// Handles every complete request in the read buffer, appending the
    /// responses, in order, to the write buffer.
    pub fn process<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) -> Next {
        loop {
            match self.phase {
                Phase::Closing => return Next::Close,
                Phase::Head => {
                    if self.start == self.end {
                        self.start = 0;
                        self.end = 0;
                        self.last_len = 0;
                        return self.next();
                    }
                    let buf = &self.rbuf[self.start..self.end];
                    let last = if self.last_len <= buf.len() { self.last_len } else { 0 };
                    match verilith_http::parse_request_with(buf, last, self.limits.max_headers, &mut self.headers) {
                        Ok(Status::Partial) => {
                            self.last_len = buf.len();
                            if self.start == 0 && self.end == self.rbuf.len() {
                                self.error(ctx, 431, b"Request Header Fields Too Large");
                            }
                            return self.next();
                        }
                        Err(_) => {
                            self.error(ctx, 400, b"Bad Request");
                            return Next::Close;
                        }
                        Ok(Status::Complete(req)) => {
                            self.last_len = 0;
                            let base = buf.as_ptr() as usize;
                            let span = |s: &[u8]| {
                                let a = s.as_ptr() as usize - base;
                                (a, a + s.len())
                            };
                            let hd = HeadInfo {
                                method: span(req.method()),
                                target: span(req.target()),
                                minor: req.minor_version(),
                                head_len: req.head_len,
                            };
                            match req.body {
                                Body::Empty => self.dispatch(h, ctx, hd, 0),
                                Body::Length(n) => {
                                    if n > self.limits.max_body as u64 {
                                        self.error(ctx, 413, b"Content Too Large");
                                        return Next::Close;
                                    }
                                    self.phase = Phase::Length { hd, need: n as usize };
                                }
                                Body::Chunked => {
                                    self.phase = Phase::Chunked { hd, out: 0, dec: ChunkedDecoder::new() };
                                }
                                Body::Close => unreachable!("requests are never close-delimited"),
                            }
                        }
                    }
                }
                Phase::Length { hd, need } => {
                    let have = self.end - self.start - hd.head_len;
                    if have < need {
                        self.maybe_continue(ctx);
                        return self.next();
                    }
                    self.dispatch(h, ctx, hd, need);
                }
                Phase::Chunked { hd, out, mut dec } => {
                    let from = self.start + hd.head_len + out;
                    if from == self.end {
                        self.maybe_continue(ctx);
                        return self.next();
                    }
                    match dec.decode(&mut self.rbuf[from..self.end]) {
                        Err(_) => {
                            self.error(ctx, 400, b"Bad Request");
                            return Next::Close;
                        }
                        Ok(Chunked::More { out: o }) => {
                            // Everything read was consumed; new bytes go right after.
                            self.end = from + o;
                            let out = out + o;
                            if out > self.limits.max_body {
                                self.error(ctx, 413, b"Content Too Large");
                                return Next::Close;
                            }
                            self.phase = Phase::Chunked { hd, out, dec };
                            self.maybe_continue(ctx);
                            return self.next();
                        }
                        Ok(Chunked::Done { out: o, rest }) => {
                            // The body is rbuf[start+head_len..][..out+o]; the
                            // next message's `rest` bytes follow it.
                            let body = out + o;
                            self.end = from + o + rest;
                            self.dispatch(h, ctx, hd, body);
                        }
                    }
                }
            }
        }
    }

    fn next(&self) -> Next {
        if matches!(self.phase, Phase::Closing) {
            Next::Close
        } else if self.wbuf.queued > self.limits.write_high {
            Next::Write
        } else {
            Next::Read
        }
    }

    /// Sends `100 Continue` once, if the request asked for it and its body
    /// has not all arrived.
    fn maybe_continue(&mut self, _ctx: &Ctx) {
        if self.sent_continue {
            return;
        }
        let buf = &self.rbuf[self.start..self.end];
        let mut expect = false;
        for hd in &self.headers {
            if hd.name.of(buf).eq_ignore_ascii_case(b"expect") && hd.value.of(buf).eq_ignore_ascii_case(b"100-continue") {
                expect = true;
            }
        }
        if expect {
            self.wbuf.extend(b"HTTP/1.1 100 Continue\r\n\r\n");
            self.sent_continue = true;
        }
    }

    /// Runs the handler on the request at `start` (with a body of
    /// `body_len` bytes right after its head), writes its response, and
    /// moves past it.
    fn dispatch<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx, hd: HeadInfo, body_len: usize) {
        let buf = &self.rbuf[self.start..self.end];
        let keep = keep_alive(hd.minor, buf, &self.headers);
        let method = &buf[hd.method.0..hd.method.1];
        let request = Request {
            method,
            target: &buf[hd.target.0..hd.target.1],
            minor: hd.minor,
            buf,
            headers: &self.headers,
            body: &buf[hd.head_len..hd.head_len + body_len],
        };
        let mut res = Response { out: &mut self.wbuf, ctx, sent: false, close: !keep, head: method == b"HEAD", h2: None };
        h.handle(&request, &mut res);
        if !res.sent {
            res.error(500);
        }
        let close = res.close;
        self.start += hd.head_len + body_len;
        self.sent_continue = false;
        self.phase = if close { Phase::Closing } else { Phase::Head };
    }

    /// Writes an error response and marks the connection to close: after a
    /// rejected head, its length and the next request's start are unknown.
    fn error(&mut self, ctx: &Ctx, status: u16, reason: &[u8]) {
        let mut res = Response { out: &mut self.wbuf, ctx, sent: false, close: true, head: false, h2: None };
        res.send_reason(status, reason, &[], reason).ok();
        self.phase = Phase::Closing;
    }
}

/// A connection's output: owned bytes, with shared bodies (static files,
/// cached responses) spliced in without a copy. The bytes on the wire are
/// `buf[..p1] + seg1 + buf[p1..p2] + seg2 + ... + buf[pk..]`.
pub struct Out {
    pub(crate) buf: Vec<u8>,
    /// Shared bodies, each with the position in `buf` it follows.
    segs: VecDeque<(usize, Seg)>,
    /// Bytes of `buf` already written.
    pos: usize,
    /// Bytes of the front shared body already written.
    seg_off: usize,
    /// Bytes not yet written.
    pub(crate) queued: usize,
}

/// A shared body, or a range of one.
pub(crate) struct Seg {
    a: Arc<[u8]>,
    off: usize,
    len: usize,
}

impl Seg {
    fn bytes(&self) -> &[u8] {
        &self.a[self.off..self.off + self.len]
    }
}

/// Bodies at least this long are sent from the shared buffer, not copied.
pub const SHARE_MIN: usize = 8 * 1024;

impl Out {
    pub(crate) fn new() -> Out {
        Out { buf: Vec::with_capacity(4096), segs: VecDeque::new(), pos: 0, seg_off: 0, queued: 0 }
    }

    pub(crate) fn clear(&mut self) {
        self.buf.clear();
        self.segs.clear();
        self.pos = 0;
        self.seg_off = 0;
        self.queued = 0;
    }

    pub(crate) fn extend(&mut self, b: &[u8]) {
        self.buf.extend_from_slice(b);
        self.queued += b.len();
    }

    /// Call after writing directly into `buf`, with its length before.
    pub(crate) fn grew(&mut self, before: usize) {
        self.queued += self.buf.len() - before;
    }

    /// `body[off..off + n]`, shared.
    pub(crate) fn share_range(&mut self, body: Arc<[u8]>, off: usize, n: usize) {
        if off == 0 && n == body.len() {
            return self.share(body);
        }
        // A sub-range: kept as its own allocation-free view.
        self.queued += n;
        self.segs.push_back((self.buf.len(), Seg { a: body, off, len: n }));
    }

    pub(crate) fn share(&mut self, body: Arc<[u8]>) {
        self.queued += body.len();
        let len = body.len();
        self.segs.push_back((self.buf.len(), Seg { a: body, off: 0, len }));
    }

    pub(crate) fn slices<'a>(&'a self, out: &mut [&'a [u8]]) -> usize {
        let mut k = 0;
        let mut p = self.pos;
        let mut off = self.seg_off;
        for (at, seg) in &self.segs {
            if k == out.len() {
                return k;
            }
            if p < *at {
                out[k] = &self.buf[p..*at];
                k += 1;
                p = *at;
                if k == out.len() {
                    return k;
                }
            }
            if off < seg.len {
                out[k] = &seg.bytes()[off..];
                k += 1;
            }
            off = 0;
        }
        if k < out.len() && p < self.buf.len() {
            out[k] = &self.buf[p..];
            k += 1;
        }
        k
    }

    pub(crate) fn advance(&mut self, mut n: usize) {
        self.queued -= n;
        while n > 0 {
            if let Some((at, seg)) = self.segs.front() {
                if self.pos < *at {
                    let t = (*at - self.pos).min(n);
                    self.pos += t;
                    n -= t;
                    continue;
                }
                let t = (seg.len - self.seg_off).min(n);
                self.seg_off += t;
                n -= t;
                if self.seg_off == seg.len {
                    self.segs.pop_front();
                    self.seg_off = 0;
                }
            } else {
                self.pos += n;
                n = 0;
            }
        }
        // Drop finished zero-length leftovers.
        while let Some((at, seg)) = self.segs.front() {
            if self.pos >= *at && self.seg_off >= seg.len {
                self.segs.pop_front();
                self.seg_off = 0;
            } else {
                break;
            }
        }
        if self.queued == 0 {
            self.clear();
        }
    }
}

/// RFC 9112 §9.3: HTTP/1.1 persists unless `Connection: close`; HTTP/1.0
/// persists only with `Connection: keep-alive`.
fn keep_alive(minor: u8, buf: &[u8], headers: &[Header]) -> bool {
    let mut close = false;
    let mut keep = false;
    for hd in headers {
        if hd.name.of(buf).eq_ignore_ascii_case(b"connection") {
            for opt in hd.value.of(buf).split(|&c| c == b',') {
                let o = opt.trim_ascii();
                if o.eq_ignore_ascii_case(b"close") {
                    close = true;
                } else if o.eq_ignore_ascii_case(b"keep-alive") {
                    keep = true;
                }
            }
        }
    }
    if close { false } else if minor >= 1 { true } else { keep }
}

/// The reason phrase the server sends for a status code.
pub fn reason(status: u16) -> &'static [u8] {
    match status {
        100 => b"Continue",
        200 => b"OK",
        201 => b"Created",
        204 => b"No Content",
        206 => b"Partial Content",
        301 => b"Moved Permanently",
        302 => b"Found",
        304 => b"Not Modified",
        400 => b"Bad Request",
        403 => b"Forbidden",
        404 => b"Not Found",
        405 => b"Method Not Allowed",
        413 => b"Content Too Large",
        416 => b"Range Not Satisfiable",
        431 => b"Request Header Fields Too Large",
        500 => b"Internal Server Error",
        501 => b"Not Implemented",
        503 => b"Service Unavailable",
        _ => b"",
    }
}

fn fmt_len(b: &mut [u8; 20], mut n: usize) -> &[u8] {
    let mut i = 20;
    loop {
        i -= 1;
        b[i] = b'0' + (n % 10) as u8;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    &b[i..]
}

/// Field lines a route sends with every response, checked once: for
/// HTTP/1.1 as verified prepared lines, for HTTP/2 as HPACK.
pub struct Fields {
    pub(crate) h1: Prepared,
    pub(crate) h2: Vec<u8>,
}

impl Fields {
    /// `None` if a name or value is not allowed (see [`SendError::Invalid`]).
    pub fn new(fields: &[Field]) -> Option<Fields> {
        let h1 = Prepared::new(fields)?;
        let v: Vec<(&[u8], &[u8])> = fields.iter().map(|f| (f.name, f.value)).collect();
        Some(Fields { h1, h2: crate::h2::encode_fields(&v) })
    }
}

/// 1xx, 204 and 304 responses have no body (RFC 9112 §6.3).
fn no_body(status: u16) -> bool {
    (100..200).contains(&status) || status == 204 || status == 304
}

/// Why [`Response::send`] refused a response.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SendError {
    /// A response was already sent for this request.
    AlreadySent,
    /// The status is not three digits, or a field name or value is not
    /// allowed (`respond::name_ok`, `value_ok`): CR, LF, NUL, a non-token
    /// name, or Content-Length/Transfer-Encoding, which the server writes.
    Invalid,
}

impl<'a> Response<'a> {
    /// Sends a complete response with a body of known length. The bytes
    /// written are proven to parse back (by verilith-http's specification) to
    /// this status, the server's fields, `fields`, and a Content-Length
    /// of `body.len()`; the body follows, except for HEAD.
    pub fn send(&mut self, status: u16, fields: &[Field], body: &[u8]) -> Result<(), SendError> {
        self.send_reason(status, reason(status), fields, body)
    }

    /// [`Response::send`] with a body that is shared, not copied: a long
    /// one is written straight from `body` with `writev`.
    pub fn send_shared(&mut self, status: u16, fields: &[Field], body: &Arc<[u8]>) -> Result<(), SendError> {
        if body.len() < SHARE_MIN {
            return self.send(status, fields, body);
        }
        self.head_only(status, reason(status), None, fields, body.len())?;
        self.body_share(status, body);
        Ok(())
    }

    fn head_only(&mut self, status: u16, reason: &[u8], pre: Option<&Fields>, fields: &[Field], len: usize) -> Result<(), SendError> {
        if self.sent {
            return Err(SendError::AlreadySent);
        }
        if let Some(r) = self.h2.as_deref_mut() {
            // HTTP/2: the same checks, then HPACK (no Connection field: §8.2.2).
            if !(100..=999).contains(&status) || !respond::check_fields(fields) {
                return Err(SendError::Invalid);
            }
            let mut v: Vec<(&[u8], &[u8])> = Vec::with_capacity(fields.len() + 1);
            for f in fields {
                v.push((f.name, f.value));
            }
            let mut extra = self.ctx.own_h2.clone();
            if let Some(p) = pre {
                extra.extend_from_slice(&p.h2);
            }
            let mut cl = [0u8; 20];
            let cls = fmt_len(&mut cl, len);
            if !no_body(status) {
                v.push((b"content-length", cls));
            }
            crate::h2::encode_head(&mut r.block, status, &v, &extra);
            self.sent = true;
            return Ok(());
        }
        let pre = pre.map(|p| &p.h1);
        let framing = if no_body(status) { Framing::Neither } else { Framing::Length(len as u64) };
        let own = if self.close { &self.ctx.own_close } else { &self.ctx.own };
        let pre = pre.unwrap_or(&self.ctx.empty);
        let before = self.out.buf.len();
        let ok = respond::write_head_prepared(&mut self.out.buf, status, reason, own, pre, fields, framing);
        self.out.grew(before);
        if !ok {
            return Err(SendError::Invalid);
        }
        self.sent = true;
        Ok(())
    }

    /// [`Response::send`] with a route's fixed fields checked in advance
    /// ([`Prepared::new`]): the fast path.
    pub fn send_prepared(&mut self, status: u16, fields: &Fields, body: &[u8]) -> Result<(), SendError> {
        self.head_only(status, reason(status), Some(fields), &[], body.len())?;
        self.body_copy(status, body);
        Ok(())
    }

    fn body_copy(&mut self, status: u16, body: &[u8]) {
        if no_body(status) || self.head {
            return;
        }
        match self.h2.as_deref_mut() {
            Some(r) => r.body = crate::h2::ReplyBody::Owned(body.to_vec()),
            None => self.out.extend(body),
        }
    }

    fn body_share(&mut self, status: u16, body: &Arc<[u8]>) {
        if no_body(status) || self.head {
            return;
        }
        match self.h2.as_deref_mut() {
            Some(r) => r.body = crate::h2::ReplyBody::Shared(body.clone()),
            None => self.out.share(body.clone()),
        }
    }

    /// [`Response::send_shared`] with prepared fields.
    pub fn send_shared_prepared(&mut self, status: u16, fields: &Fields, body: &Arc<[u8]>) -> Result<(), SendError> {
        if body.len() < SHARE_MIN {
            return self.send_prepared(status, fields, body);
        }
        self.head_only(status, reason(status), Some(fields), &[], body.len())?;
        self.body_share(status, body);
        Ok(())
    }

    fn send_reason(&mut self, status: u16, reason: &[u8], fields: &[Field], body: &[u8]) -> Result<(), SendError> {
        self.head_only(status, reason, None, fields, body.len())?;
        self.body_copy(status, body);
        Ok(())
    }

    /// A plain-text error response.
    pub fn error(&mut self, status: u16) {
        let r = reason(status);
        let _ = self.send(status, &[Field { name: b"Content-Type", value: b"text/plain" }], r);
    }

    /// Closes the connection after this response.
    pub fn close_after(&mut self) {
        self.close = true;
    }
}
