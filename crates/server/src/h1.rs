//! The HTTP/1.1 connection engine, sans I/O.
//!
//! [`Conn`] owns a connection's read and write buffers. The event loop puts
//! bytes into [`Conn::read_buf`], calls [`Conn::process`], and writes what
//! [`Conn::pending`] returns. Where each request starts and ends is decided
//! by the verified core in [`crate::conn`], whose invariant is that every
//! request handed to a handler is the specification's next request in the
//! byte stream. The response heads are written by [`crate::respond`]'s
//! verified writer. This file runs the handler between the two, decides
//! persistence (RFC 9112 §9.3), and keeps the output queue.
use std::collections::VecDeque;
use std::sync::Arc;

use verilith_http::Header;

use crate::conn::{Core, Ev, Phase};

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
    /// The read buffer and the verified request sequencing.
    core: Core,
    wbuf: Out,
    sent_continue: bool,
    limits: Limits,
    /// Requests are being read from 0-RTT data (set by the TLS layer).
    pub(crate) early: bool,
}

/// The server's own field lines, checked once and rebuilt when `Date`
/// changes (once a second per worker).
pub struct Ctx {
    own: Prepared,
    own_close: Prepared,
    empty: Prepared,
    /// The same fields as HPACK representations, for HTTP/2.
    pub(crate) own_h2: crate::h2::HList,
}

impl Ctx {
    /// `None` if `server` or `date` is not a valid field value.
    pub fn new(server: &[u8], date: &[u8]) -> Option<Ctx> {
        Ctx::with_alt_svc(server, date, None)
    }

    /// [`Ctx::new`], adding `Alt-Svc: alt` to every response (RFC 7838):
    /// how a browser that reached us over TCP learns of HTTP/3.
    pub fn with_alt_svc(server: &[u8], date: &[u8], alt: Option<&[u8]>) -> Option<Ctx> {
        let mut own = vec![Field { name: b"Server", value: server }, Field { name: b"Date", value: date }];
        let mut own_h2 = crate::h2::HList::default();
        own_h2.push(b"server", server);
        own_h2.push(b"date", date);
        if let Some(a) = alt {
            own.push(Field { name: b"Alt-Svc", value: a });
            own_h2.push(b"alt-svc", a);
        }
        let mut own_close = own.clone();
        own_close.push(Field { name: b"Connection", value: b"close" });
        Some(Ctx { own: Prepared::new(&own)?, own_close: Prepared::new(&own_close)?, empty: Prepared::empty(), own_h2 })
    }
}

impl Conn {
    pub fn new(limits: Limits) -> Conn {
        Conn { core: Core::new(limits.max_head, limits.max_headers, limits.max_body), wbuf: Out::new(), sent_continue: false, limits, early: false }
    }

    /// Makes the connection new again, keeping its buffers.
    pub fn reset(&mut self) {
        self.core.reset(self.limits.max_head);
        self.wbuf.clear();
        self.sent_continue = false;
        self.early = false;
    }

    /// Room to read into. Empty when the connection should not read now.
    ///
    /// Trusted (TRUST.md): the event loop writes only into the slice this
    /// returns, `rbuf[end..]`, which the core's invariant says nothing
    /// about; [`Conn::filled`] then adds those bytes to the core's stream.
    pub fn read_buf(&mut self) -> &mut [u8] {
        if matches!(self.core.phase, Phase::Closed) || self.wbuf.queued > self.limits.write_high {
            return &mut [];
        }
        if self.core.end == self.core.rbuf.len() && self.core.start > 0 {
            self.core.compact();
        }
        if self.core.end == self.core.rbuf.len() {
            // A body larger than the head buffer, buffered for the handler.
            let want = match self.core.phase {
                Phase::Length { hd, need } => self.core.start + hd.head_len + need,
                Phase::Chunked { .. } => self.core.rbuf.len() * 2,
                _ => self.core.rbuf.len(),
            };
            let cap = self.limits.max_head + self.limits.max_body;
            if want > self.core.rbuf.len() && self.core.rbuf.len() < cap {
                self.core.grow(want.min(cap));
            }
        }
        let end = self.core.end;
        &mut self.core.rbuf[end..]
    }

    /// `n` bytes were read into [`Conn::read_buf`].
    pub fn filled(&mut self, n: usize) {
        self.core.filled(n);
    }

    /// The peer closed its side: nothing more will arrive.
    pub fn eof(&mut self) {
        self.core.close();
    }

    /// The bytes waiting to be written, as up to `out.len()` slices in
    /// order (for one `writev`). Returns how many slices were filled.
    pub fn pending<'a>(&'a self, out: &mut [&'a [u8]]) -> usize {
        self.wbuf.slices(out)
    }

    /// [`Conn::pending`] for the event loop: file-backed bodies come as
    /// file ranges.
    pub fn pending_io<'a>(&'a self, out: &mut [&'a [u8]], more: &mut bool) -> Io<'a> {
        self.wbuf.slices_io(out, more)
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
        matches!(self.core.phase, Phase::Closed)
    }

    /// Handles every complete request in the read buffer, appending the
    /// responses, in order, to the write buffer.
    pub fn process<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) -> Next {
        loop {
            match self.core.step() {
                Ev::Ready => self.dispatch(h, ctx),
                Ev::Need => {
                    if matches!(self.core.phase, Phase::Length { .. } | Phase::Chunked { .. }) {
                        self.maybe_continue(ctx);
                    }
                    return self.next();
                }
                Ev::Bad(status) => {
                    let reason: &[u8] = match status {
                        413 => b"Content Too Large",
                        431 => b"Request Header Fields Too Large",
                        _ => b"Bad Request",
                    };
                    self.error(ctx, status, reason);
                    return Next::Close;
                }
                Ev::Closed => return Next::Close,
            }
        }
    }

    fn next(&self) -> Next {
        if matches!(self.core.phase, Phase::Closed) {
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
        let buf = &self.core.rbuf[self.core.start..self.core.end];
        let mut expect = false;
        for hd in &self.core.headers {
            if hd.name.of(buf).eq_ignore_ascii_case(b"expect") && hd.value.of(buf).eq_ignore_ascii_case(b"100-continue") {
                expect = true;
            }
        }
        if expect {
            self.wbuf.extend(b"HTTP/1.1 100 Continue\r\n\r\n");
            self.sent_continue = true;
        }
    }

    /// Runs the handler on the ready request, writes its response, and
    /// moves past it.
    fn dispatch<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) {
        let Phase::Ready { hd, body } = self.core.phase else { return };
        let c = &self.core;
        let buf = &c.rbuf[c.start..c.end];
        let keep = c.ready_persists();
        let method = &buf[hd.method.start..hd.method.end];
        let request = Request {
            method,
            target: &buf[hd.target.start..hd.target.end],
            minor: hd.minor,
            buf,
            headers: &c.headers,
            body: &buf[hd.head_len..hd.head_len + body],
            early: self.early,
        };
        let mut res = Response { out: &mut self.wbuf, ctx, sent: false, close: !keep, head: method == b"HEAD", h2: None };
        if self.early && !crate::early_ok(method) {
            res.too_early();
        } else {
            h.handle(&request, &mut res);
        }
        if !res.sent {
            res.error(500);
        }
        let close = res.close;
        self.sent_continue = false;
        self.core.done(!close);
    }

    /// Writes an error response and marks the connection to close: after a
    /// rejected head, its length and the next request's start are unknown.
    fn error(&mut self, ctx: &Ctx, status: u16, reason: &[u8]) {
        let mut res = Response { out: &mut self.wbuf, ctx, sent: false, close: true, head: false, h2: None };
        res.send_reason(status, reason, &[], reason).ok();
        self.core.close();
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
    /// A sealed file holding exactly `a`, to `sendfile` from.
    file: Option<Arc<crate::sys::Fd>>,
}

/// What to write next: slices, or a range of a file.
pub enum Io<'a> {
    Slices(usize, std::marker::PhantomData<&'a ()>),
    File { fd: i32, off: usize, len: usize },
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

    /// An `Out` that has allocated nothing: for a response that writes
    /// elsewhere (HTTP/2 and HTTP/3 replies), so a request costs no
    /// allocation for it.
    pub(crate) fn empty() -> Out {
        Out { buf: Vec::new(), segs: VecDeque::new(), pos: 0, seg_off: 0, queued: 0 }
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
        self.segs.push_back((self.buf.len(), Seg { a: body, off, len: n, file: None }));
    }

    pub(crate) fn share(&mut self, body: Arc<[u8]>) {
        self.queued += body.len();
        let len = body.len();
        self.segs.push_back((self.buf.len(), Seg { a: body, off: 0, len, file: None }));
    }

    /// A shared body that also lives in a sealed file, sent with `sendfile`.
    pub(crate) fn share_file(&mut self, body: &StaticBody) {
        self.queued += body.bytes.len();
        let len = body.bytes.len();
        self.segs.push_back((self.buf.len(), Seg { a: body.bytes.clone(), off: 0, len, file: body.file.clone() }));
    }

    /// `len` bytes of a static body from `off`, with its file if it has
    /// one (the file holds the same bytes at the same offsets).
    pub(crate) fn share_file_range(&mut self, body: &StaticBody, off: usize, len: usize) {
        self.queued += len;
        self.segs.push_back((self.buf.len(), Seg { a: body.bytes.clone(), off, len, file: body.file.clone() }));
    }

    /// [`Out::slices`], stopping before a file-backed body: the event loop
    /// writes those with `sendfile`. `more` is set when slices stop at one
    /// (more bytes follow at once: MSG_MORE).
    pub(crate) fn slices_io<'a>(&'a self, out: &mut [&'a [u8]], more: &mut bool) -> Io<'a> {
        *more = false;
        let mut k = 0;
        let mut p = self.pos;
        let mut off = self.seg_off;
        for (at, seg) in &self.segs {
            if k == out.len() {
                return Io::Slices(k, Default::default());
            }
            if p < *at {
                out[k] = &self.buf[p..*at];
                k += 1;
                p = *at;
                if k == out.len() {
                    return Io::Slices(k, Default::default());
                }
            }
            if off < seg.len {
                if let Some(f) = &seg.file {
                    if k == 0 {
                        return Io::File { fd: f.0, off: seg.off + off, len: seg.len - off };
                    }
                    *more = true;
                    return Io::Slices(k, Default::default());
                }
                out[k] = &seg.bytes()[off..];
                k += 1;
            }
            off = 0;
        }
        if k < out.len() && p < self.buf.len() {
            out[k] = &self.buf[p..];
            k += 1;
        }
        Io::Slices(k, Default::default())
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
    pub(crate) h2: crate::h2::HList,
}

impl Fields {
    /// `None` if a name or value is not allowed (see [`SendError::Invalid`]).
    pub fn new(fields: &[Field]) -> Option<Fields> {
        let h1 = Prepared::new(fields)?;
        let mut h2 = crate::h2::HList::default();
        for f in fields {
            h2.push(f.name, f.value);
        }
        Some(Fields { h1, h2 })
    }
}

/// A body served many times (a static file): in memory, and on Linux, for
/// sizes where it is faster, also in a sealed memory file that HTTP/1.1
/// responses are sent from with `sendfile`. Sealed, so the bytes sent are
/// always the bytes the Content-Length counted, whatever happens to the
/// file it was read from.
pub struct StaticBody {
    pub(crate) bytes: Arc<[u8]>,
    pub(crate) file: Option<Arc<crate::sys::Fd>>,
}

/// [`StaticBody::new`] uses `sendfile` for bodies from this long...
pub const SENDFILE_MIN: usize = 16 * 1024;
/// ...to this long. Measured on loopback (bench/server, 2 server CPUs):
/// `sendfile` is 6-17% faster from 32 to 96 KiB, and 10-37% slower from
/// 128 KiB up, where `writev` from memory wins. Over a NIC that can send
/// from page references, large files may differ: see
/// [`StaticBody::with_sendfile`].
pub const SENDFILE_MAX: usize = 112 * 1024;

impl StaticBody {
    pub fn new(bytes: Vec<u8>) -> StaticBody {
        let on = (SENDFILE_MIN..=SENDFILE_MAX).contains(&bytes.len());
        StaticBody::with_sendfile(bytes, on)
    }

    /// `sendfile` or not, whatever the size (it is used only where the
    /// platform has it: Linux).
    pub fn with_sendfile(bytes: Vec<u8>, sendfile: bool) -> StaticBody {
        let file = if crate::sys::HAS_SENDFILE && sendfile && !bytes.is_empty() {
            crate::sys::sealed_memfd(&bytes).map(Arc::new)
        } else {
            None
        };
        StaticBody { bytes: bytes.into(), file }
    }

    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    pub fn bytes(&self) -> &Arc<[u8]> {
        &self.bytes
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
            // Encoded when the HEADERS frame is written (h2.rs `schedule`).
            r.status = status;
            for f in fields {
                r.fields.push(f.name, f.value);
            }
            if let Some(p) = pre {
                r.fields.extend(&p.h2);
            }
            if !no_body(status) {
                let mut cl = [0u8; 20];
                r.fields.push(b"content-length", fmt_len(&mut cl, len));
            }
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
            // A reused reply keeps its owned body's buffer.
            Some(r) => match &mut r.body {
                crate::h2::ReplyBody::Owned(v) => {
                    v.clear();
                    v.extend_from_slice(body);
                }
                b => *b = crate::h2::ReplyBody::Owned(body.to_vec()),
            },
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

    /// A static body: `sendfile` on HTTP/1.1 where it can, shared otherwise.
    pub fn send_static(&mut self, status: u16, fields: &Fields, body: &StaticBody) -> Result<(), SendError> {
        if body.file.is_none() || self.h2.is_some() {
            return self.send_shared_prepared(status, fields, &body.bytes);
        }
        self.head_only(status, reason(status), Some(fields), &[], body.len())?;
        if !no_body(status) && !self.head {
            self.out.share_file(body);
        }
        Ok(())
    }

    /// `len` bytes of a static body from `off` (all of it, or one range
    /// of a range request), with the prepared `fields` and then `extra`.
    pub fn send_static_part(&mut self, status: u16, fields: &Fields, extra: &[Field], body: &StaticBody, off: usize, len: usize) -> Result<(), SendError> {
        if off > body.len() || len > body.len() - off {
            return Err(SendError::Invalid);
        }
        self.head_only(status, reason(status), Some(fields), extra, len)?;
        if no_body(status) || self.head {
            return Ok(());
        }
        let whole = off == 0 && len == body.len();
        match self.h2.as_deref_mut() {
            Some(r) => {
                r.body = if whole { crate::h2::ReplyBody::Shared(body.bytes.clone()) } else { crate::h2::ReplyBody::Slice(body.bytes.clone(), off, len) }
            }
            None if body.file.is_some() => self.out.share_file_range(body, off, len),
            None if len < SHARE_MIN => self.out.extend(&body.bytes[off..off + len]),
            None => self.out.share_range(body.bytes.clone(), off, len),
        }
        Ok(())
    }

    fn send_reason(&mut self, status: u16, reason: &[u8], fields: &[Field], body: &[u8]) -> Result<(), SendError> {
        self.head_only(status, reason, None, fields, body.len())?;
        self.body_copy(status, body);
        Ok(())
    }

    /// A plain-text error response.
    /// 425 Too Early (RFC 8470 §5.2): the client sends the request again
    /// once the handshake is done.
    pub(crate) fn too_early(&mut self) {
        let _ = self.send_reason(425, b"Too Early", &[], b"Too Early");
    }

    pub fn error(&mut self, status: u16) {
        let r = reason(status);
        let _ = self.send(status, &[Field { name: b"Content-Type", value: b"text/plain" }], r);
    }

    /// Closes the connection after this response.
    pub fn close_after(&mut self) {
        self.close = true;
    }
}
