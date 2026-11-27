//! The HTTP/1.1 connection engine, sans I/O.
//!
//! [`Conn`] owns a connection's read and write buffers. The event loop puts
//! bytes into [`Conn::read_buf`], calls [`Conn::process`], and writes what
//! [`Conn::pending`] returns. Everything that decides what is read and
//! written is verified, in [`crate::out::Engine`]: where each request
//! starts and ends ([`crate::conn`]), that each request handed to a handler
//! gets exactly one response, in request order, with a head proven to
//! parse back and framed by its true length, and that a closing response
//! says `Connection: close` ([`crate::out`]). This file runs the handler
//! between the engine's calls.
use std::sync::Arc;

use crate::conn::{Ev, Phase};
use crate::out::{Body, Engine, Own};
pub use crate::out::{Io, Out, SendError, StaticBody, SHARE_MIN};

use crate::respond::{Field, Prepared};
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
    /// The request core and the response ledger, verified.
    eng: Engine,
    limits: Limits,
    /// Requests are being read from 0-RTT data (set by the TLS layer).
    pub(crate) early: bool,
    /// The TLS client's certificate (DER), if it authenticated.
    pub(crate) peer: Option<std::sync::Arc<[u8]>>,
}

/// The server's own field lines, checked once and rebuilt when `Date`
/// changes (once a second per worker).
pub struct Ctx {
    pub(crate) own: Own,
    pub(crate) empty: Prepared,
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
        Some(Ctx { own: Own::new(Prepared::new(&own)?), empty: Prepared::empty(), own_h2 })
    }
}

impl Conn {
    pub fn new(limits: Limits) -> Conn {
        Conn { eng: Engine::new(limits.max_head, limits.max_headers, limits.max_body), limits, early: false, peer: None }
    }

    /// Makes the connection new again, keeping its buffers.
    pub fn reset(&mut self) {
        self.eng.reset(self.limits.max_head);
        self.early = false;
        self.peer = None;
    }

    /// Room to read into. Empty when the connection should not read now.
    ///
    /// Trusted (TRUST.md): the event loop writes only into the slice this
    /// returns, `rbuf[end..]`, which the core's invariant says nothing
    /// about; [`Conn::filled`] then adds those bytes to the core's stream.
    pub fn read_buf(&mut self) -> &mut [u8] {
        if matches!(self.eng.core.phase, Phase::Closed) || self.eng.wire.pending_len() > self.limits.write_high {
            return &mut [];
        }
        let core = &mut self.eng.core;
        if core.end == core.rbuf.len() && core.start > 0 {
            core.compact();
        }
        if core.end == core.rbuf.len() {
            // A body larger than the head buffer, buffered for the handler.
            let want = match core.phase {
                Phase::Length { hd, need } => core.start + hd.head_len + need,
                Phase::Chunked { .. } => core.rbuf.len() * 2,
                _ => core.rbuf.len(),
            };
            let cap = self.limits.max_head + self.limits.max_body;
            if want > core.rbuf.len() && core.rbuf.len() < cap {
                core.grow(want.min(cap));
            }
        }
        let end = core.end;
        &mut core.rbuf[end..]
    }

    /// `n` bytes were read into [`Conn::read_buf`].
    pub fn filled(&mut self, n: usize) {
        self.eng.core.filled(n);
    }

    /// The peer closed its side: nothing more will arrive.
    pub fn eof(&mut self) {
        self.eng.eof();
    }

    /// The bytes waiting to be written, as up to `out.len()` slices in
    /// order (for one `writev`). Returns how many slices were filled.
    pub fn pending<'a>(&'a self, out: &mut [&'a [u8]]) -> usize {
        self.eng.wire.pending(out)
    }

    /// [`Conn::pending`] for the event loop: file-backed bodies come as
    /// file ranges.
    pub fn pending_io<'a>(&'a self, out: &mut [&'a [u8]], more: &mut bool) -> Io<'a> {
        self.eng.wire.pending_io(out, more)
    }

    /// How many bytes wait to be written.
    pub fn pending_len(&self) -> usize {
        self.eng.wire.pending_len()
    }

    /// `n` bytes of [`Conn::pending`] were written.
    pub fn wrote(&mut self, n: usize) {
        self.eng.wire.wrote(n);
    }

    pub fn closing(&self) -> bool {
        matches!(self.eng.core.phase, Phase::Closed)
    }

    /// Handles every complete request in the read buffer, appending the
    /// responses, in order, to the write buffer.
    pub fn process<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) -> Next {
        loop {
            match self.eng.step(&ctx.own) {
                Ev::Ready => self.dispatch(h, ctx),
                Ev::Need => return self.next(),
                // The engine queued the error response.
                Ev::Bad(_) | Ev::Closed => return Next::Close,
            }
        }
    }

    fn next(&self) -> Next {
        if matches!(self.eng.core.phase, Phase::Closed) {
            Next::Close
        } else if self.eng.wire.pending_len() > self.limits.write_high {
            Next::Write
        } else {
            Next::Read
        }
    }

    /// Runs the handler on the ready request; the engine then moves past it.
    fn dispatch<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) {
        let Phase::Ready { hd, body } = self.eng.core.phase else { return };
        let c = &self.eng.core;
        let buf = &c.rbuf[c.start..c.end];
        let method = &buf[hd.method.start..hd.method.end];
        let request = Request {
            method,
            target: &buf[hd.target.start..hd.target.end],
            minor: hd.minor,
            buf,
            headers: &c.headers,
            body: &buf[hd.head_len..hd.head_len + body],
            early: self.early,
            peer: self.peer.as_deref(),
        };
        let mut res = Response { out: &mut self.eng.wire, ctx, sent: false, close: false, head: method == b"HEAD", h2: None };
        if crate::early::too_early(self.early, method) {
            res.too_early();
        } else {
            h.handle(&request, &mut res);
        }
        if !res.sent {
            res.error(500);
        }
        let late = res.close;
        self.eng.finish(&ctx.own, late);
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


/// A body served many times: see [`crate::out::StaticBody`].
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
        if self.h2.is_some() {
            if body.len() < SHARE_MIN {
                return self.send(status, fields, body);
            }
            self.h2_head(status, None, fields, body.len())?;
            self.h2_body(status, H2Body::Shared(body));
            return Ok(());
        }
        self.h1(status, reason(status), None, fields, Body::Shared(body, 0, body.len()))
    }

    /// HTTP/1.1: the verified ledger writes the head and the body.
    fn h1(&mut self, status: u16, reason: &[u8], pre: Option<&Fields>, fields: &[Field], body: Body) -> Result<(), SendError> {
        if self.sent {
            return Err(SendError::AlreadySent);
        }
        let pre = match pre {
            Some(p) => &p.h1,
            None => &self.ctx.empty,
        };
        self.out.answer(status, reason, &self.ctx.own, pre, fields, body, self.close)?;
        self.sent = true;
        Ok(())
    }

    /// HTTP/2 and HTTP/3: the same checks, then HPACK or QPACK (no
    /// Connection field: RFC 9113 §8.2.2).
    fn h2_head(&mut self, status: u16, pre: Option<&Fields>, fields: &[Field], len: usize) -> Result<(), SendError> {
        if self.sent {
            return Err(SendError::AlreadySent);
        }
        let Some(r) = self.h2.as_deref_mut() else { return Err(SendError::Invalid) };
        if !(100..=999).contains(&status) || !crate::respond::check_fields(fields) {
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
        Ok(())
    }

    fn h2_body(&mut self, status: u16, body: H2Body) {
        if no_body(status) || self.head {
            return;
        }
        let Some(r) = self.h2.as_deref_mut() else { return };
        r.body = match body {
            H2Body::Copy(b) => match std::mem::replace(&mut r.body, crate::h2::ReplyBody::Owned(Vec::new())) {
                // A reused reply keeps its owned body's buffer.
                crate::h2::ReplyBody::Owned(mut v) => {
                    v.clear();
                    v.extend_from_slice(b);
                    crate::h2::ReplyBody::Owned(v)
                }
                _ => crate::h2::ReplyBody::Owned(b.to_vec()),
            },
            H2Body::Shared(a) => crate::h2::ReplyBody::Shared(a.clone()),
            H2Body::Slice(a, off, len) => crate::h2::ReplyBody::Slice(a.clone(), off, len),
        };
    }

    /// [`Response::send`] with a route's fixed fields checked in advance
    /// ([`Prepared::new`]): the fast path.
    pub fn send_prepared(&mut self, status: u16, fields: &Fields, body: &[u8]) -> Result<(), SendError> {
        if self.h2.is_some() {
            self.h2_head(status, Some(fields), &[], body.len())?;
            self.h2_body(status, H2Body::Copy(body));
            return Ok(());
        }
        self.h1(status, reason(status), Some(fields), &[], Body::Bytes(body))
    }

    /// [`Response::send_shared`] with prepared fields.
    pub fn send_shared_prepared(&mut self, status: u16, fields: &Fields, body: &Arc<[u8]>) -> Result<(), SendError> {
        if self.h2.is_some() {
            if body.len() < SHARE_MIN {
                return self.send_prepared(status, fields, body);
            }
            self.h2_head(status, Some(fields), &[], body.len())?;
            self.h2_body(status, H2Body::Shared(body));
            return Ok(());
        }
        self.h1(status, reason(status), Some(fields), &[], Body::Shared(body, 0, body.len()))
    }

    /// A static body: `sendfile` on HTTP/1.1 where it can, shared otherwise.
    pub fn send_static(&mut self, status: u16, fields: &Fields, body: &StaticBody) -> Result<(), SendError> {
        if self.h2.is_some() {
            return self.send_shared_prepared(status, fields, &body.bytes);
        }
        self.h1(status, reason(status), Some(fields), &[], Body::Static(body, 0, body.len()))
    }

    /// `len` bytes of a static body from `off` (all of it, or one range
    /// of a range request), with the prepared `fields` and then `extra`.
    pub fn send_static_part(&mut self, status: u16, fields: &Fields, extra: &[Field], body: &StaticBody, off: usize, len: usize) -> Result<(), SendError> {
        if off > body.len() || len > body.len() - off {
            return Err(SendError::Invalid);
        }
        if self.h2.is_some() {
            self.h2_head(status, Some(fields), extra, len)?;
            let whole = off == 0 && len == body.len();
            self.h2_body(status, if whole { H2Body::Shared(&body.bytes) } else { H2Body::Slice(&body.bytes, off, len) });
            return Ok(());
        }
        self.h1(status, reason(status), Some(fields), extra, Body::Static(body, off, len))
    }

    fn send_reason(&mut self, status: u16, reason: &[u8], fields: &[Field], body: &[u8]) -> Result<(), SendError> {
        if self.h2.is_some() {
            self.h2_head(status, None, fields, body.len())?;
            self.h2_body(status, H2Body::Copy(body));
            return Ok(());
        }
        self.h1(status, reason, None, fields, Body::Bytes(body))
    }

    /// 425 Too Early (RFC 8470 §5.2): the client sends the request again
    /// once the handshake is done.
    pub(crate) fn too_early(&mut self) {
        let _ = self.send_reason(425, b"Too Early", &[], b"Too Early");
    }

    /// A plain-text error response.
    pub fn error(&mut self, status: u16) {
        let r = reason(status);
        let _ = self.send(status, &[Field { name: b"Content-Type", value: b"text/plain" }], r);
    }

    /// Closes the connection after this response. Called before sending,
    /// the head says `Connection: close`; called after, the connection
    /// still closes after the response, without the head saying so.
    pub fn close_after(&mut self) {
        self.close = true;
    }
}

/// A body for an HTTP/2 or HTTP/3 reply.
enum H2Body<'b> {
    Copy(&'b [u8]),
    Shared(&'b Arc<[u8]>),
    Slice(&'b Arc<[u8]>, usize, usize),
}

/// 1xx, 204 and 304 responses have no body (RFC 9112 §6.3).
fn no_body(status: u16) -> bool {
    (100..200).contains(&status) || status == 204 || status == 304
}
