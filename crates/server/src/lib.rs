#![doc = include_str!("../README.md")]
// A formally verified HTTP server: verified sans-I/O protocol engines on a
// small trusted event loop. See DESIGN.md.
//
// - [`respond`]: verified response heads, proven to parse back exactly
//   under verilith-http's specification.
// - [`h1`]: the HTTP/1.1 connection engine over verilith-http, sans I/O.
// - [`sys`]: the trusted OS shim (epoll, kqueue, sockets).
// - [`worker`]: the thread-per-core event loop.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
pub mod respond;
pub mod conn;
pub mod path;
pub mod range;
pub mod persist;
pub mod flow;
pub mod streams;
pub mod out;
pub mod h2core;

#[cfg(not(verus_keep_ghost))]
pub mod date;
#[cfg(not(verus_keep_ghost))]
pub mod files;
#[cfg(not(verus_keep_ghost))]
pub mod h1;
#[cfg(not(verus_keep_ghost))]
pub mod h2;
#[cfg(not(verus_keep_ghost))]
pub mod sys;
#[cfg(not(verus_keep_ghost))]
pub mod worker;
#[cfg(all(feature = "tls", not(verus_keep_ghost)))]
pub mod tls;
#[cfg(all(feature = "h3", not(verus_keep_ghost)))]
pub mod h3;

#[cfg(not(verus_keep_ghost))]
pub use api::*;

#[cfg(not(verus_keep_ghost))]
mod api {
    use verilith_http::Header;

    pub use crate::h1::{Fields, Limits, SendError, StaticBody};
    pub use crate::h2::Limits2;
    pub use crate::respond::{Field, Prepared};
    pub use crate::worker::{serve, Config};

    /// A request, as a handler sees it. Everything borrows the connection's
    /// read buffer: no copies.
    pub struct Request<'a> {
        pub method: &'a [u8],
        /// The request target as sent (`/path?query` for origin form).
        pub target: &'a [u8],
        /// `x` in `HTTP/1.x`.
        pub minor: u8,
        pub(crate) buf: &'a [u8],
        pub(crate) headers: &'a [Header],
        /// The whole body, decoded if it was chunked.
        pub body: &'a [u8],
        pub(crate) early: bool,
        pub(crate) peer: Option<&'a [u8]>,
    }

    impl<'a> Request<'a> {
        /// The field lines, in order, as (name, value) with the value's
        /// surrounding whitespace removed.
        pub fn headers(&self) -> impl Iterator<Item = (&'a [u8], &'a [u8])> + '_ {
            let buf = self.buf;
            self.headers.iter().map(move |h| (h.name.of(buf), h.value.of(buf)))
        }

        /// The first field with this name (ASCII case-insensitive).
        pub fn header(&self, name: &[u8]) -> Option<&'a [u8]> {
            let buf = self.buf;
            self.headers.iter().find(|h| h.name.of(buf).eq_ignore_ascii_case(name)).map(|h| h.value.of(buf))
        }

        /// Whether the request came in TLS 1.3 0-RTT data, before the
        /// handshake was confirmed (RFC 8470 §5.1). Such a request may be a
        /// replay: the server answers 425 (Too Early) to any method but
        /// GET, HEAD and OPTIONS without calling the handler, and a handler
        /// should do nothing for an early GET that it would not repeat.
        pub fn early(&self) -> bool {
            self.early
        }

        /// The client's certificate (DER), if the connection is TLS with
        /// client authentication ([`crate::tls::ClientAuth`]) and the client
        /// sent one. verilith-tls checked, with proof, that its chain leads
        /// to one of the configured trust anchors, that it is valid now and
        /// for client authentication, and that the client signed the
        /// handshake with its key (verilith-tls `spec_client.rs`).
        pub fn client_certificate(&self) -> Option<&'a [u8]> {
            self.peer
        }

        /// The target's path, before any `?`.
        pub fn path(&self) -> &'a [u8] {
            let t = self.target;
            match t.iter().position(|&c| c == b'?') {
                Some(i) => &t[..i],
                None => t,
            }
        }
    }

    /// Where a handler writes its response. See [`Response::send`].
    pub struct Response<'a> {
        pub(crate) out: &'a mut crate::out::Wire,
        pub(crate) ctx: &'a crate::h1::Ctx,
        pub(crate) sent: bool,
        pub(crate) close: bool,
        pub(crate) head: bool,
        /// Set on HTTP/2 streams: the response is encoded here.
        pub(crate) h2: Option<&'a mut crate::h2::Reply>,
    }

    /// Whether a request with this method may be answered from 0-RTT
    /// data: the safe methods (RFC 9110 §9.2.1) that browsers send early.
    pub(crate) fn early_ok(method: &[u8]) -> bool {
        matches!(method, b"GET" | b"HEAD" | b"OPTIONS")
    }

    /// Request handling. Called on the worker thread that owns the
    /// connection; it should not block.
    pub trait Handler: Send + Sync + 'static {
        fn handle(&self, req: &Request, res: &mut Response);
    }

    impl<F: Fn(&Request, &mut Response) + Send + Sync + 'static> Handler for F {
        fn handle(&self, req: &Request, res: &mut Response) {
            self(req, res)
        }
    }
}
