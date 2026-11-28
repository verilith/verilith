//! Verified reading of upstream responses, and when an upstream
//! connection may carry another request.
//!
//! The proxy sends one request at a time on an upstream connection and
//! reads its response with verilith-http's verified parser and framing
//! (RFC 9112 §4, §6.3: [`read_head`] computes `up` exactly). Interim
//! responses (1xx, RFC 9110 §15.2) are skipped; 101 (Switching Protocols)
//! is refused, since the proxy never asks for an upgrade.
//!
//! A pooled connection is where response desynchronization happens: if a
//! connection is reused while bytes of an earlier response, or bytes the
//! backend sent unasked, are still unread, the next client gets a response
//! meant for someone else ("response queue poisoning"). `reusable` is
//! the rule, decided exactly by [`reuse_ok`]: the response persists
//! (RFC 9112 §9.3, the same reading as verilith-server's `persist.rs`),
//! its length is known from its framing (not read-until-close), and it
//! ended exactly where the bytes received end.
use vstd::prelude::*;
use verilith_http::parse::{response_at, Header, Out};
#[cfg(verus_keep_ghost)]
use verilith_http::parse::{hdrs_ok, headers_view};
use verilith_http::framing::response_body_exec;
use verilith_http::spec::{Body, Parsed, SpecResponse};
#[cfg(verus_keep_ghost)]
use verilith_http::spec::{parse_response, response_body};
use verilith_server::persist::persists_exec;
#[cfg(verus_keep_ghost)]
use verilith_server::persist::persists_hm;

verus! {

/// What the bytes at the start of an upstream connection's buffer are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Up {
    /// The head is not complete yet.
    Partial,
    /// Not a response the proxy can forward: the connection is closed and
    /// the client answered 502.
    Bad,
    /// An interim (1xx) response this long, to skip.
    Interim(usize),
    /// A final response: its status, head length, body framing, and
    /// whether the connection persists after it.
    Final { status: u16, head_len: usize, body: Body, persist: bool },
}

/// The specification of [`read_head`].
pub open spec fn up(b: Seq<u8>, max: nat, head: bool) -> Up {
    match parse_response(b, max) {
        Parsed::Done(r, end) => if 100 <= r.status <= 199 {
            if r.status == 101 { Up::Bad } else { Up::Interim(end as usize) }
        } else {
            match response_body(b, r, head, false) {
                None => Up::Bad,
                Some(body) => Up::Final {
                    status: r.status,
                    head_len: end as usize,
                    body,
                    persist: persists_hm(b, r.headers, r.minor),
                },
            }
        },
        Parsed::Partial => Up::Partial,
        Parsed::Invalid => Up::Bad,
    }
}

/// Reads the response head at the start of `b` (field lines into `hs`):
/// exactly `up`.
pub fn read_head(b: &[u8], max: usize, head: bool, hs: &mut Vec<Header>) -> (r: Up)
    ensures
        r != Up::Bad ==> r == up(b@, max as nat, head),
        up(b@, max as nat, head) == Up::Bad ==> r == Up::Bad,
        hdrs_ok(final(hs)@, b@.len() as int),
        r matches Up::Interim(n) ==> 0 < n <= b@.len(),
        r matches Up::Final { head_len, .. } ==> 0 < head_len <= b@.len(),
{
    let (o, _) = response_at(b, max, hs);
    match o {
        Out::Done(line, end) => {
            let ghost q = match parse_response(b@, max as nat) {
                Parsed::Done(q, _) => q,
                _ => arbitrary(),
            };
            if end == 0 {
                // Never: a head holds its status line. Checked rather than
                // proven, so that skipping an interim response always
                // makes progress.
                return Up::Bad;
            }
            if line.status >= 100 && line.status <= 199 {
                if line.status == 101 { Up::Bad } else { Up::Interim(end) }
            } else {
                let sr = Ghost(SpecResponse { minor: line.minor, status: line.status, reason: line.reason@, headers: headers_view(hs@) });
                assert(sr@ == q);
                match response_body_exec(b, line, hs, head, false) {
                    None => Up::Bad,
                    Some(body) => {
                        let persist = persists_exec(b, hs, line.minor);
                        Up::Final { status: line.status, head_len: end, body, persist }
                    },
                }
            }
        },
        Out::Partial => Up::Partial,
        Out::Invalid => Up::Bad,
    }
}

/// Whether the connection may carry the next request, once the final
/// response with framing `body` (and persistence `persist`) has been read
/// and `consumed` bytes of the `received` taken: RFC 9112 §9.3, a known
/// length, and no byte left over.
pub open spec fn reusable(persist: bool, body: Body, consumed: nat, received: nat) -> bool {
    persist && !(body is Close) && consumed == received
}

/// `reusable`, exactly.
pub fn reuse_ok(persist: bool, body: Body, consumed: usize, received: usize) -> (r: bool)
    ensures
        r == reusable(persist, body, consumed as nat, received as nat),
{
    persist && !matches!(body, Body::Close) && consumed == received
}

} // verus!
