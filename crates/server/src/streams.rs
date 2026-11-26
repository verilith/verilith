//! HTTP/2 stream states (RFC 9113 §5.1), verified: what a frame received
//! on a stream does, given the stream's state.
//!
//! [`verdict`] is the specification, a table over the server's view of a
//! stream: idle (an even ID, which a client never opens, or one above the
//! highest it has opened), open, half-closed (remote), or closed.
//! [`classify`] computes it exactly. The theorems
//! ([`lemma_opens_only_new_odd`], [`lemma_data_only_open`]): only a
//! HEADERS frame opens a stream, only on an odd ID above every ID opened
//! before it (§5.1.1, so IDs only increase), and DATA is taken only on an
//! open stream.
use vstd::prelude::*;

verus! {

pub const PROTOCOL_ERROR: u32 = 0x1;
pub const STREAM_CLOSED: u32 = 0x5;

/// A stream's state, for a stream at or below the highest ID opened.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum St {
    /// Receiving the request.
    Open,
    /// The request is complete; the response is being sent.
    HalfClosed,
}

/// The frames that name a stream.
#[derive(Clone, Copy)]
pub enum Kind {
    Headers { end_stream: bool },
    Data,
    RstStream,
    WindowUpdate,
    Priority,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// A new stream, now open.
    Open,
    /// A trailer block on an open stream.
    Trailers,
    /// Apply the frame to the stream.
    Accept,
    /// Nothing to do (a frame on a closed stream that is allowed there).
    Ignore,
    /// RST_STREAM with this code.
    Stream(u32),
    /// GOAWAY with this code.
    Conn(u32),
}

/// The stream is idle: a client never opens an even ID, and an ID above
/// `last` has not been opened yet.
pub open spec fn idle(id: u32, last: u32) -> bool {
    id % 2 == 0 || id > last
}

/// The table: `known` is the stream's state if it is neither idle nor
/// closed.
pub open spec fn verdict(id: u32, last: u32, known: Option<St>, k: Kind) -> Verdict {
    match k {
        Kind::Headers { end_stream } => if id % 2 == 0 {
            Verdict::Conn(PROTOCOL_ERROR)  // §5.1.1
        } else if id > last {
            Verdict::Open
        } else {
            match known {
                Some(St::Open) => if end_stream { Verdict::Trailers } else { Verdict::Conn(PROTOCOL_ERROR) },  // §8.1
                // §5.1, half-closed (remote): STREAM_CLOSED, as a connection
                // error (§5.4.1 allows it): the block cannot be skipped
                // without decoding it, or the HPACK tables would diverge.
                Some(St::HalfClosed) => Verdict::Conn(STREAM_CLOSED),
                None => Verdict::Conn(STREAM_CLOSED),  // §5.1, closed
            }
        },
        Kind::Data => if idle(id, last) {
            Verdict::Conn(PROTOCOL_ERROR)  // §5.1, idle
        } else {
            match known {
                Some(St::Open) => Verdict::Accept,
                _ => Verdict::Stream(STREAM_CLOSED),
            }
        },
        Kind::RstStream => if idle(id, last) { Verdict::Conn(PROTOCOL_ERROR) } else { Verdict::Accept },
        Kind::WindowUpdate => if idle(id, last) {
            Verdict::Conn(PROTOCOL_ERROR)
        } else if known is None {
            Verdict::Ignore  // §5.1: a closed stream may still get WINDOW_UPDATE briefly
        } else {
            Verdict::Accept
        },
        Kind::Priority => Verdict::Accept,  // §5.1: allowed in every state
    }
}

/// Only HEADERS opens a stream, only on an odd ID above `last`.
pub proof fn lemma_opens_only_new_odd(id: u32, last: u32, known: Option<St>, k: Kind)
    ensures verdict(id, last, known, k) == Verdict::Open ==> (k is Headers && id % 2 == 1 && id > last),
{
}

/// DATA is taken only on an open stream that is not idle.
pub proof fn lemma_data_only_open(id: u32, last: u32, known: Option<St>)
    ensures verdict(id, last, known, Kind::Data) == Verdict::Accept ==> (known == Some(St::Open) && !idle(id, last)),
{
}

/// [`verdict`], computed.
pub fn classify(id: u32, last: u32, known: Option<St>, k: Kind) -> (r: Verdict)
    ensures r == verdict(id, last, known, k),
{
    let idle = id % 2 == 0 || id > last;
    match k {
        Kind::Headers { end_stream } => {
            if id % 2 == 0 {
                Verdict::Conn(PROTOCOL_ERROR)
            } else if id > last {
                Verdict::Open
            } else {
                match known {
                    Some(St::Open) => if end_stream { Verdict::Trailers } else { Verdict::Conn(PROTOCOL_ERROR) },
                    Some(St::HalfClosed) => Verdict::Conn(STREAM_CLOSED),
                    None => Verdict::Conn(STREAM_CLOSED),
                }
            }
        },
        Kind::Data => {
            if idle {
                Verdict::Conn(PROTOCOL_ERROR)
            } else {
                match known {
                    Some(St::Open) => Verdict::Accept,
                    _ => Verdict::Stream(STREAM_CLOSED),
                }
            }
        },
        Kind::RstStream => if idle { Verdict::Conn(PROTOCOL_ERROR) } else { Verdict::Accept },
        Kind::WindowUpdate => {
            if idle {
                Verdict::Conn(PROTOCOL_ERROR)
            } else if known.is_none() {
                Verdict::Ignore
            } else {
                Verdict::Accept
            }
        },
        Kind::Priority => Verdict::Accept,
    }
}

} // verus!
