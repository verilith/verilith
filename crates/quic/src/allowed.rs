//! Which frames each packet type may carry, and which elicit an
//! acknowledgment (RFC 9000 §12.4, Table 3; §13.2).
//!
//! [`allowed_spec`] is Table 3, column by column; [`allowed`] and
//! [`ack_eliciting`] are proven to compute it. A server also refuses the
//! frames only a server may send ([`server_receives`]: NEW_TOKEN, §19.7,
//! and HANDSHAKE_DONE, §19.20).
use crate::frame::Frame;
use vstd::prelude::*;

verus! {

/// The packet types of Table 3.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Level {
    /// Initial packets.
    Initial,
    /// 0-RTT packets.
    ZeroRtt,
    /// Handshake packets.
    Handshake,
    /// 1-RTT (short header) packets.
    OneRtt,
}

/// Table 3: `IH01` frames go in every packet type, `IH_1` not in 0-RTT,
/// `___1` only in 1-RTT, and `__01` only in 0-RTT and 1-RTT.
pub open spec fn allowed_spec(f: Frame, l: Level) -> bool {
    match f {
        // IH01
        Frame::Padding(_) | Frame::Ping => true,
        Frame::ConnectionClose { app: false, .. } => true,
        // IH_1
        Frame::Ack(_) | Frame::Crypto { .. } => l != Level::ZeroRtt,
        // ___1
        Frame::NewToken(_) | Frame::HandshakeDone => l == Level::OneRtt,
        // __01: everything else.
        _ => l == Level::ZeroRtt || l == Level::OneRtt,
    }
}

/// §13.2 (Table 3's `N`): all frames but ACK, PADDING and
/// CONNECTION_CLOSE elicit an acknowledgment.
pub open spec fn ack_eliciting_spec(f: Frame) -> bool {
    !(f is Ack || f is Padding || f is ConnectionClose)
}

/// Whether frame `f` may be in a packet of type `l`; a frame where it may
/// not is a PROTOCOL_VIOLATION (§12.4).
pub fn allowed(f: &Frame, l: Level) -> (r: bool)
    ensures
        r == allowed_spec(*f, l),
{
    let early_or_1rtt = matches!(l, Level::ZeroRtt | Level::OneRtt);
    match f {
        Frame::Padding(_) | Frame::Ping => true,
        Frame::ConnectionClose { app, .. } => !*app || early_or_1rtt,
        Frame::Ack(_) | Frame::Crypto { .. } => !matches!(l, Level::ZeroRtt),
        Frame::NewToken(_) | Frame::HandshakeDone => matches!(l, Level::OneRtt),
        _ => early_or_1rtt,
    }
}

/// Whether `f` elicits an acknowledgment.
pub fn ack_eliciting(f: &Frame) -> (r: bool)
    ensures
        r == ack_eliciting_spec(*f),
{
    !matches!(f, Frame::Ack(_) | Frame::Padding(_) | Frame::ConnectionClose { .. })
}

/// A server receives every frame type but NEW_TOKEN and HANDSHAKE_DONE,
/// which only a server sends (§19.7, §19.20).
pub fn server_receives(f: &Frame) -> (r: bool)
    ensures
        r == !(*f is NewToken || *f is HandshakeDone),
{
    !matches!(f, Frame::NewToken(_) | Frame::HandshakeDone)
}

} // verus!
