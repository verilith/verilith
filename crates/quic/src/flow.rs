//! Flow control (§4.1, §4.5): credit given and taken, per stream and per
//! connection.
//!
//! A receiver advertises limits and checks every byte offset the peer
//! uses against them ([`RecvCredit`]); a sender spends the peer's limits
//! and never goes past them ([`SendCredit`]). Both are monotone in the
//! limit: a limit that would decrease is ignored (§4.1).
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Transport error codes (§20.1) the state machines report.
pub const FLOW_CONTROL_ERROR: u64 = 0x03;
/// See [`FLOW_CONTROL_ERROR`].
pub const STREAM_LIMIT_ERROR: u64 = 0x04;
/// See [`FLOW_CONTROL_ERROR`].
pub const STREAM_STATE_ERROR: u64 = 0x05;
/// See [`FLOW_CONTROL_ERROR`].
pub const FINAL_SIZE_ERROR: u64 = 0x06;

/// What a receiver has allowed and what the peer has used: per stream,
/// the largest offset received; per connection, the sum of those over all
/// streams (§4.1).
pub struct RecvCredit {
    max: u64,
    used: u64,
}

impl RecvCredit {
    /// The limit advertised (initial_max_data and the like, then MAX_DATA
    /// or MAX_STREAM_DATA).
    pub closed spec fn max(&self) -> nat {
        self.max as nat
    }

    /// The credit the peer has used.
    pub closed spec fn used(&self) -> nat {
        self.used as nat
    }

    /// §4.1: the peer never has more than the advertised limit.
    pub open spec fn inv(&self) -> bool {
        self.used() <= self.max() < VARINT_LIMIT
    }

    /// A limit of `max`, nothing used.
    pub fn new(max: u64) -> (r: RecvCredit)
        requires
            max < VARINT_LIMIT,
        ensures
            r.inv(),
            r.max() == max,
            r.used() == 0,
    {
        RecvCredit { max, used: 0 }
    }

    /// The limit, to send in MAX_DATA or MAX_STREAM_DATA.
    pub fn limit(&self) -> (r: u64)
        ensures
            r == self.max(),
    {
        self.max
    }

    /// The credit used.
    pub fn consumed(&self) -> (r: u64)
        ensures
            r == self.used(),
    {
        self.used
    }

    /// Raises the limit to `max` (never lowers it).
    pub fn raise(&mut self, max: u64)
        requires
            old(self).inv(),
            max < VARINT_LIMIT,
        ensures
            final(self).inv(),
            final(self).used() == old(self).used(),
            final(self).max() == if max > old(self).max() { max as nat } else { old(self).max() },
    {
        if max > self.max {
            self.max = max;
        }
    }

    /// Takes `n` more bytes of credit, or `false` (FLOW_CONTROL_ERROR,
    /// nothing changed) if that goes past the limit.
    pub fn take(&mut self, n: u64) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).max() == old(self).max(),
            ok == (old(self).used() + n <= old(self).max()),
            final(self).used() == if ok { old(self).used() + n } else { old(self).used() as int },
            !ok ==> *final(self) == *old(self),
    {
        if n > self.max - self.used {
            return false;
        }
        self.used = self.used + n;
        true
    }
}

/// The peer's limit and what has been sent against it (§4.1).
pub struct SendCredit {
    max: u64,
    used: u64,
}

impl SendCredit {
    /// The peer's limit.
    pub closed spec fn max(&self) -> nat {
        self.max as nat
    }

    /// The credit spent.
    pub closed spec fn used(&self) -> nat {
        self.used as nat
    }

    /// §4.1: "A sender MUST NOT send data in excess of either limit."
    pub open spec fn inv(&self) -> bool {
        self.used() <= self.max() < VARINT_LIMIT
    }

    /// The peer's initial limit.
    pub fn new(max: u64) -> (r: SendCredit)
        requires
            max < VARINT_LIMIT,
        ensures
            r.inv(),
            r.max() == max,
            r.used() == 0,
    {
        SendCredit { max, used: 0 }
    }

    /// The credit left.
    pub fn available(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == self.max() - self.used(),
    {
        self.max - self.used
    }

    /// The credit spent: the offset of the next byte (for a stream).
    pub fn spent(&self) -> (r: u64)
        ensures
            r == self.used(),
    {
        self.used
    }

    /// Whether the sender is blocked and should send DATA_BLOCKED or
    /// STREAM_DATA_BLOCKED with `max` (§4.1).
    pub fn blocked(&self) -> (r: bool)
        ensures
            r == (self.used() == self.max()),
    {
        self.used == self.max
    }

    /// A MAX_DATA or MAX_STREAM_DATA from the peer: §4.1, "A sender MUST
    /// ignore any MAX_STREAM_DATA or MAX_DATA frames that do not increase
    /// flow control limits."
    pub fn on_max(&mut self, max: u64)
        requires
            old(self).inv(),
            max < VARINT_LIMIT,
        ensures
            final(self).inv(),
            final(self).used() == old(self).used(),
            final(self).max() == if max > old(self).max() { max as nat } else { old(self).max() },
    {
        if max > self.max {
            self.max = max;
        }
    }

    /// Spends `n` bytes of credit, at most `available()`.
    pub fn spend(&mut self, n: u64)
        requires
            old(self).inv(),
            old(self).used() + n <= old(self).max(),
        ensures
            final(self).inv(),
            final(self).max() == old(self).max(),
            final(self).used() == old(self).used() + n,
    {
        self.used = self.used + n;
    }
}

} // verus!
