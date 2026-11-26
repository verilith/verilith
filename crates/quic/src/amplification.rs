//! The anti-amplification limit (§8.1).
//!
//! Before it has validated the client's address, a server must not send
//! more than three times the bytes it has received from that address.
//! [`Budget`] counts both and is the only way to account for bytes sent,
//! and the theorem is its invariant ([`Budget::inv`]): unvalidated, the
//! bytes sent are at most three times the bytes received, after any
//! sequence of calls.
use vstd::prelude::*;

verus! {

/// The bytes received from and sent to an address not yet validated.
pub struct Budget {
    received: u64,
    sent: u64,
    validated: bool,
}

impl Budget {
    /// Bytes received.
    pub closed spec fn received(&self) -> nat {
        self.received as nat
    }

    /// Bytes sent.
    pub closed spec fn sent(&self) -> nat {
        self.sent as nat
    }

    /// Whether the address is validated.
    pub closed spec fn validated(&self) -> bool {
        self.validated
    }

    /// §8.1: "Prior to validating the client address, servers MUST NOT
    /// send more than three times as many bytes as the number of bytes
    /// they have received."
    pub open spec fn inv(&self) -> bool {
        self.validated() || self.sent() <= 3 * self.received()
    }

    /// A new connection's budget, nothing received yet (a server starts
    /// it when the client's first Initial arrives, and counts that
    /// datagram with `on_received`). A client, whose server's address is
    /// validated by definition, starts with `validated`.
    pub fn new(validated: bool) -> (r: Budget)
        ensures
            r.inv(),
            r.received() == 0,
            r.sent() == 0,
            r.validated() == validated,
    {
        Budget { received: 0, sent: 0, validated }
    }

    /// Counts a datagram of `n` bytes received from the address (§8.1:
    /// including ones that could not be processed). The count stops at
    /// `u64::MAX`, which only lowers the allowance.
    pub fn on_received(&mut self, n: u64)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).sent() == old(self).sent(),
            final(self).validated() == old(self).validated(),
            final(self).received() == if old(self).received() + n > u64::MAX { u64::MAX as int } else {
                old(self).received() + n
            },
    {
        self.received = if n > u64::MAX - self.received { u64::MAX } else { self.received + n };
    }

    /// The address is validated (§8): a Handshake packet was received
    /// from it, or a token or a path validation proved it.
    pub fn validate(&mut self)
        ensures
            final(self).inv(),
            final(self).validated(),
            final(self).sent() == old(self).sent(),
            final(self).received() == old(self).received(),
    {
        self.validated = true;
    }

    /// How many more bytes may be sent now.
    pub fn allowance(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            self.validated() ==> r == u64::MAX,
            !self.validated() ==> r as nat == if 3 * self.received() - self.sent() > u64::MAX {
                u64::MAX as nat
            } else {
                (3 * self.received() - self.sent()) as nat
            },
    {
        if self.validated {
            return u64::MAX;
        }
        let limit: u128 = 3 * self.received as u128;
        let left = limit - self.sent as u128;
        if left > u64::MAX as u128 {
            u64::MAX
        } else {
            left as u64
        }
    }

    /// Counts `n` bytes sent, which must be within `allowance()`.
    pub fn on_sent(&mut self, n: u64)
        requires
            old(self).inv(),
            old(self).validated() || old(self).sent() + n <= 3 * old(self).received(),
            old(self).sent() + n <= u64::MAX,
        ensures
            final(self).inv(),
            final(self).sent() == old(self).sent() + n,
            final(self).received() == old(self).received(),
            final(self).validated() == old(self).validated(),
    {
        self.sent = self.sent + n;
    }

    /// Counts up to `n` bytes as sent and returns how many may go: `n`,
    /// or less when the limit cuts it short (the rest waits until more is
    /// received).
    pub fn take(&mut self, n: u64) -> (r: u64)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r <= n,
            final(self).sent() == old(self).sent() + r,
            final(self).received() == old(self).received(),
            final(self).validated() == old(self).validated(),
    {
        let a = self.allowance();
        let room = u64::MAX - self.sent;
        let mut r = if n < a { n } else { a };
        if r > room {
            r = room;
        }
        self.on_sent(r);
        r
    }
}

/// §8.1 and §14.1: a client's datagrams that carry Initial packets must
/// be at least 1200 bytes; a server discards smaller ones.
pub open spec fn initial_datagram_ok(len: nat) -> bool {
    len >= 1200
}

/// `initial_datagram_ok`.
pub fn is_initial_datagram_ok(len: usize) -> (r: bool)
    ensures
        r == initial_datagram_ok(len as nat),
{
    len >= 1200
}

} // verus!
