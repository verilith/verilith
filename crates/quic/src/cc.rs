//! Congestion control (RFC 9002 §7, Appendix B): NewReno, proven to
//! follow the RFC's transitions ([`on_ack_spec`], [`on_congestion_spec`])
//! with these invariants, after any sequence of calls:
//!
//! - the congestion window never falls below kMinimumWindow, two
//!   datagrams (§7.2), nor rises above [`MAX_WINDOW`];
//! - a sender asks [`NewReno::can_send`] before each in-flight packet, and
//!   with `sent::Sent`'s exact count of bytes in flight, never has more in
//!   flight than the window (§7: "MUST NOT send packets if they would
//!   cause bytes_in_flight to be larger than the congestion window");
//! - the window is reduced at most once per recovery period: a loss or
//!   ECN-CE for a packet sent before the period began changes nothing
//!   (§7.3.2), and acknowledgments of such packets do not grow the window
//!   (§7.3.2, Appendix B.5).
//!
//! Probes (§6.2.4) and persistent congestion (§7.6.2) are the caller's to
//! invoke: `on_persistent` collapses the window to the minimum.
use vstd::prelude::*;

verus! {

/// The largest window, so that nothing overflows: 1 GiB.
pub const MAX_WINDOW: u64 = 0x4000_0000;

/// The controller's state, in bytes and microseconds.
#[derive(Clone, Copy, Debug)]
pub struct NewReno {
    /// congestion_window.
    pub cwnd: u64,
    /// ssthresh (`None`: infinite, slow start).
    pub ssthresh: Option<u64>,
    /// congestion_recovery_start_time.
    pub recovery: Option<u64>,
    /// max_datagram_size.
    pub mds: u64,
    /// Bytes acknowledged in congestion avoidance towards the next window
    /// increase (Appendix B.5, counted in bytes).
    pub acc: u64,
}

/// kMinimumWindow (§7.2).
pub open spec fn min_window(mds: u64) -> nat {
    2 * mds as nat
}

/// `p` was sent during the current recovery period (§7.3.2).
pub open spec fn in_recovery(c: NewReno, sent: u64) -> bool {
    c.recovery matches Some(r) && sent <= r
}

/// Appendix B.5, OnPacketsAcked for one in-flight packet of `size`
/// bytes sent at `sent`: no change in recovery or when application
/// limited; slow start adds the bytes; congestion avoidance one
/// datagram per window of bytes acknowledged. Capped at [`MAX_WINDOW`].
pub open spec fn on_ack_spec(c: NewReno, sent: u64, size: u64, app_limited: bool) -> NewReno {
    if in_recovery(c, sent) || app_limited {
        c
    } else if c.ssthresh is None || c.cwnd < c.ssthresh.unwrap() {
        NewReno { cwnd: if c.cwnd + size > MAX_WINDOW { MAX_WINDOW } else { (c.cwnd + size) as u64 }, ..c }
    } else if c.acc + size >= c.cwnd {
        NewReno {
            cwnd: if c.cwnd + c.mds > MAX_WINDOW { MAX_WINDOW } else { (c.cwnd + c.mds) as u64 },
            acc: (c.acc + size - c.cwnd) as u64,
            ..c
        }
    } else {
        NewReno { acc: (c.acc + size) as u64, ..c }
    }
}

/// Appendix B.6, OnCongestionEvent for a packet sent at `sent`, at `now`:
/// nothing during the current recovery period; otherwise a new period
/// starts, and ssthresh and the window become half the window, but not
/// below the minimum (kLossReductionFactor is 1/2).
pub open spec fn on_congestion_spec(c: NewReno, sent: u64, now: u64) -> NewReno {
    if in_recovery(c, sent) {
        c
    } else {
        let half = c.cwnd / 2;
        let w = if half < min_window(c.mds) { min_window(c.mds) as u64 } else { half as u64 };
        NewReno { cwnd: w, ssthresh: Some(w), recovery: Some(now), acc: 0, ..c }
    }
}

impl NewReno {
    /// The window is between the minimum and [`MAX_WINDOW`], and the
    /// bytes towards the next increase are below it.
    pub open spec fn inv(&self) -> bool {
        &&& 1200 <= self.mds <= 65527
        &&& min_window(self.mds) <= self.cwnd <= MAX_WINDOW
        &&& self.ssthresh matches Some(s) ==> min_window(self.mds) <= s <= MAX_WINDOW
        &&& self.acc < self.cwnd
    }

    /// §7.2: an initial window of `min(10 * max_datagram_size,
    /// max(14720, 2 * max_datagram_size))`, in slow start.
    pub fn new(mds: u64) -> (r: NewReno)
        requires
            1200 <= mds <= 65527,
        ensures
            r.inv(),
            r.mds == mds,
            r.recovery is None,
            r.ssthresh is None,
    {
        let a = if 14720 > 2 * mds { 14720 } else { 2 * mds };
        let w = if 10 * mds < a { 10 * mds } else { a };
        NewReno { cwnd: w, ssthresh: None, recovery: None, mds, acc: 0 }
    }

    /// Whether a packet of `size` bytes may be sent with `in_flight`
    /// bytes in flight.
    pub fn can_send(&self, in_flight: u64, size: u64) -> (r: bool)
        ensures
            r == (in_flight as nat + size as nat <= self.cwnd as nat),
    {
        in_flight <= self.cwnd && size <= self.cwnd - in_flight
    }

    /// The bytes that may still be sent with `in_flight` in flight.
    pub fn room(&self, in_flight: u64) -> (r: u64)
        ensures
            in_flight as nat + r as nat <= self.cwnd as nat || r == 0,
            in_flight <= self.cwnd ==> r == self.cwnd - in_flight,
    {
        if in_flight >= self.cwnd {
            0
        } else {
            self.cwnd - in_flight
        }
    }

    /// An in-flight packet of `size` bytes (at most one datagram) sent at
    /// `sent` was acknowledged.
    pub fn on_ack(&mut self, sent: u64, size: u64, app_limited: bool)
        requires
            old(self).inv(),
            size <= old(self).mds,
        ensures
            final(self).inv(),
            *final(self) == on_ack_spec(*old(self), sent, size, app_limited),
    {
        let rec = match self.recovery {
            Some(r) => sent <= r,
            None => false,
        };
        if rec || app_limited {
            return;
        }
        let slow = match self.ssthresh {
            None => true,
            Some(s) => self.cwnd < s,
        };
        if slow {
            self.cwnd = if self.cwnd + size > MAX_WINDOW { MAX_WINDOW } else { self.cwnd + size };
        } else if self.acc + size >= self.cwnd {
            self.acc = self.acc + size - self.cwnd;
            self.cwnd = if self.cwnd + self.mds > MAX_WINDOW { MAX_WINDOW } else { self.cwnd + self.mds };
        } else {
            self.acc = self.acc + size;
        }
    }

    /// A loss, or an increase in ECN-CE (§7.1), for a packet sent at `sent`,
    /// seen at `now`.
    pub fn on_congestion(&mut self, sent: u64, now: u64)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            *final(self) == on_congestion_spec(*old(self), sent, now),
            final(self).cwnd <= old(self).cwnd,
    {
        let rec = match self.recovery {
            Some(r) => sent <= r,
            None => false,
        };
        if rec {
            return;
        }
        let half = self.cwnd / 2;
        let w = if half < 2 * self.mds { 2 * self.mds } else { half };
        self.cwnd = w;
        self.ssthresh = Some(w);
        self.recovery = Some(now);
        self.acc = 0;
    }

    /// Persistent congestion (§7.6.2): the window collapses to the
    /// minimum, and the recovery period ends.
    pub fn on_persistent(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).cwnd == min_window(old(self).mds),
            final(self).recovery is None,
    {
        self.cwnd = 2 * self.mds;
        self.recovery = None;
        self.acc = 0;
    }
}

} // verus!
