//! RTT estimation (RFC 9002 §5) and the timers it sets: the loss delay
//! (§6.1.2) and the probe timeout (§6.2.1), proven to compute exactly
//! `rtt_next`, `loss_delay_of` and `pto_of`.
//!
//! The RFC's arithmetic is over reals (`7/8 * smoothed_rtt + 1/8 *
//! adjusted_rtt`); here it is over whole microseconds, rounding down, as
//! quinn and other implementations do. Samples are clamped to
//! [`MAX_RTT`] (about 12 days), so nothing overflows and every value
//! stays below it.
use vstd::prelude::*;

verus! {

/// kGranularity (§6.1.2): 1 ms, in microseconds.
pub const GRANULARITY: u64 = 1000;

/// kInitialRtt (§6.2.2): 333 ms.
pub const INITIAL_RTT: u64 = 333_000;

/// The largest sample taken, in microseconds.
pub const MAX_RTT: u64 = 0x100_0000_0000;

/// kPersistentCongestionThreshold (§7.6.1).
pub const PERSISTENT_THRESHOLD: u64 = 3;

/// The estimator's state (§5.3), microseconds.
#[derive(Clone, Copy, Debug)]
pub struct Rtt {
    /// latest_rtt.
    pub latest: u64,
    /// smoothed_rtt.
    pub smoothed: u64,
    /// rttvar.
    pub var: u64,
    /// min_rtt.
    pub min: u64,
    /// Whether there has been a sample.
    pub sampled: bool,
}

/// §5.3: the estimator after an RTT sample `latest` with the peer's
/// `ack_delay`, capped at `max_ack_delay` once the handshake is
/// confirmed.
pub open spec fn rtt_next(r: Rtt, latest: int, ack_delay: int, max_ack_delay: int, confirmed: bool) -> Rtt {
    if !r.sampled {
        Rtt { latest: latest as u64, smoothed: latest as u64, var: (latest / 2) as u64, min: latest as u64, sampled: true }
    } else {
        let min = if latest < r.min { latest } else { r.min as int };
        let delay = if confirmed && ack_delay > max_ack_delay { max_ack_delay } else { ack_delay };
        let adjusted = if latest >= min + delay { latest - delay } else { latest };
        let diff = if r.smoothed >= adjusted { r.smoothed - adjusted } else { adjusted - r.smoothed };
        Rtt {
            latest: latest as u64,
            smoothed: ((7 * r.smoothed + adjusted) / 8) as u64,
            var: ((3 * r.var + diff) / 4) as u64,
            min: min as u64,
            sampled: true,
        }
    }
}

/// §6.1.2: `max(kTimeThreshold * max(smoothed_rtt, latest_rtt),
/// kGranularity)`, kTimeThreshold being 9/8.
pub open spec fn loss_delay_of(r: Rtt) -> int {
    let m = if r.latest > r.smoothed { r.latest as int } else { r.smoothed as int };
    let d = m + m / 8;
    if d > GRANULARITY { d } else { GRANULARITY as int }
}

/// §6.2.1: `smoothed_rtt + max(4 * rttvar, kGranularity)`, plus
/// `max_ack_delay` in the application data space.
pub open spec fn pto_of(r: Rtt, max_ack_delay: int) -> int {
    let v = if 4 * r.var > GRANULARITY { 4 * r.var } else { GRANULARITY as int };
    r.smoothed + v + max_ack_delay
}

/// §7.6.1: `(smoothed_rtt + max(4 * rttvar, kGranularity) +
/// max_ack_delay) * kPersistentCongestionThreshold`.
pub open spec fn persistent_of(r: Rtt, max_ack_delay: int) -> int {
    pto_of(r, max_ack_delay) * PERSISTENT_THRESHOLD
}

impl Rtt {
    /// Every value is below [`MAX_RTT`].
    pub open spec fn inv(&self) -> bool {
        &&& self.latest <= MAX_RTT
        &&& self.smoothed <= MAX_RTT
        &&& self.var <= MAX_RTT
        &&& self.min <= MAX_RTT
    }

    /// Before any sample (§6.2.2): smoothed_rtt is kInitialRtt and rttvar
    /// half of it.
    pub fn new() -> (r: Rtt)
        ensures
            r.inv(),
            !r.sampled,
            r.smoothed == INITIAL_RTT,
            r.var == INITIAL_RTT / 2,
    {
        Rtt { latest: 0, smoothed: INITIAL_RTT, var: INITIAL_RTT / 2, min: 0, sampled: false }
    }

    /// An RTT sample (§5.1: the time from sending the largest packet an ACK
    /// newly acknowledges, if ack-eliciting, to receiving the ACK), clamped
    /// to [`MAX_RTT`], with the ACK's delay (§5.3).
    pub fn update(&mut self, sample: u64, ack_delay: u64, max_ack_delay: u64, confirmed: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            *final(self) == rtt_next(
                *old(self),
                if sample > MAX_RTT { MAX_RTT as int } else { sample as int },
                ack_delay as int,
                max_ack_delay as int,
                confirmed,
            ),
    {
        let latest = if sample > MAX_RTT { MAX_RTT } else { sample };
        if !self.sampled {
            *self = Rtt { latest, smoothed: latest, var: latest / 2, min: latest, sampled: true };
            return;
        }
        let min = if latest < self.min { latest } else { self.min };
        let delay = if confirmed && ack_delay > max_ack_delay { max_ack_delay } else { ack_delay };
        let adjusted = if delay <= latest && latest - delay >= min { latest - delay } else { latest };
        let diff = if self.smoothed >= adjusted { self.smoothed - adjusted } else { adjusted - self.smoothed };
        self.latest = latest;
        self.smoothed = (7 * self.smoothed + adjusted) / 8;
        self.var = (3 * self.var + diff) / 4;
        self.min = min;
    }

    /// The loss delay (§6.1.2).
    pub fn loss_delay(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == loss_delay_of(*self),
    {
        let m = if self.latest > self.smoothed { self.latest } else { self.smoothed };
        let d = m + m / 8;
        if d > GRANULARITY { d } else { GRANULARITY }
    }

    /// The probe timeout's duration (§6.2.1), before backoff, with
    /// `max_ack_delay` (0 outside the application data space).
    pub fn pto(&self, max_ack_delay: u64) -> (r: u64)
        requires
            self.inv(),
            max_ack_delay <= MAX_RTT,
        ensures
            r == pto_of(*self, max_ack_delay as int),
            r <= 7 * MAX_RTT,
    {
        let v = if 4 * self.var > GRANULARITY { 4 * self.var } else { GRANULARITY };
        self.smoothed + v + max_ack_delay
    }

    /// The persistent congestion duration (§7.6.1).
    pub fn persistent(&self, max_ack_delay: u64) -> (r: u64)
        requires
            self.inv(),
            max_ack_delay <= MAX_RTT,
        ensures
            r == persistent_of(*self, max_ack_delay as int),
    {
        self.pto(max_ack_delay) * PERSISTENT_THRESHOLD
    }
}

/// The PTO with exponential backoff (§6.2.1): `pto * 2^count`, saturating.
pub fn backoff(pto: u64, count: u32) -> (r: u64)
    ensures
        r >= pto,
{
    let mut r = pto;
    let mut i: u32 = 0;
    while i < count && i < 32
        invariant
            r >= pto,
        decreases count - i,
    {
        r = if r > u64::MAX / 2 { u64::MAX } else { 2 * r };
        i = i + 1;
    }
    r
}

} // verus!
