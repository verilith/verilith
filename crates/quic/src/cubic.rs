//! CUBIC congestion control (RFC 9438), in integer arithmetic, with the
//! same guarantees as [`crate::cc::NewReno`]:
//!
//! - the window never falls below kMinimumWindow, two datagrams (RFC 9002
//!   §7.2), nor rises above [`MAX_WINDOW`];
//! - [`Cubic::can_send`] and [`Cubic::room`] are exactly NewReno's, so a
//!   sender that asks them never has more in flight than the window;
//! - the window is reduced at most once per recovery period, and
//!   acknowledgments of packets sent before the period began do not grow
//!   it (RFC 9002 §7.3.2; RFC 9438 §4.1 keeps those rules);
//! - an acknowledgment never shrinks the window, and in congestion
//!   avoidance grows it by at most half (RFC 9438 §4.2: the target is
//!   capped at 1.5 times the window), towards `goal`, the larger of the
//!   cubic window `w_cubic` and the Reno-friendly estimate (§4.3);
//! - a congestion event sets the window to [`BETA_NUM`]/[`BETA_DEN`] (0.7)
//!   of itself, and remembers W_max with fast convergence (§4.6, §4.7).
//!
//! Time is in microseconds, windows in bytes. The cubic function is
//! evaluated in units of 1/1024 s, with the time since the epoch capped at
//! [`T_MAX`] (about 68 minutes), and C = 0.4 datagrams per second cubed.
//! Slow start is RFC 9002's (the window grows by the bytes acknowledged);
//! HyStart++ is not used.
pub use crate::cc::MAX_WINDOW;
use vstd::prelude::*;

verus! {

/// The numerator of β_cubic = 0.7 (RFC 9438 §4.6).
pub const BETA_NUM: u64 = 7;
/// The denominator of β_cubic.
pub const BETA_DEN: u64 = 10;

/// The cubic function's time is capped here, in 1/1024 s.
pub const T_MAX: u64 = 0x40_0000;

/// The controller's state.
#[derive(Clone, Copy, Debug)]
pub struct Cubic {
    /// cwnd.
    pub cwnd: u64,
    /// ssthresh (`None`: infinite, slow start).
    pub ssthresh: Option<u64>,
    /// congestion_recovery_start_time.
    pub recovery: Option<u64>,
    /// max_datagram_size.
    pub mds: u64,
    /// W_max: the window before the last reduction (§4.6, §4.7).
    pub w_max: u64,
    /// K (§4.2), in 1/1024 s: when the cubic function reaches `w_max`.
    pub k: u64,
    /// The start of the current congestion avoidance stage, microseconds;
    /// `None` until the first acknowledgment in it.
    pub epoch: Option<u64>,
    /// W_est, the Reno-friendly estimate (§4.3).
    pub w_est: u64,
    /// Growth not yet added to the window: bytes times bytes, below the
    /// window (the window grows by `acc / cwnd`).
    pub acc: u64,
}

/// kMinimumWindow for `mds`, the same as NewReno's.
pub open spec fn cmin(mds: u64) -> nat {
    2 * mds as nat
}

/// The packet sent at `sent` belongs to the current recovery period.
pub open spec fn in_recovery(c: Cubic, sent: u64) -> bool {
    c.recovery matches Some(r) && sent <= r
}

/// Slow start: no ssthresh yet, or below it.
pub open spec fn slow(c: Cubic) -> bool {
    c.ssthresh is None || c.cwnd < c.ssthresh.unwrap()
}

/// The time in the cubic function, in 1/1024 s: from the epoch's start
/// to one smoothed RTT after `now` (§4.2: W_cubic(t + RTT)), capped.
pub open spec fn t_units(epoch: u64, now: u64, srtt: u64) -> nat {
    let us = if now >= epoch { (now - epoch) as nat } else { 0 } + srtt as nat;
    let t = us * 1024 / 1_000_000;
    if t > T_MAX { T_MAX as nat } else { t }
}

/// W_cubic(t) = C * (t - K)^3 + W_max (§4.2, equation 1), in bytes, with
/// C = 0.4 datagrams per second cubed and `t`, `k` in 1/1024 s; clamped to
/// [0, MAX_WINDOW].
pub open spec fn w_cubic(w_max: u64, k: u64, mds: u64, t: nat) -> nat {
    if t >= k {
        let d = (t - k) as nat;
        let w = w_max as nat + 4 * mds as nat * (d * d * d) / (10 * 0x4000_0000);
        if w > MAX_WINDOW as nat { MAX_WINDOW as nat } else { w }
    } else {
        let d = (k - t) as nat;
        let s = 4 * mds as nat * (d * d * d) / (10 * 0x4000_0000);
        if s >= w_max as nat { 0 } else { (w_max - s) as nat }
    }
}

/// What the window grows towards in congestion avoidance: W_est where it
/// is above W_cubic (the Reno-friendly region, §4.3), else W_cubic; at
/// least the window, and at most 1.5 times it (§4.2).
pub open spec fn goal(cwnd: u64, w_est: u64, wc: nat) -> nat {
    let g = if wc < w_est as nat { w_est as nat } else { wc };
    let hi = cwnd as nat + cwnd as nat / 2;
    if g < cwnd as nat { cwnd as nat } else if g > hi { hi } else { g }
}

/// K for a reduction from `w_max` to `cwnd`: the cube root of
/// (W_max - cwnd) / C, in 1/1024 s (§4.2, equation 2, with cwnd for
/// W_max * β).
pub open spec fn k_of(w_max: u64, cwnd: u64, mds: u64) -> nat {
    if w_max <= cwnd {
        0
    } else {
        let x = (w_max - cwnd) as nat * 10 * 0x4000_0000 / (4 * mds as nat);
        cube_root(if x >= 0x4000_0000_0000_0000 { (0x4000_0000_0000_0000 - 1) as nat } else { x })
    }
}

/// `r` is ⌊∛x⌋.
pub open spec fn is_cbrt(r: nat, x: nat) -> bool {
    r * r * r <= x && x < (r + 1) * (r + 1) * (r + 1)
}

/// ⌊∛x⌋.
pub open spec fn cube_root(x: nat) -> nat {
    choose|r: nat| #[trigger] is_cbrt(r, x)
}

/// The reduction on a congestion event (§4.6, §4.7): nothing during the
/// current recovery period; otherwise W_max is the window (or 0.85 of it
/// when it is below the last W_max: fast convergence), the window and
/// ssthresh become 0.7 of it (at least the minimum), and a new recovery
/// period and congestion avoidance stage begin.
pub open spec fn on_congestion_spec(c: Cubic, sent: u64, now: u64) -> Cubic {
    if in_recovery(c, sent) {
        c
    } else {
        let wm = if c.cwnd < c.w_max { (c.cwnd as nat * 17 / 20) as u64 } else { c.cwnd };
        let r = c.cwnd as nat * BETA_NUM as nat / BETA_DEN as nat;
        let w = if r < cmin(c.mds) { cmin(c.mds) as u64 } else { r as u64 };
        Cubic { cwnd: w, ssthresh: Some(w), recovery: Some(now), w_max: wm, epoch: None, acc: 0, ..c }
    }
}

/// x³ for x < 2²¹, which fits in a u64.
#[inline(always)]
fn cube(x: u64) -> (r: u64)
    requires
        x < 0x20_0000,
    ensures
        r as nat == x as nat * x as nat * x as nat,
{
    proof {
        assert(x * x < 0x400_0000_0000) by (nonlinear_arith)
            requires
                x < 0x20_0000,
        ;
        assert(x * x * x < 0x8000_0000_0000_0000) by (nonlinear_arith)
            requires
                x < 0x20_0000,
                x * x < 0x400_0000_0000,
        ;
    }
    x * x * x
}

proof fn lemma_cube_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        a * a * a <= b * b * b,
{
    assert(a * a <= b * b) by (nonlinear_arith)
        requires
            a <= b,
    ;
    assert(a * a * a <= b * b * b) by (nonlinear_arith)
        requires
            a <= b,
            a * a <= b * b,
    ;
}

/// ⌊∛x⌋ by bisection, for x < 2⁶².
fn cbrt(x: u64) -> (r: u64)
    requires
        x < 0x4000_0000_0000_0000,
    ensures
        r < 0x20_0000,
        r as nat == cube_root(x as nat),
{
    let mut lo: u64 = 0;
    let mut hi: u64 = 0x20_0000;
    proof {
        assert(0x20_0000nat * 0x20_0000nat * 0x20_0000nat == 0x8000_0000_0000_0000nat) by (compute);
    }
    while hi - lo > 1
        invariant
            lo < hi <= 0x20_0000,
            lo as nat * lo as nat * lo as nat <= x as nat,
            (x as nat) < hi as nat * hi as nat * hi as nat,
        decreases hi - lo,
    {
        let m = lo + (hi - lo) / 2;
        if cube(m) <= x {
            lo = m;
        } else {
            hi = m;
        }
    }
    proof {
        assert(hi == lo + 1);
        let r = lo as nat;
        assert(is_cbrt(r, x as nat));
        let c = cube_root(x as nat);
        assert(is_cbrt(c, x as nat));
        // The cube is strictly increasing, so the root is unique.
        if c < r {
            lemma_cube_mono(c + 1, r);
        } else if c > r {
            lemma_cube_mono(r + 1, c);
        }
    }
    lo
}

impl Cubic {
    /// The window is between the minimum and [`MAX_WINDOW`], and so are
    /// ssthresh, W_max and W_est; the growth carried is below the window.
    pub open spec fn inv(&self) -> bool {
        &&& 1200 <= self.mds <= 65527
        &&& cmin(self.mds) <= self.cwnd <= MAX_WINDOW
        &&& self.ssthresh matches Some(s) ==> cmin(self.mds) <= s <= MAX_WINDOW
        &&& self.w_max <= MAX_WINDOW
        &&& 1200 <= self.w_est <= MAX_WINDOW
        &&& self.k < 0x20_0000
        &&& self.acc < self.cwnd
    }

    /// The initial window of RFC 9002 §7.2, in slow start.
    pub fn new(mds: u64) -> (r: Cubic)
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
        Cubic { cwnd: w, ssthresh: None, recovery: None, mds, w_max: 0, k: 0, epoch: None, w_est: w, acc: 0 }
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

    /// W_cubic at time `t` (1/1024 s).
    fn w_cubic(&self, t: u64) -> (r: u64)
        requires
            self.inv(),
            t <= T_MAX,
        ensures
            r as nat == w_cubic(self.w_max, self.k, self.mds, t as nat),
            r <= MAX_WINDOW,
    {
        let (d, up) = if t >= self.k { (t - self.k, true) } else { (self.k - t, false) };
        proof {
            assert(d <= T_MAX);
            assert(d * d <= 0x10_0000_0000_0000) by (nonlinear_arith)
                requires
                    d <= 0x40_0000,
            ;
            assert(d * d * d <= 0x4000_0000_0000_0000_0000) by (nonlinear_arith)
                requires
                    d <= 0x40_0000,
                    d * d <= 0x10_0000_0000_0000,
            ;
            assert(4 * self.mds * (d * d * d) <= 4 * 65527 * 0x4000_0000_0000_0000_0000) by (nonlinear_arith)
                requires
                    self.mds <= 65527,
                    d * d * d <= 0x4000_0000_0000_0000_0000,
            ;
        }
        let d3 = d as u128 * d as u128 * d as u128;
        let s = 4 * self.mds as u128 * d3 / (10 * 0x4000_0000);
        if up {
            let w = self.w_max as u128 + s;
            if w > MAX_WINDOW as u128 {
                MAX_WINDOW
            } else {
                w as u64
            }
        } else if s >= self.w_max as u128 {
            0
        } else {
            self.w_max - s as u64
        }
    }

    /// An in-flight packet of `size` bytes (at most one datagram) sent at
    /// `sent` was acknowledged at `now`, with smoothed RTT `srtt`
    /// (microseconds).
    #[verifier::rlimit(40)]
    pub fn on_ack(&mut self, sent: u64, size: u64, app_limited: bool, now: u64, srtt: u64)
        requires
            old(self).inv(),
            size <= old(self).mds,
            srtt <= 0xFFFF_FFFF,
        ensures
            final(self).inv(),
            final(self).mds == old(self).mds,
            final(self).recovery == old(self).recovery,
            final(self).ssthresh == old(self).ssthresh,
            in_recovery(*old(self), sent) || app_limited ==> *final(self) == *old(self),
            old(self).cwnd <= final(self).cwnd,
            !in_recovery(*old(self), sent) && !app_limited && slow(*old(self)) ==> final(self).cwnd == if old(
                self,
            ).cwnd + size > MAX_WINDOW {
                MAX_WINDOW
            } else {
                (old(self).cwnd + size) as u64
            },
            !in_recovery(*old(self), sent) && !app_limited && !slow(*old(self)) ==> final(self).cwnd as nat <= goal(
                old(self).cwnd,
                final(self).w_est,
                w_cubic(
                    final(self).w_max,
                    final(self).k,
                    final(self).mds,
                    t_units(final(self).epoch.unwrap(), now, srtt),
                ),
            ) && final(self).epoch is Some,
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
            if self.acc >= self.cwnd {
                self.acc = 0;
            }
            return;
        }
        // The first acknowledgment of a congestion avoidance stage starts
        // its epoch (§4.2): K from W_max, and W_est from the window (§4.3).
        let epoch = match self.epoch {
            Some(e) => e,
            None => {
                if self.w_max <= self.cwnd {
                    self.w_max = self.cwnd;
                    self.k = 0;
                } else {
                    let dw = self.w_max - self.cwnd;
                    proof {
                        assert(dw as nat * 0x2_8000_0000nat <= 0x4000_0000nat * 0x2_8000_0000nat) by (nonlinear_arith)
                            requires
                                dw <= 0x4000_0000,
                        ;
                    }
                    let x = dw as u128 * (10 * 0x4000_0000) / (4 * self.mds as u128);
                    let x = if x >= 0x4000_0000_0000_0000 { 0x4000_0000_0000_0000 - 1 } else { x as u64 };
                    self.k = cbrt(x);
                }
                self.w_est = self.cwnd;
                self.epoch = Some(now);
                now
            },
        };
        let us = if now >= epoch { now - epoch } else { 0 };
        let t = (us as u128 + srtt as u128) * 1024 / 1_000_000;
        let t = if t > T_MAX as u128 { T_MAX } else { t as u64 };
        let wc = self.w_cubic(t);
        // W_est += α · bytes acknowledged · mds / W_est, α = 3(1-β)/(1+β)
        // = 9/17 (§4.3, equation 4, in bytes).
        proof {
            assert(9 * self.mds as nat * size as nat <= 9 * 65527nat * 65527nat) by (nonlinear_arith)
                requires
                    self.mds <= 65527,
                    size <= 65527,
            ;
        }
        let inc = 9 * self.mds as u128 * size as u128 / (17 * self.w_est as u128);
        let e = self.w_est as u128 + inc;
        self.w_est = if e > MAX_WINDOW as u128 { MAX_WINDOW } else { e as u64 };
        let g = if wc < self.w_est { self.w_est } else { wc };
        let hi = self.cwnd + self.cwnd / 2;
        let g = if g < self.cwnd { self.cwnd } else if g > hi { hi } else { g };
        // (goal - cwnd) / cwnd per byte acknowledged (§4.4), carried in
        // `acc` until it makes a whole byte.
        let dg = g - self.cwnd;
        proof {
            assert(dg as nat * size as nat <= dg as nat * self.cwnd as nat) by (nonlinear_arith)
                requires
                    size <= self.cwnd,
            ;
            assert(dg as nat * self.cwnd as nat <= 0x4000_0000nat * 0x4000_0000nat) by (nonlinear_arith)
                requires
                    dg <= 0x4000_0000,
                    self.cwnd <= 0x4000_0000,
            ;
        }
        let a = self.acc as u128 + dg as u128 * size as u128;
        let n = a / self.cwnd as u128;
        let rest = a % self.cwnd as u128;
        proof {
            let (ai, ci, ni, di) = (a as int, self.cwnd as int, n as int, dg as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ai, ci);
            assert(ai < ci * (di + 1)) by (nonlinear_arith)
                requires
                    ai < ci + di * ci,
            ;
            assert(ni <= di) by (nonlinear_arith)
                requires
                    ai == ci * (ai / ci) + ai % ci,
                    ai % ci >= 0,
                    ni == ai / ci,
                    ai < ci * (di + 1),
                    ci > 0,
            ;
        }
        self.cwnd = self.cwnd + n as u64;
        self.acc = rest as u64;
    }

    /// A loss, or an increase in ECN-CE, for a packet sent at `sent`, seen
    /// at `now`.
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
        self.w_max = if self.cwnd < self.w_max { self.cwnd / 20 * 17 + self.cwnd % 20 * 17 / 20 } else { self.cwnd };
        proof {
            assert(self.cwnd / 20 * 17 + self.cwnd % 20 * 17 / 20 == self.cwnd * 17 / 20) by (nonlinear_arith);
        }
        let r = self.cwnd / BETA_DEN * BETA_NUM + self.cwnd % BETA_DEN * BETA_NUM / BETA_DEN;
        proof {
            assert(r == self.cwnd * 7 / 10) by (nonlinear_arith)
                requires
                    r == self.cwnd / 10 * 7 + self.cwnd % 10 * 7 / 10,
            ;
        }
        let w = if r < 2 * self.mds { 2 * self.mds } else { r };
        self.cwnd = w;
        self.ssthresh = Some(w);
        self.recovery = Some(now);
        self.epoch = None;
        self.acc = 0;
    }

    /// Persistent congestion (RFC 9002 §7.6.2): the window collapses to
    /// the minimum, the recovery period ends, and so does the congestion
    /// avoidance stage.
    pub fn on_persistent(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).cwnd == cmin(old(self).mds),
            final(self).recovery is None,
    {
        self.cwnd = 2 * self.mds;
        self.recovery = None;
        self.epoch = None;
        self.acc = 0;
    }

    /// A larger max_datagram_size, once path MTU discovery found the path
    /// carries it: the window and ssthresh are raised to at least the new
    /// minimum.
    pub fn raise_mds(&mut self, mds: u64)
        requires
            old(self).inv(),
            old(self).mds <= mds <= 65527,
        ensures
            final(self).inv(),
            final(self).mds == mds,
            final(self).cwnd == if old(self).cwnd < cmin(mds) { cmin(mds) as u64 } else { old(self).cwnd },
            final(self).recovery == old(self).recovery,
    {
        self.mds = mds;
        if self.cwnd < 2 * mds {
            self.cwnd = 2 * mds;
        }
        if let Some(s) = self.ssthresh {
            if s < 2 * mds {
                self.ssthresh = Some(2 * mds);
            }
        }
    }
}

} // verus!
