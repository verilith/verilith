//! A connection's timers (RFC 9000 §10.1, §10.2; RFC 9002 §6.1.2, §6.2.1,
//! Appendix A.8): when the next one is due, and which one fires.
//!
//! Proven:
//!
//! - [`idle_timeout`] is the smaller of the two advertised idle timeouts
//!   that are not zero, and at least three PTOs (§10.1), with no overflow
//!   however large the peer's value;
//! - [`pto_deadline`] is the earliest PTO over the spaces that have one,
//!   with the backoff applied (§6.2.1);
//! - [`next`] is the earliest armed timer, where the PTO is armed only if
//!   no loss timer is (A.8) and the anti-amplification limit allows sending
//!   (§6.2.2.1);
//! - [`due`] picks the timer that fires at `now`: the idle timeout first,
//!   then the first loss timer due, then the PTO; and at the time [`next`]
//!   returns, something is due (unless only a delayed ACK is), so a caller
//!   that sleeps until [`next`] never wakes for nothing.
use vstd::prelude::*;

verus! {

pub open spec fn smin(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

pub open spec fn smax(a: u64, b: u64) -> u64 {
    if a > b { a } else { b }
}

/// `a * b`, or `u64::MAX` if larger.
pub open spec fn sat_mul(a: u64, b: u64) -> u64 {
    if a * b > u64::MAX { u64::MAX } else { (a * b) as u64 }
}

pub open spec fn sat_add(a: u64, b: u64) -> u64 {
    if a + b > u64::MAX { u64::MAX } else { (a + b) as u64 }
}

fn mul_sat(a: u64, b: u64) -> (r: u64)
    ensures
        r == sat_mul(a, b),
{
    if b != 0 && a > u64::MAX / b {
        proof {
            assert(a * b > u64::MAX) by (nonlinear_arith)
                requires
                    b != 0,
                    a > u64::MAX / b,
            ;
        }
        u64::MAX
    } else {
        proof {
            if b != 0 {
                assert(a * b <= u64::MAX) by (nonlinear_arith)
                    requires
                        b != 0,
                        a <= u64::MAX / b,
                ;
            }
        }
        a * b
    }
}

/// `a + b`, or `u64::MAX` if larger.
pub fn add_sat(a: u64, b: u64) -> (r: u64)
    ensures
        r == sat_add(a, b),
{
    if a > u64::MAX - b {
        u64::MAX
    } else {
        a + b
    }
}

/// The idle timeout in microseconds, from ours and the peer's
/// max_idle_timeout in milliseconds (0: none), given the current PTO.
pub fn idle_timeout(ours_ms: u64, peer_ms: u64, pto: u64) -> (r: Option<u64>)
    ensures
        ours_ms == 0 && peer_ms == 0 <==> r is None,
        r matches Some(t) ==> {
            let ms = if ours_ms == 0 {
                peer_ms
            } else if peer_ms == 0 {
                ours_ms
            } else {
                smin(ours_ms, peer_ms)
            };
            t == smax(sat_mul(ms, 1000), sat_mul(pto, 3))
        },
{
    let ms = if ours_ms == 0 {
        if peer_ms == 0 {
            return None;
        }
        peer_ms
    } else if peer_ms == 0 {
        ours_ms
    } else if ours_ms < peer_ms {
        ours_ms
    } else {
        peer_ms
    };
    let a = mul_sat(ms, 1000);
    let b = mul_sat(pto, 3);
    Some(if a > b { a } else { b })
}

/// The earliest PTO: for each space with an ack-eliciting packet in
/// flight (`last[s]`, the time the last one was sent) and a PTO period
/// `dur[s]`, `last[s] + backoff(dur[s], count)`; the first such space on a
/// tie.
pub fn pto_deadline(last: &[Option<u64>; 3], dur: &[u64; 3], count: u32) -> (r: Option<(u64, usize)>)
    ensures
        r is None <==> (forall|s: int| 0 <= s < 3 ==> last@[s] is None),
        r matches Some((t, s)) ==> {
            &&& 0 <= s < 3
            &&& last@[s as int] is Some
            &&& t == sat_add(last@[s as int]->0, backoff_spec(dur@[s as int], count))
            &&& forall|u: int|
                0 <= u < 3 && #[trigger] last@[u] is Some ==> sat_add(last@[u]->0, backoff_spec(dur@[u], count))
                    >= t
            &&& forall|u: int|
                0 <= u < s && #[trigger] last@[u] is Some ==> sat_add(last@[u]->0, backoff_spec(dur@[u], count))
                    > t
        },
{
    let mut best: Option<(u64, usize)> = None;
    let mut s: usize = 0;
    while s < 3
        invariant
            0 <= s <= 3,
            best is None <==> (forall|u: int| 0 <= u < s ==> last@[u] is None),
            best matches Some((t, b)) ==> {
                &&& 0 <= b < s
                &&& last@[b as int] is Some
                &&& t == sat_add(last@[b as int]->0, backoff_spec(dur@[b as int], count))
                &&& forall|u: int|
                    0 <= u < s && #[trigger] last@[u] is Some ==> sat_add(last@[u]->0, backoff_spec(dur@[u], count))
                        >= t
                &&& forall|u: int|
                    0 <= u < b && #[trigger] last@[u] is Some ==> sat_add(last@[u]->0, backoff_spec(dur@[u], count))
                        > t
            },
        decreases 3 - s,
    {
        if let Some(l) = last[s] {
            let d = backoff_exec(dur[s], count);
            let at = add_sat(l, d);
            let better = match best {
                None => true,
                Some((b, _)) => at < b,
            };
            if better {
                best = Some((at, s));
            }
        }
        s = s + 1;
    }
    best
}

/// `rtt::backoff`, as a spec.
pub open spec fn backoff_spec(pto: u64, count: u32) -> u64
    decreases count,
{
    backoff_loop(pto, if count < 32 { count as int } else { 32 })
}

pub open spec fn backoff_loop(r: u64, n: int) -> u64
    decreases n,
{
    if n <= 0 {
        r
    } else {
        backoff_loop(if r > u64::MAX / 2 { u64::MAX } else { (2 * r) as u64 }, n - 1)
    }
}

/// The PTO period after `count` expirations without an acknowledgment:
/// doubled each time (at most 32 times), saturating (as `rtt::backoff`).
pub fn backoff_exec(pto: u64, count: u32) -> (r: u64)
    ensures
        r == backoff_spec(pto, count),
        r >= pto,
{
    let n: u32 = if count < 32 { count } else { 32 };
    let mut r = pto;
    let mut i: u32 = 0;
    while i < n
        invariant
            0 <= i <= n <= 32,
            r >= pto,
            backoff_loop(r, n - i) == backoff_spec(pto, count),
        decreases n - i,
    {
        r = if r > u64::MAX / 2 { u64::MAX } else { 2 * r };
        i = i + 1;
    }
    r
}

/// The armed timers of a connection that is not closing.
pub struct Timers {
    /// When the idle timeout fires.
    pub idle: Option<u64>,
    /// Each space's loss timer (§6.1.2).
    pub loss: [Option<u64>; 3],
    /// The earliest PTO, and its space.
    pub pto: Option<(u64, usize)>,
    /// The anti-amplification limit allows sending something.
    pub can_send: bool,
    /// When a delayed ACK is owed.
    pub ack: Option<u64>,
}

/// Some loss timer is armed.
pub open spec fn any_loss(t: Timers) -> bool {
    exists|s: int| 0 <= s < 3 && #[trigger] t.loss@[s] is Some
}

/// The PTO counts only without a loss timer (A.8), and when sending is
/// allowed (§6.2.2.1).
pub open spec fn pto_armed(t: Timers) -> bool {
    t.pto is Some && !any_loss(t) && t.can_send
}

/// `x` is the deadline of an armed timer.
pub open spec fn armed(t: Timers, x: u64) -> bool {
    ||| t.idle == Some(x)
    ||| (exists|s: int| 0 <= s < 3 && #[trigger] t.loss@[s] == Some(x))
    ||| (pto_armed(t) && (t.pto->0).0 == x)
    ||| t.ack == Some(x)
}

/// `x` is no later than any armed timer.
pub open spec fn earliest(t: Timers, x: u64) -> bool {
    &&& (t.idle matches Some(i) ==> x <= i)
    &&& forall|s: int| 0 <= s < 3 && #[trigger] t.loss@[s] is Some ==> x <= t.loss@[s]->0
    &&& (pto_armed(t) ==> x <= (t.pto->0).0)
    &&& (t.ack matches Some(a) ==> x <= a)
}

fn min_opt(a: Option<u64>, b: u64) -> (r: Option<u64>)
    ensures
        r == Some(match a {
            Some(x) => smin(x, b),
            None => b,
        }),
{
    match a {
        Some(x) => Some(if x < b { x } else { b }),
        None => Some(b),
    }
}

/// When the next timer fires: the earliest armed one.
pub fn next(t: &Timers) -> (r: Option<u64>)
    ensures
        r matches Some(x) ==> armed(*t, x) && earliest(*t, x),
        r is None ==> t.idle is None && !any_loss(*t) && !pto_armed(*t) && t.ack is None,
{
    let mut r: Option<u64> = None;
    if let Some(i) = t.idle {
        r = min_opt(r, i);
    }
    let mut loss = false;
    let mut s: usize = 0;
    while s < 3
        invariant
            0 <= s <= 3,
            loss == (exists|u: int| 0 <= u < s && #[trigger] t.loss@[u] is Some),
            r is None ==> t.idle is None && !loss,
            r matches Some(x) ==> {
                &&& (t.idle == Some(x) || (exists|u: int| 0 <= u < s && #[trigger] t.loss@[u] == Some(x)))
                &&& (t.idle matches Some(i) ==> x <= i)
                &&& forall|u: int| 0 <= u < s && #[trigger] t.loss@[u] is Some ==> x <= t.loss@[u]->0
            },
        decreases 3 - s,
    {
        if let Some(l) = t.loss[s] {
            r = min_opt(r, l);
            loss = true;
            proof {
                assert(t.loss@[s as int] is Some);
            }
        }
        s = s + 1;
    }
    proof {
        assert(loss == any_loss(*t));
    }
    if !loss && t.can_send {
        if let Some((p, _)) = t.pto {
            r = min_opt(r, p);
        }
    }
    if let Some(a) = t.ack {
        r = min_opt(r, a);
    }
    r
}

/// The timer that fires at `now`.
pub enum Due {
    /// No timer is due.
    Nothing,
    /// The idle timeout: close silently (§10.1).
    Idle,
    /// Space `s`'s loss timer: detect lost packets there (§6.1.2).
    Loss(usize),
    /// The PTO in space `s`: send probes (§6.2.4).
    Pto(usize),
}

/// Which timer fires at `now`: the idle timeout, then the first loss timer
/// due, then the PTO (if armed); a delayed ACK is the sender's business.
pub fn due(t: &Timers, now: u64) -> (r: Due)
    ensures
        r is Idle <==> (t.idle matches Some(i) && i <= now),
        r matches Due::Loss(s) ==> {
            &&& 0 <= s < 3
            &&& t.loss@[s as int] matches Some(l) && l <= now
            &&& forall|u: int| 0 <= u < s ==> !(#[trigger] t.loss@[u] matches Some(l) && l <= now)
        },
        r matches Due::Pto(s) ==> pto_armed(*t) && (t.pto->0).0 <= now && s == (t.pto->0).1,
        r is Nothing ==> {
            &&& !(t.idle matches Some(i) && i <= now)
            &&& forall|u: int| 0 <= u < 3 ==> !(#[trigger] t.loss@[u] matches Some(l) && l <= now)
            &&& !(pto_armed(*t) && (t.pto->0).0 <= now)
        },
        // Whatever `next` returns, something is then due, unless it is a
        // delayed ACK's deadline.
        next_spec_due(*t, now) ==> !(r is Nothing),
{
    if let Some(i) = t.idle {
        if i <= now {
            return Due::Idle;
        }
    }
    let mut s: usize = 0;
    let mut loss = false;
    while s < 3
        invariant
            0 <= s <= 3,
            forall|u: int| 0 <= u < s ==> !(#[trigger] t.loss@[u] matches Some(l) && l <= now),
            loss == (exists|u: int| 0 <= u < s && #[trigger] t.loss@[u] is Some),
            !(t.idle matches Some(i) && i <= now),
        decreases 3 - s,
    {
        if let Some(l) = t.loss[s] {
            if l <= now {
                return Due::Loss(s);
            }
            loss = true;
            proof {
                assert(t.loss@[s as int] is Some);
            }
        }
        s = s + 1;
    }
    proof {
        assert(loss == any_loss(*t));
    }
    if !loss && t.can_send {
        if let Some((p, sp)) = t.pto {
            if p <= now {
                return Due::Pto(sp);
            }
        }
    }
    Due::Nothing
}

/// `now` is the deadline of an armed timer other than a delayed ACK.
pub open spec fn next_spec_due(t: Timers, now: u64) -> bool {
    ||| t.idle == Some(now)
    ||| (exists|s: int| 0 <= s < 3 && #[trigger] t.loss@[s] == Some(now))
    ||| (pto_armed(t) && (t.pto->0).0 == now)
}

} // verus!
