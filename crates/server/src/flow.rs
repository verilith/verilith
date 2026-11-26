//! HTTP/2 flow control (RFC 9113 §5.2, §6.9), verified.
//!
//! [`SendWindow`] is what the peer lets us send on a stream or on the
//! connection. Its invariant ties the window to what the peer granted and
//! what we sent: `w == granted - sent`, within ±(2^31 − 1). Credit beyond
//! 2^31 − 1 is refused (the caller's FLOW_CONTROL_ERROR, §6.9.1), and
//! [`take_data`] is the only way to spend it: the length of a DATA frame
//! is at most what both windows allow, so the server never sends more
//! than the peer granted (`sent <= granted` whenever the windows have not
//! been shrunk below zero by SETTINGS, which §6.9.2 allows).
//!
//! [`RecvWindow`] is what we let the peer send: a peer that sends more
//! than we advertised is caught (`unacked <= window` always), and a
//! WINDOW_UPDATE is due once half the window is used.
use vstd::prelude::*;

verus! {

pub const MAX_WINDOW: i64 = 0x7fff_ffff;

pub struct SendWindow {
    w: i64,
    granted: Ghost<int>,
    sent: Ghost<int>,
}

impl SendWindow {
    pub closed spec fn inv(&self) -> bool {
        &&& -MAX_WINDOW <= self.w <= MAX_WINDOW
        &&& self.w as int == self.granted@ - self.sent@
        &&& self.sent@ >= 0
    }

    pub closed spec fn value(&self) -> int {
        self.w as int
    }

    /// Credit the peer has granted, in all.
    pub closed spec fn granted(&self) -> int {
        self.granted@
    }

    /// Bytes taken for DATA frames, in all.
    pub closed spec fn sent(&self) -> int {
        self.sent@
    }

    /// A window of `initial` bytes (the peer's SETTINGS_INITIAL_WINDOW_SIZE,
    /// or 65,535 for the connection).
    pub fn new(initial: u32) -> (r: SendWindow)
        requires initial as int <= MAX_WINDOW,
        ensures r.inv(), r.value() == initial as int, r.sent() == 0,
    {
        SendWindow { w: initial as i64, granted: Ghost(initial as int), sent: Ghost(0) }
    }

    /// What may be sent now.
    pub fn avail(&self) -> (r: usize)
        requires self.inv(),
        ensures r as int == if self.value() > 0 { self.value() } else { 0 },
    {
        if self.w > 0 { self.w as usize } else { 0 }
    }

    /// A WINDOW_UPDATE of `inc`: false, and no change, if the window would
    /// pass 2^31 − 1 (a FLOW_CONTROL_ERROR, §6.9.1).
    pub fn grant(&mut self, inc: u32) -> (ok: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            ok == (old(self).value() + inc as int <= MAX_WINDOW),
            ok ==> final(self).value() == old(self).value() + inc as int && final(self).granted() == old(self).granted() + inc as int,
            !ok ==> *final(self) == *old(self),
            final(self).sent() == old(self).sent(),
    {
        if inc as i64 > MAX_WINDOW - self.w {
            return false;
        }
        self.w = self.w + inc as i64;
        self.granted = Ghost(self.granted@ + inc as int);
        true
    }

    /// The peer changed SETTINGS_INITIAL_WINDOW_SIZE by `delta` (§6.9.2;
    /// the window may go below zero): false, and no change, if it would
    /// leave ±(2^31 − 1).
    pub fn shift(&mut self, delta: i64) -> (ok: bool)
        requires old(self).inv(), -MAX_WINDOW <= delta <= MAX_WINDOW,
        ensures
            final(self).inv(),
            ok == (-MAX_WINDOW <= old(self).value() + delta <= MAX_WINDOW),
            ok ==> final(self).value() == old(self).value() + delta,
            !ok ==> *final(self) == *old(self),
            final(self).sent() == old(self).sent(),
    {
        let v = self.w + delta;
        if v > MAX_WINDOW || v < -MAX_WINDOW {
            return false;
        }
        self.w = v;
        self.granted = Ghost(self.granted@ + delta as int);
        true
    }
}

/// The length of the next DATA frame of a body with `left` bytes to go,
/// frames of at most `max` bytes, taken from both windows: at most what
/// each allows. Zero when either is spent.
pub fn take_data(conn: &mut SendWindow, stream: &mut SendWindow, left: usize, max: usize) -> (n: usize)
    requires old(conn).inv(), old(stream).inv(),
    ensures
        final(conn).inv(),
        final(stream).inv(),
        n <= left,
        n <= max,
        n > 0 ==> n as int <= old(conn).value() && n as int <= old(stream).value(),
        final(conn).value() == old(conn).value() - n,
        final(stream).value() == old(stream).value() - n,
        final(conn).sent() == old(conn).sent() + n,
        final(stream).sent() == old(stream).sent() + n,
        final(conn).granted() == old(conn).granted(),
        final(stream).granted() == old(stream).granted(),
        n == 0 ==> (left == 0 || max == 0 || old(conn).value() <= 0 || old(stream).value() <= 0),
{
    let mut n = left;
    if max < n {
        n = max;
    }
    let a = conn.avail();
    if a < n {
        n = a;
    }
    let b = stream.avail();
    if b < n {
        n = b;
    }
    conn.w = conn.w - n as i64;
    conn.sent = Ghost(conn.sent@ + n as int);
    stream.w = stream.w - n as i64;
    stream.sent = Ghost(stream.sent@ + n as int);
    n
}

/// What we let the peer send, on a stream or the connection.
pub struct RecvWindow {
    window: u32,
    unacked: u32,
    received: Ghost<int>,
    acked: Ghost<int>,
}

impl RecvWindow {
    pub closed spec fn inv(&self) -> bool {
        &&& self.window as int <= MAX_WINDOW
        &&& self.unacked <= self.window
        &&& self.received@ == self.acked@ + self.unacked as int
    }

    pub closed spec fn size(&self) -> u32 {
        self.window
    }

    pub closed spec fn used(&self) -> u32 {
        self.unacked
    }

    /// Flow-controlled bytes received, in all.
    pub closed spec fn received(&self) -> int {
        self.received@
    }

    /// A window of `window` bytes, advertised.
    pub fn new(window: u32) -> (r: RecvWindow)
        requires window as int <= MAX_WINDOW,
        ensures r.inv(), r.size() == window, r.used() == 0, r.received() == 0,
    {
        RecvWindow { window, unacked: 0, received: Ghost(0), acked: Ghost(0) }
    }

    /// `n` flow-controlled bytes arrived (a DATA frame's payload, padding
    /// included). Err if the peer sent past the window (FLOW_CONTROL_ERROR,
    /// §6.9.1); else the increment of a WINDOW_UPDATE to send now, if half
    /// the window is used.
    pub fn receive(&mut self, n: u32) -> (r: Result<Option<u32>, ()>)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).size() == old(self).size(),
            r is Err <==> old(self).used() as int + n as int > old(self).size() as int,
            r is Err ==> *final(self) == *old(self),
            r matches Ok(u) ==> final(self).received() == old(self).received() + n,
            r matches Ok(Some(inc)) ==> inc as int == old(self).used() as int + n as int && final(self).used() == 0 && inc > 0,
            r matches Ok(None) ==> final(self).used() as int == old(self).used() as int + n as int,
    {
        if n > self.window - self.unacked {
            return Err(());
        }
        self.unacked = self.unacked + n;
        self.received = Ghost(self.received@ + n as int);
        if self.unacked > 0 && self.unacked >= self.window / 2 {
            let inc = self.unacked;
            self.unacked = 0;
            self.acked = Ghost(self.acked@ + inc as int);
            Ok(Some(inc))
        } else {
            Ok(None)
        }
    }
}

} // verus!
