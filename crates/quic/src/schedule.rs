//! When a server's keys for each packet number space are installed, used
//! and discarded (RFC 9001 §4.9, §5.7; RFC 9000 §17.2.2).
//!
//! Proven, of [`KeySchedule`]:
//!
//! - each space's keys go from not yet installed, to installed, to
//!   discarded, and never back (`rank` only grows), so discarded keys are
//!   never used again;
//! - Initial keys are discarded only on the first Handshake packet
//!   processed, so only once Handshake keys are installed (§4.9.1);
//! - Handshake keys are discarded only once the handshake is complete,
//!   which for a server is when it is confirmed (§4.9.2);
//! - 1-RTT packets are opened only once the handshake is complete (§5.7),
//!   while the server may send 1-RTT data as soon as its keys are
//!   installed (0.5-RTT data).
use vstd::prelude::*;

verus! {

/// One space's keys.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KeyState {
    /// Not installed yet.
    Absent,
    /// Installed.
    Ready,
    /// Discarded, for good.
    Discarded,
}

pub open spec fn rank(k: KeyState) -> int {
    match k {
        KeyState::Absent => 0,
        KeyState::Ready => 1,
        KeyState::Discarded => 2,
    }
}

/// The spaces: 0 Initial, 1 Handshake, 2 application data (1-RTT).
pub struct KeySchedule {
    initial: KeyState,
    handshake: KeyState,
    one_rtt: KeyState,
    complete: bool,
}

impl KeySchedule {
    pub closed spec fn state(&self, s: int) -> KeyState {
        if s == 0 {
            self.initial
        } else if s == 1 {
            self.handshake
        } else {
            self.one_rtt
        }
    }

    pub closed spec fn spec_complete(&self) -> bool {
        self.complete
    }

    pub closed spec fn inv(&self) -> bool {
        // Handshake and 1-RTT keys arrive together, with the server's flight.
        &&& (self.handshake == KeyState::Absent) == (self.one_rtt == KeyState::Absent)
        // Initial keys go once Handshake keys are in use.
        &&& self.initial == KeyState::Discarded ==> self.handshake != KeyState::Absent
        // Handshake keys go once the handshake is complete.
        &&& self.handshake == KeyState::Discarded <==> self.complete
        &&& self.complete ==> self.one_rtt == KeyState::Ready
        &&& self.initial != KeyState::Absent
        // 1-RTT keys are never discarded (only the connection ends).
        &&& self.one_rtt != KeyState::Discarded
    }

    /// Every space's keys moved forward or stayed.
    pub open spec fn later(&self, old: &KeySchedule) -> bool {
        &&& forall|s: int| 0 <= s < 3 ==> rank(#[trigger] old.state(s)) <= rank(self.state(s))
        &&& old.spec_complete() ==> self.spec_complete()
    }

    /// A new connection: only Initial keys.
    pub fn new() -> (r: KeySchedule)
        ensures
            r.inv(),
            r.state(0) == KeyState::Ready,
            r.state(1) == KeyState::Absent,
            r.state(2) == KeyState::Absent,
            !r.spec_complete(),
    {
        KeySchedule {
            initial: KeyState::Ready,
            handshake: KeyState::Absent,
            one_rtt: KeyState::Absent,
            complete: false,
        }
    }

    /// The handshake is complete (and, for a server, confirmed).
    #[verifier::when_used_as_spec(spec_complete)]
    pub fn complete(&self) -> (r: bool)
        ensures
            r == self.spec_complete(),
    {
        self.complete
    }

    /// Space `s`'s keys are discarded.
    pub fn discarded(&self, s: usize) -> (r: bool)
        requires
            s < 3,
        ensures
            r == (self.state(s as int) == KeyState::Discarded),
    {
        matches!(self.get(s), KeyState::Discarded)
    }

    fn get(&self, s: usize) -> (r: KeyState)
        requires
            s < 3,
        ensures
            r == self.state(s as int),
    {
        if s == 0 {
            self.initial
        } else if s == 1 {
            self.handshake
        } else {
            self.one_rtt
        }
    }

    /// Packets may be sent in space `s`: its keys are installed.
    pub fn may_send(&self, s: usize) -> (r: bool)
        requires
            s < 3,
        ensures
            r == (self.state(s as int) == KeyState::Ready),
    {
        matches!(self.get(s), KeyState::Ready)
    }

    /// Packets of space `s` may be opened: its keys are installed, and for
    /// 1-RTT the handshake is complete (§5.7).
    pub fn may_open(&self, s: usize) -> (r: bool)
        requires
            s < 3,
        ensures
            r == (self.state(s as int) == KeyState::Ready && (s == 2 ==> self.spec_complete())),
    {
        matches!(self.get(s), KeyState::Ready) && (s != 2 || self.complete)
    }

    /// The server's flight is written: Handshake and 1-RTT keys are
    /// installed. False (nothing changed) if they already were.
    pub fn on_server_flight(&mut self) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).later(&*old(self)),
            ok == (old(self).state(1) == KeyState::Absent),
            ok ==> final(self).state(1) == KeyState::Ready && final(self).state(2) == KeyState::Ready,
            final(self).state(0) == old(self).state(0),
            final(self).spec_complete() == old(self).spec_complete(),
            !ok ==> *final(self) == *old(self),
    {
        if !matches!(self.handshake, KeyState::Absent) {
            return false;
        }
        self.handshake = KeyState::Ready;
        self.one_rtt = KeyState::Ready;
        true
    }

    /// A Handshake packet was processed: Initial keys are discarded if they
    /// were not yet (§4.9.1). Returns whether they were just discarded.
    pub fn on_handshake_packet(&mut self) -> (now: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).later(&*old(self)),
            now == (old(self).state(0) == KeyState::Ready && old(self).state(1) != KeyState::Absent),
            now ==> final(self).state(0) == KeyState::Discarded,
            !now ==> *final(self) == *old(self),
            final(self).state(1) == old(self).state(1) && final(self).state(2) == old(self).state(2),
            final(self).spec_complete() == old(self).spec_complete(),
    {
        if !matches!(self.initial, KeyState::Ready) || matches!(self.handshake, KeyState::Absent) {
            return false;
        }
        self.initial = KeyState::Discarded;
        true
    }

    /// The handshake completed: for a server it is confirmed, and
    /// Handshake keys are discarded (§4.9.2). Returns whether they were
    /// just discarded; false (nothing changed) before the server's flight
    /// or if already complete.
    pub fn on_complete(&mut self) -> (now: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).later(&*old(self)),
            now == (old(self).state(1) == KeyState::Ready),
            now ==> final(self).state(1) == KeyState::Discarded && final(self).spec_complete(),
            !now ==> *final(self) == *old(self),
            final(self).state(0) == old(self).state(0) && final(self).state(2) == old(self).state(2),
    {
        if !matches!(self.handshake, KeyState::Ready) {
            return false;
        }
        self.handshake = KeyState::Discarded;
        self.complete = true;
        true
    }
}

} // verus!
