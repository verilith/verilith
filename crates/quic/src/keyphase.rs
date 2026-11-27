//! Which 1-RTT keys open a packet, through key updates (RFC 9001 §6).
//!
//! The keys of generation `g` (0 for the first 1-RTT keys, then one more
//! per update) are used with Key Phase bit `g % 2`. [`KeyPhase`] tracks the
//! current generation and the first packet number received in it; the
//! keys themselves stay with the caller (the current, previous and next
//! generation's).
//!
//! Proven:
//!
//! - [`KeyPhase::select`] only picks a generation whose phase matches the
//!   packet's Key Phase bit: the current one, the previous one or the next;
//! - the previous generation is picked only for packets numbered below the
//!   first one of the current generation, and the next only for packets
//!   numbered at or above it (§6.3: a packet newer than the update is never
//!   opened with old keys, nor an older one taken as a new update);
//! - [`KeyPhase::on_update`] moves to the next generation only for a packet
//!   [`KeyPhase::select`] sent there, and [`KeyPhase::phase`] (the bit to
//!   send with) always follows the generation.
use vstd::prelude::*;

verus! {

/// The keys to open a packet with.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Gen {
    /// The previous generation's (packets sent before the update).
    Prev,
    /// The current generation's.
    Current,
    /// The next generation's: if they open the packet, the peer updated.
    Next,
}

pub struct KeyPhase {
    generation: u64,
    /// The first packet number opened with the current generation's keys,
    /// once there has been an update.
    from: Option<u64>,
}

impl KeyPhase {
    /// The current generation.
    pub closed spec fn generation(&self) -> int {
        self.generation as int
    }

    /// The first packet number of the current generation (after an update).
    pub closed spec fn first_pn(&self) -> Option<u64> {
        self.from
    }

    pub closed spec fn inv(&self) -> bool {
        self.generation == 0 <==> self.from is None
    }

    /// The generation `select`'s answer stands for.
    pub open spec fn gen_of(&self, g: Gen) -> int {
        match g {
            Gen::Prev => self.generation() - 1,
            Gen::Current => self.generation(),
            Gen::Next => self.generation() + 1,
        }
    }

    pub fn new() -> (r: KeyPhase)
        ensures
            r.inv(),
            r.generation() == 0,
            r.first_pn() is None,
    {
        KeyPhase { generation: 0, from: None }
    }

    /// The Key Phase bit of the current generation, to send with.
    pub fn phase(&self) -> (r: bool)
        ensures
            r == (self.generation() % 2 == 1),
    {
        self.generation % 2 == 1
    }

    pub closed spec fn select_spec(&self, bit: bool, pn: u64) -> Gen {
        if bit == (self.generation % 2 == 1) {
            Gen::Current
        } else if self.from matches Some(f) && pn < f {
            Gen::Prev
        } else {
            Gen::Next
        }
    }

    /// The keys to try on packet `pn` with Key Phase bit `bit` (§6.3).
    pub fn select(&self, bit: bool, pn: u64) -> (r: Gen)
        requires
            self.inv(),
        ensures
            r == self.select_spec(bit, pn),
            self.gen_of(r) >= 0,
            (self.gen_of(r) % 2 == 1) == bit,
            r == Gen::Prev ==> (self.first_pn() matches Some(f) && pn < f),
            r == Gen::Next ==> (self.first_pn() matches Some(f) ==> pn >= f),
            bit == (self.generation() % 2 == 1) ==> r == Gen::Current,
    {
        if bit == (self.generation % 2 == 1) {
            return Gen::Current;
        }
        match self.from {
            Some(f) if pn < f => Gen::Prev,
            _ => Gen::Next,
        }
    }

    /// Packet `pn` was opened with the next generation's keys: the peer
    /// updated, and so does the sender (§6.2). Refused (false, nothing
    /// changed) for anything `select` did not send to the next generation,
    /// or past 2^64 - 1 updates.
    pub fn on_update(&mut self, bit: bool, pn: u64) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            ok == (old(self).select_spec(bit, pn) == Gen::Next && old(self).generation() < u64::MAX),
            ok ==> final(self).generation() == old(self).generation() + 1 && final(self).first_pn() == Some(pn),
            !ok ==> final(self).generation() == old(self).generation() && final(self).first_pn() == old(
                self,
            ).first_pn(),
    {
        let g = self.select(bit, pn);
        if !matches!(g, Gen::Next) || self.generation == u64::MAX {
            return false;
        }
        self.generation = self.generation + 1;
        self.from = Some(pn);
        true
    }
}

} // verus!
