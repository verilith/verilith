//! Anti-replay for 0-RTT data (RFC 8446 §8), verified: the single-use
//! register of §8.1 joined with the freshness check of §8.3.
//!
//! A ClientHello's early data is taken ([`Register::claim`]) only if
//!
//! - the client's view of its ticket's age (`obfuscated_ticket_age` less
//!   `ticket_age_add`, ms) is within [`WINDOW_MS`] of the server's (now
//!   less when the ticket was issued): `fresh`; and
//! - no ClientHello with the same key (from its PSK binder, which is
//!   unique to the ClientHello) was taken in the [`SPAN_MS`] before.
//!
//! Proven of every call that returns `true` ([`Register::claim`]'s
//! postcondition), over the history of every claim that returned `true`
//! before it (`Register::taken`):
//!
//! - a key is never taken twice less than [`SPAN_MS`] apart; and
//! - the same ClientHello (the same key, and so the same ticket and age)
//!   is never taken twice at all: the times at which it is fresh lie in
//!   `2 * WINDOW_MS`, less than [`SPAN_MS`] (`lemma_fresh_close`).
//!
//! The register is two hash sets of keys, the current generation and the
//! one before it, each covering [`SPAN_MS`] of server time; a full one
//! refuses (the handshake goes on, 1-RTT), so its memory is bounded by
//! [`MAX`] keys per generation. A server clock that goes back before the
//! current generation began also refuses. A key is 128 bits of the
//! binder: two binders that share one only cost the second its 0-RTT.
use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::obeys_key_model;
#[cfg(verus_keep_ghost)]
use vstd::laws_eq::obeys_view_eq;

verus! {

broadcast use {vstd::std_specs::hash::group_hash_axioms, vstd::laws_eq::group_laws_eq};

/// How far apart (ms) the client's and the server's view of a ticket's age
/// may be for its 0-RTT data to be taken (§8.3).
pub const WINDOW_MS: u64 = 10_000;

/// How long (ms of server time) a generation of the register lasts, and so
/// the least time a taken key is remembered: more than the `2 * WINDOW_MS`
/// in which one ClientHello can be fresh.
pub const SPAN_MS: u64 = 2 * WINDOW_MS + 1000;

/// The most keys a generation holds. When it is full, 0-RTT is refused.
pub const MAX: usize = 1 << 18;

/// The client's view of the ticket's age, ms (§4.2.11.1).
pub open spec fn client_age(obfuscated_age: u32, age_add: u32) -> int {
    (obfuscated_age as int - age_add as int) % 0x1_0000_0000
}

/// The server time (ms since the epoch) at which the server's view of the
/// ticket's age equals the client's: when a ClientHello sent at once
/// would arrive.
pub open spec fn center(obfuscated_age: u32, issued: u64, age_add: u32) -> int {
    issued as int * 1000 + client_age(obfuscated_age, age_add)
}

/// The freshness check of §8.3 at server time `now` (ms since the epoch)
/// for a ticket issued at `issued` (s since the epoch): the server's view
/// of the ticket's age, `now - issued`, is within `WINDOW_MS` of the
/// client's.
pub open spec fn fresh(now: int, obfuscated_age: u32, issued: u64, age_add: u32) -> bool {
    &&& now >= issued as int * 1000
    &&& now - center(obfuscated_age, issued, age_add) <= WINDOW_MS
    &&& center(obfuscated_age, issued, age_add) - now <= WINDOW_MS
}

/// The times at which one ClientHello is fresh are less than `SPAN_MS`
/// apart.
pub proof fn lemma_fresh_close(t1: int, t2: int, obfuscated_age: u32, issued: u64, age_add: u32)
    requires
        fresh(t1, obfuscated_age, issued, age_add),
        fresh(t2, obfuscated_age, issued, age_add),
    ensures
        t2 - t1 < SPAN_MS,
        t1 - t2 < SPAN_MS,
{
}

/// One claim that returned `true`: the key, the ClientHello's `center`,
/// and the server time it was taken at.
pub type Taken = (u128, int, int);

pub struct Register {
    current: HashSetWithView<u128>,
    previous: HashSetWithView<u128>,
    /// When `current` was started (ms since the epoch).
    since: u64,
    taken: Ghost<Set<Taken>>,
}

impl Register {
    /// Every claim that returned `true`, ever.
    pub closed spec fn taken(&self) -> Set<Taken> {
        self.taken@
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.current.well_formed()
        &&& self.previous.well_formed()
        &&& forall|e: Taken| #[trigger] self.taken@.contains(e) ==> self.remembers(e)
    }

    /// What the register keeps of a past claim: it was fresh, it is before
    /// the end of the current generation, and its key is in the register
    /// while it is less than `SPAN_MS` old at the start of it.
    closed spec fn remembers(&self, e: Taken) -> bool {
        let (k, c, t) = e;
        &&& t - c <= WINDOW_MS
        &&& c - t <= WINDOW_MS
        &&& t < self.since + SPAN_MS
        &&& t >= self.since ==> self.current@.contains(k)
        &&& t < self.since < t + SPAN_MS ==> (self.current@.contains(k) || self.previous@.contains(k))
    }

    /// An empty register whose first generation starts at `now` (ms since
    /// the epoch).
    pub fn new(now: u64) -> (r: Register)
        ensures
            r.wf(),
            r.taken() == Set::<Taken>::empty(),
    {
        assert(obeys_key_model::<u128>());
        assert(obeys_view_eq::<u128>());
        Register {
            current: HashSetWithView::new(),
            previous: HashSetWithView::new(),
            since: now,
            taken: Ghost(Set::empty()),
        }
    }

    /// Whether to take the early data of a ClientHello with `key` (from its
    /// first PSK binder) and `obfuscated_age`, resuming a ticket issued at
    /// `issued` (s since the epoch) with `age_add`, at server time `now`
    /// (ms since the epoch).
    pub fn claim(&mut self, key: u128, now: u64, obfuscated_age: u32, issued: u64, age_add: u32) -> (r: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            r ==> fresh(now as int, obfuscated_age, issued, age_add),
            // A key is never taken twice less than SPAN_MS apart ...
            r ==> forall|c: int, t: int| #[trigger] old(self).taken().contains((key, c, t)) ==> t + SPAN_MS <= now,
            // ... so the same ClientHello is never taken twice.
            r ==> forall|t: int|
                !(#[trigger] old(self).taken().contains((key, center(obfuscated_age, issued, age_add), t))),
            final(self).taken() == if r {
                old(self).taken().insert((key, center(obfuscated_age, issued, age_add), now as int))
            } else {
                old(self).taken()
            },
    {
        let ghost c = center(obfuscated_age, issued, age_add);
        let cage = obfuscated_age.wrapping_sub(age_add) as u64;
        assert(cage == client_age(obfuscated_age, age_add)) by {
            assert(obfuscated_age >= age_add ==> obfuscated_age as int - age_add as int
                == (obfuscated_age as int - age_add as int) % 0x1_0000_0000);
            assert(obfuscated_age < age_add ==> obfuscated_age as int - age_add as int + 0x1_0000_0000
                == (obfuscated_age as int - age_add as int) % 0x1_0000_0000);
        }
        let issued_ms = match issued.checked_mul(1000) {
            Some(v) => v,
            None => return false,
        };
        if now < issued_ms {
            return false;
        }
        let server_age = now - issued_ms;
        if (cage > server_age && cage - server_age > WINDOW_MS) || (server_age > cage
            && server_age - cage > WINDOW_MS) {
            return false;
        }
        assert(fresh(now as int, obfuscated_age, issued, age_add));
        if now < self.since {
            return false;
        }
        let ghost before = *self;
        if now - self.since >= SPAN_MS {
            // A new generation; the one before it is kept only if it began
            // less than 2 * SPAN_MS ago.
            if now - self.since >= 2 * SPAN_MS {
                self.previous.clear();
            } else {
                std::mem::swap(&mut self.current, &mut self.previous);
            }
            self.current.clear();
            self.since = now;
            assert forall|e: Taken| #[trigger] self.taken@.contains(e) implies self.remembers(e) by {
                assert(before.remembers(e));
            }
        }
        if self.previous.contains(&key) || self.current.contains(&key) || self.current.len() >= MAX {
            return false;
        }
        proof {
            assert forall|cc: int, t: int| #[trigger] self.taken@.contains((key, cc, t)) implies t + SPAN_MS <= now by {
                assert(self.remembers((key, cc, t)));
            }
            assert forall|t: int| !(#[trigger] self.taken@.contains((key, c, t))) by {
                if self.taken@.contains((key, c, t)) {
                    assert(self.remembers((key, c, t)));
                }
            }
        }
        let ghost mid = *self;
        self.current.insert(key);
        proof {
            self.taken@ = self.taken@.insert((key, c, now as int));
            assert forall|e: Taken| #[trigger] self.taken@.contains(e) implies self.remembers(e) by {
                if e != (key, c, now as int) {
                    assert(mid.remembers(e));
                }
            }
        }
        true
    }
}

} // verus!
