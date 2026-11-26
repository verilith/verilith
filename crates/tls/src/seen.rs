//! A set of 16-bit values for duplicate checks (extension types, key share
//! groups), with linear worst-case work and no allocation in the common
//! case.
//!
//! Values below 64 (every extension type this crate interprets, and most
//! that clients send) are bits of one word. Up to 16 others are kept in an
//! array and compared one by one. Past 16 of those, which no real client
//! sends, the set moves to a bitmap of all 2^16 values: an 8 KiB
//! allocation, once, after which each insert is one bit. So `n` inserts
//! cost at most `17n + 1024` steps whatever the values are, where a list
//! compared pairwise would cost `n^2`.
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// Bit `j` of `w`.
pub open spec fn bit(w: u64, j: int) -> bool {
    ((w >> (j as u64)) & 1) == 1
}

proof fn lemma_bit_or(w: u64, k: u64, j: u64)
    requires
        k < 64,
        j < 64,
    ensures
        ((w | (1u64 << k)) >> j) & 1 == (if j == k { 1u64 } else { (w >> j) & 1 }),
{
    assert(((w | (1u64 << k)) >> j) & 1 == (if j == k { 1u64 } else { (w >> j) & 1 })) by (bit_vector)
        requires
            k < 64,
            j < 64,
    ;
}

proof fn lemma_bit_zero(j: u64)
    requires
        j < 64,
    ensures
        (0u64 >> j) & 1 == 0,
{
    assert((0u64 >> j) & 1 == 0) by (bit_vector);
}

/// Steps an insert costs, at most, without the one-time move to the bitmap.
pub spec const INSERT_STEPS: nat = 17;

/// Steps the move to the bitmap costs, once.
pub spec const SPILL_STEPS: nat = 1041;

pub struct Seen {
    low: u64,
    small: [u16; 16],
    n: usize,
    big: Vec<u64>,
    set: Ghost<Set<u16>>,
}

impl Seen {
    pub closed spec fn view(&self) -> Set<u16> {
        self.set@
    }

    /// Whether the set has moved to the bitmap (its one-time cost paid).
    pub closed spec fn spilled(&self) -> bool {
        self.big@.len() > 0
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.n <= 16
        &&& self.big@.len() == 0 || self.big@.len() == 1024
        &&& forall|i: int| 0 <= i < self.n ==> #[trigger] self.small@[i] >= 64
        &&& forall|t: u16| t < 64 ==> (#[trigger] self.set@.contains(t) <==> bit(self.low, t as int))
        &&& self.big@.len() == 0 ==> forall|t: u16|
            t >= 64 ==> (#[trigger] self.set@.contains(t) <==> exists|i: int|
                0 <= i < self.n && self.small@[i] == t)
        &&& self.big@.len() == 1024 ==> forall|t: u16|
            t >= 64 ==> (#[trigger] self.set@.contains(t) <==> bit(
                self.big@[t as int / 64],
                t as int % 64,
            ))
    }

    pub fn new() -> (r: Seen)
        ensures
            r.wf(),
            r@ == Set::<u16>::empty(),
            !r.spilled(),
    {
        let r = Seen { low: 0, small: [0u16; 16], n: 0, big: Vec::new(), set: Ghost(Set::empty()) };
        proof {
            assert forall|t: u16| t < 64 implies (#[trigger] r.set@.contains(t) <==> bit(
                r.low,
                t as int,
            )) by {
                lemma_bit_zero(t as u64);
            }
        }
        r
    }

    /// Adds `t`; returns whether it was already there, and the steps taken.
    pub fn insert(&mut self, t: u16) -> (r: (bool, Ghost<nat>))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            r.0 == old(self)@.contains(t),
            final(self)@ == old(self)@.insert(t),
            old(self).spilled() ==> final(self).spilled(),
            r.1@ <= INSERT_STEPS + (if final(self).spilled() && !old(self).spilled() {
                SPILL_STEPS
            } else {
                0
            }),
    {
        let ghost old_set = self.set@;
        if t < 64 {
            let was = (self.low >> (t as u64)) & 1 == 1;
            self.low = self.low | (1u64 << (t as u64));
            self.set = Ghost(old_set.insert(t));
            proof {
                assert forall|u: u16| u < 64 implies (#[trigger] self.set@.contains(u) <==> bit(
                    self.low,
                    u as int,
                )) by {
                    lemma_bit_or(old(self).low, t as u64, u as u64);
                }
                assert forall|u: u16| u >= 64 && self.big@.len() == 0 implies (
                #[trigger] self.set@.contains(u) <==> exists|i: int|
                    0 <= i < self.n && self.small@[i] == u) by {
                    assert(old(self).set@.contains(u) == self.set@.contains(u));
                }
                assert forall|u: u16| u >= 64 && self.big@.len() == 1024 implies (
                #[trigger] self.set@.contains(u) <==> bit(self.big@[u as int / 64], u as int % 64)) by {
                    assert(old(self).set@.contains(u) == self.set@.contains(u));
                }
            }
            return (was, Ghost(1));
        }
        if self.big.len() == 0 {
            let mut i: usize = 0;
            while i < self.n
                invariant
                    self.wf(),
                    *self == *old(self),
                    t >= 64,
                    self.big@.len() == 0,
                    0 <= i <= self.n,
                    forall|j: int| 0 <= j < i ==> self.small@[j] != t,
                decreases self.n - i,
            {
                if self.small[i] == t {
                    return (true, Ghost(i as nat + 1));
                }
                i = i + 1;
            }
            assert(!old_set.contains(t));
            if self.n < 16 {
                let n = self.n;
                self.small[n] = t;
                self.n = n + 1;
                self.set = Ghost(old_set.insert(t));
                proof {
                    assert forall|u: u16| u < 64 implies (#[trigger] self.set@.contains(u) <==> bit(
                        self.low,
                        u as int,
                    )) by {
                        assert(old(self).set@.contains(u) == self.set@.contains(u));
                    }
                    assert forall|u: u16| u >= 64 implies (#[trigger] self.set@.contains(u)
                        <==> exists|j: int| 0 <= j < self.n && self.small@[j] == u) by {
                        if u == t {
                            assert(self.small@[n as int] == u);
                        } else if old(self).set@.contains(u) {
                            let j = choose|j: int| 0 <= j < old(self).n && old(self).small@[j] == u;
                            assert(self.small@[j] == u);
                        } else {
                            assert forall|j: int| 0 <= j < self.n implies self.small@[j] != u by {
                                if j < n {
                                    assert(self.small@[j] == old(self).small@[j]);
                                }
                            }
                        }
                    }
                }
                return (false, Ghost(17));
            }
            // Spill: every value of 64 or more seen so far goes to the bitmap.
            let mut big: Vec<u64> = Vec::with_capacity(1024);
            let mut k: usize = 0;
            while k < 1024
                invariant
                    0 <= k <= 1024,
                    big@.len() == k,
                    forall|j: int| 0 <= j < k ==> big@[j] == 0u64,
                decreases 1024 - k,
            {
                big.push(0u64);
                k = k + 1;
            }
            proof {
                assert forall|u: u16| u >= 64 implies (bit(#[trigger] big@[u as int / 64], u as int % 64) <==> exists|
                    j: int,
                | 0 <= j < 0 && self.small@[j] == u) by {
                    lemma_bit_zero((u % 64) as u64);
                }
            }
            let mut i: usize = 0;
            while i < 16
                invariant
                    self.wf(),
                    *self == *old(self),
                    self.n == 16,
                    self.big@.len() == 0,
                    0 <= i <= 16,
                    big@.len() == 1024,
                    forall|u: u16|
                        u >= 64 ==> (bit(#[trigger] big@[u as int / 64], u as int % 64) <==> exists|
                            j: int,
                        | 0 <= j < i && self.small@[j] == u),
                    forall|u: u16| u < 64 ==> big@[#[trigger] (u as int / 64)] == 0u64,
                decreases 16 - i,
            {
                let v = self.small[i];
                let w = (v / 64) as usize;
                let ghost old_big = big@;
                let x = big[w] | (1u64 << ((v % 64) as u64));
                big.set(w, x);
                proof {
                    assert forall|u: u16| u >= 64 implies (bit(
                        #[trigger] big@[u as int / 64],
                        u as int % 64,
                    ) <==> exists|j: int| 0 <= j < i + 1 && self.small@[j] == u) by {
                        lemma_bit_or(old_big[w as int], (v % 64) as u64, (u % 64) as u64);
                        if u as int / 64 == w as int {
                            if u == v {
                                assert(self.small@[i as int] == u);
                            } else {
                                assert((u % 64) != (v % 64));
                                if exists|j: int| 0 <= j < i + 1 && self.small@[j] == u {
                                    let j = choose|j: int| 0 <= j < i + 1 && self.small@[j] == u;
                                    assert(j < i);
                                }
                            }
                        } else {
                            assert(big@[u as int / 64] == old_big[u as int / 64]);
                            if exists|j: int| 0 <= j < i + 1 && self.small@[j] == u {
                                let j = choose|j: int| 0 <= j < i + 1 && self.small@[j] == u;
                                assert(j < i);
                            }
                        }
                    }
                    assert forall|u: u16| u < 64 implies big@[#[trigger] (u as int / 64)] == 0u64 by {
                        assert(u as int / 64 == 0);
                        assert(w > 0);
                    }
                }
                i = i + 1;
            }
            let w = (t / 64) as usize;
            let ghost old_big = big@;
            let x = big[w] | (1u64 << ((t % 64) as u64));
            big.set(w, x);
            self.big = big;
            self.set = Ghost(old_set.insert(t));
            proof {
                assert forall|u: u16| u < 64 implies (#[trigger] self.set@.contains(u) <==> bit(
                    self.low,
                    u as int,
                )) by {
                    assert(old(self).set@.contains(u) == self.set@.contains(u));
                }
                assert forall|u: u16| u >= 64 implies (#[trigger] self.set@.contains(u) <==> bit(
                    self.big@[u as int / 64],
                    u as int % 64,
                )) by {
                    lemma_bit_or(old_big[w as int], (t % 64) as u64, (u % 64) as u64);
                    if u as int / 64 == w as int && u != t {
                        assert((u % 64) != (t % 64));
                    }
                }
            }
            return (false, Ghost(SPILL_STEPS + 1));
        }
        let w = (t / 64) as usize;
        let was = (self.big[w] >> ((t % 64) as u64)) & 1 == 1;
        let ghost old_big = self.big@;
        let x = self.big[w] | (1u64 << ((t % 64) as u64));
        self.big.set(w, x);
        self.set = Ghost(old_set.insert(t));
        proof {
            assert forall|u: u16| u < 64 implies (#[trigger] self.set@.contains(u) <==> bit(
                self.low,
                u as int,
            )) by {
                assert(old(self).set@.contains(u) == self.set@.contains(u));
            }
            assert forall|u: u16| u >= 64 implies (#[trigger] self.set@.contains(u) <==> bit(
                self.big@[u as int / 64],
                u as int % 64,
            )) by {
                lemma_bit_or(old_big[w as int], (t % 64) as u64, (u % 64) as u64);
                assert(old(self).set@.contains(u) <==> bit(old_big[u as int / 64], u as int % 64));
                if u as int / 64 == w as int && u != t {
                    assert((u % 64) != (t % 64));
                }
            }
        }
        (was, Ghost(1))
    }
}

} // verus!
