//! What each sent packet carried, so that its acknowledgment or loss acts
//! on exactly those frames (RFC 9000 §13.3, RFC 9002 §6).
//!
//! A sender appends one record per frame to a [`RecLog`] as it builds a
//! packet, and stores a token ([`pack`]) of the packet's first record and
//! count with the packet. Proven, of the log [`RecLog::log`] of every
//! record pushed and the set [`RecLog::taken`] of those already acted on:
//!
//! - [`unpack`] of a token gives back exactly the packet's records;
//! - [`RecLog::take`] returns a record only once, however often its packet
//!   is reported acknowledged or lost, and only the record pushed at that
//!   index;
//! - [`RecLog::trim`] frees the records already taken at the front.
use vstd::prelude::*;

verus! {

/// Record indices stay below 2^56, so a token's index fits above its count.
pub const MAX_INDEX: u64 = 0x0100_0000_0000_0000;

/// The most records per packet.
pub const MAX_COUNT: u64 = 255;

pub open spec fn spec_unpack(t: u64) -> (u64, u64) {
    (t >> 8u64, t & 0xffu64)
}

/// A token for the `count` records from index `start` (an index from
/// [`RecLog::next_index`], and at most [`MAX_COUNT`] records).
pub fn pack(start: u64, count: u64) -> (t: u64)
    ensures
        start < MAX_INDEX && count <= MAX_COUNT ==> spec_unpack(t) == (start, count),
{
    let t = (start << 8u64) | count;
    if start >= MAX_INDEX || count > MAX_COUNT {
        return t;
    }
    assert(((start << 8u64) | count) >> 8u64 == start && ((start << 8u64) | count) & 0xffu64 == count)
        by (bit_vector)
        requires
            start < 0x0100_0000_0000_0000u64,
            count <= 255u64,
    ;
    t
}

/// The first record and the count of a token.
pub fn unpack(t: u64) -> (r: (u64, u64))
    ensures
        r == spec_unpack(t),
        r.1 <= MAX_COUNT,
{
    assert(t & 0xffu64 <= 255u64) by (bit_vector);
    (t >> 8u64, t & 0xffu64)
}

pub struct RecLog<T> {
    /// Records from index `base` on, at `data[head..]`; `None` once taken.
    data: Vec<Option<T>>,
    head: usize,
    base: u64,
    log: Ghost<Seq<T>>,
    taken: Ghost<ISet<int>>,
}

impl<T: Copy> RecLog<T> {
    /// Every record pushed, by index.
    pub closed spec fn log(&self) -> Seq<T> {
        self.log@
    }

    /// The indices already taken.
    pub closed spec fn taken(&self) -> ISet<int> {
        self.taken@
    }

    /// Records held (the memory used).
    pub closed spec fn held(&self) -> int {
        self.data@.len() as int
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.head <= self.data@.len()
        &&& self.log@.len() == self.base + (self.data@.len() - self.head)
        &&& self.log@.len() <= MAX_INDEX
        &&& forall|k: int| 0 <= k < self.base ==> #[trigger] self.taken@.contains(k)
        &&& forall|k: int| #[trigger] self.taken@.contains(k) ==> 0 <= k < self.log@.len()
        &&& forall|k: int|
            self.base <= k < self.log@.len() ==> #[trigger] self.data@[self.head + k - self.base] == if self.taken@.contains(
                k,
            ) {
                None
            } else {
                Some(self.log@[k])
            }
    }

    pub fn new() -> (r: RecLog<T>)
        ensures
            r.inv(),
            r.log() == Seq::<T>::empty(),
            r.taken() == ISet::<int>::empty(),
    {
        RecLog { data: Vec::new(), head: 0, base: 0, log: Ghost(Seq::empty()), taken: Ghost(ISet::empty()) }
    }

    /// The index the next record pushed gets.
    pub fn next_index(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == self.log().len(),
    {
        self.base + (self.data.len() - self.head) as u64
    }

    /// Appends `r`; false (and nothing pushed) once [`MAX_INDEX`] records
    /// have been.
    pub fn push(&mut self, r: T) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            ok == (old(self).log().len() < MAX_INDEX),
            final(self).log() == if ok { old(self).log().push(r) } else { old(self).log() },
            final(self).taken() == old(self).taken(),
    {
        if self.next_index() >= MAX_INDEX {
            return false;
        }
        let ghost d0 = self.data@;
        self.data.push(Some(r));
        proof {
            self.log@ = self.log@.push(r);
            assert forall|k: int| self.base <= k < self.log@.len() implies #[trigger] self.data@[self.head + k
                - self.base] == if self.taken@.contains(k) { None } else { Some(self.log@[k]) } by {
                if k < self.log@.len() - 1 {
                    assert(self.data@[self.head + k - self.base] == d0[self.head + k - self.base]);
                }
            }
        }
        true
    }

    /// The record at `k`, if pushed and not yet taken.
    pub fn get(&self, k: u64) -> (r: Option<T>)
        requires
            self.inv(),
        ensures
            r == if k < self.log().len() && !self.taken().contains(k as int) {
                Some(self.log()[k as int])
            } else {
                None
            },
    {
        if k < self.base || k >= self.next_index() {
            return None;
        }
        let n = self.data.len();
        let d = k - self.base;
        assert(d < n - self.head);
        let i = self.head + d as usize;
        let r = self.data[i];
        proof {
            assert(self.data@[self.head + k - self.base] == r);
        }
        r
    }

    /// Takes the record at `k`: returns it if pushed and not taken before,
    /// and marks it taken.
    pub fn take(&mut self, k: u64) -> (r: Option<T>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r == if k < old(self).log().len() && !old(self).taken().contains(k as int) {
                Some(old(self).log()[k as int])
            } else {
                None
            },
            final(self).log() == old(self).log(),
            final(self).taken() == if k < old(self).log().len() {
                old(self).taken().insert(k as int)
            } else {
                old(self).taken()
            },
    {
        let r = self.get(k);
        if k < self.base || k >= self.next_index() {
            proof {
                if k < self.log@.len() {
                    assert(self.taken@.insert(k as int) =~= self.taken@);
                }
            }
            return r;
        }
        let n = self.data.len();
        let d = k - self.base;
        assert(d < n - self.head);
        let i = self.head + d as usize;
        let ghost d0 = self.data@;
        self.data.set(i, None);
        proof {
            self.taken@ = self.taken@.insert(k as int);
            assert forall|j: int| self.base <= j < self.log@.len() implies #[trigger] self.data@[self.head + j
                - self.base] == if self.taken@.contains(j) { None } else { Some(self.log@[j]) } by {
                if j != k {
                    assert(self.data@[self.head + j - self.base] == d0[self.head + j - self.base]);
                }
            }
        }
        r
    }

    /// Frees the taken records at the front. Afterwards the first record
    /// held, if any, is not taken.
    pub fn trim(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).log() == old(self).log(),
            final(self).taken() == old(self).taken(),
            final(self).held() <= old(self).held(),
    {
        while self.head < self.data.len() && self.data[self.head].is_none()
            invariant
                self.inv(),
                self.log() == old(self).log(),
                self.taken() == old(self).taken(),
                self.held() == old(self).held(),
            decreases self.data@.len() - self.head,
        {
            proof {
                let k = self.base as int;
                assert(self.data@[self.head + k - self.base] == if self.taken@.contains(k) {
                    None
                } else {
                    Some(self.log@[k])
                });
            }
            self.head = self.head + 1;
            self.base = self.base + 1;
            proof {
                assert forall|k: int| self.base <= k < self.log@.len() implies #[trigger] self.data@[self.head + k
                    - self.base] == if self.taken@.contains(k) { None } else { Some(self.log@[k]) } by {
                    assert(self.data@[(self.head - 1) + k - (self.base - 1)] == if self.taken@.contains(k) {
                        None
                    } else {
                        Some(self.log@[k])
                    });
                }
            }
        }
        // Move what is left to the front once the freed part is at least
        // as long (so each record is moved at most once on average).
        if self.head >= 64 && self.head >= self.data.len() - self.head {
            let ghost d0 = self.data@;
            let h = self.head;
            let rest = self.data.split_off(h);
            self.data = rest;
            self.head = 0;
            proof {
                assert forall|k: int| self.base <= k < self.log@.len() implies #[trigger] self.data@[self.head + k
                    - self.base] == if self.taken@.contains(k) { None } else { Some(self.log@[k]) } by {
                    assert(self.data@[k - self.base] == d0[h + k - self.base]);
                }
            }
        }
    }

    /// Takes every record (keys discarded): later tokens for them find
    /// nothing.
    pub fn clear(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).log() == old(self).log(),
            final(self).taken() == ISet::new(|k: int| 0 <= k < old(self).log().len()),
            final(self).held() == 0,
    {
        self.base = self.next_index();
        self.data = Vec::new();
        self.head = 0;
        proof {
            self.taken@ = ISet::new(|k: int| 0 <= k < self.log@.len());
        }
    }
}

} // verus!
