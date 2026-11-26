//! The dynamic table (RFC 9204 §3.2), verified against `spec`. Entries hold
//! their name and value behind `Rc`, so an entry that copies another's name
//! (Insert with Name Reference) or all of it (Duplicate) shares it instead
//! of copying it: inserting costs time proportional to the instruction, not
//! to the entry.
use crate::spec::*;
use std::collections::VecDeque;
use std::rc::Rc;
use vstd::prelude::*;

verus! {

pub struct Ent {
    pub name: Rc<Vec<u8>>,
    pub value: Rc<Vec<u8>>,
}

impl Ent {
    pub open spec fn view(&self) -> Entry {
        ((*self.name)@, (*self.value)@)
    }
}

/// The largest capacity a table may be given: 16 MiB, far above any
/// SETTINGS_QPACK_MAX_TABLE_CAPACITY in use, so sizes never overflow.
pub const CAP_LIMIT: u64 = 0x100_0000;

pub struct DynTable {
    /// Oldest first.
    pub ents: VecDeque<Ent>,
    pub dropped: u64,
    /// The sum of the entries' sizes.
    pub size: u64,
    pub cap: u64,
}

/// The static table (trusted data, `stable.rs`): entry `i`.
#[verifier::external_body]
#[inline(always)]
pub fn static_entry(i: usize) -> (r: (&'static [u8], &'static [u8]))
    requires
        i < 99,
    ensures
        r.0@ == static_name(i as int),
        r.1@ == static_value(i as int),
        r.0@.len() <= 64,
        r.1@.len() <= 64,
{
    crate::stable::STATIC[i]
}

pub proof fn lemma_tsize_first(s: Seq<Entry>)
    requires
        s.len() > 0,
    ensures
        tsize(s) == esize(s[0]) + tsize(s.drop_first()),
    decreases s.len(),
{
    if s.len() > 1 {
        lemma_tsize_first(s.drop_last());
        assert(s.drop_last().drop_first() =~= s.drop_first().drop_last());
        assert(s.drop_first().last() == s.last());
    } else {
        assert(s.drop_first() =~= Seq::<Entry>::empty());
        assert(s.drop_last() =~= Seq::<Entry>::empty());
    }
}

pub proof fn lemma_tsize_push(s: Seq<Entry>, e: Entry)
    ensures
        tsize(s.push(e)) == tsize(s) + esize(e),
{
    assert(s.push(e).drop_last() =~= s);
}

pub proof fn lemma_tsize_entry(s: Seq<Entry>, j: int)
    requires
        0 <= j < s.len(),
    ensures
        esize(s[j]) <= tsize(s),
    decreases s.len(),
{
    if j < s.len() - 1 {
        lemma_tsize_entry(s.drop_last(), j);
    }
}

pub proof fn lemma_tsize_bound(s: Seq<Entry>)
    ensures
        tsize(s) >= 32 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_tsize_bound(s.drop_last());
    }
}

/// What eviction leaves: a suffix of the entries, with `dropped` counting
/// the ones gone, the same capacity, and room (unless empty).
pub proof fn lemma_evict(t: Table, room: nat, cap: nat)
    ensures
        ({
            let t2 = evict(t, room, cap);
            &&& t2.cap == t.cap
            &&& t2.dropped >= t.dropped
            &&& icount(t2) == icount(t)
            &&& t2.ents == t.ents.subrange(t2.dropped - t.dropped, t.ents.len() as int)
            &&& tsize(t2.ents) <= tsize(t.ents)
            &&& t2.ents.len() == 0 || tsize(t2.ents) + room <= cap
        }),
    decreases t.ents.len(),
{
    if t.ents.len() > 0 && tsize(t.ents) + room > cap {
        let t1 = Table { ents: t.ents.drop_first(), dropped: t.dropped + 1, cap: t.cap };
        lemma_evict(t1, room, cap);
        lemma_tsize_first(t.ents);
        let t2 = evict(t1, room, cap);
        assert(t2.ents =~= t.ents.subrange(t2.dropped - t.dropped, t.ents.len() as int));
    } else {
        assert(t.ents =~= t.ents.subrange(0, t.ents.len() as int));
    }
}

impl DynTable {
    pub open spec fn view(&self) -> Table {
        Table {
            ents: Seq::new(self.ents@.len(), |i: int| self.ents@[i].view()),
            dropped: self.dropped as nat,
            cap: self.cap as nat,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.size as nat == tsize(self.view().ents)
        &&& self.size <= self.cap
        &&& self.cap <= CAP_LIMIT
        &&& icount(self.view()) <= MAX_INT
    }

    pub fn new() -> (r: DynTable)
        ensures
            r.inv(),
            r.view() == empty_table(),
    {
        let t = DynTable { ents: VecDeque::new(), dropped: 0, size: 0, cap: 0 };
        proof {
            assert(t.view().ents =~= Seq::<Entry>::empty());
        }
        t
    }

    /// Entries in the table.
    #[inline(always)]
    pub fn len(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == self.view().ents.len(),
            r <= CAP_LIMIT / 32,
    {
        proof {
            lemma_tsize_bound(self.view().ents);
        }
        self.ents.len() as u64
    }

    /// The Insert Count.
    #[inline(always)]
    pub fn icount(&self) -> (r: u64)
        requires
            self.inv(),
        ensures
            r == icount(self.view()),
    {
        let n = self.len();
        self.dropped + n
    }

    /// Evicts the oldest entries until `room` more bytes fit in `cap`. The
    /// second result counts the entries evicted.
    fn evict_for(&mut self, room: u64, cap: u64) -> (r: Ghost<nat>)
        requires
            old(self).size as nat == tsize(old(self).view().ents),
            old(self).size <= CAP_LIMIT,
            room <= 2 * CAP_LIMIT,
            icount(old(self).view()) <= MAX_INT,
        ensures
            final(self).size as nat == tsize(final(self).view().ents),
            final(self).view() == evict(old(self).view(), room as nat, cap as nat),
            final(self).size <= old(self).size,
            final(self).cap == old(self).cap,
            final(self).view().ents.len() + r@ == old(self).view().ents.len(),
            icount(final(self).view()) == icount(old(self).view()),
    {
        let ghost mut steps: nat = 0;
        while self.ents.len() > 0 && self.size + room > cap
            invariant
                self.size as nat == tsize(self.view().ents),
                self.size <= old(self).size,
                old(self).size <= CAP_LIMIT,
                room <= 2 * CAP_LIMIT,
                self.cap == old(self).cap,
                evict(self.view(), room as nat, cap as nat) == evict(old(self).view(), room as nat, cap as nat),
                self.view().ents.len() + steps == old(self).view().ents.len(),
                icount(self.view()) == icount(old(self).view()),
                icount(old(self).view()) <= MAX_INT,
            decreases self.ents@.len(),
        {
            let ghost v0 = self.view();
            proof {
                lemma_tsize_first(v0.ents);
            }
            let e = self.ents.pop_front().unwrap();
            let es = e.name.len() as u64 + e.value.len() as u64 + 32;
            self.size = self.size - es;
            self.dropped = self.dropped + 1;
            proof {
                assert(self.view().ents =~= v0.ents.drop_first());
                steps = steps + 1;
            }
        }
        Ghost(steps)
    }

    /// How many entries would have been evicted after making room for
    /// `room` more bytes: `evict`'s `dropped`, without evicting.
    pub fn dropped_after(&self, room: u64) -> (d: u64)
        requires
            self.inv(),
            room <= 2 * CAP_LIMIT,
        ensures
            d as nat == evict(self.view(), room as nat, self.cap as nat).dropped,
    {
        let ghost v = self.view();
        let ghost n = v.ents.len() as int;
        let mut k: usize = 0;
        let mut size = self.size;
        proof {
            assert(v.ents.subrange(0, n) =~= v.ents);
        }
        while k < self.ents.len() && size + room > self.cap
            invariant
                self.inv(),
                v == self.view(),
                n == v.ents.len(),
                room <= 2 * CAP_LIMIT,
                k <= n,
                size as nat == tsize(v.ents.subrange(k as int, n)),
                size <= self.size,
                evict(v, room as nat, v.cap) == evict(Table { ents: v.ents.subrange(k as int, n), dropped: (v.dropped + k) as nat, cap: v.cap }, room as nat, v.cap),
            decreases n - k,
        {
            let ghost sub = v.ents.subrange(k as int, n);
            proof {
                lemma_tsize_first(sub);
                assert(sub.drop_first() =~= v.ents.subrange(k + 1, n));
                assert(sub[0] == v.ents[k as int]);
            }
            let e = &self.ents[k];
            proof {
                assert(e.view() == v.ents[k as int]);
            }
            let es = e.name.len() as u64 + e.value.len() as u64 + 32;
            size = size - es;
            k = k + 1;
        }
        proof {
            lemma_tsize_bound(v.ents);
        }
        self.dropped + k as u64
    }

    /// Inserts `e`, evicting first (`spec::insert`); false, with the table
    /// unchanged, if `insert` is `None`. The second result counts the
    /// entries evicted.
    pub fn insert(&mut self, e: Ent) -> (r: (bool, Ghost<nat>))
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            match insert(old(self).view(), e.view()) {
                Some(t) => r.0 && final(self).view() == t,
                None => !r.0 && final(self).view() == old(self).view(),
            },
            final(self).view().ents.len() + r.1@ <= old(self).view().ents.len() + 1,
            final(self).cap == old(self).cap,
    {
        let nl = e.name.len() as u64;
        let vl = e.value.len() as u64;
        if nl > self.cap || vl > self.cap - nl || 32 > self.cap - nl - vl || self.icount() >= MAX_INT {
            return (false, Ghost(0));
        }
        let es = nl + vl + 32;
        let cap = self.cap;
        let g = self.evict_for(es, cap);
        proof {
            lemma_evict(old(self).view(), es as nat, cap as nat);
            lemma_tsize_push(self.view().ents, e.view());
        }
        let ghost v1 = self.view();
        self.ents.push_back(e);
        self.size = self.size + es;
        proof {
            assert(self.view().ents =~= v1.ents.push(e.view()));
        }
        (true, g)
    }

    /// Set Dynamic Table Capacity (`spec::set_cap`). The second result
    /// counts the entries evicted.
    pub fn set_cap(&mut self, c: u64) -> (r: Ghost<nat>)
        requires
            old(self).inv(),
            c <= CAP_LIMIT,
        ensures
            final(self).inv(),
            final(self).view() == set_cap(old(self).view(), c as nat),
            final(self).view().ents.len() + r@ == old(self).view().ents.len(),
    {
        let g = self.evict_for(0, c);
        proof {
            lemma_evict(old(self).view(), 0, c as nat);
        }
        self.cap = c;
        g
    }

    /// The entry with relative index `r` (from the newest).
    #[inline(always)]
    pub fn rel(&self, r: u64) -> (e: &Ent)
        requires
            self.inv(),
            rel_ok(self.view(), r as nat),
        ensures
            e.view() == rel(self.view(), r as nat),
    {
        &self.ents[self.ents.len() - 1 - r as usize]
    }

    /// The entry with absolute index `a`.
    #[inline(always)]
    pub fn abs(&self, a: u64) -> (e: &Ent)
        requires
            self.inv(),
            abs_ok(self.view(), a as nat),
        ensures
            e.view() == abs(self.view(), a as nat),
    {
        &self.ents[(a - self.dropped) as usize]
    }
}

} // verus!
