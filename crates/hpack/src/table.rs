//! The dynamic table (RFC 7541 §2.3.2, §4), verified against `spec`.
use crate::spec::*;
use std::collections::VecDeque;
use vstd::prelude::*;

verus! {

pub struct Ent {
    pub name: Vec<u8>,
    pub value: Vec<u8>,
}

/// Entries newest first, with their total size (§4.1) and the maximum.
pub struct Table {
    pub ents: VecDeque<Ent>,
    pub size: u64,
    pub max: u32,
    /// Entries inserted so far: entry `j` (0-based, newest first) was the
    /// `ins - 1 - j`th, which names it uniquely for a cache (`capi.rs`).
    pub ins: u64,
    /// Buffers of evicted entries, reused by `insert_move` so a full table
    /// allocates nothing. Not part of the table's contents.
    pub spare: Vec<Ent>,
}

/// At most this many evicted entries' buffers are kept.
pub const SPARE_MAX: usize = 32;

/// The static table (trusted data, `stable.rs`): entry `i`, 0-based.
#[verifier::external_body]
#[inline(always)]
pub fn static_entry(i: usize) -> (r: (&'static [u8], &'static [u8]))
    requires
        i < 61,
    ensures
        r.0@ == static_name(i as int),
        r.1@ == static_value(i as int),
        r.0@.len() <= 64,
        r.1@.len() <= 64,
{
    crate::stable::STATIC[i]
}

pub proof fn lemma_tsize_bound(t: Seq<Entry>)
    ensures
        tsize(t) >= 32 * t.len(),
    decreases t.len(),
{
    if t.len() > 0 {
        lemma_tsize_bound(t.drop_last());
    }
}

proof fn lemma_evict_len(t: Seq<Entry>, room: nat, max: nat)
    ensures
        evict(t, room, max).len() <= t.len(),
        tsize(evict(t, room, max)) <= tsize(t),
        evict(t, room, max).len() == 0 || tsize(evict(t, room, max)) + room <= max,
    decreases t.len(),
{
    if t.len() > 0 && tsize(t) + room > max {
        lemma_evict_len(t.drop_last(), room, max);
    }
}

impl Table {
    pub open spec fn view(&self) -> Seq<Entry> {
        Seq::new(self.ents@.len(), |i: int| (self.ents@[i].name@, self.ents@[i].value@))
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.size as nat == tsize(self.view())
        &&& self.size <= self.max
    }

    pub fn new(max: u32) -> (r: Table)
        ensures
            r.inv(),
            r.view() == Seq::<Entry>::empty(),
            r.max == max,
    {
        let t = Table { ents: VecDeque::new(), size: 0, max, ins: 0, spare: Vec::new() };
        proof {
            assert(t.view() =~= Seq::<Entry>::empty());
        }
        t
    }

    pub fn len(&self) -> (r: usize)
        ensures
            r == self.view().len(),
            self.inv() ==> r <= 0x0800_0000,
    {
        proof {
            lemma_tsize_bound(self.view());
        }
        self.ents.len()
    }

    /// Evicts the oldest entries until `room` more bytes fit in `max`.
    fn evict_for(&mut self, room: u64, max: u32)
        requires
            old(self).size as nat == tsize(old(self).view()),
            old(self).size <= 0xFFFF_FFFF,
            room <= 0x3_0000_0000,
        ensures
            final(self).size as nat == tsize(final(self).view()),
            final(self).view() == evict(old(self).view(), room as nat, max as nat),
            final(self).max == old(self).max,
            final(self).size <= old(self).size,
    {
        while self.ents.len() > 0 && self.size + room > max as u64
            invariant
                self.size as nat == tsize(self.view()),
                self.size <= 0xFFFF_FFFF,
                room <= 0x3_0000_0000,
                self.max == old(self).max,
                self.size <= old(self).size,
                evict(old(self).view(), room as nat, max as nat) == evict(self.view(), room as nat, max as nat),
            decreases self.ents@.len(),
        {
            let ghost v = self.view();
            let e = self.ents.pop_back();
            proof {
                assert(self.view() =~= v.drop_last());
            }
            match e {
                Some(e) => {
                    let sz = e.name.len() as u64 + e.value.len() as u64 + 32;
                    proof {
                        assert(v.last() == (e.name@, e.value@));
                        assert(tsize(v) == tsize(v.drop_last()) + esize(v.last()));
                    }
                    self.size = self.size - sz;
                    if self.spare.len() < SPARE_MAX {
                        self.spare.push(e);
                    }
                },
                None => {},
            }
        }
    }

    /// Sets the maximum size, evicting to fit (§4.3).
    pub fn resize(&mut self, max: u32)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).max == max,
            final(self).view() == evict(old(self).view(), 0, max as nat),
    {
        self.evict_for(0, max);
        proof {
            lemma_evict_len(old(self).view(), 0, max as nat);
        }
        self.max = max;
    }

    /// Adds an entry (§4.4).
    pub fn insert(&mut self, name: Vec<u8>, value: Vec<u8>)
        requires
            old(self).inv(),
            name@.len() <= 0xFFFF_FFFF,
            value@.len() <= 0xFFFF_FFFF,
        ensures
            final(self).inv(),
            final(self).max == old(self).max,
            final(self).view() == insert(old(self).view(), old(self).max as nat, (name@, value@)),
    {
        let room = name.len() as u64 + value.len() as u64 + 32;
        let max = self.max;
        self.evict_for(room, max);
        proof {
            lemma_evict_len(old(self).view(), room as nat, max as nat);
        }
        if room <= max as u64 {
            let ghost v = self.view();
            self.ents.push_front(Ent { name, value });
            proof {
                let e = (name@, value@);
                assert(self.view() =~= seq![e] + v);
                lemma_tsize_front(e, v);
            }
            self.size = self.size + room;
            if self.ins < u64::MAX {
                self.ins = self.ins + 1;
            }
        }
    }

    /// Adds the entry `(name, value)` (§4.4), moving the buffers into the
    /// table instead of copying them. True if it was added (it is then
    /// entry 0, and `name` and `value` hold other buffers, contents
    /// unspecified); false if it did not fit (the table is then empty, and
    /// `name` and `value` are unchanged).
    pub fn insert_move(&mut self, name: &mut Vec<u8>, value: &mut Vec<u8>) -> (r: bool)
        requires
            old(self).inv(),
            old(name)@.len() <= 0xFFFF_FFFF,
            old(value)@.len() <= 0xFFFF_FFFF,
        ensures
            final(self).inv(),
            final(self).max == old(self).max,
            final(self).view() == insert(old(self).view(), old(self).max as nat, (old(name)@, old(value)@)),
            r ==> final(self).view().len() > 0 && final(self).view()[0] == (old(name)@, old(value)@),
            !r ==> final(name)@ == old(name)@ && final(value)@ == old(value)@,
    {
        let room = name.len() as u64 + value.len() as u64 + 32;
        let max = self.max;
        self.evict_for(room, max);
        proof {
            lemma_evict_len(old(self).view(), room as nat, max as nat);
        }
        if room <= max as u64 {
            let ghost v = self.view();
            let ghost e = (name@, value@);
            // Fresh buffers start with room for typical fields, so the
            // decoder does not regrow them right after the swap.
            let (mut n, mut w) = match self.spare.pop() {
                Some(x) => (x.name, x.value),
                None => (Vec::with_capacity(64), Vec::with_capacity(128)),
            };
            core::mem::swap(name, &mut n);
            core::mem::swap(value, &mut w);
            self.ents.push_front(Ent { name: n, value: w });
            proof {
                assert(self.view() =~= seq![e] + v);
                lemma_tsize_front(e, v);
            }
            self.size = self.size + room;
            if self.ins < u64::MAX {
                self.ins = self.ins + 1;
            }
            true
        } else {
            false
        }
    }

    /// Entry `i` of the index space (1..=61 static, then dynamic).
    pub fn get(&self, i: usize) -> (r: (&[u8], &[u8]))
        requires
            1 <= i <= self.view().len() + 61,
        ensures
            r.0@ == entry(self.view(), i as nat).0,
            r.1@ == entry(self.view(), i as nat).1,
            self.inv() ==> r.0@.len() <= 0xFFFF_FFFF && r.1@.len() <= 0xFFFF_FFFF,
    {
        proof {
            if self.inv() && i > 61 {
                lemma_esize_le(self.view(), i - 62);
                assert(self.view()[i - 62] == (self.ents@[i - 62].name@, self.ents@[i - 62].value@));
            }
        }
        if i <= 61 {
            let r = static_entry(i - 1);
            assert(r.0@.len() <= 64);
            r
        } else {
            let e = &self.ents[i - 62];
            proof {
                assert(*e == self.ents@[i - 62]);
                if self.inv() {
                    assert(esize(self.view()[i - 62]) <= tsize(self.view()));
                    assert(e.name@.len() <= 0xFFFF_FFFF);
                    assert(e.value@.len() <= 0xFFFF_FFFF);
                }
            }
            let r = (e.name.as_slice(), e.value.as_slice());
            assert(r.0@ == e.name@);
            r
        }
    }
}

/// An entry costs no more than the table.
pub proof fn lemma_esize_le(t: Seq<Entry>, i: int)
    requires
        0 <= i < t.len(),
    ensures
        esize(t[i]) <= tsize(t),
    decreases t.len(),
{
    if i < t.len() - 1 {
        lemma_esize_le(t.drop_last(), i);
    }
}

/// `tsize` of an entry added in front.
pub proof fn lemma_tsize_front(e: Entry, t: Seq<Entry>)
    ensures
        tsize(seq![e] + t) == esize(e) + tsize(t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(seq![e] + t =~= seq![e]);
        assert(seq![e].drop_last() =~= Seq::<Entry>::empty());
        assert(tsize(seq![e]) == tsize(seq![e].drop_last()) + esize(seq![e].last()));
    } else {
        lemma_tsize_front(e, t.drop_last());
        assert((seq![e] + t).drop_last() =~= seq![e] + t.drop_last());
        assert((seq![e] + t).last() == t.last());
    }
}

} // verus!
