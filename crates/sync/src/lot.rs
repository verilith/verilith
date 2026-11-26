//! The global parking lot the locks sleep in, verified against the locks'
//! progress models.
//!
//! Threads sleep keyed by an address, as in parking_lot_core, so a lock
//! needs no space for its own wait queue: 64 buckets, each a list of
//! waiters behind a `std` mutex, shared by every lock whose key hashes to
//! it. A lock's key is the address of its lock word.
//!
//! Each lock keeps, in its own invariant, the set of its waiters' tickets
//! (`list`, a ghost variable that is exactly its progress model's list),
//! and each waiter's flag. The other half of `list` belongs to the
//! parking lot: [`lock_bucket`] hands it to the thread that locks the
//! lock's bucket, together with the fact that ties it to the bucket's
//! contents ([`listed`]: the waiters listed under the key are the lock's,
//! and their tickets are exactly `list`), and [`unlock_bucket`] takes it
//! back and checks that the fact still holds and that no other key's
//! waiters were touched. So within a critical section the lock's code
//! can read its list off the bucket, and every change it makes to the
//! bucket has to be matched by the same change to `list`.
//!
//! What is trusted is that this hand-over is sound (TRUST.md, "The
//! parking lot"): that the half the bucket hands out is the one for the
//! lock asking, and that the fact it comes with is true. Both rest on one
//! property of addresses: while a lock has waiters listed, each of them
//! holds a borrow of the lock, so the lock word cannot move or be freed,
//! and no other live lock word has its address.
// Some parameters and imports are used only in specifications and proofs.
#![allow(unused_variables, unused_imports, unused_mut)]
use crate::util::*;
use std::sync::Arc;
use vstd::atomic::*;
use vstd::prelude::*;
use vstd::resource::ghost_var::*;
use vstd::resource::map::*;
use vstd::resource::Loc;

verus! {

/// What the parking lot knows of a lock: where its ghost list and its
/// waiters' records are.
pub ghost struct LotId {
    /// The lock's `list` ghost variable.
    pub list: Loc,
    /// The lock's map from ticket to `(flag, id)` of the waiter with that
    /// ticket.
    pub recs: Loc,
}

/// A waiter's record in its lock's ghost state: its flag's atomic and its
/// id in the bucket.
pub type Rec = (AtomicCellId, u64);

/// A thread parked, or about to park, in a bucket.
pub struct Waiter {
    /// The key it parked under.
    pub key: usize,
    /// Its id, unique in its bucket.
    pub id: u64,
    pub thread: Unparker,
    /// Set (inside the bucket's critical section) by the thread that takes
    /// it off the list.
    pub notified: PAtomicBool,
    pub lot: Ghost<LotId>,
    /// Its ticket in its lock's progress model.
    pub tk: Ghost<nat>,
    pub rec: Tracked<GhostPersistentPointsTo<nat, Rec>>,
}

impl Waiter {
    pub open spec fn wf(&self) -> bool {
        &&& self.rec@.id() == self.lot@.recs
        &&& self.rec@.key() == self.tk@
        &&& self.rec@.value() == (self.notified.id(), self.id)
    }
}

/// A bucket's list.
pub struct BucketList {
    pub q: Vec<Arc<Waiter>>,
    /// The next id.
    pub next: u64,
}

impl BucketList {
    pub open spec fn wf(&self) -> bool {
        &&& forall|j: int| 0 <= j < self.q@.len() ==> (#[trigger] self.q@[j]).wf() && self.q@[j].id < self.next
        &&& forall|i: int, j: int| 0 <= i < self.q@.len() && 0 <= j < self.q@.len() && i != j ==> (#[trigger] self.q@[i]).id != (#[trigger] self.q@[j]).id
    }
}

/// The bucket's waiters under `key` are those of lock `lot`, and their
/// tickets are the domain of `list`, each once; `list` maps each ticket to
/// its waiter's id.
pub open spec fn listed(q: Seq<Arc<Waiter>>, key: usize, lot: LotId, list: Map<nat, u64>) -> bool {
    &&& forall|j: int| 0 <= j < q.len() && (#[trigger] q[j]).key == key ==> q[j].lot@ == lot
    &&& forall|j: int| 0 <= j < q.len() && (#[trigger] q[j]).key == key ==> list.contains_key(q[j].tk@) && list[q[j].tk@] == q[j].id
    &&& forall|tk: nat| #[trigger] list.contains_key(tk) ==> exists|j: int| 0 <= j < q.len() && (#[trigger] q[j]).key == key && q[j].tk@ == tk
    &&& forall|i: int, j: int| 0 <= i < q.len() && 0 <= j < q.len() && i != j && (#[trigger] q[i]).key == key && (#[trigger] q[j]).key == key ==> q[i].tk@ != q[j].tk@
}

/// `a` and `b` hold the same waiters under keys other than `key`.
pub open spec fn same_others(a: Seq<Arc<Waiter>>, b: Seq<Arc<Waiter>>, key: usize) -> bool {
    forall|w: Arc<Waiter>| w.key != key ==> (#[trigger] a.contains(w) <==> #[trigger] b.contains(w))
}

pub proof fn lemma_same_others_trans(a: Seq<Arc<Waiter>>, b: Seq<Arc<Waiter>>, c: Seq<Arc<Waiter>>, key: usize)
    requires
        same_others(a, b, key),
        same_others(b, c, key),
    ensures
        same_others(a, c, key),
{
    assert forall|w: Arc<Waiter>| w.key != key implies (#[trigger] a.contains(w) <==> #[trigger] c.contains(w)) by {
        assert(a.contains(w) <==> b.contains(w));
    }
}

/// Proof that a lock is keyed by `key()`: the address of its lock word,
/// taken while the caller borrows the lock. Only a lock's own `key`
/// function makes one, and it is used only within that borrow.
#[verifier::external_body]
pub struct KeyOf {
    _p: (),
}

impl KeyOf {
    pub uninterp spec fn key(&self) -> usize;

    pub uninterp spec fn lot(&self) -> LotId;
}

/// Proof that a bucket is locked, and what it held when it was.
#[verifier::external_body]
pub struct BucketGuard {
    g: Option<std::sync::MutexGuard<'static, Option<BucketList>>>,
}

impl BucketGuard {
    /// The key the bucket was locked for.
    pub uninterp spec fn key(&self) -> usize;

    /// What the bucket held when it was locked.
    pub uninterp spec fn got(&self) -> Seq<Arc<Waiter>>;
}

/// TRUSTED. Locks the bucket of `key` and hands over the lot's half of the
/// lock's list, with what ties it to the bucket (see the module comment).
#[verifier::external_body]
pub fn lock_bucket(key: usize, Tracked(k): Tracked<&KeyOf>) -> (r: (BucketGuard, BucketList, Tracked<GhostVar<Map<nat, u64>>>))
    requires
        k.key() == key,
    ensures
        r.0.key() == key,
        r.0.got() == r.1.q@,
        r.1.wf(),
        r.2@.id() == k.lot().list,
        listed(r.1.q@, key, k.lot(), r.2@@),
{
    let mut g = bucket(key).list.lock().unwrap_or_else(|e| e.into_inner());
    let l = g.take().unwrap();
    (BucketGuard { g: Some(g) }, l, Tracked::assume_new())
}

/// TRUSTED. Unlocks the bucket and gives the half back. Checks that the
/// list still matches it and that other keys' waiters are as they were.
#[verifier::external_body]
pub fn unlock_bucket(g: BucketGuard, l: BucketList, Tracked(half): Tracked<GhostVar<Map<nat, u64>>>, Tracked(k): Tracked<&KeyOf>)
    requires
        g.key() == k.key(),
        l.wf(),
        half.id() == k.lot().list,
        listed(l.q@, k.key(), k.lot(), half@),
        same_others(l.q@, g.got(), k.key()),
{
    let mut g = g;
    let mut inner = g.g.take().unwrap();
    *inner = Some(l);
}

/// The first waiter under `key`, or `q.len()` if there is none.
pub fn find_key(l: &BucketList, key: usize) -> (i: usize)
    ensures
        i <= l.q@.len(),
        i < l.q@.len() ==> l.q@[i as int].key == key,
        i == l.q@.len() ==> forall|j: int| 0 <= j < l.q@.len() ==> (#[trigger] l.q@[j]).key != key,
{
    let n = l.q.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == l.q@.len(),
            i <= n,
            forall|j: int| 0 <= j < i ==> (#[trigger] l.q@[j]).key != key,
        decreases n - i,
    {
        if l.q[i].key == key {
            return i;
        }
        i += 1;
    }
    i
}

/// The waiter with id `id`, or `q.len()` if there is none.
pub fn find_id(l: &BucketList, id: u64) -> (i: usize)
    ensures
        i <= l.q@.len(),
        i < l.q@.len() ==> l.q@[i as int].id == id,
        i == l.q@.len() ==> forall|j: int| 0 <= j < l.q@.len() ==> (#[trigger] l.q@[j]).id != id,
{
    let n = l.q.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == l.q@.len(),
            i <= n,
            forall|j: int| 0 <= j < i ==> (#[trigger] l.q@[j]).id != id,
        decreases n - i,
    {
        if l.q[i].id == id {
            return i;
        }
        i += 1;
    }
    i
}

/// Adding a waiter of the lock under its key adds its ticket.
pub proof fn lemma_push(q: Seq<Arc<Waiter>>, key: usize, lot: LotId, list: Map<nat, u64>, w: Arc<Waiter>)
    requires
        listed(q, key, lot, list),
        w.key == key,
        w.lot@ == lot,
        !list.contains_key(w.tk@),
    ensures
        listed(q.push(w), key, lot, list.insert(w.tk@, w.id)),
        same_others(q.push(w), q, key),
{
    let q1 = q.push(w);
    let l1 = list.insert(w.tk@, w.id);
    assert forall|tk: nat| #[trigger] l1.contains_key(tk) implies exists|j: int| 0 <= j < q1.len() && (#[trigger] q1[j]).key == key && q1[j].tk@ == tk by {
        if tk == w.tk@ {
            assert(q1[q.len() as int] == w);
        } else {
            let j = choose|j: int| 0 <= j < q.len() && (#[trigger] q[j]).key == key && q[j].tk@ == tk;
            assert(q1[j] == q[j]);
        }
    }
    assert forall|j: int| 0 <= j < q1.len() && (#[trigger] q1[j]).key == key implies q1[j].lot@ == lot && l1.contains_key(q1[j].tk@) && l1[q1[j].tk@] == q1[j].id by {
        if j < q.len() {
            assert(q1[j] == q[j]);
            assert(q[j].tk@ != w.tk@);
        }
    }
    assert forall|i: int, j: int| 0 <= i < q1.len() && 0 <= j < q1.len() && i != j && (#[trigger] q1[i]).key == key && (#[trigger] q1[j]).key == key implies q1[i].tk@ != q1[j].tk@ by {
        if i < q.len() {
            assert(q1[i] == q[i]);
        }
        if j < q.len() {
            assert(q1[j] == q[j]);
        }
    }
    assert forall|x: Arc<Waiter>| x.key != key implies (#[trigger] q1.contains(x) <==> #[trigger] q.contains(x)) by {
        if q1.contains(x) {
            let j = choose|j: int| 0 <= j < q1.len() && q1[j] == x;
            assert(j < q.len());
            assert(q[j] == x);
        }
        if q.contains(x) {
            let j = choose|j: int| 0 <= j < q.len() && q[j] == x;
            assert(q1[j] == x);
        }
    }
}

/// Taking a waiter of the lock off takes off its ticket.
pub proof fn lemma_remove(q: Seq<Arc<Waiter>>, key: usize, lot: LotId, list: Map<nat, u64>, i: int)
    requires
        listed(q, key, lot, list),
        0 <= i < q.len(),
        q[i].key == key,
    ensures
        listed(q.remove(i), key, lot, list.remove(q[i].tk@)),
        same_others(q.remove(i), q, key),
        list.contains_key(q[i].tk@),
        list[q[i].tk@] == q[i].id,
        q[i].lot@ == lot,
{
    let q1 = q.remove(i);
    let t = q[i].tk@;
    let l1 = list.remove(t);
    assert forall|j: int| 0 <= j < q1.len() && (#[trigger] q1[j]).key == key implies q1[j].lot@ == lot && l1.contains_key(q1[j].tk@) && l1[q1[j].tk@] == q1[j].id by {
        let j0 = if j < i { j } else { j + 1 };
        assert(q1[j] == q[j0]);
        assert(q[j0].tk@ != t);
    }
    assert forall|x: nat| #[trigger] l1.contains_key(x) implies exists|j: int| 0 <= j < q1.len() && (#[trigger] q1[j]).key == key && q1[j].tk@ == x by {
        let j = choose|j: int| 0 <= j < q.len() && (#[trigger] q[j]).key == key && q[j].tk@ == x;
        assert(j != i);
        let j1 = if j < i { j } else { j - 1 };
        assert(q1[j1] == q[j]);
    }
    assert forall|a: int, b: int| 0 <= a < q1.len() && 0 <= b < q1.len() && a != b && (#[trigger] q1[a]).key == key && (#[trigger] q1[b]).key == key implies q1[a].tk@ != q1[b].tk@ by {
        let a0 = if a < i { a } else { a + 1 };
        let b0 = if b < i { b } else { b + 1 };
        assert(q1[a] == q[a0]);
        assert(q1[b] == q[b0]);
    }
    assert forall|x: Arc<Waiter>| x.key != key implies (#[trigger] q1.contains(x) <==> #[trigger] q.contains(x)) by {
        if q1.contains(x) {
            let j = choose|j: int| 0 <= j < q1.len() && q1[j] == x;
            let j0 = if j < i { j } else { j + 1 };
            assert(q[j0] == x);
        }
        if q.contains(x) {
            let j = choose|j: int| 0 <= j < q.len() && q[j] == x;
            assert(j != i);
            let j1 = if j < i { j } else { j - 1 };
            assert(q1[j1] == x);
        }
    }
}

/// Removing from a well-formed list keeps it so.
pub proof fn lemma_remove_wf(l: BucketList, q1: Seq<Arc<Waiter>>, i: int)
    requires
        l.wf(),
        0 <= i < l.q@.len(),
        q1 == l.q@.remove(i),
    ensures
        forall|j: int| 0 <= j < q1.len() ==> (#[trigger] q1[j]).wf() && q1[j].id < l.next,
        forall|a: int, b: int| 0 <= a < q1.len() && 0 <= b < q1.len() && a != b ==> (#[trigger] q1[a]).id != (#[trigger] q1[b]).id,
{
    assert forall|j: int| 0 <= j < q1.len() implies (#[trigger] q1[j]).wf() && q1[j].id < l.next by {
        let j0 = if j < i { j } else { j + 1 };
        assert(q1[j] == l.q@[j0]);
    }
    assert forall|a: int, b: int| 0 <= a < q1.len() && 0 <= b < q1.len() && a != b implies (#[trigger] q1[a]).id != (#[trigger] q1[b]).id by {
        let a0 = if a < i { a } else { a + 1 };
        let b0 = if b < i { b } else { b + 1 };
        assert(q1[a] == l.q@[a0]);
        assert(q1[b] == l.q@[b0]);
    }
}

/// The new waiter with the next id keeps the list well formed.
pub proof fn lemma_push_wf(l: BucketList, w: Arc<Waiter>)
    requires
        l.wf(),
        w.wf(),
        w.id == l.next,
        l.next < u64::MAX,
    ensures
        forall|j: int| 0 <= j < l.q@.push(w).len() ==> (#[trigger] l.q@.push(w)[j]).wf() && l.q@.push(w)[j].id < l.next + 1,
        forall|a: int, b: int| 0 <= a < l.q@.push(w).len() && 0 <= b < l.q@.push(w).len() && a != b ==> (#[trigger] l.q@.push(w)[a]).id != (#[trigger] l.q@.push(w)[b]).id,
{
    let q1 = l.q@.push(w);
    assert forall|j: int| 0 <= j < q1.len() implies (#[trigger] q1[j]).wf() && q1[j].id < l.next + 1 by {
        if j < l.q@.len() {
            assert(q1[j] == l.q@[j]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < q1.len() && 0 <= b < q1.len() && a != b implies (#[trigger] q1[a]).id != (#[trigger] q1[b]).id by {
        if a < l.q@.len() {
            assert(q1[a] == l.q@[a]);
        }
        if b < l.q@.len() {
            assert(q1[b] == l.q@[b]);
        }
    }
}

} // verus!

struct Bucket {
    list: std::sync::Mutex<Option<BucketList>>,
}

// Each bucket on its own cache line(s), as before.
#[repr(align(128))]
struct Padded(Bucket);

const BUCKETS: usize = 64;

static TABLE: [Padded; BUCKETS] = [const { Padded(Bucket { list: std::sync::Mutex::new(Some(BucketList { q: Vec::new(), next: 0 })) }) }; BUCKETS];

#[inline]
fn bucket(key: usize) -> &'static Bucket {
    // Fibonacci hashing of the address: 2^64 or 2^32 over the golden ratio.
    #[cfg(target_pointer_width = "64")]
    const PHI: usize = 0x9E37_79B9_7F4A_7C15;
    #[cfg(target_pointer_width = "32")]
    const PHI: usize = 0x9E37_79B9;
    &TABLE[(key.wrapping_mul(PHI) >> (usize::BITS - 6)) as usize].0
}

impl Drop for BucketGuard {
    fn drop(&mut self) {
        if self.g.is_some() {
            // Dropped without `unlock_bucket`: the bucket would be left
            // without its list.
            std::process::abort();
        }
    }
}
