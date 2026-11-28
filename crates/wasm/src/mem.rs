//! Linear memory that keeps a record of the 4 KiB chunks written since it
//! was last made clean, so that putting it back to that clean state copies
//! only those chunks (`Mem::reset`).
//!
//! The record is a type invariant: every chunk not marked dirty holds
//! exactly the bytes of `Mem::base`, the memory as it was when last made
//! clean (`Mem::new`, `Mem::rebase`, `Mem::reset`). Every write
//! marks the chunks it touches before it changes a byte, so the invariant
//! holds after every operation, whoever calls it. A host function gets
//! the memory as `&mut Mem`: it can read it and write it only through the
//! methods here (checked ones: [`Mem::write`]), so it cannot change the
//! base or leave a written chunk unmarked, and it cannot make a `Mem` of
//! its own to put in its place (the constructors are private to the
//! crate).
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::sem::*;
use crate::prims;

verus! {

/// Bytes per chunk of the written record.
pub const CHUNK: usize = 4096;

/// The chunk byte `i` is in.
pub open spec fn ck(i: int) -> int {
    i / CHUNK as int
}

pub proof fn lemma_ck(i: int)
    requires 0 <= i,
    ensures 0 <= ck(i), CHUNK * ck(i) <= i < CHUNK * ck(i) + CHUNK,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, CHUNK as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(i, CHUNK as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(i, CHUNK as int);
}

/// Bytes of `b` outside the chunks `dirty` marks are those of `base`.
pub open spec fn agrees(b: Seq<u8>, dirty: Seq<bool>, base: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() && i < base.len() && !dirty[ck(i)] ==> #[trigger] b[i] == base[i]
}

/// `d1` marks every chunk `d0` marks.
pub open spec fn more(d0: Seq<bool>, d1: Seq<bool>) -> bool {
    &&& d1.len() == d0.len()
    &&& forall|q: int| 0 <= q < d0.len() && #[trigger] d0[q] ==> d1[q]
}

/// `d` marks every chunk of bytes `lo..hi`.
pub open spec fn marks(d: Seq<bool>, lo: int, hi: int) -> bool {
    forall|k: int| lo <= k < hi ==> #[trigger] d[ck(k)]
}

/// Writing `b0` to `b1` changed bytes only in `lo..hi`, whose chunks `d1`
/// marks, and `d1` marks what `d0` did: the record still holds.
pub proof fn lemma_agrees(b0: Seq<u8>, b1: Seq<u8>, d0: Seq<bool>, d1: Seq<bool>, base: Seq<u8>, lo: int, hi: int)
    requires
        agrees(b0, d0, base),
        b0.len() <= d0.len() * CHUNK,
        b1.len() == b0.len(),
        more(d0, d1),
        marks(d1, lo, hi),
        forall|k: int| 0 <= k < b0.len() && !(lo <= k < hi) ==> #[trigger] b1[k] == b0[k],
    ensures agrees(b1, d1, base),
{
    assert forall|i: int| 0 <= i < b1.len() && i < base.len() && !d1[ck(i)] implies #[trigger] b1[i] == base[i] by {
        lemma_ck(i);
        if lo <= i < hi {
            assert(d1[ck(i)]);
        } else {
            assert(b1[i] == b0[i]);
            if d0[ck(i)] {
                assert(d1[ck(i)]);
            }
        }
    }
}

pub proof fn lemma_write_le_other(s: Seq<u8>, i: int, v: nat, n: nat, k: int)
    requires 0 <= i, i + n <= s.len(), 0 <= k < s.len(), !(i <= k < i + n),
    ensures write_le(s, i, v, n).len() == s.len(), write_le(s, i, v, n)[k] == s[k],
    decreases n,
{
    if n > 0 {
        lemma_write_le_other(s.update(i, (v % 256) as u8), i + 1, v / 256, (n - 1) as nat, k);
    }
}

/// Marks the chunks of bytes `d..d + n`.
#[inline(always)]
fn mark(dirty: &mut Vec<bool>, d: usize, n: usize)
    requires d + n <= old(dirty)@.len() * CHUNK, d + n <= usize::MAX,
    ensures more(old(dirty)@, final(dirty)@), marks(final(dirty)@, d as int, d + n),
{
    if n == 0 {
        return;
    }
    let lo = d / CHUNK;
    let hi = (d + n - 1) / CHUNK;
    proof {
        lemma_ck(d as int);
        lemma_ck(d + n - 1);
    }
    let mut c = lo;
    while c <= hi
        invariant
            lo <= c <= hi + 1,
            hi < dirty@.len(),
            hi == ck(d + n - 1),
            lo == ck(d as int),
            dirty@.len() == old(dirty)@.len(),
            forall|q: int| 0 <= q < dirty@.len() ==> #[trigger] dirty@[q] == (old(dirty)@[q] || (lo <= q < c)),
        decreases hi + 1 - c,
    {
        dirty[c] = true;
        c += 1;
    }
    proof {
        assert forall|k: int| d <= k < d + n implies #[trigger] dirty@[ck(k)] by {
            lemma_ck(k);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(d as int, k, CHUNK as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(k, d + n - 1, CHUNK as int);
        }
    }
}

/// Marks chunk `c`; the record still holds.
#[inline(always)]
fn flag(dirty: &mut Vec<bool>, c: usize, Ghost(b): Ghost<Seq<u8>>, Ghost(base): Ghost<Seq<u8>>)
    requires c < old(dirty)@.len(), agrees(b, old(dirty)@, base),
    ensures final(dirty)@ == old(dirty)@.update(c as int, true), agrees(b, final(dirty)@, base),
    no_unwind
{
    dirty[c] = true;
    proof {
        assert forall|i: int| 0 <= i < b.len() && i < base.len() && !dirty@[ck(i)] implies #[trigger] b[i] == base[i] by {
            assert(!old(dirty)@[ck(i)]);
        }
    }
}

/// `store` on the bytes, whose chunks `dirty` already marks.
#[inline(always)]
fn store_marked(bytes: &mut Vec<u8>, dirty: &Vec<bool>, Ghost(base): Ghost<Seq<u8>>, i: usize, v: u64, n: usize)
    requires
        i + n <= old(bytes)@.len(), n == 1 || n == 2 || n == 4 || n == 8,
        agrees(old(bytes)@, dirty@, base),
        marks(dirty@, i as int, i + n),
    ensures
        final(bytes)@ == write_le(old(bytes)@, i as int, store_value(v, n as nat), n as nat),
        final(bytes)@.len() == old(bytes)@.len(),
        agrees(final(bytes)@, dirty@, base),
    no_unwind
{
    let ghost b0 = bytes@;
    prims::store(bytes, i, v, n);
    proof {
        crate::run::lemma_write_le_len(b0, i as int, store_value(v, n as nat), n as nat);
        assert forall|j: int| 0 <= j < bytes@.len() && j < base.len() && !dirty@[ck(j)] implies #[trigger] bytes@[j] == base[j] by {
            if i <= j < i + n {
                assert(dirty@[ck(j)]);
            } else {
                lemma_write_le_other(b0, i as int, store_value(v, n as nat), n as nat, j);
                assert(b0[j] == base[j]);
            }
        }
    }
}

/// A linear memory and the chunks written since it was last clean.
pub struct Mem {
    bytes: Vec<u8>,
    dirty: Vec<bool>,
    base: Ghost<Seq<u8>>,
}

impl View for Mem {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Seq<u8> {
        self.bytes@
    }
}

impl Mem {
    #[verifier::type_invariant]
    spec fn inv(&self) -> bool {
        &&& self.dirty@.len() == self.bytes@.len() as int / CHUNK as int + 1
        &&& agrees(self.bytes@, self.dirty@, self.base@)
    }

    /// The memory as it was when last made clean.
    pub closed spec fn base(&self) -> Seq<u8> {
        self.base@
    }

    proof fn lemma_room(&self)
        requires self.inv(),
        ensures self.bytes@.len() < self.dirty@.len() * CHUNK,
    {
        lemma_ck(self.bytes@.len() as int);
    }

    /// A clean memory holding `v`.
    pub(crate) fn new(v: Vec<u8>) -> (r: Mem)
        ensures r@ == v@, r.base() == v@,
    {
        let nd = v.len() / CHUNK + 1;
        let dirty = vec![false; nd];
        Mem { bytes: v, dirty, base: Ghost(v@) }
    }

    /// No memory.
    pub(crate) fn empty() -> (r: Mem)
        ensures r@ == Seq::<u8>::empty(),
    {
        let r = Mem { bytes: Vec::new(), dirty: vec![false; 1], base: Ghost(Seq::empty()) };
        proof { assert(r.bytes@ =~= Seq::<u8>::empty()); }
        r
    }

    /// Takes the memory out, leaving an empty one.
    fn take(&mut self) -> (r: Mem)
        ensures r == *old(self), final(self)@ == Seq::<u8>::empty(),
    {
        let mut t = Mem::empty();
        core::mem::swap(self, &mut t);
        t
    }

    #[inline(always)]
    pub fn len(&self) -> (r: usize)
        ensures r == self@.len(),
    {
        self.bytes.len()
    }

    #[inline(always)]
    pub fn as_slice(&self) -> (r: &[u8])
        ensures r@ == self@,
    {
        self.bytes.as_slice()
    }

    #[inline(always)]
    pub(crate) fn vec(&self) -> (r: &Vec<u8>)
        ensures r@ == self@,
    {
        &self.bytes
    }

    /// Stores the low `n` (1, 2, 4 or 8) bytes of `v` at `i`, little-endian.
    #[inline(always)]
    pub(crate) fn store(&mut self, i: usize, v: u64, n: usize)
        requires i + n <= old(self)@.len(), n == 1 || n == 2 || n == 4 || n == 8,
        ensures
            final(self)@ == write_le(old(self)@, i as int, store_value(v, n as nat), n as nat),
            final(self).base() == old(self).base(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
            self.lemma_room();
            vstd::std_specs::vec::axiom_spec_len(&self.bytes);
            assert(self.bytes.len() == self.bytes@.len());
            lemma_ck(i as int);
            lemma_ck(i + n - 1);
        }
        // `n <= 8` bytes span at most two chunks: the first's and the last's.
        flag(&mut self.dirty, i / CHUNK, Ghost(self.bytes@), Ghost(self.base@));
        flag(&mut self.dirty, (i + n - 1) / CHUNK, Ghost(self.bytes@), Ghost(self.base@));
        proof {
            assert forall|k: int| i <= k < i + n implies #[trigger] self.dirty@[ck(k)] by {
                lemma_ck(k);
            }
        }
        store_marked(&mut self.bytes, &self.dirty, Ghost(self.base@), i, v, n);
    }

    /// `memory.fill`.
    pub(crate) fn fill(&mut self, d: usize, v: u8, n: usize)
        requires d + n <= old(self)@.len(),
        ensures
            final(self)@ == old(self)@.subrange(0, d as int) + Seq::new(n as nat, |_i| v)
                + old(self)@.subrange((d + n) as int, old(self)@.len() as int),
            final(self).base() == old(self).base(),
    {
        let t = self.take();
        proof { use_type_invariant(&t); t.lemma_room(); }
        let Mem { mut bytes, mut dirty, base } = t;
        let ghost b0 = bytes@;
        let ghost d0 = dirty@;
        proof { vstd::std_specs::vec::axiom_spec_len(&bytes); assert(bytes.len() == bytes@.len()); }
        mark(&mut dirty, d, n);
        prims::fill(&mut bytes, d, v, n);
        proof {
            assert forall|k: int| 0 <= k < b0.len() && !(d <= k < d + n) implies #[trigger] bytes@[k] == b0[k] by {
                if k < d { assert(bytes@[k] == b0.subrange(0, d as int)[k]); }
                else { assert(bytes@[k] == b0.subrange((d + n) as int, b0.len() as int)[k - d - n]); }
            }
            lemma_agrees(b0, bytes@, d0, dirty@, base@, d as int, d + n);
        }
        *self = Mem { bytes, dirty, base };
    }

    /// `memory.copy` (the ranges may overlap).
    pub(crate) fn copy_within(&mut self, d: usize, s: usize, n: usize)
        requires d + n <= old(self)@.len(), s + n <= old(self)@.len(),
        ensures
            final(self)@ == old(self)@.subrange(0, d as int) + old(self)@.subrange(s as int, (s + n) as int)
                + old(self)@.subrange((d + n) as int, old(self)@.len() as int),
            final(self).base() == old(self).base(),
    {
        let t = self.take();
        proof { use_type_invariant(&t); t.lemma_room(); }
        let Mem { mut bytes, mut dirty, base } = t;
        let ghost b0 = bytes@;
        let ghost d0 = dirty@;
        proof { vstd::std_specs::vec::axiom_spec_len(&bytes); assert(bytes.len() == bytes@.len()); }
        mark(&mut dirty, d, n);
        prims::copy_within(&mut bytes, d, s, n);
        proof {
            assert forall|k: int| 0 <= k < b0.len() && !(d <= k < d + n) implies #[trigger] bytes@[k] == b0[k] by {
                if k < d { assert(bytes@[k] == b0.subrange(0, d as int)[k]); }
                else { assert(bytes@[k] == b0.subrange((d + n) as int, b0.len() as int)[k - d - n]); }
            }
            lemma_agrees(b0, bytes@, d0, dirty@, base@, d as int, d + n);
        }
        *self = Mem { bytes, dirty, base };
    }

    /// Copies `data[s..s + n]` to `d`.
    pub(crate) fn copy_in(&mut self, d: usize, data: &[u8], s: usize, n: usize)
        requires d + n <= old(self)@.len(), s + n <= data@.len(),
        ensures
            final(self)@ == old(self)@.subrange(0, d as int) + data@.subrange(s as int, (s + n) as int)
                + old(self)@.subrange((d + n) as int, old(self)@.len() as int),
            final(self).base() == old(self).base(),
    {
        let t = self.take();
        proof { use_type_invariant(&t); t.lemma_room(); }
        let Mem { mut bytes, mut dirty, base } = t;
        let ghost b0 = bytes@;
        let ghost d0 = dirty@;
        proof { vstd::std_specs::vec::axiom_spec_len(&bytes); assert(bytes.len() == bytes@.len()); }
        mark(&mut dirty, d, n);
        prims::copy_in(&mut bytes, d, data, s, n);
        proof {
            assert forall|k: int| 0 <= k < b0.len() && !(d <= k < d + n) implies #[trigger] bytes@[k] == b0[k] by {
                if k < d { assert(bytes@[k] == b0.subrange(0, d as int)[k]); }
                else { assert(bytes@[k] == b0.subrange((d + n) as int, b0.len() as int)[k - d - n]); }
            }
            lemma_agrees(b0, bytes@, d0, dirty@, base@, d as int, d + n);
        }
        *self = Mem { bytes, dirty, base };
    }

    /// Copies `data[s..s + n]` to `d`, for a host function: `false`, and
    /// nothing written, if either range is out of bounds.
    pub fn write(&mut self, d: usize, data: &[u8], s: usize, n: usize) -> (ok: bool)
        ensures
            ok == (d + n <= old(self)@.len() && s + n <= data@.len()),
            ok ==> final(self)@ == old(self)@.subrange(0, d as int) + data@.subrange(s as int, (s + n) as int)
                + old(self)@.subrange((d + n) as int, old(self)@.len() as int),
            !ok ==> final(self)@ == old(self)@,
            final(self).base() == old(self).base(),
    {
        if d > self.bytes.len() || n > self.bytes.len() - d || s > data.len() || n > data.len() - s {
            return false;
        }
        self.copy_in(d, data, s, n);
        true
    }

    /// Appends `n` zero bytes (`memory.grow`), or leaves the memory
    /// unchanged and returns `false` if the allocation fails.
    pub(crate) fn try_grow(&mut self, n: usize) -> (r: bool)
        ensures
            r ==> final(self)@ == old(self)@ + Seq::new(n as nat, |_i| 0u8),
            !r ==> final(self)@ == old(self)@,
            final(self).base() == old(self).base(),
    {
        let t = self.take();
        proof { use_type_invariant(&t); t.lemma_room(); }
        let Mem { mut bytes, mut dirty, base } = t;
        let ghost b0 = bytes@;
        let len = bytes.len();
        if !prims::try_grow(&mut bytes, n) {
            *self = Mem { bytes, dirty, base };
            return false;
        }
        // One more flag per new chunk (marked, which `mark` below would
        // do anyway), then the chunks of the new bytes marked.
        let need = bytes.len() / CHUNK + 1;
        while dirty.len() < need
            invariant
                dirty@.len() <= need,
                dirty@.len() >= len as int / CHUNK as int + 1,
                forall|q: int| 0 <= q < len as int / CHUNK as int + 1 ==> #[trigger] dirty@[q] == t.dirty@[q],
                t.dirty@.len() == len as int / CHUNK as int + 1,
            decreases need - dirty@.len(),
        {
            dirty.push(true);
        }
        let ghost d0 = dirty@;
        proof {
            lemma_ck(bytes@.len() as int);
            assert(dirty@.len() == need);
            vstd::std_specs::vec::axiom_spec_len(&bytes);
            assert(bytes.len() == bytes@.len());
        }
        mark(&mut dirty, len, n);
        proof {
            assert forall|k: int| 0 <= k < b0.len() && !(len <= k < len + n) implies #[trigger] bytes@[k] == b0[k] by {}
            // `b0` agreed with the shorter record; the record only grew.
            assert(agrees(b0, d0, base@)) by {
                assert forall|i: int| 0 <= i < b0.len() && i < base@.len() && !d0[ck(i)] implies #[trigger] b0[i] == base@[i] by {
                    lemma_ck(i);
                    vstd::arithmetic::div_mod::lemma_div_is_ordered(i, len as int, CHUNK as int);
                    assert(d0[ck(i)] == t.dirty@[ck(i)]);
                }
            }
            assert forall|i: int| 0 <= i < bytes@.len() && i < base@.len() && !dirty@[ck(i)] implies #[trigger] bytes@[i] == base@[i] by {
                lemma_ck(i);
                if len <= i < len + n {
                    assert(dirty@[ck(i)]);
                } else {
                    assert(bytes@[i] == b0[i]);
                    if d0[ck(i)] { assert(dirty@[ck(i)]); }
                }
            }
        }
        *self = Mem { bytes, dirty, base };
        true
    }

    /// Marks every chunk written: for a caller that writes the bytes
    /// without saying where ([`Mem::all_mut`]).
    pub(crate) fn mark_all(&mut self)
        ensures final(self)@ == old(self)@, final(self).base() == old(self).base(),
    {
        let t = self.take();
        proof { use_type_invariant(&t); }
        let Mem { bytes, mut dirty, base } = t;
        let mut c = 0;
        while c < dirty.len()
            invariant
                0 <= c <= dirty@.len(),
                dirty@.len() == t.dirty@.len(),
                forall|q: int| 0 <= q < dirty@.len() ==> #[trigger] dirty@[q] == (t.dirty@[q] || q < c),
            decreases dirty@.len() - c,
        {
            dirty[c] = true;
            c += 1;
        }
        proof {
            assert(more(t.dirty@, dirty@));
            assert forall|i: int| 0 <= i < bytes@.len() && i < base@.len() && !dirty@[ck(i)] implies #[trigger] bytes@[i] == base@[i] by {
                lemma_ck(i);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(i, bytes@.len() as int, CHUNK as int);
            }
        }
        *self = Mem { bytes, dirty, base };
    }

    /// Makes the memory clean as it is now: its base becomes its bytes.
    pub(crate) fn rebase(&mut self)
        ensures final(self)@ == old(self)@, final(self).base() == old(self)@,
    {
        let t = self.take();
        proof { use_type_invariant(&t); }
        let Mem { bytes, mut dirty, base } = t;
        let mut c = 0;
        while c < dirty.len()
            invariant
                0 <= c <= dirty@.len(),
                dirty@.len() == t.dirty@.len(),
            decreases dirty@.len() - c,
        {
            dirty[c] = false;
            c += 1;
        }
        *self = Mem { bytes, dirty, base: Ghost(bytes@) };
    }

    /// Puts the memory back to `src`, its base: copies only the chunks
    /// written since it was clean, when it has `src`'s length (it has not
    /// grown); all of `src` otherwise. It is then clean.
    pub(crate) fn reset(&mut self, src: &[u8])
        requires old(self).base() == src@,
        ensures final(self)@ == src@, final(self).base() == src@,
    {
        let t = self.take();
        proof { use_type_invariant(&t); t.lemma_room(); }
        let Mem { mut bytes, mut dirty, base } = t;
        let n = bytes.len();
        if n != src.len() {
            let mut v = vec![0u8; src.len()];
            prims::copy_in(&mut v, 0, src, 0, src.len());
            proof { assert(v@ =~= src@); }
            *self = Mem::new(v);
            return;
        }
        let nd = dirty.len();
        let mut c = 0;
        while c < nd
            invariant
                0 <= c <= nd,
                bytes@.len() == n == src@.len(),
                dirty@.len() == nd == n as int / CHUNK as int + 1,
                base@ == src@,
                agrees(bytes@, dirty@, src@),
                forall|q: int| 0 <= q < c ==> !#[trigger] dirty@[q],
            decreases nd - c,
        {
            if dirty[c] {
                // `c * CHUNK <= n`, as `c <= n / CHUNK`.
                proof { lemma_ck(n as int); }
                let lo = c * CHUNK;
                let ghost b0 = bytes@;
                let ghost d0 = dirty@;
                let k = if n - lo < CHUNK { n - lo } else { CHUNK };
                prims::copy_in(&mut bytes, lo, src, lo, k);
                dirty[c] = false;
                proof {
                    assert forall|i: int| 0 <= i < bytes@.len() && i < src@.len() && !dirty@[ck(i)] implies #[trigger] bytes@[i] == src@[i] by {
                        lemma_ck(i);
                        if lo <= i < lo + k {
                            assert(bytes@[i] == src@.subrange(lo as int, lo + k)[i - lo]);
                        } else {
                            if i < lo { assert(bytes@[i] == b0.subrange(0, lo as int)[i]); }
                            else { assert(bytes@[i] == b0.subrange(lo + k, b0.len() as int)[i - lo - k]); }
                            // Not in chunk `c`, so its flag did not change.
                            if ck(i) == c as int {
                                assert(i >= lo + k);
                                assert(k == CHUNK || lo + k == n);
                            }
                            assert(!d0[ck(i)]);
                        }
                    }
                }
            }
            c += 1;
        }
        proof {
            assert forall|i: int| 0 <= i < n implies bytes@[i] == src@[i] by {
                lemma_ck(i);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(i, n as int, CHUNK as int);
                assert(!dirty@[ck(i)]);
                assert(bytes@[i] == src@[i]);
            }
            assert(bytes@ =~= src@);
        }
        *self = Mem { bytes, dirty, base };
    }
}

} // verus!

impl Mem {
    /// The bytes, for a caller outside the proofs that writes them without
    /// saying where: every chunk is marked written first.
    pub fn all_mut(&mut self) -> &mut [u8] {
        self.mark_all();
        self.bytes.as_mut_slice()
    }
}
