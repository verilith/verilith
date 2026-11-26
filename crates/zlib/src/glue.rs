//! The parts of the C ABI adapter (`capi`) that are logic rather than
//! pointer handling, moved here so they are verified: the buffer of
//! compressed output waiting to be copied to `next_out`, the search for
//! `inflateSync`'s flush marker, and `adler32_combine`.
#[cfg(verus_only)]
use verilith_checksum::{lemma_adler_append, lemma_adler_closed, lemma_adler_from, sum, wsum};
#[cfg(verus_only)]
use verilith_checksum::spec::{adler32, adler_a, adler_b, ADLER_MOD};
use verilith_core::prims::{copy_in, extend};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Pending output
// ---------------------------------------------------------------------------

/// Output a deflate stream has produced and not yet handed out. The ghost
/// field records everything appended since the buffer was made; the
/// invariant says what is waiting is its tail, so the bytes `deflate()`
/// gives the caller are the bytes the deflater produced, in order, none
/// lost or repeated.
pub struct Pending {
    out: Vec<u8>,
    opos: usize,
    all: Ghost<Seq<u8>>,
}

impl Clone for Pending {
    fn clone(&self) -> (r: Pending)
        ensures
            r.appended() == self.appended(),
            r.handed() == self.handed(),
    {
        proof {
            use_type_invariant(self);
        }
        let out = self.out.clone();
        proof {
            assert forall|i: int| 0 <= i < out@.len() implies #[trigger] out@[i] == self.out@[i] by {
                assert(cloned::<u8>(self.out@[i], out@[i]));
            }
            assert(out@ =~= self.out@);
        }
        Pending { out, opos: self.opos, all: Ghost(self.all@) }
    }
}

impl Pending {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.opos <= self.out@.len()
        &&& self.out@.len() - self.opos <= self.all@.len()
        &&& self.all@.subrange(self.all@.len() - (self.out@.len() - self.opos), self.all@.len() as int)
            == self.out@.subrange(self.opos as int, self.out@.len() as int)
    }

    /// Everything appended so far.
    pub closed spec fn appended(self) -> Seq<u8> {
        self.all@
    }

    /// Bytes waiting.
    pub closed spec fn waiting(self) -> nat {
        (self.out@.len() - self.opos) as nat
    }

    /// Everything handed out so far: all but the waiting bytes.
    pub open spec fn handed(self) -> Seq<u8> {
        self.appended().subrange(0, self.appended().len() - self.waiting())
    }

    pub proof fn lemma_waiting(tracked &self)
        ensures
            self.waiting() <= self.appended().len(),
            self.handed().len() == self.appended().len() - self.waiting(),
    {
        use_type_invariant(self);
    }

    pub fn new() -> (r: Pending)
        ensures
            r.appended() == Seq::<u8>::empty(),
            r.waiting() == 0,
    {
        let out: Vec<u8> = Vec::new();
        assert(Seq::<u8>::empty().subrange(0, 0) =~= out@.subrange(0, 0));
        Pending { out, opos: 0, all: Ghost(Seq::empty()) }
    }

    /// Bytes waiting.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self.waiting(),
            n <= self.appended().len(),
    {
        proof {
            use_type_invariant(self);
        }
        self.out.len() - self.opos
    }

    /// Appends `v`, taking it over when nothing is waiting (no copy).
    /// (By value: a call that could unwind may not hold a `&mut` to a
    /// field of a type with an invariant.)
    pub fn pushed(self, v: Vec<u8>) -> (r: Pending)
        ensures
            r.appended() == self.appended() + v@,
            r.waiting() == self.waiting() + v@.len(),
    {
        proof {
            use_type_invariant(&self);
        }
        let mut out = self.out;
        let opos = self.opos;
        let all = self.all;
        let ghost all2 = all@ + v@;
        let ghost k = (out@.len() - opos) as int;
        proof {
            assert(all2.subrange(all2.len() - (k + v@.len()), all2.len() as int) =~= all@.subrange(
                all@.len() - k,
                all@.len() as int,
            ) + v@);
        }
        if opos == out.len() {
            proof {
                assert(out@.subrange(opos as int, out@.len() as int) =~= Seq::<u8>::empty());
                assert(Seq::<u8>::empty() + v@ =~= v@);
                assert(v@.subrange(0, v@.len() as int) =~= v@);
            }
            Pending { out: v, opos: 0, all: Ghost(all2) }
        } else {
            let ghost w = out@;
            extend(&mut out, v.as_slice());
            proof {
                assert(out@.subrange(opos as int, out@.len() as int) =~= w.subrange(opos as int, w.len() as int)
                    + v@);
            }
            Pending { out, opos, all: Ghost(all2) }
        }
    }

    /// Appends a copy of `s`.
    pub fn extended(self, s: &[u8]) -> (r: Pending)
        ensures
            r.appended() == self.appended() + s@,
            r.waiting() == self.waiting() + s@.len(),
    {
        proof {
            use_type_invariant(&self);
        }
        let mut out = self.out;
        let opos = self.opos;
        let all = self.all;
        let ghost all2 = all@ + s@;
        let ghost k = (out@.len() - opos) as int;
        let ghost w = out@;
        extend(&mut out, s);
        proof {
            assert(all2.subrange(all2.len() - (k + s@.len()), all2.len() as int) =~= all@.subrange(
                all@.len() - k,
                all@.len() as int,
            ) + s@);
            assert(out@.subrange(opos as int, out@.len() as int) =~= w.subrange(opos as int, w.len() as int) + s@);
        }
        Pending { out, opos, all: Ghost(all2) }
    }

    /// Hands out as many waiting bytes as fit in `dst`, to its front, and
    /// returns how many: the next `n` bytes after those handed out before.
    pub fn drain_into(&mut self, dst: &mut [u8]) -> (n: usize)
        ensures
            n as int == if old(self).waiting() < old(dst)@.len() {
                old(self).waiting() as int
            } else {
                old(dst)@.len() as int
            },
            final(self).appended() == old(self).appended(),
            final(self).waiting() == old(self).waiting() - n,
            final(self).handed() == old(self).handed() + final(dst)@.subrange(0, n as int),
            final(dst)@.len() == old(dst)@.len(),
            final(dst)@.subrange(n as int, final(dst)@.len() as int) == old(dst)@.subrange(
                n as int,
                old(dst)@.len() as int,
            ),
    {
        proof {
            use_type_invariant(&*self);
        }
        let wait = self.out.len() - self.opos;
        let n = if wait < dst.len() { wait } else { dst.len() };
        let ghost d0 = dst@;
        let ghost o = self.out@;
        let ghost all = self.all@;
        let ghost h = all.len() - wait;
        copy_in(dst, 0, self.out.as_slice(), self.opos, n);
        proof {
            let got = dst@.subrange(0, n as int);
            assert(got =~= o.subrange(self.opos as int, self.opos + n));
            assert(dst@.subrange(n as int, dst@.len() as int) =~= d0.subrange(n as int, d0.len() as int));
            // The handed-out bytes grow by the first `n` waiting ones.
            assert forall|i: int| 0 <= i < n implies #[trigger] all[h + i] == got[i] by {
                assert(all.subrange(h, all.len() as int)[i] == o.subrange(self.opos as int, o.len() as int)[i]);
            }
            assert(all.subrange(0, h + n) =~= all.subrange(0, h) + got);
            assert(all.subrange(h + n, all.len() as int) =~= o.subrange(self.opos + n, o.len() as int)) by {
                assert forall|i: int| 0 <= i < all.len() - (h + n) implies #[trigger] all.subrange(h + n, all.len() as int)[i]
                    == o.subrange(self.opos + n, o.len() as int)[i] by {
                    assert(all.subrange(h, all.len() as int)[i + n] == o.subrange(self.opos as int, o.len() as int)[i + n]);
                }
            }
        }
        self.opos = self.opos + n;
        n
    }
}

// ---------------------------------------------------------------------------
// inflateSync's marker search
// ---------------------------------------------------------------------------

/// The `00 00 FF FF` that ends a stored block with no data (a sync flush).
pub open spec fn mark() -> Seq<u8> {
    seq![0u8, 0u8, 0xffu8, 0xffu8]
}

/// `h` ends with the first `k` bytes of the marker.
pub open spec fn ends_with_mark(h: Seq<u8>, k: nat) -> bool {
    k <= 4 && k <= h.len() && h.subrange(h.len() - k, h.len() as int) == mark().subrange(0, k as int)
}

/// zlib's `syncsearch` step: `got` marker bytes matched, then `x`. After a
/// mismatch a zero can still start (or continue) the marker.
pub open spec fn sync_next(got: u32, x: u8) -> u32 {
    if x == (if got < 2 { 0u8 } else { 0xffu8 }) {
        (got + 1) as u32
    } else if x != 0 {
        0
    } else {
        (4 - got) as u32
    }
}

proof fn lemma_sync_next(h: Seq<u8>, got: u32, x: u8)
    requires
        got < 4,
        ends_with_mark(h, got as nat),
    ensures
        ends_with_mark(h.push(x), sync_next(got, x) as nat),
{
    let h2 = h.push(x);
    let k = sync_next(got, x) as int;
    let m = mark();
    assert(m[0] == 0 && m[1] == 0 && m[2] == 0xff && m[3] == 0xff);
    if x == (if got < 2 { 0u8 } else { 0xffu8 }) {
        assert forall|i: int| 0 <= i < k implies #[trigger] h2.subrange(h2.len() - k, h2.len() as int)[i] == m.subrange(0, k)[i] by {
            if i < k - 1 {
                assert(h.subrange(h.len() - got, h.len() as int)[i] == m.subrange(0, got as int)[i]);
            }
        }
        assert(h2.subrange(h2.len() - k, h2.len() as int) =~= m.subrange(0, k));
    } else if x != 0 {
        assert(h2.subrange(h2.len() - 0, h2.len() as int) =~= m.subrange(0, 0));
    } else {
        // `got` is 2 or 3: the marker's zeros are matched, and `x` is a
        // zero where 0xff was wanted.
        assert(h.subrange(h.len() - got, h.len() as int)[got - 1] == m[got - 1]);
        if got == 2 {
            assert(h.subrange(h.len() - 2, h.len() as int)[0] == m[0]);
            assert(h2.subrange(h2.len() - 2, h2.len() as int) =~= m.subrange(0, 2));
        } else {
            assert(h2.subrange(h2.len() - 1, h2.len() as int) =~= m.subrange(0, 1));
        }
    }
}

/// How far `inflateSync` has got: the marker bytes matched so far, and
/// (ghost) every byte it has looked at.
pub struct SyncSearch {
    got: u32,
    #[allow(dead_code)]
    seen: Ghost<Seq<u8>>,
}

impl Clone for SyncSearch {
    fn clone(&self) -> (r: SyncSearch)
        ensures
            r.seen() == self.seen(),
            r.spec_found() == self.spec_found(),
    {
        proof {
            use_type_invariant(self);
        }
        SyncSearch { got: self.got, seen: Ghost(self.seen@) }
    }
}

impl SyncSearch {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        ends_with_mark(self.seen@, self.got as nat)
    }

    /// Every byte looked at since `new`.
    pub closed spec fn seen(self) -> Seq<u8> {
        self.seen@
    }

    pub closed spec fn spec_found(self) -> bool {
        self.got == 4
    }

    pub fn new() -> (r: SyncSearch)
        ensures
            r.seen() == Seq::<u8>::empty(),
            !r.spec_found(),
    {
        assert(Seq::<u8>::empty().subrange(0, 0) =~= mark().subrange(0, 0));
        SyncSearch { got: 0, seen: Ghost(Seq::empty()) }
    }

    /// The whole marker has been seen.
    pub fn found(&self) -> (r: bool)
        ensures
            r == self.spec_found(),
            r ==> self.seen().len() >= 4 && self.seen().subrange(self.seen().len() - 4, self.seen().len() as int)
                == mark(),
    {
        proof {
            use_type_invariant(self);
            if self.got == 4 {
                assert(mark().subrange(0, 4) =~= mark());
            }
        }
        self.got == 4
    }

    /// Looks through `input` for the rest of the marker, and returns the
    /// bytes used: up to and including the marker's last byte, or all of
    /// `input` if it does not end there.
    pub fn scan(&mut self, input: &[u8]) -> (n: usize)
        ensures
            n <= input@.len(),
            final(self).seen() == old(self).seen() + input@.subrange(0, n as int),
            !final(self).spec_found() ==> n == input@.len(),
            old(self).spec_found() ==> n == 0 && final(self).spec_found(),
    {
        proof {
            use_type_invariant(&*self);
        }
        let ghost s0 = self.seen@;
        let mut got = self.got;
        let mut n = 0;
        assert(input@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(s0 + Seq::<u8>::empty() =~= s0);
        while n < input.len() && got < 4
            invariant
                n <= input@.len(),
                got <= 4,
                ends_with_mark(s0 + input@.subrange(0, n as int), got as nat),
                self.got == 4 ==> n == 0 && got == 4,
            decreases input@.len() - n,
        {
            let x = input[n];
            proof {
                lemma_sync_next(s0 + input@.subrange(0, n as int), got, x);
                assert((s0 + input@.subrange(0, n as int)).push(x) =~= s0 + input@.subrange(0, n + 1));
            }
            got = if x == (if got < 2 { 0 } else { 0xff }) {
                got + 1
            } else if x != 0 {
                0
            } else {
                4 - got
            };
            n += 1;
        }
        *self = SyncSearch { got, seen: Ghost(s0 + input@.subrange(0, n as int)) };
        n
    }
}

// ---------------------------------------------------------------------------
// adler32_combine
// ---------------------------------------------------------------------------

/// The Adler-32 of A followed by B, from those of A and B and B's length:
/// proven equal to `adler32(A + B)` whenever the inputs are the checksums
/// of some A and B with `B.len() == len2`.
pub fn adler32_combine(adler1: u32, adler2: u32, len2: u64) -> (r: u32)
    ensures
        forall|x: Seq<u8>, y: Seq<u8>|
            adler32(x) == adler1 && adler32(y) == adler2 && y.len() == len2 ==> r == adler32(#[trigger] (x + y)),
{
    const BASE: u64 = 65521;
    let a1 = (adler1 % 65536) as u64;
    let b1 = (adler1 / 65536) as u64;
    let a2 = (adler2 % 65536) as u64;
    let b2 = (adler2 / 65536) as u64;
    let rem = len2 % BASE;
    assert(rem * a1 <= 65520 * 65535) by (nonlinear_arith)
        requires
            rem < 65521,
            a1 < 65536,
    ;
    // The sums of A, each counted again for every byte of B.
    let a = (a1 + a2 + BASE - 1) % BASE;
    let b = (rem * a1 % BASE + b1 + b2 + BASE - rem) % BASE;
    let r = (a + b * 65536) as u32;
    proof {
        assert forall|x: Seq<u8>, y: Seq<u8>|
            adler32(x) == adler1 && adler32(y) == adler2 && y.len() == len2 implies r == adler32(#[trigger] (x + y)) by {
            lemma_adler_combine(x, y, a1 as int, b1 as int, a2 as int, b2 as int, adler1 as int, adler2 as int);
        }
    }
    r
}

proof fn lemma_split16(v: int, a: int, b: int)
    requires
        0 <= a < 65536,
        0 <= b,
        v == b * 65536 + a,
    ensures
        v % 65536 == a,
        v / 65536 == b,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v, 65536, b, a);
}

/// `x ≡ y (mod 65521)` when they differ by a multiple of it.
proof fn lemma_cong(x: int, y: int, k: int)
    requires
        x == y + 65521 * k,
    ensures
        x % 65521 == y % 65521,
{
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(k, y, 65521);
}

proof fn lemma_adler_combine(x: Seq<u8>, y: Seq<u8>, a1: int, b1: int, a2: int, b2: int, adler1: int, adler2: int)
    requires
        adler32(x) == adler1,
        adler32(y) == adler2,
        a1 == adler1 % 65536,
        b1 == adler1 / 65536,
        a2 == adler2 % 65536,
        b2 == adler2 / 65536,
    ensures
        ((a1 + a2 + 65521 - 1) % 65521) + ((y.len() % 65521) * a1 % 65521 + b1 + b2 + 65521 - y.len()
            % 65521) % 65521 * 65536 == adler32(x + y),
{
    let m = 65521int;
    let n = y.len() as int;
    lemma_adler_from(x);
    lemma_adler_from(y);
    lemma_adler_from(x + y);
    lemma_adler_append(1, 0, x, y);
    let ax = adler_a(x) as int;
    let bx = adler_b(x) as int;
    assert(ax < m && bx < m) by {
        if x.len() > 0 {
            assert(adler_a(x) == (adler_a(x.drop_last()) + x.last() as nat) % ADLER_MOD);
            assert(adler_b(x) == (adler_b(x.drop_last()) + adler_a(x)) % ADLER_MOD);
        }
    }
    assert(adler_a(y) < m && adler_b(y) < m) by {
        if y.len() > 0 {
            assert(adler_a(y) == (adler_a(y.drop_last()) + y.last() as nat) % ADLER_MOD);
            assert(adler_b(y) == (adler_b(y.drop_last()) + adler_a(y)) % ADLER_MOD);
        }
    }
    lemma_adler_closed(ax as nat, bx as nat, y);
    lemma_adler_closed(1, 0, y);
    let s = sum(y) as int;
    let w = wsum(y) as int;
    // A + B's sums, and B's, in closed form.
    let a = (ax + s) % m;
    let b = (bx + n * ax + w) % m;
    assert(adler_a(x + y) == a && adler_b(x + y) == b);
    assert(adler_a(y) == (1 + s) % m);
    assert(adler_b(y) == (n * 1 + w) % m);
    lemma_split16(adler1, ax, bx);
    lemma_split16(adler2, adler_a(y) as int, adler_b(y) as int);
    assert(a1 == ax && b1 == bx);
    // The A sum.
    let q = (1 + s) / m;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(1 + s, m);
    assert(a2 == 1 + s - m * q);
    lemma_cong(a1 + a2 + m - 1, ax + s, 1 - q);
    // The B sum.
    let r = n % m;
    let qn = n / m;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, m);
    let t = r * a1;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t, m);
    let qt = t / m;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n + w, m);
    let qw = (n + w) / m;
    assert(b2 == n + w - m * qw);
    assert(n * ax == r * ax + m * (qn * ax)) by (nonlinear_arith)
        requires
            n == m * qn + r,
    ;
    lemma_cong(t % m + b1 + b2 + m - r, bx + n * ax + w, 1 - qt - qw + qn - qn * ax);
}

} // verus!
