//! XXH64 with seed 0, proven equal to `spec::xxh64`.
#[cfg(verus_only)]
use crate::bytes::lemma_le_is;
use crate::spec::*;
use verilith_core::prims::load_u64_le;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

const XP1: u64 = 0x9E3779B185EBCA87;

const XP2: u64 = 0xC2B2AE3D27D4EB4F;

const XP3: u64 = 0x165667B19E3779F9;

const XP4: u64 = 0x85EBCA77C2B2AE63;

const XP5: u64 = 0x27D4EB2F165667C5;

#[inline(always)]
fn rotl(x: u64, r: u64) -> (y: u64)
    requires
        1 <= r <= 63,
    ensures
        y == rotl64(x, r),
{
    proof {
        reveal(rotl64);
    }
    (x << r) | (x >> (64 - r))
}

#[inline(always)]
fn word(b: &[u8], i: usize) -> (r: u64)
    requires
        i + 8 <= b@.len(),
    ensures
        r == le64(b@, i as int),
{
    let r = load_u64_le(b, i);
    proof {
        lemma_le_is(b@, i as int, 8);
    }
    r
}

#[inline(always)]
fn round(acc: u64, lane: u64) -> (r: u64)
    ensures
        r == round64(acc, lane),
{
    proof {
        reveal(round64);
        reveal(add64);
        reveal(mul64);
    }
    rotl(acc.wrapping_add(lane.wrapping_mul(XP2)), 31).wrapping_mul(XP1)
}

#[inline(always)]
fn merge(h: u64, v: u64) -> (r: u64)
    ensures
        r == merge64(h, v),
{
    proof {
        reveal(merge64);
        reveal(add64);
        reveal(mul64);
    }
    (h ^ round(0, v)).wrapping_mul(XP1).wrapping_add(XP4)
}

fn add(a: u64, b: u64) -> (r: u64)
    ensures
        r == add64(a, b),
{
    proof {
        reveal(add64);
    }
    a.wrapping_add(b)
}

fn mul(a: u64, b: u64) -> (r: u64)
    ensures
        r == mul64(a, b),
{
    proof {
        reveal(mul64);
    }
    a.wrapping_mul(b)
}

/// The accumulators after all whole stripes (`stripes64`).
fn stripes(b: &[u8]) -> (r: (u64, u64, u64, u64))
    ensures
        r == stripes64(b@, 0, (add64(PRIME64_1, PRIME64_2), PRIME64_2, 0u64, (0x1_0000_0000_0000_0000 - PRIME64_1) as u64)),
{
    let n = b.len();
    let ghost v0 = (add64(PRIME64_1, PRIME64_2), PRIME64_2, 0u64, (0x1_0000_0000_0000_0000 - PRIME64_1) as u64);
    let ghost goal = stripes64(b@, 0, v0);
    let mut v1 = add(XP1, XP2);
    let mut v2 = XP2;
    let mut v3 = 0u64;
    let mut v4 = 0u64.wrapping_sub(XP1);
    let mut i: usize = 0;
    proof {
        assert(v4 == (0x1_0000_0000_0000_0000 - PRIME64_1) as u64);
    }
    while n - i >= 32
        invariant
            n == b@.len(),
            i <= n,
            goal == stripes64(b@, 0, v0),
            stripes64(b@, i as int, (v1, v2, v3, v4)) == goal,
        decreases n - i,
    {
        v1 = round(v1, word(b, i));
        v2 = round(v2, word(b, i + 8));
        v3 = round(v3, word(b, i + 16));
        v4 = round(v4, word(b, i + 24));
        i = i + 32;
    }
    (v1, v2, v3, v4)
}

/// The tail from `i0` on (`tail64`).
fn tail(b: &[u8], i0: usize, h0: u64) -> (r: u64)
    requires
        i0 <= b@.len(),
    ensures
        r == tail64(b@, i0 as int, h0),
{
    let n = b.len();
    let mut h = h0;
    let mut i = i0;
    let ghost goal = tail64(b@, i0 as int, h0);
    while i < n
        invariant
            n == b@.len(),
            i <= n,
            goal == tail64(b@, i0 as int, h0),
            tail64(b@, i as int, h) == goal,
        decreases n - i,
    {
        if n - i >= 8 {
            h = add(mul(rotl(h ^ round(0, word(b, i)), 27), XP1), XP4);
            i = i + 8;
        } else if n - i >= 4 {
            let w = b[i] as u64 + 256 * (b[i + 1] as u64 + 256 * (b[i + 2] as u64 + 256 * b[i + 3] as u64));
            proof {
                reveal_with_fuel(le, 5);
            }
            h = add(mul(rotl(h ^ mul(w, XP1), 23), XP2), XP3);
            i = i + 4;
        } else {
            h = mul(rotl(h ^ mul(b[i] as u64, XP5), 11), XP1);
            i = i + 1;
        }
    }
    h
}

/// XXH64 of `b` with seed 0 (`xxh64`).
pub fn xxh64_exec(b: &[u8]) -> (r: u64)
    ensures
        r == xxh64(b@),
{
    let n = b.len();
    let full = n / 32 * 32;
    let h0 = if n >= 32 {
        let (v1, v2, v3, v4) = stripes(b);
        let h = add(add(add(rotl(v1, 1), rotl(v2, 7)), rotl(v3, 12)), rotl(v4, 18));
        merge(merge(merge(merge(h, v1), v2), v3), v4)
    } else {
        XP5
    };
    let h = tail(b, full, add(h0, n as u64));
    let h1 = mul(h ^ (h >> 33), XP2);
    let h2 = mul(h1 ^ (h1 >> 29), XP3);
    h2 ^ (h2 >> 32)
}


// ---------------------------------------------------------------------------
// Streaming
// ---------------------------------------------------------------------------

pub open spec fn xx_v0() -> (u64, u64, u64, u64) {
    (add64(PRIME64_1, PRIME64_2), PRIME64_2, 0u64, (0x1_0000_0000_0000_0000 - PRIME64_1) as u64)
}

pub open spec fn xx_step4(b: Seq<u8>, i: int, v: (u64, u64, u64, u64)) -> (u64, u64, u64, u64) {
    (
        round64(v.0, le64(b, i)),
        round64(v.1, le64(b, i + 8)),
        round64(v.2, le64(b, i + 16)),
        round64(v.3, le64(b, i + 24)),
    )
}

/// The stripes from `i` up to `j`.
pub open spec fn xx_to(b: Seq<u8>, i: int, j: int, v: (u64, u64, u64, u64)) -> (u64, u64, u64, u64)
    decreases j - i,
{
    if i < 0 || i + 32 > j {
        v
    } else {
        xx_to(b, i + 32, j, xx_step4(b, i, v))
    }
}

proof fn lemma_xx_split(b: Seq<u8>, i: int, j: int, v: (u64, u64, u64, u64))
    requires
        0 <= i <= j <= b.len(),
        (j - i) % 32 == 0,
    ensures
        stripes64(b, i, v) == stripes64(b, j, xx_to(b, i, j, v)),
    decreases j - i,
{
    if i < j {
        lemma_xx_split(b, i + 32, j, xx_step4(b, i, v));
    }
}

proof fn lemma_le_same(b: Seq<u8>, c: Seq<u8>, i: int, k: int, n: nat)
    requires
        0 <= i,
        0 <= k,
        i + n <= b.len(),
        k + n <= c.len(),
        b.subrange(i, i + n) == c.subrange(k, k + n),
    ensures
        le(b, i, n) == le(c, k, n),
    decreases n,
{
    if n > 0 {
        assert(b[i] == b.subrange(i, i + n)[0]);
        assert(c[k] == c.subrange(k, k + n)[0]);
        assert(b.subrange(i + 1, i + n) =~= b.subrange(i, i + n).subrange(1, n as int));
        assert(c.subrange(k + 1, k + n) =~= c.subrange(k, k + n).subrange(1, n as int));
        lemma_le_same(b, c, i + 1, k + 1, (n - 1) as nat);
    }
}

proof fn lemma_xx_to_ext(b: Seq<u8>, c: Seq<u8>, i: int, j: int, v: (u64, u64, u64, u64))
    requires
        0 <= i,
        j <= b.len(),
        j <= c.len(),
        b.subrange(0, j) == c.subrange(0, j),
    ensures
        xx_to(b, i, j, v) == xx_to(c, i, j, v),
    decreases j - i,
{
    if i + 32 <= j {
        assert forall|q: int| 0 <= q && q + 8 <= j implies #[trigger] b.subrange(q, q + 8) == c.subrange(q, q + 8) by {
            assert(b.subrange(q, q + 8) =~= b.subrange(0, j).subrange(q, q + 8));
            assert(c.subrange(q, q + 8) =~= c.subrange(0, j).subrange(q, q + 8));
        }
        lemma_le_same(b, c, i, i, 8);
        lemma_le_same(b, c, i + 8, i + 8, 8);
        lemma_le_same(b, c, i + 16, i + 16, 8);
        lemma_le_same(b, c, i + 24, i + 24, 8);
        lemma_xx_to_ext(b, c, i + 32, j, xx_step4(b, i, v));
    }
}

proof fn lemma_xx_to_snoc(b: Seq<u8>, i: int, j: int, v: (u64, u64, u64, u64))
    requires
        0 <= i <= j,
        j + 32 <= b.len(),
        (j - i) % 32 == 0,
    ensures
        xx_to(b, i, j + 32, v) == xx_step4(b, j, xx_to(b, i, j, v)),
    decreases j - i,
{
    if i < j {
        lemma_xx_to_snoc(b, i + 32, j, xx_step4(b, i, v));
    } else {
        reveal_with_fuel(xx_to, 2);
    }
}

proof fn lemma_tail_shift(b: Seq<u8>, d: int, c: Seq<u8>, k: int, h: u64)
    requires
        0 <= d,
        0 <= k <= c.len(),
        c == b.subrange(d, b.len() as int),
        d <= b.len(),
    ensures
        tail64(b, d + k, h) == tail64(c, k, h),
    decreases c.len() - k,
{
    if k < c.len() {
        if k + 8 <= c.len() {
            assert(b.subrange(d + k, d + k + 8) =~= c.subrange(k, k + 8));
            lemma_le_same(b, c, d + k, k, 8);
            lemma_tail_shift(b, d, c, k + 8, add64(mul64(rotl64(h ^ round64(0, le64(c, k)), 27), PRIME64_1), PRIME64_4));
        } else if k + 4 <= c.len() {
            assert(b.subrange(d + k, d + k + 4) =~= c.subrange(k, k + 4));
            lemma_le_same(b, c, d + k, k, 4);
            lemma_tail_shift(b, d, c, k + 4, add64(mul64(rotl64(h ^ mul64(le(c, k, 4) as u64, PRIME64_1), 23), PRIME64_2), PRIME64_3));
        } else {
            assert(b[d + k] == c[k]);
            lemma_tail_shift(b, d, c, k + 1, mul64(rotl64(h ^ mul64(c[k] as u64, PRIME64_5), 11), PRIME64_1));
        }
    }
}

/// XXH64 fed in pieces.
pub struct Xxh64 {
    pub v: (u64, u64, u64, u64),
    pub done: u64,
    pub buf: Vec<u8>,
}

impl Xxh64 {
    /// The state after hashing `all`.
    pub open spec fn is(&self, all: Seq<u8>) -> bool {
        &&& self.done as int % 32 == 0
        &&& self.done <= all.len()
        &&& all.len() < 0x1_0000_0000_0000_0000
        &&& self.buf@ == all.subrange(self.done as int, all.len() as int)
        &&& self.buf@.len() < 32
        &&& self.v == xx_to(all, 0, self.done as int, xx_v0())
    }

    pub fn new() -> (r: Xxh64)
        ensures
            r.is(Seq::empty()),
    {
        let r = Xxh64 { v: (add(XP1, XP2), XP2, 0, 0u64.wrapping_sub(XP1)), done: 0, buf: Vec::new() };
        proof {
            assert(r.buf@ =~= Seq::<u8>::empty().subrange(0, 0));
        }
        r
    }

    /// Hashes the whole stripes of `s`, which is `all2` from `self.done`
    /// on; the number of bytes hashed.
    #[inline(always)]
    fn stripes_of(&mut self, s: &[u8], Ghost(all2): Ghost<Seq<u8>>) -> (r: usize)
        requires
            old(self).done as int % 32 == 0,
            old(self).done as int + s@.len() <= all2.len(),
            all2.len() < 0x1_0000_0000_0000_0000,
            s@ == all2.subrange(old(self).done as int, old(self).done + s@.len()),
            old(self).v == xx_to(all2, 0, old(self).done as int, xx_v0()),
        ensures
            r <= s@.len(),
            s@.len() - r < 32,
            r % 32 == 0,
            final(self).done == old(self).done + r,
            final(self).buf == old(self).buf,
            final(self).v == xx_to(all2, 0, final(self).done as int, xx_v0()),
    {
        let n = s.len();
        let mut i: usize = 0;
        let ghost d0 = self.done as int;
        while n - i >= 32
            invariant
                n == s@.len(),
                i <= n,
                i % 32 == 0,
                d0 + n <= all2.len(),
                0 <= d0,
                d0 % 32 == 0,
                s@ == all2.subrange(d0, d0 + n),
                self.done as int == d0 + i,
                self.buf == old(self).buf,
                all2.len() < 0x1_0000_0000_0000_0000,
                self.v == xx_to(all2, 0, d0 + i, xx_v0()),
            decreases n - i,
        {
            proof {
                lemma_xx_to_snoc(all2, 0, d0 + i, xx_v0());
                assert(all2.subrange(d0 + i, d0 + i + 8) =~= s@.subrange(i as int, i + 8));
                assert(all2.subrange(d0 + i + 8, d0 + i + 16) =~= s@.subrange(i + 8, i + 16));
                assert(all2.subrange(d0 + i + 16, d0 + i + 24) =~= s@.subrange(i + 16, i + 24));
                assert(all2.subrange(d0 + i + 24, d0 + i + 32) =~= s@.subrange(i + 24, i + 32));
                lemma_le_same(all2, s@, d0 + i, i as int, 8);
                lemma_le_same(all2, s@, d0 + i + 8, i + 8, 8);
                lemma_le_same(all2, s@, d0 + i + 16, i + 16, 8);
                lemma_le_same(all2, s@, d0 + i + 24, i + 24, 8);
            }
            self.v = (
                round(self.v.0, word(s, i)),
                round(self.v.1, word(s, i + 8)),
                round(self.v.2, word(s, i + 16)),
                round(self.v.3, word(s, i + 24)),
            );
            i = i + 32;
            self.done = self.done + 32;
        }
        i
    }

    /// Hashes `data` after what came before, without copying it.
    pub fn update(&mut self, data: &[u8], Ghost(all): Ghost<Seq<u8>>)
        requires
            old(self).is(all),
            all.len() + data@.len() < 0x1_0000_0000_0000_0000,
        ensures
            final(self).is(all + data@),
    {
        let ghost all2 = all + data@;
        proof {
            assert(all.subrange(0, self.done as int) =~= all2.subrange(0, self.done as int));
            lemma_xx_to_ext(all, all2, 0, self.done as int, xx_v0());
        }
        let mut k: usize = 0;
        if self.buf.len() > 0 {
            // Top up the partial stripe first.
            let want = 32 - self.buf.len();
            k = if want < data.len() { want } else { data.len() };
            let ghost b0 = self.buf@;
            self.buf.extend_from_slice(slice_subrange(data, 0, k));
            proof {
                assert(self.buf@ =~= all2.subrange(self.done as int, all.len() + k));
            }
            if self.buf.len() < 32 {
                proof {
                    assert(k == data@.len());
                    assert(self.buf@ =~= all2.subrange(self.done as int, all2.len() as int));
                }
                return;
            }
            let mut full: Vec<u8> = Vec::new();
            full.extend_from_slice(self.buf.as_slice());
            proof {
                assert(self.buf@.len() == all.len() + k - self.done);
                assert(full@ =~= all2.subrange(self.done as int, self.done + full@.len()));
            }
            let r = self.stripes_of(full.as_slice(), Ghost(all2));
            self.buf = Vec::new();
            proof {
                assert(r == 32);
            }
        }
        // Now `self.done` is where `data[k..]` starts.
        let rest = slice_subrange(data, k, data.len());
        proof {
            assert(self.done as int == all.len() + k);
            assert(rest@ =~= all2.subrange(self.done as int, self.done + rest@.len()));
        }
        let r = self.stripes_of(rest, Ghost(all2));
        let mut nb: Vec<u8> = Vec::new();
        nb.extend_from_slice(slice_subrange(rest, r, rest.len()));
        self.buf = nb;
        proof {
            assert(self.buf@ =~= all2.subrange(self.done as int, all2.len() as int));
        }
    }

    /// The hash of everything given (`xxh64`).
    pub fn digest(&self, Ghost(all): Ghost<Seq<u8>>) -> (r: u64)
        requires
            self.is(all),
        ensures
            r == xxh64(all),
    {
        let n = self.done + self.buf.len() as u64;
        proof {
            let d = self.done as int;
            assert(d == (all.len() / 32 * 32) as int) by (nonlinear_arith)
                requires
                    d % 32 == 0,
                    0 <= all.len() - d < 32,
                    d >= 0,
            ;
            lemma_xx_split(all, 0, d, xx_v0());
            lemma_tail_shift(all, d, self.buf@, 0, 0);
        }
        let h0 = if n >= 32 {
            let (v1, v2, v3, v4) = self.v;
            let h = add(add(add(rotl(v1, 1), rotl(v2, 7)), rotl(v3, 12)), rotl(v4, 18));
            merge(merge(merge(merge(h, v1), v2), v3), v4)
        } else {
            XP5
        };
        let h1 = add(h0, n);
        proof {
            lemma_tail_shift(all, self.done as int, self.buf@, 0, h1);
        }
        let h = tail(self.buf.as_slice(), 0, h1);
        let h2 = mul(h ^ (h >> 33), XP2);
        let h3 = mul(h2 ^ (h2 >> 29), XP3);
        h3 ^ (h3 >> 32)
    }
}

} // verus!
