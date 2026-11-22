//! The streaming hashers, proven: whatever the sizes of the pieces given to
//! `update`, `finalize` returns `spec::sha256` (or `spec::sha224`) of all
//! of them in order.
//!
//! [`Engine`] holds H(i) over the whole blocks seen so far and up to 63
//! bytes of the next block; whole blocks of an `update` go straight from
//! the caller's slice to the compression function without being copied.
use crate::cpu;
use crate::spec;
use verilith_core::prims::copy_in;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// Lemmas about hash_blocks
// ---------------------------------------------------------------------------

/// `hash_blocks` reads only the blocks it covers.
pub proof fn lemma_prefix(h0: Seq<u32>, p: Seq<u8>, q: Seq<u8>, n: nat)
    requires
        64 * n <= p.len(),
        64 * n <= q.len(),
        p.subrange(0, 64 * n as int) == q.subrange(0, 64 * n as int),
    ensures
        spec::hash_blocks(h0, p, n) == spec::hash_blocks(h0, q, n),
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as nat;
        assert(p.subrange(0, 64 * k as int) =~= p.subrange(0, 64 * n as int).subrange(0, 64 * k as int));
        assert(q.subrange(0, 64 * k as int) =~= q.subrange(0, 64 * n as int).subrange(0, 64 * k as int));
        lemma_prefix(h0, p, q, k);
        assert(spec::block(p, k as int) =~= p.subrange(0, 64 * n as int).subrange(64 * k as int, 64 * n as int));
        assert(spec::block(q, k as int) =~= q.subrange(0, 64 * n as int).subrange(64 * k as int, 64 * n as int));
    }
}

/// Hashing `p` then `q`, where `p` is `k` whole blocks.
pub proof fn lemma_concat(h0: Seq<u32>, p: Seq<u8>, q: Seq<u8>, k: nat, j: nat)
    requires
        p.len() == 64 * k,
        64 * j <= q.len(),
    ensures
        spec::hash_blocks(h0, p + q, k + j) == spec::hash_blocks(spec::hash_blocks(h0, p, k), q, j),
    decreases j,
{
    if j == 0 {
        assert((p + q).subrange(0, 64 * k as int) =~= p.subrange(0, 64 * k as int));
        lemma_prefix(h0, p + q, p, k);
    } else {
        let i = (j - 1) as nat;
        lemma_concat(h0, p, q, k, i);
        assert(spec::block(p + q, (k + i) as int) =~= spec::block(q, i as int));
        assert((k + j - 1) as nat == k + i);
    }
}

/// Absorbing the whole blocks `q` after the whole blocks `a`, with more
/// data `b` after them.
proof fn lemma_absorb(iv: Seq<u32>, h: Seq<u32>, a: Seq<u8>, q: Seq<u8>, b: Seq<u8>)
    requires
        a.len() % 64 == 0,
        q.len() % 64 == 0,
        h == spec::hash_blocks(iv, a, a.len() / 64),
    ensures
        spec::hash_blocks(h, q, q.len() / 64) == spec::hash_blocks(iv, a + q + b, (a.len() + q.len()) / 64),
{
    let k = a.len() / 64;
    let j = q.len() / 64;
    lemma_concat(iv, a, q, k, j);
    assert((a + q + b).subrange(0, 64 * (k + j) as int) =~= (a + q).subrange(0, 64 * (k + j) as int));
    lemma_prefix(iv, a + q + b, a + q, k + j);
    assert((a.len() + q.len()) / 64 == k + j);
}

/// A byte count modulo 2^64, continued by `n` more bytes.
proof fn lemma_count(c: u64, total: nat, n: u64)
    requires
        c as int == total % 0x1_0000_0000_0000_0000,
    ensures
        vstd::wrapping::u64_specs::wrapping_add(c, n) as int == (total + n) % 0x1_0000_0000_0000_0000,
{
    let m = 0x1_0000_0000_0000_0000int;
    vstd::arithmetic::div_mod::lemma_add_mod_noop(total as int, n as int, m);
    vstd::arithmetic::div_mod::lemma_small_mod(n as nat, m as nat);
    if c as int + n as int >= m {
        vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(c as int + n as int, m);
        vstd::arithmetic::div_mod::lemma_small_mod((c as int + n as int - m) as nat, m as nat);
    } else {
        vstd::arithmetic::div_mod::lemma_small_mod((c as int + n as int) as nat, m as nat);
    }
}

// ---------------------------------------------------------------------------
// The engine shared by SHA-224 and SHA-256
// ---------------------------------------------------------------------------

/// H(i) over the whole blocks so far, and the bytes of the next block.
#[derive(Clone, Copy)]
pub struct Engine {
    h: [u32; 8],
    buf: [u8; 64],
    /// Bytes in `buf`, below 64.
    n: usize,
    /// Bytes so far, modulo 2^64.
    len: u64,
    // Read only by the proofs.
    #[allow(dead_code)]
    iv: Ghost<Seq<u32>>,
    data: Ghost<Seq<u8>>,
}

impl Engine {
    /// Every byte given to `update`, in order.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.data@
    }

    /// H(0).
    pub closed spec fn iv(&self) -> Seq<u32> {
        self.iv@
    }

    pub closed spec fn wf(&self) -> bool {
        let d = self.data@;
        let full = d.len() - self.n;
        &&& self.n < 64
        &&& full >= 0
        &&& full % 64 == 0
        &&& self.h@ == spec::hash_blocks(self.iv@, d, (full / 64) as nat)
        &&& self.buf@.subrange(0, self.n as int) == d.subrange(full, d.len() as int)
        &&& self.len as int == d.len() % 0x1_0000_0000_0000_0000
    }

    pub fn new(iv: [u32; 8]) -> (r: Self)
        ensures
            r.wf(),
            r.iv() == iv@,
            r.data() == Seq::<u8>::empty(),
    {
        let r = Engine { h: iv, buf: [0u8; 64], n: 0, len: 0, iv: Ghost(iv@), data: Ghost(Seq::empty()) };
        assert(r.buf@.subrange(0, 0) =~= r.data@.subrange(0, 0));
        r
    }

    /// Puts the first bytes of `d` into the part-filled buffer, and
    /// compresses it if that fills it. Returns how many bytes it took.
    fn fill(&mut self, d: &[u8]) -> (i: usize)
        requires
            old(self).wf(),
            old(self).n > 0,
        ensures
            final(self).wf(),
            final(self).iv() == old(self).iv(),
            i <= d@.len(),
            final(self).n == 0 || i == d@.len(),
            final(self).data() == old(self).data() + d@.subrange(0, i as int),
    {
        let ghost d0 = self.data@;
        let ghost iv = self.iv@;
        let len = d.len();
        let n = self.n;
        let take = if len < 64 - n { len } else { 64 - n };
        let ghost full = d0.len() - n;
        let ghost k = (full / 64) as nat;
        let ghost a = d0.subrange(0, full);
        let ghost d1 = d0 + d@.subrange(0, take as int);
        copy_in(&mut self.buf, n, d, 0, take);
        proof {
            assert(self.buf@.subrange(0, (n + take) as int) =~= d1.subrange(full, d1.len() as int));
            assert(64 * k == full);
            assert(a.subrange(0, full) =~= d0.subrange(0, full));
            lemma_prefix(iv, d0, a, k);
        }
        if n + take == 64 {
            let ghost h0 = self.h@;
            cpu::compress_blocks(&mut self.h, &self.buf);
            proof {
                lemma_absorb(iv, h0, a, self.buf@, Seq::empty());
                assert(a + self.buf@ + Seq::<u8>::empty() =~= d1);
                assert(self.buf@.subrange(0, 0) =~= d1.subrange(d1.len() as int, d1.len() as int));
            }
            self.n = 0;
        } else {
            proof {
                assert(d1.subrange(0, full) =~= a.subrange(0, full));
                lemma_prefix(iv, a, d1, k);
            }
            self.n = n + take;
        }
        proof {
            lemma_count(self.len, d0.len(), take as u64);
        }
        self.len = self.len.wrapping_add(take as u64);
        self.data = Ghost(d1);
        take
    }

    /// Compresses the whole blocks of `d[i..]` where they are and keeps the
    /// rest. The buffer must be empty.
    fn absorb(&mut self, d: &[u8], i: usize)
        requires
            old(self).wf(),
            old(self).n == 0,
            i <= d@.len(),
        ensures
            final(self).wf(),
            final(self).iv() == old(self).iv(),
            final(self).data() == old(self).data() + d@.subrange(i as int, d@.len() as int),
    {
        let ghost d0 = self.data@;
        let ghost iv = self.iv@;
        let len = d.len();
        let whole = (len - i) / 64 * 64;
        let q = slice_subrange(d, i, i + whole);
        let ghost h0 = self.h@;
        let ghost rest = d@.subrange((i + whole) as int, len as int);
        let ghost d1 = d0 + d@.subrange(i as int, len as int);
        cpu::compress_blocks(&mut self.h, q);
        proof {
            assert(whole % 64 == 0);
            lemma_absorb(iv, h0, d0, q@, rest);
            assert(d0 + q@ + rest =~= d1);
        }
        let tail = len - i - whole;
        copy_in(&mut self.buf, 0, d, i + whole, tail);
        proof {
            assert(self.buf@.subrange(0, tail as int) =~= d1.subrange(d1.len() - tail, d1.len() as int));
            lemma_count(self.len, d0.len(), (len - i) as u64);
        }
        self.len = self.len.wrapping_add((len - i) as u64);
        self.n = tail;
        self.data = Ghost(d1);
    }

    /// Continues with the bytes of `d`.
    pub fn update(&mut self, d: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).iv() == old(self).iv(),
            final(self).data() == old(self).data() + d@,
    {
        let ghost d0 = self.data@;
        let len = d.len();
        let mut i: usize = 0;
        if self.n > 0 {
            i = self.fill(d);
        }
        // Either the buffer is empty or all of `d` is in it.
        if self.n == 0 {
            self.absorb(d, i);
            assert(d0 + d@.subrange(0, i as int) + d@.subrange(i as int, len as int) =~= d0 + d@);
        } else {
            assert(d@.subrange(0, len as int) =~= d@);
        }
        proof {
            if old(self).n == 0 {
                assert(d@.subrange(0, len as int) =~= d@);
            }
        }
    }

    /// The final block, or two, of the padded message: the buffered bytes,
    /// 0x80, zeros, and the bit length in the last 8 bytes.
    pub fn finish(&self) -> (r: [u32; 8])
        requires
            self.wf(),
        ensures
            r@ == spec::hash(self.iv(), self.data()),
    {
        let ghost d = self.data@;
        let ghost iv = self.iv@;
        let ghost p = spec::pad(d);
        let n = self.n;
        let ghost full = d.len() - n;
        let ghost k = (full / 64) as nat;
        let ghost a = d.subrange(0, full);
        let ghost rest = p.subrange(full, p.len() as int);
        let ghost z = spec::zeros(d.len());
        proof {
            lemma_pad(d);
            assert(64 * k == full);
            assert(a.subrange(0, full) =~= d.subrange(0, full));
            lemma_prefix(iv, d, a, k);
            assert(p =~= a + rest);
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-(k as int), 55 - n, 64);
            assert(55 - d.len() == 64 * (-(k as int)) + (55 - n));
            assert(forall|j: int| 0 <= j < n ==> self.buf@[j] == #[trigger] d[full + j]) by {
                assert forall|j: int| 0 <= j < n implies self.buf@[j] == #[trigger] d[full + j] by {
                    assert(self.buf@.subrange(0, n as int)[j] == d.subrange(full, d.len() as int)[j]);
                }
            }
        }
        let mut st = self.h;
        let mut b = self.buf;
        b[n] = 0x80;
        let mut j = n + 1;
        while j < 64
            invariant
                n < j <= 64,
                forall|i: int| 0 <= i < n ==> #[trigger] b@[i] == self.buf@[i],
                b@[n as int] == 0x80,
                forall|i: int| n < i < j ==> b@[i] == 0,
            decreases 64 - j,
        {
            b[j] = 0;
            j = j + 1;
        }
        let bits = self.len.wrapping_mul(8);
        proof {
            vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(d.len() as int, 8, 0x1_0000_0000_0000_0000int);
            assert(bits == spec::bit_len(d.len()));
        }
        if n >= 56 {
            // The length does not fit: a block of padding, then one of
            // zeros and the length.
            proof {
                assert(z == 119 - n);
                assert(p.len() == full + 128);
                assert forall|i: int| 0 <= i < 64 implies #[trigger] b@[i] == rest[i] by {
                    assert(rest[i] == p[full + i]);
                    if i < n {
                        assert(p[full + i] == d[full + i]);
                    }
                }
            }
            let ghost b1 = b@;
            let ghost h0 = st@;
            cpu::compress_blocks(&mut st, &b);
            let ghost h1 = st@;
            let mut j = 0;
            while j < 56
                invariant
                    j <= 56,
                    forall|i: int| 0 <= i < j ==> b@[i] == 0,
                decreases 56 - j,
            {
                b[j] = 0;
                j = j + 1;
            }
            put_be64(&mut b, bits);
            proof {
                assert forall|i: int| 0 <= i < 64 implies #[trigger] b@[i] == rest[64 + i] by {
                    assert(rest[64 + i] == p[full + 64 + i]);
                    if i >= 56 {
                        assert(b@[56 + (i - 56)] == spec::be64(bits)[i - 56]);
                        assert(p[d.len() + 1 + z + (i - 56)] == spec::be64(bits)[i - 56]);
                    }
                }
                assert(spec::block(rest, 0) =~= spec::block(b1, 0));
                assert(spec::block(rest, 1) =~= spec::block(b@, 0));
                assert(p.len() / 64 == k + 2);
                lemma_concat(iv, a, rest, k, 2);
                reveal_with_fuel(spec::hash_blocks, 3);
            }
            cpu::compress_blocks(&mut st, &b);
        } else {
            proof {
                assert(z == 55 - n);
                assert(p.len() == full + 64);
            }
            put_be64(&mut b, bits);
            proof {
                assert forall|i: int| 0 <= i < 64 implies #[trigger] b@[i] == rest[i] by {
                    assert(rest[i] == p[full + i]);
                    if i < n {
                        assert(p[full + i] == d[full + i]);
                    }
                    if i >= 56 {
                        assert(b@[56 + (i - 56)] == spec::be64(bits)[i - 56]);
                        assert(p[d.len() + 1 + z + (i - 56)] == spec::be64(bits)[i - 56]);
                    }
                }
                assert(spec::block(rest, 0) =~= spec::block(b@, 0));
                assert(p.len() / 64 == k + 1);
                lemma_concat(iv, a, rest, k, 1);
                reveal_with_fuel(spec::hash_blocks, 2);
            }
            cpu::compress_blocks(&mut st, &b);
        }
        st
    }
}

/// The bytes of the padded message, by where they fall.
proof fn lemma_pad(d: Seq<u8>)
    ensures
        spec::pad(d).len() == d.len() + 1 + spec::zeros(d.len()) + 8,
        forall|i: int| 0 <= i < d.len() ==> #[trigger] spec::pad(d)[i] == d[i],
        spec::pad(d)[d.len() as int] == 0x80,
        forall|i: int| d.len() < i <= d.len() + spec::zeros(d.len()) ==> #[trigger] spec::pad(d)[i] == 0,
        forall|i: int|
            0 <= i < 8 ==> #[trigger] spec::pad(d)[d.len() + 1 + spec::zeros(d.len()) + i] == spec::be64(
                spec::bit_len(d.len()),
            )[i],
{
    let z = spec::zeros(d.len());
    let s1 = d + seq![0x80u8];
    let s2 = s1 + Seq::new(z, |i: int| 0u8);
    assert(spec::pad(d) == s2 + spec::be64(spec::bit_len(d.len())));
    assert forall|i: int| d.len() < i <= d.len() + z implies #[trigger] spec::pad(d)[i] == 0 by {
        assert(s2[i] == 0);
    }
    assert forall|i: int| 0 <= i < d.len() implies #[trigger] spec::pad(d)[i] == d[i] by {
        assert(s2[i] == s1[i]);
    }
}

/// Writes `x` most significant byte first into `b[56..64]`.
#[inline(always)]
fn put_be64(b: &mut [u8; 64], x: u64)
    ensures
        forall|i: int| 0 <= i < 56 ==> final(b)@[i] == old(b)@[i],
        forall|i: int| 0 <= i < 8 ==> #[trigger] final(b)@[56 + i] == spec::be64(x)[i],
{
    b[56] = ((x >> 56) & 0xff) as u8;
    b[57] = ((x >> 48) & 0xff) as u8;
    b[58] = ((x >> 40) & 0xff) as u8;
    b[59] = ((x >> 32) & 0xff) as u8;
    b[60] = ((x >> 24) & 0xff) as u8;
    b[61] = ((x >> 16) & 0xff) as u8;
    b[62] = ((x >> 8) & 0xff) as u8;
    b[63] = (x & 0xff) as u8;
    proof {
        assert(x >> 0u64 == x) by (bit_vector);
    }
}

/// The first `4 * nw` bytes of `spec::digest_bytes(h)`.
#[inline(always)]
fn put_digest(out: &mut [u8], h: &[u32; 8], nw: usize)
    requires
        nw <= 8,
        old(out)@.len() == 4 * nw,
    ensures
        final(out)@ == spec::digest_bytes(h@).subrange(0, 4 * nw),
{
    let mut i: usize = 0;
    while i < nw
        invariant
            nw <= 8,
            i <= nw,
            out@.len() == 4 * nw,
            forall|k: int| 0 <= k < 4 * i ==> out@[k] == #[trigger] spec::digest_bytes(h@)[k],
        decreases nw - i,
    {
        let x = h[i];
        out[4 * i] = ((x >> 24) & 0xff) as u8;
        out[4 * i + 1] = ((x >> 16) & 0xff) as u8;
        out[4 * i + 2] = ((x >> 8) & 0xff) as u8;
        out[4 * i + 3] = (x & 0xff) as u8;
        proof {
            assert(x >> 0u32 == x) by (bit_vector);
            assert forall|k: int| 0 <= k < 4 * (i + 1) implies out@[k] == #[trigger] spec::digest_bytes(h@)[k] by {
                if k >= 4 * i {
                    assert(k / 4 == i as int);
                }
            }
        }
        i = i + 1;
    }
    assert(out@ =~= spec::digest_bytes(h@).subrange(0, 4 * nw));
}

// ---------------------------------------------------------------------------
// SHA-256 and SHA-224
// ---------------------------------------------------------------------------

/// A SHA-256 computation in progress.
#[derive(Clone, Copy)]
pub struct Sha256 {
    e: Engine,
}

impl Sha256 {
    /// Every byte given to `update`, in order.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.e.data()
    }

    pub closed spec fn wf(&self) -> bool {
        self.e.wf() && self.e.iv() == spec::IV256@
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.data() == Seq::<u8>::empty(),
    {
        Sha256 { e: Engine::new(spec::IV256) }
    }

    pub fn update(&mut self, d: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data() + d@,
    {
        self.e.update(d);
    }

    /// SHA-256 of everything so far. The hasher is left as it was, so it
    /// can be continued.
    pub fn finalize(&self) -> (r: [u8; 32])
        requires
            self.wf(),
        ensures
            r@ == spec::sha256(self.data()),
    {
        let h = self.e.finish();
        let mut out = [0u8; 32];
        put_digest(&mut out, &h, 8);
        assert(spec::digest_bytes(h@).subrange(0, 32) =~= spec::digest_bytes(h@));
        out
    }
}

/// A SHA-224 computation in progress.
#[derive(Clone, Copy)]
pub struct Sha224 {
    e: Engine,
}

impl Sha224 {
    /// Every byte given to `update`, in order.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.e.data()
    }

    pub closed spec fn wf(&self) -> bool {
        self.e.wf() && self.e.iv() == spec::IV224@
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.data() == Seq::<u8>::empty(),
    {
        Sha224 { e: Engine::new(spec::IV224) }
    }

    pub fn update(&mut self, d: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data() + d@,
    {
        self.e.update(d);
    }

    /// SHA-224 of everything so far. The hasher is left as it was, so it
    /// can be continued.
    pub fn finalize(&self) -> (r: [u8; 28])
        requires
            self.wf(),
        ensures
            r@ == spec::sha224(self.data()),
    {
        let h = self.e.finish();
        let mut out = [0u8; 28];
        put_digest(&mut out, &h, 7);
        out
    }
}

/// SHA-256 of `d`.
pub fn sha256(d: &[u8]) -> (r: [u8; 32])
    ensures
        r@ == spec::sha256(d@),
{
    let mut s = Sha256::new();
    s.update(d);
    assert(Seq::<u8>::empty() + d@ =~= d@);
    s.finalize()
}

/// SHA-224 of `d`.
pub fn sha224(d: &[u8]) -> (r: [u8; 28])
    ensures
        r@ == spec::sha224(d@),
{
    let mut s = Sha224::new();
    s.update(d);
    assert(Seq::<u8>::empty() + d@ =~= d@);
    s.finalize()
}

} // verus!

impl Default for Sha256 {
    fn default() -> Self {
        Sha256::new()
    }
}

impl Default for Sha224 {
    fn default() -> Self {
        Sha224::new()
    }
}

impl core::fmt::Debug for Sha256 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Sha256 { .. }")
    }
}

impl core::fmt::Debug for Sha224 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Sha224 { .. }")
    }
}

// For the C API, which reads a hasher back from caller memory: a hasher
// whose buffer count is out of range was not made by `new` and `update`.
impl Sha256 {
    pub(crate) fn plausible(&self) -> bool {
        self.e.n < 64
    }
}

impl Sha224 {
    pub(crate) fn plausible(&self) -> bool {
        self.e.n < 64
    }
}
