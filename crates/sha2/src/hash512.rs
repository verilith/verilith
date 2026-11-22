//! The SHA-512 family's streaming hashers, proven: whatever the sizes of the
//! pieces given to `update`, `finalize` returns `spec512::sha512` (or
//! `sha384`, `sha512_224`, `sha512_256`) of all of them in order.
//!
//! [`Engine512`] is [`crate::hash::Engine`] with 128-byte blocks and a
//! 128-bit byte count, kept as two 64-bit halves so that the hasher fits
//! OpenSSL's 216-byte `SHA512_CTX` (a `u128` would align it to 16).
use crate::cpu;
use crate::spec512 as spec;
use verilith_core::prims::copy_in;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// Lemmas about hash_blocks
// ---------------------------------------------------------------------------

/// `hash_blocks` reads only the blocks it covers.
pub proof fn lemma_prefix(h0: Seq<u64>, p: Seq<u8>, q: Seq<u8>, n: nat)
    requires
        128 * n <= p.len(),
        128 * n <= q.len(),
        p.subrange(0, 128 * n as int) == q.subrange(0, 128 * n as int),
    ensures
        spec::hash_blocks(h0, p, n) == spec::hash_blocks(h0, q, n),
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as nat;
        assert(p.subrange(0, 128 * k as int) =~= p.subrange(0, 128 * n as int).subrange(0, 128 * k as int));
        assert(q.subrange(0, 128 * k as int) =~= q.subrange(0, 128 * n as int).subrange(0, 128 * k as int));
        lemma_prefix(h0, p, q, k);
        assert(spec::block(p, k as int) =~= p.subrange(0, 128 * n as int).subrange(128 * k as int, 128 * n as int));
        assert(spec::block(q, k as int) =~= q.subrange(0, 128 * n as int).subrange(128 * k as int, 128 * n as int));
    }
}

/// Hashing `p` then `q`, where `p` is `k` whole blocks.
pub proof fn lemma_concat(h0: Seq<u64>, p: Seq<u8>, q: Seq<u8>, k: nat, j: nat)
    requires
        p.len() == 128 * k,
        128 * j <= q.len(),
    ensures
        spec::hash_blocks(h0, p + q, k + j) == spec::hash_blocks(spec::hash_blocks(h0, p, k), q, j),
    decreases j,
{
    if j == 0 {
        assert((p + q).subrange(0, 128 * k as int) =~= p.subrange(0, 128 * k as int));
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
proof fn lemma_absorb(iv: Seq<u64>, h: Seq<u64>, a: Seq<u8>, q: Seq<u8>, b: Seq<u8>)
    requires
        a.len() % 128 == 0,
        q.len() % 128 == 0,
        h == spec::hash_blocks(iv, a, a.len() / 128),
    ensures
        spec::hash_blocks(h, q, q.len() / 128) == spec::hash_blocks(iv, a + q + b, (a.len() + q.len()) / 128),
{
    let k = a.len() / 128;
    let j = q.len() / 128;
    lemma_concat(iv, a, q, k, j);
    assert((a + q + b).subrange(0, 128 * (k + j) as int) =~= (a + q).subrange(0, 128 * (k + j) as int));
    lemma_prefix(iv, a + q + b, a + q, k + j);
    assert((a.len() + q.len()) / 128 == k + j);
}

/// 2^64.
pub open spec fn m64() -> int {
    0x1_0000_0000_0000_0000
}

/// 2^128.
pub open spec fn m128() -> int {
    m64() * m64()
}

/// A count modulo `m`, continued by `n`: what `wrapping_add` computes.
proof fn lemma_count(c: int, total: nat, n: int, m: int)
    requires
        0 <= c < m,
        0 <= n < m,
        c == total as int % m,
    ensures
        (if c + n >= m { c + n - m } else { c + n }) == (total + n) as int % m,
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(total as int, n, m);
    vstd::arithmetic::div_mod::lemma_small_mod(n as nat, m as nat);
    if c + n >= m {
        vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(c + n, m);
        vstd::arithmetic::div_mod::lemma_small_mod((c + n - m) as nat, m as nat);
    } else {
        vstd::arithmetic::div_mod::lemma_small_mod((c + n) as nat, m as nat);
    }
}

// ---------------------------------------------------------------------------
// The engine shared by the SHA-512 family
// ---------------------------------------------------------------------------

/// H(i) over the whole blocks so far, and the bytes of the next block.
#[derive(Clone, Copy)]
pub struct Engine512 {
    h: [u64; 8],
    buf: [u8; 128],
    /// Bytes in `buf`, below 128.
    n: usize,
    /// Bytes so far, modulo 2^128: `hi * 2^64 + lo`.
    lo: u64,
    hi: u64,
    // Read only by the proofs.
    #[allow(dead_code)]
    iv: Ghost<Seq<u64>>,
    data: Ghost<Seq<u8>>,
}

impl Engine512 {
    /// Every byte given to `update`, in order.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.data@
    }

    /// H(0).
    pub closed spec fn iv(&self) -> Seq<u64> {
        self.iv@
    }

    pub closed spec fn wf(&self) -> bool {
        let d = self.data@;
        let full = d.len() - self.n;
        &&& self.n < 128
        &&& full >= 0
        &&& full % 128 == 0
        &&& self.h@ == spec::hash_blocks(self.iv@, d, (full / 128) as nat)
        &&& self.buf@.subrange(0, self.n as int) == d.subrange(full, d.len() as int)
        &&& self.hi as int * m64() + self.lo as int == d.len() as int % m128()
    }

    pub fn new(iv: [u64; 8]) -> (r: Self)
        ensures
            r.wf(),
            r.iv() == iv@,
            r.data() == Seq::<u8>::empty(),
    {
        let r = Engine512 { h: iv, buf: [0u8; 128], n: 0, lo: 0, hi: 0, iv: Ghost(iv@), data: Ghost(Seq::empty()) };
        assert(r.buf@.subrange(0, 0) =~= r.data@.subrange(0, 0));
        r
    }

    /// The byte count, from its halves.
    #[inline(always)]
    fn count(&self) -> (c: u128)
        ensures
            c as int == self.hi as int * m64() + self.lo as int,
    {
        (self.hi as u128) * 0x1_0000_0000_0000_0000 + (self.lo as u128)
    }

    /// Adds `n` to the byte count, which was `total` modulo 2^128.
    #[inline(always)]
    fn add_count(&mut self, n: usize, Ghost(total): Ghost<nat>)
        requires
            old(self).hi as int * m64() + old(self).lo as int == total as int % m128(),
        ensures
            final(self).hi as int * m64() + final(self).lo as int == (total + n) as int % m128(),
            final(self).h == old(self).h,
            final(self).buf == old(self).buf,
            final(self).n == old(self).n,
            final(self).iv == old(self).iv,
            final(self).data == old(self).data,
    {
        let c = self.count().wrapping_add(n as u128);
        proof {
            lemma_count(self.hi as int * m64() + self.lo as int, total, n as int, m128());
        }
        self.hi = (c / 0x1_0000_0000_0000_0000) as u64;
        self.lo = (c % 0x1_0000_0000_0000_0000) as u64;
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
        let take = if len < 128 - n { len } else { 128 - n };
        let ghost full = d0.len() - n;
        let ghost k = (full / 128) as nat;
        let ghost a = d0.subrange(0, full);
        let ghost d1 = d0 + d@.subrange(0, take as int);
        copy_in(&mut self.buf, n, d, 0, take);
        proof {
            assert(self.buf@.subrange(0, (n + take) as int) =~= d1.subrange(full, d1.len() as int));
            assert(128 * k == full);
            assert(a.subrange(0, full) =~= d0.subrange(0, full));
            lemma_prefix(iv, d0, a, k);
        }
        if n + take == 128 {
            let ghost h0 = self.h@;
            cpu::compress512_blocks(&mut self.h, &self.buf);
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
        self.add_count(take, Ghost(d0.len()));
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
        let whole = (len - i) / 128 * 128;
        let q = slice_subrange(d, i, i + whole);
        let ghost h0 = self.h@;
        let ghost rest = d@.subrange((i + whole) as int, len as int);
        let ghost d1 = d0 + d@.subrange(i as int, len as int);
        cpu::compress512_blocks(&mut self.h, q);
        proof {
            assert(whole % 128 == 0);
            lemma_absorb(iv, h0, d0, q@, rest);
            assert(d0 + q@ + rest =~= d1);
        }
        let tail = len - i - whole;
        copy_in(&mut self.buf, 0, d, i + whole, tail);
        proof {
            assert(self.buf@.subrange(0, tail as int) =~= d1.subrange(d1.len() - tail, d1.len() as int));
        }
        self.add_count(len - i, Ghost(d0.len()));
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
    /// 0x80, zeros, and the bit length in the last 16 bytes.
    pub fn finish(&self) -> (r: [u64; 8])
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
        let ghost k = (full / 128) as nat;
        let ghost a = d.subrange(0, full);
        let ghost rest = p.subrange(full, p.len() as int);
        let ghost z = spec::zeros(d.len());
        proof {
            lemma_pad(d);
            assert(128 * k == full);
            assert(a.subrange(0, full) =~= d.subrange(0, full));
            lemma_prefix(iv, d, a, k);
            assert(p =~= a + rest);
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-(k as int), 111 - n, 128);
            assert(111 - d.len() == 128 * (-(k as int)) + (111 - n));
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
        while j < 128
            invariant
                n < j <= 128,
                forall|i: int| 0 <= i < n ==> #[trigger] b@[i] == self.buf@[i],
                b@[n as int] == 0x80,
                forall|i: int| n < i < j ==> b@[i] == 0,
            decreases 128 - j,
        {
            b[j] = 0;
            j = j + 1;
        }
        let bits = self.count().wrapping_mul(8);
        let bits_hi = (bits / 0x1_0000_0000_0000_0000) as u64;
        let bits_lo = (bits % 0x1_0000_0000_0000_0000) as u64;
        proof {
            vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(d.len() as int, 8, m128());
            assert(bits as int == (d.len() * 8) as int % m128());
            assert(spec::len128(d.len()) == crate::spec::be64(bits_hi) + crate::spec::be64(bits_lo));
        }
        if n >= 112 {
            // The length does not fit: a block of padding, then one of
            // zeros and the length.
            proof {
                assert(z == 239 - n);
                assert(p.len() == full + 256);
                assert forall|i: int| 0 <= i < 128 implies #[trigger] b@[i] == rest[i] by {
                    assert(rest[i] == p[full + i]);
                    if i < n {
                        assert(p[full + i] == d[full + i]);
                    }
                }
            }
            let ghost b1 = b@;
            let ghost h0 = st@;
            cpu::compress512_blocks(&mut st, &b);
            let ghost h1 = st@;
            let mut j = 0;
            while j < 112
                invariant
                    j <= 112,
                    forall|i: int| 0 <= i < j ==> b@[i] == 0,
                decreases 112 - j,
            {
                b[j] = 0;
                j = j + 1;
            }
            put_len(&mut b, bits_hi, bits_lo);
            proof {
                assert forall|i: int| 0 <= i < 128 implies #[trigger] b@[i] == rest[128 + i] by {
                    assert(rest[128 + i] == p[full + 128 + i]);
                    if i >= 112 {
                        assert(b@[112 + (i - 112)] == spec::len128(d.len())[i - 112]);
                        assert(p[d.len() + 1 + z + (i - 112)] == spec::len128(d.len())[i - 112]);
                    }
                }
                assert(spec::block(rest, 0) =~= spec::block(b1, 0));
                assert(spec::block(rest, 1) =~= spec::block(b@, 0));
                assert(p.len() / 128 == k + 2);
                lemma_concat(iv, a, rest, k, 2);
                reveal_with_fuel(spec::hash_blocks, 3);
            }
            cpu::compress512_blocks(&mut st, &b);
        } else {
            proof {
                assert(z == 111 - n);
                assert(p.len() == full + 128);
            }
            put_len(&mut b, bits_hi, bits_lo);
            proof {
                assert forall|i: int| 0 <= i < 128 implies #[trigger] b@[i] == rest[i] by {
                    assert(rest[i] == p[full + i]);
                    if i < n {
                        assert(p[full + i] == d[full + i]);
                    }
                    if i >= 112 {
                        assert(b@[112 + (i - 112)] == spec::len128(d.len())[i - 112]);
                        assert(p[d.len() + 1 + z + (i - 112)] == spec::len128(d.len())[i - 112]);
                    }
                }
                assert(spec::block(rest, 0) =~= spec::block(b@, 0));
                assert(p.len() / 128 == k + 1);
                lemma_concat(iv, a, rest, k, 1);
                reveal_with_fuel(spec::hash_blocks, 2);
            }
            cpu::compress512_blocks(&mut st, &b);
        }
        st
    }
}

/// The bytes of the padded message, by where they fall.
proof fn lemma_pad(d: Seq<u8>)
    ensures
        spec::pad(d).len() == d.len() + 1 + spec::zeros(d.len()) + 16,
        forall|i: int| 0 <= i < d.len() ==> #[trigger] spec::pad(d)[i] == d[i],
        spec::pad(d)[d.len() as int] == 0x80,
        forall|i: int| d.len() < i <= d.len() + spec::zeros(d.len()) ==> #[trigger] spec::pad(d)[i] == 0,
        forall|i: int|
            0 <= i < 16 ==> #[trigger] spec::pad(d)[d.len() + 1 + spec::zeros(d.len()) + i] == spec::len128(d.len())[i],
{
    let z = spec::zeros(d.len());
    let s1 = d + seq![0x80u8];
    let s2 = s1 + Seq::new(z, |i: int| 0u8);
    assert(spec::pad(d) == s2 + spec::len128(d.len()));
    assert forall|i: int| d.len() < i <= d.len() + z implies #[trigger] spec::pad(d)[i] == 0 by {
        assert(s2[i] == 0);
    }
    assert forall|i: int| 0 <= i < d.len() implies #[trigger] spec::pad(d)[i] == d[i] by {
        assert(s2[i] == s1[i]);
    }
}

/// Writes `hi` then `lo`, most significant byte first, into `b[112..128]`.
#[inline(always)]
fn put_len(b: &mut [u8; 128], hi: u64, lo: u64)
    ensures
        forall|i: int| 0 <= i < 112 ==> final(b)@[i] == old(b)@[i],
        forall|i: int|
            0 <= i < 16 ==> #[trigger] final(b)@[112 + i] == (crate::spec::be64(hi) + crate::spec::be64(lo))[i],
{
    b[112] = ((hi >> 56) & 0xff) as u8;
    b[113] = ((hi >> 48) & 0xff) as u8;
    b[114] = ((hi >> 40) & 0xff) as u8;
    b[115] = ((hi >> 32) & 0xff) as u8;
    b[116] = ((hi >> 24) & 0xff) as u8;
    b[117] = ((hi >> 16) & 0xff) as u8;
    b[118] = ((hi >> 8) & 0xff) as u8;
    b[119] = (hi & 0xff) as u8;
    b[120] = ((lo >> 56) & 0xff) as u8;
    b[121] = ((lo >> 48) & 0xff) as u8;
    b[122] = ((lo >> 40) & 0xff) as u8;
    b[123] = ((lo >> 32) & 0xff) as u8;
    b[124] = ((lo >> 24) & 0xff) as u8;
    b[125] = ((lo >> 16) & 0xff) as u8;
    b[126] = ((lo >> 8) & 0xff) as u8;
    b[127] = (lo & 0xff) as u8;
    proof {
        assert(hi >> 0u64 == hi) by (bit_vector);
        assert(lo >> 0u64 == lo) by (bit_vector);
    }
}

/// The first `nb` bytes of `spec512::digest_bytes(h)`.
#[inline(always)]
fn put_digest(out: &mut [u8], h: &[u64; 8], nb: usize)
    requires
        nb <= 64,
        old(out)@.len() == nb,
    ensures
        final(out)@ == spec::digest_bytes(h@).subrange(0, nb as int),
{
    let mut k: usize = 0;
    while k < nb
        invariant
            nb <= 64,
            k <= nb,
            out@.len() == nb,
            forall|i: int| 0 <= i < k ==> out@[i] == #[trigger] spec::digest_bytes(h@)[i],
        decreases nb - k,
    {
        let s = (56 - 8 * (k % 8)) as u64;
        out[k] = ((h[k / 8] >> s) & 0xff) as u8;
        k = k + 1;
    }
    assert(out@ =~= spec::digest_bytes(h@).subrange(0, nb as int));
}

// ---------------------------------------------------------------------------
// SHA-512, SHA-384, SHA-512/224 and SHA-512/256
// ---------------------------------------------------------------------------

/// A SHA-512 computation in progress.
#[derive(Clone, Copy)]
pub struct Sha512 {
    e: Engine512,
}

impl Sha512 {
    /// Every byte given to `update`, in order.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.e.data()
    }

    pub closed spec fn wf(&self) -> bool {
        self.e.wf() && self.e.iv() == spec::IV512@
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.data() == Seq::<u8>::empty(),
    {
        Sha512 { e: Engine512::new(spec::IV512) }
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

    /// SHA-512 of everything so far. The hasher is left as it was, so it
    /// can be continued.
    pub fn finalize(&self) -> (r: [u8; 64])
        requires
            self.wf(),
        ensures
            r@ == spec::sha512(self.data()),
    {
        let h = self.e.finish();
        let mut out = [0u8; 64];
        put_digest(&mut out, &h, 64);
        assert(spec::digest_bytes(h@).subrange(0, 64) =~= spec::digest_bytes(h@));
        out
    }

    /// For the C API, which reads a hasher back from caller memory.
    pub(crate) fn plausible(&self) -> bool {
        self.e.n < 128
    }
}

/// SHA-512 of `d`.
pub fn sha512(d: &[u8]) -> (r: [u8; 64])
    ensures
        r@ == spec::sha512(d@),
{
    let mut s = Sha512::new();
    s.update(d);
    assert(Seq::<u8>::empty() + d@ =~= d@);
    s.finalize()
}

/// A SHA-384 computation in progress.
#[derive(Clone, Copy)]
pub struct Sha384 {
    e: Engine512,
}

impl Sha384 {
    /// Every byte given to `update`, in order.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.e.data()
    }

    pub closed spec fn wf(&self) -> bool {
        self.e.wf() && self.e.iv() == spec::IV384@
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.data() == Seq::<u8>::empty(),
    {
        Sha384 { e: Engine512::new(spec::IV384) }
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

    /// SHA-384 of everything so far. The hasher is left as it was, so it
    /// can be continued.
    pub fn finalize(&self) -> (r: [u8; 48])
        requires
            self.wf(),
        ensures
            r@ == spec::sha384(self.data()),
    {
        let h = self.e.finish();
        let mut out = [0u8; 48];
        put_digest(&mut out, &h, 48);
        
        out
    }

    /// For the C API, which reads a hasher back from caller memory.
    pub(crate) fn plausible(&self) -> bool {
        self.e.n < 128
    }
}

/// SHA-384 of `d`.
pub fn sha384(d: &[u8]) -> (r: [u8; 48])
    ensures
        r@ == spec::sha384(d@),
{
    let mut s = Sha384::new();
    s.update(d);
    assert(Seq::<u8>::empty() + d@ =~= d@);
    s.finalize()
}

/// A SHA-512/224 computation in progress.
#[derive(Clone, Copy)]
pub struct Sha512_224 {
    e: Engine512,
}

impl Sha512_224 {
    /// Every byte given to `update`, in order.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.e.data()
    }

    pub closed spec fn wf(&self) -> bool {
        self.e.wf() && self.e.iv() == spec::IV512_224@
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.data() == Seq::<u8>::empty(),
    {
        Sha512_224 { e: Engine512::new(spec::IV512_224) }
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

    /// SHA-512/224 of everything so far. The hasher is left as it was, so it
    /// can be continued.
    pub fn finalize(&self) -> (r: [u8; 28])
        requires
            self.wf(),
        ensures
            r@ == spec::sha512_224(self.data()),
    {
        let h = self.e.finish();
        let mut out = [0u8; 28];
        put_digest(&mut out, &h, 28);
        
        out
    }
}

/// SHA-512/224 of `d`.
pub fn sha512_224(d: &[u8]) -> (r: [u8; 28])
    ensures
        r@ == spec::sha512_224(d@),
{
    let mut s = Sha512_224::new();
    s.update(d);
    assert(Seq::<u8>::empty() + d@ =~= d@);
    s.finalize()
}

/// A SHA-512/256 computation in progress.
#[derive(Clone, Copy)]
pub struct Sha512_256 {
    e: Engine512,
}

impl Sha512_256 {
    /// Every byte given to `update`, in order.
    pub closed spec fn data(&self) -> Seq<u8> {
        self.e.data()
    }

    pub closed spec fn wf(&self) -> bool {
        self.e.wf() && self.e.iv() == spec::IV512_256@
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.data() == Seq::<u8>::empty(),
    {
        Sha512_256 { e: Engine512::new(spec::IV512_256) }
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

    /// SHA-512/256 of everything so far. The hasher is left as it was, so it
    /// can be continued.
    pub fn finalize(&self) -> (r: [u8; 32])
        requires
            self.wf(),
        ensures
            r@ == spec::sha512_256(self.data()),
    {
        let h = self.e.finish();
        let mut out = [0u8; 32];
        put_digest(&mut out, &h, 32);
        
        out
    }
}

/// SHA-512/256 of `d`.
pub fn sha512_256(d: &[u8]) -> (r: [u8; 32])
    ensures
        r@ == spec::sha512_256(d@),
{
    let mut s = Sha512_256::new();
    s.update(d);
    assert(Seq::<u8>::empty() + d@ =~= d@);
    s.finalize()
}

} // verus!

impl Default for Sha512 {
    fn default() -> Self {
        Sha512::new()
    }
}

impl core::fmt::Debug for Sha512 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Sha512 { .. }")
    }
}

impl Default for Sha384 {
    fn default() -> Self {
        Sha384::new()
    }
}

impl core::fmt::Debug for Sha384 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Sha384 { .. }")
    }
}

impl Default for Sha512_224 {
    fn default() -> Self {
        Sha512_224::new()
    }
}

impl core::fmt::Debug for Sha512_224 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Sha512_224 { .. }")
    }
}

impl Default for Sha512_256 {
    fn default() -> Self {
        Sha512_256::new()
    }
}

impl core::fmt::Debug for Sha512_256 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Sha512_256 { .. }")
    }
}
