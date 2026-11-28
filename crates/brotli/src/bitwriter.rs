//! A bit writer for the compressor (verilith-zlib's, unchanged but for
//! imports), with the bits written so far as ghost
//! state: a sequence of 0s and 1s, first bit first. `lemma_written` turns
//! that sequence into facts about the finished output's `spec::bits`.
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/// Appends the low `k` bytes of `w`, least significant first, with one
/// unaligned 8-byte store (verilith-core's `spare::append8_spare`).
#[inline(always)]
fn push_word(v: &mut Vec<u8>, w: u64, k: usize)
    requires
        k <= 8,
    ensures
        final(v)@ == old(v)@ + Seq::new(k as nat, |j: int| ((w >> (8 * j) as u64) & 0xff) as u8),
{
    verilith_core::spare::reserve_spare(v, 8);
    verilith_core::spare::append8_spare(v, w, k);
}

/// The `n` bits of `w` from `p` as a number, first bit least significant:
/// `spec::bits` for a sequence of bits.
pub open spec fn wbits(w: Seq<nat>, p: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        w[p] + 2 * wbits(w, p + 1, (n - 1) as nat)
    }
}

/// The low `n` bits of `v`, first bit least significant.
pub open spec fn bits_of(v: nat, n: nat) -> Seq<nat>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        seq![v % 2] + bits_of(v / 2, (n - 1) as nat)
    }
}

/// The bits of bytes, as they are read.
pub open spec fn bytes_bits(s: Seq<u8>) -> Seq<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        bits_of(s[0] as nat, 8) + bytes_bits(s.subrange(1, s.len() as int))
    }
}

pub open spec fn is_bits(w: Seq<nat>) -> bool {
    forall|k: int| 0 <= k < w.len() ==> #[trigger] w[k] < 2
}

pub proof fn lemma_wbits_bound(w: Seq<nat>, p: int, n: nat)
    requires
        0 <= p,
        p + n <= w.len(),
        is_bits(w),
    ensures
        wbits(w, p, n) < pow2(n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_wbits_bound(w, p + 1, (n - 1) as nat);
        lemma_pow2_unfold(n);
        assert(w[p] < 2);
    }
}

pub proof fn lemma_wbits_split(w: Seq<nat>, p: int, m: nat, n: nat)
    ensures
        wbits(w, p, m + n) == wbits(w, p, m) + pow2(m) * wbits(w, p + m, n),
    decreases m,
{
    if m == 0 {
        lemma2_to64();
        assert(m + n == n);
    } else {
        lemma_wbits_split(w, p + 1, (m - 1) as nat, n);
        assert((m - 1) as nat + n == (m + n - 1) as nat);
        assert(p + 1 + (m - 1) as nat == p + m);
        let x = wbits(w, p + 1, (m - 1) as nat);
        let y = wbits(w, p + m, n);
        let q = pow2((m - 1) as nat);
        lemma_pow2_unfold(m);
        assert(2 * (x + q * y) == 2 * x + (2 * q) * y) by (nonlinear_arith);
    }
}

pub proof fn lemma_wbits_divmod(w: Seq<nat>, p: int, m: nat, n: nat)
    requires
        m <= n,
        0 <= p,
        p + n <= w.len(),
        is_bits(w),
    ensures
        wbits(w, p, n) % pow2(m) == wbits(w, p, m),
        wbits(w, p, n) / pow2(m) == wbits(w, p + m, (n - m) as nat),
{
    lemma_wbits_split(w, p, m, (n - m) as nat);
    assert(m + (n - m) as nat == n);
    lemma_wbits_bound(w, p, m);
    lemma_pow2_pos(m);
    let lo = wbits(w, p, m);
    let hi = wbits(w, p + m, (n - m) as nat);
    assert(wbits(w, p, n) == hi * pow2(m) + lo) by {
        lemma_mul_is_commutative(hi as int, pow2(m) as int);
    }
    lemma_fundamental_div_mod_converse(wbits(w, p, n) as int, pow2(m) as int, hi as int, lo as int);
}

/// Bits inside `w` do not change when more are appended.
pub proof fn lemma_wbits_prefix(w: Seq<nat>, u: Seq<nat>, p: int, n: nat)
    requires
        0 <= p,
        p + n <= w.len(),
    ensures
        wbits(w + u, p, n) == wbits(w, p, n),
    decreases n,
{
    if n > 0 {
        lemma_wbits_prefix(w, u, p + 1, (n - 1) as nat);
    }
}

/// Bits appended are read back after `w`.
pub proof fn lemma_wbits_suffix(w: Seq<nat>, u: Seq<nat>, p: int, n: nat)
    requires
        0 <= p,
        p + n <= u.len(),
    ensures
        wbits(w + u, w.len() + p, n) == wbits(u, p, n),
    decreases n,
{
    if n > 0 {
        lemma_wbits_suffix(w, u, p + 1, (n - 1) as nat);
        assert(w.len() + p + 1 == w.len() + (p + 1));
    }
}

pub proof fn lemma_bits_of(v: nat, n: nat)
    ensures
        bits_of(v, n).len() == n,
        is_bits(bits_of(v, n)),
        wbits(bits_of(v, n), 0, n) == v % pow2(n),
    decreases n,
{
    lemma_pow2_pos(n);
    if n == 0 {
        lemma2_to64();
    } else {
        let t = bits_of(v / 2, (n - 1) as nat);
        lemma_bits_of(v / 2, (n - 1) as nat);
        let s = seq![v % 2] + t;
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] < 2 by {
            if k > 0 {
                assert(s[k] == t[k - 1]);
            }
        }
        lemma_wbits_suffix(seq![v % 2], t, 0, (n - 1) as nat);
        assert(wbits(s, 1, (n - 1) as nat) == wbits(t, 0, (n - 1) as nat));
        lemma_pow2_unfold(n);
        lemma_pow2_pos((n - 1) as nat);
        lemma_breakdown(v as int, 2, pow2((n - 1) as nat) as int);
    }
}

pub proof fn lemma_bytes_bits(s: Seq<u8>)
    ensures
        bytes_bits(s).len() == 8 * s.len(),
        is_bits(bytes_bits(s)),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] wbits(bytes_bits(s), 8 * i, 8) == s[i] as nat,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        lemma_bytes_bits(t);
        lemma_bits_of(s[0] as nat, 8);
        lemma2_to64();
        let a = bits_of(s[0] as nat, 8);
        let bt = bytes_bits(t);
        assert(bytes_bits(s) == a + bt);
        assert forall|k: int| 0 <= k < (a + bt).len() implies #[trigger] (a + bt)[k] < 2 by {
            if k >= 8 {
                assert((a + bt)[k] == bt[k - 8]);
            } else {
                assert((a + bt)[k] == a[k]);
            }
        }
        assert forall|i: int| 0 <= i < s.len() implies #[trigger] wbits(bytes_bits(s), 8 * i, 8) == s[i] as nat by {
            if i == 0 {
                lemma_wbits_prefix(a, bt, 0, 8);
                lemma_small_mod(s[0] as nat, 256);
            } else {
                lemma_wbits_suffix(a, bt, 8 * (i - 1), 8);
                assert(8 + 8 * (i - 1) == 8 * i);
                assert(t[i - 1] == s[i]);
            }
        }
    }
}

/// The output's bits are the written bits: every byte is the next 8.
pub open spec fn bytes_hold(b: Seq<u8>, w: Seq<nat>) -> bool {
    &&& w.len() == 8 * b.len()
    &&& is_bits(w)
    &&& forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] as nat == wbits(w, 8 * i, 8)
}

/// What is written is what `spec::bits` reads.
pub proof fn lemma_written(b: Seq<u8>, w: Seq<nat>, p: int, n: nat)
    requires
        bytes_hold(b, w),
        0 <= p,
        p + n <= w.len(),
    ensures
        bits(b, p, n) == wbits(w, p, n),
    decreases n,
{
    if n > 0 {
        lemma_written(b, w, p + 1, (n - 1) as nat);
        let i = p / 8;
        let j = p % 8;
        assert(p == 8 * i + j);
        assert(0 <= i < b.len());
        lemma_bits_in_byte(b, i, j as nat, 1);
        lemma2_to64();
        assert(bits(b, p, 1) == bit(b, p) + 2 * bits(b, p + 1, 0));
        lemma_wbits_divmod(w, 8 * i, j as nat, 8);
        lemma_wbits_divmod(w, 8 * i + j, 1, (8 - j) as nat);
        assert(wbits(w, p, 1) == w[p] + 2 * wbits(w, p + 1, 0));
        lemma_pow2_pos(1);
    }
}

#[derive(Clone)]
pub struct BitWriter {
    out: Vec<u8>,
    acc: u64,
    nacc: u32,
    /// Every bit written, first bit first.
    w: Ghost<Seq<nat>>,
    /// The bytes already handed out by `take`.
    gone: Ghost<Seq<u8>>,
}

impl BitWriter {
    pub closed spec fn bits(&self) -> Seq<nat> {
        self.w@
    }

    /// The bytes `take` has returned so far.
    pub closed spec fn sent(&self) -> Seq<u8> {
        self.gone@
    }

    pub closed spec fn bytes(&self) -> Seq<u8> {
        self.gone@ + self.out@
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.nacc < 8
        &&& self.w@.len() == 8 * self.bytes().len() + self.nacc
        &&& is_bits(self.w@)
        &&& self.acc as nat == wbits(self.w@, (8 * self.bytes().len()) as int, self.nacc as nat)
        &&& forall|i: int| 0 <= i < self.bytes().len() ==> #[trigger] self.bytes()[i] as nat == wbits(self.w@, 8 * i, 8)
    }

    /// Hands out the whole bytes written so far.
    pub fn take(&mut self) -> (r: Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).bits() == old(self).bits(),
            final(self).sent() == old(self).sent() + r@,
            final(self).bytes() == final(self).sent(),
    {
        let mut r: Vec<u8> = Vec::new();
        std::mem::swap(&mut r, &mut self.out);
        self.gone = Ghost(self.gone@ + r@);
        proof {
            assert(self.bytes() =~= old(self).bytes());
            assert(self.bytes() =~= self.gone@);
        }
        r
    }

    /// With no partial byte, the bytes written hold all the bits.
    pub proof fn lemma_whole(&self)
        requires
            self.wf(),
            self.bits().len() % 8 == 0,
        ensures
            bytes_hold(self.bytes(), self.bits()),
    {
    }

    pub fn new(cap: usize) -> (r: BitWriter)
        ensures
            r.wf(),
            r.bits() == Seq::<nat>::empty(),
            r.sent() == Seq::<u8>::empty(),
    {
        let r = BitWriter { out: Vec::with_capacity(cap), acc: 0, nacc: 0, w: Ghost(Seq::empty()), gone: Ghost(Seq::empty()) };
        proof {
            reveal_with_fuel(wbits, 1);
            assert(r.bytes() =~= Seq::<u8>::empty());
        }
        r
    }

    /// Moves whole bytes from the accumulator to the output.
    #[inline(always)]
    fn drain(&mut self)
        requires
            old(self).nacc < 64,
            old(self).w@.len() == 8 * old(self).bytes().len() + old(self).nacc,
            is_bits(old(self).w@),
            old(self).acc as nat == wbits(old(self).w@, (8 * old(self).bytes().len()) as int, old(self).nacc as nat),
            forall|i: int| 0 <= i < old(self).bytes().len() ==> #[trigger] old(self).bytes()[i] as nat == wbits(old(self).w@, 8 * i, 8),
        ensures
            final(self).wf(),
            final(self).w == old(self).w,
            final(self).gone == old(self).gone,
    {
        let k = self.nacc / 8;
        let ghost p: int = (8 * self.bytes().len()) as int;
        let ghost n = self.nacc as nat;
        let ghost o0 = self.bytes();
        proof {
            assert forall|j: int| 0 <= j < k implies (#[trigger] ((self.acc >> (8 * j) as u64) & 0xff)) as nat == wbits(self.w@, p + 8 * j, 8) by {
                lemma_acc_byte(self.w@, p, n, self.acc, j as nat);
            }
            lemma_acc_rest(self.w@, p, n, self.acc, k as nat);
        }
        push_word(&mut self.out, self.acc, k as usize);
        self.acc = self.acc >> (8 * k) as u64;
        self.nacc = self.nacc - 8 * k;
        proof {
            let added = Seq::new(k as nat, |j: int| ((old(self).acc >> (8 * j) as u64) & 0xff) as u8);
            assert(self.bytes() =~= o0 + added);
            assert forall|i: int| 0 <= i < self.bytes().len() implies #[trigger] self.bytes()[i] as nat == wbits(self.w@, 8 * i, 8) by {
                if i < o0.len() {
                    assert(self.bytes()[i] == o0[i]);
                } else {
                    let j = i - o0.len();
                    let a0 = old(self).acc;
                    let sj = (8 * j) as u64;
                    let x = (a0 >> sj) & 0xff;
                    assert(x < 256) by (bit_vector)
                        requires
                            x == (a0 >> sj) & 0xff,
                    ;
                    assert(self.bytes()[i] == added[j]);
                    assert(added[j] as nat == x as nat);
                    assert(x as nat == wbits(self.w@, p + 8 * j, 8));
                    assert(p + 8 * j == 8 * i);
                }
            }
            assert(8 * self.bytes().len() == p + 8 * k);
        }
    }

    /// Writes the low `n` bits of `v`, first bit least significant.
    #[inline(always)]
    pub fn put(&mut self, v: u32, n: u32)
        requires
            old(self).wf(),
            n <= 32,
            (v as nat) < pow2(n as nat),
        ensures
            final(self).wf(),
            final(self).bits() == old(self).bits() + bits_of(v as nat, n as nat),
            final(self).sent() == old(self).sent(),
    {
        self.put64(v as u64, n);
    }

    /// Writes the low `n` bits of `v` (up to 56), first bit least
    /// significant.
    #[inline(always)]
    pub fn put64(&mut self, v: u64, n: u32)
        requires
            old(self).wf(),
            n <= 56,
            (v as nat) < pow2(n as nat),
        ensures
            final(self).wf(),
            final(self).bits() == old(self).bits() + bits_of(v as nat, n as nat),
            final(self).sent() == old(self).sent(),
    {
        let ghost w0 = self.w@;
        let ghost u = bits_of(v as nat, n as nat);
        let ghost p: int = (8 * self.bytes().len()) as int;
        proof {
            lemma_bits_of(v as nat, n as nat);
            lemma_small_mod(v as nat, pow2(n as nat));
            lemma_pow2_pos(self.nacc as nat);
            lemma_wbits_bound(w0, p, self.nacc as nat);
            lemma_wbits_prefix(w0, u, p, self.nacc as nat);
            lemma_wbits_suffix(w0, u, 0, n as nat);
            assert(w0.len() + 0 == p + self.nacc);
            lemma_wbits_split(w0 + u, p, self.nacc as nat, n as nat);
            assert forall|i: int| 0 <= i < self.bytes().len() implies #[trigger] self.bytes()[i] as nat == wbits(w0 + u, 8 * i, 8) by {
                lemma_wbits_prefix(w0, u, 8 * i, 8);
            }
            assert forall|k: int| 0 <= k < (w0 + u).len() implies #[trigger] (w0 + u)[k] < 2 by {
                if k >= w0.len() {
                    assert((w0 + u)[k] == u[k - w0.len()]);
                } else {
                    assert((w0 + u)[k] == w0[k]);
                }
            }
            lemma_or_bits64(self.acc, v, self.nacc as u64, n as nat);
        }
        self.acc = self.acc | (v << (self.nacc as u64));
        self.nacc = self.nacc + n;
        self.w = Ghost(w0 + u);
        self.drain();
    }

    /// Pads with 0 bits to a byte boundary.
    pub fn align(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).bits().len() % 8 == 0,
            final(self).bits().len() >= old(self).bits().len(),
            final(self).bits().len() < old(self).bits().len() + 8,
            final(self).bits() == old(self).bits() + bits_of(0, (final(self).bits().len() - old(self).bits().len()) as nat),
            final(self).sent() == old(self).sent(),
    {
        let ghost w0 = self.w@;
        let ghost o: int = self.bytes().len() as int;
        if self.nacc > 0 {
            let k = 8 - self.nacc;
            proof {
                lemma_pow2_pos(k as nat);
                lemma_bits_of(0, k as nat);
            }
            self.put(0, k);
            proof {
                assert(self.w@.len() == 8 * o + 8);
                lemma_mod_multiples_basic(o + 1, 8);
                assert(8 * o + 8 == (o + 1) * 8);
            }
        } else {
            proof {
                assert(w0 + bits_of(0, 0) =~= w0);
                lemma_mod_multiples_basic(o, 8);
                assert(8 * o == o * 8);
            }
        }
    }

    /// Appends whole bytes; the writer must be at a byte boundary.
    pub fn put_bytes(&mut self, s: &[u8])
        requires
            old(self).wf(),
            old(self).bits().len() % 8 == 0,
        ensures
            final(self).wf(),
            final(self).bits() == old(self).bits() + bytes_bits(s@),
            final(self).sent() == old(self).sent(),
    {
        let ghost w0 = self.w@;
        proof {
            assert(self.nacc == 0);
            lemma_bytes_bits(s@);
        }
        let ghost o0 = self.bytes();
        verilith_core::prims::extend(&mut self.out, s);
        self.w = Ghost(w0 + bytes_bits(s@));
        proof {
            let u = bytes_bits(s@);
            assert(self.bytes() =~= o0 + s@);
            assert forall|i: int| 0 <= i < self.bytes().len() implies #[trigger] self.bytes()[i] as nat == wbits(self.w@, 8 * i, 8) by {
                if i < o0.len() {
                    lemma_wbits_prefix(w0, u, 8 * i, 8);
                    assert(self.bytes()[i] == o0[i]);
                } else {
                    lemma_wbits_suffix(w0, u, 8 * (i - o0.len()), 8);
                    assert(w0.len() + 8 * (i - o0.len()) == 8 * i);
                    assert(self.bytes()[i] == s@[i - o0.len()]);
                }
            }
            assert forall|k: int| 0 <= k < self.w@.len() implies #[trigger] self.w@[k] < 2 by {
                if k >= w0.len() {
                    assert(self.w@[k] == u[k - w0.len()]);
                } else {
                    assert(self.w@[k] == w0[k]);
                }
            }
            reveal_with_fuel(wbits, 1);
        }
    }

    /// Pads to a byte boundary and returns the bytes.
    pub fn finish(mut self) -> (r: (Vec<u8>, Ghost<Seq<nat>>))
        requires
            self.wf(),
        ensures
            bytes_hold(self.sent() + r.0@, r.1@),
            r.1@.len() >= self.bits().len(),
            r.1@.len() < self.bits().len() + 8,
            r.1@.subrange(0, self.bits().len() as int) == self.bits(),
    {
        let ghost w0 = self.w@;
        self.align();
        proof {
            let n = (self.w@.len() - w0.len()) as nat;
            assert(self.w@.subrange(0, w0.len() as int) =~= w0);
        }
        let r = (self.out, Ghost(self.w@));
        r
    }
}

/// Byte `j` of an accumulator holding `n` bits from `p`.
pub proof fn lemma_acc_byte(w: Seq<nat>, p: int, n: nat, acc: u64, j: nat)
    requires
        0 <= p,
        p + n <= w.len(),
        is_bits(w),
        n < 64,
        8 * j + 8 <= n,
        acc as nat == wbits(w, p, n),
    ensures
        ((acc >> (8 * j) as u64) & 0xff) as nat == wbits(w, p + 8 * j, 8),
{
    let s = (8 * j) as u64;
    lemma_wbits_divmod(w, p, 8 * j, n);
    lemma_u64_shr_is_div(acc, s);
    let hi = acc >> s;
    lemma_wbits_divmod(w, p + 8 * j, 8, (n - 8 * j) as nat);
    lemma2_to64();
    assert((hi & 0xff) as nat == hi as nat % 256) by {
        lemma_and_mask(hi, 8);
        lemma_mask(8);
    }
}

/// What is left of the accumulator after its first `k` bytes.
pub proof fn lemma_acc_rest(w: Seq<nat>, p: int, n: nat, acc: u64, k: nat)
    requires
        0 <= p,
        p + n <= w.len(),
        is_bits(w),
        n < 64,
        k == n / 8,
        acc as nat == wbits(w, p, n),
    ensures
        (acc >> (8 * k) as u64) as nat == wbits(w, p + 8 * k, (n - 8 * k) as nat),
        n - 8 * k < 8,
{
    lemma_wbits_divmod(w, p, 8 * k, n);
    lemma_u64_shr_is_div(acc, (8 * k) as u64);
}

/// `x`'s `n1` bits then `y`'s `n2` bits, as one `n1 + n2`-bit value.
#[inline(always)]
pub fn join(x: u64, n1: u32, y: u64, n2: u32) -> (r: u64)
    requires
        n1 + n2 <= 56,
        (x as nat) < pow2(n1 as nat),
        (y as nat) < pow2(n2 as nat),
    ensures
        (r as nat) < pow2((n1 + n2) as nat),
        bits_of(r as nat, (n1 + n2) as nat) == bits_of(x as nat, n1 as nat) + bits_of(y as nat, n2 as nat),
{
    proof {
        lemma2_to64();
        lemma2_to64_rest();
        lemma_pow2_pos(n1 as nat);
        lemma_pow2_pos(n2 as nat);
        lemma_pow2_adds(n1 as nat, n2 as nat);
        if n1 + n2 < 56 {
            lemma_pow2_strictly_increases((n1 + n2) as nat, 56);
        }
        let a1 = pow2(n1 as nat) as int;
        let a2 = pow2(n2 as nat) as int;
        lemma_mul_inequality(y as int, a2 - 1, a1);
        lemma_mul_is_distributive_sub(a1, a2, 1);
        lemma_mul_is_commutative(y as int, a1);
        lemma_mul_is_commutative(a2 - 1, a1);
        lemma_mul_basics(a1);
        assert(a1 * (a2 - 1) == a1 * a2 - a1);
        assert(a1 * a2 == pow2((n1 + n2) as nat));
        assert(a1 * y as int <= a1 * (a2 - 1));
        assert(pow2(n1 as nat) * y as nat <= pow2((n1 + n2) as nat) - pow2(n1 as nat));
        lemma_u64_shl_is_mul(y, n1 as u64);
        lemma_u64_pow2_no_overflow(n1 as nat);
        lemma_u64_shl_is_mul(1, n1 as u64);
        assert(x < (1u64 << n1 as u64));
        let s = n1 as u64;
        let yy = y << s;
        assert((x | yy) == x + yy) by (bit_vector)
            requires
                x < (1u64 << s),
                yy == y << s,
                s <= 56,
        ;
        lemma_bits_concat(x as nat, n1 as nat, y as nat, n2 as nat);
    }
    x | (y << (n1 as u64))
}

/// Adding `v` (up to 56 bits) above `c` buffered bits.
pub proof fn lemma_or_bits64(x: u64, y: u64, c: u64, n: nat)
    requires
        c < 8,
        n <= 56,
        x < pow2(c as nat),
        y < pow2(n),
    ensures
        (x | (y << c)) as nat == x as nat + pow2(c as nat) * y as nat,
{
    lemma2_to64();
    lemma_pow2_pos(c as nat);
    if n < 56 {
        lemma_pow2_strictly_increases(n, 56);
    }
    assert(pow2(56) == 0x100_0000_0000_0000) by {
        lemma2_to64_rest();
    }
    assert(y < 0x100_0000_0000_0000);
    assert(pow2(c as nat) <= 128) by {
        if c < 7 {
            lemma_pow2_strictly_increases(c as nat, 7);
        }
    }
    lemma_mul_inequality(y as int, 0x100_0000_0000_0000, pow2(c as nat) as int);
    lemma_mul_is_commutative(y as int, pow2(c as nat) as int);
    lemma_u64_shl_is_mul(y, c);
    lemma_mask(c);
    assert(x < (1u64 << c));
    assert((x | (y << c)) == x + (y << c)) by (bit_vector)
        requires
            x < (1u64 << c),
            c < 8,
            y < 0x100_0000_0000_0000,
    ;
}

/// The bits of `a` then `b`, as one number.
pub proof fn lemma_bits_concat(a: nat, m: nat, b: nat, k: nat)
    requires
        a < pow2(m),
    ensures
        bits_of(a + pow2(m) * b, m + k) == bits_of(a, m) + bits_of(b, k),
    decreases m,
{
    if m == 0 {
        lemma2_to64();
        assert(pow2(0) == 1);
        assert(a == 0);
        vstd::arithmetic::mul::lemma_mul_basics(b as int);
        assert(a + pow2(m) * b == b);
        assert(bits_of(a, 0) + bits_of(b, k) =~= bits_of(b, k));
    } else {
        let m1 = (m - 1) as nat;
        let q = pow2(m1) * b;
        lemma_pow2_unfold(m);
        lemma_mul_is_associative(2, pow2(m1) as int, b as int);
        assert(pow2(m) * b == 2 * q);
        let v = a + 2 * q;
        lemma_fundamental_div_mod(a as int, 2);
        lemma_fundamental_div_mod_converse(v as int, 2, (a / 2 + q) as int, (a % 2) as int);
        assert(v % 2 == a % 2);
        assert(v / 2 == a / 2 + q);
        assert(a / 2 < pow2(m1));
        lemma_bits_concat(a / 2, m1, b, k);
        assert(m + k - 1 == m1 + k);
        assert(bits_of(v, m + k) == seq![v % 2] + bits_of(v / 2, (m + k - 1) as nat));
        assert(bits_of(a, m) == seq![a % 2] + bits_of(a / 2, m1));
        assert(seq![a % 2] + (bits_of(a / 2, m1) + bits_of(b, k)) =~= (seq![a % 2] + bits_of(a / 2, m1)) + bits_of(b, k));
    }
}

/// Adding `v` above `c` buffered bits.
pub proof fn lemma_or_bits(x: u64, y: u64, c: u64, n: nat)
    requires
        c < 8,
        n <= 32,
        x < pow2(c as nat),
        y < pow2(n),
    ensures
        (x | (y << c)) as nat == x as nat + pow2(c as nat) * y as nat,
{
    lemma2_to64();
    lemma_pow2_pos(c as nat);
    if n < 32 {
        lemma_pow2_strictly_increases(n, 32);
    }
    assert(y < 0x1_0000_0000);
    assert(pow2(c as nat) <= 128) by {
        if c < 7 {
            lemma_pow2_strictly_increases(c as nat, 7);
        }
    }
    lemma_mul_inequality(y as int, 0x1_0000_0000, pow2(c as nat) as int);
    lemma_mul_is_commutative(y as int, pow2(c as nat) as int);
    lemma_u64_shl_is_mul(y, c);
    lemma_mask(c);
    assert(x < (1u64 << c));
    assert((x | (y << c)) == x + (y << c)) by (bit_vector)
        requires
            x < (1u64 << c),
            c < 8,
            y < 0x1_0000_0000,
    ;
}


/// A position in a `BitWriter` to go back to (`BitWriter::reset`).
pub struct Mark {
    len: usize,
    acc: u64,
    nacc: u32,
    w: Ghost<Seq<nat>>,
    gone: Ghost<Seq<u8>>,
}

impl Mark {
    pub closed spec fn bits(&self) -> Seq<nat> {
        self.w@
    }

    pub closed spec fn sent(&self) -> Seq<u8> {
        self.gone@
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.nacc < 8
        &&& self.w@.len() == 8 * (self.gone@.len() + self.len) + self.nacc
        &&& is_bits(self.w@)
        &&& self.acc as nat == wbits(self.w@, 8 * (self.gone@.len() + self.len), self.nacc as nat)
    }
}

impl BitWriter {
    /// The position now, to come back to with `reset`.
    pub fn mark(&self) -> (m: Mark)
        requires
            self.wf(),
        ensures
            m.wf(),
            m.bits() == self.bits(),
            m.sent() == self.sent(),
    {
        Mark { len: self.out.len(), acc: self.acc, nacc: self.nacc, w: Ghost(self.w@), gone: Ghost(self.gone@) }
    }

    /// Forgets every bit written since `m`. Nothing may have been taken
    /// in between.
    pub fn reset(&mut self, m: &Mark)
        requires
            old(self).wf(),
            m.wf(),
            m.sent() == old(self).sent(),
            m.bits().len() <= old(self).bits().len(),
            m.bits() == old(self).bits().subrange(0, m.bits().len() as int),
        ensures
            final(self).wf(),
            final(self).bits() == m.bits(),
            final(self).sent() == old(self).sent(),
    {
        let ghost w0 = self.w@;
        let ghost wm = m.w@;
        let ghost o0 = self.bytes();
        proof {
            assert(m.len <= self.out@.len());
            assert(w0 =~= wm + w0.subrange(wm.len() as int, w0.len() as int));
        }
        self.out.truncate(m.len);
        self.acc = m.acc;
        self.nacc = m.nacc;
        self.w = Ghost(wm);
        proof {
            assert(self.bytes() =~= o0.subrange(0, self.bytes().len() as int));
            assert forall|i: int| 0 <= i < self.bytes().len() implies #[trigger] self.bytes()[i] as nat == wbits(self.w@, 8 * i, 8) by {
                assert(self.bytes()[i] == o0[i]);
                lemma_wbits_prefix(wm, w0.subrange(wm.len() as int, w0.len() as int), 8 * i, 8);
            }
        }
    }

    /// The number of bits written since `m` (for size decisions only).
    pub fn bits_since(&self, m: &Mark) -> u64 {
        let a = if self.out.len() >= m.len { (self.out.len() - m.len) as u64 } else { 0 };
        let a = if a > 0x1000_0000_0000 { 0x1000_0000_0000 } else { a };
        let b = 8 * a + self.nacc as u64;
        if b >= m.nacc as u64 { b - m.nacc as u64 } else { 0 }
    }
}

} // verus!

impl BitWriter {
    /// Bits written but not yet in a whole byte (below 8).
    pub fn pending_bits(&self) -> u32 {
        self.nacc
    }

    /// Whole bytes written but not yet taken.
    pub fn pending_bytes(&self) -> usize {
        self.out.len()
    }
}
