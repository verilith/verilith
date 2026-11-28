//! The encoder's entropy-coded data: bits written most significant first,
//! a `0x00` stuffed after every `0xFF` byte, and the last byte filled out
//! with 1 bits (T.81 F.1.2.3 and B.1.1.5; libjpeg's `jchuff.c`). Proven to
//! read back, through the specification's `ecs` and `ebit`, as the bits
//! written.
#[cfg(verus_only)]
use crate::bits::lemma_ecs_step;
use crate::spec::*;
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

// ---------------------------------------------------------------------------
// Bits as numbers
// ---------------------------------------------------------------------------
pub open spec fn b2i(b: bool) -> nat {
    if b {
        1
    } else {
        0
    }
}

/// The bits as a number, the first most significant.
pub open spec fn val(b: Seq<bool>) -> nat
    decreases b.len(),
{
    if b.len() == 0 {
        0
    } else {
        2 * val(b.drop_last()) + b2i(b.last())
    }
}

/// The low `n` bits of `v`, most significant first.
pub open spec fn bits_of(v: nat, n: nat) -> Seq<bool>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        bits_of(v / 2, (n - 1) as nat).push(v % 2 == 1)
    }
}

/// `b` is in the segment `e` from bit `k` on.
pub open spec fn bits_at(e: Seq<u8>, k: int, b: Seq<bool>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> ebit(e, k + i) == b2i(#[trigger] b[i]) as int
}

pub proof fn lemma_bits_of_len(v: nat, n: nat)
    ensures
        bits_of(v, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_bits_of_len(v / 2, (n - 1) as nat);
    }
}

pub proof fn lemma_val_bound(b: Seq<bool>)
    ensures
        val(b) < pow2(b.len()),
    decreases b.len(),
{
    if b.len() == 0 {
        lemma2_to64();
    } else {
        lemma_val_bound(b.drop_last());
        lemma_pow2_unfold(b.len());
    }
}

pub proof fn lemma_val_cat(a: Seq<bool>, b: Seq<bool>)
    ensures
        val(a + b) == val(a) * pow2(b.len()) + val(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        lemma2_to64();
    } else {
        let c = a + b;
        assert(c.drop_last() =~= a + b.drop_last());
        assert(c.last() == b.last());
        lemma_val_cat(a, b.drop_last());
        lemma_pow2_unfold(b.len());
        let p = pow2((b.len() - 1) as nat);
        assert(2 * (val(a) * p) == val(a) * (2 * p)) by (nonlinear_arith);
    }
}

pub proof fn lemma_val_bits_of(v: nat, n: nat)
    requires
        v < pow2(n),
    ensures
        val(bits_of(v, n)) == v,
        bits_of(v, n).len() == n,
    decreases n,
{
    lemma_bits_of_len(v, n);
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_pow2_unfold(n);
        lemma_val_bits_of(v / 2, (n - 1) as nat);
        let b = bits_of(v, n);
        assert(b.drop_last() =~= bits_of(v / 2, (n - 1) as nat));
    }
}

/// Bit `j` of `b`, read out of its value.
pub proof fn lemma_val_bit(b: Seq<bool>, j: int)
    requires
        0 <= j < b.len(),
    ensures
        (val(b) as int / pow2((b.len() - 1 - j) as nat) as int) % 2 == b2i(b[j]) as int,
    decreases b.len(),
{
    let m = b.len() as int;
    if j == m - 1 {
        lemma2_to64();
    } else {
        let c = b.drop_last();
        lemma_val_bit(c, j);
        let k = (m - 2 - j) as nat;
        lemma_pow2_unfold(k + 1);
        lemma_pow2_pos(k);
        let p = pow2(k) as int;
        let x = b2i(b.last()) as int;
        // (2a + x) / (2p) == a / p
        assert((2 * val(c) as int + x) / (2 * p) == val(c) as int / p) by {
            lemma_div_denominator(2 * val(c) as int + x, 2, p);
            assert((2 * val(c) as int + x) / 2 == val(c) as int) by {
                lemma_fundamental_div_mod_converse(2 * val(c) as int + x, 2, val(c) as int, x);
            }
        }
        assert(c[j] == b[j]);
        assert((m - 1 - j) as nat == k + 1);
    }
}

pub proof fn lemma_ebits_val(e: Seq<u8>, k: int, b: Seq<bool>)
    requires
        bits_at(e, k, b),
    ensures
        ebits(e, k, b.len()) == val(b),
    decreases b.len(),
{
    if b.len() > 0 {
        let c = b.drop_last();
        assert(bits_at(e, k, c)) by {
            assert forall|i: int| 0 <= i < c.len() implies ebit(e, k + i) == b2i(#[trigger] c[i]) as int by {
                assert(c[i] == b[i]);
            }
        }
        lemma_ebits_val(e, k, c);
        assert(ebit(e, k + (b.len() - 1)) == b2i(b[b.len() - 1]) as int);
        assert((b.len() - 1) as nat == c.len());
    }
}

pub proof fn lemma_bits_at_cat(e: Seq<u8>, k: int, a: Seq<bool>, b: Seq<bool>)
    ensures
        bits_at(e, k, a + b) <==> bits_at(e, k, a) && bits_at(e, k + a.len(), b),
{
    let c = a + b;
    if bits_at(e, k, c) {
        assert forall|i: int| 0 <= i < a.len() implies ebit(e, k + i) == b2i(#[trigger] a[i]) as int by {
            assert(c[i] == a[i]);
        }
        assert forall|i: int| 0 <= i < b.len() implies ebit(e, k + a.len() + i) == b2i(#[trigger] b[i]) as int by {
            assert(c[a.len() + i] == b[i]);
            assert(k + (a.len() + i) == k + a.len() + i);
        }
    }
    if bits_at(e, k, a) && bits_at(e, k + a.len(), b) {
        assert forall|i: int| 0 <= i < c.len() implies ebit(e, k + i) == b2i(#[trigger] c[i]) as int by {
            if i < a.len() {
                assert(c[i] == a[i]);
            } else {
                let j = i - a.len();
                assert(c[i] == b[j]);
                assert(ebit(e, k + a.len() + j) == b2i(b[j]) as int);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Byte stuffing
// ---------------------------------------------------------------------------
/// One data byte as it is written: `0xFF` is followed by a stuffed zero.
pub open spec fn unit(b: u8) -> Seq<u8> {
    if b == 0xFF {
        seq![0xFFu8, 0u8]
    } else {
        seq![b]
    }
}

pub open spec fn stuff(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        unit(s[0]) + stuff(s.drop_first())
    }
}

pub proof fn lemma_stuff_push(s: Seq<u8>, b: u8)
    ensures
        stuff(s.push(b)) == stuff(s) + unit(b),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(b).drop_first() =~= Seq::<u8>::empty());
        assert(stuff(Seq::<u8>::empty()) == Seq::<u8>::empty());
        assert(unit(b) + Seq::<u8>::empty() =~= unit(b));
        assert(Seq::<u8>::empty() + unit(b) =~= unit(b));
    } else {
        assert(s.push(b).drop_first() =~= s.drop_first().push(b));
        lemma_stuff_push(s.drop_first(), b);
        assert(unit(s[0]) + (stuff(s.drop_first()) + unit(b)) =~= (unit(s[0]) + stuff(s.drop_first())) + unit(b));
    }
}

/// Stuffed data followed by EOI is, to the decoder, an entropy-coded
/// segment holding exactly that data, and the next marker is the EOI.
pub proof fn lemma_ecs_stuffed(d: Seq<u8>, p: int, s: Seq<u8>)
    requires
        0 <= p,
        p + stuff(s).len() + 2 <= d.len(),
        d.subrange(p, p + stuff(s).len()) == stuff(s),
        d[p + stuff(s).len()] == 0xFF,
        d[p + stuff(s).len() + 1] == 0xD9,
    ensures
        ecs(d, p) == s,
        marker_after(d, p) == (0xD9u8, p + stuff(s).len() + 2),
    decreases s.len(),
{
    let l = stuff(s).len() as int;
    if s.len() == 0 {
        assert(l == 0);
        assert(byte(d, p) == 0xFF);
        assert(byte(d, p + 1) == 0xD9);
        assert(skip_ff(d, p + 1) == p + 1);
        assert(ecs(d, p) =~= s);
    } else {
        let u = unit(s[0]);
        let r = s.drop_first();
        assert(stuff(s) == u + stuff(r));
        assert(d[p] == stuff(s)[0]);
        if s[0] == 0xFF {
            assert(d[p + 1] == stuff(s)[1]);
            assert(byte(d, p) == 0xFF && byte(d, p + 1) == 0);
            assert(skip_ff(d, p + 1) == p + 1);
            assert(d.subrange(p + 2, p + 2 + stuff(r).len()) =~= stuff(r)) by {
                assert forall|i: int| 0 <= i < stuff(r).len() implies d.subrange(p + 2, p + 2 + stuff(r).len())[i]
                    == stuff(r)[i] by {
                    assert(d.subrange(p, p + l)[2 + i] == stuff(s)[2 + i]);
                }
            }
            lemma_ecs_stuffed(d, p + 2, r);
            lemma_ecs_step(d, p);
            assert(ecs(d, p) =~= s);
        } else {
            assert(byte(d, p) == s[0]);
            assert(d.subrange(p + 1, p + 1 + stuff(r).len()) =~= stuff(r)) by {
                assert forall|i: int| 0 <= i < stuff(r).len() implies d.subrange(p + 1, p + 1 + stuff(r).len())[i]
                    == stuff(r)[i] by {
                    assert(d.subrange(p, p + l)[1 + i] == stuff(s)[1 + i]);
                }
            }
            lemma_ecs_stuffed(d, p + 1, r);
            lemma_ecs_step(d, p);
            assert(ecs(d, p) =~= s);
        }
    }
}

// ---------------------------------------------------------------------------
// The writer
// ---------------------------------------------------------------------------
/// Writes bits. `out` holds the stuffed bytes of `done`, the whole bytes
/// written so far; the `n` bits after them are the low bits of `acc`.
pub struct BitWriter {
    pub out: Vec<u8>,
    pub acc: u64,
    pub n: u32,
    /// Every bit written, in order.
    pub bits: Ghost<Seq<bool>>,
    pub done: Ghost<Seq<u8>>,
}

impl BitWriter {
    pub open spec fn wf(&self) -> bool {
        let l = 8 * self.done@.len();
        &&& self.n < 8
        &&& self.bits@.len() == l + self.n
        &&& bits_at(self.done@, 0, self.bits@.subrange(0, l as int))
        &&& self.acc == val(self.bits@.subrange(l as int, self.bits@.len() as int))
        &&& self.out@ == stuff(self.done@)
    }

    pub fn new(out: Vec<u8>) -> (r: BitWriter)
        requires
            out@.len() == 0,
        ensures
            r.wf(),
            r.bits@ == Seq::<bool>::empty(),
            r.out@ == Seq::<u8>::empty(),
    {
        let r = BitWriter { out, acc: 0, n: 0, bits: Ghost(Seq::empty()), done: Ghost(Seq::empty()) };
        proof {
            assert(r.bits@.subrange(0, 0) =~= Seq::<bool>::empty());
            assert(val(Seq::<bool>::empty()) == 0);
            assert(stuff(Seq::<u8>::empty()) == Seq::<u8>::empty());
            assert(r.out@ =~= Seq::<u8>::empty());
        }
        r
    }

    /// Writes the low `s` bits of `v`, most significant first.
    pub fn put(&mut self, v: u32, s: u32)
        requires
            old(self).wf(),
            s <= 24,
            v < pow2(s as nat),
        ensures
            final(self).wf(),
            final(self).bits@ == old(self).bits@ + bits_of(v as nat, s as nat),
            final(self).out@.len() >= old(self).out@.len(),
    {
        let ghost b0 = self.bits@;
        let ghost l0 = 8 * self.done@.len();
        proof {
            lemma2_to64();
            lemma_val_bits_of(v as nat, s as nat);
            lemma_val_bound(b0.subrange(l0 as int, b0.len() as int));
            lemma_pow2_adds(self.n as nat, s as nat);
            lemma_pow2_strictly_increases((self.n + s) as nat, 32);
            lemma_pow2_pos(s as nat);
            assert(self.acc * pow2(s as nat) <= u64::MAX) by (nonlinear_arith)
                requires
                    self.acc < pow2(self.n as nat),
                    pow2(self.n as nat) * pow2(s as nat) == pow2((self.n + s) as nat),
                    pow2((self.n + s) as nat) < pow2(32),
                    pow2(32) == 0x1_0000_0000,
                    pow2(s as nat) > 0,
            ;
            lemma_u64_shl_is_mul(self.acc, s as u64);
            assert(self.acc * pow2(s as nat) + v < pow2((self.n + s) as nat)) by (nonlinear_arith)
                requires
                    self.acc < pow2(self.n as nat),
                    v < pow2(s as nat),
                    pow2(self.n as nat) * pow2(s as nat) == pow2((self.n + s) as nat),
            ;
        }
        self.acc = (self.acc << s as u64) + v as u64;
        self.n = self.n + s;
        self.bits = Ghost(b0 + bits_of(v as nat, s as nat));
        proof {
            let b = self.bits@;
            assert(b.subrange(0, l0 as int) =~= b0.subrange(0, l0 as int));
            assert(b.subrange(l0 as int, b.len() as int) =~= b0.subrange(l0 as int, b0.len() as int) + bits_of(
                v as nat,
                s as nat,
            ));
            lemma_val_cat(b0.subrange(l0 as int, b0.len() as int), bits_of(v as nat, s as nat));
        }
        while self.n >= 8
            invariant
                self.n < 32,
                self.bits@ == b0 + bits_of(v as nat, s as nat),
                self.bits@.len() == 8 * self.done@.len() + self.n,
                bits_at(self.done@, 0, self.bits@.subrange(0, 8 * self.done@.len() as int)),
                self.acc == val(self.bits@.subrange(8 * self.done@.len() as int, self.bits@.len() as int)),
                self.acc < pow2(self.n as nat),
                self.out@ == stuff(self.done@),
                self.out@.len() >= old(self).out@.len(),
            decreases self.n,
        {
            self.emit_byte();
        }
    }

    /// Moves the first 8 of the bits in `acc` out to `out`.
    fn emit_byte(&mut self)
        requires
            8 <= old(self).n < 32,
            old(self).bits@.len() == 8 * old(self).done@.len() + old(self).n,
            bits_at(old(self).done@, 0, old(self).bits@.subrange(0, 8 * old(self).done@.len() as int)),
            old(self).acc == val(
                old(self).bits@.subrange(8 * old(self).done@.len() as int, old(self).bits@.len() as int),
            ),
            old(self).acc < pow2(old(self).n as nat),
            old(self).out@ == stuff(old(self).done@),
        ensures
            final(self).n == old(self).n - 8,
            final(self).bits@ == old(self).bits@,
            final(self).bits@.len() == 8 * final(self).done@.len() + final(self).n,
            bits_at(final(self).done@, 0, final(self).bits@.subrange(0, 8 * final(self).done@.len() as int)),
            final(self).acc == val(
                final(self).bits@.subrange(8 * final(self).done@.len() as int, final(self).bits@.len() as int),
            ),
            final(self).acc < pow2(final(self).n as nat),
            final(self).out@ == stuff(final(self).done@),
            final(self).out@.len() > old(self).out@.len(),
    {
        let ghost bits = self.bits@;
        let ghost done = self.done@;
        let ghost l: int = 8 * done.len() as int;
        let ghost t = bits.subrange(l as int, bits.len() as int);
        let ghost t0 = t.subrange(0, 8);
        let ghost t1 = t.subrange(8, t.len() as int);
        let sh = self.n - 8;
        proof {
            assert(t =~= t0 + t1);
            lemma_val_cat(t0, t1);
            lemma_val_bound(t0);
            lemma_val_bound(t1);
            lemma_pow2_pos(sh as nat);
            lemma_u64_shr_is_div(self.acc, sh as u64);
            lemma_fundamental_div_mod_converse(self.acc as int, pow2(sh as nat) as int, val(t0) as int, val(t1) as int);
            lemma2_to64();
            assert(t1.len() == sh);
        }
        let byte = (self.acc >> sh as u64) as u8;
        let ghost done2 = done.push(byte);
        proof {
            assert(byte == val(t0));
            assert forall|i: int| 0 <= i < l + 8 implies ebit(done2, 0 + i) == b2i(
                #[trigger] bits.subrange(0, l + 8)[i],
            ) as int by {
                if i < l {
                    assert(bits.subrange(0, l + 8)[i] == bits.subrange(0, l as int)[i]);
                    assert(ebit(done, 0 + i) == b2i(bits.subrange(0, l as int)[i]) as int);
                    assert(i / 8 < done.len()) by {
                        lemma_div_by_multiple_is_strongly_ordered(i, l as int, done.len() as int, 8);
                        lemma_div_by_multiple(done.len() as int, 8);
                    }
                    assert(done2[i / 8] == done[i / 8]);
                } else {
                    let j = i - l;
                    assert(i / 8 == done.len() && i % 8 == j) by {
                        lemma_fundamental_div_mod_converse(i, 8, done.len() as int, j);
                    }
                    assert(done2[i / 8] == byte);
                    lemma_val_bit(t0, j);
                    assert(t0[j] == bits.subrange(0, l + 8)[i]);
                }
            }
            assert(bits.subrange(0, 8 * done2.len() as int) =~= bits.subrange(0, l + 8));
            assert(bits.subrange(8 * done2.len() as int, bits.len() as int) =~= t1);
        }
        proof {
            assert(byte * pow2(sh as nat) <= self.acc) by (nonlinear_arith)
                requires
                    self.acc == val(t0) * pow2(sh as nat) + val(t1),
                    byte == val(t0),
            ;
            lemma_u64_shl_is_mul(byte as u64, sh as u64);
        }
        self.acc = self.acc - ((byte as u64) << sh as u64);
        self.n = sh;
        self.out.push(byte);
        if byte == 0xFF {
            self.out.push(0);
        }
        self.done = Ghost(done2);
        proof {
            lemma_stuff_push(done, byte);
            assert(self.out@ =~= stuff(done2));
        }
    }

    /// Fills the last byte with 1 bits (libjpeg's `flush_bits`) and returns
    /// the stuffed bytes. Every bit written is in them, in order.
    pub fn finish(self) -> (r: (Vec<u8>, Ghost<Seq<u8>>))
        requires
            self.wf(),
        ensures
            r.0@ == stuff(r.1@),
            bits_at(r.1@, 0, self.bits@),
            self.bits@.len() <= 8 * r.1@.len(),
    {
        let mut w = self;
        let ghost b0 = w.bits@;
        if w.n > 0 {
            let pad = 8 - w.n;
            proof {
                lemma2_to64();
                lemma_pow2_le_7(pad as nat);
                lemma_pow2_pos(pad as nat);
                lemma_u32_shl_is_mul(1u32, pad);
            }
            let ones = (1u32 << pad) - 1;
            let ghost dl0 = w.done@.len();
            w.put(ones, pad);
            proof {
                lemma_bits_of_len(ones as nat, pad as nat);
                assert(8 * w.done@.len() + w.n == 8 * dl0 + 8);
            }
        }
        proof {
            let l = 8 * w.done@.len();
            assert(w.n == 0);
            assert(w.bits@.subrange(0, l as int) =~= w.bits@);
            assert(w.bits@.subrange(0, b0.len() as int) =~= b0);
            assert forall|i: int| 0 <= i < b0.len() implies ebit(w.done@, 0 + i) == b2i(#[trigger] b0[i]) as int by {
                assert(b0[i] == w.bits@[i]);
                assert(w.bits@.subrange(0, l as int)[i] == w.bits@[i]);
            }
        }
        let ghost d = w.done@;
        (w.out, Ghost(d))
    }
}

proof fn lemma_pow2_le_7(n: nat)
    requires
        n <= 7,
    ensures
        pow2(n) <= 128,
{
    lemma2_to64();
    if n < 7 {
        lemma_pow2_strictly_increases(n, 7);
    }
}

} // verus!
