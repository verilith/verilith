//! Reading the input: bytes, markers, and the bits of an entropy-coded
//! segment.
use crate::prims::*;
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

/// The input is short enough that positions in and just past it cannot
/// overflow. Every input is: `decode` checks.
pub open spec fn len_ok(d: Seq<u8>) -> bool {
    d.len() + 0x2_0000 < usize::MAX
}

/// A position the decoder can be at: in the input, or within one segment
/// past its end.
pub open spec fn pos_ok(d: Seq<u8>, p: int) -> bool {
    0 <= p <= d.len() + 0x1_0010
}

/// Byte `i` of the input, with the end-of-image bytes past its end.
#[inline(always)]
pub fn rd(data: &[u8], i: usize) -> (r: u8)
    ensures
        r == byte(data@, i as int),
{
    if i < data.len() {
        data[i]
    } else if (i - data.len()) % 2 == 0 {
        0xFF
    } else {
        0xD9
    }
}

pub fn rd16(data: &[u8], i: usize) -> (r: u16)
    requires
        i < usize::MAX,
    ensures
        r as int == be16(data@, i as int),
{
    (rd(data, i) as u16) * 256 + rd(data, i + 1) as u16
}

pub fn skip_ff_x(data: &[u8], q: usize) -> (r: usize)
    requires
        len_ok(data@),
        q <= data@.len() + 0x1_0020,
    ensures
        r as int == skip_ff(data@, q as int),
        r <= q + 1 || r <= data@.len() + 1,
{
    let ghost q0 = q;
    let mut q = q;
    while q < data.len() && data[q] == 0xFF
        invariant
            skip_ff(data@, q as int) == skip_ff(data@, q0 as int),
            q <= data@.len() || q == q0,
        decreases data@.len() - q,
    {
        q += 1;
    }
    if q >= data.len() {
        if (q - data.len()) % 2 == 0 {
            q + 1
        } else {
            q
        }
    } else {
        q
    }
}

pub fn marker_after_x(data: &[u8], p: usize) -> (r: (u8, usize))
    requires
        len_ok(data@),
        p <= data@.len() + 0x1_0020,
    ensures
        r.0 == marker_after(data@, p as int).0,
        r.1 as int == marker_after(data@, p as int).1,
{
    let mut i = p;
    loop
        invariant
            len_ok(data@),
            i <= data@.len() + 0x1_0020,
            marker_after(data@, i as int) == marker_after(data@, p as int),
        decreases left(data@, i as int),
    {
        if i >= data.len() {
            return (0xD9, i + 2 + (i - data.len()) % 2);
        }
        if data[i] != 0xFF {
            i += 1;
        } else {
            let q = skip_ff_x(data, i + 1);
            let c = rd(data, q);
            proof {
                lemma_skip_ff(data@, i + 1);
            }
            if c == 0 {
                i = q + 1;
            } else {
                return (c, q + 1);
            }
        }
    }
}

/// How `ecs` and `marker_after` step over one byte of entropy-coded data.
pub proof fn lemma_ecs_step(d: Seq<u8>, p: int)
    requires
        p >= 0,
    ensures
        byte(d, p) != 0xFF ==> ecs(d, p) == seq![byte(d, p)] + ecs(d, p + 1) && marker_after(d, p) == marker_after(
            d,
            p + 1,
        ),
        byte(d, p) == 0xFF && byte(d, skip_ff(d, p + 1)) == 0 ==> ecs(d, p) == seq![0xFFu8] + ecs(
            d,
            skip_ff(d, p + 1) + 1,
        ) && marker_after(d, p) == marker_after(d, skip_ff(d, p + 1) + 1) && skip_ff(d, p + 1) < d.len(),
        byte(d, p) == 0xFF && byte(d, skip_ff(d, p + 1)) != 0 ==> ecs(d, p).len() == 0,
{
    lemma_skip_ff(d, p + 1);
    if p >= d.len() {
        let k = p - d.len();
        assert((k + 1) % 2 == 1 - k % 2);
        if k % 2 == 1 {
            // An odd position past the end holds 0xD9; the next is even.
            assert(ecs(d, p + 1) =~= Seq::<u8>::empty());
            assert(ecs(d, p) =~= seq![byte(d, p)] + ecs(d, p + 1));
        }
    }
}

// ---------------------------------------------------------------------------
// Bits
// ---------------------------------------------------------------------------
pub proof fn lemma_ebits_bound(e: Seq<u8>, k: int, n: nat)
    ensures
        0 <= ebits(e, k, n) < pow2(n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_ebits_bound(e, k, (n - 1) as nat);
        lemma_pow2_unfold(n);
        lemma_ebit_01(e, k + n - 1);
    }
}

pub proof fn lemma_ebit_01(e: Seq<u8>, k: int)
    ensures
        ebit(e, k) == 0 || ebit(e, k) == 1,
{
    if 0 <= k < 8 * e.len() {
        lemma_pow2_pos((7 - k % 8) as nat);
    }
}

/// The first `a` of `a + b` bits, then the next `b`.
pub proof fn lemma_ebits_split(e: Seq<u8>, k: int, a: nat, b: nat)
    ensures
        ebits(e, k, a + b) == ebits(e, k, a) * pow2(b) + ebits(e, k + a, b),
    decreases b,
{
    if b == 0 {
        lemma2_to64();
        assert(a + b == a);
    } else {
        lemma_ebits_split(e, k, a, (b - 1) as nat);
        assert((a + b - 1) as nat == a + (b - 1) as nat);
        lemma_pow2_unfold(b);
        let x = ebits(e, k, a);
        let q = pow2((b - 1) as nat) as int;
        assert(2 * (x * q) == x * (2 * q)) by (nonlinear_arith);
        let y = ebits(e, k + a, (b - 1) as nat);
        let bit = ebit(e, k + a + b - 1);
        assert(ebits(e, k, (a + b - 1) as nat) == x * q + y);
        assert(ebits(e, k, a + b) == 2 * ebits(e, k, (a + b - 1) as nat) + ebit(e, k + (a + b) - 1));
        assert(ebits(e, k + a, b) == 2 * y + bit);
        assert(pow2(b) == 2 * q);
    }
}

/// The eight bits of byte `j`.
pub proof fn lemma_ebits_byte(e: Seq<u8>, j: int)
    requires
        j >= 0,
    ensures
        ebits(e, 8 * j, 8) == if j < e.len() {
            e[j] as int
        } else {
            0
        },
{
    reveal_with_fuel(ebits, 9);
    lemma2_to64();
    if j < e.len() {
        let x = e[j];
        assert(x as int == 2 * (2 * (2 * (2 * (2 * (2 * (2 * ((x as int / 128) % 2) + (x as int / 64) % 2) + (x as int
            / 32) % 2) + (x as int / 16) % 2) + (x as int / 8) % 2) + (x as int / 4) % 2) + (x as int / 2) % 2) + (
        x as int / 1) % 2) by (bit_vector);
        assert(ebit(e, 8 * j + 0) == (x as int / 128) % 2);
        assert(ebit(e, 8 * j + 1) == (x as int / 64) % 2);
        assert(ebit(e, 8 * j + 2) == (x as int / 32) % 2);
        assert(ebit(e, 8 * j + 3) == (x as int / 16) % 2);
        assert(ebit(e, 8 * j + 4) == (x as int / 8) % 2);
        assert(ebit(e, 8 * j + 5) == (x as int / 4) % 2);
        assert(ebit(e, 8 * j + 6) == (x as int / 2) % 2);
        assert(ebit(e, 8 * j + 7) == (x as int / 1) % 2);
    } else {
        assert(ebit(e, 8 * j + 0) == 0);
        assert(ebit(e, 8 * j + 1) == 0);
        assert(ebit(e, 8 * j + 2) == 0);
        assert(ebit(e, 8 * j + 3) == 0);
        assert(ebit(e, 8 * j + 4) == 0);
        assert(ebit(e, 8 * j + 5) == 0);
        assert(ebit(e, 8 * j + 6) == 0);
        assert(ebit(e, 8 * j + 7) == 0);
    }
}

/// `(1 << c) - 1` is the mask of the low `c` bits.
proof fn lemma_mask(x: u64, c: nat)
    requires
        c < 64,
    ensures
        (x & (((1u64 << c) - 1) as u64)) as int == x as int % (pow2(c) as int),
        (1u64 << c) as int == pow2(c),
        pow2(c) >= 1,
{
    lemma_u64_low_bits_mask_is_mod(x, c);
    lemma_u64_pow2_no_overflow(c);
    lemma_u64_shl_is_mul(1, c as u64);
    lemma_pow2_pos(c);
    assert(((1u64 << c) - 1) as u64 == low_bits_mask(c) as u64);
}

/// Shifting a byte into a buffer whose low `c` bits matter gives one whose
/// low `c + 8` bits are those and the byte, whatever is above them.
proof fn lemma_shift_in(x: u64, c: nat, b: u8)
    requires
        c <= 56,
    ensures
        ((x << 8) | b as u64) as int % (pow2(c + 8) as int) == (x as int % (pow2(c) as int)) * 256 + b,
{
    let cc = c as u64;
    let bb = b as u64;
    let z = (x << 8) | bb;
    let y = x & (((1u64 << cc) - 1) as u64);
    lemma_mask(x, c);
    lemma2_to64();
    lemma2_to64_rest();
    assert(y < 0x100_0000_0000_0000) by (bit_vector)
        requires
            y == x & (((1u64 << cc) - 1) as u64),
            cc <= 56,
    ;
    assert(((y << 8) | bb) == y * 256 + bb) by (bit_vector)
        requires
            y < 0x100_0000_0000_0000,
            bb < 256,
    ;
    if c < 56 {
        let c8 = (cc + 8) as u64;
        assert(z & (((1u64 << c8) - 1) as u64) == (y << 8) | bb) by (bit_vector)
            requires
                z == (x << 8) | bb,
                y == x & (((1u64 << cc) - 1) as u64),
                c8 == cc + 8,
                cc < 56,
                bb < 256,
        ;
        lemma_mask(z, c + 8);
    } else {
        assert(z == (y << 8) | bb) by (bit_vector)
            requires
                z == (x << 8) | bb,
                y == x & (((1u64 << cc) - 1) as u64),
                cc == 56,
                bb < 256,
        ;
        assert(pow2(c + 8) == 0x1_0000_0000_0000_0000);
        lemma_small_mod(z as nat, pow2(64));
    }
}

/// The `k` bits above the low `c` of `x`, by shift and mask.
proof fn lemma_field(x: u64, c: nat, k: nat)
    requires
        c + k <= 64,
        c < 64,
        k < 64,
    ensures
        ((x >> c) & (((1u64 << k) - 1) as u64)) as int == (x as int % (pow2(c + k) as int)) / (pow2(c) as int),
{
    let cc = c as u64;
    let kk = k as u64;
    let r = (x >> cc) & (((1u64 << kk) - 1) as u64);
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_pos(c);
    if c + k < 64 {
        let ck = (cc + kk) as u64;
        let z = x & (((1u64 << ck) - 1) as u64);
        assert(r == z >> cc) by (bit_vector)
            requires
                r == (x >> cc) & (((1u64 << kk) - 1) as u64),
                z == x & (((1u64 << ck) - 1) as u64),
                ck == cc + kk,
                ck < 64,
        ;
        lemma_mask(x, c + k);
        lemma_u64_shr_is_div(z, cc);
    } else {
        assert(r == x >> cc) by (bit_vector)
            requires
                r == (x >> cc) & (((1u64 << kk) - 1) as u64),
                cc + kk == 64,
                kk < 64,
        ;
        assert(pow2(c + k) == 0x1_0000_0000_0000_0000);
        lemma_small_mod(x as nat, pow2(64));
        lemma_u64_shr_is_div(x, cc);
    }
}

/// The bits of the entropy-coded segment that starts at `p0`.
#[derive(Clone, Copy)]
pub struct BitReader {
    /// The next input byte.
    pub pos: usize,
    /// The bits read from the input and not yet used, in the low `cnt`
    /// bits, the next one highest. The bits above them are used ones that
    /// have not been shifted out yet, and mean nothing.
    pub buf: u64,
    pub cnt: u32,
    /// How many of them are zeros supplied after the end of the segment.
    pub pad: u32,
    /// Set, at a refill, once a bit past the end of the segment has been
    /// used; between refills `cnt < pad` says the same (see `over`).
    pub stk: bool,
    /// Where the segment starts, and how many of its bits have been used.
    pub p0: Ghost<int>,
    pub n: Ghost<int>,
}

impl BitReader {
    /// The segment's bytes.
    pub open spec fn e(&self, d: Seq<u8>) -> Seq<u8> {
        ecs(d, self.p0@)
    }

    /// A bit past the end of the segment has been used. Reading bits does
    /// not have to keep track: the padding is at the bottom of the buffer,
    /// so one has been used exactly when fewer bits are left than there are
    /// padding bits.
    pub open spec fn over(&self) -> bool {
        self.stk || self.cnt < self.pad
    }

    #[inline(always)]
    pub fn is_over(&self) -> (r: bool)
        ensures
            r == self.over(),
    {
        self.stk || self.cnt < self.pad
    }

    pub open spec fn wf(&self, d: Seq<u8>) -> bool {
        let e = ecs(d, self.p0@);
        let end = 8 * e.len();
        let n = self.n@;
        let cnt = self.cnt as int;
        &&& len_ok(d)
        &&& pos_ok(d, self.p0@)
        &&& self.pos <= d.len() || self.pos <= self.p0@ + 1
        &&& self.pos >= self.p0@
        &&& cnt <= 64
        &&& n >= 0
        &&& self.buf as int % (pow2(cnt as nat) as int) == ebits(e, n, cnt as nat)
        &&& marker_after(d, self.pos as int) == marker_after(d, self.p0@)
        &&& (n + cnt) % 8 == 0
        &&& self.over() == (n > end)
        &&& if self.pad > 0 || self.stk {
            &&& ecs(d, self.pos as int).len() == 0
            &&& n + cnt >= end
            &&& !self.stk ==> self.pad as int == n + cnt - end
        } else {
            &&& n + cnt <= end
            &&& ecs(d, self.pos as int) == e.skip((n + cnt) / 8)
        }
    }

    pub fn new(pos: usize, Ghost(d): Ghost<Seq<u8>>) -> (r: BitReader)
        requires
            len_ok(d),
            pos_ok(d, pos as int),
        ensures
            r.wf(d),
            r.p0@ == pos,
            r.n@ == 0,
            r.pos == pos,
            !r.over(),
    {
        proof {
            assert(ecs(d, pos as int).skip(0) =~= ecs(d, pos as int));
            lemma2_to64();
        }
        BitReader { pos, buf: 0, cnt: 0, pad: 0, stk: false, p0: Ghost(pos as int), n: Ghost(0) }
    }

    /// The reader after taking in one more data byte `b`.
    pub open spec fn fed(self, b: u8) -> BitReader {
        BitReader {
            pos: (self.pos + 1) as usize,
            buf: (self.buf << 8) | b as u64,
            cnt: (self.cnt + 8) as u32,
            pad: self.pad,
            stk: self.stk,
            p0: self.p0,
            n: self.n,
        }
    }

    /// Taking in a byte that is not `0xFF` keeps the reader well formed.
    pub proof fn lemma_feed(self, d: Seq<u8>, b: u8)
        requires
            self.wf(d),
            self.cnt <= 56,
            self.pos < d.len(),
            d[self.pos as int] == b,
            b != 0xFF,
        ensures
            self.fed(b).wf(d),
            self.fed(b).pad == 0 && !self.fed(b).over(),
    {
        let e = self.e(d);
        let n = self.n@;
        let cnt = self.cnt as int;
        let j = (n + cnt) / 8;
        let pos0 = self.pos as int;
        let ended = self.pad > 0 || self.stk;
        lemma_ecs_step(d, pos0);
        assert(byte(d, pos0) == b);
        assert(ecs(d, pos0).len() >= 1);
        assert(!ended);
        assert(n + cnt == 8 * j);
        lemma_ebits_byte(e, j);
        let rest = ecs(d, pos0 + 1);
        assert(e.skip(j) == seq![b] + rest);
        assert(e.skip(j).len() == rest.len() + 1);
        assert(e.skip(j)[0] == b);
        assert(e[j] == b);
        assert((seq![b] + rest).skip(1) =~= rest);
        assert(e.skip(j).skip(1) =~= e.skip(j + 1));
        assert(rest =~= e.skip(j + 1));
        assert(ebits(e, n + cnt, 8) == b as int);
        lemma_ebits_split(e, n, cnt as nat, 8);
        lemma_ebits_bound(e, n, cnt as nat);
        lemma2_to64();
        lemma2_to64_rest();
        assert(pow2(cnt as nat) <= pow2(56)) by {
            if cnt < 56 {
                lemma_pow2_strictly_increases(cnt as nat, 56);
            }
        }
        assert((cnt + 8) as nat == cnt as nat + 8);
        assert((n + cnt + 8) / 8 == j + 1);
        lemma_shift_in(self.buf, cnt as nat, b);
    }

    /// Four bytes at once, when there is room for them and none of them
    /// needs a closer look. Returns false, having done nothing, otherwise.
    #[inline(always)]
    pub fn fast4(&mut self, data: &[u8]) -> (ok: bool)
        requires
            old(self).wf(data@),
        ensures
            final(self).wf(data@),
            final(self).p0 == old(self).p0,
            final(self).n == old(self).n,
            final(self).over() == old(self).over(),
            ok ==> final(self).cnt >= 32,
            !ok ==> *final(self) == *old(self),
    {
        // Four bytes at once when none of them needs a closer look.
        let n = data.len();
        if self.cnt <= 32 && self.pos < n && n - self.pos >= 4 {
            let b0 = sget(data, self.pos);
            let b1 = sget(data, self.pos + 1);
            let b2 = sget(data, self.pos + 2);
            let b3 = sget(data, self.pos + 3);
            // One test for all four: a byte of `!w4` is zero exactly when
            // that byte of `w4` is 0xFF, and this is the usual test for a
            // word with a zero byte.
            let w4: u32 = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
            let x4 = !w4;
            let d4 = x4.wrapping_sub(0x0101_0101);
            let z = d4 & w4 & 0x8080_8080;
            if z == 0 {
                proof {
                    let t = (x4 as u64 + 0x1_0000_0000u64 - 0x0101_0101u64) as u64;
                    assert(t & 0xffff_ffffu64 == t % 0x1_0000_0000u64) by (bit_vector);
                    assert(d4 as u64 == t & 0xffff_ffffu64);
                    assert(b0 != 0xFF && b1 != 0xFF && b2 != 0xFF && b3 != 0xFF) by (bit_vector)
                        requires
                            w4 == ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32),
                            x4 == !w4,
                            t == (x4 as u64 + 0x1_0000_0000u64 - 0x0101_0101u64) as u64,
                            d4 as u64 == t & 0xffff_ffffu64,
                            d4 & w4 & 0x8080_8080u32 == 0,
                    ;
                }
                let ghost s0 = *self;
                let ghost s1 = s0.fed(b0);
                let ghost s2 = s1.fed(b1);
                let ghost s3 = s2.fed(b2);
                let ghost s4 = s3.fed(b3);
                let w = w4 as u64;
                assert(w == ((b0 as u64) << 24) | ((b1 as u64) << 16) | ((b2 as u64) << 8) | (b3 as u64)) by (bit_vector)
                    requires
                        w == w4 as u64,
                        w4 == ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32),
                ;
                proof {
                    s0.lemma_feed(data@, b0);
                    s1.lemma_feed(data@, b1);
                    s2.lemma_feed(data@, b2);
                    s3.lemma_feed(data@, b3);
                    let x = s0.buf;
                    assert(((x << 32) | w) == (((((((x << 8) | b0 as u64) << 8) | b1 as u64) << 8) | b2 as u64) << 8)
                        | b3 as u64) by (bit_vector)
                        requires
                            w == ((b0 as u64) << 24) | ((b1 as u64) << 16) | ((b2 as u64) << 8) | (b3 as u64),
                    ;
                }
                self.buf = (self.buf << 32) | w;
                self.cnt += 32;
                self.pos += 4;
                proof {
                    assert(*self == s4);
                }
                return true;
            }
        }
        false
    }

    /// At least 32 bits in the buffer: `fast4` inline, the general case out
    /// of line and on a copy, so that a caller's reader can stay in
    /// registers.
    #[inline(always)]
    pub fn refill_i(&mut self, data: &[u8])
        requires
            old(self).wf(data@),
        ensures
            final(self).wf(data@),
            final(self).cnt >= 32,
            final(self).p0 == old(self).p0,
            final(self).n == old(self).n,
            final(self).over() == old(self).over(),
    {
        if !self.fast4(data) {
            let mut t = *self;
            t.refill(data);
            *self = t;
        }
    }

    #[inline(never)]
    pub fn refill(&mut self, data: &[u8])
        requires
            old(self).wf(data@),
        ensures
            final(self).wf(data@),
            final(self).cnt >= 32,
            final(self).p0 == old(self).p0,
            final(self).n == old(self).n,
            final(self).over() == old(self).over(),
    {
        if self.fast4(data) {
            return;
        }
        while self.cnt <= 56
            invariant
                self.wf(data@),
                self.p0 == old(self).p0,
                self.n == old(self).n,
                self.over() == old(self).over(),
            decreases 64 - self.cnt,
        {
            let ghost d = data@;
            let ghost e = self.e(d);
            let ghost n = self.n@;
            let ghost cnt = self.cnt as int;
            let ghost j = (n + cnt) / 8;
            let ghost pos0 = self.pos as int;
            let ghost ended = self.pad > 0 || self.stk;
            let c = rd(data, self.pos);
            let mut b: u8 = 0;
            let mut is_data = false;
            proof {
                lemma_ecs_step(d, pos0);
                lemma_skip_ff(d, pos0 + 1);
            }
            if c != 0xFF {
                b = c;
                is_data = true;
                self.pos += 1;
            } else {
                let q = skip_ff_x(data, self.pos + 1);
                if rd(data, q) == 0 {
                    b = 0xFF;
                    is_data = true;
                    self.pos = q + 1;
                }
            }
            proof {
                // The byte loaded is the next eight bits of the segment.
                assert(n + cnt == 8 * j);
                lemma_ebits_byte(e, j);
                if is_data {
                    assert(!ended);
                    let rest = ecs(d, self.pos as int);
                    assert(e.skip(j) == seq![b] + rest);
                    assert(e.skip(j).len() == rest.len() + 1);
                    assert(e.skip(j)[0] == b);
                    assert(e[j] == b);
                    assert((seq![b] + rest).skip(1) =~= rest);
                    assert(e.skip(j).skip(1) =~= e.skip(j + 1));
                    assert(rest =~= e.skip(j + 1));
                } else {
                    assert(ecs(d, pos0).len() == 0);
                    if !ended {
                        assert(e.skip(j).len() == 0);
                    }
                    assert(j >= e.len());
                }
                assert(ebits(e, n + cnt, 8) == b as int);
                lemma_ebits_split(e, n, cnt as nat, 8);
                lemma_ebits_bound(e, n, cnt as nat);
                lemma2_to64();
                lemma2_to64_rest();
                lemma_shift_in(self.buf, cnt as nat, b);
                assert((cnt + 8) as nat == cnt as nat + 8);
            }
            if !is_data && !self.stk {
                // Padding. If some of it has been used already, say so
                // for good; `pad` then stops counting, and cannot overflow.
                if self.cnt < self.pad {
                    self.stk = true;
                } else {
                    self.pad += 8;
                }
            }
            self.buf = (self.buf << 8) | b as u64;
            self.cnt += 8;
            proof {
                assert((n + cnt + 8) / 8 == j + 1);
            }
        }
    }

    /// The next 16 bits, without using them.
    #[inline]
    pub fn peek16(&mut self, data: &[u8]) -> (r: u32)
        requires
            old(self).wf(data@),
        ensures
            final(self).wf(data@),
            final(self).p0 == old(self).p0,
            final(self).n == old(self).n,
            final(self).over() == old(self).over(),
            final(self).cnt >= 16,
            r as int == ebits(old(self).e(data@), old(self).n@, 16),
    {
        if self.cnt < 16 {
            self.refill(data);
        }
        self.peek16_have(Ghost(data))
    }

    /// The next 16 bits, without using them, leaving at least 32 in the
    /// buffer: enough for a short code and the value that follows it.
    #[inline(always)]
    pub fn peek16w(&mut self, data: &[u8]) -> (r: u32)
        requires
            old(self).wf(data@),
        ensures
            final(self).wf(data@),
            final(self).p0 == old(self).p0,
            final(self).n == old(self).n,
            final(self).over() == old(self).over(),
            final(self).cnt >= 32,
            r as int == ebits(old(self).e(data@), old(self).n@, 16),
    {
        if self.cnt < 32 {
            self.refill_i(data);
        }
        self.peek16_have(Ghost(data))
    }

    /// The next 16 bits of a buffer that holds them.
    #[inline(always)]
    pub fn peek16_have(&self, Ghost(data): Ghost<&[u8]>) -> (r: u32)
        requires
            self.wf(data@),
            self.cnt >= 16,
        ensures
            r as int == ebits(self.e(data@), self.n@, 16),
    {
        let c2 = self.cnt - 16;
        proof {
            self.lemma_top(data@, 16);
            lemma_field(self.buf, c2 as nat, 16);
            assert((c2 as nat + 16) as nat == self.cnt as nat);
            assert(((1u64 << 16) - 1) as u64 == 0xffffu64) by (bit_vector);
            lemma_ebits_bound(self.e(data@), self.n@, 16);
            lemma2_to64();
        }
        ((self.buf >> c2) & 0xffff) as u32
    }

    /// The next `k` bits, `1 <= k <= 16`.
    #[inline]
    pub fn get(&mut self, data: &[u8], k: u32) -> (r: u32)
        requires
            old(self).wf(data@),
            1 <= k <= 16,
        ensures
            final(self).wf(data@),
            final(self).p0 == old(self).p0,
            final(self).n@ == old(self).n@ + k,
            r as int == ebits(old(self).e(data@), old(self).n@, k as nat),
            old(self).over() ==> final(self).over(),
    {
        if self.cnt < k {
            self.refill(data);
        }
        self.get_have(Ghost(data), k)
    }

    /// `get` for a reader that its caller keeps in registers: the refill
    /// is `refill_i`.
    #[inline(always)]
    pub fn get_r(&mut self, data: &[u8], k: u32) -> (r: u32)
        requires
            old(self).wf(data@),
            1 <= k <= 16,
        ensures
            final(self).wf(data@),
            final(self).p0 == old(self).p0,
            final(self).n@ == old(self).n@ + k,
            r as int == ebits(old(self).e(data@), old(self).n@, k as nat),
            old(self).over() ==> final(self).over(),
    {
        if self.cnt < k {
            self.refill_i(data);
        }
        self.get_have(Ghost(data), k)
    }

    /// The next `k` bits of a buffer that holds them, `1 <= k <= 24`.
    #[inline(always)]
    pub fn get_have(&mut self, Ghost(data): Ghost<&[u8]>, k: u32) -> (r: u32)
        requires
            old(self).wf(data@),
            1 <= k <= 24,
            k <= old(self).cnt,
        ensures
            final(self).wf(data@),
            final(self).p0 == old(self).p0,
            final(self).n@ == old(self).n@ + k,
            r as int == ebits(old(self).e(data@), old(self).n@, k as nat),
            old(self).over() ==> final(self).over(),
    {
        let ghost s0 = *self;
        self.cnt -= k;
        let x = self.buf;
        let c = self.cnt;
        assert((1u64 << k) >= 1 && ((x >> c) & (((1u64 << k) - 1) as u64)) <= 0xffff_ffff) by (bit_vector)
            requires
                k <= 24,
        ;
        let v = ((self.buf >> self.cnt) & ((1u64 << k) - 1)) as u32;
        proof {
            s0.lemma_top(data@, k as nat);
            s0.lemma_adv(data@, k as nat);
            lemma_field(self.buf, self.cnt as nat, k as nat);
            assert((self.cnt as nat + k as nat) as nat == s0.cnt as nat);
            lemma_ebits_bound(s0.e(data@), s0.n@, k as nat);
            lemma_pow2_strictly_increases(k as nat, 32);
            lemma2_to64();
            lemma_mask(0, k as nat);
            self.n = Ghost(s0.n@ + k);
            assert(*self == s0.adv(k as nat));
        }
        v
    }

    /// The `s` bits that follow the next `l`, using up all of them: a
    /// Huffman code and the value after it in one step. `s` may be 0.
    #[inline(always)]
    pub fn get2_have(&mut self, Ghost(data): Ghost<&[u8]>, l: u32, s: u32) -> (r: u32)
        requires
            old(self).wf(data@),
            1 <= l,
            s <= 16,
            l + s <= 32,
            l + s <= old(self).cnt,
        ensures
            final(self).wf(data@),
            final(self).p0 == old(self).p0,
            final(self).n@ == old(self).n@ + l + s,
            r as int == ebits(old(self).e(data@), old(self).n@ + l, s as nat),
            old(self).over() ==> final(self).over(),
    {
        let ghost s0 = *self;
        let ghost s1 = s0.adv(l as nat);
        self.cnt -= l + s;
        let x = self.buf;
        let c = self.cnt;
        assert((1u64 << s) >= 1 && ((x >> c) & (((1u64 << s) - 1) as u64)) <= 0xffff_ffff) by (bit_vector)
            requires
                s <= 24,
        ;
        let v = ((self.buf >> self.cnt) & ((1u64 << s) - 1)) as u32;
        proof {
            s0.lemma_adv(data@, l as nat);
            s1.lemma_top(data@, s as nat);
            s1.lemma_adv(data@, s as nat);
            lemma_field(self.buf, self.cnt as nat, s as nat);
            assert((self.cnt as nat + s as nat) as nat == s1.cnt as nat);
            lemma_ebits_bound(s1.e(data@), s1.n@, s as nat);
            lemma_pow2_strictly_increases(s as nat, 32);
            lemma2_to64();
            lemma_mask(0, s as nat);
            self.n = Ghost(s0.n@ + l + s);
            assert(*self == s1.adv(s as nat));
        }
        v
    }

    /// The reader after `k` of its bits are used.
    pub open spec fn adv(self, k: nat) -> BitReader {
        BitReader { cnt: (self.cnt - k) as u32, n: Ghost(self.n@ + k), ..self }
    }

    /// Using bits keeps the reader well formed: nothing in the buffer has
    /// to change.
    pub proof fn lemma_adv(self, d: Seq<u8>, k: nat)
        requires
            self.wf(d),
            k <= self.cnt,
        ensures
            self.adv(k).wf(d),
            self.adv(k).e(d) == self.e(d),
            self.over() ==> self.adv(k).over(),
    {
        let e = self.e(d);
        let n = self.n@;
        let c2 = (self.cnt - k) as nat;
        let m = pow2(c2) as int;
        let hi = ebits(e, n, k);
        let lo = ebits(e, n + k, c2);
        let x = self.buf as int;
        lemma_ebits_split(e, n, k, c2);
        assert(k + c2 == self.cnt as nat);
        lemma_ebits_bound(e, n + k, c2);
        lemma_ebits_bound(e, n, k);
        lemma_pow2_pos(c2);
        lemma_pow2_pos(k);
        lemma_pow2_adds(c2, k);
        lemma_mod_mod(x, m, pow2(k) as int);
        assert(pow2(self.cnt as nat) == m * pow2(k));
        assert(x % (pow2(self.cnt as nat) as int) == hi * m + lo);
        lemma_fundamental_div_mod_converse(hi * m + lo, m, hi, lo);
        assert(x % m == lo);
    }

    /// The next `k` bits are the top `k` of the buffer's `cnt`.
    pub proof fn lemma_top(self, d: Seq<u8>, k: nat)
        requires
            self.wf(d),
            k <= self.cnt,
        ensures
            (self.buf as int % (pow2(self.cnt as nat) as int)) / (pow2((self.cnt - k) as nat) as int) == ebits(
                self.e(d),
                self.n@,
                k,
            ),
    {
        let e = self.e(d);
        let n = self.n@;
        let c2 = (self.cnt - k) as nat;
        let m = pow2(c2) as int;
        let hi = ebits(e, n, k);
        let lo = ebits(e, n + k, c2);
        lemma_ebits_split(e, n, k, c2);
        assert(k + c2 == self.cnt as nat);
        lemma_ebits_bound(e, n + k, c2);
        lemma_ebits_bound(e, n, k);
        lemma_pow2_pos(c2);
        lemma_fundamental_div_mod_converse(hi * m + lo, m, hi, lo);
    }
}

} // verus!
