//! The VP8 boolean (arithmetic) decoder, RFC 6386 section 7, in the form
//! libwebp 1.6.0 uses (`src/utils/bit_reader*`): a 56-bit window refilled 7
//! bytes at a time while 8 remain, then a byte at a time; the input is
//! exhausted (`eof`) the first time a read needs a bit past the end, after
//! which 8 zero bits are supplied.
use crate::vp8spec::*;
use verilith_core::prims::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
pub struct BoolReader {
    /// Unread bits; the top 8 above `bits` are the comparison window.
    pub value: u64,
    /// The range after the last decision, in `[1, 255]`, not yet normalized
    /// (`bits` already counts its normalization shift).
    pub range: u32,
    /// `range.leading_zeros()`, kept so that the next step's shift does not
    /// wait on a count.
    pub sh: u32,
    /// Bits in `value` below the window, or negative when it needs a refill.
    pub bits: i32,
    /// The next byte to load.
    pub pos: usize,
    /// One past the last byte of the partition.
    pub end: usize,
    /// A read went past the end of the partition.
    pub eof: bool,
}

/// How far a range of `r` (`1 <= r <= 255`) is shifted to bring it back to
/// `[128, 255]`: its leading zeros as a byte.
pub open spec fn nshift(r: u32) -> u32 {
    if r >= 128 {
        0
    } else if r >= 64 {
        1
    } else if r >= 32 {
        2
    } else if r >= 16 {
        3
    } else if r >= 8 {
        4
    } else if r >= 4 {
        5
    } else if r >= 2 {
        6
    } else {
        7
    }
}

/// The range `r` (`1 <= r <= 255`) normalized: shifted into `[128, 255]`,
/// which is the range the RFC's decoder holds between reads.
pub open spec fn nrange(r: u32) -> int {
    if r >= 128 {
        r as int
    } else if r >= 64 {
        2 * r
    } else if r >= 32 {
        4 * r
    } else if r >= 16 {
        8 * r
    } else if r >= 8 {
        16 * r
    } else if r >= 4 {
        32 * r
    } else if r >= 2 {
        64 * r
    } else {
        128 * r
    }
}

/// `leading_zeros` of a range is 24 more than its normalization shift, and
/// shifting by it brings the range to the top byte.
pub proof fn lemma_lz(r: u32)
    requires
        1 <= r <= 255,
    ensures
        r.leading_zeros() == 24 + nshift(r),
        nshift(r) <= 7,
        128 <= nrange(r) <= 255,
        nrange(r) == r * pow2(nshift(r) as nat),
        (r << r.leading_zeros()) >> 24u32 == nrange(r),
        r <= 254 ==> nrange(r) <= 254,
{
    vstd::std_specs::bits::axiom_u32_leading_zeros(r);
    let z = r.leading_zeros();
    assert(z < 32);
    assert((r >> sub(31u32, z)) & 1u32 != 0u32);
    assert(r >> sub(32u32, z) == 0u32);
    assert(1 <= r <= 255 && z < 32 && (r >> sub(31u32, z)) & 1u32 != 0u32 && r >> sub(32u32, z) == 0u32 ==> z == add(
        24u32,
        if r >= 128 {
            0u32
        } else if r >= 64 {
            1u32
        } else if r >= 32 {
            2u32
        } else if r >= 16 {
            3u32
        } else if r >= 8 {
            4u32
        } else if r >= 4 {
            5u32
        } else if r >= 2 {
            6u32
        } else {
            7u32
        },
    )) by (bit_vector);
    assert(1 <= r <= 255 ==> (r << (if r >= 128 {
        24u32
    } else if r >= 64 {
        25u32
    } else if r >= 32 {
        26u32
    } else if r >= 16 {
        27u32
    } else if r >= 8 {
        28u32
    } else if r >= 4 {
        29u32
    } else if r >= 2 {
        30u32
    } else {
        31u32
    })) >> 24u32 == (if r >= 128 {
        r
    } else if r >= 64 {
        mul(2u32, r)
    } else if r >= 32 {
        mul(4u32, r)
    } else if r >= 16 {
        mul(8u32, r)
    } else if r >= 8 {
        mul(16u32, r)
    } else if r >= 4 {
        mul(32u32, r)
    } else if r >= 2 {
        mul(64u32, r)
    } else {
        mul(128u32, r)
    })) by (bit_vector);
    lemma2_to64();
    assert(pow2(0) == 1 && pow2(1) == 2 && pow2(2) == 4 && pow2(3) == 8 && pow2(4) == 16 && pow2(5) == 32 && pow2(6)
        == 64 && pow2(7) == 128);
    let k = nshift(r) as nat;
    assert(k == 0 || k == 1 || k == 2 || k == 3 || k == 4 || k == 5 || k == 6 || k == 7);
}

/// The lazily normalized split: with `s` the normalization shift of the
/// range `r`, `((r * prob) << s + 256 - prob) >> 8` is the RFC's
/// `1 + (((r << s) - 1) * prob >> 8)`, computed 24 bits up.
pub proof fn lemma_lazy_split(r: u32, prob: u8)
    requires
        1 <= r <= 255,
    ensures
        r * prob <= 65025,
        (((r * prob) as u64) << (r.leading_zeros() as u64)) <= 0x7fff_ffff_ffff,
        (((256 - prob) as u64) << 24u32) <= 0x1_0000_0000,
        (((((r * prob) as u64) << (r.leading_zeros() as u64)) + (((256 - prob) as u64) << 24u32)) as u64 >> 32u32)
            == bool_split(nrange(r), prob as int),
        1 <= bool_split(nrange(r), prob as int) < nrange(r),
{
    lemma_lz(r);
    lemma2_to64();
    lemma2_to64_rest();
    let s = nshift(r) as nat;
    let lz = r.leading_zeros();
    let ps = pow2(s) as int;
    let nr = nrange(r);
    assert(r * prob <= 65025) by (nonlinear_arith)
        requires
            r <= 255,
            prob <= 255,
    ;
    let m = (r * prob) as u64;
    lemma_pow2_adds(24, s);
    assert(pow2(lz as nat) == 16777216 * ps);
    assert(1 <= ps <= 128);
    assert(m * ps == nr * prob) by (nonlinear_arith)
        requires
            m == r * prob,
            nr == r * ps,
    ;
    assert(m * (16777216 * ps) == 16777216 * (m * ps)) by (nonlinear_arith);
    assert(nr * prob <= 65025) by (nonlinear_arith)
        requires
            0 <= nr <= 255,
            prob <= 255,
    ;
    assert(m * pow2(lz as nat) <= 16777216 * 65025);
    lemma_u64_shl_is_mul(m, lz as u64);
    let k = (256 - prob) as u64;
    lemma_u64_shl_is_mul(k, 24);
    let x = ((m << (lz as u64)) + (k << 24u32)) as u64;
    let y = nr * prob + 256 - prob;
    assert(x == 16777216 * y);
    lemma_u64_shr_is_div(x, 32);
    assert((x >> 32u32) == y / 256);
    assert((nr - 1) * prob == nr * prob - prob) by (nonlinear_arith);
    lemma_split(nr, prob as int);
}

/// `2^i`.
pub open spec fn p2(i: nat) -> int
    decreases i,
{
    if i == 0 {
        1
    } else {
        2 * p2((i - 1) as nat)
    }
}

/// `2^s` for small `s`.
pub open spec fn pow2_32(s: u32) -> u32 {
    if s == 0 {
        1
    } else if s == 1 {
        2
    } else if s == 2 {
        4
    } else if s == 3 {
        8
    } else if s == 4 {
        16
    } else if s == 5 {
        32
    } else if s == 6 {
        64
    } else {
        128
    }
}

/// `(v >> p) & 0xffff_ffff` above `s` means `v` holds `(s + 1) << p`.
proof fn lemma_sub_ok(v: u64, p: u64, s: u64)
    requires
        p <= 55,
        s < 256,
        ((v >> p) & 0xffff_ffffu64) > s,
    ensures
        v >= (((s + 1) as u64) << p),
{
    assert(p <= 55 && s < 256 && ((v >> p) & 0xffff_ffffu64) > s ==> v >= (((s + 1) as u64) << p)) by (bit_vector);
}

/// `p2` grows.
pub proof fn lemma_p2_mono(i: nat, j: nat)
    requires
        i <= j,
    ensures
        1 <= p2(i) <= p2(j),
    decreases j,
{
    if j > 0 {
        if i < j {
            lemma_p2_mono(i, (j - 1) as nat);
        } else {
            lemma_p2_mono(0, (j - 1) as nat);
        }
    }
}

/// The bytes of the partition a reader that started at `start` reads.
pub open spec fn part(buf: Seq<u8>, start: int, end: int) -> Seq<u8> {
    buf.subrange(start, end)
}

/// `pow2` up to the widest window.
proof fn lemma_pow2_le55(n: nat)
    requires
        n <= 55,
    ensures
        1 <= pow2(n) <= 0x80_0000_0000_0000,
{
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_pos(n);
    if n < 55 {
        lemma_pow2_strictly_increases(n, 55);
    }
}

/// The window of a reader with a loaded window is the spec's value.
proof fn lemma_window_value(r: BoolReader, buf: Seq<u8>, start: int, s: BoolState)
    requires
        r.inv(buf.len()),
        r.rel(buf, start, s),
        r.bits >= 0,
    ensures
        ((r.value >> (r.bits as u64)) & 0xffff_ffffu64) == s.value,
        0 <= s.value < 255,
        r.value == s.value * pow2(r.bits as nat) + stream_bits(part(buf, start, r.end as int), s.pos, r.bits as nat),
        stream_bits(part(buf, start, r.end as int), s.pos, r.bits as nat) < pow2(r.bits as nat),
{
    let data = part(buf, start, r.end as int);
    let n = r.bits as nat;
    let p = pow2(n) as int;
    let low = stream_bits(data, s.pos, n) as int;
    lemma_bits_bound(data, s.pos, n);
    lemma_pow2_le55(n);
    lemma_u64_shr_is_div(r.value, r.bits as u64);
    lemma_fundamental_div_mod_converse(r.value as int, p, s.value, low);
    let w = r.value >> (r.bits as u64);
    assert(w == s.value);
    assert(w < 256 ==> w & 0xffff_ffffu64 == w) by (bit_vector);
}

/// One `get_bit`, from a loaded window, is one `read_bool` of the spec.
proof fn lemma_get_bit(
    pre: BoolReader,
    post: BoolReader,
    buf: Seq<u8>,
    start: int,
    s: BoolState,
    prob: u8,
    split: u32,
    vw: u32,
    r: u32,
)
    requires
        pre.inv(buf.len()),
        pre.rel(buf, start, s),
        pre.bits >= 0,
        split == bool_split(nrange(pre.range), prob as int),
        vw == ((pre.value >> (pre.bits as u64)) & 0xffff_ffffu64),
        vw >= split ==> post.value == pre.value - ((split as u64) << (pre.bits as u64)) && r == nrange(pre.range)
            - split,
        vw < split ==> post.value == pre.value && r == split,
        post.range == r,
        post.bits == pre.bits - nshift(r),
        post.pos == pre.pos,
        post.end == pre.end,
        post.eof == pre.eof,
    ensures
        post.rel(buf, start, bool_next(part(buf, start, pre.end as int), s, prob as int)),
        (vw >= split) == bool_bit(s, prob as int),
        1 <= post.range <= 254,
{
    let data = part(buf, start, pre.end as int);
    let n = pre.bits as nat;
    let p = pow2(n) as int;
    let low = stream_bits(data, s.pos, n) as int;
    lemma_window_value(pre, buf, start, s);
    lemma_pow2_le55(n);
    lemma2_to64();
    let sp = bool_split(s.range, prob as int);
    assert(sp == split);
    lemma_split(s.range, prob as int);
    let t = bool_take(s, prob as int);
    lemma_take_wf(s, prob as int);
    // The subtraction.
    let k = split as u64;
    assert(k * p <= 256 * 0x80_0000_0000_0000) by (nonlinear_arith)
        requires
            0 <= k <= 256,
            0 <= p <= 0x80_0000_0000_0000,
    ;
    lemma_u64_shl_is_mul(k, pre.bits as u64);
    assert((s.value - sp) * p == s.value * p - sp * p) by (nonlinear_arith);
    assert(post.value == t.value * p + low);
    assert(r == t.range);
    // The renormalization.
    lemma_lz(r);
    let m = nshift(r) as nat;
    lemma_norm(data, t, m);
    let q = bool_next(data, s, prob as int);
    assert(q.range == nrange(r));
    assert(q.value == t.value * pow2(m) + stream_bits(data, t.pos, m));
    assert(q.pos == s.pos + m);
    lemma_bits_bound(data, t.pos, m);
    assert(q.value < q.range) by {
        let pm = pow2(m) as int;
        assert(t.value * pm + pm <= t.range * pm) by (nonlinear_arith)
            requires
                t.value + 1 <= t.range,
                pm >= 0,
        ;
    }
    if n >= m {
        lemma_window(data, t.value, s.pos, m, n);
    } else {
        lemma_window(data, t.value, s.pos, n, m);
    }
}

/// A 64-bit word with its bytes reversed.
pub open spec fn bswap_spec(x: u64) -> u64 {
    (x << 56u32) | ((x & 0xff00u64) << 40u32) | ((x & 0xff_0000u64) << 24u32) | ((x & 0xff00_0000u64) << 8u32) | ((x
        >> 8u32) & 0xff00_0000u64) | ((x >> 24u32) & 0xff_0000u64) | ((x >> 40u32) & 0xff00u64) | (x >> 56u32)
}

/// `swap_bytes`, spelled out so that it has a meaning here; the compiler
/// turns this back into the single byte-swap instruction.
#[inline(always)]
fn bswap64(x: u64) -> (r: u64)
    ensures
        r == bswap_spec(x),
{
    (x << 56u32) | ((x & 0xff00u64) << 40u32) | ((x & 0xff_0000u64) << 24u32) | ((x & 0xff00_0000u64) << 8u32) | ((x
        >> 8u32) & 0xff00_0000u64) | ((x >> 24u32) & 0xff_0000u64) | ((x >> 40u32) & 0xff00u64) | (x >> 56u32)
}

/// The top 7 bytes of a byte-swapped little-endian load are the first 7
/// bytes, big-endian.
proof fn lemma_be7(buf: Seq<u8>, p: int, w: u64)
    requires
        0 <= p,
        p + 8 <= buf.len(),
        w as nat == le_word(buf, p),
    ensures
        bswap_spec(w) >> 8u32 == (buf[p] as u64) << 48u32 | (buf[p + 1] as u64) << 40u32 | (buf[p + 2] as u64) << 32u32
            | (buf[p + 3] as u64) << 24u32 | (buf[p + 4] as u64) << 16u32 | (buf[p + 5] as u64) << 8u32 | (buf[p
            + 6] as u64),
{
    reveal_with_fuel(le_bytes, 9);
    let d0 = buf[p] as u64;
    let d1 = buf[p + 1] as u64;
    let d2 = buf[p + 2] as u64;
    let d3 = buf[p + 3] as u64;
    let d4 = buf[p + 4] as u64;
    let d5 = buf[p + 5] as u64;
    let d6 = buf[p + 6] as u64;
    let d7 = buf[p + 7] as u64;
    assert(w == d0 + 256 * (d1 + 256 * (d2 + 256 * (d3 + 256 * (d4 + 256 * (d5 + 256 * (d6 + 256 * d7)))))));
    assert(w == d0 + 256 * d1 + 65536 * d2 + 16777216 * d3 + 4294967296 * d4 + 1099511627776 * d5 + 281474976710656
        * d6 + 72057594037927936 * d7);
    assert(d0 < 256 && d1 < 256 && d2 < 256 && d3 < 256 && d4 < 256 && d5 < 256 && d6 < 256 && d7 < 256 && w == d0
        | d1 << 8u32 | d2 << 16u32 | d3 << 24u32 | d4 << 32u32 | d5 << 40u32 | d6 << 48u32 | d7 << 56u32 ==> ((w
        << 56u32) | ((w & 0xff00u64) << 40u32) | ((w & 0xff_0000u64) << 24u32) | ((w & 0xff00_0000u64) << 8u32) | ((w
        >> 8u32) & 0xff00_0000u64) | ((w >> 24u32) & 0xff_0000u64) | ((w >> 40u32) & 0xff00u64) | (w >> 56u32))
        >> 8u32 == d0 << 48u32 | d1 << 40u32 | d2 << 32u32 | d3 << 24u32 | d4 << 16u32 | d5 << 8u32 | d6)
        by (bit_vector);
    assert(d0 < 256 && d1 < 256 && d2 < 256 && d3 < 256 && d4 < 256 && d5 < 256 && d6 < 256 && d7 < 256 ==> d0 | d1
        << 8u32 | d2 << 16u32 | d3 << 24u32 | d4 << 32u32 | d5 << 40u32 | d6 << 48u32 | d7 << 56u32 == d0 + 256 * d1
        + 65536 * d2 + 16777216 * d3 + 4294967296 * d4 + 1099511627776 * d5 + 281474976710656 * d6 + 72057594037927936
        * d7) by (bit_vector);
}

/// The sign mask of `get_signed`: all ones exactly when the window is at
/// or past the split (for a window inside the range), and what it does to
/// the range and the result.
proof fn lemma_signed_mask(rn: u32, value: u32, v: i32)
    requires
        128 <= rn <= 255,
        -0x7fff_ffff <= v,
    ensures
        ({
            let split = (rn + 1) as u32 >> 1u32;
            let mask = ((split as i32).wrapping_sub(1).wrapping_sub(value as i32) >> 31u32) as u32;
            let res = ((v as u32 ^ mask).wrapping_sub(mask)) as i32;
            &&& mask == 0 || mask == 0xffff_ffffu32
            &&& 64 <= split <= 128
            &&& split == 1 + ((rn - 1) * 128) / 256
            &&& mask & rn & 1 <= 1
            &&& split & mask == (if mask == 0 {
                0
            } else {
                split
            })
            &&& value < 256 ==> (mask != 0 <==> value >= split)
            &&& mask != 0 ==> split - (mask & rn & 1) == rn - split
            &&& mask == 0 ==> split - (mask & rn & 1) == split
            &&& rn <= 254 ==> 64 <= split - (mask & rn & 1) <= 127
            &&& res == (if mask != 0 {
                -v
            } else {
                v as int
            })
        }),
{
    let split = (rn + 1) as u32 >> 1u32;
    let d = (split as i32).wrapping_sub(1).wrapping_sub(value as i32);
    let mask = (d >> 31u32) as u32;
    assert(128 <= rn <= 255 ==> 64 <= (add(rn, 1) >> 1u32) <= 128 && (add(rn, 1) >> 1u32) == add(rn, 1) / 2 && sub(
        add(rn, 1) >> 1u32,
        rn & 1,
    ) == sub(rn, add(rn, 1) >> 1u32)) by (bit_vector);
    assert(rn & 1 <= 1) by (bit_vector);
    assert(0u32 & rn & 1 == 0 && 0xffff_ffffu32 & rn & 1 == rn & 1 && split & 0u32 == 0 && split & 0xffff_ffffu32
        == split) by (bit_vector);
    assert((d >> 31u32) as u32 == 0 || (d >> 31u32) as u32 == 0xffff_ffffu32) by (bit_vector);
    assert((d >> 31u32) as u32 != 0 <==> d < 0) by (bit_vector);
    if value < 256 {
        assert(d == split - 1 - value);
    }
    assert(((v as u32) ^ 0u32) as i32 == v) by (bit_vector);
    assert(v > -0x8000_0000i32 ==> sub((v as u32) ^ 0xffff_ffffu32, 0xffff_ffffu32) as i32 == -v) by (bit_vector);
    assert(((v as u32) ^ 0u32).wrapping_sub(0u32) == (v as u32) ^ 0u32);
    let a = (v as u32) ^ 0xffff_ffffu32;
    assert(sub(a, 0xffff_ffffu32) == (if a == 0xffff_ffffu32 {
        0u32
    } else {
        add(a, 1u32)
    })) by (bit_vector);
    assert(a.wrapping_sub(0xffff_ffffu32) == sub(a, 0xffff_ffffu32));
    let res = ((v as u32 ^ mask).wrapping_sub(mask)) as i32;
    assert(mask == 0 || mask == 0xffff_ffffu32);
    assert(64 <= split <= 128);
    assert(split == 1 + ((rn - 1) * 128) / 256);
    assert(value < 256 ==> (mask != 0 <==> value >= split));
    assert(mask != 0 ==> split - (mask & rn & 1) == rn - split);
    assert(mask == 0 ==> split - (mask & rn & 1) == split);
    assert(mask == 0 ==> res == v);
    assert(mask != 0 ==> res == -v);
}

impl BoolReader {
    /// The reader agrees with the RFC's decoder in state `s`, for a
    /// partition that began at `start`: the spec's range is this one
    /// normalized (`nrange`), and the window
    /// holds the spec's value followed by the stream bits loaded but not
    /// yet shifted in. (When `bits` is negative the spec is ahead by that
    /// many bits, which the next refill supplies.) It says nothing once a
    /// read has gone past the end of the partition.
    pub closed spec fn rel(&self, buf: Seq<u8>, start: int, s: BoolState) -> bool {
        let data = part(buf, start, self.end as int);
        let l = 8 * (self.pos - start);
        &&& 0 <= start <= self.pos
        &&& !self.eof
        &&& bool_wf(s)
        &&& s.range == nrange(self.range)
        &&& s.pos == l - self.bits
        &&& if self.bits >= 0 {
            self.value == s.value * pow2(self.bits as nat) + stream_bits(data, s.pos, self.bits as nat)
        } else {
            s.value == self.value * pow2((-self.bits) as nat) + stream_bits(data, l as nat, (-self.bits) as nat)
        }
    }

    /// The kept shift is the range's.
    pub closed spec fn sh_ok(&self) -> bool {
        self.sh == self.range.leading_zeros()
    }

    /// What every operation keeps, whatever the input: the reader stays
    /// in its partition, the range is a byte and not zero, and the bit count leaves
    /// room for a refill.
    pub open spec fn inv(&self, len: nat) -> bool {
        &&& self.pos <= self.end
        &&& self.end <= len
        &&& 1 <= self.range <= 255
        &&& self.sh_ok()
        &&& -8 <= self.bits <= 55
    }

    /// A reader over `buf[start..end]`.
    pub fn new(buf: &[u8], start: usize, end: usize) -> (br: BoolReader)
        requires
            start <= end <= buf@.len(),
        ensures
            br.end == end,
            br.inv(buf@.len()),
            !br.eof && bool_wf(bool_init(part(buf@, start as int, end as int))) ==> br.rel(
                buf@,
                start as int,
                bool_init(part(buf@, start as int, end as int)),
            ),
    {
        let mut br = BoolReader { value: 0, range: 255, sh: 24, bits: -8, pos: start, end, eof: false };
        proof {
            lemma_lz(255);
            lemma2_to64();
            let s0 = bool_init(part(buf@, start as int, end as int));
            if bool_wf(s0) {
                assert(0 * pow2(8) == 0);
                assert(8 * (br.pos - start) == 0);
                assert(s0.value == stream_bits(part(buf@, start as int, end as int), 0, 8));
                assert(br.rel(buf@, start as int, s0));
            }
        }
        br.load(buf);
        br
    }

    /// A refill of `nb` whole bytes keeps the reader on the spec's state.
    proof fn lemma_load(pre: BoolReader, post: BoolReader, buf: Seq<u8>, start: int, s: BoolState, nb: nat, b: u64)
        requires
            pre.inv(buf.len()),
            pre.bits < 0,
            pre.rel(buf, start, s),
            nb == 7 || nb == 1,
            pre.pos + nb <= pre.end,
            nb == 7 ==> b == (buf[pre.pos as int] as u64) << 48u32 | (buf[pre.pos + 1] as u64) << 40u32 | (buf[pre.pos
                + 2] as u64) << 32u32 | (buf[pre.pos + 3] as u64) << 24u32 | (buf[pre.pos + 4] as u64) << 16u32 | (
            buf[pre.pos + 5] as u64) << 8u32 | (buf[pre.pos + 6] as u64),
            nb == 7 ==> post.value == b | (pre.value << 56u32),
            nb == 1 ==> b == buf[pre.pos as int] as u64,
            nb == 1 ==> post.value == b | (pre.value << 8u32),
            post.pos == pre.pos + nb,
            post.bits == pre.bits + 8 * nb,
            post.range == pre.range,
            post.end == pre.end,
            post.eof == pre.eof,
        ensures
            post.rel(buf, start, s),
    {
        let data = part(buf, start, pre.end as int);
        let i = (pre.pos - start) as nat;
        let l = 8 * i;
        let k = (-pre.bits) as nat;
        let m = 8 * nb;
        lemma2_to64();
        lemma2_to64_rest();
        lemma_bits_bound(data, l, k);
        let v = pre.value;
        lemma_pow2_pos(k);
        assert(v <= s.value) by {
            let pk = pow2(k) as int;
            assert(v * pk >= v) by (nonlinear_arith)
                requires
                    v >= 0,
                    pk >= 1,
            ;
        }
        assert(v < 256);
        lemma_bytes(data, i, nb);
        let sb = stream_bits(data, l, m);
        if nb == 7 {
            reveal_with_fuel(be_bytes, 8);
            let d0 = buf[pre.pos as int];
            let d1 = buf[pre.pos + 1];
            let d2 = buf[pre.pos + 2];
            let d3 = buf[pre.pos + 3];
            let d4 = buf[pre.pos + 4];
            let d5 = buf[pre.pos + 5];
            let d6 = buf[pre.pos + 6];
            assert(data[i as int + 0] == d0 && data[i as int + 1] == d1 && data[i as int + 2] == d2 && data[i as int + 3] == d3 && data[i as int + 4]
                == d4 && data[i as int + 5] == d5 && data[i as int + 6] == d6);
            assert(sb == 256 * (256 * (256 * (256 * (256 * (256 * (d0 as nat) + d1) + d2) + d3) + d4) + d5) + d6);
            assert(v < 256 ==> ((d0 as u64) << 48u32 | (d1 as u64) << 40u32 | (d2 as u64) << 32u32 | (d3 as u64)
                << 24u32 | (d4 as u64) << 16u32 | (d5 as u64) << 8u32 | (d6 as u64)) | (v << 56u32) == 256 * (256 * (256
                * (256 * (256 * (256 * (256 * v + d0 as u64) + d1 as u64) + d2 as u64) + d3 as u64) + d4 as u64)
                + d5 as u64) + d6 as u64) by (bit_vector);
            assert(post.value == v * pow2(56) + sb);
        } else {
            reveal_with_fuel(be_bytes, 2);
            let d0 = buf[pre.pos as int];
            assert(data[i as int + 0] == d0);
            assert(sb == d0);
            assert(v < 256 ==> (d0 as u64) | (v << 8u32) == 256 * v + d0 as u64) by (bit_vector);
            assert(post.value == v * pow2(8) + sb);
        }
        lemma_window(data, v as int, l, k, m);
        assert(l + k == s.pos);
        assert(8 * (post.pos - start) == l + m);
    }

    /// `VP8LoadNewBytes`.
    #[inline(always)]
    fn load(&mut self, buf: &[u8])
        requires
            old(self).inv(buf@.len()),
            old(self).bits < 0,
        ensures
            final(self).end == old(self).end,
            final(self).inv(buf@.len()),
            final(self).bits >= 0,
            final(self).range == old(self).range,
            old(self).eof ==> final(self).eof,
            forall|start: int, s: BoolState| #[trigger]
                old(self).rel(buf@, start, s) && !final(self).eof ==> final(self).rel(buf@, start, s),
    {
        let ghost pre = *self;
        if self.end - self.pos >= 8 {
            let p = self.pos;
            let w = load_u64_le(buf, p);
            proof {
                lemma_be7(buf@, p as int, w);
            }
            let b = bswap64(w) >> 8u32;
            self.pos = self.pos + 7;
            self.value = b | (self.value << 56u32);
            self.bits = self.bits + 56;
            proof {
                let post = *self;
                assert forall|start: int, s: BoolState| #[trigger] pre.rel(buf@, start, s) implies post.rel(
                    buf@,
                    start,
                    s,
                ) by {
                    Self::lemma_load(pre, post, buf@, start, s, 7, b);
                }
            }
        } else if self.pos < self.end {
            let ghost b = buf@[self.pos as int] as u64;
            self.value = (get(buf, self.pos) as u64) | (self.value << 8u32);
            self.pos = self.pos + 1;
            self.bits = self.bits + 8;
            proof {
                let post = *self;
                assert forall|start: int, s: BoolState| #[trigger] pre.rel(buf@, start, s) implies post.rel(
                    buf@,
                    start,
                    s,
                ) by {
                    Self::lemma_load(pre, post, buf@, start, s, 1, b);
                }
            }
        } else if !self.eof {
            self.value = self.value << 8u32;
            self.bits = self.bits + 8;
            self.eof = true;
        } else {
            // Past the end twice: the decode has already failed.
            self.value = 0;
            self.bits = 0;
        }
    }

    /// `VP8GetBit`: one bit with probability `prob / 256` of being zero.
    #[inline(always)]
    pub fn get_bit(&mut self, buf: &[u8], prob: u8) -> (b: bool)
        requires
            old(self).inv(buf@.len()),
        ensures
            final(self).end == old(self).end,
            final(self).inv(buf@.len()),
            old(self).eof ==> final(self).eof,
            forall|start: int, s: BoolState| #[trigger]
                old(self).rel(buf@, start, s) && !final(self).eof ==> {
                    &&& final(self).rel(buf@, start, bool_next(part(buf@, start, old(self).end as int), s, prob as int))
                    &&& b == bool_bit(s, prob as int)
                    &&& final(self).range <= 254
                },
    {
        if self.bits < 0 {
            self.load(buf);
        }
        let ghost pre = *self;
        let ru = self.range;
        let pos = self.bits as u32;
        let lz = self.sh;
        proof {
            lemma_lz(ru);
            lemma_lazy_split(ru, prob);
        }
        let m = ru * prob as u32;
        let x = ((m as u64) << lz as u64) + (((256 - prob as u32) as u64) << 24u32);
        let split = (x >> 32u32) as u32;
        let rn = (ru << lz) >> 24u32;
        proof {
            let w = self.value >> pos as u64;
            assert(w & 0xffff_ffffu64 <= 0xffff_ffffu64) by (bit_vector);
        }
        let value = ((self.value >> pos as u64) & 0xffff_ffffu64) as u32;
        let bit = value >= split;
        let r = if bit {
            proof {
                lemma_sub_ok(self.value, pos as u64, (split - 1) as u64);
            }
            self.value = self.value - ((split as u64) << pos as u64);
            rn - split
        } else {
            split
        };
        proof {
            lemma_lz(r);
        }
        self.range = r;
        let nlz = r.leading_zeros();
        self.sh = nlz;
        self.bits = self.bits - (nlz as i32 - 24);
        proof {
            let post = *self;
            assert forall|start: int, s: BoolState| #[trigger]
                old(self).rel(buf@, start, s) && !post.eof implies post.rel(
                buf@,
                start,
                bool_next(part(buf@, start, old(self).end as int), s, prob as int),
            ) && bit == bool_bit(s, prob as int) && post.range <= 254 by {
                assert(pre.rel(buf@, start, s));
                lemma_get_bit(pre, post, buf@, start, s, prob, split, value, r);
            }
        }
        bit
    }

    /// `VP8GetSigned`: `v` or `-v`, on an even-probability bit that always
    /// consumes one bit of range.
    #[inline(always)]
    pub fn get_signed(&mut self, buf: &[u8], v: i32) -> (r: i32)
        requires
            old(self).inv(buf@.len()),
            -0x7fff_ffff <= v,
        ensures
            final(self).end == old(self).end,
            final(self).inv(buf@.len()),
            r == v || r == -v,
            old(self).eof ==> final(self).eof,
            forall|start: int, s: BoolState| #[trigger]
                old(self).rel(buf@, start, s) && !final(self).eof && old(self).range <= 254 ==> {
                    &&& final(self).rel(buf@, start, bool_next(part(buf@, start, old(self).end as int), s, 128))
                    &&& r == (if bool_bit(s, 128) {
                        -(v as int)
                    } else {
                        v as int
                    })
                    &&& final(self).range <= 254
                },
    {
        if self.bits < 0 {
            self.load(buf);
        }
        let ghost pre = *self;
        let pos = self.bits as u32;
        let ru = self.range;
        let lz = self.sh;
        proof {
            lemma_lz(ru);
        }
        let rn = (ru << lz) >> 24u32;
        let split = (rn + 1) >> 1u32;
        proof {
            let w = self.value >> pos as u64;
            assert(w & 0xffff_ffffu64 <= 0xffff_ffffu64) by (bit_vector);
        }
        let value = ((self.value >> pos as u64) & 0xffff_ffffu64) as u32;
        self.bits = self.bits - 1;
        let mask: u32 = ((split as i32).wrapping_sub(1).wrapping_sub(value as i32) >> 31u32) as u32;
        proof {
            lemma_signed_mask(rn, value, v);
        }
        let nr = split - (mask & rn & 1);
        self.range = nr;
        self.sh = nr.leading_zeros();
        proof {
            let p = pos as u64;
            assert(0u64 << p == 0) by (bit_vector);
        }
        self.value = self.value.wrapping_sub(((split & mask) as u64) << pos as u64);
        let res = ((v as u32 ^ mask).wrapping_sub(mask)) as i32;
        proof {
            assert(res == (if mask != 0 {
                -v
            } else {
                v as int
            }));
            let post = *self;
            assert forall|start: int, s: BoolState| #[trigger]
                old(self).rel(buf@, start, s) && !post.eof && old(self).range <= 254 implies post.rel(
                buf@,
                start,
                bool_next(part(buf@, start, old(self).end as int), s, 128),
            ) && (mask != 0) == bool_bit(s, 128) && post.range <= 254 by {
                assert(pre.rel(buf@, start, s));
                lemma_window_value(pre, buf@, start, s);
                if value >= split {
                    lemma_sub_ok(pre.value, pos as u64, (split - 1) as u64);
                }
                lemma_get_bit(pre, post, buf@, start, s, 128, split, value, post.range);
            }
        }
        res
    }

    /// `VP8GetValue`: `n` bits, most significant first.
    pub fn get_value(&mut self, buf: &[u8], n: u32) -> (v: u32)
        requires
            old(self).inv(buf@.len()),
            n <= 8,
        ensures
            final(self).end == old(self).end,
            final(self).inv(buf@.len()),
            v < p2(n as nat),
            v < 256,
            old(self).eof ==> final(self).eof,
            forall|start: int, s: BoolState| #[trigger]
                old(self).rel(buf@, start, s) && !final(self).eof ==> {
                    &&& final(self).rel(buf@, start, bool_literal(part(buf@, start, old(self).end as int), s, n as nat).0)
                    &&& v == bool_literal(part(buf@, start, old(self).end as int), s, n as nat).1
                },
    {
        let mut v: u32 = 0;
        let mut k = n;
        proof {
            assert(p2(8) == 256) by (compute);
            lemma_p2_mono(n as nat, 8);
        }
        while k > 0
            invariant
                self.inv(buf@.len()),
                self.end == old(self).end,
                k <= n <= 8,
                v < p2((n - k) as nat),
                p2(n as nat) <= 256,
                old(self).eof ==> self.eof,
                forall|start: int, s: BoolState| #[trigger]
                    old(self).rel(buf@, start, s) && !self.eof ==> {
                        &&& self.rel(
                            buf@,
                            start,
                            bool_literal(part(buf@, start, old(self).end as int), s, (n - k) as nat).0,
                        )
                        &&& v == bool_literal(part(buf@, start, old(self).end as int), s, (n - k) as nat).1
                    },
            decreases k,
        {
            let ghost mid = *self;
            let ghost v0 = v;
            k = k - 1;
            let b = self.get_bit(buf, 0x80);
            proof {
                let post = *self;
                assert forall|start: int, s: BoolState| #[trigger]
                    old(self).rel(buf@, start, s) && !post.eof implies post.rel(
                    buf@,
                    start,
                    bool_literal(part(buf@, start, old(self).end as int), s, (n - k) as nat).0,
                ) && 2 * v0 + (if b {
                    1int
                } else {
                    0int
                }) == bool_literal(part(buf@, start, old(self).end as int), s, (n - k) as nat).1 by {
                    let data = part(buf@, start, old(self).end as int);
                    let j = (n - k - 1) as nat;
                    assert(!mid.eof);
                    let s1 = bool_literal(data, s, j).0;
                    assert(mid.rel(buf@, start, s1));
                    assert((n - k) as nat == j + 1);
                    assert(bool_literal(data, s, (n - k) as nat) == (
                        bool_next(data, s1, 128),
                        2 * bool_literal(data, s, j).1 + if bool_bit(s1, 128) {
                            1int
                        } else {
                            0int
                        },
                    ));
                }
            }
            proof {
                assert(p2((n - k) as nat) == 2 * p2((n - k - 1) as nat));
                lemma_p2_mono((n - k) as nat, n as nat);
            }
            v = 2 * v + b as u32;
        }
        v
    }

    /// `VP8GetSignedValue`: an `n`-bit magnitude, then its sign.
    pub fn get_signed_value(&mut self, buf: &[u8], n: u32) -> (v: i32)
        requires
            old(self).inv(buf@.len()),
            n <= 8,
        ensures
            final(self).end == old(self).end,
            final(self).inv(buf@.len()),
            -255 <= v <= 255,
            -p2(n as nat) < v < p2(n as nat),
            old(self).eof ==> final(self).eof,
            forall|start: int, s: BoolState| #[trigger]
                old(self).rel(buf@, start, s) && !final(self).eof ==> {
                    let data = part(buf@, start, old(self).end as int);
                    let (s1, m) = bool_literal(data, s, n as nat);
                    &&& final(self).rel(buf@, start, bool_next(data, s1, 128))
                    &&& v == (if bool_bit(s1, 128) {
                        -m
                    } else {
                        m
                    })
                },
    {
        let m = self.get_value(buf, n) as i32;
        if self.get_bit(buf, 0x80) {
            -m
        } else {
            m
        }
    }
}

} // verus!
