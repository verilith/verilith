//! Entropy coding for the compressor: the bit writer, FSE tables and
//! descriptions, Huffman codes and tree descriptions, and the literals and
//! sequences sections. Only memory safety is proven here: `compress` keeps
//! a block only after the verified decoder has decoded it back.
use vstd::prelude::*;
use verilith_core::spare::{push_spare, reserve_spare};

verus! {

// ---------------------------------------------------------------------------
// The bit writer
// ---------------------------------------------------------------------------

/// Bits added low first; whole bytes go out little-endian.
pub struct Bits {
    pub acc: u64,
    pub n: u32,
}

/// `out` only grew.
pub open spec fn grew(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() <= b.len() && b.subrange(0, a.len() as int) == a
}

pub proof fn lemma_grew_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        grew(a, b),
        grew(b, c),
    ensures
        grew(a, c),
{
    assert(c.subrange(0, a.len() as int) =~= c.subrange(0, b.len() as int).subrange(0, a.len() as int));
}

pub proof fn lemma_grew_refl(a: Seq<u8>)
    ensures
        grew(a, a),
{
    assert(a.subrange(0, a.len() as int) =~= a);
}

/// The low 8 bits of `x`.
#[inline(always)]
pub fn lo8(x: u64) -> u8 {
    let y = x & 0xff;
    proof {
        assert(y < 256) by (bit_vector)
            requires y == x & 0xff;
    }
    y as u8
}

/// The low 16 bits of `x`.
#[inline(always)]
pub fn lo16(x: u64) -> u16 {
    let y = x & 0xffff;
    proof {
        assert(y < 0x1_0000) by (bit_vector)
            requires y == x & 0xffff;
    }
    y as u16
}

/// The low 12 bits of `x`: an index into an FSE table.
#[inline(always)]
pub fn lo12(x: u32) -> (r: usize)
    ensures
        r < 4096,
{
    let y = x & 0xFFF;
    proof {
        assert(y < 4096) by (bit_vector)
            requires y == x & 0xFFF;
    }
    y as usize
}

/// The low 32 bits of `x`.
#[inline(always)]
pub fn lo32(x: u64) -> u32 {
    let y = x & 0xffff_ffff;
    proof {
        assert(y < 0x1_0000_0000) by (bit_vector)
            requires y == x & 0xffff_ffff;
    }
    y as u32
}

/// Pushes `x`: the vector only grows.
#[inline(always)]
pub fn push(out: &mut Vec<u8>, x: u8)
    ensures
        grew(old(out)@, final(out)@),
        final(out)@.len() == old(out)@.len() + 1,
{
    out.push(x);
    proof {
        assert(out@.subrange(0, old(out)@.len() as int) =~= old(out)@);
    }
}

impl Bits {
    pub fn new() -> (r: Bits)
        ensures
            r.n == 0,
    {
        Bits { acc: 0, n: 0 }
    }

    /// Moves the whole bytes of the accumulator to `out` (one 8-byte
    /// store).
    #[inline(always)]
    pub fn flush(&mut self, out: &mut Vec<u8>)
        requires
            old(self).n < 64,
        ensures
            final(self).n == old(self).n % 8,
            grew(old(out)@, final(out)@),
            final(out)@.len() == old(out)@.len() + old(self).n / 8,
    {
        let k = self.n / 8;
        let ghost o0 = out@;
        verilith_core::spare::reserve_spare(out, 8);
        verilith_core::spare::append8_spare(out, self.acc, k as usize);
        proof {
            assert(out@.subrange(0, o0.len() as int) =~= o0);
        }
        let sh = (8 * k) as u64;
        self.acc = self.acc >> sh;
        self.n = self.n - 8 * k;
    }

    /// `flush` into room the caller reserved: one store, no capacity
    /// check.
    #[inline(always)]
    pub fn flush_s(&mut self, out: &mut Vec<u8>)
        requires
            old(self).n < 64,
            verilith_core::spare::spare(*old(out)) >= 8,
        ensures
            final(self).n < 8,
            grew(old(out)@, final(out)@),
            verilith_core::spare::spare(*final(out)) >= verilith_core::spare::spare(*old(out)) - 7,
    {
        let k = self.n / 8;
        let ghost o0 = out@;
        verilith_core::spare::append8_spare(out, self.acc, k as usize);
        proof {
            assert(out@.subrange(0, o0.len() as int) =~= o0);
        }
        let sh = (8 * k) as u64;
        self.acc = self.acc >> sh;
        self.n = self.n - 8 * k;
    }

    /// Adds the low `nb` bits of `v`, which fit without a flush.
    #[inline(always)]
    pub fn put(&mut self, v: u64, nb: u32)
        requires
            old(self).n + nb <= 63,
        ensures
            final(self).n == old(self).n + nb,
    {
        assert((1u64 << nb) >= 1) by (bit_vector)
            requires
                nb <= 63,
        ;
        let mask = (1u64 << nb) - 1;
        self.acc = self.acc | ((v & mask) << self.n);
        self.n = self.n + nb;
    }

    /// Adds `v`, which the caller has made less than `2^nb`, and which
    /// fits without a flush.
    #[inline(always)]
    pub fn put_raw(&mut self, v: u64, nb: u32)
        requires
            old(self).n + nb <= 63,
        ensures
            final(self).n == old(self).n + nb,
    {
        self.acc = self.acc | (v << self.n);
        self.n = self.n + nb;
    }

    /// Adds the low `nb` bits of `v`.
    #[inline(always)]
    pub fn add(&mut self, out: &mut Vec<u8>, v: u64, nb: u32)
        requires
            old(self).n < 64,
            nb <= 32,
        ensures
            final(self).n < 64,
            final(self).n >= 1 || nb == 0 || old(self).n + nb > 63,
            old(self).n + nb <= 63 ==> final(self).n == old(self).n + nb && final(out)@ == old(out)@,
            grew(old(out)@, final(out)@),
    {
        if self.n + nb > 63 {
            self.flush(out);
        } else {
            proof {
                lemma_grew_refl(out@);
            }
        }
        assert((1u64 << nb) >= 1) by (bit_vector)
            requires
                nb <= 32,
        ;
        let mask = (1u64 << nb) - 1;
        self.acc = self.acc | ((v & mask) << self.n);
        self.n = self.n + nb;
    }

    /// Adds `v`, which the caller has made less than `2^nb` (larger
    /// values only spoil the stream, which the decoder's check rejects).
    #[inline(always)]
    pub fn add_raw(&mut self, out: &mut Vec<u8>, v: u64, nb: u32)
        requires
            old(self).n < 64,
            nb <= 32,
        ensures
            final(self).n < 64,
            grew(old(out)@, final(out)@),
    {
        if self.n + nb > 63 {
            self.flush(out);
        } else {
            proof {
                lemma_grew_refl(out@);
            }
        }
        self.acc = self.acc | (v << self.n);
        self.n = self.n + nb;
    }

    /// The end marker, then the last bits.
    pub fn close(&mut self, out: &mut Vec<u8>)
        requires
            old(self).n < 64,
        ensures
            grew(old(out)@, final(out)@),
            final(out)@.len() > old(out)@.len(),
    {
        let ghost o0 = out@;
        if self.n == 63 {
            self.flush(out);
        } else {
            proof {
                lemma_grew_refl(out@);
            }
        }
        let ghost o1 = out@;
        self.add(out, 1, 1);
        let ghost o2 = out@;
        let n1 = self.n;
        self.flush(out);
        let ghost o3 = out@;
        if self.n > 0 {
            push(out, lo8(self.acc));
        } else {
            proof {
                lemma_grew_refl(out@);
            }
        }
        proof {
            lemma_grew_trans(o0, o1, o2);
            lemma_grew_trans(o0, o2, o3);
            lemma_grew_trans(o0, o3, out@);
            assert(n1 >= 1);
            assert(n1 / 8 >= 1 || n1 % 8 >= 1);
        }
        self.acc = 0;
        self.n = 0;
    }
}

// ---------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------

/// Index of the highest set bit (0 for 0).
#[inline(always)]
pub fn hbit(x: u32) -> (r: u32)
    ensures
        r <= 31,
{
    if x == 0 {
        0
    } else {
        31 - x.leading_zeros()
    }
}

/// `256 * log2(1 + i / 256)`, rounded.
pub const LOG_FRAC: [u16; 256] = [
    0, 1, 3, 4, 6, 7, 9, 10, 11, 13, 14, 16, 17, 18, 20, 21, 22, 24, 25, 26, 28, 29, 30, 32, 33, 34,
    36, 37, 38, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 59, 60, 61, 62, 63, 65, 66,
    67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95,
    96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117,
    118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137,
    138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 155, 156,
    157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 169, 170, 171, 172, 173, 174, 175,
    176, 177, 178, 178, 179, 180, 181, 182, 183, 184, 185, 185, 186, 187, 188, 189, 190, 191, 192, 192,
    193, 194, 195, 196, 197, 198, 198, 199, 200, 201, 202, 203, 203, 204, 205, 206, 207, 208, 208, 209,
    210, 211, 212, 212, 213, 214, 215, 216, 216, 217, 218, 219, 220, 220, 221, 222, 223, 224, 224, 225,
    226, 227, 228, 228, 229, 230, 231, 231, 232, 233, 234, 234, 235, 236, 237, 238, 238, 239, 240, 241,
    241, 242, 243, 244, 244, 245, 246, 247, 247, 248, 249, 249, 250, 251, 252, 252, 253, 254, 255, 255,
];

/// `256 * log2(x)`, approximately (0 for 0).
pub fn log2_256(x: u32) -> (r: u32)
    ensures
        r <= 32 * 256,
{
    if x == 0 {
        return 0;
    }
    let h = hbit(x);
    let frac: u32 = if h >= 8 {
        let y = x >> (h - 8);
        proof {
            assert(y & 255 < 256) by (bit_vector);
        }
        y & 255
    } else {
        let y = x << (8 - h);
        proof {
            assert(y & 255 < 256) by (bit_vector);
        }
        y & 255
    };
    h * 256 + LOG_FRAC[frac as usize] as u32
}

// ---------------------------------------------------------------------------
// FSE: normalized counts, table descriptions, encoding tables
// ---------------------------------------------------------------------------

/// The accuracy log for `total` symbols of values up to `maxsv`, at most
/// `maxlog` (libzstd's `FSE_optimalTableLog`, at least 5).
pub fn fse_log(maxlog: u32, total: u32, maxsv: u32) -> (r: u32)
    requires
        5 <= maxlog <= 12,
        total >= 2,
    ensures
        5 <= r <= maxlog,
{
    let min_src = hbit(total) + 1;
    let min_sym = hbit(maxsv) + 2;
    let minb = if min_src < min_sym {
        min_src
    } else {
        min_sym
    };
    let hb = hbit(total - 1);
    let mut log = maxlog;
    if hb >= 2 && hb - 2 < log {
        log = hb - 2;
    }
    if minb > log {
        log = minb;
    }
    if log < 5 {
        log = 5;
    }
    if log > maxlog {
        log = maxlog;
    }
    log
}

const RTB: [u64; 8] = [0, 473195, 504333, 520860, 550000, 700000, 750000, 830000];

/// Normalizes `count[0..=maxsv]` (summing to `total`) to `2^log`
/// (libzstd's `FSE_normalizeCount`). `None` when it fails.
pub fn normalize(count: &[u32], total: u32, maxsv: usize, log: u32, lowprob: bool) -> (r: Option<Vec<i16>>)
    requires
        maxsv < count@.len(),
        count@.len() <= 256,
        5 <= log <= 12,
        total >= 2,
    ensures
        r matches Some(v) ==> v@.len() == maxsv + 1,
{
    let scale: u64 = 62 - log as u64;
    let step: u64 = 0x4000_0000_0000_0000u64 / total as u64;
    let vstep: u64 = 1u64 << (scale - 20);
    proof {
        assert(1i64 << log <= 4096 && 1i64 << log >= 1) by (bit_vector)
            requires log <= 12;
    }
    let mut still: i64 = 1i64 << log;
    let mut largest: usize = 0;
    let mut largest_p: i64 = 0;
    let low = (total >> log) as u64;
    let mut norm: Vec<i16> = vec![0i16; maxsv + 1];
    let mut s: usize = 0;
    while s <= maxsv
        invariant
            maxsv < count@.len(),
            norm@.len() == maxsv + 1,
            largest <= maxsv,
            -0x10000 <= still <= 4096,
            5 <= log <= 12,
            scale == 62 - log as u64,
            s <= maxsv + 1,
            step == 0x4000_0000_0000_0000u64 / total as u64,
            total >= 2,
            vstep == 1u64 << (scale - 20),
        decreases maxsv + 1 - s,
    {
        let c = count[s] as u64;
        if c == total as u64 {
            return None;
        }
        if c == 0 {
            norm.set(s, 0);
        } else if c <= low {
            norm.set(s, if lowprob { -1 } else { 1 });
            if still > -0x10000 {
                still = still - 1;
            }
        } else {
            if c > total as u64 {
                return None;
            }
            proof {
                let t = total as u64;
                assert(c * step <= t * step) by (nonlinear_arith)
                    requires c <= t;
                assert(t * (0x4000_0000_0000_0000u64 / t) <= 0x4000_0000_0000_0000u64) by (nonlinear_arith)
                    requires t >= 2;
            }
            let prod = c * step;
            let mut proba: u64 = prod >> scale;
            if proba < 8 {
                proof {
                    let sh = (scale - 20) as u64;
                    assert(vstep <= (1u64 << 37)) by (bit_vector)
                        requires vstep == 1u64 << sh, sh >= 30, sh <= 37;
                }
                let rtb = vstep.wrapping_mul(RTB[proba as usize]);
                if prod.wrapping_sub(proba << scale) > rtb {
                    proba = proba + 1;
                }
            }
            if proba > 4096 {
                return None;
            }
            if proba as i64 > largest_p {
                largest_p = proba as i64;
                largest = s;
            }
            norm.set(s, proba as i16);
            if still - (proba as i64) < -0x10000 {
                return None;
            }
            still = still - proba as i64;
        }
        s = s + 1;
    }
    let nl = norm[largest] as i64;
    if -still >= (nl >> 1) {
        // libzstd's FSE_normalizeM2.
        return normalize_m2(count, total, maxsv, log, lowprob);
    }
    if nl + still < 1 || nl + still > 4096 {
        return None;
    }
    norm.set(largest, (nl + still) as i16);
    Some(norm)
}

/// The second normalization method of libzstd (`FSE_normalizeM2`).
fn normalize_m2(count: &[u32], total0: u32, maxsv: usize, log: u32, lowprob: bool) -> (r: Option<Vec<i16>>)
    requires
        maxsv < count@.len(),
        count@.len() <= 256,
        5 <= log <= 12,
        total0 >= 2,
    ensures
        r matches Some(v) ==> v@.len() == maxsv + 1,
{
    let nya: i16 = -2;
    let mut norm: Vec<i16> = vec![0i16; maxsv + 1];
    let mut distributed: u32 = 0;
    let mut total: u64 = total0 as u64;
    let low = total >> log;
    let mut low_one: u64 = (total * 3) >> (log + 1);
    let mut s: usize = 0;
    while s <= maxsv
        invariant
            maxsv < count@.len(),
            norm@.len() == maxsv + 1,
            s <= maxsv + 1,
            distributed <= s,
            count@.len() <= 256,
            5 <= log <= 12,
            total <= 0xFFFF_FFFF,
        decreases maxsv + 1 - s,
    {
        let c = count[s] as u64;
        if c == 0 {
            norm.set(s, 0);
        } else if c <= low {
            norm.set(s, if lowprob { -1 } else { 1 });
            distributed = distributed + 1;
            total = if c <= total { total - c } else { 0 };
        } else if c <= low_one {
            norm.set(s, 1);
            distributed = distributed + 1;
            total = if c <= total { total - c } else { 0 };
        } else {
            norm.set(s, nya);
        }
        s = s + 1;
    }
    let size: u32 = 1u32 << log;
    if distributed > size {
        return None;
    }
    let mut todo: u32 = size - distributed;
    if todo == 0 {
        return Some(norm);
    }
    if total / (todo as u64) > low_one {
        low_one = (total * 3) / (todo as u64 * 2);
        let mut s: usize = 0;
        while s <= maxsv
            invariant
                maxsv < count@.len(),
                norm@.len() == maxsv + 1,
                s <= maxsv + 1,
                count@.len() <= 256,
                distributed <= 4096 + s,
                total <= 0xFFFF_FFFF,
            decreases maxsv + 1 - s,
        {
            let c = count[s] as u64;
            if norm[s] == nya && c <= low_one {
                norm.set(s, 1);
                distributed = distributed + 1;
                total = if c <= total { total - c } else { 0 };
            }
            s = s + 1;
        }
        if distributed > size {
            return None;
        }
        todo = size - distributed;
    }
    if distributed as usize == maxsv + 1 {
        // All symbols took 1 or "less than 1": the most frequent takes the rest.
        let mut mx: usize = 0;
        let mut mc: u32 = 0;
        let mut s: usize = 0;
        while s <= maxsv
            invariant
                maxsv < count@.len(),
                s <= maxsv + 1,
                mx <= maxsv,
            decreases maxsv + 1 - s,
        {
            if count[s] > mc {
                mc = count[s];
                mx = s;
            }
            s = s + 1;
        }
        let v = norm[mx] as i64 + todo as i64;
        if v > 4096 || v < 1 {
            return None;
        }
        norm.set(mx, v as i16);
        return Some(norm);
    }
    if total == 0 {
        // Spread the rest over the symbols with a positive count.
        let mut guard: u32 = 0;
        let mut s: usize = 0;
        while todo > 0 && guard < 0x10_0000
            invariant
                norm@.len() == maxsv + 1,
                s <= maxsv,
            decreases 0x10_0000 - guard,
        {
            let v = norm[s];
            if v > 0 && v < 4096 {
                todo = todo - 1;
                norm.set(s, v + 1);
            }
            s = if s == maxsv { 0 } else { s + 1 };
            guard = guard + 1;
        }
        if todo > 0 {
            return None;
        }
        return Some(norm);
    }
    let vlog: u64 = 62 - log as u64;
    let vl1: u64 = vlog - 1;
    proof {
        assert((1u64 << vl1) >= 1 && (1u64 << vl1) <= 0x100_0000_0000_0000u64) by (bit_vector)
            requires 49 <= vl1 <= 56;
    }
    let mid: u64 = (1u64 << vl1) - 1;
    proof {
        let t = todo as u64;
        let lg = log as u64;
        assert((1u64 << vlog) * t <= 0x4000_0000_0000_0000u64) by (bit_vector)
            requires t == todo as u64, todo <= size, size == (1u32 << log), 5 <= log <= 12, lg == log as u64, vlog == 62 - lg;
    }
    let rstep: u64 = ((1u64 << vlog) * (todo as u64) + mid) / total;
    let mut tmp: u64 = mid;
    let mut s: usize = 0;
    while s <= maxsv
        invariant
            maxsv < count@.len(),
            count@.len() <= 256,
            norm@.len() == maxsv + 1,
            s <= maxsv + 1,
            total > 0,
            vlog == 62 - log as u64,
            log <= 12,
        decreases maxsv + 1 - s,
    {
        if norm[s] == nya {
            let c = count[s] as u64;
            if rstep > 0 && c > 0xFFFF_FFFF_FFFF_FFFF / rstep {
                return None;
            }
            proof {
                if rstep > 0 {
                    assert(c * rstep <= 0xFFFF_FFFF_FFFF_FFFFu64) by (nonlinear_arith)
                        requires rstep > 0, c <= 0xFFFF_FFFF_FFFF_FFFFu64 / rstep;
                }
            }
            let add = c * rstep;
            if tmp > 0xFFFF_FFFF_FFFF_FFFF - add {
                return None;
            }
            let e = tmp + add;
            let st = tmp >> vlog;
            let en = e >> vlog;
            if en <= st || en - st > 4096 {
                return None;
            }
            norm.set(s, (en - st) as i16);
            tmp = e;
        }
        s = s + 1;
    }
    Some(norm)
}

/// Does `norm` fill `2^log` exactly, with no value out of range?
pub fn norm_ok(norm: &[i16], log: u32) -> (r: bool)
    requires
        log <= 12,
{
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < norm.len()
        invariant
            i <= norm@.len(),
            -0x100_0000 <= sum <= 0x100_0000,
        decreases norm@.len() - i,
    {
        let v = norm[i];
        if v < -1 || v > 4096 {
            return false;
        }
        sum = sum + if v == -1 { 1 } else { v as i64 };
        if sum > 0x10000 {
            return false;
        }
        i = i + 1;
    }
    sum == (1i64 << log)
}

/// Pushes the low 16 bits of `bs`.
#[inline(always)]
fn push16(out: &mut Vec<u8>, bs: u64)
    ensures
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    push(out, bs as u8);
    let ghost o1 = out@;
    push(out, (bs >> 8) as u8);
    proof {
        lemma_grew_trans(o0, o1, out@);
    }
}

/// Writes the table description of `norm` (libzstd's `FSE_writeNCount`).
#[verifier::loop_isolation(false)]
pub fn write_ncount(out: &mut Vec<u8>, norm: &[i16], log: u32) -> (ok: bool)
    requires
        5 <= log <= 12,
        norm@.len() <= 256,
    ensures
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    proof {
        lemma_grew_refl(out@);
    }
    proof {
        assert(1i64 << log <= 4096 && 1i64 << log >= 32) by (bit_vector)
            requires 5 <= log <= 12;
    }
    let size: i64 = 1i64 << log;
    let mut remaining: i64 = size + 1;
    let mut threshold: i64 = size;
    let mut nbits: u32 = log + 1;
    let mut bs: u64 = (log - 5) as u64;
    let mut bc: u32 = 4;
    let mut prev0 = false;
    let n = norm.len();
    let mut s: usize = 0;
    while s < n && remaining > 1
        invariant
            s <= n,
            bc <= 16,
            1 <= nbits <= 13,
            0 <= threshold <= 4096,
            1 <= remaining <= 4097,
            grew(o0, out@),
        decreases n - s,
    {
        if prev0 {
            let mut start = s;
            while s < n && norm[s] == 0
                invariant
                    start <= s <= n,
                decreases n - s,
            {
                s = s + 1;
            }
            if s == n {
                return false;
            }
            while s >= start + 24
                invariant
                    start <= s < n,
                    bc <= 16,
                    grew(o0, out@),
                decreases s - start,
            {
                start = start + 24;
                bs = bs | (0xFFFFu64 << bc);
                let ghost o1 = out@;
                push16(out, bs);
                proof {
                    lemma_grew_trans(o0, o1, out@);
                }
                bs = bs >> 16;
            }
            while s >= start + 3
                invariant
                    start <= s < n,
                    bc <= 30,
                    grew(o0, out@),
                decreases s - start,
            {
                start = start + 3;
                if bc >= 28 {
                    return false;
                }
                bs = bs | (3u64 << bc);
                bc = bc + 2;
            }
            if bc >= 28 {
                return false;
            }
            bs = bs | (((s - start) as u64) << bc);
            bc = bc + 2;
            while bc > 16
                invariant
                    bc <= 30,
                    grew(o0, out@),
                decreases bc,
            {
                let ghost o1 = out@;
                push16(out, bs);
                proof {
                    lemma_grew_trans(o0, o1, out@);
                }
                bs = bs >> 16;
                bc = bc - 16;
            }
        }
        if s >= n {
            return false;
        }
        let cnt0 = norm[s] as i64;
        s = s + 1;
        let max = (2 * threshold - 1) - remaining;
        remaining = remaining - if cnt0 < 0 { -cnt0 } else { cnt0 };
        let mut cnt = cnt0 + 1;
        if cnt >= threshold {
            cnt = cnt + max;
        }
        if cnt < 0 || cnt >= 0x10000 {
            return false;
        }
        bs = bs | ((cnt as u64) << bc);
        bc = bc + nbits;
        if cnt < max {
            bc = bc - 1;
        }
        prev0 = cnt == 1;
        if remaining < 1 {
            return false;
        }
        while remaining < threshold && nbits > 1
            invariant
                1 <= nbits <= 13,
                0 <= threshold <= 4096,
                bc <= 29,
            decreases nbits,
        {
            nbits = nbits - 1;
            threshold = threshold / 2;
        }
        while bc > 16
            invariant
                bc <= 29,
                grew(o0, out@),
            decreases bc,
        {
            let ghost o1 = out@;
            push16(out, bs);
            proof {
                lemma_grew_trans(o0, o1, out@);
            }
            bs = bs >> 16;
            bc = bc - 16;
        }
    }
    if remaining != 1 {
        return false;
    }
    let nb = (bc + 7) / 8;
    let mut k: u32 = 0;
    while k < nb
        invariant
            k <= nb <= 2,
            grew(o0, out@),
        decreases nb - k,
    {
        let ghost o1 = out@;
        push(out, lo8(bs >> (8 * k)));
        proof {
            lemma_grew_trans(o0, o1, out@);
        }
        k = k + 1;
    }
    true
}

/// An FSE encoding table (libzstd's `FSE_CTable`), in fixed-size
/// arrays so that a byte or a masked state indexes them without a check.
pub struct FseC {
    pub log: u32,
    /// `2^log - 1`.
    pub mask: u32,
    /// The next state for each (symbol, row) pair, in symbol order.
    pub next: [u16; 4096],
    /// Per symbol: `deltaNbBits` (low half) and `deltaFindState` (high
    /// half, as a two's complement `u32`).
    pub sym: [u64; 256],
}

impl FseC {
    pub open spec fn wf(&self) -> bool {
        &&& 0 <= self.log <= 12
    }

    pub fn new() -> (r: FseC)
        ensures
            r.wf(),
    {
        FseC { log: 5, mask: 31, next: [0u16; 4096], sym: [0u64; 256] }
    }
}

/// The encoding table of `norm` at accuracy `log`, built in place (false
/// if `norm` is not a distribution at that accuracy).
pub fn build_ctable(norm: &[i16], log: u32, t: &mut FseC) -> (ok: bool)
    requires
        5 <= log <= 12,
        1 <= norm@.len() <= 256,
    ensures
        final(t).wf(),
        ok ==> final(t).log == log,
{
    t.log = log;
    if !norm_ok(norm, log) {
        return false;
    }
    let n = norm.len();
    let size: usize = 1usize << log;
    proof {
        assert(1usize << log <= 4096) by (bit_vector)
            requires log <= 12;
        assert(1usize << log >= 32) by (bit_vector)
            requires 5 <= log <= 12;
    }
    let mut high: usize = size - 1;
    let mut tab: Vec<u8> = vec![0u8; size];
    // Cumulated counts; "less than 1" symbols at the end of the table.
    let mut cumul: Vec<u32> = vec![0u32; n + 1];
    let mut u: usize = 1;
    while u <= n
        invariant
            t.log == log,
            log <= 12,
            1 <= u <= n + 1,
            n == norm@.len(),
            cumul@.len() == n + 1,
            tab@.len() == size,
            high < size,
            32 <= size <= 4096,
            n <= 256,
            forall|k: int| 0 <= k < u ==> cumul@[k] <= 4097 * k,
        decreases n + 1 - u,
    {
        let v = norm[u - 1];
        let prev = cumul[u - 1];
        if v == -1 {
            cumul.set(u, prev + 1);
            tab.set(high, (u - 1) as u8);
            if high == 0 {
                return false;
            }
            high = high - 1;
        } else {
            if v < 0 || v > 4096 {
                return false;
            }
            cumul.set(u, prev + v as u32);
        }
        u = u + 1;
    }
    // Spread the other symbols.
    proof {
        assert((size >> 1) + (size >> 3) + 3 < size) by (bit_vector)
            requires 32 <= size <= 4096;
    }
    let step = (size >> 1) + (size >> 3) + 3;
    let mask = size - 1;
    let mut pos: usize = 0;
    let mut s: usize = 0;
    while s < n
        invariant
            t.log == log,
            log <= 12,
            s <= n,
            n == norm@.len(),
            tab@.len() == size,
            pos < size,
            mask == size - 1,
            size <= 4096,
            step < size,
            high < size,
        decreases n - s,
    {
        let v = norm[s];
        let mut i: i16 = 0;
        while i < v
            invariant
                t.log == log,
            log <= 12,
                tab@.len() == size,
                pos < size,
                mask == size - 1,
                size <= 4096,
                step < size,
                high < size,
                i <= v || v < 0,
            decreases v - i,
        {
            tab.set(pos, lo8(s as u64));
            let ps = pos + step;
            proof {
                assert(ps & mask <= mask) by (bit_vector);
            }
            pos = ps & mask;
            let mut guard: usize = 0;
            while pos > high && guard < size
                invariant
                    t.log == log,
            log <= 12,
                    pos < size,
                    mask == size - 1,
                    step < size,
                    size <= 4096,
                decreases size - guard,
            {
                let ps = pos + step;
                proof {
                    assert(ps & mask <= mask) by (bit_vector);
                }
                pos = ps & mask;
                guard = guard + 1;
            }
            i = i + 1;
        }
        s = s + 1;
    }
    // The next-state table, in symbol order.
    let mut u: usize = 0;
    while u < size
        invariant
            t.log == log,
            log <= 12,
            u <= size,
            size <= 4096,
            tab@.len() == size,
            cumul@.len() == n + 1,
            n == norm@.len(),
        decreases size - u,
    {
        let sym = tab[u] as usize;
        if sym < n {
            let c = cumul[sym] as usize;
            if c < size {
                t.next[c] = (size + u) as u16;
                cumul.set(sym, cumul[sym] + 1);
            }
        }
        u = u + 1;
    }
    // Symbol transformations.
    let mut total: i32 = 0;
    let mut s: usize = 0;
    while s < n
        invariant
            t.log == log,
            log <= 12,
            s <= n,
            n == norm@.len(),
            n <= 256,
            5 <= log <= 12,
            -0x10000 <= total <= 0x10000,
        decreases n - s,
    {
        let v = norm[s] as i32;
        proof {
            let l1 = (log + 1) as u32;
            assert((l1 << 16) >= (1u32 << log) && (log << 16) >= (1u32 << log)) by (bit_vector)
                requires 5 <= log <= 12, l1 == log + 1;
        }
        if v == 0 {
            t.sym[s] = pack(((log + 1) << 16) - (1u32 << log), 0);
        } else if v == -1 || v == 1 {
            t.sym[s] = pack((log << 16) - (1u32 << log), total - 1);
            if total < 0x10000 {
                total = total + 1;
            }
        } else {
            if v < 0 || v > 4096 {
                return false;
            }
            let hb = hbit((v - 1) as u32);
            if hb > log {
                return false;
            }
            let mbo = log - hb;
            if mbo > 12 {
                return false;
            }
            let msp = (v as u32) << mbo;
            let d = (mbo << 16) as u64;
            if d < msp as u64 {
                return false;
            }
            t.sym[s] = pack((d - msp as u64) as u32, total - v);
            if total <= 0x10000 - v {
                total = total + v;
            }
        }
        s = s + 1;
    }
    proof {
        assert((1u32 << log) as usize == size) by (bit_vector)
            requires size == 1usize << log, log <= 12;
    }
    let mask = (size - 1) as u32;
    t.mask = mask;
    true
}

/// One `FseC::sym` entry.
#[inline(always)]
fn pack(dnb: u32, dfs: i32) -> u64 {
    (dnb as u64) | ((dfs as u32 as u64) << 32)
}

/// An FSE encoder state.
pub struct FseState {
    pub v: u32,
}

/// `FSE_initCState2`: the state after the first (last encoded) symbol.
#[inline(always)]
pub fn fse_init(t: &FseC, s: u8) -> (r: FseState)
    requires
        t.wf(),
{
    let e = t.sym[s as usize];
    let dnb = lo32(e);
    let dfs = lo32(e >> 32);
    let nbo = lo32(((dnb as u64 + 0x8000) >> 16) as u64);
    let nbo = if nbo > 31 { 31 } else { nbo };
    let st = ((nbo as u64) << 16).wrapping_sub(dnb as u64);
    let x = lo32(st >> nbo).wrapping_add(dfs);
    FseState { v: t.next[lo12(x)] as u32 }
}

/// One step of `FSE_encodeSymbol`: the bits to write (the state's low
/// `nb` bits) and the next state. No branches: the shift is clamped to
/// the table's accuracy and the next index is masked into the table.
#[inline(always)]
pub fn fse_step(t: &FseC, st: &mut FseState, s: u8) -> (r: (u64, u32))
    requires
        t.wf(),
    ensures
        r.1 <= t.log,
{
    let e = t.sym[s as usize];
    let nb0 = lo32((st.v as u64 + lo32(e) as u64) >> 16);
    let nb = if nb0 > t.log { t.log } else { nb0 };
    let v = st.v as u64;
    let x = (st.v >> nb).wrapping_add(lo32(e >> 32)) & t.mask;
    st.v = t.next[lo12(x)] as u32;
    (v, nb)
}

/// `FSE_encodeSymbol`.
#[inline(always)]
pub fn fse_enc(t: &FseC, st: &mut FseState, s: u8, bw: &mut Bits, out: &mut Vec<u8>)
    requires
        t.wf(),
        old(bw).n < 64,
    ensures
        final(bw).n < 64,
        grew(old(out)@, final(out)@),
{
    let (v, nb) = fse_step(t, st, s);
    bw.add(out, v, nb);
}

/// `FSE_flushCState`.
#[inline(always)]
pub fn fse_flush(t: &FseC, st: &FseState, bw: &mut Bits, out: &mut Vec<u8>)
    requires
        t.wf(),
        old(bw).n < 64,
    ensures
        final(bw).n < 64,
        grew(old(out)@, final(out)@),
{
    bw.add(out, st.v as u64, t.log);
}

/// The cost in 1/256 bits of coding `count` with `norm` at accuracy `log`
/// (`None` if a symbol has no probability there).
pub fn fse_cost(count: &[u32], maxsv: usize, norm: &[i16], log: u32) -> (r: Option<u64>)
    requires
        maxsv < count@.len(),
        log <= 12,
{
    let mut c: u64 = 0;
    let lg = (log * 256) as u64;
    let mut s: usize = 0;
    while s <= maxsv
        invariant
            maxsv < count@.len(),
            s <= maxsv + 1,
            log <= 12,
            lg == (log * 256) as u64,
        decreases maxsv + 1 - s,
    {
        let k = count[s];
        if k > 0 {
            if s >= norm.len() {
                return None;
            }
            let v = norm[s];
            if v == 0 {
                return None;
            }
            let p: u32 = if v < 0 { 1 } else { v as u32 };
            let l = log2_256(p) as u64;
            let per = if lg > l { lg - l } else { 0 };
            proof {
                assert(per <= 12 * 256);
                assert((k as u64) * per <= 0xFFFF_FFFF * 3072) by (nonlinear_arith)
                    requires per <= 3072;
            }
            let add = (k as u64) * per;
            c = if c > 0xFFFF_FFFF_FFFF_FFFF - add { 0xFFFF_FFFF_FFFF_FFFF } else { c + add };
        }
        s = s + 1;
    }
    Some(c)
}

// ---------------------------------------------------------------------------
// The predefined distributions
// ---------------------------------------------------------------------------

pub const LL_DEF: [i16; 36] = [
    4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1, -1, -1, -1, -1,
];

pub const ML_DEF: [i16; 53] = [
    1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1,
];

pub const OF_DEF: [i16; 29] = [
    1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1,
];


pub const LL_CODE: [u8; 64] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 20, 20,
    21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
];

pub const ML_CODE: [u8; 128] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
    28, 29, 30, 31, 32, 32, 33, 33, 34, 34, 35, 35, 36, 36, 36, 36, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38,
    38, 38, 39, 39, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
    41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42,
    42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42,
];

pub const LL_BASE: [u32; 36] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28, 32, 40, 48, 64, 128, 256,
    512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
];

pub const LL_BITS: [u8; 36] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16,
];

pub const ML_BASE: [u32; 53] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
    31, 32, 33, 34, 35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051, 4099, 8195,
    16387, 32771, 65539,
];

pub const ML_BITS: [u8; 53] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1,
    1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
];

/// The literals length code of `ll` (at most 131071).
#[inline(always)]
pub fn ll_code(ll: u32) -> (r: u8)
    ensures
        r < 36,
{
    if ll < 64 {
        let c = LL_CODE[ll as usize];
        if c < 36 { c } else { 35 }
    } else {
        let c = hbit(ll) + 19;
        if c < 36 { c as u8 } else { 35 }
    }
}

/// The match length code of `ml` (at least 3).
#[inline(always)]
pub fn ml_code(ml: u32) -> (r: u8)
    ensures
        r < 53,
{
    let b = if ml >= 3 { ml - 3 } else { 0 };
    if b < 128 {
        let c = ML_CODE[b as usize];
        if c < 53 { c } else { 52 }
    } else {
        let c = hbit(b) + 36;
        if c < 53 { c as u8 } else { 52 }
    }
}

// ---------------------------------------------------------------------------
// Huffman codes
// ---------------------------------------------------------------------------

/// Sorts `a` in place, ascending (bottom-up merge sort).
#[verifier::loop_isolation(false)]
pub fn sort_u64(a: &mut Vec<u64>)
    ensures
        final(a)@.len() == old(a)@.len(),
{
    let n = a.len();
    let mut t: Vec<u64> = vec![0u64; n];
    let mut w: usize = 1;
    while w < n
        invariant
            a@.len() == n,
            t@.len() == n,
            w >= 1,
        decreases n - w,
    {
        let mut lo: usize = 0;
        while lo < n
            invariant
                a@.len() == n,
                t@.len() == n,
                lo <= n,
                w >= 1,
                w < n,
            decreases n - lo,
        {
            let mid = if n - lo > w { lo + w } else { n };
            let hi = if n - mid > w { mid + w } else { n };
            let mut i = lo;
            let mut j = mid;
            let mut k = lo;
            while k < hi
                invariant
                    lo <= i <= mid,
                    mid <= j <= hi,
                    hi <= n,
                    k == i + j - mid,
                    a@.len() == n,
                    t@.len() == n,
                decreases hi - k,
            {
                if i < mid && (j >= hi || a[i] <= a[j]) {
                    t.set(k, a[i]);
                    i = i + 1;
                } else {
                    t.set(k, a[j]);
                    j = j + 1;
                }
                k = k + 1;
            }
            lo = hi;
        }
        let mut k: usize = 0;
        while k < n
            invariant
                a@.len() == n,
                t@.len() == n,
                k <= n,
            decreases n - k,
        {
            a.set(k, t[k]);
            k = k + 1;
        }
        if w > n / 2 {
            break;
        }
        w = w * 2;
    }
}

pub const POW2: [u64; 16] = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768];

/// Huffman code lengths of at most `maxbits` for `freq` (a Huffman tree,
/// then lengths over `maxbits` cut as miniz does, so the code stays
/// complete). All zero when fewer than two symbols occur.
#[verifier::loop_isolation(false)]
pub fn huf_lens(freq: &[u32], maxbits: usize) -> (r: Vec<u8>)
    requires
        freq@.len() <= 256,
        1 <= maxbits <= 15,
    ensures
        r@.len() == freq@.len(),
        forall|i: int| 0 <= i < r@.len() ==> r@[i] <= maxbits,
{
    let nsym = freq.len();
    let mut lens: Vec<u8> = vec![0u8; nsym];
    let mut keys: Vec<u64> = Vec::with_capacity(nsym);
    let mut s: usize = 0;
    while s < nsym
        invariant
            s <= nsym,
            lens@.len() == nsym,
            keys@.len() <= s,
            forall|i: int| 0 <= i < lens@.len() ==> lens@[i] <= maxbits,
        decreases nsym - s,
    {
        if freq[s] > 0 {
            keys.push(((freq[s] as u64) << 9u64) | s as u64);
        }
        s = s + 1;
    }
    sort_u64(&mut keys);
    let m = keys.len();
    if m < 2 {
        return lens;
    }
    let mut syms: Vec<usize> = Vec::with_capacity(m);
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            keys@.len() == m,
            syms@.len() == i,
            forall|k: int| 0 <= k < syms@.len() ==> #[trigger] syms@[k] < nsym,
        decreases m - i,
    {
        let sym = (keys[i] & 511) as usize;
        if sym >= nsym {
            return lens;
        }
        syms.push(sym);
        i = i + 1;
    }
    // The tree: leaves 0..m (in `syms` order), then internal nodes, each
    // made from the two lightest nodes left.
    let total = 2 * m - 1;
    let mut w: Vec<u64> = vec![0u64; total];
    let mut parent: Vec<usize> = vec![0usize; total];
    let mut k: usize = 0;
    while k < m
        invariant
            k <= m,
            w@.len() == total,
            forall|q: int| 0 <= q < k ==> #[trigger] w@[q] < 0x1_0000_0000,
        decreases m - k,
    {
        w.set(k, freq[syms[k]] as u64);
        k = k + 1;
    }
    let mut leaf: usize = 0;
    let mut node: usize = m;
    let mut k: usize = m;
    while k < total
        invariant
            m <= k <= total,
            leaf <= m,
            m <= node <= k,
            w@.len() == total,
            parent@.len() == total,
            forall|q: int| 0 <= q < k ==> #[trigger] w@[q] <= 0x4_0000_0000_0000,
        decreases total - k,
    {
        let mut pair = [0usize; 2];
        let mut t: usize = 0;
        while t < 2
            invariant
                t <= 2,
                leaf <= m,
                m <= node <= k,
                k < total,
                forall|z: int| 0 <= z < t ==> #[trigger] pair@[z] < k,
            decreases 2 - t,
        {
            if leaf < m && (node >= k || w[leaf] <= w[node]) {
                pair[t] = leaf;
                leaf = leaf + 1;
            } else if node < k {
                pair[t] = node;
                node = node + 1;
            } else {
                return lens;
            }
            t = t + 1;
        }
        let a0 = w[pair[0]];
        let a1 = w[pair[1]];
        let sum = if a0 + a1 > 0x4_0000_0000_0000 { 0x4_0000_0000_0000 } else { a0 + a1 };
        w.set(k, sum);
        parent.set(pair[0], k);
        parent.set(pair[1], k);
        k = k + 1;
    }
    // Depths, from the root down.
    let mut depth = parent;
    depth.set(total - 1, 0);
    let mut x = total - 1;
    while x > 0
        invariant
            x < total,
            depth@.len() == total,
        decreases x,
    {
        x = x - 1;
        let px = depth[x];
        if px > x && px < total && depth[px] < total {
            depth.set(x, depth[px] + 1);
        } else {
            depth.set(x, total);
        }
    }
    // How many codes of each length, the long ones cut to `maxbits`.
    let mut count = [0u64; 16];
    let mut q: usize = 0;
    while q < m
        invariant
            q <= m,
            depth@.len() == total,
            forall|z: int| 0 <= z < 16 ==> #[trigger] count@[z] <= q,
        decreases m - q,
    {
        let mut d = depth[q];
        if d > maxbits {
            d = maxbits;
        }
        if d == 0 {
            d = 1;
        }
        count[d] = count[d] + 1;
        q = q + 1;
    }
    let mut kraft: u64 = 0;
    let mut l: usize = 1;
    while l <= maxbits
        invariant
            1 <= l <= maxbits + 1,
        decreases maxbits + 1 - l,
    {
        let sh = (maxbits - l) as u64;
        proof {
            assert(1u64 << sh <= 32768) by (bit_vector)
                requires sh <= 15;
        }
        let p = 1u64 << sh;
        kraft = kraft.wrapping_add(count[l].wrapping_mul(p));
        l = l + 1;
    }
    let full: u64 = POW2[maxbits];
    while kraft > full
        invariant
            1 <= maxbits <= 15,
        decreases kraft,
    {
        if count[maxbits] == 0 {
            return lens;
        }
        count[maxbits] = count[maxbits] - 1;
        let mut i = maxbits - 1;
        while i > 0
            invariant
                i < maxbits <= 15,
            decreases i,
        {
            if count[i] > 0 && count[i + 1] < 0x1_0000 && count[maxbits] < 0x1_0000 {
                count[i] = count[i] - 1;
                count[i + 1] = count[i + 1] + 2;
                break;
            }
            i = i - 1;
        }
        kraft = kraft - 1;
    }
    // The longest codes go to the rarest symbols.
    let mut idx: usize = 0;
    let mut l = maxbits;
    while l > 0
        invariant
            l <= maxbits <= 15,
            idx <= m,
            lens@.len() == nsym,
            forall|i: int| 0 <= i < lens@.len() ==> lens@[i] <= maxbits,
        decreases l,
    {
        let mut c = count[l];
        while c > 0 && idx < m
            invariant
                idx <= m,
                1 <= l <= maxbits,
                lens@.len() == nsym,
                forall|i: int| 0 <= i < lens@.len() ==> lens@[i] <= maxbits,
            decreases c,
        {
            lens.set(syms[idx], l as u8);
            idx = idx + 1;
            c = c - 1;
        }
        l = l - 1;
    }
    lens
}

/// A Huffman code for bytes: lengths and code values.
pub struct HufC {
    pub log: u32,
    pub lens: Vec<u8>,
    pub codes: Vec<u16>,
    pub w: Vec<u8>,
    /// The largest symbol that occurs.
    pub maxsym: usize,
}

impl HufC {
    pub open spec fn wf(&self) -> bool {
        &&& self.lens@.len() == 256
        &&& self.codes@.len() == 256
        &&& self.w@.len() == 256
        &&& self.maxsym < 256
        &&& forall|i: int| 0 <= i < 256 ==> self.lens@[i] <= 12
    }
}

/// The Huffman code for the counts `cnt` (256 of them), with weights and
/// canonical code values as the decoder assigns them: symbols by weight,
/// then by value.
#[verifier::loop_isolation(false)]
pub fn huf_build(cnt: &[u32], maxbits: usize) -> (r: Option<HufC>)
    requires
        cnt@.len() == 256,
        1 <= maxbits <= 11,
    ensures
        r matches Some(c) ==> c.wf(),
{
    let lens = huf_lens(cnt, maxbits);
    let mut log: u32 = 0;
    let mut maxsym: usize = 0;
    let mut s: usize = 0;
    while s < 256
        invariant
            s <= 256,
            lens@.len() == 256,
            log <= maxbits,
            maxsym < 256,
            forall|i: int| 0 <= i < 256 ==> lens@[i] <= maxbits,
            forall|i: int| 0 <= i < s ==> lens@[i] <= log,
        decreases 256 - s,
    {
        if lens[s] > 0 {
            maxsym = s;
        }
        if lens[s] as u32 > log {
            log = lens[s] as u32;
        }
        s = s + 1;
    }
    if log == 0 {
        return None;
    }
    let mut w: Vec<u8> = vec![0u8; 256];
    let mut s: usize = 0;
    while s < 256
        invariant
            s <= 256,
            lens@.len() == 256,
            w@.len() == 256,
            1 <= log <= maxbits,
            forall|i: int| 0 <= i < 256 ==> lens@[i] <= log,
        decreases 256 - s,
    {
        if lens[s] > 0 {
            w.set(s, (log + 1 - lens[s] as u32) as u8);
        }
        s = s + 1;
    }
    let mut codes: Vec<u16> = vec![0u16; 256];
    let mut row: u32 = 0;
    let mut x: u32 = 1;
    while x <= log
        invariant
            1 <= x <= log + 1,
            log <= 11,
            codes@.len() == 256,
            w@.len() == 256,
        decreases log + 1 - x,
    {
        let mut s: usize = 0;
        while s < 256
            invariant
                s <= 256,
                codes@.len() == 256,
                w@.len() == 256,
                1 <= x <= log,
            decreases 256 - s,
        {
            if w[s] as u32 == x {
                let xm = x - 1;
                codes.set(s, lo16(((row >> xm) & 0xFFFF) as u64));
                row = row.wrapping_add(1u32 << xm);
            }
            s = s + 1;
        }
        x = x + 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < 256 ==> lens@[i] <= 12);
    }
    if row != (1u32 << log) {
        return None;
    }
    Some(HufC { log, lens, codes, w, maxsym })
}

/// The cost in bits of the literals with code `c`.
pub fn huf_bits(cnt: &[u32], c: &HufC) -> (r: u64)
    requires
        cnt@.len() == 256,
        c.wf(),
{
    let mut t: u64 = 0;
    let mut s: usize = 0;
    while s < 256
        invariant
            s <= 256,
            c.wf(),
            cnt@.len() == 256,
            t <= s * 0xFFFF_FFFF * 12,
        decreases 256 - s,
    {
        proof {
            assert((cnt@[s as int] as u64) * (c.lens@[s as int] as u64) <= 0xFFFF_FFFF * 12) by (nonlinear_arith)
                requires c.lens@[s as int] <= 12;
        }
        t = t + (cnt[s] as u64) * (c.lens[s] as u64);
        s = s + 1;
    }
    t
}

/// The weights of `c`, FSE-compressed (libzstd's `HUF_compressWeights`),
/// appended to `out`. `false`: not possible or not smaller.
#[verifier::loop_isolation(false)]
pub fn huf_fse_weights(c: &HufC, out: &mut Vec<u8>) -> (ok: bool)
    requires
        c.wf(),
    ensures
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    proof {
        lemma_grew_refl(out@);
    }
    let n = c.maxsym;
    if n <= 2 {
        return false;
    }
    let mut hist: Vec<u32> = vec![0u32; 13];
    let mut maxw: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            hist@.len() == 13,
            maxw <= 12,
            forall|k: int| 0 <= k < 13 ==> hist@[k] <= i,
        decreases n - i,
    {
        let x = c.w[i] as usize;
        if x <= 12 {
            hist.set(x, hist[x] + 1);
            if x > maxw {
                maxw = x;
            }
        }
        i = i + 1;
    }
    let mut most: u32 = 0;
    let mut k: usize = 0;
    while k < 13
        invariant
            k <= 13,
            hist@.len() == 13,
        decreases 13 - k,
    {
        if hist[k] > most {
            most = hist[k];
        }
        k = k + 1;
    }
    if most as usize == n || most <= 1 {
        return false;
    }
    let log = fse_log(6, n as u32, maxw as u32);
    let norm = match normalize(&hist, n as u32, maxw, log, false) {
        Some(v) => v,
        None => return false,
    };
    let mut ct = FseC::new();
    if !build_ctable(&norm, log, &mut ct) {
        return false;
    }
    if !write_ncount(out, &norm, log) {
        return false;
    }
    let ghost o1 = out@;
    // Two states take turns: symbol `i` goes with the first state when `i`
    // is even. The last two symbols start the states.
    let mut bw = Bits::new();
    let mut s1 = FseState { v: 0 };
    let mut s2 = FseState { v: 0 };
    let mut i = n;
    let mut init1 = false;
    let mut init2 = false;
    proof {
        lemma_grew_refl(out@);
    }
    while i > 0
        invariant
            i <= n,
            bw.n < 64,
            ct.wf(),
            grew(o1, out@),
        decreases i,
    {
        i = i - 1;
        let sym = c.w[i];
        let ghost o2 = out@;
        if i % 2 == 0 {
            if !init1 {
                s1 = fse_init(&ct, sym);
                init1 = true;
                proof {
                    lemma_grew_refl(out@);
                }
            } else {
                fse_enc(&ct, &mut s1, sym, &mut bw, out);
            }
        } else {
            if !init2 {
                s2 = fse_init(&ct, sym);
                init2 = true;
                proof {
                    lemma_grew_refl(out@);
                }
            } else {
                fse_enc(&ct, &mut s2, sym, &mut bw, out);
            }
        }
        proof {
            lemma_grew_trans(o1, o2, out@);
        }
    }
    let ghost o3 = out@;
    fse_flush(&ct, &s2, &mut bw, out);
    let ghost o4 = out@;
    fse_flush(&ct, &s1, &mut bw, out);
    let ghost o5 = out@;
    bw.close(out);
    proof {
        lemma_grew_trans(o1, o3, o4);
        lemma_grew_trans(o1, o4, o5);
        lemma_grew_trans(o1, o5, out@);
        lemma_grew_trans(o0, o1, out@);
    }
    true
}

/// The tree description of `c` (§4.2.1), appended to `out`.
#[verifier::loop_isolation(false)]
pub fn huf_desc(c: &HufC, out: &mut Vec<u8>, tmp: &mut Vec<u8>) -> (ok: bool)
    requires
        c.wf(),
    ensures
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    let n = c.maxsym;
    tmp.clear();
    let fse = huf_fse_weights(c, tmp);
    let direct = (n + 1) / 2 + 1;
    if fse && tmp.len() >= 1 && tmp.len() < 128 && (n > 128 || tmp.len() + 1 < direct) {
        push(out, tmp.len() as u8);
        let ghost o1 = out@;
        out.extend_from_slice(tmp.as_slice());
        proof {
            assert(out@.subrange(0, o1.len() as int) =~= o1);
            lemma_grew_trans(o0, o1, out@);
        }
        return true;
    }
    if n > 128 || n == 0 {
        proof {
            lemma_grew_refl(out@);
        }
        return false;
    }
    push(out, (127 + n) as u8);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n + 1,
            n <= 128,
            grew(o0, out@),
        decreases n + 1 - i,
    {
        let wa = c.w[i];
        let wb = if i + 1 < n { c.w[i + 1] } else { 0 };
        let hi = wa & 15;
        let lo = wb & 15;
        proof {
            assert(hi < 16 && lo < 16) by (bit_vector)
                requires hi == wa & 15, lo == wb & 15;
        }
        let ghost o1 = out@;
        push(out, hi * 16 + lo);
        proof {
            lemma_grew_trans(o0, o1, out@);
        }
        i = i + 2;
    }
    true
}

/// One Huffman stream of `lits[a..b]`, the last symbol first.
#[verifier::loop_isolation(false)]
pub fn huf_stream(c: &HufC, lits: &[u8], a: usize, b: usize, out: &mut Vec<u8>)
    requires
        c.wf(),
        a <= b <= lits@.len(),
    ensures
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    proof {
        lemma_grew_refl(out@);
    }
    let mut bw = Bits::new();
    let mut i = b;
    while i > a
        invariant
            a <= i <= b,
            bw.n < 64,
            grew(o0, out@),
        decreases i,
    {
        i = i - 1;
        let s = lits[i] as usize;
        let ghost o1 = out@;
        bw.add_raw(out, c.codes[s] as u64, c.lens[s] as u32);
        proof {
            lemma_grew_trans(o0, o1, out@);
        }
    }
    let ghost o1 = out@;
    bw.close(out);
    proof {
        lemma_grew_trans(o0, o1, out@);
    }
}

// ---------------------------------------------------------------------------
// The literals section (§3.1.1.3.1)
// ---------------------------------------------------------------------------

/// Pushes the low `n` bytes of `x`, little-endian.
pub fn push_n(out: &mut Vec<u8>, x: u64, n: u32)
    requires
        n <= 8,
    ensures
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    proof {
        lemma_grew_refl(out@);
    }
    let mut k: u32 = 0;
    while k < n
        invariant
            k <= n <= 8,
            grew(o0, out@),
        decreases n - k,
    {
        let ghost o1 = out@;
        push(out, (x >> (8 * k)) as u8);
        proof {
            lemma_grew_trans(o0, o1, out@);
        }
        k = k + 1;
    }
}

/// The header of raw (`ty` 0) or RLE (`ty` 1) literals of size `n`.
pub fn plain_lits_header(out: &mut Vec<u8>, n: usize, ty: u64)
    requires
        n < 0x10_0000,
        ty < 2,
    ensures
        grew(old(out)@, final(out)@),
{
    if n < 32 {
        push_n(out, ((n as u64) << 3) | ty, 1);
    } else if n < 4096 {
        push_n(out, ((n as u64) << 4) | (1 << 2) | ty, 2);
    } else {
        push_n(out, ((n as u64) << 4) | (3 << 2) | ty, 3);
    }
}

/// Raw literals.
pub fn raw_lits(out: &mut Vec<u8>, lits: &[u8])
    requires
        lits@.len() < 0x10_0000,
    ensures
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    plain_lits_header(out, lits.len(), 0);
    let ghost o1 = out@;
    out.extend_from_slice(lits);
    proof {
        assert(out@.subrange(0, o1.len() as int) =~= o1);
        lemma_grew_trans(o0, o1, out@);
    }
}

/// Scratch space for the literals section.
pub struct LitScratch {
    pub cnt: Vec<u32>,
    pub desc: Vec<u8>,
    pub tmp: Vec<u8>,
    pub streams: Vec<u8>,
}

impl LitScratch {
    pub fn new() -> (r: LitScratch)
        ensures
            r.cnt@.len() == 256,
    {
        LitScratch { cnt: vec![0u32; 256], desc: Vec::new(), tmp: Vec::new(), streams: Vec::new() }
    }
}

/// The literals section for `lits`, Huffman-coded when that is smaller.
#[verifier::loop_isolation(false)]
pub fn put_lits(out: &mut Vec<u8>, lits: &[u8], sc: &mut LitScratch, maxbits: usize)
    requires
        lits@.len() < 0x10_0000,
        old(sc).cnt@.len() == 256,
        1 <= maxbits <= 11,
    ensures
        grew(old(out)@, final(out)@),
        final(sc).cnt@.len() == 256,
{
    let ghost o0 = out@;
    let n = lits.len();
    if n < 64 {
        raw_lits(out, lits);
        return;
    }
    let mut k: usize = 0;
    while k < 256
        invariant
            k <= 256,
            sc.cnt@.len() == 256,
            forall|q: int| 0 <= q < k ==> #[trigger] sc.cnt@[q] == 0,
        decreases 256 - k,
    {
        sc.cnt.set(k, 0);
        k = k + 1;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            sc.cnt@.len() == 256,
            forall|q: int| 0 <= q < 256 ==> #[trigger] sc.cnt@[q] <= i,
        decreases n - i,
    {
        let b = lits[i] as usize;
        sc.cnt.set(b, sc.cnt[b] + 1);
        i = i + 1;
    }
    let mut distinct: usize = 0;
    let mut k: usize = 0;
    while k < 256
        invariant
            k <= 256,
            distinct <= k,
            sc.cnt@.len() == 256,
        decreases 256 - k,
    {
        if sc.cnt[k] > 0 {
            distinct = distinct + 1;
        }
        k = k + 1;
    }
    if distinct == 1 {
        plain_lits_header(out, n, 1);
        let ghost o1 = out@;
        push(out, lits[0]);
        proof {
            lemma_grew_trans(o0, o1, out@);
        }
        return;
    }
    let c = match huf_build(sc.cnt.as_slice(), maxbits) {
        Some(c) => c,
        None => {
            raw_lits(out, lits);
            return;
        },
    };
    // Rough check before coding: the bits alone must save something.
    let bits = huf_bits(sc.cnt.as_slice(), &c);
    if bits / 8 + 16 >= n as u64 {
        raw_lits(out, lits);
        return;
    }
    sc.desc.clear();
    if !huf_desc(&c, &mut sc.desc, &mut sc.tmp) {
        raw_lits(out, lits);
        return;
    }
    sc.streams.clear();
    let single = n < 256;
    if single {
        huf_stream(&c, lits, 0, n, &mut sc.streams);
    } else {
        let seg = (n + 3) / 4;
        let ghost s0 = sc.streams@;
        push_n(&mut sc.streams, 0, 6);
        let a1 = sc.streams.len();
        huf_stream(&c, lits, 0, seg, &mut sc.streams);
        let a2 = sc.streams.len();
        huf_stream(&c, lits, seg, 2 * seg, &mut sc.streams);
        let a3 = sc.streams.len();
        huf_stream(&c, lits, 2 * seg, 3 * seg, &mut sc.streams);
        let a4 = sc.streams.len();
        huf_stream(&c, lits, 3 * seg, n, &mut sc.streams);
        let l1 = a2 - a1;
        let l2 = a3 - a2;
        let l3 = a4 - a3;
        if l1 > 0xFFFF || l2 > 0xFFFF || l3 > 0xFFFF || sc.streams.len() < 6 {
            raw_lits(out, lits);
            return;
        }
        sc.streams.set(0, lo8((l1 & 255) as u64));
        sc.streams.set(1, lo8((l1 >> 8) as u64));
        sc.streams.set(2, lo8((l2 & 255) as u64));
        sc.streams.set(3, lo8((l2 >> 8) as u64));
        sc.streams.set(4, lo8((l3 & 255) as u64));
        sc.streams.set(5, lo8((l3 >> 8) as u64));
    }
    if sc.desc.len() >= 262144 || sc.streams.len() >= 262144 {
        raw_lits(out, lits);
        return;
    }
    let csize = sc.desc.len() + sc.streams.len();
    let big = if csize > n { csize } else { n };
    let lh: u32 = if big < 1024 {
        3
    } else if big < 16384 {
        4
    } else {
        5
    };
    if csize + lh as usize + 8 >= n || csize >= 262144 || (single && lh != 3) {
        raw_lits(out, lits);
        return;
    }
    let sf: u64 = if lh == 3 {
        if single { 0 } else { 1 }
    } else if lh == 4 {
        2
    } else {
        3
    };
    let shift: u64 = if lh == 3 {
        14
    } else if lh == 4 {
        18
    } else {
        22
    };
    let hv: u64 = 2 | (sf << 2) | ((n as u64) << 4) | ((csize as u64) << shift);
    push_n(out, hv, lh);
    let ghost o1 = out@;
    out.extend_from_slice(sc.desc.as_slice());
    let ghost o2 = out@;
    out.extend_from_slice(sc.streams.as_slice());
    proof {
        assert(o2.subrange(0, o1.len() as int) =~= o1);
        assert(out@.subrange(0, o2.len() as int) =~= o2);
        lemma_grew_trans(o0, o1, o2);
        lemma_grew_trans(o0, o2, out@);
    }
}

// ---------------------------------------------------------------------------
// The sequences section (§3.1.1.3.2)
// ---------------------------------------------------------------------------

/// How one kind of code (literals lengths, offsets, match lengths) is
/// coded: mode 0 predefined, 1 RLE, 2 an FSE table (the table itself is
/// in `SeqScratch`).
pub struct KindEnc {
    pub mode: u8,
    pub sym: u8,
}

/// Counts codes `c` into `hist` (cleared first, `nmax` long). Returns the
/// largest code seen and its count.
#[verifier::loop_isolation(false)]
fn count_codes(c: &[u8], hist: &mut Vec<u32>, nmax: usize) -> (r: (usize, u32))
    requires
        1 <= nmax <= 256,
        c@.len() < 0x1_0000_0000,
    ensures
        final(hist)@.len() == nmax,
        r.0 < nmax,
{
    hist.clear();
    let mut k: usize = 0;
    while k < nmax
        invariant
            k <= nmax,
            hist@.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] hist@[q] == 0,
        decreases nmax - k,
    {
        hist.push(0);
        k = k + 1;
    }
    let mut i: usize = 0;
    while i < c.len()
        invariant
            i <= c@.len(),
            hist@.len() == nmax,
            forall|q: int| 0 <= q < nmax ==> #[trigger] hist@[q] <= i,
        decreases c@.len() - i,
    {
        let x = c[i] as usize;
        if x < nmax {
            hist.set(x, hist[x] + 1);
        }
        i = i + 1;
    }
    let mut mx: usize = 0;
    let mut most: u32 = 0;
    let mut k: usize = 0;
    while k < nmax
        invariant
            k <= nmax,
            hist@.len() == nmax,
            mx < nmax,
        decreases nmax - k,
    {
        if hist[k] > 0 {
            mx = k;
        }
        if hist[k] > most {
            most = hist[k];
        }
        k = k + 1;
    }
    (mx, most)
}

/// Chooses the coding of one kind and writes its table description, if
/// any, to `out`. `def`/`dlog`: the predefined distribution; `maxlog`: the
/// largest accuracy log.
#[verifier::loop_isolation(false)]
fn choose_kind(
    codes: &[u8],
    hist: &mut Vec<u32>,
    nmax: usize,
    def: &[i16],
    dlog: u32,
    maxlog: u32,
    out: &mut Vec<u8>,
    tmp: &mut Vec<u8>,
    ct: &mut FseC,
) -> (r: Option<KindEnc>)
    requires
        1 <= nmax <= 256,
        codes@.len() >= 1,
        codes@.len() < 0x20000,
        1 <= def@.len() <= 256,
        5 <= dlog <= 12,
        5 <= maxlog <= 12,
    ensures
        grew(old(out)@, final(out)@),
        final(ct).wf(),
        r matches Some(k) ==> (k.mode != 1 ==> final(ct).log >= 5),
{
    let ghost o0 = out@;
    proof {
        lemma_grew_refl(out@);
    }
    let n = codes.len();
    let (mx, most) = count_codes(codes, hist, nmax);
    if !build_ctable(def, dlog, ct) {
        return None;
    }
    if most as usize == n {
        if n <= 2 && mx < def.len() {
            return Some(KindEnc { mode: 0, sym: 0 });
        }
        push(out, mx as u8);
        // An RLE kind writes no state bits: a table of accuracy 0 makes
        // every step write none, so the sequence loop needs no branch.
        ct.log = 0;
        ct.mask = 0;
        return Some(KindEnc { mode: 1, sym: mx as u8 });
    }
    let dcost: Option<u64> = if mx < def.len() {
        fse_cost(hist.as_slice(), mx, def, dlog)
    } else {
        None
    };
    if n < 2 {
        return None;
    }
    let log = fse_log(maxlog, n as u32, mx as u32);
    let norm = match normalize(hist.as_slice(), n as u32, mx, log, n >= 2048) {
        Some(v) => v,
        None => {
            if dcost.is_some() {
                return Some(KindEnc { mode: 0, sym: 0 });
            }
            return None;
        },
    };
    tmp.clear();
    if !write_ncount(tmp, norm.as_slice(), log) {
        if dcost.is_some() {
            return Some(KindEnc { mode: 0, sym: 0 });
        }
        return None;
    }
    let ccost = match fse_cost(hist.as_slice(), mx, norm.as_slice(), log) {
        Some(c) => c,
        None => return None,
    };
    let hcost = (tmp.len() as u64).wrapping_mul(2048);
    if let Some(dc) = dcost {
        if dc <= ccost.wrapping_add(hcost) {
            return Some(KindEnc { mode: 0, sym: 0 });
        }
    }
    if !build_ctable(norm.as_slice(), log, ct) {
        return None;
    }
    out.extend_from_slice(tmp.as_slice());
    proof {
        assert(out@.subrange(0, o0.len() as int) =~= o0);
    }
    Some(KindEnc { mode: 2, sym: 0 })
}

/// Scratch space for the sequences section.
pub struct SeqScratch {
    pub llc: Vec<u8>,
    pub mlc: Vec<u8>,
    pub ofc: Vec<u8>,
    pub hist: Vec<u32>,
    pub tmp: Vec<u8>,
    /// The tables of the literals lengths, offsets and match lengths.
    pub lct: FseC,
    pub oct: FseC,
    pub mct: FseC,
}

impl SeqScratch {
    pub fn new() -> (r: SeqScratch) {
        SeqScratch {
            llc: Vec::new(),
            mlc: Vec::new(),
            ofc: Vec::new(),
            hist: Vec::new(),
            tmp: Vec::new(),
            lct: FseC::new(),
            oct: FseC::new(),
            mct: FseC::new(),
        }
    }
}

/// The sequences section: literals lengths `ll`, match lengths `ml` and
/// offset values `ob` (1 to 3 for repeat offsets, offset + 3 otherwise).
#[verifier::loop_isolation(false)]
pub fn put_seqs(out: &mut Vec<u8>, ll: &[u32], ml: &[u32], ob: &[u32], sc: &mut SeqScratch) -> (ok: bool)
    requires
        ll@.len() == ml@.len(),
        ll@.len() == ob@.len(),
    ensures
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    proof {
        lemma_grew_refl(out@);
    }
    let n = ll.len();
    if n >= 0x20000 {
        return false;
    }
    if n < 128 {
        push(out, n as u8);
    } else if n < 0x7F00 {
        push_n(out, ((n / 256 + 128) as u64) | (((n % 256) as u64) << 8), 2);
    } else {
        push_n(out, 255 | (((n - 0x7F00) as u64) << 8), 3);
    }
    if n == 0 {
        return true;
    }
    let ghost o1 = out@;
    sc.llc.clear();
    sc.mlc.clear();
    sc.ofc.clear();
    reserve_spare(&mut sc.llc, n);
    reserve_spare(&mut sc.mlc, n);
    reserve_spare(&mut sc.ofc, n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            sc.llc@.len() == i,
            sc.mlc@.len() == i,
            sc.ofc@.len() == i,
            verilith_core::spare::spare(sc.llc) >= n - i,
            verilith_core::spare::spare(sc.mlc) >= n - i,
            verilith_core::spare::spare(sc.ofc) >= n - i,
        decreases n - i,
    {
        push_spare(&mut sc.llc, ll_code(ll[i]));
        push_spare(&mut sc.mlc, ml_code(ml[i]));
        push_spare(&mut sc.ofc, hbit(ob[i]) as u8);
        i = i + 1;
    }
    // The modes byte is written once the modes are known.
    let mpos = out.len();
    push(out, 0);
    let ghost o2 = out@;
    proof {
        lemma_grew_trans(o0, o1, o2);
    }
    let lle = match choose_kind(sc.llc.as_slice(), &mut sc.hist, 36, &LL_DEF, 6, 9, out, &mut sc.tmp, &mut sc.lct) {
        Some(k) => k,
        None => {
            proof {
                lemma_grew_trans(o0, o2, out@);
            }
            return false;
        },
    };
    let ghost o3 = out@;
    proof {
        lemma_grew_trans(o0, o2, o3);
    }
    let ofe = match choose_kind(sc.ofc.as_slice(), &mut sc.hist, 32, &OF_DEF, 5, 8, out, &mut sc.tmp, &mut sc.oct) {
        Some(k) => k,
        None => {
            proof {
                lemma_grew_trans(o0, o3, out@);
            }
            return false;
        },
    };
    let ghost o4 = out@;
    proof {
        lemma_grew_trans(o0, o3, o4);
    }
    let mle = match choose_kind(sc.mlc.as_slice(), &mut sc.hist, 53, &ML_DEF, 6, 9, out, &mut sc.tmp, &mut sc.mct) {
        Some(k) => k,
        None => {
            proof {
                lemma_grew_trans(o0, o4, out@);
            }
            return false;
        },
    };
    let ghost o5 = out@;
    let modes: u8 = (lle.mode << 6) | (ofe.mode << 4) | (mle.mode << 2);
    out.set(mpos, modes);
    proof {
        lemma_grew_trans(o0, o1, o2);
        lemma_grew_trans(o0, o2, o3);
        lemma_grew_trans(o0, o3, o4);
        lemma_grew_trans(o0, o4, o5);
        assert(out@.subrange(0, o0.len() as int) =~= o0) by {
            assert(o5.subrange(0, o0.len() as int) == o0);
        }
    }
    let ghost o6 = out@;
    // The bitstream: the last sequence first.
    let mut bw = Bits::new();
    let last = n - 1;
    let mut sll = fse_init(&sc.lct, sc.llc[last]);
    let mut sof = fse_init(&sc.oct, sc.ofc[last]);
    let mut sml = fse_init(&sc.mct, sc.mlc[last]);
    proof {
        lemma_grew_refl(out@);
    }
    extra_bits(&mut bw, out, sc.llc[last], sc.mlc[last], sc.ofc[last], ll[last], ml[last], ob[last]);
    let ghost o7 = out@;
    // Room for every sequence: two stores of at most 7 bytes each, so no
    // capacity check in the loop.
    reserve_spare(out, 16 * last + 8);
    assert(out@ == o7);
    let llc = sc.llc.as_slice();
    let mlc = sc.mlc.as_slice();
    let ofc = sc.ofc.as_slice();
    let mut i = last;
    while i > 0
        invariant
            i <= last,
            bw.n < 64,
            sc.lct.wf(),
            sc.oct.wf(),
            sc.mct.wf(),
            grew(o6, out@),
            verilith_core::spare::spare(*out) >= 16 * i + 8,
        decreases i,
    {
        i = i - 1;
        let ghost a = out@;
        // libzstd's order: offset, match length, literals length states,
        // then the literals length, match length and offset extra bits.
        bw.flush_s(out);
        let (v, nb) = fse_step(&sc.oct, &mut sof, ofc[i]);
        bw.put(v, nb);
        let (v, nb) = fse_step(&sc.mct, &mut sml, mlc[i]);
        bw.put(v, nb);
        let (v, nb) = fse_step(&sc.lct, &mut sll, llc[i]);
        bw.put(v, nb);
        let lc = llc[i] as usize;
        let mc = mlc[i] as usize;
        let lc = if lc < 36 { lc } else { 35 };
        let mc = if mc < 53 { mc } else { 52 };
        let lb = LL_BASE[lc];
        let mb = ML_BASE[mc];
        let lbn = LL_BITS[lc] as u32;
        let mbn = ML_BITS[mc] as u32;
        let lbn = if lbn > 16 { 16 } else { lbn };
        let mbn = if mbn > 16 { 16 } else { mbn };
        bw.put_raw(ll[i].wrapping_sub(lb) as u64, lbn);
        let ghost a2 = out@;
        bw.flush_s(out);
        bw.put_raw(ml[i].wrapping_sub(mb) as u64, mbn);
        let oc = ofc[i] as u32;
        let oc = if oc <= 31 { oc } else { 31 };
        bw.put(ob[i] as u64, oc);
        proof {
            lemma_grew_trans(a, a2, out@);
            lemma_grew_trans(o6, a, out@);
        }
    }
    let ghost b = out@;
    flush3(&mut bw, out, &lle, &ofe, &mle, &sc.lct, &sc.oct, &sc.mct, &sll, &sof, &sml);
    let ghost b2 = out@;
    bw.close(out);
    proof {
        lemma_grew_trans(b, b2, out@);
        lemma_grew_trans(o6, b, out@);
        lemma_grew_trans(o0, o6, out@);
    }
    true
}

/// The final states: match length, offset, literals length.
#[inline(always)]
fn flush3(
    bw: &mut Bits,
    out: &mut Vec<u8>,
    lle: &KindEnc,
    ofe: &KindEnc,
    mle: &KindEnc,
    lct: &FseC,
    oct: &FseC,
    mct: &FseC,
    sll: &FseState,
    sof: &FseState,
    sml: &FseState,
)
    requires
        old(bw).n < 64,
        lct.wf(),
        oct.wf(),
        mct.wf(),
    ensures
        final(bw).n < 64,
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    proof {
        lemma_grew_refl(out@);
    }
    if mle.mode != 1 {
        fse_flush(&mct, sml, bw, out);
    }
    let ghost o1 = out@;
    if ofe.mode != 1 {
        fse_flush(&oct, sof, bw, out);
    }
    let ghost o2 = out@;
    if lle.mode != 1 {
        fse_flush(&lct, sll, bw, out);
    }
    proof {
        lemma_grew_refl(o1);
        lemma_grew_refl(o2);
        lemma_grew_trans(o0, o1, o2);
        lemma_grew_trans(o0, o2, out@);
    }
}

/// The extra bits of one sequence: literals length, match length, offset.
#[inline(always)]
fn extra_bits(bw: &mut Bits, out: &mut Vec<u8>, llc: u8, mlc: u8, ofc: u8, ll: u32, ml: u32, ob: u32)
    requires
        old(bw).n < 64,
    ensures
        final(bw).n < 64,
        grew(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    let lc = if (llc as usize) < 36 { llc as usize } else { 35 };
    let mc = if (mlc as usize) < 53 { mlc as usize } else { 52 };
    let lb = LL_BASE[lc];
    let mb = ML_BASE[mc];
    bw.add_raw(out, (if ll >= lb { ll - lb } else { 0 }) as u64, LL_BITS[lc] as u32);
    let ghost o1 = out@;
    bw.add_raw(out, (if ml >= mb { ml - mb } else { 0 }) as u64, ML_BITS[mc] as u32);
    let ghost o2 = out@;
    let oc = if ofc <= 31 { ofc as u32 } else { 31 };
    bw.add(out, ob as u64, oc);
    proof {
        lemma_grew_refl(o1);
        lemma_grew_refl(o2);
        lemma_grew_trans(o0, o1, o2);
        lemma_grew_trans(o0, o2, out@);
    }
}

} // verus!
