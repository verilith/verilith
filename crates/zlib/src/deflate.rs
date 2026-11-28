//! A verified DEFLATE compressor. Whatever the input, the output inflates
//! back to it under the same specification the decompressor is proven
//! against (`spec::inflate`, `spec::zlib_decompress`,
//! `spec::gzip_decompress`).
//!
//! The choices that only affect the compression ratio (which matches to
//! take, the Huffman code lengths) are made by ordinary code whose results
//! are checked before use: matches are compared byte by byte, and code
//! lengths go through `huffman::build`, which accepts exactly the lengths
//! the decoder accepts. A block whose codes fail the check is stored.
#[cfg(verus_only)]
use crate::bitwriter::*;
#[cfg(verus_only)]
use crate::dlemmas::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use crate::huffman::*;
#[cfg(verus_only)]
use crate::ilemmas::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
use verilith_core::sort::order_by;
use verilith_core::lz::eq_len;
#[cfg(verus_only)]
use verilith_core::sort::below;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use crate::bitwriter::{join, BitWriter};
use crate::dlemmas::Blk;
use crate::huffman::{build, reverse, Code, DIST_BASE, DIST_EXTRA, LEN_BASE, LEN_EXTRA};
use vstd::prelude::*;

verus! {

/// The length symbol (less 257) of each length from 3 to 258.
pub const LEN_SYM: [u8; 259] = [
    0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 12, 12, 13,
    13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17,
    17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20,
    20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
    21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23,
    23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25,
    25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25,
    25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26,
    26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
    27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28,
];

/// The distance symbol of distance `j + 1` for `j < 256`, and of distance
/// `128 * (j - 256) + 1` above (libdeflate's table: above 256, every distance
/// base is 1 more than a multiple of 128).
pub const DIST_SLOT: [u8; 512] = [
    0, 1, 2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
    9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
    13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
    14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
    14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 0, 0, 16, 17, 18, 18, 19, 19,
    20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25,
    25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26,
    26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27,
    27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
    28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
    28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
    28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29,
    29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29,
    29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29,
    29, 29, 29, 29, 29, 29, 29, 29,
];

pub proof fn lemma_len_sym()
    ensures
        forall|l: int| 3 <= l <= 258 ==> (#[trigger] LEN_SYM@[l]) as int == crate::dlemmas::lidx(l as nat),
{
    assert(forall|l: int| 3 <= l <= 258 ==> (#[trigger] LEN_SYM@[l]) as int == crate::dlemmas::lidx(l as nat)) by (compute);
}

pub proof fn lemma_dist_slot()
    ensures
        forall|j: int| 0 <= j < 256 ==> (#[trigger] DIST_SLOT@[j]) as int == crate::dlemmas::didx((j + 1) as nat),
        forall|j: int| 2 <= j < 256 ==> (#[trigger] DIST_SLOT@[256 + j]) as int == crate::dlemmas::didx((128 * j + 1) as nat),
{
    assert(forall|j: int| 0 <= j < 256 ==> (#[trigger] DIST_SLOT@[j]) as int == crate::dlemmas::didx((j + 1) as nat)) by (compute);
    assert(forall|j: int| 2 <= j < 256 ==> (#[trigger] DIST_SLOT@[256 + j]) as int == crate::dlemmas::didx((128 * j + 1) as nat)) by (compute);
}

/// Above 256, a distance has the symbol of the distance 1 more than the
/// multiple of 128 below it.
pub proof fn lemma_didx_128(d: nat)
    requires
        257 <= d <= 32768,
    ensures
        crate::dlemmas::didx(d) == crate::dlemmas::didx(128 * ((d - 1) as int / 128) as nat + 1),
{
    assert(forall|i: int| 0 <= i < 16 ==> #[trigger] dist_base()[i] <= 193) by (compute);
    assert(forall|i: int| 16 <= i < 30 ==> #[trigger] dist_base()[i] % 128 == 1) by (compute);
    lemma_tables();
    lemma_steps();
    lemma_didx(d);
    let i = crate::dlemmas::didx(d);
    let q = (d - 1) as int / 128;
    let d1 = 128 * q + 1;
    assert(q >= 2 && d1 <= d) by (nonlinear_arith)
        requires q == (d - 1) as int / 128, d >= 257, d1 == 128 * q + 1;
    if i >= 16 {
        let m = (dist_base()[i] - 1) as int / 128;
        assert(dist_base()[i] == 128 * m + 1);
        assert(m <= q) by (nonlinear_arith)
            requires 128 * m + 1 <= d, q == (d - 1) as int / 128, m >= 0;
    }
    assert(dist_base()[i] <= d1);
    if i < 29 {
        assert(dist_base()[i + 1] == dist_base()[i] + pow2(dist_extra()[i]));
    }
    lemma_idx_unique(dist_base(), dist_extra(), d1 as nat, 29, i);
}

/// The length symbol (less 257) for `len`.
pub fn len_index(len: u32) -> (r: usize)
    requires
        3 <= len <= 258,
    ensures
        r as int == crate::dlemmas::lidx(len as nat),
        r < 29,
{
    proof {
        lemma_len_sym();
        lemma_lidx(len as nat);
    }
    LEN_SYM[len as usize] as usize
}

/// The distance symbol for `d`.
pub fn dist_index(d: u32) -> (r: usize)
    requires
        1 <= d <= 32768,
    ensures
        r as int == crate::dlemmas::didx(d as nat),
        r < 30,
{
    proof {
        lemma_dist_slot();
        lemma_didx(d as nat);
    }
    if d <= 256 {
        DIST_SLOT[(d - 1) as usize] as usize
    } else {
        proof {
            lemma_didx_128(d as nat);
        }
        DIST_SLOT[256 + ((d - 1) / 128) as usize] as usize
    }
}

/// Checks code lengths the way the decoder does, and returns the code's
/// counts and first codes.
pub fn check_lens(code: &mut Code, lens: &[u8], single_ok: bool) -> (r: bool)
    requires
        lens@.len() <= 288,
    ensures
        r == valid_lens(lens@, single_ok),
        r ==> code_ok(*final(code), lens@),
{
    let mut tab = [0u32; 2];
    proof {
        lemma2_to64();
    }
    let (ok, _) = build(code, &mut tab, 1, lens, crate::huffman::ALPHA_CL, single_ok);
    ok
}

/// The canonical code of every symbol, bit-reversed for writing.
pub fn canon_codes(code: &Code, lens: &[u8]) -> (r: Vec<u32>)
    requires
        lens@.len() <= 288,
        valid_lens(lens@, true) || valid_lens(lens@, false),
        code_ok(*code, lens@),
    ensures
        r@.len() == lens@.len(),
        forall|s: int| 0 <= s < lens@.len() && 1 <= lens@[s] ==> #[trigger] r@[s] as nat == rev(canon(lens@, s), lens@[s] as nat),
{
    let ghost ls = lens@;
    let n = lens.len();
    let mut next = code.first;
    let mut r: Vec<u32> = Vec::with_capacity(n);
    let mut s: usize = 0;
    proof {
        assert forall|l: nat| 1 <= l <= 15 implies #[trigger] next@[l as int] as nat == first_code(ls, l) + count_below(ls, l, 0) by {
            assert(len_ok(*code, ls, l));
        }
    }
    while s < n
        invariant
            ls == lens@,
            n == ls.len(),
            n <= 288,
            s <= n,
            r@.len() == s,
            valid_lens(ls, true) || valid_lens(ls, false),
            forall|l: nat| 1 <= l <= 15 ==> #[trigger] next@[l as int] as nat == first_code(ls, l) + count_below(ls, l, s as int),
            forall|i: int| 0 <= i < s && 1 <= ls[i] ==> #[trigger] r@[i] as nat == rev(canon(ls, i), ls[i] as nat),
        decreases n - s,
    {
        let l = lens[s] as usize;
        proof {
            assert(ls[s as int] as nat <= MAX_BITS);
        }
        if l == 0 {
            r.push(0);
        } else {
            let ghost ln = l as nat;
            proof {
                lemma_count_below_mono(ls, ln, s as int + 1, n as int);
                assert(count_below(ls, ln, s as int + 1) == count_below(ls, ln, s as int) + 1);
                assert(left(ls, ln) >= 0);
                lemma_codes_fit(ls, ln);
                lemma_pow2_strictly_increases(ln, 32);
                lemma2_to64();
                assert(next@[l as int] as nat == first_code(ls, ln) + count_below(ls, ln, s as int));
            }
            let c = next[l];
            next[l] = c + 1;
            let (v, _) = reverse(c, l as u32);
            r.push(v);
        }
        proof {
            assert forall|k: nat| 1 <= k <= 15 implies #[trigger] next@[k as int] as nat == first_code(ls, k) + count_below(ls, k, s as int + 1) by {
                assert(count_below(ls, k, s as int + 1) == count_below(ls, k, s as int) + if ls[s as int] as nat == k { 1nat } else { 0nat });
            }
            assert forall|i: int| 0 <= i < s + 1 && 1 <= ls[i] implies #[trigger] r@[i] as nat == rev(canon(ls, i), ls[i] as nat) by {
            }
        }
        s = s + 1;
    }
    r
}


/// The compressor's output so far, with the blocks written as ghost state.
#[derive(Clone)]
pub struct Encoder {
    pub bw: BitWriter,
    pub bs: Ghost<Seq<Blk>>,
    pub ps: Ghost<Seq<int>>,
    pub os: Ghost<Seq<Seq<u8>>>,
    pub done: Ghost<bool>,
    /// Bytes written before the first block (a zlib or gzip header).
    pub head: Ghost<Seq<u8>>,
    /// The output before the first block: empty, or a preset dictionary
    /// that the blocks may refer back into.
    pub base: Ghost<Seq<u8>>,
    /// The fixed codes, once a block has needed them.
    pub fx: FxSlot,
}

/// The fixed literal and distance codes (RFC 1951 3.2.6) with their
/// canonical codes, built once and reused across blocks and streams.
pub struct FixedCodes {
    lit: Vec<u8>,
    lcodes: Vec<u32>,
    dist: Vec<u8>,
    dcodes: Vec<u32>,
}

impl FixedCodes {
    #[verifier::type_invariant]
    spec fn ok(self) -> bool {
        &&& self.lit@ == fixed_lit_lens()
        &&& self.dist@ == fixed_dist_lens()
        &&& codes_for(self.lit@, self.lcodes@)
        &&& codes_for(self.dist@, self.dcodes@)
    }

    /// Builds the codes; None only if the fixed lengths failed their
    /// check (they do not; the check is what proves them).
    pub fn build() -> (r: Option<FixedCodes>) {
        let mut lit: Vec<u8> = Vec::with_capacity(288);
        let mut i: usize = 0;
        while i < 288
            invariant
                i <= 288,
                lit@.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] lit@[k] == fixed_lit_lens()[k],
            decreases 288 - i,
        {
            lit.push(if i < 144 { 8u8 } else if i < 256 { 9u8 } else if i < 280 { 7u8 } else { 8u8 });
            i = i + 1;
        }
        assert(lit@ =~= fixed_lit_lens());
        let dist: Vec<u8> = vec![5u8; 32];
        assert(dist@ =~= fixed_dist_lens());
        let mut lcode = Code::new();
        let mut dcode = Code::new();
        if !check_lens(&mut lcode, &lit, true) || !check_lens(&mut dcode, &dist, true) {
            return None;
        }
        let lcodes = canon_codes(&lcode, &lit);
        let dcodes = canon_codes(&dcode, &dist);
        Some(FixedCodes { lit, lcodes, dist, dcodes })
    }
}

/// A place for the fixed codes. Copying a stream does not copy them.
pub struct FxSlot(pub Option<FixedCodes>);

impl Clone for FxSlot {
    fn clone(&self) -> (r: FxSlot) {
        FxSlot(None)
    }
}

impl Encoder {
    pub open spec fn inv(&self) -> bool {
        &&& self.bw.wf()
        &&& enc_inv(self.bw.bits(), self.bs@, self.ps@, self.os@, self.done@)
        &&& self.ps@[0] == 8 * self.head@.len()
        &&& self.os@[0] == self.base@
        &&& self.bw.bits().len() >= 8 * self.head@.len()
        &&& self.bw.bits().subrange(0, 8 * self.head@.len() as int) == bytes_bits(self.head@)
    }

    /// The output the blocks so far describe.
    pub open spec fn out(&self) -> Seq<u8> {
        self.os@[self.bs@.len() as int]
    }

    pub fn new(cap: usize) -> (r: Encoder)
        ensures
            r.inv(),
            r.out() == Seq::<u8>::empty(),
            !r.done@,
            r.head@ == Seq::<u8>::empty(),
            r.base@ == Seq::<u8>::empty(),
            r.bw.sent() == Seq::<u8>::empty(),
    {
        let bw = BitWriter::new(cap);
        proof {
            assert(bytes_bits(Seq::<u8>::empty()) == Seq::<nat>::empty());
            assert(bw.bits().subrange(0, 0) =~= Seq::<nat>::empty());
        }
        Encoder {
            bw,
            bs: Ghost(Seq::empty()),
            ps: Ghost(Seq::empty().push(0int)),
            os: Ghost(Seq::empty().push(Seq::empty())),
            done: Ghost(false),
            head: Ghost(Seq::empty()),
            base: Ghost(Seq::empty()),
            fx: FxSlot(None),
        }
    }

    /// An encoder whose output starts with the bytes `hdr`.
    pub fn with_header(hdr: &[u8], cap: usize) -> (r: Encoder)
        ensures
            r.inv(),
            r.out() == Seq::<u8>::empty(),
            !r.done@,
            r.head@ == hdr@,
            r.base@ == Seq::<u8>::empty(),
            r.bw.sent() == Seq::<u8>::empty(),
    {
        Self::with_header_base(hdr, cap, Ghost(Seq::empty()))
    }

    /// `with_header`, for blocks that come after `base` (a preset
    /// dictionary): their matches may refer back into it.
    pub fn with_header_base(hdr: &[u8], cap: usize, Ghost(base): Ghost<Seq<u8>>) -> (r: Encoder)
        ensures
            r.inv(),
            r.out() == base,
            !r.done@,
            r.head@ == hdr@,
            r.base@ == base,
            r.bw.sent() == Seq::<u8>::empty(),
    {
        let mut bw = BitWriter::new(cap);
        bw.put_bytes(hdr);
        proof {
            lemma_bytes_bits(hdr@);
            assert(Seq::<nat>::empty() + bytes_bits(hdr@) =~= bytes_bits(hdr@));
            assert(bw.bits() == bytes_bits(hdr@));
            assert(bw.bits().len() == 8 * hdr@.len());
            assert(bw.bits().subrange(0, 8 * hdr@.len() as int) =~= bw.bits());
            let ps = Seq::empty().push((8 * hdr@.len()) as int);
            assert(ps[0] == bw.bits().len());
            let os = Seq::empty().push(base);
            let bs = Seq::<Blk>::empty();
            assert(ps.len() == bs.len() + 1);
            assert(os.len() == bs.len() + 1);
            assert(os[0] == base);
            assert(ps[bs.len() as int] == bw.bits().len());
            assert(forall|i: int| 0 <= i <= bs.len() ==> 0 <= #[trigger] ps[i] <= ps[bs.len() as int]);
            assert(enc_inv(bw.bits(), bs, ps, os, false));
        }
        Encoder {
            bw,
            bs: Ghost(Seq::empty()),
            ps: Ghost(Seq::empty().push((8 * hdr@.len()) as int)),
            os: Ghost(Seq::empty().push(base)),
            done: Ghost(false),
            head: Ghost(hdr@),
            base: Ghost(base),
            fx: FxSlot(None),
        }
    }

    /// Records block `k`, just written as `block_bits(k, fin)`.
    fn record(&mut self, Ghost(k): Ghost<Blk>, Ghost(fin): Ghost<bool>, Ghost(w0): Ghost<Seq<nat>>)
        requires
            old(self).bw.wf(),
            enc_inv(w0, old(self).bs@, old(self).ps@, old(self).os@, false),
            !old(self).done@,
            blk_ok(k, w0.len() as int, old(self).os@[old(self).bs@.len() as int]),
            old(self).bw.bits() == w0 + block_bits(k, fin),
            old(self).ps@[0] == 8 * old(self).head@.len(),
            old(self).os@[0] == old(self).base@,
            w0.len() >= 8 * old(self).head@.len(),
            w0.subrange(0, 8 * old(self).head@.len() as int) == bytes_bits(old(self).head@),
        ensures
            final(self).inv(),
            final(self).bw == old(self).bw,
            final(self).head == old(self).head && final(self).base == old(self).base && final(self).bw.sent() == old(self).bw.sent(),
            final(self).out() == blk_out(k, old(self).out()),
            final(self).done@ == fin,
    {
        proof {
            lemma_enc_push(w0, self.bs@, self.ps@, self.os@, k, fin);
            let h = 8 * self.head@.len() as int;
            assert((w0 + block_bits(k, fin)).subrange(0, h) =~= w0.subrange(0, h));
        }
        let ghost n = self.bs@.len() as int;
        self.ps = Ghost(self.ps@.push((w0.len() + block_bits(k, fin).len()) as int));
        self.os = Ghost(self.os@.push(blk_out(k, self.os@[n])));
        assert(self.os@[0] == old(self).os@[0]);
        self.bs = Ghost(self.bs@.push(k));
        self.done = Ghost(fin);
    }

    /// Writes `data` (at most 65535 bytes) as a stored block.
    pub fn stored(&mut self, data: &[u8], fin: bool)
        requires
            old(self).inv(),
            !old(self).done@,
            data@.len() <= 65535,
        ensures
            final(self).inv(),
            final(self).out() == old(self).out() + data@,
            final(self).done@ == fin,
            final(self).head == old(self).head && final(self).base == old(self).base && final(self).bw.sent() == old(self).bw.sent(),
            final(self).bw.bits().len() % 8 == 0,
    {
        let ghost w0 = self.bw.bits();
        proof {
            lemma2_to64();
        }
        self.bw.put(if fin { 1 } else { 0 }, 1);
        self.bw.put(0, 2);
        let ghost w1 = self.bw.bits();
        self.bw.align();
        let ghost pad = (self.bw.bits().len() - w1.len()) as nat;
        let n = data.len();
        let m = 65535 - n;
        let hdr = [(n % 256) as u8, (n / 256) as u8, (m % 256) as u8, (m / 256) as u8];
        let ghost w2 = self.bw.bits();
        self.bw.put_bytes(&hdr);
        proof {
            lemma_bytes_bits(hdr@);
            assert(self.bw.bits().len() == w2.len() + 32);
            assert(self.bw.bits().len() % 8 == 0);
        }
        self.bw.put_bytes(data);
        proof {
            lemma_bytes_bits(data@);
            assert(self.bw.bits().len() % 8 == 0);
        }
        let ghost k = Blk {
            kind: 0,
            data: data@,
            pad,
            cl: Seq::empty(),
            hclen: 0,
            lit: Seq::empty(),
            dist: Seq::empty(),
            ts: Seq::empty(),
        };
        proof {
            let f = if fin { 1nat } else { 0nat };
            assert(hdr@ + data@ =~= stored_bytes(data@));
            lemma_bytes_bits_concat(hdr@, data@);
            reveal(body_bits);
            reveal(blk_ok);
            assert(self.bw.bits() =~= w0 + block_bits(k, fin));
            assert(w1.len() == w0.len() + 3) by {
                lemma_bits_of(f, 1);
                lemma_bits_of(0, 2);
            }
            assert((w0.len() + 3 + pad) % 8 == 0);
            assert(blk_ok(k, w0.len() as int, self.os@[self.bs@.len() as int]));
        }
        self.record(Ghost(k), Ghost(fin), Ghost(w0));
    }

    /// Writes tokens `ts` as a block with codes it sends.
    pub fn dynamic(
        &mut self,
        ts: &[u32],
        sy: &[u16],
        lit: &[u8],
        lcodes: &[u32],
        dist: &[u8],
        dcodes: &[u32],
        cl: &[u8],
        clcodes: &[u32],
        hclen: usize,
        fin: bool,
    )
        requires
            old(self).inv(),
            !old(self).done@,
            dyn_ok(cl@, hclen as nat, lit@, dist@),
            syms_for(ts@, sy@),
            codes_for(lit@, lcodes@),
            codes_for(dist@, dcodes@),
            codes_for(cl@, clcodes@),
            forall|i: int| 0 <= i < ts@.len() ==> #[trigger] tok_coded(lit@, dist@, ts@[i]) && tok_valid(ts@[i]),
            toks_ok(old(self).out(), ts@),
        ensures
            final(self).inv(),
            final(self).out() == expand(old(self).out(), ts@),
            final(self).done@ == fin,
            final(self).head == old(self).head && final(self).base == old(self).base && final(self).bw.sent() == old(self).bw.sent(),
    {
        let ghost w0 = self.bw.bits();
        proof {
            lemma2_to64();
        }
        self.bw.put(if fin { 1 } else { 0 }, 1);
        self.bw.put(2, 2);
        put_header(&mut self.bw, cl, clcodes, hclen, lit, dist);
        put_tokens(&mut self.bw, ts, sy, lit, lcodes, dist, dcodes);
        put_code(&mut self.bw, lit, lcodes, 256);
        let ghost k = Blk { kind: 2, data: Seq::empty(), pad: 0, cl: cl@, hclen: hclen as nat, lit: lit@, dist: dist@, ts: ts@ };
        proof {
            reveal(body_bits);
            reveal(blk_ok);
            assert(self.bw.bits() =~= w0 + block_bits(k, fin));
            assert(codes_ok(k, self.os@[self.bs@.len() as int]));
        }
        self.record(Ghost(k), Ghost(fin), Ghost(w0));
    }

    /// Writes the tokens `ts` as a block with the fixed codes (RFC 1951
    /// 3.2.6): no code header, which wins on small blocks.
    pub fn fixed(
        &mut self,
        ts: &[u32],
        sy: &[u16],
        lit: &[u8],
        lcodes: &[u32],
        dist: &[u8],
        dcodes: &[u32],
        fin: bool,
    )
        requires
            old(self).inv(),
            !old(self).done@,
            lit@ == fixed_lit_lens(),
            dist@ == fixed_dist_lens(),
            syms_for(ts@, sy@),
            codes_for(lit@, lcodes@),
            codes_for(dist@, dcodes@),
            forall|i: int| 0 <= i < ts@.len() ==> #[trigger] tok_coded(lit@, dist@, ts@[i]) && tok_valid(ts@[i]),
            toks_ok(old(self).out(), ts@),
        ensures
            final(self).inv(),
            final(self).out() == expand(old(self).out(), ts@),
            final(self).done@ == fin,
            final(self).head == old(self).head && final(self).base == old(self).base && final(self).bw.sent() == old(self).bw.sent(),
    {
        let ghost w0 = self.bw.bits();
        proof {
            lemma2_to64();
        }
        self.bw.put(if fin { 1 } else { 0 }, 1);
        self.bw.put(1, 2);
        put_tokens(&mut self.bw, ts, sy, lit, lcodes, dist, dcodes);
        put_code(&mut self.bw, lit, lcodes, 256);
        let ghost k = Blk { kind: 1, data: Seq::empty(), pad: 0, cl: Seq::empty(), hclen: 0, lit: lit@, dist: dist@, ts: ts@ };
        proof {
            reveal(body_bits);
            reveal(blk_ok);
            assert(self.bw.bits() =~= w0 + block_bits(k, fin));
            assert(codes_ok(k, self.os@[self.bs@.len() as int]));
        }
        self.record(Ghost(k), Ghost(fin), Ghost(w0));
    }

    /// The bytes written, once the final block is.
    pub fn finish(self) -> (r: Vec<u8>)
        requires
            self.inv(),
            self.done@,
            self.head@ == Seq::<u8>::empty(),
            self.base@ == Seq::<u8>::empty(),
        ensures
            inflate(self.bw.sent() + r@) == Some((self.out(), (self.bw.sent() + r@).len() as int)),
    {
        let ghost w = self.bw.bits();
        let ghost g = self.bw.sent();
        let (b, wf) = self.bw.finish();
        proof {
            lemma_enc_done(g + b@, wf@, w, self.bs@, self.ps@, self.os@);
        }
        b
    }

    /// The bytes written, then `tail` (a zlib or gzip trailer) on the next
    /// byte boundary.
    pub fn finish_tail(self, tail: &[u8]) -> (r: Vec<u8>)
        requires
            self.inv(),
            self.done@,
        ensures
            ({
                let t = self.bw.sent() + r@;
                &&& t.len() >= self.head@.len()
                &&& t.subrange(0, self.head@.len() as int) == self.head@
                &&& match inflate_blocks(t, 8 * self.head@.len() as int, self.base@) {
                    Some((e, o)) => o == self.out() && 0 <= e && (e + 7) / 8 + tail@.len() == t.len()
                        && t.subrange((e + 7) / 8, t.len() as int) == tail@,
                    None => false,
                }
            }),
    {
        hide(inflate_blocks);
        hide(enc_inv);
        let ghost w = self.bw.bits();
        let ghost h = self.head@.len() as int;
        let ghost g = self.bw.sent();
        let mut bw = self.bw;
        bw.align();
        let ghost w1 = bw.bits();
        bw.put_bytes(tail);
        let ghost w2 = bw.bits();
        let (b, wf) = bw.finish();
        proof {
            lemma_bytes_bits(tail@);
            assert(wf@.len() == w2.len()) by {
                assert(wf@.len() == 8 * (g + b@).len());
                assert(w2.len() % 8 == 0);
            }
            assert(wf@ =~= w2) by {
                assert(wf@.subrange(0, w2.len() as int) == w2);
            }
            assert(wf@.subrange(0, w.len() as int) =~= w);
            assert(wf@.subrange(w1.len() as int, wf@.len() as int) =~= bytes_bits(tail@));
            lemma_tail(g + b@, wf@, w, w1.len() as int, self.bs@, self.ps@, self.os@, self.head@, tail@);
        }
        b
    }
}


/// What `Encoder::finish_tail` writes.
proof fn lemma_tail(
    b: Seq<u8>,
    wf: Seq<nat>,
    w: Seq<nat>,
    w1: int,
    bs: Seq<Blk>,
    ps: Seq<int>,
    os: Seq<Seq<u8>>,
    head: Seq<u8>,
    tail: Seq<u8>,
)
    requires
        enc_inv(w, bs, ps, os, true),
        ps[0] == 8 * head.len(),
        w.len() >= 8 * head.len(),
        w.subrange(0, 8 * head.len() as int) == bytes_bits(head),
        w1 % 8 == 0,
        w.len() <= w1 < w.len() + 8,
        bytes_hold(b, wf),
        wf.len() == w1 + 8 * tail.len(),
        wf.subrange(0, w.len() as int) == w,
        wf.subrange(w1, wf.len() as int) == bytes_bits(tail),
    ensures
        b.len() >= head.len(),
        b.subrange(0, head.len() as int) == head,
        match inflate_blocks(b, 8 * head.len() as int, os[0]) {
            Some((e, o)) => o == os[bs.len() as int] && 0 <= e && (e + 7) / 8 + tail.len() == b.len()
                && b.subrange((e + 7) / 8, b.len() as int) == tail,
            None => false,
        },
{
    let h = head.len() as int;
    lemma_bytes_bits(head);
    lemma_bytes_bits(tail);
    lemma_enc_done_at(b, wf, w, bs, ps, os);
    let n = bs.len() as int;
    let e = ps[n];
    let q = w1 / 8;
    assert((e + 7) / 8 == q);
    assert(8 * q == w1);
    assert(b.len() == q + tail.len());
    assert(wf.subrange(8 * q, 8 * q + 8 * tail.len()) == bytes_bits(tail));
    lemma_bytes_at(b, wf, q, tail);
    assert(wf.subrange(0, 8 * h) =~= w.subrange(0, 8 * h));
    lemma_bytes_at(b, wf, 0, head);
    assert(b.subrange(0, h) =~= b.subrange(0, 0 + h));
}

/// A token's fields are in DEFLATE's ranges.
pub open spec fn tok_valid(t: u32) -> bool {
    is_lit(t) || (3 <= tlen(t) <= 258 && 1 <= tdist(t) <= 32768)
}

/// A literal, or a match reaching back at most `w` bytes.
#[verifier::opaque]
pub open spec fn tok_within(t: u32, w: nat) -> bool {
    is_lit(t) || tdist(t) <= w
}

/// `emit`, keeping every token within `w` bytes.
#[inline(always)]
fn emit_within(toks: &mut Vec<u32>, fr: &mut Freqs, t: u32, Ghost(w): Ghost<nat>)
    requires
        old(fr).ok(old(toks)@),
        old(toks)@.len() + 1 < MAX_TOKS,
        tok_valid(t),
        is_lit(t) || tdist(t) <= w,
        forall|i: int| 0 <= i < old(toks)@.len() ==> #[trigger] tok_within(old(toks)@[i], w),
    ensures
        final(toks)@ == old(toks)@.push(t),
        final(fr).ok(final(toks)@),
        forall|i: int| 0 <= i < final(toks)@.len() ==> #[trigger] tok_within(final(toks)@[i], w),
{
    emit(toks, fr, t);
    proof {
        reveal(tok_within);
        assert forall|i: int| 0 <= i < toks@.len() implies #[trigger] tok_within(toks@[i], w) by {
            if i < toks@.len() - 1 {
                assert(toks@[i] == old(toks)@[i]);
            }
        }
    }
}

/// `sy` holds each match's length and distance symbols, as
/// `lidx + 256 * didx`.
pub open spec fn syms_for(ts: Seq<u32>, sy: Seq<u16>) -> bool {
    forall|i: int| 0 <= i < ts.len() && !is_lit(ts[i]) ==> i < sy.len() && (#[trigger] sy[i]) as int % 256 == lidx(tlen(ts[i]))
        && sy[i] as int / 256 == didx(tdist(ts[i]))
}

/// `codes` holds the bit-reversed canonical codes of `lens`.
pub open spec fn codes_for(lens: Seq<u8>, codes: Seq<u32>) -> bool {
    &&& codes.len() == lens.len()
    &&& lens_ok(lens)
    &&& forall|s: int| 0 <= s < lens.len() && 1 <= lens[s] ==> #[trigger] codes[s] as nat == rev(canon(lens, s), lens[s] as nat)
}

/// `t`'s symbols are counted in `lf` and `df`.
pub open spec fn tok_counted(lf: Seq<u32>, df: Seq<u32>, t: u32) -> bool {
    if is_lit(t) {
        t < lf.len() && lf[t as int] >= 1
    } else {
        &&& 257 + lidx(tlen(t)) < lf.len()
        &&& lf[257 + lidx(tlen(t))] >= 1
        &&& didx(tdist(t)) < df.len()
        &&& df[didx(tdist(t))] >= 1
    }
}

/// The symbol counts and match symbols of a block's tokens, gathered as
/// the parser makes them (as libdeflate does) instead of in a second pass.
pub struct Freqs {
    pub lf: Vec<u32>,
    pub df: Vec<u32>,
    pub sy: Vec<u16>,
}

/// The most tokens a block holds.
pub const MAX_TOKS: usize = 16384;

impl Freqs {
    /// Counts for the tokens `ts`, with end of block counted once.
    pub open spec fn ok(&self, ts: Seq<u32>) -> bool {
        &&& self.lf@.len() == 286
        &&& self.df@.len() == 30
        &&& self.sy@.len() <= MAX_TOKS
        &&& syms_for(ts, self.sy@)
        &&& forall|k: int| 0 <= k < 286 ==> #[trigger] self.lf@[k] <= ts.len() + 1
        &&& forall|k: int| 0 <= k < 30 ==> #[trigger] self.df@[k] <= ts.len()
        &&& forall|k: int| 0 <= k < ts.len() ==> #[trigger] tok_counted(self.lf@, self.df@, ts[k])
    }

    /// Counts for an empty block.
    pub fn new() -> (r: Freqs)
        ensures
            r.ok(Seq::empty()),
    {
        let mut lf: Vec<u32> = vec![0u32; 286];
        lf.set(256, 1);
        // `sy` grows as matches come, so a short or literal-heavy block
        // zeroes little; literals have no entry of their own.
        Freqs { lf, df: vec![0u32; 30], sy: Vec::new() }
    }
}

/// Appends token `t` to `toks`, counting its symbols in `fr`.
#[inline(always)]
pub fn emit(toks: &mut Vec<u32>, fr: &mut Freqs, t: u32)
    requires
        old(fr).ok(old(toks)@),
        old(toks)@.len() + 1 < MAX_TOKS,
        tok_valid(t),
    ensures
        final(toks)@ == old(toks)@.push(t),
        final(fr).ok(final(toks)@),
{
    let i = toks.len();
    let ghost ts0 = toks@;
    let ghost lf0 = fr.lf@;
    let ghost df0 = fr.df@;
    let ghost sy_s = fr.sy@;
    if t < 256 {
        let c = verilith_core::prims::get32(fr.lf.as_slice(), t as usize);
        verilith_core::prims::set32(fr.lf.as_mut_slice(), t as usize, c + 1);
    } else {
        let li = len_index(t / 65536);
        let di = dist_index(t % 65536);
        let c = verilith_core::prims::get32(fr.lf.as_slice(), 257 + li);
        verilith_core::prims::set32(fr.lf.as_mut_slice(), 257 + li, c + 1);
        let c = verilith_core::prims::get32(fr.df.as_slice(), di);
        verilith_core::prims::set32(fr.df.as_mut_slice(), di, c + 1);
        let v = (li + 256 * di) as u16;
        if i >= fr.sy.len() {
            let want = if i < 64 { 128 } else if i < MAX_TOKS / 2 { 2 * i } else { MAX_TOKS };
            let ghost sy0 = fr.sy@;
            fr.sy.resize(want, 0u16);
            proof {
                assert forall|k: int| 0 <= k < sy0.len() implies #[trigger] fr.sy@[k] == sy0[k] by {
                    assert(fr.sy@.subrange(0, sy0.len() as int)[k] == sy0[k]);
                }
            }
        }
        proof {
            assert((t / 65536) as nat == tlen(t) && (t % 65536) as nat == tdist(t));
            assert(v as int % 256 == li && v as int / 256 == di);
        }
        crate::prims::set16(fr.sy.as_mut_slice(), i, v);
        proof {
            assert(i < fr.sy@.len() && fr.sy@[i as int] == v);
        }
    }
    proof {
        assert(fr.sy@.len() >= sy_s.len());
        assert(fr.sy@.len() <= MAX_TOKS);
        assert forall|k: int| 0 <= k < sy_s.len() && k != i implies #[trigger] fr.sy@[k] == sy_s[k] by {}
    }
    toks.push(t);
    proof {
        let ts = toks@;
        assert(ts[i as int] == t);
        assert forall|k: int| 0 <= k < i implies #[trigger] ts[k] == ts0[k] by {}
        assert forall|k: int| 0 <= k <= i && !is_lit(ts[k]) implies k < fr.sy@.len() && (#[trigger] fr.sy@[k]) as int % 256 == lidx(tlen(ts[k]))
            && fr.sy@[k] as int / 256 == didx(tdist(ts[k])) by {
            assert(ts[k] == if k < i { ts0[k] } else { t });
            if k < i {
                assert(!is_lit(ts0[k]));
                assert(k < sy_s.len() && sy_s[k] as int % 256 == lidx(tlen(ts0[k])));
                assert(fr.sy@[k] == sy_s[k]);
            }
        }
        if !is_lit(t) {
            lemma_lidx(tlen(t));
            lemma_didx(tdist(t));
        }
        assert forall|j: int| 0 <= j < 286 implies #[trigger] fr.lf@[j] >= lf0[j] by {}
        assert forall|j: int| 0 <= j < 30 implies #[trigger] fr.df@[j] >= df0[j] by {}
        assert forall|k: int| 0 <= k <= i implies #[trigger] tok_counted(fr.lf@, fr.df@, ts[k]) by {
            if k < i {
                assert(ts[k] == ts0[k]);
                assert(tok_counted(lf0, df0, ts0[k]));
                if !is_lit(ts0[k]) {
                    assert(fr.lf@[257 + lidx(tlen(ts0[k]))] >= lf0[257 + lidx(tlen(ts0[k]))]);
                    assert(fr.df@[didx(tdist(ts0[k]))] >= df0[didx(tdist(ts0[k]))]);
                } else {
                    assert(fr.lf@[ts0[k] as int] >= lf0[ts0[k] as int]);
                }
            }
        }
    }
}

/// Writes symbol `s`'s code.
#[inline(always)]
fn put_code(bw: &mut BitWriter, lens: &[u8], codes: &[u32], s: usize)
    requires
        old(bw).wf(),
        codes_for(lens@, codes@),
        s < lens@.len(),
        1 <= lens@[s as int],
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        final(bw).bits() == old(bw).bits() + code_of(lens@, s as int),
{
    proof {
        lemma_rev_bound(canon(lens@, s as int), lens@[s as int] as nat);
    }
    bw.put(codes[s], lens[s] as u32);
}

/// `e` holds the bits that send length `l` with the code `lit`: the length
/// symbol's code then the extra bits, as `bits | count << 24`.
pub open spec fn len_ent_ok(lit: Seq<u8>, e: u32, l: int) -> bool {
    let li = lidx(l as nat);
    &&& e >> 24 <= 20
    &&& ((e & 0xff_ffff) as nat) < pow2((e >> 24) as nat)
    &&& bits_of((e & 0xff_ffff) as nat, (e >> 24) as nat) == code_of(lit, 257 + li)
        + bits_of((l - len_base()[li]) as nat, len_extra()[li])
}

proof fn lemma_pack24(a: u32, n: u32)
    requires
        a < 0x100_0000,
        n < 256,
    ensures
        (a | (n << 24)) & 0xff_ffff == a,
        (a | (n << 24)) >> 24 == n,
{
    assert((a | (n << 24)) & 0xff_ffff == a && (a | (n << 24)) >> 24 == n) by (bit_vector)
        requires
            a < 0x100_0000,
            n < 256,
    ;
}

/// For each length, the bits that send it with the code `lit` (libdeflate
/// keeps the same table), so a match needs one lookup for its length.
fn len_table(lit: &[u8], lcodes: &[u32]) -> (lt: Vec<u32>)
    requires
        codes_for(lit@, lcodes@),
    ensures
        lt@.len() == 259,
        forall|l: int| 3 <= l <= 258 && 257 + lidx(l as nat) < lit@.len() && 1 <= lit@[257 + lidx(l as nat)]
            ==> #[trigger] len_ent_ok(lit@, lt@[l], l),
{
    let mut lt: Vec<u32> = vec![0u32; 259];
    let mut l: usize = 3;
    proof {
        lemma_len_sym();
        lemma_tables();
    }
    while l <= 258
        invariant
            3 <= l <= 259,
            lt@.len() == 259,
            codes_for(lit@, lcodes@),
            forall|j: int| 3 <= j <= 258 ==> (#[trigger] LEN_SYM@[j]) as int == lidx(j as nat),
            forall|j: int| 0 <= j < 29 ==> #[trigger] LEN_BASE@[j] as nat == len_base()[j] && LEN_EXTRA@[j] as nat == len_extra()[j]
                && LEN_EXTRA@[j] <= 5,
            forall|j: int| 3 <= j < l && 257 + lidx(j as nat) < lit@.len() && 1 <= lit@[257 + lidx(j as nat)]
                ==> #[trigger] len_ent_ok(lit@, lt@[j], j),
        decreases 259 - l,
    {
        let li = LEN_SYM[l] as usize;
        let ls = 257 + li;
        proof {
            lemma_lidx(l as nat);
        }
        if ls < lit.len() && lit[ls] >= 1 {
            proof {
                lemma_rev_bound(canon(lit@, ls as int), lit@[ls as int] as nat);
                assert(lit@[ls as int] <= 15);
                lemma_pow2_strictly_increases(5, 24);
                lemma2_to64();
            }
            let n = lit[ls] as u32 + LEN_EXTRA[li] as u32;
            let a = join(lcodes[ls] as u64, lit[ls] as u32, (l as u32 - LEN_BASE[li] as u32) as u64, LEN_EXTRA[li] as u32);
            proof {
                if n < 24 {
                    lemma_pow2_strictly_increases(n as nat, 24);
                }
                assert(pow2(24) == 0x100_0000) by (compute);
                assert(a < 0x100_0000);
                lemma_pack24(a as u32, n);
            }
            let e = (a as u32) | (n << 24);
            let ghost lt0 = lt@;
            lt.set(l, e);
            proof {
                assert(len_ent_ok(lit@, lt@[l as int], l as int));
                assert forall|j: int| 3 <= j < l + 1 && 257 + lidx(j as nat) < lit@.len() && 1 <= lit@[257 + lidx(j as nat)]
                    implies #[trigger] len_ent_ok(lit@, lt@[j], j) by {
                    if j < l {
                        assert(lt@[j] == lt0[j]);
                    }
                }
            }
        }
        l = l + 1;
    }
    lt
}

/// Writes the tokens with the codes `lit` and `dist`.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn put_tokens(bw: &mut BitWriter, ts: &[u32], sy: &[u16], lit: &[u8], lcodes: &[u32], dist: &[u8], dcodes: &[u32])
    requires
        old(bw).wf(),
        syms_for(ts@, sy@),
        codes_for(lit@, lcodes@),
        codes_for(dist@, dcodes@),
        forall|i: int| 0 <= i < ts@.len() ==> #[trigger] tok_coded(lit@, dist@, ts@[i]) && tok_valid(ts@[i]),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        final(bw).bits() == old(bw).bits() + cat(ts@, tok_fn(lit@, dist@)),
{
    let ghost w0 = bw.bits();
    let ghost f = tok_fn(lit@, dist@);
    let lt = len_table(lit, lcodes);
    let mut i: usize = 0;
    proof {
        lemma_tables();
        assert(ts@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(w0 + cat(Seq::<u32>::empty(), f) =~= w0);
    }
    while i < ts.len()
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            codes_for(lit@, lcodes@),
            codes_for(dist@, dcodes@),
            forall|i: int| 0 <= i < ts@.len() ==> #[trigger] tok_coded(lit@, dist@, ts@[i]) && tok_valid(ts@[i]),
            i <= ts@.len(),
            syms_for(ts@, sy@),
            bw.bits() == w0 + cat(ts@.subrange(0, i as int), f),
            f == tok_fn(lit@, dist@),
            forall|j: int| 0 <= j < 29 ==> #[trigger] LEN_BASE@[j] as nat == len_base()[j] && LEN_EXTRA@[j] as nat == len_extra()[j],
            lt@.len() == 259,
            forall|l: int| 3 <= l <= 258 && 257 + lidx(l as nat) < lit@.len() && 1 <= lit@[257 + lidx(l as nat)]
                ==> #[trigger] len_ent_ok(lit@, lt@[l], l),
            forall|j: int| 0 <= j < 30 ==> #[trigger] DIST_BASE@[j] as nat == dist_base()[j] && DIST_EXTRA@[j] as nat == dist_extra()[j],
        decreases ts@.len() - i,
    {
        let t = ts[i];
        let ghost wi = bw.bits();
        proof {
            assert(tok_coded(lit@, dist@, ts@[i as int]) && tok_valid(ts@[i as int]));
        }
        if t < 256 && i + 1 < ts.len() && ts[i + 1] < 256 {
            // Two literals (at most 30 bits) in one write.
            let t2 = ts[i + 1];
            proof {
                assert(tok_coded(lit@, dist@, ts@[i + 1]) && tok_valid(ts@[i + 1]));
                lemma_rev_bound(canon(lit@, t as int), lit@[t as int] as nat);
                lemma_rev_bound(canon(lit@, t2 as int), lit@[t2 as int] as nat);
            }
            let n1 = verilith_core::prims::get(lit, t as usize) as u32;
            let n2 = verilith_core::prims::get(lit, t2 as usize) as u32;
            let v = join(verilith_core::prims::get32(lcodes, t as usize) as u64, n1, verilith_core::prims::get32(lcodes, t2 as usize) as u64, n2);
            bw.put64(v, n1 + n2);
            proof {
                assert(bw.bits() =~= wi + tok_bits(lit@, dist@, t) + tok_bits(lit@, dist@, t2));
                lemma_cat_push(ts@.subrange(0, i as int), t, f);
                assert(ts@.subrange(0, i as int).push(t) =~= ts@.subrange(0, i as int + 1));
                lemma_cat_push(ts@.subrange(0, i as int + 1), t2, f);
                assert(ts@.subrange(0, i as int + 1).push(t2) =~= ts@.subrange(0, i as int + 2));
            }
            i = i + 2;
            continue;
        }
        if t < 256 {
            put_code(bw, lit, lcodes, t as usize);
        } else {
            let len = t / 65536;
            let d = t % 65536;
            proof {
                assert(!is_lit(ts@[i as int]));
                let _ = sy@[i as int];
                assert(i < sy@.len());
            }
            let di = (crate::prims::get16(sy, i) / 256) as usize;
            proof {
                assert(sy@[i as int] as int / 256 == didx(tdist(ts@[i as int])));
                lemma_lidx(len as nat);
                lemma_didx(d as nat);
                assert(len_ent_ok(lit@, lt@[len as int], len as int));
                lemma_rev_bound(canon(dist@, di as int), dist@[di as int] as nat);
            }
            // The four fields (at most 48 bits) in one write.
            let e = verilith_core::prims::get32(lt.as_slice(), len as usize);
            let a = (e & 0xff_ffff) as u64;
            let na = e >> 24;
            let dl = verilith_core::prims::get(dist, di) as u32;
            let b = join(verilith_core::prims::get32(dcodes, di) as u64, dl, (d - DIST_BASE[di] as u32) as u64, DIST_EXTRA[di] as u32);
            let nb = dl + DIST_EXTRA[di] as u32;
            let v = join(a, na, b, nb);
            bw.put64(v, na + nb);
            proof {
                let li = lidx(len as nat);
                assert(bits_of(v as nat, (na + nb) as nat) =~= code_of(lit@, 257 + li) + bits_of((len - len_base()[li]) as nat, len_extra()[li])
                    + code_of(dist@, di as int) + bits_of((d - DIST_BASE@[di as int]) as nat, DIST_EXTRA@[di as int] as nat));
            }
        }
        proof {
            assert(bw.bits() =~= wi + tok_bits(lit@, dist@, t));
            lemma_cat_push(ts@.subrange(0, i as int), t, f);
            assert(ts@.subrange(0, i as int).push(t) =~= ts@.subrange(0, i as int + 1));
        }
        i = i + 1;
    }
    proof {
        assert(ts@.subrange(0, ts@.len() as int) =~= ts@);
    }
}


/// Writes the code length code's lengths in `clen_order`.
fn put_cl(bw: &mut BitWriter, cl: &[u8], hclen: usize)
    requires
        old(bw).wf(),
        hclen <= 19,
        cl@.len() == 19,
        forall|s: int| 0 <= s < 19 ==> #[trigger] cl@[s] < 8,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        final(bw).bits() == old(bw).bits() + cat(cl_sent(cl@, hclen as nat), b3_fn()),
{
    let ghost w1 = bw.bits();
    let ghost v = cl_sent(cl@, hclen as nat);
    let mut i: usize = 0;
    proof {
        lemma_clen_order();
        assert(v.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(w1 + cat(Seq::<u8>::empty(), b3_fn()) =~= w1);
    }
    while i < hclen
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            i <= hclen <= 19,
            cl@.len() == 19,
            v == cl_sent(cl@, hclen as nat),
            forall|s: int| 0 <= s < 19 ==> #[trigger] cl@[s] < 8,
            forall|i: int| 0 <= i < 19 ==> #[trigger] crate::inflate::CLEN_ORDER@[i] as nat == clen_order()[i]
                && clen_order()[i] < 19,
            bw.bits() == w1 + cat(v.subrange(0, i as int), b3_fn()),
        decreases hclen - i,
    {
        let x = cl[crate::inflate::CLEN_ORDER[i] as usize];
        proof {
            lemma2_to64();
            assert(x < 8);
        }
        bw.put(x as u32, 3);
        proof {
            assert(v[i as int] == x);
            lemma_cat_push(v.subrange(0, i as int), x, b3_fn());
            assert(v.subrange(0, i as int).push(x) =~= v.subrange(0, i as int + 1));
        }
        i = i + 1;
    }
    proof {
        assert(v.subrange(0, hclen as int) =~= v);
    }
}

/// Writes the literal/length and distance code lengths as code length
/// symbols 0 to 15.
fn put_lens(bw: &mut BitWriter, cl: &[u8], clcodes: &[u32], lit: &[u8], dist: &[u8])
    requires
        old(bw).wf(),
        lit@.len() <= 288,
        dist@.len() <= 32,
        codes_for(cl@, clcodes@),
        forall|i: int| 0 <= i < (lit@ + dist@).len() ==> #[trigger] (lit@ + dist@)[i] < 16 && (lit@ + dist@)[i] < cl@.len()
            && 1 <= cl@[(lit@ + dist@)[i] as int],
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        final(bw).bits() == old(bw).bits() + cat(lit@ + dist@, len_fn(cl@)),
{
    let ghost w2 = bw.bits();
    let ghost ld = lit@ + dist@;
    let hlit = lit.len();
    let total = hlit + dist.len();
    let mut j: usize = 0;
    proof {
        assert(ld.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(w2 + cat(Seq::<u8>::empty(), len_fn(cl@)) =~= w2);
    }
    while j < total
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            codes_for(cl@, clcodes@),
            forall|i: int| 0 <= i < ld.len() ==> #[trigger] ld[i] < 16 && ld[i] < cl@.len() && 1 <= cl@[ld[i] as int],
            ld == lit@ + dist@,
            hlit == lit@.len(),
            total == ld.len(),
            j <= total,
            bw.bits() == w2 + cat(ld.subrange(0, j as int), len_fn(cl@)),
        decreases total - j,
    {
        let x = if j < hlit { lit[j] } else { dist[j - hlit] };
        proof {
            assert(x == ld[j as int]);
        }
        put_code(bw, cl, clcodes, x as usize);
        proof {
            lemma_cat_push(ld.subrange(0, j as int), x, len_fn(cl@));
            assert(ld.subrange(0, j as int).push(x) =~= ld.subrange(0, j as int + 1));
        }
        j = j + 1;
    }
    proof {
        assert(ld.subrange(0, total as int) =~= ld);
    }
}

/// Writes a dynamic block's header (after the 3 block header bits).
fn put_header(bw: &mut BitWriter, cl: &[u8], clcodes: &[u32], hclen: usize, lit: &[u8], dist: &[u8])
    requires
        old(bw).wf(),
        dyn_ok(cl@, hclen as nat, lit@, dist@),
        codes_for(cl@, clcodes@),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        final(bw).bits() == old(bw).bits() + dyn_bits(cl@, hclen as nat, lit@, dist@),
{
    let ghost w0 = bw.bits();
    proof {
        lemma2_to64();
    }
    bw.put((lit.len() - 257) as u32, 5);
    bw.put((dist.len() - 1) as u32, 5);
    bw.put((hclen - 4) as u32, 4);
    put_cl(bw, cl, hclen);
    put_lens(bw, cl, clcodes, lit, dist);
    proof {
        assert(bw.bits() =~= w0 + dyn_bits(cl@, hclen as nat, lit@, dist@));
    }
}


// ---------------------------------------------------------------------------
// Finding matches
// ---------------------------------------------------------------------------

pub const HSIZE: usize = 32768;
pub const WSIZE: usize = 32768;

/// Hash chains over the input: `head[h]` is one more than the last
/// position whose next 4 bytes hash to `h`, and `prev[p % WSIZE]` the
/// distance back from `p` to the position before it with the same hash
/// (0xffff, beyond any window, if none within 65535 bytes). Distances, unlike positions, fit in 16
/// bits, which halves the table's cache footprint, and need no update when
/// the window slides. They only suggest
/// candidates: every match is checked against the data.
#[derive(Clone)]
pub struct Matcher {
    /// Positions plus one, cut to 32 bits: a wrong candidate (past 4 GiB)
    /// is only a wasted try, since every match is checked.
    head: Vec<u32>,
    prev: Vec<u16>,
    /// How many candidates to try, and the length that ends the search
    /// (and is taken at once, without looking ahead).
    chain: usize,
    nice: usize,
    /// The lazy parser looks ahead only from a match shorter than `lazy`,
    /// and with a quarter of the chain from one of `good` or more (zlib's
    /// `max_lazy` and `good_length`).
    lazy: usize,
    good: usize,
    /// Take each match found without looking ahead (levels 1 to 4, as
    /// libdeflate's greedy parser).
    greedy: bool,
    /// Look two bytes ahead instead of one (levels 8 and 9, libdeflate's
    /// `lazy2`).
    lazy2: bool,
    /// Level 1: no chains, but two candidates per hash, the newest in
    /// `head` and the one before in `head1` (libdeflate's hash table
    /// match finder). `head1` is empty at other levels.
    fast: bool,
    head1: Vec<u32>,
    /// The farthest a match may reach back (at most `WSIZE`).
    wmax: usize,
    /// `head` has `2^hbits` entries, and `prev` `pmask + 1` (a power of
    /// two). Both are full size except for small one-shot inputs, where
    /// zeroing full tables would cost more than the compression.
    hbits: u32,
    pmask: usize,
}

/// `d` bytes back from `p`, the next `len` bytes repeat.
pub open spec fn is_match(data: Seq<u8>, p: int, len: nat, d: nat) -> bool {
    &&& 3 <= len <= 258
    &&& 1 <= d <= 32768
    &&& d <= p
    &&& p + len <= data.len()
    &&& forall|k: int| 0 <= k < len ==> #[trigger] data[p + k] == data[p + k - d]
}

/// The token for a match.
pub open spec fn match_tok(len: nat, d: nat) -> u32 {
    (len * 65536 + d) as u32
}

pub proof fn lemma_match_tok(len: nat, d: nat)
    requires
        3 <= len <= 258,
        1 <= d <= 32768,
    ensures
        !is_lit(match_tok(len, d)),
        tlen(match_tok(len, d)) == len,
        tdist(match_tok(len, d)) == d,
        tok_valid(match_tok(len, d)),
{
    let t = len * 65536 + d;
    assert(t < 0x1_0000_0000);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(t as int, 65536, len as int, d as int);
}

impl Matcher {
    /// How far back a match may reach.
    pub closed spec fn window(&self) -> nat {
        self.wmax as nat
    }

    pub closed spec fn wf(&self) -> bool {
        &&& 8 <= self.hbits <= 16
        &&& self.head@.len() == pow2(self.hbits as nat)
        &&& self.fast ==> self.head1@.len() == self.head@.len()
        &&& self.prev@.len() == self.pmask + 1
        &&& self.pmask < WSIZE
        &&& forall|x: usize| #[trigger] (x & self.pmask) <= self.pmask
        &&& 3 <= self.nice <= 258
        &&& 1 <= self.wmax <= WSIZE
    }

    /// Search effort by level, as libdeflate's: (nice, chain).
    fn params(level: u32) -> (r: (usize, usize))
        ensures
            3 <= r.0 <= 258,
            r.1 >= 1,
    {
        if level <= 1 {
            (32, 2)
        } else if level == 2 {
            (10, 6)
        } else if level == 3 {
            (14, 12)
        } else if level == 4 {
            (30, 16)
        } else if level == 5 {
            (30, 16)
        } else if level == 6 {
            (65, 35)
        } else if level == 7 {
            (130, 100)
        } else if level == 8 {
            (258, 300)
        } else {
            (258, 600)
        }
    }

    /// (max_lazy, good_length) by level for the lazy parser: zlib's, but
    /// 32 rather than 16 at levels 5 and 6, which kept the ratio on HTML.
    fn lazy_params(level: u32) -> (r: (usize, usize)) {
        if level <= 7 {
            (32, 8)
        } else if level == 8 {
            (128, 32)
        } else {
            (258, 32)
        }
    }

    /// A matcher for a stream of unknown length. Its hash table has 2^15
    /// entries, as zlib's does: a stream starts with a cleared table, and
    /// for the many short streams (Node makes one per call) clearing 2^16
    /// entries cost more than compressing 1 KiB.
    pub fn new(level: u32) -> (r: Matcher)
        ensures
            r.wf(),
            r.window() == WSIZE,
    {
        Self::new_for(level, 16384)
    }

    /// A matcher for at most `n` bytes of input: the tables shrink to fit.
    pub fn new_for(level: u32, n: usize) -> (r: Matcher)
        ensures
            r.wf(),
            r.window() == WSIZE,
    {
        let (nice, chain) = Self::params(level);
        let (lazy, good) = Self::lazy_params(level);
        // Twice as many hash entries as positions, and a chain entry for
        // every position, up to the full sizes.
        let mut hbits: u32 = 8;
        let mut hsize: usize = 256;
        proof {
            vstd::arithmetic::power2::lemma2_to64();
        }
        while hbits < 16 && hsize < n
            invariant
                8 <= hbits <= 16,
                hsize == pow2(hbits as nat),
                hsize <= 65536,
            decreases 16 - hbits,
        {
            proof {
                vstd::arithmetic::power2::lemma_pow2_unfold((hbits + 1) as nat);
                vstd::arithmetic::power2::lemma2_to64();
                if hbits < 15 {
                    vstd::arithmetic::power2::lemma_pow2_strictly_increases((hbits + 1) as nat, 16);
                }
            }
            hsize = hsize * 2;
            hbits = hbits + 1;
        }
        // A chain entry per position, up to the window: positions of a
        // short input do not share entries.
        let mut pmask: usize = 255;
        while pmask < 16384 && pmask + 1 < n
            invariant
                255 <= pmask <= 32767,
            decreases 32767 - pmask,
        {
            pmask = pmask * 2 + 1;
        }
        proof {
            assert(forall|x: usize| #[trigger] (x & pmask) <= pmask) by (bit_vector);
        }
        Matcher {
            head: vec![0u32; hsize],
            prev: vec![0xffffu16; pmask + 1],
            chain,
            nice,
            lazy,
            good,
            wmax: WSIZE,
            greedy: level <= 4,
            lazy2: level >= 8,
            fast: level <= 1,
            head1: if level <= 1 { vec![0u32; hsize] } else { Vec::new() },
            hbits,
            pmask,
        }
    }

    #[inline(always)]
    fn hash(&self, data: &[u8], p: usize) -> (r: usize)
        requires
            self.wf(),
            p + 4 <= data@.len(),
        ensures
            r < self.head@.len(),
    {
        let x: u64 = if data.len() - p >= 8 {
            let w = verilith_core::prims::load_u64_le(data, p);
            let y = w & 0xffff_ffff;
            assert(y < 0x1_0000_0000) by (bit_vector)
                requires
                    y == w & 0xffff_ffff,
            ;
            y
        } else {
            data[p] as u64 + 256 * data[p + 1] as u64 + 65536 * data[p + 2] as u64 + 16777216 * data[p + 3] as u64
        };
        self.hash_word(x)
    }

    /// The hash of the four bytes in `x`.
    #[inline(always)]
    fn hash_word(&self, x: u64) -> (r: usize)
        requires
            self.wf(),
        ensures
            r < self.head@.len(),
    {
        let m = x.wrapping_mul(2654435761u64);
        // The top `hbits` bits of the 32-bit product.
        let b = self.hbits as u64;
        let sh = 32u64 - b;
        let h = (m & 0xffff_ffff) >> sh;
        proof {
            assert(h < (1u64 << b)) by (bit_vector)
                requires
                    h == (m & 0xffff_ffff) >> sh,
                    sh + b == 32,
                    8 <= b <= 16,
            ;
            vstd::bits::lemma_u64_pow2_no_overflow(b as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, b);
        }
        h as usize
    }

    /// Changes the search effort to `level`'s, keeping the chains.
    pub fn set_level(&mut self, level: u32)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
    {
        let (nice, chain) = Self::params(level);
        self.chain = chain;
        self.nice = nice;
        let (lazy, good) = Self::lazy_params(level);
        self.lazy = lazy;
        self.good = good;
        self.greedy = level <= 4;
        self.lazy2 = level >= 8;
        if level <= 1 && self.head1.len() != self.head.len() {
            self.head1 = vec![0u32; self.head.len()];
        }
        self.fast = level <= 1;
    }

    /// Limits matches to the last `2^bits` bytes (8 <= bits <= 15).
    pub fn set_window(&mut self, bits: u32)
        requires
            old(self).wf(),
            8 <= bits <= 15,
        ensures
            final(self).wf(),
            final(self).window() == (1usize << bits) as nat,
    {
        self.wmax = 1usize << bits;
        proof {
            assert(1usize << bits <= 32768 && 1usize << bits >= 1) by (bit_vector)
                requires
                    8 <= bits <= 15,
            ;
        }
    }

    /// Moves every position down by `k`, a multiple of the window size,
    /// as the data they index loses its first `k` bytes.
    pub fn slide(&mut self, k: usize)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
    {
        let k32 = if k > 0xffff_ffff { 0xffff_ffffu32 } else { k as u32 };
        let mut i: usize = 0;
        while i < self.head.len()
            invariant
                self.wf(),
            decreases self.head@.len() - i,
        {
            let v = self.head[i];
            self.head.set(i, if v > k32 { v - k32 } else { 0 });
            i = i + 1;
        }
        let mut i: usize = 0;
        while i < self.head1.len()
            invariant
                self.wf(),
            decreases self.head1@.len() - i,
        {
            let v = self.head1[i];
            self.head1.set(i, if v > k32 { v - k32 } else { 0 });
            i = i + 1;
        }
    }

    /// Adds position `p` to the chains.
    #[inline(always)]
    fn insert(&mut self, data: &[u8], p: usize)
        requires
            old(self).wf(),
            p < data@.len(),
        ensures
            final(self).wf(),
            final(self).fast == old(self).fast,
            final(self).wmax == old(self).wmax,
    {
        if data.len() - p >= 4 {
            let h = self.hash(data, p);
            if self.fast {
                self.insert_fast(p, h);
            } else {
                self.insert_h(p, h);
            }
        }
    }

    /// Adds position `p`, whose hash is `h`, to the two-entry table.
    #[inline(always)]
    fn insert_fast(&mut self, p: usize, h: usize)
        requires
            old(self).wf(),
            old(self).fast,
            h < old(self).head@.len(),
            p < usize::MAX,
        ensures
            final(self).wf(),
            final(self).fast,
            final(self).wmax == old(self).wmax,
    {
        let c0 = verilith_core::prims::get32(self.head.as_slice(), h);
        verilith_core::prims::set32(self.head1.as_mut_slice(), h, c0);
        verilith_core::prims::set32(self.head.as_mut_slice(), h, (p + 1) as u32);
    }

    /// Whether `v`, a table entry, names a position before `p` inside the
    /// window, and the longest match there, up to `maxlen`.
    #[inline(always)]
    fn try_at(&self, data: &[u8], p: usize, v: u32, maxlen: usize) -> (r: (usize, usize))
        requires
            self.wf(),
            p + maxlen <= data@.len(),
            maxlen <= 258,
        ensures
            r.0 <= maxlen,
            r.0 > 0 ==> 1 <= r.1 <= self.wmax && r.1 <= p && forall|k: int| 0 <= k < r.0 ==> #[trigger] data@[p + k] == data@[p + k - r.1],
    {
        let c = v as usize;
        if c == 0 || c > p || p - (c - 1) > self.wmax {
            return (0, 0);
        }
        let c = c - 1;
        let k = eq_len(data, p, c, maxlen);
        proof {
            assert forall|j: int| 0 <= j < k implies #[trigger] data@[p + j] == data@[p + j - (p - c)] by {
                assert(p + j - (p - c) == c + j);
            }
        }
        (k, p - c)
    }

    /// Adds position `p`, whose hash is `h`, to the chains.
    #[inline(always)]
    fn insert_h(&mut self, p: usize, h: usize)
        requires
            old(self).wf(),
            h < old(self).head@.len(),
            p < usize::MAX,
        ensures
            final(self).wf(),
            final(self).fast == old(self).fast,
            final(self).wmax == old(self).wmax,
    {
        let old_head = verilith_core::prims::get32(self.head.as_slice(), h) as usize;
        // `old_head - 1` is the previous position. A stale, empty or
        // cut value gives a distance that is only a wasted try (or
        // ends the chain), since matches are checked.
        let d = (p + 1).wrapping_sub(old_head);
        let d = if d > 0xffff { 0xffff } else { d };
        crate::prims::set16(self.prev.as_mut_slice(), p & self.pmask, d as u16);
        verilith_core::prims::set32(self.head.as_mut_slice(), h, (p + 1) as u32);
    }

    /// The longest match at `p` longer than `least` among the candidates
    /// tried, or length 0 if none is.
    #[inline(always)]
    fn longest(&self, data: &[u8], p: usize, h: usize, least: usize, chain: usize) -> (r: (usize, usize))
        requires
            self.wf(),
            p < data@.len(),
            h < self.head@.len(),
        ensures
            r.0 == 0 || (r.0 > least && is_match(data@, p as int, r.0 as nat, r.1 as nat) && r.1 <= self.wmax),
    {
        let n = data.len();
        let maxlen = if n - p < 258 { n - p } else { 258 };
        if maxlen < 4 || least >= maxlen {
            return (0, 0);
        }
        // Candidates `c` must satisfy `limit <= c < p`, where `p - limit`
        // is the window.
        let limit = if p > self.wmax { p - self.wmax } else { 0 };
        let hv = verilith_core::prims::get32(self.head.as_slice(), h) as usize;
        if hv == 0 || hv - 1 >= p || hv - 1 < limit {
            return (0, 0);
        }
        let mut c = hv - 1;
        let mut tries = chain;
        // The length to beat: at least 3, for a match to count.
        let mut best: usize = if least < 2 { 2 } else { least };
        let mut found = false;
        let mut bdist: usize = 0;
        // The byte a candidate must match to beat `best`.
        let mut want = verilith_core::prims::get(data, p + best);
        while tries > 0
            invariant_except_break
                best < maxlen,
                want == data@[p + best],
            invariant
                self.wf(),
                n == data@.len(),
                p < n,
                4 <= maxlen <= 258,
                p + maxlen <= n,
                2 <= best <= maxlen,
                best >= least,
                limit <= c < p,
                p - limit <= self.wmax,
                found ==> best > least && best >= 3 && 1 <= bdist <= 32768 && bdist <= p && bdist <= self.wmax && forall|k: int| 0 <= k < best ==> #[trigger] data@[p + k] == data@[p + k - bdist],
            decreases tries,
        {
            // A candidate can only beat `best` if it matches at `best`.
            if verilith_core::prims::get(data, c + best) == want {
                let k = eq_len(data, p, c, maxlen);
                if k > best {
                    best = k;
                    found = true;
                    bdist = p - c;
                    proof {
                        assert forall|j: int| 0 <= j < best implies #[trigger] data@[p + j] == data@[p + j - bdist] by {
                            assert(p + j - bdist == c + j);
                        }
                    }
                    if k >= self.nice || k >= maxlen {
                        break;
                    }
                    want = verilith_core::prims::get(data, p + best);
                }
            }
            // No previous position is stored as a distance of 0xffff,
            // farther than any window.
            let d = crate::prims::get16(self.prev.as_slice(), c & self.pmask) as usize;
            if d > c - limit {
                break;
            }
            c = c - d;
            tries = tries - 1;
        }
        if found {
            (best, bdist)
        } else {
            (0, 0)
        }
    }

    /// Searches for a match at `p` longer than `least`, then adds `p` to
    /// the chains.
    #[inline(always)]
    fn search(&mut self, data: &[u8], p: usize, least: usize, chain: usize) -> (r: (usize, usize))
        requires
            old(self).wf(),
            p < data@.len(),
        ensures
            final(self).wf(),
            final(self).wmax == old(self).wmax,
            r.0 == 0 || (r.0 > least && is_match(data@, p as int, r.0 as nat, r.1 as nat) && r.1 <= old(self).wmax),
    {
        if data.len() - p < 4 {
            return (0, 0);
        }
        let h = self.hash(data, p);
        let r = self.longest(data, p, h, least, chain);
        self.insert_h(p, h);
        r
    }

    /// `hash` for a position with 8 bytes after it.
    #[inline(always)]
    fn hash8(&self, data: &[u8], p: usize) -> (r: usize)
        requires
            self.wf(),
            p + 8 <= data@.len(),
        ensures
            r < self.head@.len(),
    {
        // The low 32 bits of the product depend only on the first four
        // bytes.
        self.hash_word(verilith_core::prims::load_u64_le(data, p))
    }

    /// Adds every position of `data` to the chains: a preset dictionary's,
    /// so that matches can be found into it.
    pub fn prime(&mut self, data: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
    {
        self.insert_range(data, 0, data.len());
    }

    /// Adds positions `from` to `to` (exclusive) to the chains.
    #[inline(always)]
    fn insert_range(&mut self, data: &[u8], from: usize, to: usize)
        requires
            old(self).wf(),
            to <= data@.len(),
        ensures
            final(self).wf(),
            final(self).fast == old(self).fast,
            final(self).wmax == old(self).wmax,
    {
        let n = data.len();
        // Positions with 8 bytes after them, without the checks per byte.
        let mid = if n < 8 { 0 } else if to <= n - 7 { to } else { n - 7 };
        let mut q = from;
        if self.fast {
            while q < mid
                invariant
                    self.wf(),
                    self.fast,
                    self.wmax == old(self).wmax,
                    n == data@.len(),
                    mid == 0 || mid + 7 <= n,
                decreases mid - q,
            {
                let h = self.hash8(data, q);
                self.insert_fast(q, h);
                q = q + 1;
            }
        } else {
            while q < mid
                invariant
                    self.wf(),
                    self.fast == old(self).fast,
                    self.wmax == old(self).wmax,
                    n == data@.len(),
                    mid == 0 || mid + 7 <= n,
                decreases mid - q,
            {
                let h = self.hash8(data, q);
                self.insert_h(q, h);
                q = q + 1;
            }
        }
        while q < to
            invariant
                self.wf(),
                self.fast == old(self).fast,
                self.wmax == old(self).wmax,
                to <= data@.len(),
            decreases to - q,
        {
            self.insert(data, q);
            q = q + 1;
        }
    }

    /// `fill` for level 1: greedy, with two candidates per position.
    fn fill_fast(&mut self, data: &[u8], start: usize, toks: &mut Vec<u32>, fr: &mut Freqs, limit: usize) -> (e: usize)
        requires
            old(fr).ok(Seq::empty()),
            limit + 2 < MAX_TOKS,
            old(self).wf(),
            old(self).fast,
            start < data@.len(),
            old(toks)@.len() == 0,
            limit >= 1,
        ensures
            final(self).wf(),
            start < e <= data@.len(),
            toks_ok(data@.subrange(0, start as int), final(toks)@),
            expand(data@.subrange(0, start as int), final(toks)@) == data@.subrange(0, e as int),
            forall|i: int| 0 <= i < final(toks)@.len() ==> #[trigger] tok_valid(final(toks)@[i]),
            forall|i: int| 0 <= i < final(toks)@.len() ==> #[trigger] tok_within(final(toks)@[i], old(self).window()),
            final(self).window() == old(self).window(),
            final(toks)@.len() <= limit + 1,
            final(fr).ok(final(toks)@),
    {
        let n = data.len();
        let ghost out0 = data@.subrange(0, start as int);
        let mut p = start;
        proof {
            assert(expand(out0, toks@) == out0);
            assert(toks_ok(out0, toks@));
        }
        while p < n && toks.len() < limit
            invariant
                self.wf(),
                self.fast,
                n == data@.len(),
                out0 == data@.subrange(0, start as int),
                start <= p <= n,
                toks_ok(out0, toks@),
                expand(out0, toks@) == data@.subrange(0, p as int),
                forall|i: int| 0 <= i < toks@.len() ==> #[trigger] tok_valid(toks@[i]),
                forall|i: int| 0 <= i < toks@.len() ==> #[trigger] tok_within(toks@[i], self.wmax as nat),
                self.wmax == old(self).wmax,
                p > start || (p == start && toks@.len() == 0),
                limit >= 1,
                toks@.len() <= limit,
                fr.ok(toks@),
                limit + 2 < MAX_TOKS,
            decreases n - p,
        {
            let mut ml: usize = 0;
            let mut md: usize = 0;
            if n - p >= 4 {
                let maxlen = if n - p < 258 { n - p } else { 258 };
                let h = self.hash(data, p);
                let c0 = verilith_core::prims::get32(self.head.as_slice(), h);
                let c1 = verilith_core::prims::get32(self.head1.as_slice(), h);
                self.insert_fast(p, h);
                let (k0, d0) = self.try_at(data, p, c0, maxlen);
                let (k1, d1) = self.try_at(data, p, c1, maxlen);
                let (k, d) = if k1 > k0 { (k1, d1) } else { (k0, d0) };
                if k >= 4 || (k == 3 && d <= 8192) {
                    ml = k;
                    md = d;
                }
            }
            if ml > 0 {
                let t = (ml * 65536 + md) as u32;
                proof {
                    lemma_match_tok(ml as nat, md as nat);
                    lemma_expand_push(out0, toks@, t);
                    lemma_copy_data(data@, p as int, md as nat, ml as nat);
                }
                emit_within(toks, fr, t, Ghost(self.wmax as nat));
                let end = p + ml;
                self.insert_range(data, p + 1, end);
                p = end;
            } else {
                let t = data[p] as u32;
                proof {
                    lemma_expand_push(out0, toks@, t);
                    assert(data@.subrange(0, p as int).push(t as u8) =~= data@.subrange(0, p + 1));
                }
                emit_within(toks, fr, t, Ghost(self.wmax as nat));
                p = p + 1;
            }
        }
        p
    }

    /// `fill` without lazy matching.
    fn fill_greedy(&mut self, data: &[u8], start: usize, toks: &mut Vec<u32>, fr: &mut Freqs, limit: usize) -> (e: usize)
        requires
            old(fr).ok(Seq::empty()),
            limit + 2 < MAX_TOKS,
            old(self).wf(),
            start < data@.len(),
            old(toks)@.len() == 0,
            limit >= 1,
        ensures
            final(self).wf(),
            start < e <= data@.len(),
            toks_ok(data@.subrange(0, start as int), final(toks)@),
            expand(data@.subrange(0, start as int), final(toks)@) == data@.subrange(0, e as int),
            forall|i: int| 0 <= i < final(toks)@.len() ==> #[trigger] tok_valid(final(toks)@[i]),
            forall|i: int| 0 <= i < final(toks)@.len() ==> #[trigger] tok_within(final(toks)@[i], old(self).window()),
            final(self).window() == old(self).window(),
            final(toks)@.len() <= limit + 1,
            final(fr).ok(final(toks)@),
    {
        let n = data.len();
        let ghost out0 = data@.subrange(0, start as int);
        let mut p = start;
        proof {
            assert(expand(out0, toks@) == out0);
            assert(toks_ok(out0, toks@));
        }
        while p < n && toks.len() < limit
            invariant
                self.wf(),
                n == data@.len(),
                out0 == data@.subrange(0, start as int),
                start <= p <= n,
                toks_ok(out0, toks@),
                expand(out0, toks@) == data@.subrange(0, p as int),
                forall|i: int| 0 <= i < toks@.len() ==> #[trigger] tok_valid(toks@[i]),
                forall|i: int| 0 <= i < toks@.len() ==> #[trigger] tok_within(toks@[i], self.wmax as nat),
                self.wmax == old(self).wmax,
                p > start || (p == start && toks@.len() == 0),
                limit >= 1,
                toks@.len() <= limit,
                fr.ok(toks@),
                limit + 2 < MAX_TOKS,
            decreases n - p,
        {
            let (ml, md) = self.search(data, p, 2, self.chain);
            // A 3-byte match far back costs about as much as its literals.
            if ml > 0 && (ml > 3 || md <= 8192) {
                let t = (ml * 65536 + md) as u32;
                proof {
                    lemma_match_tok(ml as nat, md as nat);
                    lemma_expand_push(out0, toks@, t);
                    lemma_copy_data(data@, p as int, md as nat, ml as nat);
                }
                emit_within(toks, fr, t, Ghost(self.wmax as nat));
                let end = p + ml;
                self.insert_range(data, p + 1, end);
                p = end;
            } else {
                let t = data[p] as u32;
                proof {
                    lemma_expand_push(out0, toks@, t);
                    assert(data@.subrange(0, p as int).push(t as u8) =~= data@.subrange(0, p + 1));
                }
                emit_within(toks, fr, t, Ghost(self.wmax as nat));
                p = p + 1;
            }
        }
        p
    }

    /// Whether a match of `nl` bytes `nd` back, one position later, is
    /// worth a literal more than the match of `cl` bytes `cd` back:
    /// libdeflate's rule, which weighs 4 per byte of length against the
    /// bits of the distances, and needs more than `margin`.
    #[inline(always)]
    fn better(cl: usize, cd: usize, nl: usize, nd: usize, margin: i64) -> bool
        requires
            cl <= 258 && nl <= 258,
    {
        if nl < cl {
            return false;
        }
        let bc = 64 - (cd as u64).leading_zeros() as i64;
        let bn = 64 - (nd as u64).leading_zeros() as i64;
        proof {
            vstd::std_specs::bits::axiom_u64_leading_zeros(cd as u64);
            vstd::std_specs::bits::axiom_u64_leading_zeros(nd as u64);
        }
        4 * ((nl - cl) as i64) + (bc - bn) > margin
    }

    /// Finds tokens for the input from `start`, at most about `limit` of
    /// them, and returns where they end.
    pub fn fill(&mut self, data: &[u8], start: usize, toks: &mut Vec<u32>, fr: &mut Freqs, limit: usize) -> (e: usize)
        requires
            old(fr).ok(Seq::empty()),
            limit + 2 < MAX_TOKS,
            old(self).wf(),
            start < data@.len(),
            old(toks)@.len() == 0,
            limit >= 1,
        ensures
            final(self).wf(),
            start < e <= data@.len(),
            toks_ok(data@.subrange(0, start as int), final(toks)@),
            expand(data@.subrange(0, start as int), final(toks)@) == data@.subrange(0, e as int),
            forall|i: int| 0 <= i < final(toks)@.len() ==> #[trigger] tok_valid(final(toks)@[i]),
            forall|i: int| 0 <= i < final(toks)@.len() ==> #[trigger] tok_within(final(toks)@[i], old(self).window()),
            final(self).window() == old(self).window(),
            final(toks)@.len() <= limit + 1,
            final(fr).ok(final(toks)@),
    {
        if self.fast {
            return self.fill_fast(data, start, toks, fr, limit);
        }
        if self.greedy {
            return self.fill_greedy(data, start, toks, fr, limit);
        }
        let n = data.len();
        let ghost out0 = data@.subrange(0, start as int);
        let mut p = start;
        // A match found at `p`, already in the chains, not yet taken.
        let mut have = false;
        let mut cl: usize = 0;
        let mut cd: usize = 0;
        proof {
            assert(expand(out0, toks@) == out0);
            assert(toks_ok(out0, toks@));
        }
        while p < n && toks.len() < limit
            invariant
                self.wf(),
                n == data@.len(),
                out0 == data@.subrange(0, start as int),
                start <= p <= n,
                toks_ok(out0, toks@),
                expand(out0, toks@) == data@.subrange(0, p as int),
                forall|i: int| 0 <= i < toks@.len() ==> #[trigger] tok_valid(toks@[i]),
                forall|i: int| 0 <= i < toks@.len() ==> #[trigger] tok_within(toks@[i], self.wmax as nat),
                self.wmax == old(self).wmax,
                have ==> p < n && is_match(data@, p as int, cl as nat, cd as nat) && cd <= self.wmax,
                have ==> toks@.len() < limit,
                p > start || toks@.len() == 0,
                limit >= 1,
                toks@.len() <= limit,
                fr.ok(toks@),
                limit + 2 < MAX_TOKS,
            decreases n - p, if have { 0int } else { 1int },
        {
            if !have {
                let (ml, md) = self.search(data, p, 2, self.chain);
                if ml > 0 && (ml > 3 || md <= 8192) {
                    have = true;
                    cl = ml;
                    cd = md;
                } else {
                    let t = data[p] as u32;
                    proof {
                        lemma_expand_push(out0, toks@, t);
                        assert(data@.subrange(0, p as int).push(t as u8) =~= data@.subrange(0, p + 1));
                    }
                    emit_within(toks, fr, t, Ghost(self.wmax as nat));
                    p = p + 1;
                }
                continue;
            }
            // Look ahead unless the match is long enough already, or there
            // is no room for the literals a better match would add.
            let mut take_at = 1usize;
            if cl < self.nice && p + 1 < n && limit - toks.len() >= 3 {
                // From a match of `lazy` or more, one candidate only: a
                // longer match there is rare, and full lookahead took a
                // third of the time on HTML (zlib does none).
                let effort = if cl >= self.lazy { 1 } else if cl >= self.good { self.chain / 4 + 1 } else { self.chain / 2 + 1 };
                let (nl, nd) = self.search(data, p + 1, cl - 1, effort);
                take_at = 2;
                if nl > 0 && Self::better(cl, cd, nl, nd, 2) {
                    let t = data[p] as u32;
                    proof {
                        lemma_expand_push(out0, toks@, t);
                        assert(data@.subrange(0, p as int).push(t as u8) =~= data@.subrange(0, p + 1));
                    }
                    emit_within(toks, fr, t, Ghost(self.wmax as nat));
                    p = p + 1;
                    cl = nl;
                    cd = nd;
                    continue;
                }
                if self.lazy2 && p + 2 < n {
                    let (ml, md) = self.search(data, p + 2, cl - 1, self.chain / 4 + 1);
                    take_at = 3;
                    if ml > 0 && Self::better(cl, cd, ml, md, 6) {
                        let t1 = data[p] as u32;
                        let t2 = data[p + 1] as u32;
                        proof {
                            lemma_expand_push(out0, toks@, t1);
                            assert(data@.subrange(0, p as int).push(t1 as u8) =~= data@.subrange(0, p + 1));
                            lemma_expand_push(out0, toks@.push(t1), t2);
                            assert(data@.subrange(0, p + 1).push(t2 as u8) =~= data@.subrange(0, p + 2));
                        }
                        emit_within(toks, fr, t1, Ghost(self.wmax as nat));
                        emit_within(toks, fr, t2, Ghost(self.wmax as nat));
                        p = p + 2;
                        cl = ml;
                        cd = md;
                        continue;
                    }
                }
            }
            let t = (cl * 65536 + cd) as u32;
            proof {
                lemma_match_tok(cl as nat, cd as nat);
                lemma_expand_push(out0, toks@, t);
                lemma_copy_data(data@, p as int, cd as nat, cl as nat);
            }
            emit_within(toks, fr, t, Ghost(self.wmax as nat));
            let end = p + cl;
            self.insert_range(data, p + take_at, end);
            p = end;
            have = false;
        }
        p
    }
}


// ---------------------------------------------------------------------------
// Code lengths
// ---------------------------------------------------------------------------

/// Huffman code lengths of at most `maxbits` bits for the frequencies
/// `freq`: a Huffman tree, then lengths over `maxbits` shortened as miniz
/// does. Only the ratio depends on this; the caller checks the lengths.
pub fn huff_lens(freq: &[u32], maxbits: usize) -> (r: Vec<u8>)
    requires
        freq@.len() <= 320,
        1 <= maxbits <= 15,
    ensures
        r@.len() == freq@.len(),
{
    let nsym = freq.len();
    let mut lens: Vec<u8> = vec![0u8; nsym];
    // The symbols used, by increasing frequency (ties by symbol): sort
    // `freq << 9 | symbol` keys, then read the symbols back, checking each.
    let mut keys: Vec<u64> = Vec::with_capacity(nsym);
    let mut s: usize = 0;
    while s < nsym
        invariant
            s <= nsym,
            nsym == freq@.len(),
            nsym <= 320,
            lens@.len() == nsym,
        decreases nsym - s,
    {
        if freq[s] > 0 {
            keys.push(((freq[s] as u64) << 9u64) | s as u64);
        }
        s = s + 1;
    }
    let by_key = |a: usize, b: usize| -> (r: bool)
        requires
            a < keys@.len(),
            b < keys@.len(),
        ensures
            r == (keys@[a as int] <= keys@[b as int]),
        { keys[a] <= keys[b] };
    let ord = order_by(keys.len(), &by_key, Ghost(|a: usize, b: usize| keys@[a as int] <= keys@[b as int]));
    let mut syms: Vec<usize> = Vec::with_capacity(keys.len());
    let mut i: usize = 0;
    while i < ord.len()
        invariant
            i <= ord@.len(),
            ord@.len() == keys@.len(),
            below(ord@, keys@.len()),
            nsym == freq@.len(),
            lens@.len() == nsym,
            syms@.len() <= i,
            forall|k: int| 0 <= k < syms@.len() ==> #[trigger] syms@[k] < nsym,
        decreases ord@.len() - i,
    {
        let sym = (keys[ord[i]] & 511) as usize;
        if sym >= nsym {
            return lens;
        }
        syms.push(sym);
        i = i + 1;
    }
    let m = syms.len();
    if m > nsym {
        return lens;
    }
    if m == 0 {
        return lens;
    }
    if m == 1 {
        lens.set(syms[0], 1);
        return lens;
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
            m == syms@.len(),
            nsym == freq@.len(),
            w@.len() == total,
            total == 2 * m - 1,
            forall|q: int| 0 <= q < syms@.len() ==> #[trigger] syms@[q] < nsym,
            forall|q: int| 0 <= q < k ==> #[trigger] w@[q] < 0x1_0000_0000,
            lens@.len() == nsym,
            nsym == freq@.len(),
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
            total == 2 * m - 1,
            m >= 2,
            m <= 320,
            leaf <= m,
            m <= node <= k,
            w@.len() == total,
            parent@.len() == total,
            forall|q: int| 0 <= q < total ==> #[trigger] parent@[q] < total,
            lens@.len() == nsym,
            nsym == freq@.len(),
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
                pair@.len() == 2,
                w@.len() == total,
                total == 2 * m - 1,
                lens@.len() == nsym,
            nsym == freq@.len(),
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
                // Not reachable for a well-formed queue; give up safely.
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
    // Depths, from the root down: a parent comes after its children, so
    // `parent[x]` becomes `x`'s depth once `x`'s parent's depth is known.
    let mut depth = parent;
    depth.set(total - 1, 0);
    let mut x = total - 1;
    while x > 0
        invariant
            x < total,
            depth@.len() == total,
            forall|q: int| 0 <= q < total ==> #[trigger] depth@[q] <= total,
            lens@.len() == nsym,
            nsym == freq@.len(),
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
            m <= 320,
            depth@.len() == total,
            total == 2 * m - 1,
            1 <= maxbits <= 15,
            forall|z: int| 0 <= z < 16 ==> #[trigger] count@[z] <= q,
            count@.len() == 16,
            lens@.len() == nsym,
            nsym == freq@.len(),
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
    // Make the code fit: while the code space is over-subscribed, move a
    // code from the longest length to a shorter one's subtree.
    let mut kraft: u64 = 0;
    let mut l: usize = 1;
    while l <= maxbits
        invariant
            1 <= l <= maxbits + 1,
            maxbits <= 15,
            forall|z: int| 0 <= z < 16 ==> #[trigger] count@[z] <= 320,
            count@.len() == 16,
            lens@.len() == nsym,
            nsym == freq@.len(),
            kraft <= 320 * 32768 * l,
        decreases maxbits + 1 - l,
    {
        proof {
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma_pow2_strictly_increases((maxbits - l) as nat, 15);
        }
        let sh = (maxbits - l) as u64;
        proof {
            assert((1u64 << sh) <= 32768) by {
                crate::ilemmas::lemma_mask(sh);
                if sh < 15 {
                    vstd::arithmetic::power2::lemma_pow2_strictly_increases(sh as nat, 15);
                }
            }
            assert(count@[l as int] * (1u64 << sh) <= 320 * 32768) by (nonlinear_arith)
                requires
                    count@[l as int] <= 320,
                    (1u64 << sh) <= 32768,
            ;
        }
        kraft = kraft + count[l] * (1u64 << sh);
        l = l + 1;
    }
    let full: u64 = 1u64 << (maxbits as u64);
    while kraft > full
        invariant
            maxbits <= 15,
            1 <= maxbits,
            count@.len() == 16,
            lens@.len() == nsym,
            nsym == freq@.len(),
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
                count@.len() == 16,
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
            m == syms@.len(),
            nsym == freq@.len(),
            lens@.len() == nsym,
            nsym == freq@.len(),
            count@.len() == 16,
            forall|q: int| 0 <= q < syms@.len() ==> #[trigger] syms@[q] < nsym,
        decreases l,
    {
        let mut c = count[l];
        while c > 0 && idx < m
            invariant
                idx <= m,
                m == syms@.len(),
                lens@.len() == nsym,
            nsym == freq@.len(),
                1 <= l <= 15,
                forall|q: int| 0 <= q < syms@.len() ==> #[trigger] syms@[q] < nsym,
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


// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

/// Writes `raw` as stored blocks, the last final when `fin` is.
pub fn emit_stored(enc: &mut Encoder, raw: &[u8], fin: bool)
    requires
        old(enc).inv(),
        !old(enc).done@,
    ensures
        final(enc).inv(),
        final(enc).out() == old(enc).out() + raw@,
        final(enc).done@ == fin,
        final(enc).head == old(enc).head && final(enc).base == old(enc).base && final(enc).bw.sent() == old(enc).bw.sent(),
        final(enc).bw.bits().len() % 8 == 0,
{
    let n = raw.len();
    let ghost o0 = enc.out();
    let mut pos: usize = 0;
    let mut more = true;
    while more
        invariant
            n == raw@.len(),
            pos <= n,
            enc.inv(),
            more ==> !enc.done@,
            !more ==> enc.done@ == fin && pos == n && enc.bw.bits().len() % 8 == 0,
            enc.out() == o0 + raw@.subrange(0, pos as int),
            enc.head == old(enc).head && enc.base == old(enc).base,
            enc.bw.sent() == old(enc).bw.sent(),
        decreases n - pos + if more { 1int } else { 0int },
    {
        let c = if n - pos > 65535 { 65535 } else { n - pos };
        let last = pos + c == n;
        let chunk = vstd::slice::slice_subrange(raw, pos, pos + c);
        enc.stored(chunk, fin && last);
        proof {
            assert(raw@.subrange(0, pos as int) + raw@.subrange(pos as int, (pos + c) as int) =~= raw@.subrange(0, (pos + c) as int));
        }
        pos = pos + c;
        if last {
            more = false;
        }
    }
    proof {
        assert(raw@.subrange(0, n as int) =~= raw@);
    }
}

/// Cuts trailing zero lengths, keeping at least `min`.
fn trim(lens: &mut Vec<u8>, min: usize)
    requires
        min <= old(lens)@.len(),
    ensures
        min <= final(lens)@.len() <= old(lens)@.len(),
        final(lens)@ == old(lens)@.subrange(0, final(lens)@.len() as int),
{
    let mut k = lens.len();
    while k > min && lens[k - 1] == 0
        invariant
            min <= k <= lens@.len(),
        decreases k,
    {
        k = k - 1;
    }
    lens.truncate(k);
}

/// Writes `ts` as one block with codes fitted to its symbols, if that
/// checks and is smaller than storing `nraw` bytes. Otherwise leaves
/// `enc` as it was and returns false.
/// Writes `ts` as a fixed-code block, unless the fixed code tables fail
/// their check (they do not; the check is what proves them).
fn try_fixed(enc: &mut Encoder, ts: &[u32], sy: &[u16], fin: bool) -> (r: bool)
    requires
        old(enc).inv(),
        !old(enc).done@,
        toks_ok(old(enc).out(), ts@),
        syms_for(ts@, sy@),
        forall|i: int| 0 <= i < ts@.len() ==> #[trigger] tok_valid(ts@[i]),
    ensures
        r ==> final(enc).inv() && final(enc).out() == expand(old(enc).out(), ts@) && final(enc).done@ == fin
            && final(enc).head == old(enc).head && final(enc).base == old(enc).base && final(enc).bw.sent() == old(enc).bw.sent(),
        !r ==> *final(enc) == *old(enc),
{
    if enc.fx.0.is_none() {
        match FixedCodes::build() {
            Some(f) => {
                enc.fx = FxSlot(Some(f));
            },
            None => {
                return false;
            },
        }
    }
    let fx = match enc.fx.0.take() {
        Some(f) => f,
        None => {
            return false;
        },
    };
    proof {
        use_type_invariant(&fx);
    }
    assert forall|k: int| 0 <= k < ts@.len() implies #[trigger] tok_coded(fx.lit@, fx.dist@, ts@[k]) && tok_valid(ts@[k]) by {
        assert(tok_valid(ts@[k]));
        if !is_lit(ts@[k]) {
            lemma_lidx(tlen(ts@[k]));
            lemma_didx(tdist(ts@[k]));
        }
    }
    enc.fixed(ts, sy, &fx.lit, &fx.lcodes, &fx.dist, &fx.dcodes, fin);
    enc.fx = FxSlot(Some(fx));
    true
}

pub fn try_dynamic(enc: &mut Encoder, ts: &[u32], fr: &Freqs, nraw: usize, fin: bool) -> (r: bool)
    requires
        old(enc).inv(),
        !old(enc).done@,
        ts@.len() <= 0x10_0000,
        fr.ok(ts@),
        toks_ok(old(enc).out(), ts@),
        forall|i: int| 0 <= i < ts@.len() ==> #[trigger] tok_valid(ts@[i]),
    ensures
        r ==> final(enc).inv() && final(enc).out() == expand(old(enc).out(), ts@) && final(enc).done@ == fin
            && final(enc).head == old(enc).head && final(enc).base == old(enc).base && final(enc).bw.sent() == old(enc).bw.sent(),
        !r ==> *final(enc) == *old(enc),
{
    let n = ts.len();
    let lf = fr.lf.as_slice();
    let df = fr.df.as_slice();
    let sy = fr.sy.as_slice();
    let mut lit = huff_lens(lf, 15);
    let mut dist = huff_lens(df, 15);
    trim(&mut lit, 257);
    trim(&mut dist, 1);
    let mut lcode = Code::new();
    let mut dcode = Code::new();
    if !check_lens(&mut lcode, &lit, true) || !check_lens(&mut dcode, &dist, true) || lit[256] == 0 {
        return false;
    }
    // Every symbol used must have a code, so every token has one.
    let mut q: usize = 0;
    while q < 286
        invariant
            q <= 286,
            lf@.len() == 286,
            forall|k: int| 0 <= k < q && #[trigger] lf@[k] >= 1 ==> k < lit@.len() && lit@[k] >= 1,
        decreases 286 - q,
    {
        if lf[q] > 0 && (q >= lit.len() || lit[q] == 0) {
            return false;
        }
        q = q + 1;
    }
    let mut q: usize = 0;
    while q < 30
        invariant
            q <= 30,
            df@.len() == 30,
            forall|k: int| 0 <= k < q && #[trigger] df@[k] >= 1 ==> k < dist@.len() && dist@[k] >= 1,
        decreases 30 - q,
    {
        if df[q] > 0 && (q >= dist.len() || dist[q] == 0) {
            return false;
        }
        q = q + 1;
    }
    assert forall|k: int| 0 <= k < n implies #[trigger] tok_coded(lit@, dist@, ts@[k]) by {
        assert(tok_counted(lf@, df@, ts@[k]));
        assert(tok_valid(ts@[k]));
        if is_lit(ts@[k]) {
            assert(lf@[ts@[k] as int] >= 1);
        } else {
            lemma_lidx(tlen(ts@[k]));
            lemma_didx(tdist(ts@[k]));
            assert(lf@[257 + lidx(tlen(ts@[k]))] >= 1);
            assert(df@[didx(tdist(ts@[k]))] >= 1);
        }
    }
    // The code length code.
    let nl = lit.len();
    let nd = dist.len();
    let mut cf: Vec<u32> = vec![0u32; 19];
    let mut j: usize = 0;
    while j < nl + nd
        invariant
            nl == lit@.len(),
            nd == dist@.len(),
            nl <= 286,
            nd <= 30,
            j <= nl + nd,
            cf@.len() == 19,
            forall|k: int| 0 <= k < 19 ==> #[trigger] cf@[k] <= j,
        decreases nl + nd - j,
    {
        let x = if j < nl { lit[j] } else { dist[j - nl] };
        if x < 19 {
            cf.set(x as usize, cf[x as usize] + 1);
        }
        j = j + 1;
    }
    let mut used: usize = 0;
    let mut k: usize = 0;
    while k < 19
        invariant
            k <= 19,
            used <= k,
            cf@.len() == 19,
        decreases 19 - k,
    {
        if cf[k] > 0 {
            used = used + 1;
        }
        k = k + 1;
    }
    // The decoder wants at least two code length codes.
    if used < 2 {
        if cf[0] == 0 {
            cf.set(0, 1);
        } else {
            cf.set(1, 1);
        }
    }
    let cl = huff_lens(&cf, 7);
    let mut ccode = Code::new();
    if !check_lens(&mut ccode, &cl, false) {
        return false;
    }
    let mut k: usize = 0;
    while k < 19
        invariant
            k <= 19,
            cl@.len() == 19,
            forall|q: int| 0 <= q < k ==> #[trigger] cl@[q] < 8,
        decreases 19 - k,
    {
        if cl[k] >= 8 {
            return false;
        }
        k = k + 1;
    }
    let mut j: usize = 0;
    while j < nl + nd
        invariant
            nl == lit@.len(),
            nd == dist@.len(),
            nl <= 286,
            nd <= 30,
            j <= nl + nd,
            cl@.len() == 19,
            forall|q: int| 0 <= q < j ==> #[trigger] (lit@ + dist@)[q] < 16 && 1 <= cl@[(lit@ + dist@)[q] as int],
        decreases nl + nd - j,
    {
        let x = if j < nl { lit[j] } else { dist[j - nl] };
        assert((lit@ + dist@)[j as int] == x);
        if x >= 16 || cl[x as usize] == 0 {
            return false;
        }
        j = j + 1;
    }
    proof {
        crate::ilemmas::lemma_clen_order();
    }
    let mut hclen: usize = 19;
    while hclen > 4 && cl[crate::inflate::CLEN_ORDER[hclen - 1] as usize] == 0
        invariant
            4 <= hclen <= 19,
            cl@.len() == 19,
            forall|q: int| hclen <= q < 19 ==> #[trigger] cl@[clen_order()[q] as int] == 0,
            forall|i: int| 0 <= i < 19 ==> #[trigger] crate::inflate::CLEN_ORDER@[i] as nat == clen_order()[i]
                && clen_order()[i] < 19,
        decreases hclen,
    {
        hclen = hclen - 1;
    }
    proof {
        crate::ilemmas::lemma_clen_order();
        assert forall|s: int| 0 <= s < 19 && clen_slot()[s] >= hclen implies #[trigger] cl@[s] == 0 by {
            let q = clen_slot()[s] as int;
            assert(clen_order()[q] == s);
            assert(cl@[clen_order()[q] as int] == 0);
        }
        assert(dyn_ok(cl@, hclen as nat, lit@, dist@));
    }
    let lcodes = canon_codes(&lcode, &lit);
    let dcodes = canon_codes(&dcode, &dist);
    let clcodes = canon_codes(&ccode, &cl);
    // The block's size against storing.
    let mut bits: u64 = 17 + 3 * hclen as u64;
    let mut j: usize = 0;
    while j < nl + nd
        invariant
            nl == lit@.len(),
            nd == dist@.len(),
            nl <= 286,
            nd <= 30,
            j <= nl + nd,
            cl@.len() == 19,
            bits <= 400 + 8 * j,
        decreases nl + nd - j,
    {
        let x = if j < nl { lit[j] } else { dist[j - nl] };
        if (x as usize) < 19 && cl[x as usize] < 8 {
            bits = bits + cl[x as usize] as u64;
        }
        j = j + 1;
    }
    proof {
        crate::ilemmas::lemma_tables();
    }
    // The symbols' bits, from their counts (end of block included).
    let mut q: usize = 0;
    while q < nl
        invariant
            nl == lit@.len(),
            nl <= 286,
            q <= nl,
            lf@.len() == 286,
            n <= 0x10_0000,
            forall|k: int| 0 <= k < 286 ==> #[trigger] lf@[k] <= n + 1,
            forall|k: int| 0 <= k < lit@.len() ==> #[trigger] lit@[k] <= 15,
            forall|k: int| 0 <= k < 29 ==> #[trigger] crate::huffman::LEN_EXTRA@[k] <= 5,
            bits <= 3000 + 0x200_0000 * q,
        decreases nl - q,
    {
        let w: u64 = if q >= 257 { lit[q] as u64 + crate::huffman::LEN_EXTRA[q - 257] as u64 } else { lit[q] as u64 };
        let f = lf[q] as u64;
        assert(f * w <= 0x200_0000) by (nonlinear_arith)
            requires
                f <= 0x10_0001,
                w <= 20,
        ;
        bits = bits + f * w;
        q = q + 1;
    }
    let mut q: usize = 0;
    while q < nd
        invariant
            nd == dist@.len(),
            nd <= 30,
            nl <= 286,
            q <= nd,
            df@.len() == 30,
            n <= 0x10_0000,
            forall|k: int| 0 <= k < 30 ==> #[trigger] df@[k] <= n,
            forall|k: int| 0 <= k < dist@.len() ==> #[trigger] dist@[k] <= 15,
            forall|k: int| 0 <= k < 30 ==> #[trigger] crate::huffman::DIST_EXTRA@[k] <= 13,
            bits <= 3000 + 0x200_0000 * (nl + q),
        decreases nd - q,
    {
        let w: u64 = dist[q] as u64 + crate::huffman::DIST_EXTRA[q] as u64;
        let f = df[q] as u64;
        assert(f * w <= 0x200_0000) by (nonlinear_arith)
            requires
                f <= 0x10_0000,
                w <= 28,
        ;
        bits = bits + f * w;
        q = q + 1;
    }
    let stored_bits: u64 = if nraw as u64 >= 0x1_0000_0000_0000 {
        0xffff_ffff_ffff_ffff
    } else {
        8 * (nraw as u64) + 40 * (nraw as u64 / 65535 + 1)
    };
    // The same tokens with the fixed codes: 3 header bits and no tables.
    let mut fbits: u64 = 3;
    let mut q: usize = 0;
    while q < 286
        invariant
            q <= 286,
            lf@.len() == 286,
            n <= 0x10_0000,
            forall|k: int| 0 <= k < 286 ==> #[trigger] lf@[k] <= n + 1,
            forall|k: int| 0 <= k < 29 ==> #[trigger] crate::huffman::LEN_EXTRA@[k] <= 5,
            fbits <= 3 + 0x200_0000 * q,
        decreases 286 - q,
    {
        let l: u64 = if q < 144 { 8 } else if q < 256 { 9 } else if q < 280 { 7 } else { 8 };
        let w: u64 = if q >= 257 { l + crate::huffman::LEN_EXTRA[q - 257] as u64 } else { l };
        let f = lf[q] as u64;
        assert(f * w <= 0x200_0000) by (nonlinear_arith)
            requires
                f <= 0x10_0001,
                w <= 20,
        ;
        fbits = fbits + f * w;
        q = q + 1;
    }
    let mut q: usize = 0;
    while q < 30
        invariant
            q <= 30,
            df@.len() == 30,
            n <= 0x10_0000,
            forall|k: int| 0 <= k < 30 ==> #[trigger] df@[k] <= n,
            forall|k: int| 0 <= k < 30 ==> #[trigger] crate::huffman::DIST_EXTRA@[k] <= 13,
            fbits <= 3 + 0x200_0000 * (286 + q),
        decreases 30 - q,
    {
        let w: u64 = 5 + crate::huffman::DIST_EXTRA[q] as u64;
        let f = df[q] as u64;
        assert(f * w <= 0x200_0000) by (nonlinear_arith)
            requires
                f <= 0x10_0000,
                w <= 18,
        ;
        fbits = fbits + f * w;
        q = q + 1;
    }
    if fbits < bits && fbits < stored_bits {
        if try_fixed(enc, ts, &sy, fin) {
            return true;
        }
    }
    if bits >= stored_bits {
        return false;
    }
    enc.dynamic(ts, sy, &lit, &lcodes, &dist, &dcodes, &cl, &clcodes, hclen, fin);
    true
}

/// Writes the tokens `ts`, which add `raw` to the output, as the next
/// block (or blocks, when stored).
pub fn emit_block(enc: &mut Encoder, ts: &[u32], fr: &Freqs, raw: &[u8], fin: bool)
    requires
        old(enc).inv(),
        !old(enc).done@,
        ts@.len() <= 0x10_0000,
        fr.ok(ts@),
        toks_ok(old(enc).out(), ts@),
        expand(old(enc).out(), ts@) == old(enc).out() + raw@,
        forall|i: int| 0 <= i < ts@.len() ==> #[trigger] tok_valid(ts@[i]),
    ensures
        final(enc).inv(),
        final(enc).out() == old(enc).out() + raw@,
        final(enc).done@ == fin,
        final(enc).head == old(enc).head && final(enc).base == old(enc).base && final(enc).bw.sent() == old(enc).bw.sent(),
{
    if !try_dynamic(enc, ts, fr, raw.len(), fin) {
        emit_stored(enc, raw, fin);
    }
}

/// Writes `data` as the blocks of `enc`, at zlib's `level` (0 to 9).
pub fn compress_into(enc: &mut Encoder, data: &[u8], level: u32)
    requires
        old(enc).inv(),
        !old(enc).done@,
        old(enc).out() == Seq::<u8>::empty(),
    ensures
        final(enc).inv(),
        final(enc).done@,
        final(enc).out() == data@,
        final(enc).head == old(enc).head && final(enc).base == old(enc).base && final(enc).bw.sent() == old(enc).bw.sent(),
{
    let n = data.len();
    if n == 0 || level == 0 {
        emit_stored(enc, data, true);
        proof {
            assert(Seq::<u8>::empty() + data@ =~= data@);
        }
        return;
    }
    let mut m = Matcher::new_for(level, data.len());
    let mut start: usize = 0;
    proof {
        assert(data@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while start < n
        invariant
            n == data@.len(),
            n > 0,
            start <= n,
            enc.inv(),
            m.wf(),
            enc.done@ == (start == n),
            enc.out() == data@.subrange(0, start as int),
            enc.head == old(enc).head && enc.base == old(enc).base,
            enc.bw.sent() == old(enc).bw.sent(),
        decreases n - start,
    {
        // At most one token per byte, so a short input needs few.
        let cap = if n - start < MAX_TOKS - 3 { n - start + 3 } else { MAX_TOKS };
        let mut toks: Vec<u32> = Vec::with_capacity(cap);
        let mut fr = Freqs::new();
        let e = m.fill(data, start, &mut toks, &mut fr, cap - 3);
        let raw = vstd::slice::slice_subrange(data, start, e);
        proof {
            assert(data@.subrange(0, start as int) + data@.subrange(start as int, e as int) =~= data@.subrange(0, e as int));
        }
        emit_block(enc, &toks, &fr, raw, e == n);
        start = e;
    }
    proof {
        assert(data@.subrange(0, n as int) =~= data@);
    }
}

/// Compresses `data` to a raw DEFLATE stream at zlib's `level` (0 to 9).
pub fn compress_raw(data: &[u8], level: u32) -> (r: Vec<u8>)
    ensures
        inflate(r@) == Some((data@, r@.len() as int)),
{
    let mut enc = Encoder::new(data.len() / 2 + 64);
    compress_into(&mut enc, data, level);
    let r = enc.finish();
    assert(Seq::<u8>::empty() + r@ =~= r@);
    r
}

/// The four bytes of `a`, most significant first.
pub fn be_bytes(a: u32) -> (r: [u8; 4])
    ensures
        be32(r@, 0) == a as nat,
        r@.len() == 4,
{
    let b0 = (a >> 24) as u8;
    let b1 = (a >> 16) as u8;
    let b2 = (a >> 8) as u8;
    let b3 = a as u8;
    assert(b0 as u64 * 16777216 + b1 as u64 * 65536 + b2 as u64 * 256 + b3 as u64 == a as u64) by (bit_vector)
        requires
            b0 == (a >> 24) as u8,
            b1 == (a >> 16) as u8,
            b2 == (a >> 8) as u8,
            b3 == a as u8,
    ;
    [b0, b1, b2, b3]
}

/// The four bytes of `a`, least significant first.
pub fn le_bytes(a: u32) -> (r: [u8; 4])
    ensures
        le32(r@, 0) == a as nat,
        r@.len() == 4,
{
    let b0 = a as u8;
    let b1 = (a >> 8) as u8;
    let b2 = (a >> 16) as u8;
    let b3 = (a >> 24) as u8;
    assert(b0 as u64 + b1 as u64 * 256 + b2 as u64 * 65536 + b3 as u64 * 16777216 == a as u64) by (bit_vector)
        requires
            b3 == (a >> 24) as u8,
            b2 == (a >> 16) as u8,
            b1 == (a >> 8) as u8,
            b0 == a as u8,
    ;
    [b0, b1, b2, b3]
}

/// Compresses `data` to a zlib stream at `level` (0 to 9).
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn zlib_compress(data: &[u8], level: u32) -> (r: Vec<u8>)
    ensures
        zlib_decompress(r@) == Some((data@, r@.len() as int)),
{
    let flg: u8 = if level <= 1 {
        0x01
    } else if level <= 5 {
        0x5e
    } else if level == 6 {
        0x9c
    } else {
        0xda
    };
    let hdr = [0x78u8, flg];
    let tail = be_bytes(crate::checksum::adler32(data));
    let mut enc = Encoder::with_header(&hdr, data.len() / 2 + 64);
    compress_into(&mut enc, data, level);
    let r = enc.finish_tail(&tail);
    proof {
        assert(Seq::<u8>::empty() + r@ =~= r@);
        assert(r@[0] == r@.subrange(0, 2)[0]);
        assert(r@[1] == r@.subrange(0, 2)[1]);
        let (e, o) = inflate_blocks(r@, 16, Seq::empty()).unwrap();
        let i = (e + 7) / 8;
        assert forall|j: int| 0 <= j < 4 implies #[trigger] r@[i + j] == tail@[j] by {
            assert(r@[i + j] == r@.subrange(i, r@.len() as int)[j]);
        }
        assert(be32(r@, i) == be32(tail@, 0));
    }
    r
}

/// Compresses `data` to a gzip member at `level` (0 to 9), with no name,
/// time or other optional fields.
pub fn gzip_compress(data: &[u8], level: u32) -> (r: Vec<u8>)
    ensures
        gzip_decompress(r@) == Some((data@, r@.len() as int)),
{
    hide(inflate_blocks);
    hide(gzip_decompress);
    hide(le32);
    let xfl: u8 = if level == 1 { 4 } else if level == 9 { 2 } else { 0 };
    let hdr = [31u8, 139, 8, 0, 0, 0, 0, 0, xfl, 255];
    let c = le_bytes(crate::checksum::crc32(data));
    let l = le_bytes(((data.len() as u64) % 0x1_0000_0000) as u32);
    let tail = [c[0], c[1], c[2], c[3], l[0], l[1], l[2], l[3]];
    let mut enc = Encoder::with_header(&hdr, data.len() / 2 + 64);
    compress_into(&mut enc, data, level);
    let r = enc.finish_tail(&tail);
    proof {
        assert(Seq::<u8>::empty() + r@ =~= r@);
        assert(tail@.subrange(0, 4) =~= c@);
        assert(tail@.subrange(4, 8) =~= l@);
        assert(le32(tail@, 0) == le32(c@, 0)) by {
            reveal(le32);
            assert(tail@[0] == c@[0] && tail@[1] == c@[1] && tail@[2] == c@[2] && tail@[3] == c@[3]);
        }
        assert(le32(tail@, 4) == le32(l@, 0)) by {
            reveal(le32);
            assert(tail@[4] == l@[0] && tail@[5] == l@[1] && tail@[6] == l@[2] && tail@[7] == l@[3]);
        }
        assert(hdr@[0] == 31 && hdr@[1] == 139 && hdr@[2] == 8 && hdr@[3] == 0 && hdr@.len() == 10);
        assert(crate::dstream::head_ok(crate::wrap::Format::Gzip, hdr@));
        crate::dstream::lemma_finish(crate::wrap::Format::Gzip, r@, hdr@, tail@, data@);
        reveal(crate::wrap::spec_decompress);
    }
    r
}


} // verus!
