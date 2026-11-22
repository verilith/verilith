//! The specification: what a JPEG file decodes to.
//!
//! This file is the one to audit. It is written from ITU-T T.81 (the JPEG
//! standard) for the marker syntax, the Huffman codes and the coefficient
//! decoding procedures of baseline, extended sequential and progressive
//! scans, and from libjpeg-turbo 3.1.2 for everything T.81 leaves open or
//! does not fix to the bit: what to do with damaged files, the integer
//! inverse DCT (`jidctint.c`), chroma upsampling (`jdsample.c`) and the
//! YCbCr to RGB conversion (`jdcolor.c`). Each part names its source.
//!
//! Everything here is a total function over `Seq<u8>`: [`jpeg_decode`]
//! gives, for every byte string, either the image or `None`.
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The input
// ---------------------------------------------------------------------------
/// Byte `i` of the input. Past its end the decoder sees the two bytes of an
/// EOI marker, over and over: this is what libjpeg's memory source feeds a
/// decoder that runs off the end (`fill_mem_input_buffer`), and it is why a
/// truncated file still decodes to something.
pub open spec fn byte(d: Seq<u8>, i: int) -> u8 {
    if 0 <= i < d.len() {
        d[i]
    } else if (i - d.len()) % 2 == 0 {
        0xFFu8
    } else {
        0xD9u8
    }
}

/// The big-endian 16-bit number at `i`.
pub open spec fn be16(d: Seq<u8>, i: int) -> int {
    byte(d, i) as int * 256 + byte(d, i + 1) as int
}

/// The first position at or after `q` whose byte is not `0xFF`.
pub open spec fn skip_ff(d: Seq<u8>, q: int) -> int
    decreases left(d, q),
{
    if q >= d.len() {
        if (q - d.len()) % 2 == 0 {
            q + 1
        } else {
            q
        }
    } else if byte(d, q) == 0xFF {
        skip_ff(d, q + 1)
    } else {
        q
    }
}

/// How far `p` is from the end of the input (0 at or past the end).
pub open spec fn left(d: Seq<u8>, p: int) -> int {
    if p < d.len() {
        d.len() - p
    } else {
        0
    }
}

/// The next marker at or after `p` (T.81 B.1.1.2, and libjpeg's
/// `next_marker`): bytes that are not `0xFF` are skipped, any number of
/// `0xFF` fill bytes may precede the marker code, and `0xFF 0x00` is not a
/// marker. Returns the marker code and the position after it. Past the end
/// of the input the answer is EOI, from the bytes `byte` supplies there.
pub open spec fn marker_after(d: Seq<u8>, p: int) -> (u8, int)
    decreases left(d, p),
    via marker_after_dec
{
    if p >= d.len() {
        (0xD9u8, p + 2 + (p - d.len()) % 2)
    } else if byte(d, p) != 0xFF {
        marker_after(d, p + 1)
    } else {
        let q = skip_ff(d, p + 1);
        if byte(d, q) == 0 {
            marker_after(d, q + 1)
        } else {
            (byte(d, q), q + 1)
        }
    }
}

#[via_fn]
proof fn marker_after_dec(d: Seq<u8>, p: int) {
    lemma_skip_ff(d, p + 1);
}

pub proof fn lemma_skip_ff(d: Seq<u8>, q: int)
    ensures
        skip_ff(d, q) >= q,
        byte(d, skip_ff(d, q)) != 0xFF,
        q <= d.len() ==> skip_ff(d, q) <= d.len() + 1,
        forall|j: int| q <= j < skip_ff(d, q) ==> byte(d, j) == 0xFF,
        skip_ff(d, q) >= d.len() ==> byte(d, skip_ff(d, q)) == 0xD9,
    decreases left(d, q),
{
    if q >= d.len() {
        let k = q - d.len();
        assert((k + 1) % 2 == 1 - k % 2);
    } else if byte(d, q) == 0xFF {
        lemma_skip_ff(d, q + 1);
    }
}

/// The bytes of the entropy-coded segment that starts at `p` (T.81 B.1.1.5):
/// everything up to the next marker, with each stuffed `0xFF 0x00` standing
/// for the data byte `0xFF`. As libjpeg does (`jpeg_fill_bit_buffer`), `0xFF`
/// bytes in front of a stuffed zero are fill and are dropped.
pub open spec fn ecs(d: Seq<u8>, p: int) -> Seq<u8>
    decreases left(d, p),
    via ecs_dec
{
    if p >= d.len() {
        if (p - d.len()) % 2 == 0 {
            Seq::<u8>::empty()
        } else {
            seq![0xD9u8]
        }
    } else if byte(d, p) != 0xFF {
        seq![byte(d, p)] + ecs(d, p + 1)
    } else {
        let q = skip_ff(d, p + 1);
        if byte(d, q) == 0 {
            seq![0xFFu8] + ecs(d, q + 1)
        } else {
            Seq::<u8>::empty()
        }
    }
}

#[via_fn]
proof fn ecs_dec(d: Seq<u8>, p: int) {
    lemma_skip_ff(d, p + 1);
}

/// Bit `k` of an entropy-coded segment, most significant bit of each byte
/// first (T.81 F.2.2.5, NEXTBIT). Past the end of the segment the bits are
/// zeros, which is what libjpeg feeds a decoder that reaches a marker early.
pub open spec fn ebit(e: Seq<u8>, k: int) -> int {
    if 0 <= k < 8 * e.len() {
        (e[k / 8] as int / pow2((7 - k % 8) as nat) as int) % 2
    } else {
        0
    }
}

/// The `n` bits at `k` as a number, first bit most significant (T.81
/// F.2.2.4, RECEIVE).
pub open spec fn ebits(e: Seq<u8>, k: int, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        2 * ebits(e, k, (n - 1) as nat) + ebit(e, k + n - 1)
    }
}

// ---------------------------------------------------------------------------
// Fixed tables
// ---------------------------------------------------------------------------
/// The zigzag order (T.81 Figure A.6): `ZZ[k]` is the position, in the
/// row-major 8x8 block, of the `k`-th coefficient of the zigzag sequence.
/// The sixteen extra entries are libjpeg's (`jpeg_natural_order`): a run
/// that would carry `k` past 63 in a corrupt file lands on position 63.
pub const ZZ: [u8; 80] = [
    0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20,
    13, 6, 7, 14, 21, 28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59,
    52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63,
    63, 63, 63, 63, 63, 63, 63,
];

pub open spec fn zz(k: int) -> int {
    ZZ[k] as int
}

// ---------------------------------------------------------------------------
// Huffman codes (T.81 Annex C and F.2.2.3)
// ---------------------------------------------------------------------------
/// A Huffman table as a DHT segment gives it: `counts[l - 1]` codes of
/// length `l` (BITS), and the symbols in order of increasing code length
/// (HUFFVAL), zero-filled.
pub ghost struct HuffTable {
    pub counts: Seq<u8>,
    pub vals: Seq<u8>,
}

/// Number of codes of length `l`, `1 <= l <= 16`.
pub open spec fn hcount(t: HuffTable, l: int) -> int {
    if 1 <= l <= 16 {
        t.counts[l - 1] as int
    } else {
        0
    }
}

/// The code of the first symbol of length `l` (Annex C, Figure C.2: codes
/// of one length are consecutive, and the first of the next length is the
/// one after the last, with a zero appended).
pub open spec fn hfirst(t: HuffTable, l: int) -> int
    decreases l,
{
    if l <= 1 {
        0
    } else {
        2 * (hfirst(t, l - 1) + hcount(t, l - 1))
    }
}

/// The index in `vals` of the first symbol of length `l`.
pub open spec fn hbase(t: HuffTable, l: int) -> int
    decreases l,
{
    if l <= 1 {
        0
    } else {
        hbase(t, l - 1) + hcount(t, l - 1)
    }
}

/// A usable table: at most 256 symbols, and the codes of every length fit
/// in that many bits with the all-ones code left over (libjpeg's
/// `jpeg_make_d_derived_tbl` rejects the rest).
pub open spec fn huff_ok(t: HuffTable) -> bool {
    &&& hbase(t, 17) <= 256
    &&& forall|l: int| 1 <= l <= 16 ==> hfirst(t, l) + #[trigger] hcount(t, l) < pow2(l as nat)
}

/// A usable DC table also has no symbol above 15.
pub open spec fn huff_dc_ok(t: HuffTable) -> bool {
    &&& huff_ok(t)
    &&& forall|i: int| 0 <= i < hbase(t, 17) ==> #[trigger] t.vals[i] <= 15
}

/// DECODE (F.2.2.3), having read the `l` bits `code` at `n`: the symbol and
/// the position after its code. A code longer than 16 bits is not in any
/// table; libjpeg warns, takes 17 bits and returns symbol 0.
pub open spec fn hdec(t: HuffTable, e: Seq<u8>, n: int, l: int, code: int) -> (int, int)
    decreases 17 - l,
{
    if l > 16 {
        (0, n + 17)
    } else if code < hfirst(t, l) + hcount(t, l) {
        (t.vals[hbase(t, l) + code - hfirst(t, l)] as int, n + l)
    } else {
        hdec(t, e, n, l + 1, 2 * code + ebit(e, n + l))
    }
}

/// The symbol whose code starts at bit `n`, and the position after it.
pub open spec fn huff(t: HuffTable, e: Seq<u8>, n: int) -> (int, int) {
    hdec(t, e, n, 1, ebit(e, n))
}

/// A symbol is a byte, and its code takes at least one bit.
pub proof fn lemma_hdec(t: HuffTable, e: Seq<u8>, n: int, l: int, code: int)
    requires
        1 <= l <= 17,
    ensures
        0 <= hdec(t, e, n, l, code).0 <= 255,
        n + l <= hdec(t, e, n, l, code).1 <= n + 17,
    decreases 17 - l,
{
    if l <= 16 && !(code < hfirst(t, l) + hcount(t, l)) {
        lemma_hdec(t, e, n, l + 1, 2 * code + ebit(e, n + l));
    }
}

pub proof fn lemma_huff(t: HuffTable, e: Seq<u8>, n: int)
    ensures
        0 <= huff(t, e, n).0 <= 255,
        n + 1 <= huff(t, e, n).1 <= n + 17,
{
    lemma_hdec(t, e, n, 1, ebit(e, n));
}

/// How far `k` is below `lim` (0 at or above it).
pub open spec fn togo(k: int, lim: int) -> int {
    if k < lim {
        lim - k
    } else {
        0
    }
}

/// EXTEND (F.2.2.1): the signed value of the `s`-bit field `v`.
pub open spec fn extend(v: int, s: int) -> int {
    if v < pow2((s - 1) as nat) {
        v - pow2(s as nat) + 1
    } else {
        v
    }
}

/// `x` reduced to a signed 16-bit value (C's conversion to `short`).
pub open spec fn wrap16(x: int) -> int {
    let m = x % 0x1_0000;
    if m >= 0x8000 {
        m - 0x1_0000
    } else {
        m
    }
}

/// `x` reduced to a signed 32-bit value.
pub open spec fn wrap32(x: int) -> int {
    let m = x % 0x1_0000_0000;
    if m >= 0x8000_0000 {
        m - 0x1_0000_0000
    } else {
        m
    }
}

// ---------------------------------------------------------------------------
// Tables, frame and scan headers
// ---------------------------------------------------------------------------
/// The tables in force (T.81 B.2.4): four quantization tables in row-major
/// order, four DC and four AC Huffman tables, and the restart interval.
pub ghost struct Tables {
    pub q: Seq<Seq<u16>>,
    pub qdef: Seq<bool>,
    pub dc: Seq<HuffTable>,
    pub dcdef: Seq<bool>,
    pub ac: Seq<HuffTable>,
    pub acdef: Seq<bool>,
    pub ri: int,
}

#[derive(Clone, Copy)]
pub struct Comp {
    pub id: u8,
    pub h: u8,
    pub v: u8,
    pub tq: u8,
}

/// A frame header (T.81 B.2.2): progressive or sequential, the image's
/// width and height, and its `nc` components.
pub ghost struct Frame {
    pub prog: bool,
    pub w: int,
    pub h: int,
    pub nc: int,
    pub comps: Seq<Comp>,
}

/// A scan header (T.81 B.2.3): for each of its `ns` components the index of
/// the frame component and the DC and AC table numbers, then the spectral
/// selection and successive approximation.
pub ghost struct Scan {
    pub ns: int,
    pub ci: Seq<int>,
    pub td: Seq<int>,
    pub ta: Seq<int>,
    pub ss: int,
    pub se: int,
    pub ah: int,
    pub al: int,
}

pub open spec fn max2(a: int, b: int) -> int {
    if a >= b {
        a
    } else {
        b
    }
}

pub open spec fn maxh(f: Frame) -> int {
    if f.nc == 1 {
        f.comps[0].h as int
    } else {
        max2(f.comps[0].h as int, max2(f.comps[1].h as int, f.comps[2].h as int))
    }
}

pub open spec fn maxv(f: Frame) -> int {
    if f.nc == 1 {
        f.comps[0].v as int
    } else {
        max2(f.comps[0].v as int, max2(f.comps[1].v as int, f.comps[2].v as int))
    }
}

/// `ceil(a / b)`.
pub open spec fn cdiv(a: int, b: int) -> int {
    (a + b - 1) / b
}

/// MCUs per row and MCU rows of an interleaved scan (T.81 A.2.3).
pub open spec fn mcux(f: Frame) -> int {
    cdiv(f.w as int, 8 * maxh(f))
}

pub open spec fn mcuy(f: Frame) -> int {
    cdiv(f.h as int, 8 * maxv(f))
}

/// The size, in blocks, of component `c`'s coefficient array: whole MCUs.
pub open spec fn cw(f: Frame, c: int) -> int {
    mcux(f) * f.comps[c].h as int
}

pub open spec fn ch(f: Frame, c: int) -> int {
    mcuy(f) * f.comps[c].v as int
}

/// The blocks of component `c` that hold image data (T.81 A.2.4): the
/// MCUs of a scan of this component alone.
pub open spec fn wb(f: Frame, c: int) -> int {
    cdiv(f.w as int * f.comps[c].h as int, 8 * maxh(f))
}

pub open spec fn hb(f: Frame, c: int) -> int {
    cdiv(f.h as int * f.comps[c].v as int, 8 * maxv(f))
}

/// The size, in samples, of component `c` (T.81 A.1.1).
pub open spec fn dw(f: Frame, c: int) -> int {
    cdiv(f.w as int * f.comps[c].h as int, maxh(f))
}

pub open spec fn dh(f: Frame, c: int) -> int {
    cdiv(f.h as int * f.comps[c].v as int, maxv(f))
}

/// The frames this decoder takes: 8-bit samples (checked where the header
/// is read), one or three components, sampling factors 1 to 4 that divide
/// the largest (libjpeg has no upsampler for the others), and libjpeg's
/// limit of 65500 on each dimension.
pub open spec fn frame_ok(f: Frame) -> bool {
    &&& f.nc == 1 || f.nc == 3
    &&& 1 <= f.w <= 65500
    &&& 1 <= f.h <= 65500
    &&& forall|c: int|
        0 <= c < f.nc ==> {
            &&& 1 <= (#[trigger] f.comps[c]).h <= 4
            &&& 1 <= f.comps[c].v <= 4
            &&& maxh(f) % f.comps[c].h as int == 0
            &&& maxv(f) % f.comps[c].v as int == 0
        }
}

/// The scan's kind. A sequential frame's scans are all `Base`.
pub enum Kind {
    Base,
    DcFirst,
    DcRefine,
    AcFirst,
    AcRefine,
}

pub open spec fn kind(f: Frame, s: Scan) -> Kind {
    if !f.prog {
        Kind::Base
    } else if s.ss == 0 {
        if s.ah == 0 {
            Kind::DcFirst
        } else {
            Kind::DcRefine
        }
    } else if s.ah == 0 {
        Kind::AcFirst
    } else {
        Kind::AcRefine
    }
}

/// Blocks in one MCU of the scan (T.81 A.2.3): one for a scan of a single
/// component, else `h * v` for each of its components.
pub open spec fn mcu_blocks(f: Frame, s: Scan) -> int {
    if s.ns == 1 {
        1
    } else {
        blocks_upto(f, s, s.ns as int)
    }
}

/// Blocks of the first `i` components of the scan in an interleaved MCU.
pub open spec fn blocks_upto(f: Frame, s: Scan, i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        blocks_upto(f, s, i - 1) + f.comps[s.ci[i - 1] as int].h as int * f.comps[s.ci[i - 1] as int].v as int
    }
}

/// A scan header this decoder (and libjpeg) accepts for the frame and the
/// tables in force.
pub open spec fn scan_ok(f: Frame, t: Tables, s: Scan) -> bool {
    &&& 1 <= s.ns <= f.nc
    &&& forall|i: int| 0 <= i < s.ns ==> 0 <= (#[trigger] s.ci[i]) < f.nc
    &&& forall|i: int, j: int| 0 <= i < j < s.ns ==> s.ci[i] != s.ci[j]
    &&& mcu_blocks(f, s) <= 10
    &&& match kind(f, s) {
        Kind::Base => forall|i: int|
            0 <= i < s.ns ==> {
                &&& 0 <= (#[trigger] s.td[i]) < 4 && t.dcdef[s.td[i] as int] && huff_dc_ok(t.dc[s.td[i] as int])
                &&& 0 <= s.ta[i] < 4 && t.acdef[s.ta[i] as int] && huff_ok(t.ac[s.ta[i] as int])
            },
        // T.81 G.1.1.1.1 and libjpeg's `start_pass_phuff_decoder`.
        Kind::DcFirst => {
            &&& s.se == 0 && s.al <= 13
            &&& forall|i: int|
                0 <= i < s.ns ==> 0 <= (#[trigger] s.td[i]) < 4 && t.dcdef[s.td[i] as int] && huff_dc_ok(
                    t.dc[s.td[i] as int],
                )
        },
        Kind::DcRefine => s.se == 0 && s.al <= 13 && s.al == s.ah - 1,
        Kind::AcFirst => {
            &&& s.ss <= s.se < 64 && s.ns == 1 && s.al <= 13
            &&& 0 <= s.ta[0] < 4 && t.acdef[s.ta[0] as int] && huff_ok(t.ac[s.ta[0] as int])
        },
        Kind::AcRefine => {
            &&& s.ss <= s.se < 64 && s.ns == 1 && s.al <= 13 && s.al == s.ah - 1
            &&& 0 <= s.ta[0] < 4 && t.acdef[s.ta[0] as int] && huff_ok(t.ac[s.ta[0] as int])
        },
    }
}

// ---------------------------------------------------------------------------
// Coefficients of one block
// ---------------------------------------------------------------------------
// A component's coefficients are one sequence, 64 per block in row-major
// order, quantized as the file has them. `o` is where the block starts.
// Decoding writes into what is already there: the array starts as zeros, and
// later scans of a progressive file refine it.
/// The AC coefficients of a sequential block from zigzag position `k`
/// (T.81 F.2.2.2, Figure F.13).
pub open spec fn base_ac(t: HuffTable, e: Seq<u8>, n: int, k: int, a: Seq<i16>, o: int) -> (Seq<i16>, int)
    decreases togo(k, 64),
    via base_ac_dec
{
    if k >= 64 {
        (a, n)
    } else {
        let (sym, n1) = huff(t, e, n);
        let r = sym / 16;
        let s = sym % 16;
        if s != 0 {
            let v = extend(ebits(e, n1, s as nat), s);
            base_ac(t, e, n1 + s, k + r + 1, a.update(o + zz(k + r), #[verifier::truncate] (v as i16)), o)
        } else if r != 15 {
            (a, n1)
        } else {
            base_ac(t, e, n1, k + 16, a, o)
        }
    }
}

#[via_fn]
proof fn base_ac_dec(t: HuffTable, e: Seq<u8>, n: int, k: int, a: Seq<i16>, o: int) {
    lemma_huff(t, e, n);
}

/// A DC difference (T.81 F.2.2.1): the symbol is the number of bits of the
/// value that follows.
pub open spec fn dc_diff(t: HuffTable, e: Seq<u8>, n: int) -> (int, int) {
    let (s, n1) = huff(t, e, n);
    if s == 0 {
        (0, n1)
    } else {
        (extend(ebits(e, n1, s as nat), s), n1 + s)
    }
}

/// A sequential block (T.81 F.2.2): the DC difference added to the
/// prediction, then the AC coefficients. Returns the coefficients, the new
/// prediction and the position. The prediction wraps at 32 bits and is
/// stored in 16, as in libjpeg.
pub open spec fn base_block(dct: HuffTable, act: HuffTable, e: Seq<u8>, n: int, pred: int, a: Seq<i16>, o: int) -> (
    Seq<i16>,
    int,
    int,
) {
    let (diff, n1) = dc_diff(dct, e, n);
    let p = wrap32(pred + diff);
    let (a2, n2) = base_ac(act, e, n1, 1, a.update(o, wrap16(p) as i16), o);
    (a2, p, n2)
}

/// The first DC scan of a progressive block (T.81 G.1.2.1): as a sequential
/// DC, shifted left by `al`. The last result says the prediction stayed
/// within 32 bits (libjpeg stops with an error when it does not).
pub open spec fn dc_first(t: HuffTable, e: Seq<u8>, n: int, pred: int, al: int, a: Seq<i16>, o: int) -> (
    Seq<i16>,
    int,
    int,
    bool,
) {
    let (diff, n1) = dc_diff(t, e, n);
    let p = pred + diff;
    (a.update(o, wrap16(p * pow2(al as nat)) as i16), p, n1, -0x8000_0000 <= p <= 0x7fff_ffff)
}

/// `2^al` as a coefficient, for `al <= 13`.
pub open spec fn bit16(al: int) -> i16 {
    pow2(al as nat) as i16
}

/// A DC refinement (T.81 G.1.2.1): one more bit of the DC coefficient.
pub open spec fn dc_refine(e: Seq<u8>, n: int, al: int, a: Seq<i16>, o: int) -> (Seq<i16>, int) {
    if ebit(e, n) == 1 {
        (a.update(o, a[o] | bit16(al)), n + 1)
    } else {
        (a, n + 1)
    }
}

/// The first AC scan of a block's band `k..=se` (T.81 G.1.2.2, Figure
/// G.3), for a block not covered by an end-of-band run. Returns the
/// coefficients, the position, and the number of following blocks whose
/// band is empty (EOBRUN).
pub open spec fn ac_first(t: HuffTable, e: Seq<u8>, n: int, k: int, se: int, al: int, a: Seq<i16>, o: int) -> (
    Seq<i16>,
    int,
    int,
)
    decreases togo(k, se + 1),
    via ac_first_dec
{
    if k > se {
        (a, n, 0)
    } else {
        let (sym, n1) = huff(t, e, n);
        let r = sym / 16;
        let s = sym % 16;
        if s != 0 {
            let v = extend(ebits(e, n1, s as nat), s);
            ac_first(
                t,
                e,
                n1 + s,
                k + r + 1,
                se,
                al,
                a.update(o + zz(k + r), wrap16(v * pow2(al as nat)) as i16),
                o,
            )
        } else if r == 15 {
            ac_first(t, e, n1, k + 16, se, al, a, o)
        } else {
            (a, n1 + r, pow2(r as nat) + ebits(e, n1, r as nat) - 1)
        }
    }
}

#[via_fn]
proof fn ac_first_dec(t: HuffTable, e: Seq<u8>, n: int, k: int, se: int, al: int, a: Seq<i16>, o: int) {
    lemma_huff(t, e, n);
}

/// One correction bit applied to a coefficient that is already nonzero
/// (T.81 G.1.2.3): if the bit is set and the coefficient does not have
/// bit `al` yet, it moves away from zero by `2^al`.
pub open spec fn refine_coef(c: i16, bit: int, al: int) -> i16 {
    if bit == 1 && c & bit16(al) == 0 {
        if c >= 0 {
            wrap16(c + pow2(al as nat)) as i16
        } else {
            wrap16(c - pow2(al as nat)) as i16
        }
    } else {
        c
    }
}

/// Refinement passing over the band from `k`: every nonzero coefficient
/// takes a correction bit, and the pass stops at the zero coefficient
/// after `r` others (T.81 Figure G.7), or after `se`. Returns the
/// coefficients, the position, and the `k` it stopped at.
pub open spec fn refine_skip(e: Seq<u8>, n: int, k: int, se: int, r: int, al: int, a: Seq<i16>, o: int) -> (
    Seq<i16>,
    int,
    int,
)
    decreases se + 1 - k,
{
    if k > se {
        (a, n, k)
    } else if a[o + zz(k)] != 0 {
        refine_skip(
            e,
            n + 1,
            k + 1,
            se,
            r,
            al,
            a.update(o + zz(k), refine_coef(a[o + zz(k)], ebit(e, n), al)),
            o,
        )
    } else if r <= 0 {
        (a, n, k)
    } else {
        refine_skip(e, n, k + 1, se, r - 1, al, a, o)
    }
}

/// Refinement of the rest of the band inside an end-of-band run: only
/// correction bits.
pub open spec fn refine_rest(e: Seq<u8>, n: int, k: int, se: int, al: int, a: Seq<i16>, o: int) -> (Seq<i16>, int)
    decreases se + 1 - k,
{
    if k > se {
        (a, n)
    } else if a[o + zz(k)] != 0 {
        refine_rest(e, n + 1, k + 1, se, al, a.update(o + zz(k), refine_coef(a[o + zz(k)], ebit(e, n), al)), o)
    } else {
        refine_rest(e, n, k + 1, se, al, a, o)
    }
}

/// An AC refinement scan of a block's band from `k` (T.81 G.1.2.3, Figure
/// G.5), for a block not inside an end-of-band run. Returns the
/// coefficients, the position, and the number of following blocks whose
/// band only takes correction bits (EOBRUN).
pub open spec fn ac_refine(t: HuffTable, e: Seq<u8>, n: int, k: int, se: int, al: int, a: Seq<i16>, o: int) -> (
    Seq<i16>,
    int,
    int,
)
    decreases togo(k, se + 1),
    via ac_refine_dec
{
    if k > se {
        (a, n, 0)
    } else {
        let (sym, n1) = huff(t, e, n);
        let r = sym / 16;
        let s = sym % 16;
        if s != 0 {
            // A new coefficient of magnitude 2^al; its sign bit comes first.
            let v = if ebit(e, n1) == 1 {
                pow2(al as nat) as int
            } else {
                -(pow2(al as nat) as int)
            };
            let (a2, n2, k2) = refine_skip(e, n1 + 1, k, se, r, al, a, o);
            ac_refine(t, e, n2, k2 + 1, se, al, a2.update(o + zz(k2), #[verifier::truncate] (v as i16)), o)
        } else if r == 15 {
            let (a2, n2, k2) = refine_skip(e, n1, k, se, 15, al, a, o);
            ac_refine(t, e, n2, k2 + 1, se, al, a2, o)
        } else {
            let (a2, n2) = refine_rest(e, n1 + r, k, se, al, a, o);
            (a2, n2, pow2(r as nat) + ebits(e, n1, r as nat) - 1)
        }
    }
}

#[via_fn]
proof fn ac_refine_dec(t: HuffTable, e: Seq<u8>, n: int, k: int, se: int, al: int, a: Seq<i16>, o: int) {
    let (sym, n1) = huff(t, e, n);
    lemma_huff(t, e, n);
    lemma_refine_skip_k(e, n1 + 1, k, se, sym / 16, al, a, o);
    lemma_refine_skip_k(e, n1, k, se, 15, al, a, o);
}

pub proof fn lemma_refine_skip_k(e: Seq<u8>, n: int, k: int, se: int, r: int, al: int, a: Seq<i16>, o: int)
    ensures
        refine_skip(e, n, k, se, r, al, a, o).2 >= k,
        k <= se + 1 ==> refine_skip(e, n, k, se, r, al, a, o).2 <= se + 1,
        refine_skip(e, n, k, se, r, al, a, o).1 >= n,
        refine_skip(e, n, k, se, r, al, a, o).0.len() == a.len(),
    decreases se + 1 - k,
{
    if k > se {
    } else if a[o + zz(k)] != 0 {
        lemma_refine_skip_k(
            e,
            n + 1,
            k + 1,
            se,
            r,
            al,
            a.update(o + zz(k), refine_coef(a[o + zz(k)], ebit(e, n), al)),
            o,
        );
    } else if r <= 0 {
    } else {
        lemma_refine_skip_k(e, n, k + 1, se, r - 1, al, a, o);
    }
}

// ---------------------------------------------------------------------------
// Scans
// ---------------------------------------------------------------------------
/// What a scan carries from one MCU to the next.
pub ghost struct SS {
    /// The coefficients of each component.
    pub a: Seq<Seq<i16>>,
    /// The DC prediction of each component of the scan.
    pub pred: Seq<int>,
    /// Blocks still covered by an end-of-band run.
    pub eob: int,
    /// Where the current entropy-coded segment starts.
    pub p: int,
    /// The bit position in that segment.
    pub n: int,
    /// The segment ran out before an MCU was complete.
    pub insuf: bool,
    /// MCUs until the next restart marker is due.
    pub togo: int,
    /// The number, 0 to 7, of the next restart marker.
    pub rst: int,
    /// No error so far.
    pub ok: bool,
}

/// Block `b` of an interleaved MCU: the index `i` of its component in the
/// scan, and the block's number within that component's part of the MCU.
pub open spec fn blk_slot(f: Frame, s: Scan, b: int, i: int) -> (int, int)
    decreases s.ns - i,
{
    let n = f.comps[s.ci[i] as int].h as int * f.comps[s.ci[i] as int].v as int;
    if i >= s.ns - 1 || b < n {
        (i, b)
    } else {
        blk_slot(f, s, b - n, i + 1)
    }
}

/// Block `b` of MCU `m` (T.81 A.2.2 and A.2.3): the index of its component
/// in the scan and its number in that component's coefficient array. A
/// scan of one component goes through the component's own blocks, row by
/// row; an interleaved scan takes `h` by `v` blocks of each component per
/// MCU.
pub open spec fn blk_index(f: Frame, s: Scan, m: int, b: int) -> (int, int) {
    if s.ns == 1 {
        let c = s.ci[0] as int;
        (0, (m / wb(f, c)) * cw(f, c) + m % wb(f, c))
    } else {
        let (i, off) = blk_slot(f, s, b, 0);
        let c = s.ci[i] as int;
        let h = f.comps[c].h as int;
        let v = f.comps[c].v as int;
        let x = (m % mcux(f)) * h + off % h;
        let y = (m / mcux(f)) * v + off / h;
        (i, y * cw(f, c) + x)
    }
}

/// MCUs in the scan.
pub open spec fn scan_mcus(f: Frame, s: Scan) -> int {
    if s.ns == 1 {
        wb(f, s.ci[0] as int) * hb(f, s.ci[0] as int)
    } else {
        mcux(f) * mcuy(f)
    }
}

/// Block `b` of MCU `m` of a sequential or DC scan.
pub open spec fn mcu_dc_block(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int, b: int) -> SS {
    let (i, idx) = blk_index(f, s, m, b);
    let c = s.ci[i] as int;
    let e = ecs(d, st.p);
    let o = idx * 64;
    match kind(f, s) {
        Kind::Base => {
            let (a2, p2, n2) = base_block(
                t.dc[s.td[i] as int],
                t.ac[s.ta[i] as int],
                e,
                st.n,
                st.pred[i],
                st.a[c],
                o,
            );
            SS { a: st.a.update(c, a2), pred: st.pred.update(i, p2), n: n2, ..st }
        },
        Kind::DcFirst => {
            let (a2, p2, n2, ok) = dc_first(t.dc[s.td[i] as int], e, st.n, st.pred[i], s.al as int, st.a[c], o);
            SS { a: st.a.update(c, a2), pred: st.pred.update(i, p2), n: n2, ok: st.ok && ok, ..st }
        },
        _ => {
            let (a2, n2) = dc_refine(e, st.n, s.al as int, st.a[c], o);
            SS { a: st.a.update(c, a2), n: n2, ..st }
        },
    }
}

/// Blocks `b..` of MCU `m`, for the scans that code every block the same
/// way (sequential and DC).
pub open spec fn mcu_dc(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int, b: int) -> SS
    decreases mcu_blocks(f, s) - b,
{
    if b >= mcu_blocks(f, s) {
        st
    } else {
        mcu_dc(d, f, t, s, mcu_dc_block(d, f, t, s, st, m, b), m, b + 1)
    }
}

/// The one block of MCU `m` of an AC scan.
pub open spec fn mcu_ac(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int) -> SS {
    let (i, idx) = blk_index(f, s, m, 0);
    let c = s.ci[0] as int;
    let e = ecs(d, st.p);
    let o = idx * 64;
    let tab = t.ac[s.ta[0] as int];
    if kind(f, s) is AcFirst {
        if st.eob > 0 {
            SS { eob: st.eob - 1, ..st }
        } else {
            let (a2, n2, run) = ac_first(tab, e, st.n, s.ss as int, s.se as int, s.al as int, st.a[c], o);
            SS { a: st.a.update(c, a2), n: n2, eob: run, ..st }
        }
    } else if st.eob > 0 {
        let (a2, n2) = refine_rest(e, st.n, s.ss as int, s.se as int, s.al as int, st.a[c], o);
        SS { a: st.a.update(c, a2), n: n2, eob: st.eob - 1, ..st }
    } else {
        let (a2, n2, run) = ac_refine(tab, e, st.n, s.ss as int, s.se as int, s.al as int, st.a[c], o);
        SS { a: st.a.update(c, a2), n: n2, eob: run, ..st }
    }
}

/// What libjpeg's `jpeg_resync_to_restart` does with marker `m`, found at
/// the position before `q`, when restart marker number `want` was due.
/// Returns where decoding goes on and whether a restart marker was taken:
/// a restart numbered just after the wanted one, or any other kind of
/// marker, is left in place (the segment before it is then empty); one
/// numbered just before, or an invalid code, is dropped and the search
/// goes on; any other restart marker is taken for the wanted one.
pub open spec fn resync(d: Seq<u8>, m: u8, q: int, want: int) -> (int, bool)
    decreases togo(q, d.len() as int + 1),
    via resync_dec
{
    // A marker code read past the end of the input is EOI.
    if q > d.len() {
        (q - 2, false)
    } else if m < 0xC0 || m == 0xD0 + (want + 7) % 8 || m == 0xD0 + (want + 6) % 8 {
        let (m2, q2) = marker_after(d, q);
        resync(d, m2, q2, want)
    } else if m < 0xD0 || m > 0xD7 || m == 0xD0 + (want + 1) % 8 || m == 0xD0 + (want + 2) % 8 {
        (q - 2, false)
    } else {
        (q, true)
    }
}

#[via_fn]
proof fn resync_dec(d: Seq<u8>, m: u8, q: int, want: int) {
    lemma_marker_after(d, q);
}

pub proof fn lemma_marker_after(d: Seq<u8>, p: int)
    ensures
        marker_after(d, p).1 >= p + 2,
        p <= d.len() ==> marker_after(d, p).1 <= d.len() + 2,
        marker_after(d, p).0 != 0xFF,
        marker_after(d, p).0 != 0,
        marker_after(d, p).1 > d.len() ==> marker_after(d, p).0 == 0xD9,
    decreases left(d, p),
{
    lemma_skip_ff(d, p + 1);
    if p >= d.len() {
    } else if byte(d, p) != 0xFF {
        lemma_marker_after(d, p + 1);
    } else {
        let q = skip_ff(d, p + 1);
        if byte(d, q) == 0 {
            lemma_marker_after(d, q + 1);
        }
    }
}

/// A restart (T.81 E.2.4 and F.2.1.3.1): the rest of the segment is
/// dropped, the next marker should be the restart marker that is due, and
/// the predictions and the end-of-band run start over.
pub open spec fn restart(d: Seq<u8>, t: Tables, st: SS) -> SS {
    let (m, q) = marker_after(d, st.p);
    let (p2, taken) = if m == 0xD0 + st.rst {
        (q, true)
    } else {
        resync(d, m, q, st.rst)
    };
    SS {
        p: p2,
        n: 0,
        pred: seq![0int, 0int, 0int],
        eob: 0,
        togo: t.ri as int,
        rst: (st.rst + 1) % 8,
        insuf: if taken {
            false
        } else {
            st.insuf
        },
        ..st
    }
}

/// MCU `m` of a scan. Once a segment has run out in the middle of an MCU,
/// the MCUs up to the next restart marker are left as they are (libjpeg's
/// `insufficient_data`); a DC refinement scan reads on regardless, and the
/// zeros it reads change nothing.
pub open spec fn mcu_step(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int) -> SS {
    let st1 = if t.ri != 0 && st.togo == 0 {
        restart(d, t, st)
    } else {
        st
    };
    let st2 = if st1.insuf && !(kind(f, s) is DcRefine) {
        st1
    } else {
        let x = match kind(f, s) {
            Kind::AcFirst | Kind::AcRefine => mcu_ac(d, f, t, s, st1, m),
            _ => mcu_dc(d, f, t, s, st1, m, 0),
        };
        SS { insuf: st1.insuf || x.n > 8 * ecs(d, st1.p).len(), ..x }
    };
    SS { togo: st2.togo - 1, ..st2 }
}

/// MCUs `m..` of a scan.
pub open spec fn scan_from(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int) -> SS
    decreases scan_mcus(f, s) - m,
{
    if m >= scan_mcus(f, s) {
        st
    } else {
        scan_from(d, f, t, s, mcu_step(d, f, t, s, st, m), m + 1)
    }
}

/// A whole scan whose entropy-coded data starts at `p`, over coefficients
/// `a`.
pub open spec fn scan(d: Seq<u8>, f: Frame, t: Tables, s: Scan, a: Seq<Seq<i16>>, p: int) -> SS {
    scan_from(
        d,
        f,
        t,
        s,
        SS {
            a,
            pred: seq![0int, 0int, 0int],
            eob: 0,
            p,
            n: 0,
            insuf: false,
            togo: t.ri as int,
            rst: 0,
            ok: true,
        },
        0,
    )
}

// ---------------------------------------------------------------------------
// Marker segments (T.81 B.2)
// ---------------------------------------------------------------------------
/// The 64 entries of a quantization table at `p`, one or two bytes each, in
/// zigzag order, written to their row-major places.
pub open spec fn dqt_fill(d: Seq<u8>, p: int, wide: bool, i: int, q: Seq<u16>) -> Seq<u16>
    decreases 64 - i,
{
    if i >= 64 {
        q
    } else {
        let v = if wide {
            be16(d, p + 2 * i) as u16
        } else {
            byte(d, p + i) as u16
        };
        dqt_fill(d, p, wide, i + 1, q.update(zz(i), v))
    }
}

/// The tables of a DQT segment (T.81 B.2.4.1) from `p`, with `rem` bytes of
/// the segment left.
pub open spec fn dqt(d: Seq<u8>, p: int, rem: int, t: Tables) -> Option<Tables>
    decreases togo(0, rem),
{
    if rem <= 0 {
        if rem == 0 {
            Some(t)
        } else {
            None
        }
    } else {
        let wide = byte(d, p) >= 16;
        let n = (byte(d, p) % 16) as int;
        let size: int = if wide {
            129
        } else {
            65
        };
        if n >= 4 {
            None
        } else {
            let q = dqt_fill(d, p + 1, wide, 0, t.q[n]);
            dqt(d, p + size, rem - size, Tables { q: t.q.update(n, q), qdef: t.qdef.update(n, true), ..t })
        }
    }
}

/// The sum of the sixteen code counts at `p`.
pub open spec fn dht_total(d: Seq<u8>, p: int, i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        dht_total(d, p, i - 1) + byte(d, p + i - 1) as int
    }
}

/// The table a DHT segment defines at `p`: sixteen counts, then `total`
/// symbols.
pub open spec fn dht_table(d: Seq<u8>, p: int, total: int) -> HuffTable {
    HuffTable {
        counts: Seq::new(16, |i: int| byte(d, p + i)),
        vals: Seq::new(
            256,
            |i: int|
                if i < total {
                    byte(d, p + 16 + i)
                } else {
                    0u8
                },
        ),
    }
}

/// The tables of a DHT segment (T.81 B.2.4.2) from `p`, with `rem` bytes
/// of the segment left.
pub open spec fn dht(d: Seq<u8>, p: int, rem: int, t: Tables) -> Option<Tables>
    decreases togo(0, rem),
    via dht_dec
{
    if rem <= 16 {
        if rem == 0 {
            Some(t)
        } else {
            None
        }
    } else {
        let tc = byte(d, p) as int;
        let total = dht_total(d, p + 1, 16);
        let ac = tc >= 16;
        let idx = if ac {
            tc - 16
        } else {
            tc
        };
        if total > 256 || total > rem - 17 || idx >= 4 {
            None
        } else {
            let h = dht_table(d, p + 1, total);
            let t2 = if ac {
                Tables { ac: t.ac.update(idx, h), acdef: t.acdef.update(idx, true), ..t }
            } else {
                Tables { dc: t.dc.update(idx, h), dcdef: t.dcdef.update(idx, true), ..t }
            };
            dht(d, p + 17 + total, rem - 17 - total, t2)
        }
    }
}

#[via_fn]
proof fn dht_dec(d: Seq<u8>, p: int, rem: int, t: Tables) {
    lemma_dht_total(d, p + 1, 16);
}

pub proof fn lemma_dht_total(d: Seq<u8>, p: int, i: int)
    ensures
        0 <= dht_total(d, p, i),
        i >= 0 ==> dht_total(d, p, i) <= 255 * i,
    decreases i,
{
    if i > 0 {
        lemma_dht_total(d, p, i - 1);
    }
}

/// The fields of the frame header at `q` (just after an SOF marker; T.81
/// B.2.2).
pub open spec fn sof_frame(d: Seq<u8>, q: int, prog: bool) -> Frame {
    let nc = byte(d, q + 7);
    Frame {
        prog,
        h: be16(d, q + 3),
        w: be16(d, q + 5),
        nc: nc as int,
        comps: Seq::new(
            nc as nat,
            |c: int|
                Comp {
                    id: byte(d, q + 8 + 3 * c),
                    h: byte(d, q + 9 + 3 * c) / 16,
                    v: byte(d, q + 9 + 3 * c) % 16,
                    tq: byte(d, q + 10 + 3 * c),
                },
        ),
    }
}

/// The frame header at `q`, if it is one this decoder takes.
pub open spec fn sof(d: Seq<u8>, q: int, prog: bool) -> Option<Frame> {
    let len = be16(d, q);
    let nc = byte(d, q + 7);
    let f = sof_frame(d, q, prog);
    if byte(d, q + 2) == 8 && (nc == 1 || nc == 3) && len == 8 + 3 * nc && frame_ok(f) {
        Some(f)
    } else {
        None
    }
}

/// The frame component the `i`-th entry of a scan header names by `id`:
/// the first one with that identifier that is not before position `i`
/// (libjpeg's `get_sos`; with distinct identifiers this asks that a scan
/// list its components in frame order, as T.81 B.2.3 requires).
pub open spec fn find_comp(f: Frame, id: u8, i: int, c: int) -> int
    decreases f.nc - c,
{
    if c >= f.nc {
        -1
    } else if c >= i && f.comps[c].id == id {
        c
    } else {
        find_comp(f, id, i, c + 1)
    }
}

/// The scan header at `q` (just after an SOS marker). A component it names
/// that the frame does not have comes out as -1, which `scan_ok` rejects.
pub open spec fn sos(d: Seq<u8>, q: int, f: Frame) -> Option<Scan> {
    let len = be16(d, q);
    let ns = byte(d, q + 2);
    if len != 2 * ns + 6 || ns < 1 || ns > 4 || ns > f.nc {
        None
    } else {
        let s = Scan {
            ns: ns as int,
            ci: Seq::new(ns as nat, |i: int| find_comp(f, byte(d, q + 3 + 2 * i), i, 0)),
            td: Seq::new(ns as nat, |i: int| byte(d, q + 4 + 2 * i) as int / 16),
            ta: Seq::new(ns as nat, |i: int| byte(d, q + 4 + 2 * i) as int % 16),
            ss: byte(d, q + 3 + 2 * ns) as int,
            se: byte(d, q + 4 + 2 * ns) as int,
            ah: byte(d, q + 5 + 2 * ns) as int / 16,
            al: byte(d, q + 5 + 2 * ns) as int % 16,
        };
        Some(s)
    }
}

/// The five bytes at `p` are `tag`.
pub open spec fn has_tag(d: Seq<u8>, p: int, tag: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < 5 ==> byte(d, p + i) == tag[i]
}

// ---------------------------------------------------------------------------
// The file
// ---------------------------------------------------------------------------
/// How the three components are to be read (libjpeg's
/// `default_decompress_parms`).
pub enum Color {
    Gray,
    YCbCr,
    Rgb,
}

/// The decoder's state between marker segments.
pub ghost struct Dec {
    pub t: Tables,
    pub f: Option<Frame>,
    /// A JFIF APP0 segment was seen.
    pub jfif: bool,
    /// An Adobe APP14 segment was seen, and its transform byte.
    pub adobe: Option<u8>,
    /// A scan has been decoded.
    pub started: bool,
    /// The file may have more than one scan: it is progressive, or its
    /// first scan left a component out.
    pub multi: bool,
    pub color: Color,
    /// Each component's quantization table, as it stood at the
    /// component's first scan; all zeros until then.
    pub ql: Seq<Seq<u16>>,
    pub qset: Seq<bool>,
    /// The coefficients of each component.
    pub a: Seq<Seq<i16>>,
}

/// The color space of a frame, decided at its first scan.
pub open spec fn color_of(f: Frame, jfif: bool, adobe: Option<u8>) -> Color {
    if f.nc == 1 {
        Color::Gray
    } else if jfif {
        Color::YCbCr
    } else if adobe is Some {
        if adobe->0 == 0 {
            Color::Rgb
        } else {
            Color::YCbCr
        }
    } else if f.comps[0].id == 82 && f.comps[1].id == 71 && f.comps[2].id == 66 {
        Color::Rgb
    } else {
        Color::YCbCr
    }
}

/// The quantization tables after latching those of scan `s`'s components
/// that had none yet, from scan component `i` on; `None` if one of them
/// names a table that was never defined.
pub open spec fn latch(f: Frame, t: Tables, s: Scan, ql: Seq<Seq<u16>>, qset: Seq<bool>, i: int) -> Option<
    (Seq<Seq<u16>>, Seq<bool>),
>
    decreases s.ns - i,
{
    if i >= s.ns {
        Some((ql, qset))
    } else {
        let c = s.ci[i] as int;
        if qset[c] {
            latch(f, t, s, ql, qset, i + 1)
        } else {
            let n = f.comps[c].tq as int;
            if n >= 4 || !t.qdef[n] {
                None
            } else {
                latch(f, t, s, ql.update(c, t.q[n]), qset.update(c, true), i + 1)
            }
        }
    }
}

/// The state after the scan whose header is at `q`, and where its
/// entropy-coded data ended.
pub open spec fn do_scan(d: Seq<u8>, q: int, st: Dec) -> Option<(Dec, int)> {
    if st.f is None {
        None
    } else {
        let f = st.f->0;
        match sos(d, q, f) {
            None => None,
            Some(s) => {
                let first = !st.started;
                let t = if first && !f.prog {
                    with_std(st.t)
                } else {
                    st.t
                };
                let multi = if first {
                    f.prog || s.ns < f.nc
                } else {
                    st.multi
                };
                let a = if first {
                    Seq::new(f.nc as nat, |c: int| Seq::new((64 * cw(f, c) * ch(f, c)) as nat, |j: int| 0i16))
                } else {
                    st.a
                };
                if !scan_ok(f, t, s) || (!first && !st.multi) {
                    None
                } else {
                    match latch(f, t, s, st.ql, st.qset, 0) {
                        None => None,
                        Some((ql, qset)) => {
                            let r = scan(d, f, t, s, a, q + be16(d, q));
                            if !r.ok {
                                None
                            } else {
                                Some(
                                    (
                                        Dec {
                                            t,
                                            started: true,
                                            multi,
                                            color: if first {
                                                color_of(f, st.jfif, st.adobe)
                                            } else {
                                                st.color
                                            },
                                            ql,
                                            qset,
                                            a: r.a,
                                            ..st
                                        },
                                        r.p,
                                    ),
                                )
                            }
                        },
                    }
                }
            },
        }
    }
}

/// The position after a segment with nothing in it for the decoder (COM,
/// most APPn): its length field counts itself.
pub open spec fn skip_seg(d: Seq<u8>, q: int) -> int {
    q + max2(be16(d, q), 2)
}

/// Whether the `n` bytes at `p` are a well-formed DAC payload (T.81 B.2.4.3,
/// and libjpeg's `get_dac`): pairs of a table number below 32 and a value,
/// where a DC table's value has its low half no greater than its high half.
pub open spec fn dac(d: Seq<u8>, p: int, n: int) -> bool
    decreases n + 2,
{
    if n <= 0 {
        n == 0
    } else {
        let i = byte(d, p);
        let v = byte(d, p + 1);
        i < 32 && (i >= 16 || (v & 0x0F) <= (v >> 4)) && dac(d, p + 2, n - 2)
    }
}

/// The marker segments from `p` to EOI (T.81 B.2.1, and libjpeg's
/// `read_markers`): the state at EOI, or `None` if the file is not one this
/// decoder takes.
pub open spec fn run(d: Seq<u8>, st: Dec, p: int) -> Option<Dec>
    decreases left(d, p),
    via run_dec
{
    let (m, q) = marker_after(d, p);
    if p >= d.len() || m == 0xD9 {
        // EOI.
        if st.started {
            Some(st)
        } else {
            None
        }
    } else if m == 0xDA {
        match do_scan(d, q, st) {
            None => None,
            Some((st2, p2)) => run(d, st2, p2),
        }
    } else if m == 0xDB {
        match dqt(d, q + 2, be16(d, q) - 2, st.t) {
            None => None,
            Some(t) => run(d, Dec { t, ..st }, q + be16(d, q)),
        }
    } else if m == 0xC4 {
        match dht(d, q + 2, be16(d, q) - 2, st.t) {
            None => None,
            Some(t) => run(d, Dec { t, ..st }, q + be16(d, q)),
        }
    } else if m == 0xDD {
        if be16(d, q) != 4 {
            None
        } else {
            run(d, Dec { t: Tables { ri: be16(d, q + 2), ..st.t }, ..st }, q + 4)
        }
    } else if m == 0xC0 || m == 0xC1 || m == 0xC2 {
        // Baseline, extended sequential and progressive Huffman frames.
        match sof(d, q, m == 0xC2) {
            None => None,
            Some(f) => if st.f is Some {
                None
            } else {
                run(d, Dec { f: Some(f), ..st }, q + be16(d, q))
            },
        }
    } else if m == 0xE0 {
        // JFIF.
        let jfif = be16(d, q) >= 16 && has_tag(d, q + 2, seq![0x4Au8, 0x46u8, 0x49u8, 0x46u8, 0u8]);
        run(d, Dec { jfif: st.jfif || jfif, ..st }, skip_seg(d, q))
    } else if m == 0xEE {
        // Adobe.
        let adobe = be16(d, q) >= 14 && has_tag(d, q + 2, seq![0x41u8, 0x64u8, 0x6Fu8, 0x62u8, 0x65u8]);
        run(
            d,
            Dec {
                adobe: if adobe {
                    Some(byte(d, q + 13))
                } else {
                    st.adobe
                },
                ..st
            },
            skip_seg(d, q),
        )
    } else if m == 0xCC {
        // DAC sets up arithmetic coding, which no frame taken here uses,
        // but libjpeg checks it all the same.
        if dac(d, q + 2, be16(d, q) - 2) {
            run(d, st, skip_seg(d, q))
        } else {
            None
        }
    } else if (0xE1 <= m <= 0xEF) || m == 0xFE || m == 0xDC {
        // Other APPn, COM, DNL: skipped.
        run(d, st, skip_seg(d, q))
    } else if (0xD0 <= m <= 0xD7) || m == 0x01 {
        // RSTn and TEM outside a scan stand alone and are passed over.
        run(d, st, q)
    } else {
        // SOI again, the other frame types (lossless, arithmetic,
        // hierarchical) and reserved codes.
        None
    }
}

#[via_fn]
proof fn run_dec(d: Seq<u8>, st: Dec, p: int) {
    lemma_marker_after(d, p);
    let q = marker_after(d, p).1;
    if st.f is Some && sos(d, q, st.f->0) is Some {
        let f = st.f->0;
        let s = sos(d, q, f)->0;
        let a = if !st.started {
            Seq::new(f.nc as nat, |c: int| Seq::new((64 * cw(f, c) * ch(f, c)) as nat, |j: int| 0i16))
        } else {
            st.a
        };
        let t = if !st.started && !f.prog {
            with_std(st.t)
        } else {
            st.t
        };
        lemma_scan_p(
            d,
            f,
            t,
            s,
            SS {
                a,
                pred: seq![0int, 0int, 0int],
                eob: 0,
                p: q + be16(d, q),
                n: 0,
                insuf: false,
                togo: t.ri as int,
                rst: 0,
                ok: true,
            },
            0,
        );
    }
}

/// A scan ends at or after the place it started.
pub proof fn lemma_scan_p(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int)
    ensures
        scan_from(d, f, t, s, st, m).p >= st.p,
    decreases scan_mcus(f, s) - m,
{
    if m < scan_mcus(f, s) {
        let st1 = if t.ri != 0 && st.togo == 0 {
            restart(d, t, st)
        } else {
            st
        };
        lemma_marker_after(d, st.p);
        let (mk, q) = marker_after(d, st.p);
        lemma_resync_p(d, mk, q, st.rst);
        assert(st1.p >= st.p);
        lemma_mcu_dc_p(d, f, t, s, st1, m, 0);
        lemma_scan_p(d, f, t, s, mcu_step(d, f, t, s, st, m), m + 1);
    }
}

pub proof fn lemma_resync_p(d: Seq<u8>, m: u8, q: int, want: int)
    ensures
        resync(d, m, q, want).0 >= q - 2,
    decreases togo(q, d.len() as int + 1),
{
    if q > d.len() {
    } else if m < 0xC0 || m == 0xD0 + (want + 7) % 8 || m == 0xD0 + (want + 6) % 8 {
        lemma_marker_after(d, q);
        let (m2, q2) = marker_after(d, q);
        lemma_resync_p(d, m2, q2, want);
    }
}

pub proof fn lemma_mcu_dc_p(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int, b: int)
    ensures
        mcu_dc(d, f, t, s, st, m, b).p == st.p,
    decreases mcu_blocks(f, s) - b,
{
    if b < mcu_blocks(f, s) {
        lemma_mcu_dc_p(d, f, t, s, mcu_dc_block(d, f, t, s, st, m, b), m, b + 1);
    }
}

/// The typical Huffman tables of T.81 K.3: the code counts and symbols for
/// luminance DC, chrominance DC, luminance AC and chrominance AC.
pub const STD_DC_L: [u8; 28] = [0, 1, 5, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

pub const STD_DC_C: [u8; 28] = [0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

pub const STD_AC_L: [u8; 178] = [
    0, 2, 1, 3, 3, 2, 4, 3, 5, 5, 4, 4, 0, 0, 1, 0x7d, 0x01, 0x02, 0x03, 0x00, 0x04, 0x11, 0x05, 0x12, 0x21, 0x31, 0x41,
    0x06, 0x13, 0x51, 0x61, 0x07, 0x22, 0x71, 0x14, 0x32, 0x81, 0x91, 0xa1, 0x08, 0x23, 0x42, 0xb1, 0xc1, 0x15, 0x52,
    0xd1, 0xf0, 0x24, 0x33, 0x62, 0x72, 0x82, 0x09, 0x0a, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x25, 0x26, 0x27, 0x28, 0x29,
    0x2a, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x53, 0x54, 0x55,
    0x56, 0x57, 0x58, 0x59, 0x5a, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,
    0x79, 0x7a, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a,
    0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xc2,
    0xc3, 0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda, 0xe1, 0xe2,
    0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa,
];

pub const STD_AC_C: [u8; 178] = [
    0, 2, 1, 2, 4, 4, 3, 4, 7, 5, 4, 4, 0, 1, 2, 0x77, 0x00, 0x01, 0x02, 0x03, 0x11, 0x04, 0x05, 0x21, 0x31, 0x06, 0x12,
    0x41, 0x51, 0x07, 0x61, 0x71, 0x13, 0x22, 0x32, 0x81, 0x08, 0x14, 0x42, 0x91, 0xa1, 0xb1, 0xc1, 0x09, 0x23, 0x33,
    0x52, 0xf0, 0x15, 0x62, 0x72, 0xd1, 0x0a, 0x16, 0x24, 0x34, 0xe1, 0x25, 0xf1, 0x17, 0x18, 0x19, 0x1a, 0x26, 0x27,
    0x28, 0x29, 0x2a, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x53, 0x54,
    0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x73, 0x74, 0x75, 0x76, 0x77,
    0x78, 0x79, 0x7a, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98,
    0x99, 0x9a, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9,
    0xba, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda,
    0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa,
];

/// The table a list of sixteen counts and then symbols stands for.
pub open spec fn std_table(a: Seq<u8>) -> HuffTable {
    HuffTable {
        counts: a.subrange(0, 16),
        vals: Seq::new(
            256,
            |i: int|
                if 16 + i < a.len() {
                    a[16 + i]
                } else {
                    0u8
                },
        ),
    }
}

/// The tables a decoder starts with: none, and no restart interval.
pub open spec fn no_tables() -> Tables {
    let none = HuffTable { counts: Seq::new(16, |i: int| 0u8), vals: Seq::new(256, |i: int| 0u8) };
    Tables {
        q: Seq::new(4, |i: int| zeros64()),
        qdef: Seq::new(4, |i: int| false),
        dc: Seq::new(4, |i: int| none),
        dcdef: Seq::new(4, |i: int| false),
        ac: Seq::new(4, |i: int| none),
        acdef: Seq::new(4, |i: int| false),
        ri: 0,
    }
}

/// `t` with the typical Huffman tables in slots 0 (luminance) and 1
/// (chrominance) where the file has defined none. libjpeg does this for a
/// sequential file when its first scan starts (`jinit_huff_decoder`), for
/// the files, Motion JPEG frames above all, that carry no tables; it does
/// not for a progressive one.
pub open spec fn with_std(t: Tables) -> Tables {
    Tables {
        dc: Seq::new(
            4,
            |i: int|
                if t.dcdef[i] || i >= 2 {
                    t.dc[i]
                } else if i == 0 {
                    std_table(STD_DC_L@)
                } else {
                    std_table(STD_DC_C@)
                },
        ),
        dcdef: Seq::new(4, |i: int| t.dcdef[i] || i < 2),
        ac: Seq::new(
            4,
            |i: int|
                if t.acdef[i] || i >= 2 {
                    t.ac[i]
                } else if i == 0 {
                    std_table(STD_AC_L@)
                } else {
                    std_table(STD_AC_C@)
                },
        ),
        acdef: Seq::new(4, |i: int| t.acdef[i] || i < 2),
        ..t
    }
}

/// The state a decoder starts in.
pub open spec fn dec_init() -> Dec {
    Dec {
        t: no_tables(),
        f: None,
        jfif: false,
        adobe: None,
        started: false,
        multi: false,
        color: Color::Gray,
        ql: seq![zeros64(), zeros64(), zeros64()],
        qset: seq![false, false, false],
        a: Seq::empty(),
    }
}

pub open spec fn zeros64() -> Seq<u16> {
    Seq::new(64, |i: int| 0u16)
}

// ---------------------------------------------------------------------------
// Samples: dequantization and the inverse DCT (libjpeg's `jidctint.c`)
// ---------------------------------------------------------------------------
/// A 16-bit quantization value as libjpeg's multiplier table holds it, in
/// a signed 16-bit word.
pub open spec fn sx16(x: int) -> int {
    if x >= 0x8000 {
        x - 0x1_0000
    } else {
        x
    }
}

/// `(x + 2^(n-1)) >> n`: division by `2^n`, rounded to nearest.
pub open spec fn descale(x: int, n: nat) -> int {
    (x + pow2((n - 1) as nat)) / pow2(n) as int
}

/// One pass of the Loeffler-Ligtenberg-Moshovitz inverse DCT over eight
/// values, in 13-bit fixed point, before the final shift
/// (`jpeg_idct_islow`).
pub open spec fn idct_1d(x: Seq<int>) -> Seq<int> {
    let z1 = (x[2] + x[6]) * 4433;
    let t2 = z1 + x[6] * (-15137);
    let t3 = z1 + x[2] * 6270;
    let t0 = (x[0] + x[4]) * 8192;
    let t1 = (x[0] - x[4]) * 8192;
    let t10 = t0 + t3;
    let t13 = t0 - t3;
    let t11 = t1 + t2;
    let t12 = t1 - t2;
    let z1 = x[7] + x[1];
    let z2 = x[5] + x[3];
    let z3 = x[7] + x[3];
    let z4 = x[5] + x[1];
    let z5 = (z3 + z4) * 9633;
    let z1 = z1 * (-7373);
    let z2 = z2 * (-20995);
    let z3 = z3 * (-16069) + z5;
    let z4 = z4 * (-3196) + z5;
    let t0 = x[7] * 2446 + z1 + z3;
    let t1 = x[5] * 16819 + z2 + z4;
    let t2 = x[3] * 25172 + z2 + z3;
    let t3 = x[1] * 12299 + z1 + z4;
    seq![t10 + t3, t11 + t2, t12 + t1, t13 + t0, t13 - t0, t12 - t1, t11 - t2, t10 - t3]
}

/// The first pass, down column `x` of the dequantized block `c`: row `y` of
/// the workspace, which libjpeg keeps in 32 bits.
pub open spec fn idct_col(c: Seq<int>, x: int, y: int) -> int {
    wrap32(descale(idct_1d(Seq::new(8, |i: int| c[8 * i + x]))[y], 11))
}

/// libjpeg's range limit after the inverse DCT: the level shift by 128 and
/// the clamp to a sample, on the low ten bits of the value.
pub open spec fn range_limit(x: int) -> u8 {
    let m = x % 1024;
    if m < 128 {
        (m + 128) as u8
    } else if m < 512 {
        255u8
    } else if m < 896 {
        0u8
    } else {
        (m - 896) as u8
    }
}

/// The sample at row `y`, column `x` of a block of dequantized
/// coefficients.
pub open spec fn idct(c: Seq<int>, y: int, x: int) -> u8 {
    range_limit(descale(idct_1d(Seq::new(8, |j: int| idct_col(c, j, y)))[x], 18))
}

/// The dequantized coefficients of the block at `o`.
pub open spec fn dequant(a: Seq<i16>, o: int, q: Seq<u16>) -> Seq<int> {
    Seq::new(64, |k: int| a[o + k] as int * sx16(q[k] as int))
}

/// What has been decoded: the frame, each component's coefficients and
/// quantization table, and the color space.
pub ghost struct Coded {
    pub f: Frame,
    pub a: Seq<Seq<i16>>,
    pub ql: Seq<Seq<u16>>,
    pub color: Color,
}

/// Sample (`r`, `x`) of component `c`.
pub open spec fn sample(k: Coded, c: int, r: int, x: int) -> int {
    idct(dequant(k.a[c], 64 * ((r / 8) * cw(k.f, c) + x / 8), k.ql[c]), r % 8, x % 8) as int
}

// ---------------------------------------------------------------------------
// Pixels: upsampling (libjpeg's `jdsample.c`, "fancy" upsampling) and color
// conversion (`jdcolor.c`)
// ---------------------------------------------------------------------------
pub open spec fn clamp(x: int, lo: int, hi: int) -> int {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

/// The sample row a vertical 2:1 upsampler blends with row `y / 2` for
/// output row `y`: the one above for the upper output row, the one below
/// for the lower, and the row itself at the image's top and bottom.
pub open spec fn far_row(k: Coded, c: int, y: int) -> int {
    if y % 2 == 0 {
        clamp(y / 2 - 1, 0, dh(k.f, c) - 1)
    } else {
        clamp(y / 2 + 1, 0, dh(k.f, c) - 1)
    }
}

/// `3 * near + far` for the two rows `h2v2_fancy_upsample` blends.
pub open spec fn colsum(k: Coded, c: int, y: int, x: int) -> int {
    3 * sample(k, c, y / 2, x) + sample(k, c, far_row(k, c, y), x)
}

/// Component `c` at output pixel (`y`, `x`): the component's sample there,
/// brought up to the frame's resolution. Horizontal 2:1 (`h2v1`), vertical
/// 2:1 (`h1v2`) and 2:1 both ways (`h2v2`) use libjpeg's triangle filters,
/// the two that double the width only when the component is more than two
/// samples wide; every other ratio replicates samples.
pub open spec fn upsampled(k: Coded, c: int, y: int, x: int) -> int {
    let hs = maxh(k.f) / k.f.comps[c].h as int;
    let vs = maxv(k.f) / k.f.comps[c].v as int;
    let w = dw(k.f, c);
    let i = x / 2;
    if hs == 2 && vs == 1 && w > 2 {
        let s = sample(k, c, y, i);
        if x % 2 == 0 {
            if i == 0 {
                s
            } else {
                (3 * s + sample(k, c, y, i - 1) + 1) / 4
            }
        } else if i == w - 1 {
            s
        } else {
            (3 * s + sample(k, c, y, i + 1) + 2) / 4
        }
    } else if hs == 1 && vs == 2 {
        (colsum(k, c, y, x) + 1 + y % 2) / 4
    } else if hs == 2 && vs == 2 && w > 2 {
        let s = colsum(k, c, y, i);
        if x % 2 == 0 {
            if i == 0 {
                (4 * s + 8) / 16
            } else {
                (3 * s + colsum(k, c, y, i - 1) + 8) / 16
            }
        } else if i == w - 1 {
            (4 * s + 7) / 16
        } else {
            (3 * s + colsum(k, c, y, i + 1) + 7) / 16
        }
    } else {
        sample(k, c, y / vs, x / hs)
    }
}

/// libjpeg's YCbCr to RGB conversion (JFIF's, in 16-bit fixed point).
pub open spec fn ycc_r(y: int, cr: int) -> int {
    clamp(y + (91881 * (cr - 128) + 32768) / 65536, 0, 255)
}

pub open spec fn ycc_g(y: int, cb: int, cr: int) -> int {
    clamp(y + (-22554 * (cb - 128) - 46802 * (cr - 128) + 32768) / 65536, 0, 255)
}

pub open spec fn ycc_b(y: int, cb: int) -> int {
    clamp(y + (116130 * (cb - 128) + 32768) / 65536, 0, 255)
}

/// Channel `ch` of output pixel (`y`, `x`): one channel for a grayscale
/// file, red, green and blue for the others.
pub open spec fn pixel(k: Coded, y: int, x: int, ch: int) -> int {
    match k.color {
        Color::Gray => upsampled(k, 0, y, x),
        Color::Rgb => upsampled(k, ch, y, x),
        Color::YCbCr => {
            let l = upsampled(k, 0, y, x);
            let cb = upsampled(k, 1, y, x);
            let cr = upsampled(k, 2, y, x);
            if ch == 0 {
                ycc_r(l, cr)
            } else if ch == 1 {
                ycc_g(l, cb, cr)
            } else {
                ycc_b(l, cb)
            }
        },
    }
}

/// A decoded image: `nc` channels (1 gray, or 3 red-green-blue) per pixel,
/// rows top to bottom.
pub ghost struct Image {
    pub w: int,
    pub h: int,
    pub nc: int,
    pub px: Seq<u8>,
}

pub open spec fn render(k: Coded) -> Image {
    let nc = k.f.nc as int;
    let w = k.f.w as int;
    Image {
        w,
        h: k.f.h as int,
        nc,
        px: Seq::new((w * k.f.h * nc) as nat, |j: int| pixel(k, j / (w * nc), (j / nc) % w, j % nc) as u8),
    }
}

/// What the scans of a file decode to: `None` if the file is not a JPEG
/// this decoder takes.
pub open spec fn jpeg_coded(d: Seq<u8>) -> Option<Coded> {
    if byte(d, 0) != 0xFF || byte(d, 1) != 0xD8 {
        None
    } else {
        match run(d, dec_init(), 2) {
            None => None,
            Some(st) => Some(Coded { f: st.f->0, a: st.a, ql: st.ql, color: st.color }),
        }
    }
}

/// The image a file decodes to.
pub open spec fn jpeg_decode(d: Seq<u8>) -> Option<Image> {
    match jpeg_coded(d) {
        None => None,
        Some(k) => Some(render(k)),
    }
}

} // verus!
