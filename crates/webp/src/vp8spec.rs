//! A specification of VP8 (RFC 6386), written from the RFC and not from
//! the decoder, and the lemmas about it that the decoder's proofs use.
//!
//! So far it covers section 7, the boolean entropy decoder: every bit the
//! lossy decoder reads from a partition goes through it.
use crate::vp8tables::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Section 7: the boolean decoder
// ---------------------------------------------------------------------
/// Bit `i` of a partition, the most significant bit of each byte first.
/// Bits past the end read as zero (RFC 6386 section 7.3: the decoder may
/// read past the end of a partition, and zeros are supplied).
pub open spec fn stream_bit(data: Seq<u8>, i: nat) -> nat {
    if i / 8 < data.len() {
        (data[(i / 8) as int] as nat / pow2((7 - i % 8) as nat)) % 2
    } else {
        0
    }
}

/// The `n` bits from bit `a` on, as a number.
pub open spec fn stream_bits(data: Seq<u8>, a: nat, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        2 * stream_bits(data, a, (n - 1) as nat) + stream_bit(data, a + (n - 1) as nat)
    }
}

/// The decoder state of section 7.3, with the two-byte `value` of the RFC's
/// reference code replaced by its top byte and a bit position: the low byte
/// of the RFC's `value` only buffers bits that `pos` has not reached yet.
pub struct BoolState {
    /// `range`, in `[128, 255]` between reads.
    pub range: int,
    /// The top byte of the RFC's `value`: the code word relative to `range`.
    pub value: int,
    /// The next bit of the partition to shift into `value`.
    pub pos: nat,
}

/// `init_bool_decoder`: the first byte is the value and the range is 255.
pub open spec fn bool_init(data: Seq<u8>) -> BoolState {
    BoolState { range: 255, value: stream_bits(data, 0, 8) as int, pos: 8 }
}

/// `split = 1 + (((range - 1) * prob) >> 8)`.
pub open spec fn bool_split(range: int, prob: int) -> int {
    1 + ((range - 1) * prob) / 256
}

/// The bit `read_bool(prob)` returns in state `s`.
pub open spec fn bool_bit(s: BoolState, prob: int) -> bool {
    s.value >= bool_split(s.range, prob)
}

/// `read_bool` up to its renormalization loop.
pub open spec fn bool_take(s: BoolState, prob: int) -> BoolState {
    let split = bool_split(s.range, prob);
    if s.value >= split {
        BoolState { range: s.range - split, value: s.value - split, pos: s.pos }
    } else {
        BoolState { range: split, value: s.value, pos: s.pos }
    }
}

/// The renormalization loop: `while range < 128 { value <<= 1; range <<= 1;
/// ... }`, shifting in one partition bit per round.
pub open spec fn bool_norm(data: Seq<u8>, s: BoolState) -> BoolState
    decreases
            (if 0 < s.range < 128 {
                128 - s.range
            } else {
                0
            }),
{
    if s.range >= 128 || s.range <= 0 {
        s
    } else {
        bool_norm(
            data,
            BoolState { range: 2 * s.range, value: 2 * s.value + stream_bit(data, s.pos), pos: s.pos + 1 },
        )
    }
}

/// The state after `read_bool(prob)`.
pub open spec fn bool_next(data: Seq<u8>, s: BoolState, prob: int) -> BoolState {
    bool_norm(data, bool_take(s, prob))
}

/// `read_literal(n)` (section 7.3, `L(n)` in section 8): `n` bits at
/// probability 128, the most significant first.
pub open spec fn bool_literal(data: Seq<u8>, s: BoolState, n: nat) -> (BoolState, int)
    decreases n,
{
    if n == 0 {
        (s, 0)
    } else {
        let (s1, v) = bool_literal(data, s, (n - 1) as nat);
        (
            bool_next(data, s1, 128),
            2 * v + if bool_bit(s1, 128) {
                1int
            } else {
                0int
            },
        )
    }
}

/// What an arithmetic coder guarantees of the code word: it lies inside
/// the current range. Every stream an encoder can produce keeps this; the
/// one way to break it is a partition whose first byte is `0xff`.
pub open spec fn bool_wf(s: BoolState) -> bool {
    128 <= s.range <= 255 && 0 <= s.value < s.range
}

// ---------------------------------------------------------------------
// Sections 9 and 19.2: the key frame header
// ---------------------------------------------------------------------
/// `L(1)`: a flag.
pub open spec fn rd_flag(data: Seq<u8>, s: BoolState) -> (BoolState, bool) {
    (bool_next(data, s, 128), bool_bit(s, 128))
}

/// An `n`-bit magnitude followed by its sign bit.
pub open spec fn rd_signed(data: Seq<u8>, s: BoolState, n: nat) -> (BoolState, int) {
    let (s1, m) = bool_literal(data, s, n);
    (
        bool_next(data, s1, 128),
        if bool_bit(s1, 128) {
            -m
        } else {
            m
        },
    )
}

/// A flag, then a signed `n`-bit value if it is set; zero if not.
pub open spec fn rd_opt_signed(data: Seq<u8>, s: BoolState, n: nat) -> (BoolState, int) {
    if bool_bit(s, 128) {
        rd_signed(data, bool_next(data, s, 128), n)
    } else {
        (bool_next(data, s, 128), 0)
    }
}

/// A flag, then an `n`-bit value if it is set; `dflt` if not.
pub open spec fn rd_opt_lit(data: Seq<u8>, s: BoolState, n: nat, dflt: int) -> (BoolState, int) {
    if bool_bit(s, 128) {
        bool_literal(data, bool_next(data, s, 128), n)
    } else {
        (bool_next(data, s, 128), dflt)
    }
}

/// `count` optional signed values in a row.
pub open spec fn rd_opt_signed_seq(data: Seq<u8>, s: BoolState, n: nat, count: nat) -> (BoolState, Seq<int>)
    decreases count,
{
    if count == 0 {
        (s, Seq::empty())
    } else {
        let (s1, v) = rd_opt_signed_seq(data, s, n, (count - 1) as nat);
        let (s2, x) = rd_opt_signed(data, s1, n);
        (s2, v.push(x))
    }
}

/// `count` optional values in a row.
pub open spec fn rd_opt_lit_seq(data: Seq<u8>, s: BoolState, n: nat, dflt: int, count: nat) -> (BoolState, Seq<int>)
    decreases count,
{
    if count == 0 {
        (s, Seq::empty())
    } else {
        let (s1, v) = rd_opt_lit_seq(data, s, n, dflt, (count - 1) as nat);
        let (s2, x) = rd_opt_lit(data, s1, n, dflt);
        (s2, v.push(x))
    }
}

/// Section 9.3, `update_segmentation()`.
pub struct SegHeader {
    pub enabled: bool,
    pub update_map: bool,
    pub update_data: bool,
    /// `segment_feature_mode`: the values are absolute, not deltas.
    pub absolute: bool,
    /// Quantizer per segment.
    pub quant: Seq<int>,
    /// Loop filter level per segment.
    pub lf: Seq<int>,
    /// `segment_prob_update`: the tree probabilities of the segment map.
    pub probs: Seq<int>,
}

pub open spec fn zeros4() -> Seq<int> {
    seq![0int, 0int, 0int, 0int]
}

/// The segment header. Where the frame does not carry a field, the value
/// is the key-frame default libwebp uses (`ResetSegmentHeader`): zeros,
/// probabilities of 255, and absolute mode.
pub open spec fn seg_header(data: Seq<u8>, s: BoolState) -> (BoolState, SegHeader) {
    let (s1, enabled) = rd_flag(data, s);
    if !enabled {
        (
            s1,
            SegHeader {
                enabled: false,
                update_map: false,
                update_data: false,
                absolute: true,
                quant: zeros4(),
                lf: zeros4(),
                probs: seq![255int, 255int, 255int],
            },
        )
    } else {
        let (s2, update_map) = rd_flag(data, s1);
        let (s3, update_data) = rd_flag(data, s2);
        let (s4, absolute) = if update_data {
            rd_flag(data, s3)
        } else {
            (s3, true)
        };
        let (s5, quant) = if update_data {
            rd_opt_signed_seq(data, s4, 7, 4)
        } else {
            (s4, zeros4())
        };
        let (s6, lf) = if update_data {
            rd_opt_signed_seq(data, s5, 6, 4)
        } else {
            (s5, zeros4())
        };
        let (s7, probs) = if update_map {
            rd_opt_lit_seq(data, s6, 8, 255, 3)
        } else {
            (s6, seq![255int, 255int, 255int])
        };
        (s7, SegHeader { enabled, update_map, update_data, absolute, quant, lf, probs })
    }
}

/// Sections 9.6 and 19.2: the loop filter header with `mb_lf_adjustments()`.
pub struct FilterHeader {
    /// `filter_type`: the simple filter.
    pub simple: bool,
    pub level: int,
    pub sharpness: int,
    pub adj_enable: bool,
    pub delta_update: bool,
    /// `ref_frame_delta`, zero where the frame carries none.
    pub ref_delta: Seq<int>,
    /// `mb_mode_delta`, zero where the frame carries none.
    pub mode_delta: Seq<int>,
}

pub open spec fn filter_header(data: Seq<u8>, s: BoolState) -> (BoolState, FilterHeader) {
    let (s1, simple) = rd_flag(data, s);
    let (s2, level) = bool_literal(data, s1, 6);
    let (s3, sharpness) = bool_literal(data, s2, 3);
    let (s4, adj_enable) = rd_flag(data, s3);
    let (s5, delta_update) = if adj_enable {
        rd_flag(data, s4)
    } else {
        (s4, false)
    };
    let (s6, ref_delta) = if delta_update {
        rd_opt_signed_seq(data, s5, 6, 4)
    } else {
        (s5, zeros4())
    };
    let (s7, mode_delta) = if delta_update {
        rd_opt_signed_seq(data, s6, 6, 4)
    } else {
        (s6, zeros4())
    };
    (s7, FilterHeader { simple, level, sharpness, adj_enable, delta_update, ref_delta, mode_delta })
}

/// Section 9.6, `quant_indices()`.
pub struct QuantHeader {
    pub y_ac_qi: int,
    pub y_dc_delta: int,
    pub y2_dc_delta: int,
    pub y2_ac_delta: int,
    pub uv_dc_delta: int,
    pub uv_ac_delta: int,
}

pub open spec fn quant_header(data: Seq<u8>, s: BoolState) -> (BoolState, QuantHeader) {
    let (s1, y_ac_qi) = bool_literal(data, s, 7);
    let (s2, y_dc_delta) = rd_opt_signed(data, s1, 4);
    let (s3, y2_dc_delta) = rd_opt_signed(data, s2, 4);
    let (s4, y2_ac_delta) = rd_opt_signed(data, s3, 4);
    let (s5, uv_dc_delta) = rd_opt_signed(data, s4, 4);
    let (s6, uv_ac_delta) = rd_opt_signed(data, s5, 4);
    (s6, QuantHeader { y_ac_qi, y_dc_delta, y2_dc_delta, y2_ac_delta, uv_dc_delta, uv_ac_delta })
}

/// Section 13.4, `token_prob_update()` on a key frame: each of the 1056
/// token probabilities is replaced by an 8-bit value when a flag, read at
/// that entry's update probability (section 13.4's `coeff_update_probs`),
/// is set, and is the default (section 13.5) otherwise.
pub open spec fn token_probs(data: Seq<u8>, s: BoolState, count: nat) -> (BoolState, Seq<int>)
    decreases count,
{
    if count == 0 {
        (s, Seq::empty())
    } else {
        let k = (count - 1) as nat;
        let (s1, v) = token_probs(data, s, k);
        let up = spec_coeffs_update_proba(k as int) as int;
        let s2 = bool_next(data, s1, up);
        if bool_bit(s1, up) {
            let (s3, x) = bool_literal(data, s2, 8);
            (s3, v.push(x))
        } else {
            (s2, v.push(spec_coeffs_proba0(k as int) as int))
        }
    }
}

/// The key frame header of section 19.2, after the uncompressed data chunk.
pub struct FrameHeader {
    pub color_space: bool,
    pub clamping_type: bool,
    pub seg: SegHeader,
    pub filter: FilterHeader,
    pub log2_parts: int,
    pub quant: QuantHeader,
    pub refresh_entropy_probs: bool,
    pub probs: Seq<int>,
    pub mb_no_coeff_skip: bool,
    pub prob_skip_false: int,
}

pub open spec fn frame_header(data: Seq<u8>, s: BoolState) -> (BoolState, FrameHeader) {
    let (s1, color_space) = rd_flag(data, s);
    let (s2, clamping_type) = rd_flag(data, s1);
    let (s3, seg) = seg_header(data, s2);
    let (s4, filter) = filter_header(data, s3);
    let (s5, log2_parts) = bool_literal(data, s4, 2);
    let (s6, quant) = quant_header(data, s5);
    let (s7, refresh_entropy_probs) = rd_flag(data, s6);
    let (s8, probs) = token_probs(data, s7, 1056);
    let (s9, mb_no_coeff_skip) = rd_flag(data, s8);
    let (s10, prob_skip_false) = if mb_no_coeff_skip {
        bool_literal(data, s9, 8)
    } else {
        (s9, 0)
    };
    (
        s10,
        FrameHeader {
            color_space,
            clamping_type,
            seg,
            filter,
            log2_parts,
            quant,
            refresh_entropy_probs,
            probs,
            mb_no_coeff_skip,
            prob_skip_false,
        },
    )
}

/// Section 9.1: the three-byte frame tag's `first_part_size`.
pub open spec fn first_part_size(file: Seq<u8>, off: int) -> int {
    (file[off] as int + 256 * (file[off + 1] as int) + 65536 * (file[off + 2] as int)) / 32
}

/// Section 9.1: the 14-bit width and height after the start code.
pub open spec fn frame_width(file: Seq<u8>, off: int) -> int {
    (file[off + 7] as int % 64) * 256 + file[off + 6] as int
}

pub open spec fn frame_height(file: Seq<u8>, off: int) -> int {
    (file[off + 9] as int % 64) * 256 + file[off + 8] as int
}

pub open spec fn le24(file: Seq<u8>, i: int) -> int {
    file[i] as int + 256 * (file[i + 1] as int) + 65536 * (file[i + 2] as int)
}

/// Section 9.5: where token partition `p` begins, for a file whose
/// partition size table is at `pstart` and has `last` three-byte entries.
/// A size that runs past the end of the file is cut to what is left, as
/// libwebp does (`ParsePartitions`).
pub open spec fn part_begin(file: Seq<u8>, pstart: int, last: int, p: nat) -> int
    decreases p,
{
    if p == 0 {
        pstart + 3 * last
    } else {
        let b = part_begin(file, pstart, last, (p - 1) as nat);
        let sz = le24(file, pstart + 3 * (p - 1));
        let left = file.len() - b;
        b + if sz > left {
            left
        } else {
            sz
        }
    }
}

pub open spec fn clip_to(v: int, m: int) -> int {
    if v < 0 {
        0
    } else if v > m {
        m
    } else {
        v
    }
}

/// Section 9.6: the quantizer index of segment `i`.
pub open spec fn seg_qindex(fh: FrameHeader, i: int) -> int {
    if fh.seg.enabled {
        if fh.seg.absolute {
            fh.seg.quant[i]
        } else {
            fh.seg.quant[i] + fh.quant.y_ac_qi
        }
    } else {
        fh.quant.y_ac_qi
    }
}

/// Sections 9.6 and 14.1: the six dequantization factors of segment `i`,
/// as `(y1 dc, y1 ac, y2 dc, y2 ac, uv dc, uv ac)`.
pub open spec fn seg_quant(fh: FrameHeader, i: int) -> (int, int, int, int, int, int) {
    let q = seg_qindex(fh, i);
    let y2ac = (spec_ac_table(clip_to(q + fh.quant.y2_ac_delta, 127)) as int * 101581) / 65536;
    (
        spec_dc_table(clip_to(q + fh.quant.y_dc_delta, 127)) as int,
        spec_ac_table(clip_to(q, 127)) as int,
        spec_dc_table(clip_to(q + fh.quant.y2_dc_delta, 127)) as int * 2,
        if y2ac < 8 {
            8
        } else {
            y2ac
        },
        spec_dc_table(clip_to(q + fh.quant.uv_dc_delta, 117)) as int,
        spec_ac_table(clip_to(q + fh.quant.uv_ac_delta, 127)) as int,
    )
}

/// Sections 9.3, 9.6 and 15.2: the loop filter level of a macroblock in
/// segment `s`, with 4x4 prediction (`B_PRED`) or not, on a key frame.
///
/// This is libwebp's arithmetic (`PrecomputeFilterStrengths`): one clamp,
/// at the end. libvpx (`vp8_loop_filter_frame_init`) also clamps the
/// segment's level to 0..63 before it adds the deltas, so the two differ
/// when that level leaves the range and the deltas are enabled.
pub open spec fn seg_filter_level(fh: FrameHeader, s: int, i4x4: bool) -> int {
    let base = if fh.seg.enabled {
        if fh.seg.absolute {
            fh.seg.lf[s]
        } else {
            fh.seg.lf[s] + fh.filter.level
        }
    } else {
        fh.filter.level
    };
    let adj = if fh.filter.adj_enable {
        base + fh.filter.ref_delta[0] + if i4x4 {
            fh.filter.mode_delta[0]
        } else {
            0
        }
    } else {
        base
    };
    clip_to(adj, 63)
}

/// Section 15.2: the interior limit for a filter level and sharpness.
pub open spec fn interior_limit(level: int, sharpness: int) -> int {
    let a = if sharpness > 4 {
        level / 4
    } else if sharpness > 0 {
        level / 2
    } else {
        level
    };
    let b = if sharpness > 0 && a > 9 - sharpness {
        9 - sharpness
    } else {
        a
    };
    if b < 1 {
        1
    } else {
        b
    }
}

/// Section 15.3: the high edge variance threshold on a key frame.
pub open spec fn hev_threshold(level: int) -> int {
    if level >= 40 {
        2
    } else if level >= 15 {
        1
    } else {
        0
    }
}

// ---------------------------------------------------------------------
// Sections 9.3, 9.11 and 11: the per-macroblock header of a key frame
// ---------------------------------------------------------------------
/// `B(p)`: one bit at probability `p`.
pub open spec fn rd_bool(data: Seq<u8>, s: BoolState, p: int) -> (BoolState, bool) {
    (bool_next(data, s, p), bool_bit(s, p))
}

/// Section 9.3: the segment of a macroblock, from `mb_segment_tree` when
/// the frame updates the segment map.
pub open spec fn mb_segment(data: Seq<u8>, s: BoolState, fh: FrameHeader) -> (BoolState, int) {
    if fh.seg.update_map {
        let (s1, b0) = rd_bool(data, s, fh.seg.probs[0]);
        if !b0 {
            let (s2, b1) = rd_bool(data, s1, fh.seg.probs[1]);
            (
                s2,
                if b1 {
                    1
                } else {
                    0
                },
            )
        } else {
            let (s2, b1) = rd_bool(data, s1, fh.seg.probs[2]);
            (
                s2,
                if b1 {
                    3
                } else {
                    2
                },
            )
        }
    } else {
        (s, 0)
    }
}

/// Section 9.11: `mb_skip_coeff`.
pub open spec fn mb_skip(data: Seq<u8>, s: BoolState, fh: FrameHeader) -> (BoolState, bool) {
    if fh.mb_no_coeff_skip {
        rd_bool(data, s, fh.prob_skip_false)
    } else {
        (s, false)
    }
}

/// Section 11.2: `kf_ymode_tree` below its `B_PRED` branch, with
/// `kf_ymode_prob`. Modes are numbered as libwebp numbers them, here and
/// below: 0 `DC_PRED`, 1 `TM_PRED`, 2 `V_PRED`, 3 `H_PRED`.
pub open spec fn kf_ymode(data: Seq<u8>, s: BoolState) -> (BoolState, int) {
    let (s1, b) = rd_bool(data, s, 156);
    if b {
        let (s2, c) = rd_bool(data, s1, 128);
        (
            s2,
            if c {
                1
            } else {
                3
            },
        )
    } else {
        let (s2, c) = rd_bool(data, s1, 163);
        (
            s2,
            if c {
                2
            } else {
                0
            },
        )
    }
}

/// Section 11.2: `uv_mode_tree` with `kf_uv_mode_prob`.
pub open spec fn uv_mode(data: Seq<u8>, s: BoolState) -> (BoolState, int) {
    let (s1, a) = rd_bool(data, s, 142);
    if !a {
        (s1, 0)
    } else {
        let (s2, b) = rd_bool(data, s1, 114);
        if !b {
            (s2, 2)
        } else {
            let (s3, c) = rd_bool(data, s2, 183);
            (
                s3,
                if c {
                    1
                } else {
                    3
                },
            )
        }
    }
}

/// Section 11.2: `bmode_tree`, with the nine probabilities at `pb` of
/// `kf_bmode_probs`. Subblock modes: 0 `B_DC_PRED`, 1 `B_TM_PRED`,
/// 2 `B_VE_PRED`, 3 `B_HE_PRED`, 4 `B_RD_PRED`, 5 `B_VR_PRED`,
/// 6 `B_LD_PRED`, 7 `B_VL_PRED`, 8 `B_HD_PRED`, 9 `B_HU_PRED`.
pub open spec fn rd_bmode(data: Seq<u8>, s: BoolState, pb: int) -> (BoolState, int) {
    let (s0, b0) = rd_bool(data, s, spec_bmodes_proba(pb) as int);
    if !b0 {
        (s0, 0)
    } else {
        let (s1, b1) = rd_bool(data, s0, spec_bmodes_proba(pb + 1) as int);
        if !b1 {
            (s1, 1)
        } else {
            let (s2, b2) = rd_bool(data, s1, spec_bmodes_proba(pb + 2) as int);
            if !b2 {
                (s2, 2)
            } else {
                let (s3, b3) = rd_bool(data, s2, spec_bmodes_proba(pb + 3) as int);
                if !b3 {
                    let (s4, b4) = rd_bool(data, s3, spec_bmodes_proba(pb + 4) as int);
                    if !b4 {
                        (s4, 3)
                    } else {
                        let (s5, b5) = rd_bool(data, s4, spec_bmodes_proba(pb + 5) as int);
                        (
                            s5,
                            if b5 {
                                5
                            } else {
                                4
                            },
                        )
                    }
                } else {
                    let (s6, b6) = rd_bool(data, s3, spec_bmodes_proba(pb + 6) as int);
                    if !b6 {
                        (s6, 6)
                    } else {
                        let (s7, b7) = rd_bool(data, s6, spec_bmodes_proba(pb + 7) as int);
                        if !b7 {
                            (s7, 7)
                        } else {
                            let (s8, b8) = rd_bool(data, s7, spec_bmodes_proba(pb + 8) as int);
                            (
                                s8,
                                if b8 {
                                    9
                                } else {
                                    8
                                },
                            )
                        }
                    }
                }
            }
        }
    }
}

/// The subblock modes of a `B_PRED` macroblock read so far, with the
/// contexts they leave: the modes of the row above and of the column to
/// the left (section 11.3).
pub struct BmState {
    pub s: BoolState,
    pub modes: Seq<int>,
    pub top: Seq<int>,
    pub left: Seq<int>,
}

/// Subblock `n` (in raster order): its mode is read with the probabilities
/// selected by the modes above and to the left.
pub open spec fn bmode_step(data: Seq<u8>, st: BmState, n: nat) -> BmState {
    let y = (n / 4) as int;
    let x = (n % 4) as int;
    let l = if x == 0 {
        st.left[y]
    } else {
        st.modes[n - 1]
    };
    let (s1, m) = rd_bmode(data, st.s, (st.top[x] * 10 + l) * 9);
    BmState {
        s: s1,
        modes: st.modes.push(m),
        top: st.top.update(x, m),
        left: if x == 3 {
            st.left.update(y, m)
        } else {
            st.left
        },
    }
}

pub open spec fn rd_bmodes(data: Seq<u8>, s: BoolState, top: Seq<int>, left: Seq<int>, n: nat) -> BmState
    decreases n,
{
    if n == 0 {
        BmState { s, modes: Seq::empty(), top, left }
    } else {
        bmode_step(data, rd_bmodes(data, s, top, left, (n - 1) as nat), (n - 1) as nat)
    }
}

/// The modes of one macroblock.
pub struct MbModeSpec {
    pub segment: int,
    pub skip: bool,
    /// `B_PRED`: sixteen subblock modes in `bmodes`. Otherwise `ymode`.
    pub is_i4x4: bool,
    pub ymode: int,
    pub bmodes: Seq<int>,
    pub uvmode: int,
}

/// A macroblock's modes with the state and the mode contexts after it.
pub struct MbOut {
    pub s: BoolState,
    pub m: MbModeSpec,
    pub top: Seq<int>,
    pub left: Seq<int>,
}

/// Section 19.3, `macroblock_header()` on a key frame, with the four
/// subblock modes above (`top`) and to the left (`left`) as context. A
/// macroblock that is not `B_PRED` leaves its own mode as the context
/// (section 11.3; the numbering makes the implied subblock mode equal).
pub open spec fn mb_modes(data: Seq<u8>, s: BoolState, fh: FrameHeader, top: Seq<int>, left: Seq<int>) -> MbOut {
    let (s1, segment) = mb_segment(data, s, fh);
    let (s2, skip) = mb_skip(data, s1, fh);
    let (s3, not_b) = rd_bool(data, s2, 145);
    if not_b {
        let (s4, ymode) = kf_ymode(data, s3);
        let (s5, uvmode) = uv_mode(data, s4);
        MbOut {
            s: s5,
            m: MbModeSpec { segment, skip, is_i4x4: false, ymode, bmodes: Seq::empty(), uvmode },
            top: Seq::new(4, |i: int| ymode),
            left: Seq::new(4, |i: int| ymode),
        }
    } else {
        let b = rd_bmodes(data, s3, top, left, 16);
        let (s5, uvmode) = uv_mode(data, b.s);
        MbOut {
            s: s5,
            m: MbModeSpec { segment, skip, is_i4x4: true, ymode: 0, bmodes: b.modes, uvmode },
            top: b.top,
            left: b.left,
        }
    }
}

/// The modes of the first `n` macroblocks of a row, with the contexts
/// they leave. `top` holds four subblock modes per macroblock column; the
/// left context starts each row as `B_DC_PRED`.
pub struct RowModes {
    pub s: BoolState,
    pub mbs: Seq<MbModeSpec>,
    pub top: Seq<int>,
    pub left: Seq<int>,
}

pub open spec fn row_modes(data: Seq<u8>, s: BoolState, fh: FrameHeader, top: Seq<int>, n: nat) -> RowModes
    decreases n,
{
    if n == 0 {
        RowModes { s, mbs: Seq::empty(), top, left: zeros4() }
    } else {
        let k = (n - 1) as int;
        let r = row_modes(data, s, fh, top, (n - 1) as nat);
        let o = mb_modes(data, r.s, fh, r.top.subrange(4 * k, 4 * k + 4), r.left);
        RowModes {
            s: o.s,
            mbs: r.mbs.push(o.m),
            top: Seq::new(
                r.top.len(),
                |i: int|
                    if 4 * k <= i < 4 * k + 4 {
                        o.top[i - 4 * k]
                    } else {
                        r.top[i]
                    },
            ),
            left: o.left,
        }
    }
}

/// The decoder state and the mode context after the modes of `rows` rows
/// of `mb_w` macroblocks, starting from state `s` (the end of the frame
/// header) with every context `B_DC_PRED`.
pub open spec fn mode_rows(data: Seq<u8>, s: BoolState, fh: FrameHeader, mb_w: nat, rows: nat) -> RowModes
    decreases rows,
{
    if rows == 0 {
        RowModes { s, mbs: Seq::empty(), top: Seq::new(4 * mb_w, |i: int| 0int), left: zeros4() }
    } else {
        let r = mode_rows(data, s, fh, mb_w, (rows - 1) as nat);
        row_modes(data, r.s, fh, r.top, mb_w)
    }
}

// ---------------------------------------------------------------------
// Section 13: the DCT coefficient tokens of one block
// ---------------------------------------------------------------------
/// `x` as a 16-bit two's complement value. Coefficients are stored in 16
/// bits after dequantization, by libwebp as by libvpx; only tokens no
/// encoder produces for a real image reach the wrap.
pub open spec fn wrap16s(x: int) -> int {
    let m = x % 0x1_0000;
    if m >= 0x8000 {
        m - 0x1_0000
    } else {
        m
    }
}

/// Section 13.3: `coeff_bands`, with a seventeenth entry so that the
/// position after the last coefficient has one.
pub open spec fn coeff_band(n: int) -> int {
    seq![0int, 1, 2, 3, 6, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7, 0][n]
}

/// Section 14.2: `zigzag`, where coefficient `n` of the stream goes.
pub open spec fn zigzag(n: int) -> int {
    seq![0int, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15][n]
}

/// Where the eleven tree probabilities for block type `t`, position `n`
/// and context `ctx` start in the flattened `coeff_probs`.
pub open spec fn token_pidx(t: int, n: int, ctx: int) -> int {
    ((t * 8 + coeff_band(n)) * 3 + ctx) * 11
}

/// Section 13.2: the extra bits of a `dct_cat` token, the most significant
/// first, each at its own probability.
pub open spec fn rd_extra(data: Seq<u8>, s: BoolState, tab: Seq<u8>, n: nat) -> (BoolState, int)
    decreases n,
{
    if n == 0 {
        (s, 0)
    } else {
        let (s1, v) = rd_extra(data, s, tab, (n - 1) as nat);
        let (s2, b) = rd_bool(data, s1, tab[n - 1] as int);
        (
            s2,
            2 * v + if b {
                1int
            } else {
                0int
            },
        )
    }
}

/// `Pcat3` to `Pcat6`.
pub open spec fn pcat3() -> Seq<u8> {
    seq![173u8, 148, 140]
}

pub open spec fn pcat4() -> Seq<u8> {
    seq![176u8, 155, 140, 135]
}

pub open spec fn pcat5() -> Seq<u8> {
    seq![180u8, 157, 141, 134, 130]
}

pub open spec fn pcat6() -> Seq<u8> {
    seq![254u8, 254, 243, 230, 196, 177, 153, 140, 133, 130, 129]
}

pub open spec fn b2i(b: bool) -> int {
    if b {
        1
    } else {
        0
    }
}

/// Section 13.2: `coeff_tree` below `DCT_1`, with the tree probabilities
/// at `p`: the tokens `DCT_2` to `dct_cat6`, as the magnitude they stand
/// for (the category's base plus its extra bits).
pub open spec fn large_value(data: Seq<u8>, s: BoolState, probs: Seq<int>, p: int) -> (BoolState, int) {
    let (s3, b3) = rd_bool(data, s, probs[p + 3]);
    if !b3 {
        let (s4, b4) = rd_bool(data, s3, probs[p + 4]);
        if !b4 {
            (s4, 2)
        } else {
            let (s5, b5) = rd_bool(data, s4, probs[p + 5]);
            (s5, 3 + b2i(b5))
        }
    } else {
        let (s6, b6) = rd_bool(data, s3, probs[p + 6]);
        if !b6 {
            let (s7, b7) = rd_bool(data, s6, probs[p + 7]);
            if !b7 {
                let (s8, e) = rd_bool(data, s7, 159);
                (s8, 5 + b2i(e))
            } else {
                let (s8, e1) = rd_bool(data, s7, 165);
                let (s9, e0) = rd_bool(data, s8, 145);
                (s9, 7 + 2 * b2i(e1) + b2i(e0))
            }
        } else {
            let (s8, b8) = rd_bool(data, s6, probs[p + 8]);
            let (s9, b9) = rd_bool(data, s8, probs[p + 9 + b2i(b8)]);
            if !b8 && !b9 {
                let (sx, v) = rd_extra(data, s9, pcat3(), 3);
                (sx, v + 11)
            } else if !b8 {
                let (sx, v) = rd_extra(data, s9, pcat4(), 4);
                (sx, v + 19)
            } else if !b9 {
                let (sx, v) = rd_extra(data, s9, pcat5(), 5);
                (sx, v + 35)
            } else {
                let (sx, v) = rd_extra(data, s9, pcat6(), 11);
                (sx, v + 67)
            }
        }
    }
}

/// Section 13: the tokens of one block of type `t` from position `n`, in
/// context `ctx`, dequantized (section 14.1) by `dq_dc` at position 0 and
/// `dq_ac` elsewhere and stored into `out` at their zigzag places. Returns
/// the state, the block, and the position at which the block ended (the
/// one holding `dct_eob`, or 16).
///
/// `check_eob` is false right after a `DCT_0`, which `dct_eob` cannot
/// follow: the tree is then entered below its root.
pub open spec fn block_tokens(
    data: Seq<u8>,
    s: BoolState,
    probs: Seq<int>,
    t: int,
    n: int,
    ctx: int,
    check_eob: bool,
    dq_dc: int,
    dq_ac: int,
    out: Seq<int>,
) -> (BoolState, Seq<int>, int)
    decreases 16 - n,
{
    if n >= 16 {
        (s, out, 16)
    } else {
        let p = token_pidx(t, n, ctx);
        if check_eob && !bool_bit(s, probs[p]) {
            (bool_next(data, s, probs[p]), out, n)
        } else {
            let s1 = if check_eob {
                bool_next(data, s, probs[p])
            } else {
                s
            };
            let (s2, nonzero) = rd_bool(data, s1, probs[p + 1]);
            if !nonzero {
                block_tokens(data, s2, probs, t, n + 1, 0, false, dq_dc, dq_ac, out)
            } else {
                let (s3, big) = rd_bool(data, s2, probs[p + 2]);
                let (s4, v) = if big {
                    large_value(data, s3, probs, p)
                } else {
                    (s3, 1)
                };
                let (s5, neg) = rd_bool(data, s4, 128);
                let d = if n > 0 {
                    dq_ac
                } else {
                    dq_dc
                };
                let c = wrap16s(
                    (if neg {
                        -v
                    } else {
                        v
                    }) * d,
                );
                block_tokens(
                    data,
                    s5,
                    probs,
                    t,
                    n + 1,
                    if big {
                        2
                    } else {
                        1
                    },
                    true,
                    dq_dc,
                    dq_ac,
                    out.update(zigzag(n), c),
                )
            }
        }
    }
}

/// `block_tokens`, one step unfolded (for proofs that keep it hidden).
pub proof fn lemma_block_tokens_unfold(
    data: Seq<u8>,
    s: BoolState,
    probs: Seq<int>,
    t: int,
    n: int,
    ctx: int,
    check_eob: bool,
    dq_dc: int,
    dq_ac: int,
    out: Seq<int>,
)
    ensures
        block_tokens(data, s, probs, t, n, ctx, check_eob, dq_dc, dq_ac, out) == ({
    if n >= 16 {
        (s, out, 16)
    } else {
        let p = token_pidx(t, n, ctx);
        if check_eob && !bool_bit(s, probs[p]) {
            (bool_next(data, s, probs[p]), out, n)
        } else {
            let s1 = if check_eob {
                bool_next(data, s, probs[p])
            } else {
                s
            };
            let (s2, nonzero) = rd_bool(data, s1, probs[p + 1]);
            if !nonzero {
                block_tokens(data, s2, probs, t, n + 1, 0, false, dq_dc, dq_ac, out)
            } else {
                let (s3, big) = rd_bool(data, s2, probs[p + 2]);
                let (s4, v) = if big {
                    large_value(data, s3, probs, p)
                } else {
                    (s3, 1)
                };
                let (s5, neg) = rd_bool(data, s4, 128);
                let d = if n > 0 {
                    dq_ac
                } else {
                    dq_dc
                };
                let c = wrap16s(
                    (if neg {
                        -v
                    } else {
                        v
                    }) * d,
                );
                block_tokens(
                    data,
                    s5,
                    probs,
                    t,
                    n + 1,
                    if big {
                        2
                    } else {
                        1
                    },
                    true,
                    dq_dc,
                    dq_ac,
                    out.update(zigzag(n), c),
                )
            }
        }
    }
}),
{
}


// ---------------------------------------------------------------------
// Sections 13.3 and 14.3: the residual data of one macroblock
// ---------------------------------------------------------------------
/// Section 14.3: the inverse Walsh-Hadamard transform of the Y2 block,
/// `vp8_short_inv_walsh4x4_c`: a pass down the columns, then a pass along
/// the rows with the rounding shift. Output `k` is the DC coefficient of
/// luma subblock `k`.
pub open spec fn iwht_col(ip: Seq<int>, i: int) -> (int, int, int, int) {
    let a1 = ip[i] + ip[12 + i];
    let b1 = ip[4 + i] + ip[8 + i];
    let c1 = ip[4 + i] - ip[8 + i];
    let d1 = ip[i] - ip[12 + i];
    (a1 + b1, c1 + d1, a1 - b1, d1 - c1)
}

/// The first pass's output, as the 4x4 block it is stored in.
pub open spec fn iwht_mid(ip: Seq<int>) -> Seq<int> {
    Seq::new(
        16,
        |j: int|
            {
                let c = iwht_col(ip, j % 4);
                if j / 4 == 0 {
                    c.0
                } else if j / 4 == 1 {
                    c.1
                } else if j / 4 == 2 {
                    c.2
                } else {
                    c.3
                }
            },
    )
}

pub open spec fn iwht_row(m: Seq<int>, r: int) -> (int, int, int, int) {
    let a1 = m[4 * r] + m[4 * r + 3];
    let b1 = m[4 * r + 1] + m[4 * r + 2];
    let c1 = m[4 * r + 1] - m[4 * r + 2];
    let d1 = m[4 * r] - m[4 * r + 3];
    ((a1 + b1 + 3) / 8, (c1 + d1 + 3) / 8, (a1 - b1 + 3) / 8, (d1 - c1 + 3) / 8)
}

pub open spec fn iwht(ip: Seq<int>) -> Seq<int> {
    let m = iwht_mid(ip);
    Seq::new(
        16,
        |k: int|
            {
                let r = iwht_row(m, k / 4);
                wrap16s(
                    if k % 4 == 0 {
                        r.0
                    } else if k % 4 == 1 {
                        r.1
                    } else if k % 4 == 2 {
                        r.2
                    } else {
                        r.3
                    },
                )
            },
    )
}

/// The coefficients of a macroblock while its tokens are read (384 of
/// them: sixteen luma blocks, four U, four V, sixteen coefficients each),
/// with the "has nonzero coefficients" contexts of section 13.3 for the
/// blocks above and to the left. A context holds nine flags: luma columns
/// (or rows) 0 to 3, U 4 and 5, V 6 and 7, and Y2 at 8.
pub struct ResState {
    pub s: BoolState,
    pub coeffs: Seq<int>,
    pub top: Seq<bool>,
    pub left: Seq<bool>,
}

/// `out` with the sixteen entries from `at` replaced by `blk`.
pub open spec fn splice16(out: Seq<int>, at: int, blk: Seq<int>) -> Seq<int> {
    Seq::new(
        out.len(),
        |i: int|
            if at <= i < at + 16 {
                blk[i - at]
            } else {
                out[i]
            },
    )
}

/// Block `k` of a plane that is `w` blocks wide (4 for luma, 2 for
/// chroma), whose first block is number `base` of the macroblock and whose
/// context flags start at `off`: its tokens are read in the context given
/// by the flags to its left and above, and it sets both.
pub open spec fn plane_block(
    data: Seq<u8>,
    st: ResState,
    probs: Seq<int>,
    t: int,
    first: int,
    dq_dc: int,
    dq_ac: int,
    base: int,
    off: int,
    w: int,
    k: int,
) -> ResState {
    let y = k / w;
    let x = k % w;
    let ctx = b2i(st.left[off + y]) + b2i(st.top[off + x]);
    let at = 16 * (base + k);
    let r = block_tokens(data, st.s, probs, t, first, ctx, true, dq_dc, dq_ac, st.coeffs.subrange(at, at + 16));
    let f = r.2 > first;
    ResState {
        s: r.0,
        coeffs: splice16(st.coeffs, at, r.1),
        top: st.top.update(off + x, f),
        left: st.left.update(off + y, f),
    }
}

/// The first `n` blocks of a plane, in raster order.
pub open spec fn plane_blocks(
    data: Seq<u8>,
    st: ResState,
    probs: Seq<int>,
    t: int,
    first: int,
    dq_dc: int,
    dq_ac: int,
    base: int,
    off: int,
    w: int,
    n: nat,
) -> ResState
    decreases n,
{
    if n == 0 {
        st
    } else {
        plane_block(
            data,
            plane_blocks(data, st, probs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat),
            probs,
            t,
            first,
            dq_dc,
            dq_ac,
            base,
            off,
            w,
            n - 1,
        )
    }
}

/// The Y2 block of a macroblock that is not `B_PRED` (block type 1): its
/// inverse WHT gives the DC coefficient of each luma block.
pub open spec fn y2_block(data: Seq<u8>, st: ResState, probs: Seq<int>, dq_dc: int, dq_ac: int) -> ResState {
    let ctx = b2i(st.left[8]) + b2i(st.top[8]);
    let r = block_tokens(data, st.s, probs, 1, 0, ctx, true, dq_dc, dq_ac, Seq::new(16, |i: int| 0int));
    let dc = iwht(r.1);
    let f = r.2 > 0;
    ResState {
        s: r.0,
        coeffs: Seq::new(
            st.coeffs.len(),
            |i: int|
                if 0 <= i < 256 && i % 16 == 0 {
                    dc[i / 16]
                } else {
                    st.coeffs[i]
                },
        ),
        top: st.top.update(8, f),
        left: st.left.update(8, f),
    }
}

/// Section 13 (`residual_data()` of section 19.3): the coefficients of a
/// macroblock that is not skipped, from the token partition at state `s`.
/// `q` holds the segment's factors as `seg_quant` returns them. With a Y2
/// block the luma blocks are type 0 and start at position 1; without one
/// they are type 3. Chroma blocks are type 2.
pub open spec fn mb_residuals(
    data: Seq<u8>,
    s: BoolState,
    probs: Seq<int>,
    q: (int, int, int, int, int, int),
    is_i4x4: bool,
    top: Seq<bool>,
    left: Seq<bool>,
) -> ResState {
    let st0 = ResState { s, coeffs: Seq::new(384, |i: int| 0int), top, left };
    let st1 = if is_i4x4 {
        st0
    } else {
        y2_block(data, st0, probs, q.2, q.3)
    };
    let (t, first) = if is_i4x4 {
        (3int, 0int)
    } else {
        (0int, 1int)
    };
    let sy = plane_blocks(data, st1, probs, t, first, q.0, q.1, 0, 0, 4, 16);
    let su = plane_blocks(data, sy, probs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    plane_blocks(data, su, probs, 2, 0, q.4, q.5, 20, 6, 2, 4)
}

/// A block whose tokens run past its second position has a nonzero
/// coefficient: it is not zeros spelled out as tokens.
pub open spec fn blk_solid(c: Seq<int>, nz: int) -> bool {
    nz > 1 ==> !zero_blk(c)
}

/// `blk_solid` for the first `n` blocks of a plane.
pub open spec fn plane_solid(
    data: Seq<u8>,
    st: ResState,
    probs: Seq<int>,
    t: int,
    first: int,
    dq_dc: int,
    dq_ac: int,
    base: int,
    off: int,
    w: int,
    n: nat,
) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        let k = (n - 1) as int;
        let e = plane_blocks(data, st, probs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat);
        let ctx = b2i(e.left[off + k / w]) + b2i(e.top[off + k % w]);
        let at = 16 * (base + k);
        let r = block_tokens(data, e.s, probs, t, first, ctx, true, dq_dc, dq_ac, e.coeffs.subrange(at, at + 16));
        plane_solid(data, st, probs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat) && blk_solid(r.1, r.2)
    }
}

/// `blk_solid` for the 24 blocks of a macroblock that is not skipped (the
/// arguments are `mb_residuals`'). The loop filter's choice of inner edges
/// follows the tokens in the reference decoder and the coefficients in
/// libwebp; the two agree on macroblocks that satisfy this.
pub open spec fn mb_solid(
    data: Seq<u8>,
    s: BoolState,
    probs: Seq<int>,
    q: (int, int, int, int, int, int),
    is_i4x4: bool,
    top: Seq<bool>,
    left: Seq<bool>,
) -> bool {
    let st0 = ResState { s, coeffs: Seq::new(384, |i: int| 0int), top, left };
    let st1 = if is_i4x4 {
        st0
    } else {
        y2_block(data, st0, probs, q.2, q.3)
    };
    let (t, first) = if is_i4x4 {
        (3int, 0int)
    } else {
        (0int, 1int)
    };
    let sy = plane_blocks(data, st1, probs, t, first, q.0, q.1, 0, 0, 4, 16);
    let su = plane_blocks(data, sy, probs, 2, 0, q.4, q.5, 16, 4, 2, 4);
    &&& plane_solid(data, st1, probs, t, first, q.0, q.1, 0, 0, 4, 16)
    &&& plane_solid(data, sy, probs, 2, 0, q.4, q.5, 16, 4, 2, 4)
    &&& plane_solid(data, su, probs, 2, 0, q.4, q.5, 20, 6, 2, 4)
}

/// `mb_solid` for a macroblock as `mb_tokens` reads it.
pub open spec fn tok_solid(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    m: MbModeSpec,
    top: Seq<bool>,
    left: Seq<bool>,
) -> bool {
    (fh.mb_no_coeff_skip && m.skip) || mb_solid(data, s, fh.probs, seg_quant(fh, m.segment), m.is_i4x4, top, left)
}

/// Some coefficient is not zero.
pub open spec fn any_nz(c: Seq<int>) -> bool {
    exists|j: int| 0 <= j < c.len() && #[trigger] c[j] != 0
}

// ---------------------------------------------------------------------
// Section 14.4: the inverse DCT
// ---------------------------------------------------------------------
/// `x + ((x * cospi8sqrt2minus1) >> 16)`: `x` times `sqrt(2) * cos(pi/8)`.
pub open spec fn idct_mul1(x: int) -> int {
    x + (x * 20091) / 65536
}

/// `(x * sinpi8sqrt2) >> 16`: `x` times `sqrt(2) * sin(pi/8)`.
pub open spec fn idct_mul2(x: int) -> int {
    (x * 35468) / 65536
}

/// One pass of `vp8_short_idct4x4llm_c` over four values.
pub open spec fn idct_1d(x0: int, x1: int, x2: int, x3: int) -> (int, int, int, int) {
    let a = x0 + x2;
    let b = x0 - x2;
    let c = idct_mul2(x1) - idct_mul1(x3);
    let d = idct_mul1(x1) + idct_mul2(x3);
    (a + d, b + c, b - c, a - d)
}

pub open spec fn pick4(t: (int, int, int, int), k: int) -> int {
    if k == 0 {
        t.0
    } else if k == 1 {
        t.1
    } else if k == 2 {
        t.2
    } else {
        t.3
    }
}

/// The first (vertical) pass: output `y` of column `col` of the block
/// `c`, which holds its coefficients in raster order.
pub open spec fn idct_v(c: Seq<int>, col: int, y: int) -> int {
    pick4(idct_1d(c[col], c[4 + col], c[8 + col], c[12 + col]), y)
}

/// The second (horizontal) pass on row `y`, with its rounding term,
/// before the final shift.
pub open spec fn idct_pre(c: Seq<int>, y: int, x: int) -> int {
    pick4(idct_1d(idct_v(c, 0, y) + 4, idct_v(c, 1, y), idct_v(c, 2, y), idct_v(c, 3, y)), x)
}

/// The residual of a 4x4 block of dequantized coefficients, in raster
/// order. The arithmetic is exact here. The reference decoder keeps the
/// intermediate values in 16 bits; see `idct_tame`.
pub open spec fn idct(c: Seq<int>) -> Seq<int> {
    Seq::new(16, |k: int| idct_pre(c, k / 4, k % 4) / 8)
}

pub open spec fn fits16(x: int) -> bool {
    -0x8000 <= x <= 0x7fff
}

/// The intermediate values of a block's inverse DCT fit in 16 bits, as
/// they do for the coefficients of any real image. Decoders that work in
/// 16 bits (libvpx, and libwebp's SIMD code) agree with `idct` on such
/// blocks, and differ from it and from each other on the rest.
pub open spec fn idct_tame(c: Seq<int>) -> bool {
    &&& forall|x: int, y: int| 0 <= x < 4 && 0 <= y < 4 ==> fits16(#[trigger] idct_v(c, x, y))
    &&& forall|y: int, x: int| 0 <= x < 4 && 0 <= y < 4 ==> fits16(#[trigger] idct_pre(c, y, x))
}

/// One pass grows its inputs by less than a factor of four.
pub proof fn lemma_idct_1d_bound(x0: int, x1: int, x2: int, x3: int, b: int)
    requires
        b >= 128,
        -b <= x0 <= b,
        -b <= x1 <= b,
        -b <= x2 <= b,
        -b <= x3 <= b,
    ensures
        ({
            let r = idct_1d(x0, x1, x2, x3);
            let m = 4 * b - b / 8;
            -m <= r.0 <= m && -m <= r.1 <= m && -m <= r.2 <= m && -m <= r.3 <= m
        }),
{
    let p = (b * 20091) / 65536;
    let q = (b * 35468) / 65536;
    assert(-p - 1 <= (x1 * 20091) / 65536 <= p);
    assert(-p - 1 <= (x3 * 20091) / 65536 <= p);
    assert(-q - 1 <= (x1 * 35468) / 65536 <= q);
    assert(-q - 1 <= (x3 * 35468) / 65536 <= q);
}

/// Coefficients below 2048 in size, far more than an image's can be, keep
/// the inverse DCT inside 16 bits.
pub proof fn lemma_idct_small(c: Seq<int>)
    requires
        c.len() == 16,
        forall|k: int| 0 <= k < 16 ==> -2047 <= #[trigger] c[k] <= 2047,
    ensures
        idct_tame(c),
{
    assert forall|x: int, y: int| 0 <= x < 4 && 0 <= y < 4 implies -7933 <= #[trigger] idct_v(c, x, y) <= 7933 by {
        lemma_idct_1d_bound(c[x], c[4 + x], c[8 + x], c[12 + x], 2047);
    }
    assert forall|y: int, x: int| 0 <= x < 4 && 0 <= y < 4 implies fits16(#[trigger] idct_pre(c, y, x)) by {
        assert(-7933 <= idct_v(c, 0, y) <= 7933);
        assert(-7933 <= idct_v(c, 1, y) <= 7933);
        assert(-7933 <= idct_v(c, 2, y) <= 7933);
        assert(-7933 <= idct_v(c, 3, y) <= 7933);
        lemma_idct_1d_bound(idct_v(c, 0, y) + 4, idct_v(c, 1, y), idct_v(c, 2, y), idct_v(c, 3, y), 7937);
    }
}

// ---------------------------------------------------------------------
// Sections 9.5, 9.11 and 13: the coefficients of a whole frame
// ---------------------------------------------------------------------
/// The coefficients of a macroblock with modes `m`. One flagged as skipped
/// (section 9.11) has none and reads nothing; it clears the contexts of
/// its blocks, except the Y2 one when it has no Y2 block.
pub open spec fn mb_tokens(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    m: MbModeSpec,
    top: Seq<bool>,
    left: Seq<bool>,
) -> ResState {
    if fh.mb_no_coeff_skip && m.skip {
        ResState {
            s,
            coeffs: Seq::new(384, |i: int| 0int),
            top: Seq::new(9, |i: int| i == 8 && m.is_i4x4 && top[8]),
            left: Seq::new(9, |i: int| i == 8 && m.is_i4x4 && left[8]),
        }
    } else {
        mb_residuals(data, s, fh.probs, seg_quant(fh, m.segment), m.is_i4x4, top, left)
    }
}

/// The coefficients of the first `n` macroblocks of a row, with the
/// contexts they leave: `tops` holds the nine flags of each macroblock
/// column, and the left context starts each row clear.
pub struct RowTokens {
    pub s: BoolState,
    pub tops: Seq<Seq<bool>>,
    pub left: Seq<bool>,
    pub mbs: Seq<Seq<int>>,
}

pub open spec fn row_tokens(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    tops: Seq<Seq<bool>>,
    n: nat,
) -> RowTokens
    decreases n,
{
    if n == 0 {
        RowTokens { s, tops, left: Seq::new(9, |i: int| false), mbs: Seq::empty() }
    } else {
        let k = (n - 1) as int;
        let r = row_tokens(data, s, fh, modes, tops, (n - 1) as nat);
        let o = mb_tokens(data, r.s, fh, modes[k], r.tops[k], r.left);
        RowTokens { s: o.s, tops: r.tops.update(k, o.top), left: o.left, mbs: r.mbs.push(o.coeffs) }
    }
}

/// Section 9.5: token partition `p` of a file whose partition size table
/// is at `pstart` and has `last` entries (the last partition runs to the
/// end of the file).
pub open spec fn tok_part(file: Seq<u8>, pstart: int, last: int, p: int) -> Seq<u8> {
    file.subrange(
        part_begin(file, pstart, last, p as nat),
        if p < last {
            part_begin(file, pstart, last, (p + 1) as nat)
        } else {
            file.len() as int
        },
    )
}

pub open spec fn num_parts(fh: FrameHeader) -> int {
    if fh.log2_parts == 0 {
        1
    } else if fh.log2_parts == 1 {
        2
    } else if fh.log2_parts == 2 {
        4
    } else {
        8
    }
}

/// The state of every token partition and the contexts after `rows` rows
/// of `mb_w` macroblocks. Row `y` is read from partition `y mod n`, with
/// the modes the first partition (`first`, from state `gh` after the frame
/// header) gives that row.
pub struct TokRows {
    pub parts: Seq<BoolState>,
    pub tops: Seq<Seq<bool>>,
}

pub open spec fn tok_rows(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    rows: nat,
) -> TokRows
    decreases rows,
{
    let np = num_parts(fh);
    if rows == 0 {
        TokRows {
            parts: Seq::new(np as nat, |p: int| bool_init(tok_part(file, pstart, np - 1, p))),
            tops: Seq::new(mb_w, |j: int| Seq::new(9, |i: int| false)),
        }
    } else {
        let y = (rows - 1) as int;
        let r = tok_rows(file, pstart, first, gh, fh, mb_w, (rows - 1) as nat);
        let p = y % np;
        let o = row_tokens(
            tok_part(file, pstart, np - 1, p),
            r.parts[p],
            fh,
            mode_rows(first, gh, fh, mb_w, rows).mbs,
            r.tops,
            mb_w,
        );
        TokRows { parts: r.parts.update(p, o.s), tops: o.tops }
    }
}

pub proof fn lemma_row_tokens_zero(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    tops: Seq<Seq<bool>>,
)
    ensures
        row_tokens(data, s, fh, modes, tops, 0) == (RowTokens {
            s,
            tops,
            left: Seq::new(9, |i: int| false),
            mbs: Seq::empty(),
        }),
{
}

pub proof fn lemma_row_tokens_step(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    tops: Seq<Seq<bool>>,
    k: nat,
)
    ensures
        ({
            let r = row_tokens(data, s, fh, modes, tops, k);
            let o = mb_tokens(data, r.s, fh, modes[k as int], r.tops[k as int], r.left);
            row_tokens(data, s, fh, modes, tops, k + 1) == (RowTokens {
                s: o.s,
                tops: r.tops.update(k as int, o.top),
                left: o.left,
                mbs: r.mbs.push(o.coeffs),
            })
        }),
{
    assert((k + 1 - 1) as nat == k);
}

pub proof fn lemma_tok_rows_zero(file: Seq<u8>, pstart: int, first: Seq<u8>, gh: BoolState, fh: FrameHeader, mb_w: nat)
    ensures
        ({
            let t = tok_rows(file, pstart, first, gh, fh, mb_w, 0);
            &&& forall|p: int|
                0 <= p < num_parts(fh) ==> #[trigger] t.parts[p] == bool_init(
                    tok_part(file, pstart, num_parts(fh) - 1, p),
                )
            &&& forall|j: int| 0 <= j < mb_w ==> #[trigger] t.tops[j] == Seq::new(9, |i: int| false)
        }),
{
}

pub proof fn lemma_tok_rows_step(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    y: nat,
)
    ensures
        ({
            let np = num_parts(fh);
            let r = tok_rows(file, pstart, first, gh, fh, mb_w, y);
            let p = y as int % np;
            let o = row_tokens(
                tok_part(file, pstart, np - 1, p),
                r.parts[p],
                fh,
                mode_rows(first, gh, fh, mb_w, y + 1).mbs,
                r.tops,
                mb_w,
            );
            tok_rows(file, pstart, first, gh, fh, mb_w, y + 1) == (TokRows { parts: r.parts.update(p, o.s), tops: o.tops })
        }),
{
    assert((y + 1 - 1) as nat == y);
}

pub proof fn lemma_row_tokens_shape(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    tops: Seq<Seq<bool>>,
    n: nat,
)
    ensures
        row_tokens(data, s, fh, modes, tops, n).tops.len() == tops.len(),
        row_tokens(data, s, fh, modes, tops, n).mbs.len() == n,
    decreases n,
{
    if n > 0 {
        lemma_row_tokens_shape(data, s, fh, modes, tops, (n - 1) as nat);
    }
}

pub proof fn lemma_tok_rows_shape(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    rows: nat,
)
    ensures
        tok_rows(file, pstart, first, gh, fh, mb_w, rows).parts.len() == num_parts(fh),
        tok_rows(file, pstart, first, gh, fh, mb_w, rows).tops.len() == mb_w,
    decreases rows,
{
    if rows > 0 {
        lemma_tok_rows_shape(file, pstart, first, gh, fh, mb_w, (rows - 1) as nat);
        let np = num_parts(fh);
        let r = tok_rows(file, pstart, first, gh, fh, mb_w, (rows - 1) as nat);
        let p = ((rows - 1) as int) % np;
        lemma_row_tokens_shape(
            tok_part(file, pstart, np - 1, p),
            r.parts[p],
            fh,
            mode_rows(first, gh, fh, mb_w, rows).mbs,
            r.tops,
            mb_w,
        );
    }
}

// ---------------------------------------------------------------------
// Section 15: the loop filter's kernels
// ---------------------------------------------------------------------
//
// The filters work on the eight pixels across an edge, four on each side:
// `p3 p2 p1 p0 | q0 q1 q2 q3`. Pixels are the integers 0..255 here; the
// RFC's code works on them as signed bytes (`u2s(x) = x - 128`), which
// changes no difference of two pixels, so only the final writes mention
// the offset (`lf_adj`).
//
// Where the RFC's text and libwebp (`src/dsp/dec.c`) might be read
// differently, the definitions follow libwebp, and say so.
/// The RFC's `c()`: a value clamped to a signed byte.
pub open spec fn lf_c(v: int) -> int {
    if v < -128 {
        -128
    } else if v > 127 {
        127
    } else {
        v
    }
}

/// `s2u(u2s(x) + d)`: the pixel `x` adjusted by `d`, with the signed-byte
/// clamp. (The same as clamping `x + d` to 0..255, libwebp's `clip_8b`.)
pub open spec fn lf_adj(x: int, d: int) -> int {
    lf_c(x - 128 + d) + 128
}

pub open spec fn lf_abs(v: int) -> int {
    if v < 0 {
        -v
    } else {
        v
    }
}

/// The eight pixels across an edge.
pub struct Edge8 {
    pub p3: int,
    pub p2: int,
    pub p1: int,
    pub p0: int,
    pub q0: int,
    pub q1: int,
    pub q2: int,
    pub q3: int,
}

/// The filter value of `common_adjust` (section 15.2), before rounding:
/// `c((use_outer_taps ? c(P1 - Q1) : 0) + 3 * (Q0 - P0))`.
pub open spec fn lf_w(outer: bool, x: Edge8) -> int {
    lf_c((if outer { lf_c(x.p1 - x.q1) } else { 0 }) + 3 * (x.q0 - x.p0))
}

/// The amount `common_adjust` takes from `q0` (its return value):
/// `c(a + 4) >> 3`. The shifts are arithmetic (floors).
pub open spec fn lf_a(outer: bool, x: Edge8) -> int {
    lf_c(lf_w(outer, x) + 4) / 8
}

/// The amount `common_adjust` adds to `p0`: `c(a + 3) >> 3`.
pub open spec fn lf_b(outer: bool, x: Edge8) -> int {
    lf_c(lf_w(outer, x) + 3) / 8
}

/// `common_adjust`: the two pixels next to the edge move toward each other.
pub open spec fn lf_common(outer: bool, x: Edge8) -> Edge8 {
    Edge8 { p0: lf_adj(x.p0, lf_b(outer, x)), q0: lf_adj(x.q0, -lf_a(outer, x)), ..x }
}

/// `hev`: high edge variance (section 15.3).
pub open spec fn lf_hev(x: Edge8, thresh: int) -> bool {
    lf_abs(x.p1 - x.p0) > thresh || lf_abs(x.q1 - x.q0) > thresh
}

/// The simple filter's test against the edge limit `e` (section 15.2):
/// `|p0 - q0| * 2 + |p1 - q1| / 2 <= e`.
///
/// This is libwebp's reading, and libvpx's. libwebp tests
/// `4 * |p0 - q0| + |p1 - q1| <= 2 * e + 1` (`NeedsFilter_C`, called with
/// `thresh2 = 2 * thresh + 1`), which is the same thing; the RFC's own C
/// text writes the sum with a shift whose precedence can be read
/// otherwise.
pub open spec fn lf_simple_yes(x: Edge8, e: int) -> bool {
    lf_abs(x.p0 - x.q0) * 2 + lf_abs(x.p1 - x.q1) / 2 <= e
}

/// The normal filter's test (`filter_yes`, section 15.3): the simple
/// test, and every neighbouring difference within the interior limit `i`.
pub open spec fn lf_normal_yes(x: Edge8, e: int, i: int) -> bool {
    &&& lf_simple_yes(x, e)
    &&& lf_abs(x.p3 - x.p2) <= i
    &&& lf_abs(x.p2 - x.p1) <= i
    &&& lf_abs(x.p1 - x.p0) <= i
    &&& lf_abs(x.q3 - x.q2) <= i
    &&& lf_abs(x.q2 - x.q1) <= i
    &&& lf_abs(x.q1 - x.q0) <= i
}

/// The simple filter on one edge position (`simple_segment`).
pub open spec fn lf_simple(x: Edge8, e: int) -> Edge8 {
    if lf_simple_yes(x, e) {
        lf_common(true, x)
    } else {
        x
    }
}

/// The normal filter on a subblock edge (`subblock_filter`): with high
/// edge variance the simple adjustment, and otherwise that without the
/// outer taps, and half of it (rounded) on the next pixels out.
pub open spec fn lf_subblock(x: Edge8, e: int, i: int, h: int) -> Edge8 {
    if !lf_normal_yes(x, e, i) {
        x
    } else if lf_hev(x, h) {
        lf_common(true, x)
    } else {
        let a = (lf_a(false, x) + 1) / 2;
        Edge8 { p1: lf_adj(x.p1, a), q1: lf_adj(x.q1, -a), ..lf_common(false, x) }
    }
}

/// The normal filter on a macroblock edge (`MBfilter`): with high edge
/// variance the simple adjustment, and otherwise 27/128, 18/128 and
/// 9/128 of the filter value on the three pixels each side.
pub open spec fn lf_mbedge(x: Edge8, e: int, i: int, h: int) -> Edge8 {
    if !lf_normal_yes(x, e, i) {
        x
    } else if lf_hev(x, h) {
        lf_common(true, x)
    } else {
        let w = lf_w(true, x);
        let a0 = lf_c((27 * w + 63) / 128);
        let a1 = lf_c((18 * w + 63) / 128);
        let a2 = lf_c((9 * w + 63) / 128);
        Edge8 {
            p3: x.p3,
            p2: lf_adj(x.p2, a2),
            p1: lf_adj(x.p1, a1),
            p0: lf_adj(x.p0, a0),
            q0: lf_adj(x.q0, -a0),
            q1: lf_adj(x.q1, -a1),
            q2: lf_adj(x.q2, -a2),
            q3: x.q3,
        }
    }
}

/// One edge position filtered: by the simple filter (`simple`), or by the
/// normal filter for a subblock edge (`inner`) or a macroblock edge, with
/// edge limit `e`, interior limit `i` and hev threshold `h`.
pub open spec fn lf_kernel(x: Edge8, simple: bool, inner: bool, e: int, i: int, h: int) -> Edge8 {
    if simple {
        lf_simple(x, e)
    } else if inner {
        lf_subblock(x, e, i, h)
    } else {
        lf_mbedge(x, e, i, h)
    }
}

/// The eight pixels across the edge at `p` in a plane: `step` apart, the
/// edge between `p - step` and `p`.
pub open spec fn lf_lane(b: Seq<u8>, p: int, step: int) -> Edge8 {
    Edge8 {
        p3: b[p - 4 * step] as int,
        p2: b[p - 3 * step] as int,
        p1: b[p - 2 * step] as int,
        p0: b[p - step] as int,
        q0: b[p] as int,
        q1: b[p + step] as int,
        q2: b[p + 2 * step] as int,
        q3: b[p + 3 * step] as int,
    }
}

/// The plane with the pixels across the edge at `p` replaced by `y`'s
/// (`p3` and `q3` are never written).
pub open spec fn lf_put(b: Seq<u8>, p: int, step: int, y: Edge8) -> Seq<u8> {
    b.update(p - 3 * step, y.p2 as u8).update(p - 2 * step, y.p1 as u8).update(p - step, y.p0 as u8).update(
        p,
        y.q0 as u8,
    ).update(p + step, y.q1 as u8).update(p + 2 * step, y.q2 as u8)
}

/// The plane after filtering the one edge position at `p`.
pub open spec fn lf_filter(b: Seq<u8>, p: int, step: int, simple: bool, inner: bool, e: int, i: int, h: int) -> Seq<
    u8,
> {
    lf_put(b, p, step, lf_kernel(lf_lane(b, p, step), simple, inner, e, i, h))
}

/// The plane after filtering `n` positions along an edge, from `p` and
/// `vstride` apart, each across the edge in direction `hstride`, in order.
pub open spec fn lf_run(
    b: Seq<u8>,
    p: int,
    hstride: int,
    vstride: int,
    n: nat,
    simple: bool,
    inner: bool,
    e: int,
    i: int,
    h: int,
) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        b
    } else {
        lf_filter(
            lf_run(b, p, hstride, vstride, (n - 1) as nat, simple, inner, e, i, h),
            p + (n - 1) * vstride,
            hstride,
            simple,
            inner,
            e,
            i,
            h,
        )
    }
}

/// The plane after the inner edges `1..=n` of a macroblock at `d` are
/// filtered in order, each a run of `size` positions; edge `k` is `4 k`
/// pixels on in the direction `hstride` (`gap` is 1 for the edges between
/// columns, and the plane's stride for those between rows).
pub open spec fn lf_inner_edges(
    b: Seq<u8>,
    d: int,
    gap: int,
    hstride: int,
    vstride: int,
    n: nat,
    size: nat,
    simple: bool,
    e: int,
    i: int,
    h: int,
) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        b
    } else {
        lf_run(
            lf_inner_edges(b, d, gap, hstride, vstride, (n - 1) as nat, size, simple, e, i, h),
            d + 4 * n * gap,
            hstride,
            vstride,
            size,
            simple,
            true,
            e,
            i,
            h,
        )
    }
}

/// One plane after the loop filter of one macroblock, whose top left
/// pixel is at `d` in the plane of the given stride, `size` pixels wide
/// and high (16 in Y, 8 in U and V).
///
/// In the order of section 15: the left macroblock edge (unless the
/// macroblock is in the first column: `left`), the subblock edges between
/// columns, the top macroblock edge (unless in the first row), and the
/// subblock edges between rows; the subblock edges only if `inner` (the
/// macroblock has coefficients, or is predicted by subblocks).
///
/// `limit` is the subblock edge limit, `2 * level + interior_limit`; the
/// macroblock edges use `2 * (level + 2) + interior_limit`, which is
/// `limit + 4` (as libwebp writes it).
pub open spec fn lf_mb_plane(
    b: Seq<u8>,
    d: int,
    stride: int,
    size: nat,
    left: bool,
    top: bool,
    simple: bool,
    inner: bool,
    limit: int,
    i: int,
    h: int,
) -> Seq<u8> {
    let b1 = if left {
        lf_run(b, d, 1, stride, size, simple, false, limit + 4, i, h)
    } else {
        b
    };
    let b2 = if inner {
        lf_inner_edges(b1, d, 1, 1, stride, (size / 4 - 1) as nat, size, simple, limit, i, h)
    } else {
        b1
    };
    let b3 = if top {
        lf_run(b2, d, stride, 1, size, simple, false, limit + 4, i, h)
    } else {
        b2
    };
    if inner {
        lf_inner_edges(b3, d, stride, stride, 1, (size / 4 - 1) as nat, size, simple, limit, i, h)
    } else {
        b3
    }
}

/// The planes `(Y, U, V)` after the loop filter of macroblock
/// `(mb_x, mb_y)`, in planes of whole macroblocks `mb_w` across.
///
/// Nothing is filtered when the edge limit is 0 (the filter level is 0).
/// The simple filter works on Y only; it has no interior limit or hev
/// threshold (written as 0 here).
pub open spec fn lf_mb(
    y: Seq<u8>,
    u: Seq<u8>,
    v: Seq<u8>,
    mb_x: int,
    mb_y: int,
    mb_w: int,
    simple: bool,
    inner: bool,
    limit: int,
    i: int,
    h: int,
) -> (Seq<u8>, Seq<u8>, Seq<u8>) {
    let yd = 16 * mb_y * (16 * mb_w) + 16 * mb_x;
    let uvd = 8 * mb_y * (8 * mb_w) + 8 * mb_x;
    if limit == 0 {
        (y, u, v)
    } else if simple {
        (lf_mb_plane(y, yd, 16 * mb_w, 16, mb_x > 0, mb_y > 0, true, inner, limit, 0, 0), u, v)
    } else {
        (
            lf_mb_plane(y, yd, 16 * mb_w, 16, mb_x > 0, mb_y > 0, false, inner, limit, i, h),
            lf_mb_plane(u, uvd, 8 * mb_w, 8, mb_x > 0, mb_y > 0, false, inner, limit, i, h),
            lf_mb_plane(v, uvd, 8 * mb_w, 8, mb_x > 0, mb_y > 0, false, inner, limit, i, h),
        )
    }
}

// ---------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------
pub proof fn lemma_bits_bound(data: Seq<u8>, a: nat, n: nat)
    ensures
        stream_bits(data, a, n) < pow2(n),
    decreases n,
{
    lemma2_to64();
    if n > 0 {
        lemma_bits_bound(data, a, (n - 1) as nat);
        lemma_pow2_unfold(n);
        assert(stream_bit(data, a + (n - 1) as nat) <= 1);
    }
}

/// Bits concatenate.
pub proof fn lemma_bits_split(data: Seq<u8>, a: nat, m: nat, n: nat)
    ensures
        stream_bits(data, a, m + n) == stream_bits(data, a, m) * pow2(n) + stream_bits(data, a + m, n),
    decreases n,
{
    lemma2_to64();
    let x = stream_bits(data, a, m) as int;
    if n == 0 {
        assert(m + n == m);
        assert(stream_bits(data, a + m, 0) == 0);
        assert(x * 1 == x);
    } else {
        let n1 = (n - 1) as nat;
        lemma_bits_split(data, a, m, n1);
        lemma_pow2_unfold(n);
        assert((m + n - 1) as nat == m + n1);
        assert(a + (m + n - 1) as nat == a + m + n1);
        let p = pow2(n1) as int;
        assert(2 * (x * p) == x * (2 * p)) by (nonlinear_arith);
        assert(stream_bits(data, a, m + n) == 2 * stream_bits(data, a, m + n1) + stream_bit(data, a + m + n1));
        assert(stream_bits(data, a + m, n) == 2 * stream_bits(data, a + m, n1) + stream_bit(data, a + m + n1));
        assert(pow2(n) == 2 * p);
        assert(x * pow2(n) == x * (2 * p));
    }
}

/// A window of the stream, moved `k` bits along: the identity behind every
/// refill and every renormalization of the decoder.
pub proof fn lemma_window(data: Seq<u8>, v: int, l: nat, k: nat, m: nat)
    requires
        k <= m,
    ensures
        v * pow2(m) + stream_bits(data, l, m) == (v * pow2(k) + stream_bits(data, l, k)) * pow2((m - k) as nat)
            + stream_bits(data, l + k, (m - k) as nat),
{
    let d = (m - k) as nat;
    lemma_bits_split(data, l, k, d);
    lemma_pow2_adds(k, d);
    assert(k + d == m);
    let a = pow2(k) as int;
    let b = pow2(d) as int;
    let x = stream_bits(data, l, k) as int;
    assert(v * (a * b) + x * b == (v * a + x) * b) by (nonlinear_arith);
}

/// A whole byte of the stream is that byte.
pub proof fn lemma_byte(data: Seq<u8>, i: nat)
    requires
        i < data.len(),
    ensures
        stream_bits(data, 8 * i, 8) == data[i as int],
{
    lemma2_to64();
    let b = data[i as int];
    let a = 8 * i;
    assert forall|j: nat| j < 8 implies #[trigger] stream_bit(data, a + j) == (b as nat / pow2((7 - j) as nat)) % 2 by {
        assert((a + j) / 8 == i);
        assert((a + j) % 8 == j);
    }
    assert(stream_bit(data, a + 0) == (b as nat / 128) % 2);
    assert(stream_bit(data, a + 1) == (b as nat / 64) % 2);
    assert(stream_bit(data, a + 2) == (b as nat / 32) % 2);
    assert(stream_bit(data, a + 3) == (b as nat / 16) % 2);
    assert(stream_bit(data, a + 4) == (b as nat / 8) % 2);
    assert(stream_bit(data, a + 5) == (b as nat / 4) % 2);
    assert(stream_bit(data, a + 6) == (b as nat / 2) % 2);
    assert(stream_bit(data, a + 7) == (b as nat / 1) % 2);
    assert(stream_bits(data, a, 0) == 0);
    assert(stream_bits(data, a, 1) == 2 * stream_bits(data, a, 0) + stream_bit(data, a + 0));
    assert(stream_bits(data, a, 2) == 2 * stream_bits(data, a, 1) + stream_bit(data, a + 1));
    assert(stream_bits(data, a, 3) == 2 * stream_bits(data, a, 2) + stream_bit(data, a + 2));
    assert(stream_bits(data, a, 4) == 2 * stream_bits(data, a, 3) + stream_bit(data, a + 3));
    assert(stream_bits(data, a, 5) == 2 * stream_bits(data, a, 4) + stream_bit(data, a + 4));
    assert(stream_bits(data, a, 6) == 2 * stream_bits(data, a, 5) + stream_bit(data, a + 5));
    assert(stream_bits(data, a, 7) == 2 * stream_bits(data, a, 6) + stream_bit(data, a + 6));
    assert(stream_bits(data, a, 8) == 2 * stream_bits(data, a, 7) + stream_bit(data, a + 7));
    assert(b == 128 * ((b / 128) % 2) + 64 * ((b / 64) % 2) + 32 * ((b / 32) % 2) + 16 * ((b / 16) % 2) + 8 * ((b / 8)
        % 2) + 4 * ((b / 4) % 2) + 2 * ((b / 2) % 2) + (b % 2)) by (bit_vector);
}

/// `n` bytes from byte `i`, big-endian.
pub open spec fn be_bytes(data: Seq<u8>, i: nat, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        256 * be_bytes(data, i, (n - 1) as nat) + data[i + n - 1] as nat
    }
}

pub proof fn lemma_bytes(data: Seq<u8>, i: nat, n: nat)
    requires
        i + n <= data.len(),
    ensures
        stream_bits(data, 8 * i, 8 * n) == be_bytes(data, i, n),
    decreases n,
{
    lemma2_to64();
    if n > 0 {
        let n1 = (n - 1) as nat;
        lemma_bytes(data, i, n1);
        lemma_bits_split(data, 8 * i, 8 * n1, 8);
        lemma_byte(data, i + n1);
        assert(8 * n1 + 8 == 8 * n);
        assert(8 * i + 8 * n1 == 8 * (i + n1));
    }
}

/// The renormalization loop in closed form: it shifts by the `n` that
/// brings the range back into `[128, 255]`.
pub proof fn lemma_norm(data: Seq<u8>, s: BoolState, n: nat)
    requires
        1 <= s.range,
        128 <= s.range * pow2(n) <= 255,
    ensures
        bool_norm(data, s) == (BoolState {
            range: s.range * pow2(n),
            value: s.value * pow2(n) + stream_bits(data, s.pos, n),
            pos: s.pos + n,
        }),
    decreases n,
{
    lemma2_to64();
    if n == 0 {
        assert(stream_bits(data, s.pos, 0) == 0);
        assert(s.range * 1 == s.range && s.value * 1 == s.value);
        assert(s.pos + 0 == s.pos);
    } else {
        let n1 = (n - 1) as nat;
        lemma_pow2_unfold(n);
        let p = pow2(n1) as int;
        let r = s.range;
        let v = s.value;
        lemma_pow2_pos(n1);
        assert(r * (2 * p) >= 2 * r) by (nonlinear_arith)
            requires
                p >= 1,
                r >= 1,
        ;
        assert(r < 128);
        let b = stream_bit(data, s.pos) as int;
        let s1 = BoolState { range: 2 * r, value: 2 * v + b, pos: s.pos + 1 };
        assert((2 * r) * p == r * (2 * p)) by (nonlinear_arith);
        lemma_norm(data, s1, n1);
        lemma_bits_split(data, s.pos, 1, n1);
        assert(stream_bits(data, s.pos, 1) == b) by {
            assert(stream_bits(data, s.pos, 0) == 0);
            assert(stream_bits(data, s.pos, 1) == 2 * stream_bits(data, s.pos, 0) + stream_bit(
                data,
                s.pos + 0 as nat,
            ));
        }
        assert(1 + n1 == n);
        let t = stream_bits(data, s.pos + 1, n1) as int;
        assert((2 * v + b) * p + t == v * (2 * p) + (b * p + t)) by (nonlinear_arith);
        assert(bool_norm(data, s) == bool_norm(data, s1));
        assert(pow2(n) == 2 * p);
        assert(s.range * pow2(n) == r * (2 * p));
        assert(s.value * pow2(n) == v * (2 * p));
        assert(stream_bits(data, s.pos, n) == b * p + t);
        assert(s.pos + 1 + n1 == s.pos + n);
    }
}

/// The split point lies strictly inside the range.
pub proof fn lemma_split(range: int, prob: int)
    requires
        128 <= range <= 256,
        0 <= prob <= 255,
    ensures
        1 <= bool_split(range, prob) < range,
{
    let x = (range - 1) * prob;
    assert(0 <= x <= (range - 1) * 255) by (nonlinear_arith)
        requires
            x == (range - 1) * prob,
            range >= 1,
            0 <= prob <= 255,
    ;
}

/// A step keeps the code word inside the range, and leaves a range below
/// 255.
pub proof fn lemma_take_wf(s: BoolState, prob: int)
    requires
        bool_wf(s),
        0 <= prob <= 255,
    ensures
        1 <= bool_take(s, prob).range <= 254,
        0 <= bool_take(s, prob).value < bool_take(s, prob).range,
{
    lemma_split(s.range, prob);
}

pub proof fn lemma_rd_bmodes_shape(data: Seq<u8>, s: BoolState, top: Seq<int>, left: Seq<int>, n: nat)
    requires
        top.len() == 4,
        left.len() == 4,
        n <= 16,
    ensures
        rd_bmodes(data, s, top, left, n).modes.len() == n,
        rd_bmodes(data, s, top, left, n).top.len() == 4,
        rd_bmodes(data, s, top, left, n).left.len() == 4,
    decreases n,
{
    if n > 0 {
        lemma_rd_bmodes_shape(data, s, top, left, (n - 1) as nat);
    }
}

pub proof fn lemma_mb_modes_shape(data: Seq<u8>, s: BoolState, fh: FrameHeader, top: Seq<int>, left: Seq<int>)
    requires
        top.len() == 4,
        left.len() == 4,
    ensures
        mb_modes(data, s, fh, top, left).top.len() == 4,
        mb_modes(data, s, fh, top, left).left.len() == 4,
{
    let s3 = rd_bool(data, mb_skip(data, mb_segment(data, s, fh).0, fh).0, 145).0;
    lemma_rd_bmodes_shape(data, s3, top, left, 16);
}

pub proof fn lemma_row_modes_shape(data: Seq<u8>, s: BoolState, fh: FrameHeader, top: Seq<int>, n: nat)
    requires
        4 * n <= top.len(),
    ensures
        row_modes(data, s, fh, top, n).mbs.len() == n,
        row_modes(data, s, fh, top, n).top.len() == top.len(),
        row_modes(data, s, fh, top, n).left.len() == 4,
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as int;
        lemma_row_modes_shape(data, s, fh, top, (n - 1) as nat);
        let r = row_modes(data, s, fh, top, (n - 1) as nat);
        lemma_mb_modes_shape(data, r.s, fh, r.top.subrange(4 * k, 4 * k + 4), r.left);
    }
}

pub proof fn lemma_mode_rows_shape(data: Seq<u8>, s: BoolState, fh: FrameHeader, mb_w: nat, rows: nat)
    ensures
        mode_rows(data, s, fh, mb_w, rows).top.len() == 4 * mb_w,
    decreases rows,
{
    if rows > 0 {
        lemma_mode_rows_shape(data, s, fh, mb_w, (rows - 1) as nat);
        let r = mode_rows(data, s, fh, mb_w, (rows - 1) as nat);
        lemma_row_modes_shape(data, r.s, fh, r.top, mb_w);
    }
}

/// The inverse WHT of a block with only its first coefficient set gives
/// every luma block the same DC.
pub proof fn lemma_iwht_dc(ip: Seq<int>)
    requires
        ip.len() == 16,
        -0x8000 <= ip[0] <= 0x7fff,
        forall|j: int| 1 <= j < 16 ==> ip[j] == 0,
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] iwht(ip)[k] == (ip[0] + 3) / 8,
{
    let m = iwht_mid(ip);
    assert forall|j: int| 0 <= j < 16 implies #[trigger] m[j] == (if j % 4 == 0 {
        ip[0]
    } else {
        0
    }) by {
        let c = iwht_col(ip, j % 4);
        if j % 4 != 0 {
            assert(ip[j % 4] == 0 && ip[4 + j % 4] == 0 && ip[8 + j % 4] == 0 && ip[12 + j % 4] == 0);
        } else {
            assert(ip[4] == 0 && ip[8] == 0 && ip[12] == 0);
        }
    }
    assert forall|k: int| 0 <= k < 16 implies #[trigger] iwht(ip)[k] == (ip[0] + 3) / 8 by {
        let r = k / 4;
        assert(m[4 * r] == ip[0] && m[4 * r + 1] == 0 && m[4 * r + 2] == 0 && m[4 * r + 3] == 0);
    }
}

/// A plane's blocks touch only that plane's context flags, and keep the
/// shapes.
pub proof fn lemma_plane_blocks_frame(
    data: Seq<u8>,
    st: ResState,
    probs: Seq<int>,
    t: int,
    first: int,
    dq_dc: int,
    dq_ac: int,
    base: int,
    off: int,
    w: int,
    n: nat,
)
    requires
        st.coeffs.len() == 384,
        st.top.len() == 9,
        st.left.len() == 9,
        (w == 4 && off == 0) || (w == 2 && (off == 4 || off == 6)),
        n <= w * w,
        0 <= base,
        base + w * w <= 24,
        0 <= first <= 1,
    ensures
        ({
            let r = plane_blocks(data, st, probs, t, first, dq_dc, dq_ac, base, off, w, n);
            &&& r.coeffs.len() == 384
            &&& r.top.len() == 9
            &&& r.left.len() == 9
            &&& forall|j: int| 0 <= j < 9 && !(off <= j < off + w) ==> #[trigger] r.top[j] == st.top[j]
            &&& forall|j: int| 0 <= j < 9 && !(off <= j < off + w) ==> #[trigger] r.left[j] == st.left[j]
        }),
    decreases n,
{
    if n > 0 {
        lemma_plane_blocks_frame(data, st, probs, t, first, dq_dc, dq_ac, base, off, w, (n - 1) as nat);
        let k = (n - 1) as int;
        assert(0 <= k / w < w && 0 <= k % w < w) by (nonlinear_arith)
            requires
                0 <= k < w * w,
                w == 2 || w == 4,
        ;
    }
}

/// A block's tokens leave alone every coefficient outside the positions
/// they cover, and end at or after the position they start at.
pub proof fn lemma_block_tokens_frame(
    data: Seq<u8>,
    s: BoolState,
    probs: Seq<int>,
    t: int,
    n: int,
    ctx: int,
    check_eob: bool,
    dq_dc: int,
    dq_ac: int,
    out: Seq<int>,
)
    requires
        0 <= n <= 16,
        out.len() == 16,
    ensures
        ({
            let r = block_tokens(data, s, probs, t, n, ctx, check_eob, dq_dc, dq_ac, out);
            &&& n <= r.2 <= 16
            &&& r.1.len() == 16
            &&& forall|j: int|
                0 <= j < 16 && (forall|k: int| n <= k < r.2 ==> zigzag(k) != j) ==> #[trigger] r.1[j] == out[j]
        }),
    decreases 16 - n,
{
    lemma_block_tokens_unfold(data, s, probs, t, n, ctx, check_eob, dq_dc, dq_ac, out);
    let r = block_tokens(data, s, probs, t, n, ctx, check_eob, dq_dc, dq_ac, out);
    if n < 16 {
        let p = token_pidx(t, n, ctx);
        if check_eob && !bool_bit(s, probs[p]) {
        } else {
            let s1 = if check_eob {
                bool_next(data, s, probs[p])
            } else {
                s
            };
            let (s2, nonzero) = rd_bool(data, s1, probs[p + 1]);
            if !nonzero {
                lemma_block_tokens_frame(data, s2, probs, t, n + 1, 0, false, dq_dc, dq_ac, out);
            } else {
                let (s3, big) = rd_bool(data, s2, probs[p + 2]);
                let (s4, v) = if big {
                    large_value(data, s3, probs, p)
                } else {
                    (s3, 1)
                };
                let (s5, neg) = rd_bool(data, s4, 128);
                let d = if n > 0 {
                    dq_ac
                } else {
                    dq_dc
                };
                let c = wrap16s(
                    (if neg {
                        -v
                    } else {
                        v
                    }) * d,
                );
                let o2 = out.update(zigzag(n), c);
                let cx = if big {
                    2int
                } else {
                    1int
                };
                lemma_block_tokens_frame(data, s5, probs, t, n + 1, cx, true, dq_dc, dq_ac, o2);
                assert forall|j: int|
                    0 <= j < 16 && (forall|k: int| n <= k < r.2 ==> zigzag(k) != j) implies #[trigger] r.1[j]
                    == out[j] by {
                    assert(zigzag(n) != j);
                    assert(forall|k: int| n + 1 <= k < r.2 ==> zigzag(k) != j);
                    assert(o2[j] == out[j]);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Intra prediction (RFC 6386 section 12)
// ---------------------------------------------------------------------------
//
// A block's neighbours are given as two sequences. `a` is the row above,
// starting at the corner: `a[0]` is the pixel above and to the left (the
// RFC's `P`), and `a[1 + i]` is the pixel above column `i` (the RFC's
// `A[i]`, running on to the right of the block for subblocks). `l[i]` is
// the pixel left of row `i` (the RFC's `L[i]`).

/// The sum of `s[lo..hi]`.
pub open spec fn sum_range(s: Seq<int>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        sum_range(s, lo, hi - 1) + s[hi - 1]
    }
}

pub proof fn lemma_sum_range_eq(s: Seq<int>, t: Seq<int>, lo: int, hi: int)
    requires
        forall|i: int| lo <= i < hi ==> s[i] == t[i],
    ensures
        sum_range(s, lo, hi) == sum_range(t, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_range_eq(s, t, lo, hi - 1);
    }
}

/// The rounded average of two pixels.
pub open spec fn spec_avg2(a: int, b: int) -> int {
    (a + b + 1) / 2
}

/// The rounded `1 2 1` weighting of three pixels.
pub open spec fn spec_avg3(a: int, b: int, c: int) -> int {
    (a + 2 * b + c + 2) / 4
}

/// Pixel `(r, c)` of the prediction of an `n`-square luma (`n == 16`) or
/// chroma (`n == 8`) block (section 12.2, `vp8_build_intra_predictors`).
/// Modes 0 to 3 are `DC_PRED`, `TM_PRED`, `V_PRED` and `H_PRED`. Modes 4
/// to 6 are what `DC_PRED` means on the frame's edge: with no row above
/// (4), no column to the left (5), or neither (6).
pub open spec fn pred_big(mode: int, n: int, a: Seq<int>, l: Seq<int>, r: int, c: int) -> int {
    if mode == 0 {
        (sum_range(a, 1, n + 1) + sum_range(l, 0, n) + n) / (2 * n)
    } else if mode == 1 {
        clip_to(a[1 + c] + l[r] - a[0], 255)
    } else if mode == 2 {
        a[1 + c]
    } else if mode == 3 {
        l[r]
    } else if mode == 4 {
        (sum_range(l, 0, n) + n / 2) / n
    } else if mode == 5 {
        (sum_range(a, 1, n + 1) + n / 2) / n
    } else {
        128
    }
}

/// The RFC's edge array `E` of a subblock: `E[0..4]` the left column from
/// the bottom up, `E[4]` the corner, `E[5..13]` the row above.
pub open spec fn edge4(a: Seq<int>, l: Seq<int>, i: int) -> int {
    if i < 4 {
        l[3 - i]
    } else {
        a[i - 4]
    }
}

/// `avg3(E[i - 1], E[i], E[i + 1])`.
pub open spec fn edge3(a: Seq<int>, l: Seq<int>, i: int) -> int {
    spec_avg3(edge4(a, l, i - 1), edge4(a, l, i), edge4(a, l, i + 1))
}

/// `avg2(E[i], E[i + 1])`.
pub open spec fn edge2(a: Seq<int>, l: Seq<int>, i: int) -> int {
    spec_avg2(edge4(a, l, i), edge4(a, l, i + 1))
}

/// Pixel `(r, c)` of the prediction of a 4x4 subblock (section 12.3,
/// `subblock_intra_predict`). Modes 0 to 9 are `B_DC_PRED`, `B_TM_PRED`,
/// `B_VE_PRED`, `B_HE_PRED`, `B_RD_PRED`, `B_VR_PRED`, `B_LD_PRED`,
/// `B_VL_PRED`, `B_HD_PRED` and `B_HU_PRED`.
pub open spec fn pred4_px(mode: int, a: Seq<int>, l: Seq<int>, r: int, c: int) -> int {
    if mode == 0 {
        (sum_range(a, 1, 5) + sum_range(l, 0, 4) + 4) / 8
    } else if mode == 1 {
        clip_to(a[1 + c] + l[r] - a[0], 255)
    } else if mode == 2 {
        // avg3(A[c - 1], A[c], A[c + 1]), with A[-1] the corner.
        spec_avg3(a[c], a[c + 1], a[c + 2])
    } else if mode == 3 {
        // avg3(L[r - 1], L[r], L[r + 1]), with L[-1] the corner and the
        // last row repeating L[3].
        if r == 3 {
            spec_avg3(l[2], l[3], l[3])
        } else {
            edge3(a, l, 3 - r)
        }
    } else if mode == 4 {
        edge3(a, l, 4 - r + c)
    } else if mode == 5 {
        if r == 0 {
            edge2(a, l, 4 + c)
        } else if r == 1 {
            edge3(a, l, 4 + c)
        } else if r == 2 {
            if c == 0 {
                edge3(a, l, 3)
            } else {
                edge2(a, l, 3 + c)
            }
        } else {
            if c == 0 {
                edge3(a, l, 2)
            } else {
                edge3(a, l, 3 + c)
            }
        }
    } else if mode == 6 {
        if r == 3 && c == 3 {
            spec_avg3(a[7], a[8], a[8])
        } else {
            spec_avg3(a[1 + r + c], a[2 + r + c], a[3 + r + c])
        }
    } else if mode == 7 {
        if r == 0 {
            spec_avg2(a[1 + c], a[2 + c])
        } else if r == 1 {
            spec_avg3(a[1 + c], a[2 + c], a[3 + c])
        } else if r == 2 {
            if c == 3 {
                spec_avg3(a[5], a[6], a[7])
            } else {
                spec_avg2(a[2 + c], a[3 + c])
            }
        } else {
            if c == 3 {
                spec_avg3(a[6], a[7], a[8])
            } else {
                spec_avg3(a[2 + c], a[3 + c], a[4 + c])
            }
        }
    } else if mode == 8 {
        if r == 0 && c == 2 {
            edge3(a, l, 5)
        } else if r == 0 && c == 3 {
            edge3(a, l, 6)
        } else if c % 2 == 0 {
            edge2(a, l, 3 - r + c / 2)
        } else {
            edge3(a, l, 4 - r + c / 2)
        }
    } else {
        let k = r + c / 2;
        if k >= 3 {
            l[3]
        } else if c % 2 == 0 {
            spec_avg2(l[k], l[k + 1])
        } else if k == 2 {
            spec_avg3(l[2], l[3], l[3])
        } else {
            spec_avg3(l[k], l[k + 1], l[k + 2])
        }
    }
}

// ---------------------------------------------------------------------------
// Reconstruction of a macroblock in the scratch block
// ---------------------------------------------------------------------------
//
// Prediction and the residual are put together in a scratch block, as in
// libwebp and the RFC's reference decoder: an array of 26 rows of 32
// bytes. The macroblock's 16x16 luma block starts at `s_y()`, with the
// row above it one row up (running four pixels past the block on the
// right, for subblock prediction) and the column left of it one byte to
// the left. The 8x8 chroma blocks start at `s_u()` and `s_v()` and have
// their neighbours in the same places.

/// Where the luma block starts in the scratch block.
pub open spec fn s_y() -> int {
    40
}

/// Where the U block starts.
pub open spec fn s_u() -> int {
    584
}

/// Where the V block starts.
pub open spec fn s_v() -> int {
    600
}

/// Offset `o` from a block's first pixel is inside the block, `w` wide
/// and four rows high, in the scratch layout.
pub open spec fn in_blk(o: int, w: int) -> bool {
    0 <= o && o % 32 < w && o / 32 < 4
}

/// The scratch buffer with the residual `res` (a 4x4 block in raster
/// order) added to the block at `d`, clipped to a byte (RFC 6386 section
/// 14.5).
pub open spec fn add_res(b: Seq<u8>, d: int, res: Seq<int>) -> Seq<u8> {
    Seq::new(
        b.len(),
        |j: int|
            if in_blk(j - d, 4) {
                clip_to(b[j] + res[4 * ((j - d) / 32) + (j - d) % 32], 255) as u8
            } else {
                b[j]
            },
    )
}

/// The row above the `n`-wide block at `d` in the scratch layout, from
/// the corner: the `a` of `vp8spec::pred_big`.
pub open spec fn nb_above(b: Seq<u8>, d: int, n: int) -> Seq<int> {
    Seq::new((n + 1) as nat, |i: int| b[d - 33 + i] as int)
}

/// The column left of the `n`-high block at `d`.
pub open spec fn nb_left(b: Seq<u8>, d: int, n: int) -> Seq<int> {
    Seq::new(n as nat, |i: int| b[d + 32 * i - 1] as int)
}

/// Offset `o` from a block's first pixel is inside the `n`-square block.
pub open spec fn in_sq(o: int, n: int) -> bool {
    0 <= o && o % 32 < n && o / 32 < n
}

/// The scratch buffer with the `n`-square block at `d` replaced by its
/// prediction from the pixels around it (RFC 6386 section 12.2).
pub open spec fn paint_big(b: Seq<u8>, d: int, n: int, mode: int) -> Seq<u8> {
    Seq::new(
        b.len(),
        |j: int|
            if in_sq(j - d, n) {
                pred_big(mode, n, nb_above(b, d, n), nb_left(b, d, n), (j - d) / 32, (j - d) % 32) as u8
            } else {
                b[j]
            },
    )
}

/// The scratch buffer with the 4x4 subblock at `d` replaced by its
/// prediction (section 12.3).
pub open spec fn paint4(b: Seq<u8>, d: int, mode: int) -> Seq<u8> {
    Seq::new(
        b.len(),
        |j: int|
            if in_sq(j - d, 4) {
                pred4_px(mode, nb_above(b, d, 8), nb_left(b, d, 4), (j - d) / 32, (j - d) % 32) as u8
            } else {
                b[j]
            },
    )
}

/// `ws` with `n` bytes at `d` taken from `src[s..]`.
pub open spec fn put_run(ws: Seq<u8>, d: int, src: Seq<u8>, s: int, n: int) -> Seq<u8> {
    Seq::new(ws.len(), |j: int| if d <= j < d + n { src[j - d + s] } else { ws[j] })
}

/// `ws` with `n` bytes at `d` set to `v`.
pub open spec fn fill_run(ws: Seq<u8>, d: int, n: int, v: u8) -> Seq<u8> {
    Seq::new(ws.len(), |j: int| if d <= j < d + n { v } else { ws[j] })
}

/// The scratch block with the last four columns of the first `ny` luma
/// rows (counting from the row above the block) and the first `nu` and
/// `nv` chroma rows moved into the four columns left of each block: the
/// macroblock just reconstructed becomes the left neighbour of the next.
pub open spec fn rot3(ws: Seq<u8>, ny: int, nu: int, nv: int) -> Seq<u8> {
    Seq::new(
        ws.len(),
        |j: int|
            if 4 <= j && (j - 4) % 32 < 4 && (j - 4) / 32 < ny {
                ws[j + 16]
            } else if 548 <= j && (j - 548) % 32 < 4 && (j - 548) / 32 < nu {
                ws[j + 8]
            } else if 564 <= j && (j - 564) % 32 < 4 && (j - 564) / 32 < nv {
                ws[j + 8]
            } else {
                ws[j]
            },
    )
}

/// The scratch block with the four pixels above and to the right of the
/// luma block (at offset 24) repeated to the right of rows 3, 7 and 11,
/// up to `k` times: the lower subblocks of the right column predict from
/// the same four pixels as the top one.
pub open spec fn tr_rep(ws: Seq<u8>, k: int) -> Seq<u8> {
    Seq::new(
        ws.len(),
        |j: int|
            if 24 + 128 <= j < 24 + 128 * k && (j - 24) % 128 < 4 {
                ws[24 + (j - 24) % 128]
            } else {
                ws[j]
            },
    )
}

/// The scratch block with the pixels above and to the right of a `B_PRED`
/// macroblock set up. Below the first macroblock row they come from the
/// row above, `ty`: the next macroblock's first four pixels, or for the
/// last macroblock of a row its own last pixel four times.
pub open spec fn set_tr(ws: Seq<u8>, ty: Seq<u8>, mb_x: int, mb_y: int, mb_w: int) -> Seq<u8> {
    let w1 = if mb_y > 0 {
        if mb_x >= mb_w - 1 {
            fill_run(ws, 24, 4, ty[16 * mb_x + 15])
        } else {
            put_run(ws, 24, ty, 16 * mb_x + 16, 4)
        }
    } else {
        ws
    };
    tr_rep(w1, 4)
}

/// The scratch block made ready for macroblock `(mb_x, mb_y)`, from the
/// scratch block as the previous macroblock left it and the bottom rows
/// `ty`, `tu`, `tv` of the macroblock row above.
pub open spec fn mb_setup(
    ws: Seq<u8>,
    ty: Seq<u8>,
    tu: Seq<u8>,
    tv: Seq<u8>,
    mb_x: int,
    mb_y: int,
    mb_w: int,
    is_i4x4: bool,
) -> Seq<u8> {
    let w0 = if mb_x > 0 {
        rot3(ws, 17, 9, 9)
    } else {
        ws
    };
    let w1 = if mb_y > 0 {
        put_run(put_run(put_run(w0, 8, ty, 16 * mb_x, 16), 552, tu, 8 * mb_x, 8), 568, tv, 8 * mb_x, 8)
    } else {
        w0
    };
    if is_i4x4 {
        set_tr(w1, ty, mb_x, mb_y, mb_w)
    } else {
        w1
    }
}

/// Where luma subblock `n` (in raster order) starts, from the luma block.
pub open spec fn scan(n: int) -> int {
    4 * (n % 4) + 128 * (n / 4)
}

/// `DC_PRED` on the frame's edge predicts from the side it has (section
/// 12.2): the mode `pred_big` takes for it.
pub open spec fn edge_mode(mb_x: int, mb_y: int, mode: int) -> int {
    if mode == 0 {
        if mb_x == 0 {
            if mb_y == 0 {
                6
            } else {
                5
            }
        } else if mb_y == 0 {
            4
        } else {
            0
        }
    } else {
        mode
    }
}

/// The sixteen coefficients of the block at `co[i]`.
pub open spec fn blk(co: Seq<int>, i: int) -> Seq<int> {
    Seq::new(16, |k: int| co[i + k])
}

/// A `B_PRED` macroblock's first `k` luma subblocks: each is predicted
/// from the pixels around it, earlier subblocks included, and has its
/// residual added.
pub open spec fn rec_luma4(ws: Seq<u8>, bmodes: Seq<int>, co: Seq<int>, k: int) -> Seq<u8>
    decreases k,
{
    if k <= 0 {
        ws
    } else {
        let d = s_y() + scan(k - 1);
        add_res(paint4(rec_luma4(ws, bmodes, co, k - 1), d, bmodes[k - 1]), d, idct(blk(co, 16 * (k - 1))))
    }
}

/// The residuals of the first `k` luma subblocks added to a predicted
/// 16x16 block.
pub open spec fn rec_res16(ws: Seq<u8>, co: Seq<int>, k: int) -> Seq<u8>
    decreases k,
{
    if k <= 0 {
        ws
    } else {
        add_res(rec_res16(ws, co, k - 1), s_y() + scan(k - 1), idct(blk(co, 16 * (k - 1))))
    }
}

/// The residuals of the four subblocks of the chroma block at `d`, whose
/// coefficients start at `co[i]`.
pub open spec fn rec_chroma(ws: Seq<u8>, d: int, co: Seq<int>, i: int) -> Seq<u8> {
    let b1 = add_res(ws, d, idct(blk(co, i)));
    let b2 = add_res(b1, d + 4, idct(blk(co, i + 16)));
    let b3 = add_res(b2, d + 4 * 32, idct(blk(co, i + 32)));
    add_res(b3, d + 4 * 32 + 4, idct(blk(co, i + 48)))
}

/// Macroblock `(mb_x, mb_y)` reconstructed in the scratch block `ws` (as
/// `mb_setup` leaves it) from its modes `m` and its 384 dequantized
/// coefficients `co` (sixteen luma blocks, then four U and four V).
pub open spec fn mb_recon(ws: Seq<u8>, m: MbModeSpec, mb_x: int, mb_y: int, co: Seq<int>) -> Seq<u8> {
    let wy = if m.is_i4x4 {
        rec_luma4(ws, m.bmodes, co, 16)
    } else {
        rec_res16(paint_big(ws, s_y(), 16, edge_mode(mb_x, mb_y, m.ymode)), co, 16)
    };
    let uvm = edge_mode(mb_x, mb_y, m.uvmode);
    let wp = paint_big(paint_big(wy, s_u(), 8, uvm), s_v(), 8, uvm);
    rec_chroma(rec_chroma(wp, s_u(), co, 256), s_v(), co, 320)
}

// ---------------------------------------------------------------------------
// Which coefficients a block has
// ---------------------------------------------------------------------------

/// A block whose coefficients are zero except, at most, numbers 0, 1 and 4.
pub open spec fn only_ac3(cb: Seq<int>) -> bool {
    forall|k: int| 0 <= k < 16 && k != 0 && k != 1 && k != 4 ==> #[trigger] cb[k] == 0
}

/// A block whose coefficients are zero except, at most, the first.
pub open spec fn only_dc(cb: Seq<int>) -> bool {
    forall|k: int| 1 <= k < 16 ==> #[trigger] cb[k] == 0
}

/// A block with no coefficients.
pub open spec fn zero_blk(cb: Seq<int>) -> bool {
    only_dc(cb) && cb[0] == 0
}

/// Block `i` of a macroblock's 384 coefficients.
pub open spec fn mblk(co: Seq<int>, i: int) -> Seq<int> {
    blk(co, 16 * i)
}

/// Every block of the macroblock has an inverse DCT that fits in 16 bits
/// (see `idct_tame`).
pub open spec fn mb_tame(co: Seq<int>) -> bool {
    forall|i: int| 0 <= i < 24 ==> idct_tame(#[trigger] mblk(co, i))
}

/// A block's tokens leave alone the coefficients from the position they
/// end at: a block whose tokens end by position 3 has only its first three
/// coefficients in zigzag order (raster places 0, 1 and 4), and one whose
/// tokens end by position 1 has only its DC.
pub proof fn lemma_block_sel(
    data: Seq<u8>,
    s: BoolState,
    probs: Seq<int>,
    t: int,
    first: int,
    ctx: int,
    dq_dc: int,
    dq_ac: int,
    out: Seq<int>,
)
    requires
        0 <= first <= 1,
        out.len() == 16,
        forall|j: int| 1 <= j < 16 ==> out[j] == 0,
    ensures
        ({
            let r = block_tokens(data, s, probs, t, first, ctx, true, dq_dc, dq_ac, out);
            &&& r.2 <= 3 ==> only_ac3(r.1)
            &&& r.2 <= 1 ==> only_dc(r.1)
            &&& first == 1 ==> r.1[0] == out[0]
        }),
{
    lemma_block_tokens_frame(data, s, probs, t, first, ctx, true, dq_dc, dq_ac, out);
    let r = block_tokens(data, s, probs, t, first, ctx, true, dq_dc, dq_ac, out);
    assert(zigzag(0) == 0 && zigzag(1) == 1 && zigzag(2) == 4);
    assert(forall|k: int| 1 <= k < 16 ==> zigzag(k) != 0);
    if r.2 <= 3 {
        assert forall|j: int| 0 <= j < 16 && j != 0 && j != 1 && j != 4 implies #[trigger] r.1[j] == 0 by {
            assert(forall|k: int| first <= k < r.2 ==> zigzag(k) != j);
        }
    }
    if r.2 <= 1 {
        assert forall|j: int| 1 <= j < 16 implies #[trigger] r.1[j] == 0 by {
            assert(forall|k: int| first <= k < r.2 ==> zigzag(k) != j);
        }
    }
    if first == 1 {
        assert(forall|k: int| first <= k < r.2 ==> zigzag(k) != 0);
    }
}

// ---------------------------------------------------------------------------
// Reconstruction of a frame, before the loop filter
// ---------------------------------------------------------------------------

/// What reconstruction carries from one macroblock to the next: the
/// scratch block, the bottom pixel rows of the macroblock row above (`ty`,
/// `tu`, `tv`, each as wide as the frame in whole macroblocks), and the
/// planes.
pub struct Recon {
    pub ws: Seq<u8>,
    pub ty: Seq<u8>,
    pub tu: Seq<u8>,
    pub tv: Seq<u8>,
    pub y: Seq<u8>,
    pub u: Seq<u8>,
    pub v: Seq<u8>,
}

/// The plane `pl` (rows of `stride` bytes) with the first `k` rows of the
/// `n`-wide block at `ws[d..]` (rows of 32 bytes) written at column `x0`
/// of rows `y0` on.
pub open spec fn put_rows(pl: Seq<u8>, x0: int, y0: int, stride: int, ws: Seq<u8>, d: int, n: int, k: int) -> Seq<u8>
    decreases k,
{
    if k <= 0 {
        pl
    } else {
        put_run(put_rows(pl, x0, y0, stride, ws, d, n, k - 1), (y0 + (k - 1)) * stride + x0, ws, d + 32 * (k - 1), n)
    }
}

/// The scratch block at the start of macroblock row `mb_y`: the columns
/// left of the blocks hold 129. On the first row the rows above them hold
/// 127 (the luma one for four pixels past the block as well); on later
/// rows the corners above and left of the blocks hold 129. Section 12.2
/// gives these values for the pixels a frame does not have.
pub open spec fn row_init(ws: Seq<u8>, mb_y: int) -> Seq<u8> {
    Seq::new(
        ws.len(),
        |j: int|
            if 39 <= j && (j - 39) % 32 == 0 && (j - 39) / 32 < 16 {
                129u8
            } else if 583 <= j && (j - 583) % 32 == 0 && (j - 583) / 32 < 8 {
                129u8
            } else if 599 <= j && (j - 599) % 32 == 0 && (j - 599) / 32 < 8 {
                129u8
            } else if mb_y > 0 {
                if j == 7 || j == 551 || j == 567 {
                    129u8
                } else {
                    ws[j]
                }
            } else if (7 <= j < 28) || (551 <= j < 560) || (567 <= j < 576) {
                127u8
            } else {
                ws[j]
            },
    )
}

/// Macroblock `(mb_x, mb_y)` of a frame `mb_w` by `mb_h` macroblocks:
/// reconstructed in the scratch block, written to the planes, and its
/// bottom rows kept for the macroblock row below.
pub open spec fn mb_step(st: Recon, m: MbModeSpec, co: Seq<int>, mb_x: int, mb_y: int, mb_w: int, mb_h: int) -> Recon {
    let w = mb_recon(mb_setup(st.ws, st.ty, st.tu, st.tv, mb_x, mb_y, mb_w, m.is_i4x4), m, mb_x, mb_y, co);
    let keep = mb_y < mb_h - 1;
    Recon {
        ws: w,
        ty: if keep {
            put_run(st.ty, 16 * mb_x, w, 520, 16)
        } else {
            st.ty
        },
        tu: if keep {
            put_run(st.tu, 8 * mb_x, w, 808, 8)
        } else {
            st.tu
        },
        tv: if keep {
            put_run(st.tv, 8 * mb_x, w, 824, 8)
        } else {
            st.tv
        },
        y: put_rows(st.y, 16 * mb_x, 16 * mb_y, 16 * mb_w, w, s_y(), 16, 16),
        u: put_rows(st.u, 8 * mb_x, 8 * mb_y, 8 * mb_w, w, s_u(), 8, 8),
        v: put_rows(st.v, 8 * mb_x, 8 * mb_y, 8 * mb_w, w, s_v(), 8, 8),
    }
}

/// The first `n` macroblocks of row `mb_y`, with modes `ms` and
/// coefficients `cos`.
pub open spec fn row_recon(
    st: Recon,
    ms: Seq<MbModeSpec>,
    cos: Seq<Seq<int>>,
    mb_y: int,
    mb_w: int,
    mb_h: int,
    n: nat,
) -> Recon
    decreases n,
{
    if n == 0 {
        st
    } else {
        mb_step(row_recon(st, ms, cos, mb_y, mb_w, mb_h, (n - 1) as nat), ms[n - 1], cos[n - 1], n - 1, mb_y, mb_w, mb_h)
    }
}

/// Every macroblock of a row has tame coefficients (see `idct_tame`).
pub open spec fn row_tame(cos: Seq<Seq<int>>) -> bool {
    forall|j: int| 0 <= j < cos.len() ==> mb_tame(#[trigger] cos[j])
}

/// The coefficients of macroblock `j` of a row are those its tokens give.
pub proof fn lemma_row_tokens_mbs(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    tops: Seq<Seq<bool>>,
    n: nat,
    j: int,
)
    requires
        0 <= j < n,
    ensures
        ({
            let r = row_tokens(data, s, fh, modes, tops, j as nat);
            let full = row_tokens(data, s, fh, modes, tops, n);
            &&& full.mbs.len() == n
            &&& full.mbs[j] == mb_tokens(data, r.s, fh, modes[j], r.tops[j], r.left).coeffs
        }),
    decreases n,
{
    lemma_row_tokens_len(data, s, fh, modes, tops, (n - 1) as nat);
    if j < n - 1 {
        lemma_row_tokens_mbs(data, s, fh, modes, tops, (n - 1) as nat, j);
    }
}

pub proof fn lemma_row_tokens_len(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    tops: Seq<Seq<bool>>,
    n: nat,
)
    ensures
        row_tokens(data, s, fh, modes, tops, n).mbs.len() == n,
    decreases n,
{
    if n > 0 {
        lemma_row_tokens_len(data, s, fh, modes, tops, (n - 1) as nat);
    }
}

/// Section 15: the planes `(Y, U, V)` after the loop filter of macroblock
/// `(mb_x, mb_y)`, which has modes `m` and coefficients `co`. Its level
/// comes from its segment and prediction kind; the inner edges are
/// filtered if it is `B_PRED` or has a nonzero coefficient.
pub open spec fn lf_mb_at(
    p: (Seq<u8>, Seq<u8>, Seq<u8>),
    fh: FrameHeader,
    m: MbModeSpec,
    co: Seq<int>,
    mb_x: int,
    mb_y: int,
    mb_w: int,
) -> (Seq<u8>, Seq<u8>, Seq<u8>) {
    let lv = seg_filter_level(fh, m.segment, m.is_i4x4);
    if lv > 0 {
        let il = interior_limit(lv, fh.filter.sharpness);
        lf_mb(
            p.0,
            p.1,
            p.2,
            mb_x,
            mb_y,
            mb_w,
            fh.filter.simple,
            m.is_i4x4 || any_nz(co),
            2 * lv + il,
            il,
            hev_threshold(lv),
        )
    } else {
        p
    }
}

/// The loop filter of the first `n` macroblocks of row `mb_y`, in order.
pub open spec fn lf_row(
    p: (Seq<u8>, Seq<u8>, Seq<u8>),
    fh: FrameHeader,
    ms: Seq<MbModeSpec>,
    cos: Seq<Seq<int>>,
    mb_y: int,
    mb_w: int,
    n: nat,
) -> (Seq<u8>, Seq<u8>, Seq<u8>)
    decreases n,
{
    if n == 0 {
        p
    } else {
        lf_mb_at(lf_row(p, fh, ms, cos, mb_y, mb_w, (n - 1) as nat), fh, ms[n - 1], cos[n - 1], n - 1, mb_y, mb_w)
    }
}

/// `tok_solid` for macroblock `j` of a row (the arguments are
/// `row_tokens`').
pub open spec fn tok_solid_at(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    tops: Seq<Seq<bool>>,
    j: int,
) -> bool {
    let r = row_tokens(data, s, fh, modes, tops, j as nat);
    tok_solid(data, r.s, fh, modes[j], r.tops[j], r.left)
}

pub open spec fn row_solid(
    data: Seq<u8>,
    s: BoolState,
    fh: FrameHeader,
    modes: Seq<MbModeSpec>,
    tops: Seq<Seq<bool>>,
    n: nat,
) -> bool {
    forall|j: int| 0 <= j < n ==> #[trigger] tok_solid_at(data, s, fh, modes, tops, j)
}

/// `row_solid` for row `y` of a frame.
pub open spec fn frame_row_solid(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    y: nat,
) -> bool {
    let np = num_parts(fh);
    let r = tok_rows(file, pstart, first, gh, fh, mb_w, y);
    let p = y as int % np;
    row_solid(tok_part(file, pstart, np - 1, p), r.parts[p], fh, mode_rows(first, gh, fh, mb_w, y + 1).mbs, r.tops, mb_w)
}

/// No block of the frame is zeros spelled out as tokens (see `mb_solid`).
pub open spec fn frame_solid(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    mb_h: nat,
) -> bool {
    forall|y: nat| y < mb_h ==> #[trigger] frame_row_solid(file, pstart, first, gh, fh, mb_w, y)
}

/// The coefficients of the macroblocks of row `y`, from the token
/// partition that carries the row.
pub open spec fn frame_coeffs(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    y: nat,
) -> Seq<Seq<int>> {
    let np = num_parts(fh);
    let r = tok_rows(file, pstart, first, gh, fh, mb_w, y);
    let p = y as int % np;
    row_tokens(
        tok_part(file, pstart, np - 1, p),
        r.parts[p],
        fh,
        mode_rows(first, gh, fh, mb_w, y + 1).mbs,
        r.tops,
        mb_w,
    ).mbs
}

/// Every macroblock of the frame has tame coefficients.
pub open spec fn frame_tame(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    mb_h: nat,
) -> bool {
    forall|y: nat| y < mb_h ==> row_tame(#[trigger] frame_coeffs(file, pstart, first, gh, fh, mb_w, y))
}

/// Before the first macroblock: everything is zero.
pub open spec fn recon_init(mb_w: nat, mb_h: nat) -> Recon {
    Recon {
        ws: Seq::new(832, |i: int| 0u8),
        ty: Seq::new(16 * mb_w, |i: int| 0u8),
        tu: Seq::new(8 * mb_w, |i: int| 0u8),
        tv: Seq::new(8 * mb_w, |i: int| 0u8),
        y: Seq::new(16 * mb_w * (16 * mb_h), |i: int| 0u8),
        u: Seq::new(8 * mb_w * (8 * mb_h), |i: int| 0u8),
        v: Seq::new(8 * mb_w * (8 * mb_h), |i: int| 0u8),
    }
}

/// One row's loop filter, if the frame has one.
pub open spec fn lf_recon(a: Recon, fh: FrameHeader, ms: Seq<MbModeSpec>, cos: Seq<Seq<int>>, y: int, mb_w: nat) -> Recon {
    if fh.filter.level == 0 {
        a
    } else {
        let p = lf_row((a.y, a.u, a.v), fh, ms, cos, y, mb_w as int, mb_w);
        Recon { y: p.0, u: p.1, v: p.2, ..a }
    }
}

/// The first `rows` macroblock rows of a frame: each row is reconstructed
/// and then loop-filtered. Prediction reads the scratch block and the
/// saved rows, which the filter does not touch, so later rows see these
/// rows unfiltered, as section 15 requires. `vp8order` proves this is
/// the same as filtering the whole frame after it is reconstructed.
pub open spec fn frame_recon(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    mb_h: nat,
    rows: nat,
) -> Recon
    decreases rows,
{
    if rows == 0 {
        recon_init(mb_w, mb_h)
    } else {
        let y = (rows - 1) as nat;
        let r = frame_recon(file, pstart, first, gh, fh, mb_w, mb_h, y);
        let ms = mode_rows(first, gh, fh, mb_w, rows).mbs;
        let cos = frame_coeffs(file, pstart, first, gh, fh, mb_w, y);
        lf_recon(
            row_recon(Recon { ws: row_init(r.ws, y as int), ..r }, ms, cos, y as int, mb_w as int, mb_h as int, mb_w),
            fh,
            ms,
            cos,
            y as int,
            mb_w,
        )
    }
}

/// The key frame at `file[off..]`, in the terms the functions above take:
/// where its first partition ends, that partition, the decoder state after
/// the frame header, the header, and the frame's size in macroblocks.
pub open spec fn vp8_parts(file: Seq<u8>, off: int) -> (int, Seq<u8>, BoolState, FrameHeader, nat, nat) {
    let end = off + 10 + first_part_size(file, off);
    let pt = file.subrange(off + 10, end);
    let x = frame_header(pt, bool_init(pt));
    (end, pt, x.0, x.1, ((frame_width(file, off) + 15) / 16) as nat, ((frame_height(file, off) + 15) / 16) as nat)
}

/// What the pixel theorem asks of a frame: its partitions begin as a
/// boolean decoder can, its coefficients are tame, and, if it has a loop
/// filter, no block is zeros spelled out as tokens.
pub open spec fn vp8_plain(file: Seq<u8>, off: int) -> bool {
    let (end, pt, gh, fh, mb_w, mb_h) = vp8_parts(file, off);
    let np = num_parts(fh);
    &&& bool_wf(bool_init(pt))
    &&& forall|p: int| 0 <= p < np ==> bool_wf(bool_init(#[trigger] tok_part(file, end, np - 1, p)))
    &&& frame_tame(file, end, pt, gh, fh, mb_w, mb_h)
    &&& fh.filter.level != 0 ==> frame_solid(file, end, pt, gh, fh, mb_w, mb_h)
}

/// The decoded frame at `file[off..]`: `y`, `u` and `v` are its
/// planes, in rows of `16 * mb_w` and `8 * mb_w` bytes.
pub open spec fn vp8_frame(file: Seq<u8>, off: int) -> Recon {
    let (end, pt, gh, fh, mb_w, mb_h) = vp8_parts(file, off);
    frame_recon(file, end, pt, gh, fh, mb_w, mb_h, mb_h)
}

/// One more row of `frame_recon`.
pub proof fn lemma_frame_step(
    file: Seq<u8>,
    pstart: int,
    first: Seq<u8>,
    gh: BoolState,
    fh: FrameHeader,
    mb_w: nat,
    mb_h: nat,
    y: nat,
    f0: Recon,
    mbs: Seq<Seq<int>>,
    f2: Recon,
    f3: Recon,
)
    requires
        y < mb_h,
        frame_tame(file, pstart, first, gh, fh, mb_w, mb_h),
        f0 == frame_recon(file, pstart, first, gh, fh, mb_w, mb_h, y),
        ({
            let np = num_parts(fh);
            let r = tok_rows(file, pstart, first, gh, fh, mb_w, y);
            let p = y as int % np;
            mbs == row_tokens(
                tok_part(file, pstart, np - 1, p),
                r.parts[p],
                fh,
                mode_rows(first, gh, fh, mb_w, y + 1).mbs,
                r.tops,
                mb_w,
            ).mbs
        }),
        row_tame(mbs) ==> f2 == row_recon(
            Recon { ws: row_init(f0.ws, y as int), ..f0 },
            mode_rows(first, gh, fh, mb_w, y + 1).mbs,
            mbs,
            y as int,
            mb_w as int,
            mb_h as int,
            mb_w,
        ),
        f3 == lf_recon(f2, fh, mode_rows(first, gh, fh, mb_w, y + 1).mbs, mbs, y as int, mb_w),
    ensures
        f3 == frame_recon(file, pstart, first, gh, fh, mb_w, mb_h, y + 1),
{
    assert(mbs == frame_coeffs(file, pstart, first, gh, fh, mb_w, y));
    assert((y + 1 - 1) as nat == y);
}

pub open spec fn all_zero(s: Seq<u8>, n: int) -> bool {
    s.len() == n && forall|i: int| 0 <= i < n ==> #[trigger] s[i] == 0
}

pub proof fn lemma_recon_init(st: Recon, mb_w: nat, mb_h: nat)
    requires
        all_zero(st.ws, (832) as int),
        all_zero(st.ty, (16 * mb_w) as int),
        all_zero(st.tu, (8 * mb_w) as int),
        all_zero(st.tv, (8 * mb_w) as int),
        all_zero(st.y, (16 * mb_w * (16 * mb_h)) as int),
        all_zero(st.u, (8 * mb_w * (8 * mb_h)) as int),
        all_zero(st.v, (8 * mb_w * (8 * mb_h)) as int),
    ensures
        st == recon_init(mb_w, mb_h),
{
    let r = recon_init(mb_w, mb_h);
    assert(st.ws =~= r.ws);
    assert(st.ty =~= r.ty);
    assert(st.tu =~= r.tu);
    assert(st.tv =~= r.tv);
    assert(st.y =~= r.y);
    assert(st.u =~= r.u);
    assert(st.v =~= r.v);
}

// ---------------------------------------------------------------------------
// YUV 4:2:0 to RGB
// ---------------------------------------------------------------------------
//
// The last stage of libwebp 1.6.0's default RGB output: the "fancy"
// chroma upsampler (`UPSAMPLE_FUNC` in `src/dsp/upsampling.c`, driven row
// by row by `EmitFancyRGB` in `src/dec/io_dec.c`) and the fixed-point
// conversion `VP8YuvToRgb` of `src/dsp/yuv.h`. Neither is fixed by the VP8
// format (RFC 6386 ends at the planes): this is libwebp's choice of
// filter, constants and rounding, written here in exact integers. C's
// `>> n` on the non-negative values below is `/ 2^n`.

/// `MultHi(v, coeff)`: `(v * coeff) >> 8`.
pub open spec fn yuv_mult_hi(v: int, coeff: int) -> int {
    (v * coeff) / 256
}

/// `VP8Clip8`: a value with `YUV_FIX2 = 6` fraction bits, as a byte.
pub open spec fn yuv_clip8(v: int) -> int {
    if 0 <= v < 16384 {
        v / 64
    } else if v < 0 {
        0
    } else {
        255
    }
}

/// `VP8YUVToR`.
pub open spec fn yuv_r(y: int, v: int) -> int {
    yuv_clip8(yuv_mult_hi(y, 19077) + yuv_mult_hi(v, 26149) - 14234)
}

/// `VP8YUVToG`.
pub open spec fn yuv_g(y: int, u: int, v: int) -> int {
    yuv_clip8(yuv_mult_hi(y, 19077) - yuv_mult_hi(u, 6419) - yuv_mult_hi(v, 13320) + 8708)
}

/// `VP8YUVToB`.
pub open spec fn yuv_b(y: int, u: int) -> int {
    yuv_clip8(yuv_mult_hi(y, 19077) + yuv_mult_hi(u, 33050) - 17685)
}

/// The upsampled chroma of a pixel in the first column, or the last one
/// of an even width: `(3 * n + f + 2) >> 2` of the sample `n` on the
/// nearer chroma line and `f` on the farther.
pub open spec fn fancy_edge(n: int, f: int) -> int {
    (3 * n + f + 2) / 4
}

/// The upsampled chroma of any other pixel, from the four samples around
/// it: `n0` the nearest, `n1` beside it on the same chroma line, `f0` and
/// `f1` the same two columns of the farther line. The weights come to
/// 9, 3, 3, 1 (of 16), in the two rounded steps of `UPSAMPLE_FUNC`:
/// `diag = (n0 + n1 + f0 + f1 + 8 + 2 * (n1 + f0)) >> 3`, then
/// `(diag + n0) >> 1`.
pub open spec fn fancy_mid(n0: int, n1: int, f0: int, f1: int) -> int {
    ((n0 + n1 + f0 + f1 + 8 + 2 * (n1 + f0)) / 8 + n0) / 2
}

/// Pixel `x` of a `len`-pixel line of upsampled chroma, from the chroma
/// lines of `c` that start at `no` (the nearer) and `fo` (the farther).
/// Pixel `x` is nearest chroma column `x / 2`; its other column is the
/// next one for odd `x` and the one before for even `x`.
pub open spec fn fancy_line(c: Seq<u8>, no: int, fo: int, len: int, x: int) -> int {
    let k = x / 2;
    if x == 0 || (x == len - 1 && len % 2 == 0) {
        fancy_edge(c[no + k] as int, c[fo + k] as int)
    } else {
        let k1 = if x % 2 == 1 {
            k + 1
        } else {
            k - 1
        };
        fancy_mid(c[no + k] as int, c[no + k1] as int, c[fo + k] as int, c[fo + k1] as int)
    }
}

/// The farther chroma line of output row `y` (the nearer is `y / 2`): the
/// next one for odd `y` and the one before for even `y`, except that the
/// first row, and the last row of an even height, have only their own
/// (`EmitFancyRGB` passes the same line twice).
pub open spec fn fancy_far_row(y: int, h: int) -> int {
    if y == 0 {
        0
    } else if y % 2 == 1 {
        if y + 1 < h {
            y / 2 + 1
        } else {
            y / 2
        }
    } else {
        y / 2 - 1
    }
}

/// The upsampled chroma at pixel `(x, y)` of a `w` by `h` image whose
/// chroma plane `c` has rows of `stride` bytes.
pub open spec fn fancy_chroma(c: Seq<u8>, stride: int, w: int, h: int, x: int, y: int) -> int {
    fancy_line(c, (y / 2) * stride, fancy_far_row(y, h) * stride, w, x)
}

/// A frame's planes: `width` by `height` pixels, luma rows `y_stride`
/// bytes apart, and chroma at half resolution (rounded up) in rows
/// `uv_stride` apart.
pub ghost struct Yuv420 {
    pub y: Seq<u8>,
    pub u: Seq<u8>,
    pub v: Seq<u8>,
    pub y_stride: int,
    pub uv_stride: int,
    pub width: int,
    pub height: int,
}

/// Red, green and blue of pixel `(x, y)`.
pub open spec fn rgb_r(im: Yuv420, x: int, y: int) -> int {
    yuv_r(im.y[y * im.y_stride + x] as int, fancy_chroma(im.v, im.uv_stride, im.width, im.height, x, y))
}

pub open spec fn rgb_g(im: Yuv420, x: int, y: int) -> int {
    yuv_g(
        im.y[y * im.y_stride + x] as int,
        fancy_chroma(im.u, im.uv_stride, im.width, im.height, x, y),
        fancy_chroma(im.v, im.uv_stride, im.width, im.height, x, y),
    )
}

pub open spec fn rgb_b(im: Yuv420, x: int, y: int) -> int {
    yuv_b(im.y[y * im.y_stride + x] as int, fancy_chroma(im.u, im.uv_stride, im.width, im.height, x, y))
}

/// Alpha of pixel `(x, y)`: from `alpha`, one byte per pixel in rows of
/// `w`, or opaque.
pub open spec fn rgb_a(alpha: Seq<u8>, has_alpha: bool, w: int, x: int, y: int) -> int {
    if has_alpha {
        alpha[y * w + x] as int
    } else {
        255
    }
}

/// Four bytes as an ARGB word.
pub open spec fn argb_word(a: int, r: int, g: int, b: int) -> int {
    a * 0x100_0000 + r * 0x1_0000 + g * 0x100 + b
}

/// Bytes per pixel of output layout `kind`: ARGB words (0), or bytes in
/// the order RGBA (1), BGRA (2), ARGB (3), RGB (4), BGR (5).
pub open spec fn rgb_bpp(kind: int) -> int {
    if kind == 0 {
        1
    } else if kind <= 3 {
        4
    } else {
        3
    }
}

/// Byte `k` of a pixel in byte layout `kind` (1 to 5).
pub open spec fn rgb_byte(kind: int, a: int, r: int, g: int, b: int, k: int) -> int {
    if kind == 1 {
        if k == 0 { r } else if k == 1 { g } else if k == 2 { b } else { a }
    } else if kind == 2 {
        if k == 0 { b } else if k == 1 { g } else if k == 2 { r } else { a }
    } else if kind == 3 {
        if k == 0 { a } else if k == 1 { r } else if k == 2 { g } else { b }
    } else if kind == 4 {
        if k == 0 { r } else if k == 1 { g } else { b }
    } else {
        if k == 0 { b } else if k == 1 { g } else { r }
    }
}

/// The ARGB word of pixel `(x, y)`.
pub open spec fn rgb_argb(im: Yuv420, alpha: Seq<u8>, has_alpha: bool, x: int, y: int) -> int {
    argb_word(rgb_a(alpha, has_alpha, im.width, x, y), rgb_r(im, x, y), rgb_g(im, x, y), rgb_b(im, x, y))
}

/// Byte `k` of pixel `(x, y)` in byte layout `kind`.
pub open spec fn rgb_out_byte(im: Yuv420, alpha: Seq<u8>, has_alpha: bool, kind: int, x: int, y: int, k: int) -> int {
    rgb_byte(kind, rgb_a(alpha, has_alpha, im.width, x, y), rgb_r(im, x, y), rgb_g(im, x, y), rgb_b(im, x, y), k)
}

/// `out` is the image as ARGB words, rows packed.
pub open spec fn rgb_image_argb(im: Yuv420, alpha: Seq<u8>, has_alpha: bool, out: Seq<u32>) -> bool {
    &&& out.len() == im.width * im.height
    &&& forall|x: int, y: int|
        0 <= x < im.width && 0 <= y < im.height ==> out[y * im.width + x] as int == #[trigger] rgb_argb(
            im,
            alpha,
            has_alpha,
            x,
            y,
        )
}

/// `ob` begins with the image in byte layout `kind`, rows packed.
pub open spec fn rgb_image_bytes(im: Yuv420, alpha: Seq<u8>, has_alpha: bool, kind: int, ob: Seq<u8>) -> bool {
    &&& ob.len() >= rgb_bpp(kind) * im.width * im.height
    &&& forall|x: int, y: int, k: int|
        0 <= x < im.width && 0 <= y < im.height && 0 <= k < rgb_bpp(kind) ==> ob[(y * im.width + x) * rgb_bpp(kind)
            + k] as int == #[trigger] rgb_out_byte(im, alpha, has_alpha, kind, x, y, k)
}

/// The frame decoded from `file[off..]` as an image: the planes of
/// `vp8_frame`, in rows of whole macroblocks, at the size its header gives.
pub open spec fn vp8_yuv(file: Seq<u8>, off: int) -> Yuv420 {
    let f = vp8_frame(file, off);
    let w = frame_width(file, off);
    Yuv420 {
        y: f.y,
        u: f.u,
        v: f.v,
        y_stride: 16 * ((w + 15) / 16),
        uv_stride: 8 * ((w + 15) / 16),
        width: w,
        height: frame_height(file, off),
    }
}

} // verus!
