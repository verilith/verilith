//! Parsing a VP8 key frame (RFC 6386 sections 9, 11, 13, 19), as libwebp
//! 1.6.0 does it (`src/dec/vp8_dec.c`, `tree_dec.c`, `quant_dec.c`): the
//! frame header, the per-macroblock intra modes, and the DCT/WHT tokens.
use crate::pixels::Error;
use crate::vp8bool::*;
use crate::vp8spec::*;
use crate::vp8tables::*;
use verilith_core::prims::*;
use vstd::prelude::*;

verus! {

/// Dequantization factors of one segment: `[dc, ac]` for Y1, Y2 and UV.
#[derive(Clone, Copy)]
pub struct Quant {
    pub y1: [i32; 2],
    pub y2: [i32; 2],
    pub uv: [i32; 2],
}

/// Loop filter parameters of one segment and macroblock kind.
#[derive(Clone, Copy)]
pub struct FInfo {
    /// Edge limit; 0 means no filtering.
    pub limit: i32,
    /// Interior limit.
    pub ilevel: i32,
    /// High edge variance threshold.
    pub hev_thresh: i32,
    /// Filter the inner edges too.
    pub inner: bool,
}

/// What the frame header says.
pub struct Header {
    pub width: usize,
    pub height: usize,
    pub mb_w: usize,
    pub mb_h: usize,
    pub update_map: bool,
    pub seg_probs: [u8; 3],
    /// 0: no loop filter, 1: simple, 2: normal.
    pub filter_type: u32,
    /// Filter parameters by `[segment][is_i4x4]`, flattened.
    pub fstrengths: [FInfo; 8],
    pub dqm: [Quant; 4],
    /// Token probabilities `[type][band][ctx][proba]`, flattened.
    pub proba: Vec<u8>,
    pub use_skip_proba: bool,
    pub skip_p: u8,
    /// Token partitions: `num_parts` of them, as byte ranges of the file.
    pub num_parts: usize,
    pub part_start: [usize; 8],
    pub part_end: [usize; 8],
}

/// Dequantization factors in range (`kDcTable` and `kAcTable` entries,
/// doubled or scaled for Y2).
pub open spec fn quant_ok(q: Quant) -> bool {
    &&& 0 <= q.y1@[0] <= 1024
    &&& 0 <= q.y1@[1] <= 1024
    &&& 0 <= q.y2@[0] <= 1024
    &&& 0 <= q.y2@[1] <= 1024
    &&& 0 <= q.uv@[0] <= 1024
    &&& 0 <= q.uv@[1] <= 1024
}

/// Filter parameters in range.
pub open spec fn finfo_ok(f: FInfo) -> bool {
    &&& 0 <= f.limit <= 2 * 63 + 63
    &&& 0 <= f.ilevel <= 63
    &&& 0 <= f.hev_thresh <= 2
}

impl Header {
    /// What `parse_header` guarantees.
    pub open spec fn ok(&self, len: nat) -> bool {
        &&& 1 <= self.width < 0x4000
        &&& 1 <= self.height < 0x4000
        &&& self.mb_w == (self.width + 15) / 16
        &&& self.mb_h == (self.height + 15) / 16
        &&& self.filter_type <= 2
        &&& self.proba@.len() == 1056
        &&& (self.num_parts == 1 || self.num_parts == 2 || self.num_parts == 4 || self.num_parts == 8)
        &&& forall|i: int|
            0 <= i < self.num_parts ==> (#[trigger] self.part_start@[i]) <= self.part_end@[i] && self.part_end@[i] <= len
        &&& forall|i: int| 0 <= i < 8 ==> #[trigger] finfo_ok(self.fstrengths@[i])
        &&& forall|i: int| 0 <= i < 4 ==> #[trigger] quant_ok(self.dqm@[i])
    }
}

#[inline(always)]
fn clip(v: i32, m: i32) -> (r: i32)
    requires
        0 <= m,
    ensures
        0 <= r <= m,
        r == clip_to(v as int, m as int),
{
    if v < 0 {
        0
    } else if v > m {
        m
    } else {
        v
    }
}

/// The segment header as read (`ParseSegmentHeader`).
pub struct SegRaw {
    pub use_segment: bool,
    pub update_map: bool,
    pub absolute_delta: bool,
    pub quantizer: [i32; 4],
    pub fstrength: [i32; 4],
    pub seg_probs: [u8; 3],
}

impl SegRaw {
    pub open spec fn ok(&self) -> bool {
        &&& forall|j: int| 0 <= j < 4 ==> -255 <= #[trigger] self.quantizer@[j] <= 255
        &&& forall|j: int| 0 <= j < 4 ==> -255 <= #[trigger] self.fstrength@[j] <= 255
    }

    pub open spec fn matches(&self, h: SegHeader) -> bool {
        &&& self.use_segment == h.enabled
        &&& self.update_map == h.update_map
        &&& self.absolute_delta == h.absolute
        &&& forall|j: int| 0 <= j < 4 ==> #[trigger] self.quantizer@[j] == h.quant[j]
        &&& forall|j: int| 0 <= j < 4 ==> #[trigger] self.fstrength@[j] == h.lf[j]
        &&& forall|j: int| 0 <= j < 3 ==> #[trigger] self.seg_probs@[j] == h.probs[j]
    }
}

/// The filter header as read (`ParseFilterHeader`): of the adjustment
/// deltas a key frame uses only the first of each kind.
pub struct FiltRaw {
    pub simple: bool,
    pub level: i32,
    pub sharpness: i32,
    pub use_lf_delta: bool,
    pub ref_lf_delta0: i32,
    pub mode_lf_delta0: i32,
}

impl FiltRaw {
    pub open spec fn ok(&self) -> bool {
        &&& 0 <= self.level < 64
        &&& 0 <= self.sharpness < 8
        &&& -255 <= self.ref_lf_delta0 <= 255
        &&& -255 <= self.mode_lf_delta0 <= 255
    }

    pub open spec fn matches(&self, h: FilterHeader) -> bool {
        &&& self.simple == h.simple
        &&& self.level == h.level
        &&& self.sharpness == h.sharpness
        &&& self.use_lf_delta == h.adj_enable
        &&& self.ref_lf_delta0 == h.ref_delta[0]
        &&& self.mode_lf_delta0 == h.mode_delta[0]
    }
}

/// The quantizer indices as read (`VP8ParseQuant`'s first half).
pub struct QRaw {
    pub base_q0: i32,
    pub dqy1_dc: i32,
    pub dqy2_dc: i32,
    pub dqy2_ac: i32,
    pub dquv_dc: i32,
    pub dquv_ac: i32,
}

impl QRaw {
    pub open spec fn ok(&self) -> bool {
        &&& 0 <= self.base_q0 < 128
        &&& -255 <= self.dqy1_dc <= 255
        &&& -255 <= self.dqy2_dc <= 255
        &&& -255 <= self.dqy2_ac <= 255
        &&& -255 <= self.dquv_dc <= 255
        &&& -255 <= self.dquv_ac <= 255
    }

    pub open spec fn matches(&self, h: QuantHeader) -> bool {
        &&& self.base_q0 == h.y_ac_qi
        &&& self.dqy1_dc == h.y_dc_delta
        &&& self.dqy2_dc == h.y2_dc_delta
        &&& self.dqy2_ac == h.y2_ac_delta
        &&& self.dquv_dc == h.uv_dc_delta
        &&& self.dquv_ac == h.uv_ac_delta
    }
}

/// A segment's factors are the specification's.
pub open spec fn quant_matches(q: Quant, t: (int, int, int, int, int, int)) -> bool {
    &&& q.y1@[0] == t.0
    &&& q.y1@[1] == t.1
    &&& q.y2@[0] == t.2
    &&& q.y2@[1] == t.3
    &&& q.uv@[0] == t.4
    &&& q.uv@[1] == t.5
}

/// A filter entry is the specification's for segment `s` and macroblock
/// kind `i4x4`.
pub open spec fn finfo_matches(f: FInfo, fh: FrameHeader, s: int, i4x4: bool) -> bool {
    let lv = seg_filter_level(fh, s, i4x4);
    &&& f.inner == i4x4
    &&& if lv > 0 {
        &&& f.ilevel == interior_limit(lv, fh.filter.sharpness)
        &&& f.limit == 2 * lv + f.ilevel
        &&& f.hev_thresh == hev_threshold(lv)
    } else {
        f.limit == 0
    }
}

/// A macroblock's filter entry is the specification's: its segment's and
/// kind's strengths, with the inner edges on if it is `B_PRED` or has a
/// nonzero coefficient.
pub open spec fn fi_is(f: FInfo, fh: FrameHeader, m: MbModeSpec, co: Seq<int>) -> bool {
    let lv = seg_filter_level(fh, m.segment, m.is_i4x4);
    &&& f.inner == (m.is_i4x4 || any_nz(co))
    &&& if lv > 0 {
        &&& f.ilevel == interior_limit(lv, fh.filter.sharpness)
        &&& f.limit == 2 * lv + f.ilevel
        &&& f.hev_thresh == hev_threshold(lv)
    } else {
        f.limit == 0
    }
}

impl Header {
    /// The loop filter's kind and strengths are the specification's.
    pub open spec fn lf_matches(&self, fh: FrameHeader) -> bool {
        &&& self.filter_type == (if fh.filter.level == 0 {
            0int
        } else if fh.filter.simple {
            1int
        } else {
            2int
        })
        &&& self.filter_type > 0 ==> forall|j: int|
            0 <= j < 8 ==> finfo_matches(#[trigger] self.fstrengths@[j], fh, j / 2, j % 2 == 1)
    }

    /// The header is the one the specification reads from this file:
    /// `fh` from the first partition, the token partitions from the size
    /// table at `pstart`.
    pub open spec fn matches(&self, file: Seq<u8>, pstart: int, fh: FrameHeader) -> bool {
        &&& self.update_map == fh.seg.update_map
        &&& forall|j: int| 0 <= j < 3 ==> #[trigger] self.seg_probs@[j] == fh.seg.probs[j]
        &&& self.filter_type == (if fh.filter.level == 0 {
            0int
        } else if fh.filter.simple {
            1int
        } else {
            2int
        })
        &&& self.filter_type > 0 ==> forall|j: int|
            0 <= j < 8 ==> finfo_matches(#[trigger] self.fstrengths@[j], fh, j / 2, j % 2 == 1)
        &&& forall|i: int| 0 <= i < 4 ==> quant_matches(#[trigger] self.dqm@[i], seg_quant(fh, i))
        &&& forall|k: int| 0 <= k < 1056 ==> #[trigger] self.proba@[k] == fh.probs[k]
        &&& self.use_skip_proba == fh.mb_no_coeff_skip
        &&& self.skip_p == fh.prob_skip_false
        &&& self.num_parts == (if fh.log2_parts == 0 {
            1int
        } else if fh.log2_parts == 1 {
            2int
        } else if fh.log2_parts == 2 {
            4int
        } else {
            8int
        })
        &&& forall|p: int|
            0 <= p < self.num_parts ==> (#[trigger] self.part_start@[p]) == part_begin(
                file,
                pstart,
                self.num_parts - 1,
                p as nat,
            )
        &&& forall|p: int|
            0 <= p < self.num_parts - 1 ==> (#[trigger] self.part_end@[p]) == part_begin(
                file,
                pstart,
                self.num_parts - 1,
                (p + 1) as nat,
            )
        &&& self.part_end@[self.num_parts - 1] == file.len()
    }
}

/// A flag, then a signed `n`-bit value if it is set.
fn read_opt_signed(br: &mut BoolReader, data: &[u8], n: u32, Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (v:
    i32)
    requires
        old(br).inv(data@.len()),
        n <= 8,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        -255 <= v <= 255,
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = rd_opt_signed(part(data@, p0, old(br).end as int), g, n as nat);
            final(br).rel(data@, p0, x.0) && v == x.1
        },
{
    if br.get_bit(data, 0x80) {
        br.get_signed_value(data, n)
    } else {
        0
    }
}

/// Four optional signed `n`-bit values.
#[verifier::loop_isolation(false)]
fn read_opt_signed4(br: &mut BoolReader, data: &[u8], n: u32, Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (r:
    [i32; 4])
    requires
        old(br).inv(data@.len()),
        n <= 8,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        forall|j: int| 0 <= j < 4 ==> -255 <= #[trigger] r@[j] <= 255,
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = rd_opt_signed_seq(part(data@, p0, old(br).end as int), g, n as nat, 4);
            final(br).rel(data@, p0, x.0) && forall|j: int| 0 <= j < 4 ==> #[trigger] r@[j] == x.1[j]
        },
{
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g);
    let mut r: [i32; 4] = [0, 0, 0, 0];
    let mut s: usize = 0;
    while s < 4
        invariant
            s <= 4,
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            forall|j: int| 0 <= j < 4 ==> -255 <= #[trigger] r@[j] <= 255,
            ok0 && !br.eof ==> br.rel(data@, p0, rd_opt_signed_seq(pt, g, n as nat, s as nat).0),
            rd_opt_signed_seq(pt, g, n as nat, s as nat).1.len() == s,
            ok0 && !br.eof ==> forall|j: int|
                0 <= j < s ==> #[trigger] r@[j] == rd_opt_signed_seq(pt, g, n as nat, s as nat).1[j],
        decreases 4 - s,
    {
        let ghost cur = rd_opt_signed_seq(pt, g, n as nat, s as nat);
        let v = read_opt_signed(br, data, n, Ghost(p0), Ghost(cur.0));
        proof {
            let nx = rd_opt_signed(pt, cur.0, n as nat);
            assert((s + 1 - 1) as nat == s as nat);
            assert(rd_opt_signed_seq(pt, g, n as nat, (s + 1) as nat) == (nx.0, cur.1.push(nx.1)));
        }
        r[s] = v;
        s = s + 1;
    }
    r
}

/// The three probabilities of the segment map tree.
#[verifier::loop_isolation(false)]
fn read_seg_probs(br: &mut BoolReader, data: &[u8], Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (r: [u8; 3])
    requires
        old(br).inv(data@.len()),
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = rd_opt_lit_seq(part(data@, p0, old(br).end as int), g, 8, 255, 3);
            final(br).rel(data@, p0, x.0) && forall|j: int| 0 <= j < 3 ==> #[trigger] r@[j] == x.1[j]
        },
{
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g);
    let mut r: [u8; 3] = [255, 255, 255];
    let mut s: usize = 0;
    while s < 3
        invariant
            s <= 3,
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            ok0 && !br.eof ==> br.rel(data@, p0, rd_opt_lit_seq(pt, g, 8, 255, s as nat).0),
            rd_opt_lit_seq(pt, g, 8, 255, s as nat).1.len() == s,
            ok0 && !br.eof ==> forall|j: int|
                0 <= j < s ==> #[trigger] r@[j] == rd_opt_lit_seq(pt, g, 8, 255, s as nat).1[j],
        decreases 3 - s,
    {
        let ghost c = rd_opt_lit_seq(pt, g, 8, 255, s as nat);
        let p = if br.get_bit(data, 0x80) {
            br.get_value(data, 8) as u8
        } else {
            255
        };
        proof {
            let nx = rd_opt_lit(pt, c.0, 8, 255);
            assert((s + 1 - 1) as nat == s as nat);
            assert(rd_opt_lit_seq(pt, g, 8, 255, (s + 1) as nat) == (nx.0, c.1.push(nx.1)));
            assert(ok0 && !br.eof ==> br.rel(data@, p0, nx.0) && p == nx.1);
        }
        r[s] = p;
        s = s + 1;
    }
    r
}

/// `ParseSegmentHeader`.
#[verifier::loop_isolation(false)]
fn parse_segment(br: &mut BoolReader, data: &[u8], Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (r: SegRaw)
    requires
        old(br).inv(data@.len()),
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        r.ok(),
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = seg_header(part(data@, p0, old(br).end as int), g);
            final(br).rel(data@, p0, x.0) && r.matches(x.1)
        },
{
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g);
    let mut quantizer: [i32; 4] = [0, 0, 0, 0];
    let mut fstrength: [i32; 4] = [0, 0, 0, 0];
    let mut absolute_delta = true;
    let mut update_map = false;
    let mut seg_probs: [u8; 3] = [255, 255, 255];
    let use_segment = br.get_bit(data, 0x80);
    let ghost s1 = rd_flag(pt, g).0;
    let ghost mut cur = s1;
    proof {
        assert(ok0 && !br.eof ==> br.rel(data@, p0, s1) && use_segment == rd_flag(pt, g).1);
    }
    if use_segment {
        update_map = br.get_bit(data, 0x80);
        let ghost s2 = rd_flag(pt, s1).0;
        proof {
            assert(ok0 && !br.eof ==> br.rel(data@, p0, s2) && update_map == rd_flag(pt, s1).1);
        }
        let update_data = br.get_bit(data, 0x80);
        let ghost s3 = rd_flag(pt, s2).0;
        proof {
            cur = s3;
            assert(ok0 && !br.eof ==> br.rel(data@, p0, s3) && update_data == rd_flag(pt, s2).1);
        }
        if update_data {
            absolute_delta = br.get_bit(data, 0x80);
            let ghost s4 = rd_flag(pt, s3).0;
            proof {
                assert(ok0 && !br.eof ==> br.rel(data@, p0, s4) && absolute_delta == rd_flag(pt, s3).1);
            }
            quantizer = read_opt_signed4(br, data, 7, Ghost(p0), Ghost(s4));
            let ghost s5 = rd_opt_signed_seq(pt, s4, 7, 4).0;
            fstrength = read_opt_signed4(br, data, 6, Ghost(p0), Ghost(s5));
            proof {
                cur = rd_opt_signed_seq(pt, s5, 6, 4).0;
                assert(ok0 && !br.eof ==> br.rel(data@, p0, cur));
            }
        }
        let ghost s6 = cur;
        if update_map {
            seg_probs = read_seg_probs(br, data, Ghost(p0), Ghost(s6));
            proof {
                cur = rd_opt_lit_seq(pt, s6, 8, 255, 3).0;
            }
        }
    }
    let r = SegRaw { use_segment, update_map, absolute_delta, quantizer, fstrength, seg_probs };
    proof {
        if ok0 && !br.eof {
            let x = seg_header(pt, g);
            assert(br.rel(data@, p0, cur));
            assert(use_segment == x.1.enabled);
            assert(x.0 == cur);
            assert(r.matches(x.1));
        }
    }
    r
}

/// `ParseFilterHeader`.
fn parse_filter(br: &mut BoolReader, data: &[u8], Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (r: FiltRaw)
    requires
        old(br).inv(data@.len()),
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        r.ok(),
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = filter_header(part(data@, p0, old(br).end as int), g);
            final(br).rel(data@, p0, x.0) && r.matches(x.1)
        },
{
    proof {
        assert(p2(6) == 64) by (compute);
        assert(p2(3) == 8) by (compute);
    }
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g);
    let simple = br.get_bit(data, 0x80);
    let ghost s1 = rd_flag(pt, g).0;
    let level = br.get_value(data, 6) as i32;
    let ghost s2 = bool_literal(pt, s1, 6).0;
    let sharpness = br.get_value(data, 3) as i32;
    let ghost s3 = bool_literal(pt, s2, 3).0;
    let use_lf_delta = br.get_bit(data, 0x80);
    let ghost s4 = rd_flag(pt, s3).0;
    proof {
        assert(ok0 && !br.eof ==> br.rel(data@, p0, s4));
    }
    let mut ref_lf_delta0: i32 = 0;
    let mut mode_lf_delta0: i32 = 0;
    let ghost mut cur = s4;
    if use_lf_delta {
        let upd = br.get_bit(data, 0x80);
        let ghost s5 = rd_flag(pt, s4).0;
        proof {
            cur = s5;
        }
        if upd {
            let a = read_opt_signed4(br, data, 6, Ghost(p0), Ghost(s5));
            let ghost s6 = rd_opt_signed_seq(pt, s5, 6, 4).0;
            let b = read_opt_signed4(br, data, 6, Ghost(p0), Ghost(s6));
            ref_lf_delta0 = a[0];
            mode_lf_delta0 = b[0];
            proof {
                cur = rd_opt_signed_seq(pt, s6, 6, 4).0;
            }
        }
    }
    let r = FiltRaw { simple, level, sharpness, use_lf_delta, ref_lf_delta0, mode_lf_delta0 };
    proof {
        if ok0 && !br.eof {
            let x = filter_header(pt, g);
            assert(br.rel(data@, p0, cur));
            assert(x.0 == cur);
            assert(r.matches(x.1));
        }
    }
    r
}

/// The quantizer indices (`VP8ParseQuant`'s reads).
fn parse_quant_indices(br: &mut BoolReader, data: &[u8], Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (r:
    QRaw)
    requires
        old(br).inv(data@.len()),
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        r.ok(),
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = quant_header(part(data@, p0, old(br).end as int), g);
            final(br).rel(data@, p0, x.0) && r.matches(x.1)
        },
{
    proof {
        assert(p2(7) == 128) by (compute);
    }
    let ghost pt = part(data@, p0, br.end as int);
    let base_q0 = br.get_value(data, 7) as i32;
    let ghost s1 = bool_literal(pt, g, 7).0;
    let dqy1_dc = read_opt_signed(br, data, 4, Ghost(p0), Ghost(s1));
    let ghost s2 = rd_opt_signed(pt, s1, 4).0;
    let dqy2_dc = read_opt_signed(br, data, 4, Ghost(p0), Ghost(s2));
    let ghost s3 = rd_opt_signed(pt, s2, 4).0;
    let dqy2_ac = read_opt_signed(br, data, 4, Ghost(p0), Ghost(s3));
    let ghost s4 = rd_opt_signed(pt, s3, 4).0;
    let dquv_dc = read_opt_signed(br, data, 4, Ghost(p0), Ghost(s4));
    let ghost s5 = rd_opt_signed(pt, s4, 4).0;
    let dquv_ac = read_opt_signed(br, data, 4, Ghost(p0), Ghost(s5));
    QRaw { base_q0, dqy1_dc, dqy2_dc, dqy2_ac, dquv_dc, dquv_ac }
}

/// The dequantization factors of the four segments (`VP8ParseQuant`'s
/// second half).
#[verifier::loop_isolation(false)]
fn build_dqm(seg: &SegRaw, q: &QRaw, Ghost(fh): Ghost<FrameHeader>) -> (dqm: [Quant; 4])
    requires
        seg.ok(),
        q.ok(),
    ensures
        forall|j: int| 0 <= j < 4 ==> #[trigger] quant_ok(dqm@[j]),
        seg.matches(fh.seg) && q.matches(fh.quant) ==> forall|i: int|
            0 <= i < 4 ==> quant_matches(#[trigger] dqm@[i], seg_quant(fh, i)),
{
    let ghost m = seg.matches(fh.seg) && q.matches(fh.quant);
    let q0 = Quant { y1: [0, 0], y2: [0, 0], uv: [0, 0] };
    let mut dqm: [Quant; 4] = [q0, q0, q0, q0];
    let mut i: usize = 0;
    while i < 4
        invariant
            i <= 4,
            forall|j: int| 0 <= j < i ==> #[trigger] quant_ok(dqm@[j]),
            m ==> forall|j: int| 0 <= j < i ==> quant_matches(#[trigger] dqm@[j], seg_quant(fh, j)),
        decreases 4 - i,
    {
        if !seg.use_segment && i > 0 {
            let m0 = dqm[0];
            dqm[i] = m0;
        } else {
            let qi: i32 = if seg.use_segment {
                let qs = seg.quantizer[i];
                if seg.absolute_delta {
                    qs
                } else {
                    qs + q.base_q0
                }
            } else {
                q.base_q0
            };
            let y2a = ac_table(clip(qi + q.dqy2_ac, 127) as usize) as i32;
            proof {
                assert(0 <= y2a * 101581 <= 284 * 101581) by (nonlinear_arith)
                    requires
                        0 <= y2a <= 284,
                ;
            }
            let y2ac = (y2a * 101581) / 0x1_0000;
            let mq = Quant {
                y1: [dc_table(clip(qi + q.dqy1_dc, 127) as usize) as i32, ac_table(clip(qi, 127) as usize) as i32],
                y2: [
                    dc_table(clip(qi + q.dqy2_dc, 127) as usize) as i32 * 2,
                    if y2ac < 8 {
                        8
                    } else {
                        y2ac
                    },
                ],
                uv: [
                    dc_table(clip(qi + q.dquv_dc, 117) as usize) as i32,
                    ac_table(clip(qi + q.dquv_ac, 127) as usize) as i32,
                ],
            };
            proof {
                if m {
                    assert(qi == seg_qindex(fh, i as int));
                    assert(quant_matches(mq, seg_quant(fh, i as int)));
                }
            }
            dqm[i] = mq;
        }
        i = i + 1;
    }
    dqm
}

/// `PrecomputeFilterStrengths`: by `[segment][is_i4x4]`, flattened.
#[verifier::loop_isolation(false)]
fn build_fstrengths(seg: &SegRaw, fl: &FiltRaw, filter_type: u32, Ghost(fh): Ghost<FrameHeader>) -> (fstrengths: [FInfo;
    8])
    requires
        seg.ok(),
        fl.ok(),
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] finfo_ok(fstrengths@[j]),
        seg.matches(fh.seg) && fl.matches(fh.filter) && filter_type > 0 ==> forall|j: int|
            0 <= j < 8 ==> finfo_matches(#[trigger] fstrengths@[j], fh, j / 2, j % 2 == 1),
{
    let ghost m = seg.matches(fh.seg) && fl.matches(fh.filter);
    let f0 = FInfo { limit: 0, ilevel: 0, hev_thresh: 0, inner: false };
    let mut fstrengths: [FInfo; 8] = [f0; 8];
    if filter_type > 0 {
        let mut s: usize = 0;
        while s < 4
            invariant
                s <= 4,
                forall|j: int| 0 <= j < 8 ==> #[trigger] finfo_ok(fstrengths@[j]),
                m ==> forall|j: int|
                    0 <= j < 2 * s ==> finfo_matches(#[trigger] fstrengths@[j], fh, j / 2, j % 2 == 1),
            decreases 4 - s,
        {
            proof {
                assert(-255 <= seg.fstrength@[s as int] <= 255);
            }
            let base_level: i32 = if seg.use_segment {
                if seg.absolute_delta {
                    seg.fstrength[s]
                } else {
                    seg.fstrength[s] + fl.level
                }
            } else {
                fl.level
            };
            let mut i4x4: usize = 0;
            while i4x4 <= 1
                invariant
                    s < 4,
                    i4x4 <= 2,
                    -510 <= base_level <= 510,
                    forall|j: int| 0 <= j < 8 ==> #[trigger] finfo_ok(fstrengths@[j]),
                    m ==> forall|j: int|
                        0 <= j < 2 * s + i4x4 ==> finfo_matches(#[trigger] fstrengths@[j], fh, j / 2, j % 2 == 1),
                decreases 2 - i4x4,
            {
                let mut lv = base_level;
                if fl.use_lf_delta {
                    lv = lv + fl.ref_lf_delta0;
                    if i4x4 == 1 {
                        lv = lv + fl.mode_lf_delta0;
                    }
                }
                lv = if lv < 0 {
                    0
                } else if lv > 63 {
                    63
                } else {
                    lv
                };
                let info = if lv > 0 {
                    let mut ilevel = lv;
                    if fl.sharpness > 0 {
                        if fl.sharpness > 4 {
                            ilevel = ilevel / 4;
                        } else {
                            ilevel = ilevel / 2;
                        }
                        if ilevel > 9 - fl.sharpness {
                            ilevel = 9 - fl.sharpness;
                        }
                    }
                    if ilevel < 1 {
                        ilevel = 1;
                    }
                    FInfo {
                        limit: 2 * lv + ilevel,
                        ilevel,
                        hev_thresh: if lv >= 40 {
                            2
                        } else if lv >= 15 {
                            1
                        } else {
                            0
                        },
                        inner: i4x4 == 1,
                    }
                } else {
                    FInfo { limit: 0, ilevel: 0, hev_thresh: 0, inner: i4x4 == 1 }
                };
                proof {
                    let j = (2 * s + i4x4) as int;
                    assert(j / 2 == s && (j % 2 == 1) == (i4x4 == 1));
                    if m {
                        assert(lv == seg_filter_level(fh, s as int, i4x4 == 1));
                        assert(finfo_matches(info, fh, s as int, i4x4 == 1));
                    }
                }
                fstrengths[2 * s + i4x4] = info;
                i4x4 = i4x4 + 1;
            }
            s = s + 1;
        }
    }
    fstrengths
}

/// The token probabilities (`VP8ParseProba`'s main loop).
#[verifier::loop_isolation(false)]
fn parse_token_probs(br: &mut BoolReader, data: &[u8], Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (proba:
    Vec<u8>)
    requires
        old(br).inv(data@.len()),
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        proba@.len() == 1056,
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = token_probs(part(data@, p0, old(br).end as int), g, 1056);
            final(br).rel(data@, p0, x.0) && forall|k: int| 0 <= k < 1056 ==> #[trigger] proba@[k] == x.1[k]
        },
{
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g);
    let mut proba: Vec<u8> = Vec::with_capacity(1056);
    let mut k: usize = 0;
    while k < 1056
        invariant
            k <= 1056,
            proba@.len() == k,
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            ok0 && !br.eof ==> br.rel(data@, p0, token_probs(pt, g, k as nat).0),
            token_probs(pt, g, k as nat).1.len() == k,
            ok0 && !br.eof ==> forall|j: int| 0 <= j < k ==> #[trigger] proba@[j] == token_probs(pt, g, k as nat).1[j],
        decreases 1056 - k,
    {
        let ghost c = token_probs(pt, g, k as nat);
        let ghost up = spec_coeffs_update_proba(k as int) as int;
        let v = if br.get_bit(data, coeffs_update_proba(k)) {
            br.get_value(data, 8) as u8
        } else {
            coeffs_proba0(k)
        };
        proof {
            assert((k + 1 - 1) as nat == k as nat);
            let s2 = bool_next(pt, c.0, up);
            let nx = if bool_bit(c.0, up) {
                bool_literal(pt, s2, 8)
            } else {
                (s2, spec_coeffs_proba0(k as int) as int)
            };
            assert(token_probs(pt, g, (k + 1) as nat) == (nx.0, c.1.push(nx.1)));
            assert(ok0 && !br.eof ==> br.rel(data@, p0, nx.0) && v == nx.1);
        }
        proba.push(v);
        k = k + 1;
    }
    proba
}

/// `ParsePartitions`: the byte ranges of the token partitions, from the
/// size table at `pstart`.
fn parse_partitions(data: &[u8], pstart: usize, num_parts: usize) -> (r: Option<([usize; 8], [usize; 8])>)
    requires
        pstart <= data@.len(),
        1 <= num_parts <= 8,
    ensures
        r matches Some((part_start, part_end)) ==> {
            &&& forall|i: int| 0 <= i < num_parts ==> #[trigger] part_start@[i] <= part_end@[i] <= data@.len()
            &&& forall|i: int|
                0 <= i < num_parts ==> #[trigger] part_start@[i] == part_begin(
                    data@,
                    pstart as int,
                    num_parts - 1,
                    i as nat,
                )
            &&& forall|i: int|
                0 <= i < num_parts - 1 ==> #[trigger] part_end@[i] == part_begin(
                    data@,
                    pstart as int,
                    num_parts - 1,
                    (i + 1) as nat,
                )
            &&& part_end@[num_parts - 1] == data@.len()
        },
{
    proof {
        assert(data@.len() == data.len());
    }
    let n = data.len();
    let size = n - pstart;
    let last_part = num_parts - 1;
    if size < 3 * last_part {
        return None;
    }
    let mut part_start: [usize; 8] = [0; 8];
    let mut part_end: [usize; 8] = [0; 8];
    let mut part = pstart + 3 * last_part;
    let mut size_left = size - 3 * last_part;
    let mut p: usize = 0;
    while p < last_part
        invariant
            n == data@.len(),
            last_part == num_parts - 1,
            last_part < 8,
            p <= last_part,
            part + size_left == n,
            pstart + 3 * last_part <= part,
            part == part_begin(data@, pstart as int, last_part as int, p as nat),
            forall|i: int| 0 <= i < p ==> #[trigger] part_start@[i] <= part_end@[i] <= n,
            forall|i: int|
                0 <= i < p ==> #[trigger] part_start@[i] == part_begin(data@, pstart as int, last_part as int, i as nat),
            forall|i: int|
                0 <= i < p ==> #[trigger] part_end@[i] == part_begin(
                    data@,
                    pstart as int,
                    last_part as int,
                    (i + 1) as nat,
                ),
        decreases last_part - p,
    {
        let sz = pstart + 3 * p;
        let mut psize = get(data, sz) as usize + (get(data, sz + 1) as usize) * 256 + (get(data, sz + 2) as usize)
            * 65536;
        proof {
            assert(psize == le24(data@, sz as int));
            assert((p + 1 - 1) as nat == p as nat);
        }
        if psize > size_left {
            psize = size_left;
        }
        part_start[p] = part;
        part_end[p] = part + psize;
        part = part + psize;
        size_left = size_left - psize;
        p = p + 1;
    }
    part_start[last_part] = part;
    part_end[last_part] = n;
    if size_left == 0 {
        return None;
    }
    Some((part_start, part_end))
}

/// `VP8GetHeaders`, from the VP8 frame tag at `data[off]` to the end of the
/// file (libwebp hands the decoder everything after the chunk header).
/// Returns the header and the reader of the first partition.
///
/// The header is the one the specification (`vp8spec::frame_header`, RFC
/// 6386 sections 9 and 19.2) reads from the first partition, and the
/// reader is left where the specification's is, whenever the partition's
/// code word starts inside the coder's range (`bool_wf`) and the reads
/// have stayed inside the partition.
#[verifier::loop_isolation(false)]
#[verifier::rlimit(100)]
pub fn parse_header(data: &[u8], off: usize) -> (r: Result<(Header, BoolReader), Error>)
    requires
        off <= data@.len(),
    ensures
        r matches Ok((h, br)) ==> {
            &&& h.ok(data@.len())
            &&& br.inv(data@.len())
            &&& off + 10 <= data@.len()
            &&& h.width == frame_width(data@, off as int)
            &&& h.height == frame_height(data@, off as int)
            &&& br.end == off + 10 + first_part_size(data@, off as int)
            &&& {
                let pt = part(data@, off + 10, br.end as int);
                !br.eof && bool_wf(bool_init(pt)) ==> {
                    let x = frame_header(pt, bool_init(pt));
                    br.rel(data@, off + 10, x.0) && h.matches(data@, br.end as int, x.1)
                }
            }
        },
{
    proof {
        assert(data@.len() == data.len());
    }
    let n = data.len();
    if n - off < 10 {
        return Err(Error::Bitstream);
    }
    let b0 = get(data, off);
    let b1 = get(data, off + 1);
    let b2 = get(data, off + 2);
    let bits = b0 as u32 | (b1 as u32) << 8u32 | (b2 as u32) << 16u32;
    let key_frame = bits & 1 == 0;
    let profile = (bits >> 1u32) & 7;
    let show = (bits >> 4u32) & 1;
    let partition_length = (bits >> 5u32) as usize;
    proof {
        assert(((b0 as u32 | (b1 as u32) << 8u32 | (b2 as u32) << 16u32) >> 5u32) == (b0 as u32 + 256 * (b1 as u32)
            + 65536 * (b2 as u32)) / 32) by (bit_vector);
        assert(partition_length == first_part_size(data@, off as int));
    }
    if profile > 3 || show == 0 || !key_frame {
        return Err(Error::Bitstream);
    }
    if get(data, off + 3) != 0x9d || get(data, off + 4) != 0x01 || get(data, off + 5) != 0x2a {
        return Err(Error::Bitstream);
    }
    let width = (get(data, off + 7) as usize % 64) * 256 + get(data, off + 6) as usize;
    let height = (get(data, off + 9) as usize % 64) * 256 + get(data, off + 8) as usize;
    if width == 0 || height == 0 {
        return Err(Error::Bitstream);
    }
    let p0 = off + 10;
    if partition_length > n - p0 {
        return Err(Error::Bitstream);
    }
    let mut br = BoolReader::new(data, p0, p0 + partition_length);
    let ghost gp = p0 as int;
    let ghost pt = part(data@, gp, (p0 + partition_length) as int);
    let ghost g0 = bool_init(pt);
    let ghost wf = bool_wf(g0);
    let ghost fhx = frame_header(pt, g0);
    let ghost fh = fhx.1;
    // Color space and clamping type: read, not used (libwebp ignores them).
    let _colorspace = br.get_bit(data, 0x80);
    let _clamp = br.get_bit(data, 0x80);
    let ghost g2 = rd_flag(pt, rd_flag(pt, g0).0).0;
    proof {
        assert(wf && !br.eof ==> br.rel(data@, gp, g2));
    }

    let seg = parse_segment(&mut br, data, Ghost(gp), Ghost(g2));
    let ghost g3 = seg_header(pt, g2).0;
    if br.eof {
        return Err(Error::Bitstream);
    }
    let fl = parse_filter(&mut br, data, Ghost(gp), Ghost(g3));
    let ghost g4 = filter_header(pt, g3).0;
    let filter_type: u32 = if fl.level == 0 {
        0
    } else if fl.simple {
        1
    } else {
        2
    };
    if br.eof {
        return Err(Error::Bitstream);
    }
    proof {
        assert(wf ==> br.rel(data@, gp, g4) && seg.matches(fh.seg) && fl.matches(fh.filter));
        assert(p2(2) == 4) by (compute);
    }

    // Partitions.
    let pstart = p0 + partition_length;
    let lp = br.get_value(data, 2) % 4;
    let ghost g5 = bool_literal(pt, g4, 2).0;
    let num_parts: usize = if lp == 0 {
        1
    } else if lp == 1 {
        2
    } else if lp == 2 {
        4
    } else {
        8
    };
    let (part_start, part_end) = match parse_partitions(data, pstart, num_parts) {
        Some(x) => x,
        None => {
            return Err(Error::Bitstream);
        },
    };

    // Quantizers.
    let q = parse_quant_indices(&mut br, data, Ghost(gp), Ghost(g5));
    let ghost g6 = quant_header(pt, g5).0;
    proof {
        assert(wf && !br.eof ==> br.rel(data@, gp, g6) && q.matches(fh.quant) && lp == fh.log2_parts);
    }
    let dqm = build_dqm(&seg, &q, Ghost(fh));

    // Token probabilities.
    let _update_proba = br.get_bit(data, 0x80);
    let ghost g7 = rd_flag(pt, g6).0;
    let proba = parse_token_probs(&mut br, data, Ghost(gp), Ghost(g7));
    let ghost g8 = token_probs(pt, g7, 1056).0;
    let use_skip_proba = br.get_bit(data, 0x80);
    let skip_p = if use_skip_proba {
        br.get_value(data, 8) as u8
    } else {
        0
    };

    // Loop filter strengths.
    let fstrengths = build_fstrengths(&seg, &fl, filter_type, Ghost(fh));

    let hdr = Header {
        width,
        height,
        mb_w: (width + 15) / 16,
        mb_h: (height + 15) / 16,
        update_map: seg.update_map,
        seg_probs: seg.seg_probs,
        filter_type,
        fstrengths,
        dqm,
        proba,
        use_skip_proba,
        skip_p,
        num_parts,
        part_start,
        part_end,
    };
    proof {
        if wf && !br.eof {
            assert(br.rel(data@, gp, fhx.0));
            assert(hdr.matches(data@, pstart as int, fh));
        }
    }
    Ok((hdr, br))
}

/// The intra modes of one macroblock (`VP8MBData` without the coefficients).
pub struct MbModes {
    pub segment: usize,
    pub skip: bool,
    pub is_i4x4: bool,
    /// The 16x16 mode in `imodes[0]`, or the sixteen 4x4 modes.
    pub imodes: [u8; 16],
    pub uvmode: u8,
}

/// Four subblock modes of a context, as the specification holds them.
pub open spec fn ctx4(sq: Seq<u8>, off: int) -> Seq<int> {
    Seq::new(4, |i: int| sq[off + i] as int)
}

impl MbModes {
    pub open spec fn matches(&self, m: MbModeSpec) -> bool {
        &&& self.segment == m.segment
        &&& self.skip == m.skip
        &&& self.is_i4x4 == m.is_i4x4
        &&& self.uvmode == m.uvmode
        &&& !self.is_i4x4 ==> self.imodes@[0] == m.ymode
        &&& self.is_i4x4 ==> m.bmodes.len() == 16 && forall|i: int|
            0 <= i < 16 ==> #[trigger] self.imodes@[i] == m.bmodes[i]
    }
}

impl Header {
    /// The fields the macroblock headers depend on are the specification's.
    pub open spec fn mode_matches(&self, fh: FrameHeader) -> bool {
        &&& self.update_map == fh.seg.update_map
        &&& forall|j: int| 0 <= j < 3 ==> #[trigger] self.seg_probs@[j] == fh.seg.probs[j]
        &&& self.use_skip_proba == fh.mb_no_coeff_skip
        &&& self.skip_p == fh.prob_skip_false
    }
}

/// One subblock mode, with the nine tree probabilities at `pb`.
#[inline(always)]
fn read_bmode(br: &mut BoolReader, data: &[u8], pb: usize, Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (m:
    usize)
    requires
        old(br).inv(data@.len()),
        pb + 9 <= 900,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        m < 10,
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = rd_bmode(part(data@, p0, old(br).end as int), g, pb as int);
            final(br).rel(data@, p0, x.0) && m == x.1
        },
{
    if !br.get_bit(data, bmodes_proba(pb)) {
        0
    } else if !br.get_bit(data, bmodes_proba(pb + 1)) {
        1
    } else if !br.get_bit(data, bmodes_proba(pb + 2)) {
        2
    } else if !br.get_bit(data, bmodes_proba(pb + 3)) {
        if !br.get_bit(data, bmodes_proba(pb + 4)) {
            3
        } else if !br.get_bit(data, bmodes_proba(pb + 5)) {
            4
        } else {
            5
        }
    } else if !br.get_bit(data, bmodes_proba(pb + 6)) {
        6
    } else if !br.get_bit(data, bmodes_proba(pb + 7)) {
        7
    } else if !br.get_bit(data, bmodes_proba(pb + 8)) {
        8
    } else {
        9
    }
}

/// The sixteen subblock modes of a `B_PRED` macroblock.
#[inline(always)]
#[verifier::loop_isolation(false)]
#[verifier::rlimit(50)]
fn read_bmodes(
    br: &mut BoolReader,
    data: &[u8],
    top: &mut Vec<u8>,
    left: &mut [u8; 4],
    mb_x: usize,
    Ghost(p0): Ghost<int>,
    Ghost(g): Ghost<BoolState>,
) -> (imodes: [u8; 16])
    requires
        old(br).inv(data@.len()),
        4 * mb_x + 4 <= old(top)@.len(),
        forall|i: int| 0 <= i < old(top)@.len() ==> old(top)@[i] < 10,
        forall|i: int| 0 <= i < 4 ==> old(left)@[i] < 10,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(top)@.len() == old(top)@.len(),
        forall|i: int| 0 <= i < final(top)@.len() ==> final(top)@[i] < 10,
        forall|i: int| 0 <= i < 4 ==> final(left)@[i] < 10,
        forall|i: int| 0 <= i < 16 ==> imodes@[i] < 10,
        forall|j: int|
            0 <= j < final(top)@.len() && !(4 * mb_x <= j < 4 * mb_x + 4) ==> final(top)@[j] == old(top)@[j],
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let b = rd_bmodes(
                part(data@, p0, old(br).end as int),
                g,
                ctx4(old(top)@, 4 * mb_x),
                ctx4(old(left)@, 0),
                16,
            );
            &&& final(br).rel(data@, p0, b.s)
            &&& b.modes.len() == 16
            &&& forall|i: int| 0 <= i < 16 ==> #[trigger] imodes@[i] == b.modes[i]
            &&& forall|i: int| 0 <= i < 4 ==> #[trigger] final(top)@[4 * mb_x + i] == b.top[i]
            &&& forall|i: int| 0 <= i < 4 ==> #[trigger] final(left)@[i] == b.left[i]
        },
{
    proof {
        assert(data@.len() == data.len());
        assert(top@.len() == top.len());
    }
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g);
    let ghost t0 = ctx4(top@, 4 * mb_x);
    let ghost l0 = ctx4(left@, 0);
    let mut imodes: [u8; 16] = [0; 16];
    let mut y: usize = 0;
    while y < 4
        invariant
            data@.len() <= usize::MAX,
            y <= 4,
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            4 * mb_x + 4 <= top@.len(),
            top@.len() == old(top)@.len(),
            forall|j: int| 0 <= j < top@.len() ==> top@[j] < 10,
            forall|j: int| 0 <= j < 4 ==> left@[j] < 10,
            forall|j: int| 0 <= j < 16 ==> imodes@[j] < 10,
            forall|j: int| 0 <= j < top@.len() && !(4 * mb_x <= j < 4 * mb_x + 4) ==> top@[j] == old(top)@[j],
            rd_bmodes(pt, g, t0, l0, (4 * y) as nat).modes.len() == 4 * y,
            rd_bmodes(pt, g, t0, l0, (4 * y) as nat).top.len() == 4,
            rd_bmodes(pt, g, t0, l0, (4 * y) as nat).left.len() == 4,
            ok0 && !br.eof ==> {
                let st = rd_bmodes(pt, g, t0, l0, (4 * y) as nat);
                &&& br.rel(data@, p0, st.s)
                &&& forall|j: int| 0 <= j < 4 * y ==> #[trigger] imodes@[j] == st.modes[j]
                &&& forall|j: int| 0 <= j < 4 ==> #[trigger] top@[4 * mb_x + j] == st.top[j]
                &&& forall|j: int| 0 <= j < 4 ==> #[trigger] left@[j] == st.left[j]
            },
        decreases 4 - y,
    {
        let mut ymode = left[y] as usize;
        let mut x: usize = 0;
        while x < 4
            invariant
                data@.len() <= usize::MAX,
                x <= 4,
                y < 4,
                ymode < 10,
                br.inv(data@.len()),
                br.end == old(br).end,
                old(br).eof ==> br.eof,
                4 * mb_x + 4 <= top@.len(),
                top@.len() == old(top)@.len(),
                forall|j: int| 0 <= j < top@.len() ==> top@[j] < 10,
                forall|j: int| 0 <= j < 4 ==> left@[j] < 10,
                forall|j: int| 0 <= j < 16 ==> imodes@[j] < 10,
                forall|j: int| 0 <= j < top@.len() && !(4 * mb_x <= j < 4 * mb_x + 4) ==> top@[j] == old(top)@[j],
                rd_bmodes(pt, g, t0, l0, (4 * y + x) as nat).modes.len() == 4 * y + x,
                rd_bmodes(pt, g, t0, l0, (4 * y + x) as nat).top.len() == 4,
                rd_bmodes(pt, g, t0, l0, (4 * y + x) as nat).left.len() == 4,
                ok0 && !br.eof ==> {
                    let st = rd_bmodes(pt, g, t0, l0, (4 * y + x) as nat);
                    &&& br.rel(data@, p0, st.s)
                    &&& forall|j: int| 0 <= j < 4 * y + x ==> #[trigger] imodes@[j] == st.modes[j]
                    &&& forall|j: int| 0 <= j < 4 ==> #[trigger] top@[4 * mb_x + j] == st.top[j]
                    &&& forall|j: int| 0 <= j < 4 && j != y ==> #[trigger] left@[j] == st.left[j]
                    &&& x < 4 ==> left@[y as int] == st.left[y as int]
                    &&& ymode == (if x == 0 {
                        st.left[y as int]
                    } else {
                        st.modes[4 * y + x - 1]
                    })
                },
            decreases 4 - x,
        {
            let ghost n = (4 * y + x) as nat;
            let ghost st = rd_bmodes(pt, g, t0, l0, n);
            let t = top[4 * mb_x + x] as usize;
            let pb = (t * 10 + ymode) * 9;
            ymode = read_bmode(br, data, pb, Ghost(p0), Ghost(st.s));
            store_at(top, 4 * mb_x + x, ymode as u8);
            imodes[4 * y + x] = ymode as u8;
            proof {
                assert(n / 4 == y && n % 4 == x) by (nonlinear_arith)
                    requires
                        n == 4 * y + x,
                        x < 4,
                ;
                assert((n + 1 - 1) as nat == n);
                let st2 = bmode_step(pt, st, n);
                assert(rd_bmodes(pt, g, t0, l0, (n + 1) as nat) == st2);
                assert((4 * y + (x + 1)) as nat == (n + 1) as nat);
                if ok0 && !br.eof {
                    assert(t == st.top[x as int]);
                    assert(ymode == st2.modes[n as int]);
                    assert(forall|j: int| 0 <= j < n + 1 ==> #[trigger] imodes@[j] == st2.modes[j]);
                    assert(forall|j: int| 0 <= j < 4 ==> #[trigger] top@[4 * mb_x + j] == st2.top[j]);
                }
            }
            x = x + 1;
        }
        left[y] = ymode as u8;
        proof {
            assert((4 * (y + 1)) as nat == (4 * y + 4) as nat);
        }
        y = y + 1;
    }
    imodes
}

/// `ParseIntraMode`: the modes of macroblock `mb_x`. `top` holds four
/// 4x4 modes per macroblock column (the bottom row of the one above),
/// `left` the right column of the macroblock to the left.
///
/// They are the modes `vp8spec::mb_modes` reads (RFC 6386 sections 9.3,
/// 9.11 and 11), when the header is the specification's `fh` and the
/// reader is at the specification's state `g`.
#[verifier::loop_isolation(false)]
#[verifier::rlimit(50)]
pub fn parse_intra_mode(
    br: &mut BoolReader,
    data: &[u8],
    hdr: &Header,
    top: &mut Vec<u8>,
    left: &mut [u8; 4],
    mb_x: usize,
    Ghost(p0): Ghost<int>,
    Ghost(g): Ghost<BoolState>,
    Ghost(fh): Ghost<FrameHeader>,
) -> (m: MbModes)
    requires
        old(br).inv(data@.len()),
        4 * mb_x + 4 <= old(top)@.len(),
        forall|i: int| 0 <= i < old(top)@.len() ==> old(top)@[i] < 10,
        forall|i: int| 0 <= i < 4 ==> old(left)@[i] < 10,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(top)@.len() == old(top)@.len(),
        forall|i: int| 0 <= i < final(top)@.len() ==> final(top)@[i] < 10,
        forall|i: int| 0 <= i < 4 ==> final(left)@[i] < 10,
        m.segment < 4,
        m.uvmode < 4,
        forall|i: int| 0 <= i < 16 ==> m.imodes@[i] < 10,
        !m.is_i4x4 ==> m.imodes@[0] < 4,
        forall|j: int|
            0 <= j < final(top)@.len() && !(4 * mb_x <= j < 4 * mb_x + 4) ==> final(top)@[j] == old(top)@[j],
        old(br).rel(data@, p0, g) && hdr.mode_matches(fh) && !final(br).eof ==> {
            let o = mb_modes(
                part(data@, p0, old(br).end as int),
                g,
                fh,
                ctx4(old(top)@, 4 * mb_x),
                ctx4(old(left)@, 0),
            );
            &&& final(br).rel(data@, p0, o.s)
            &&& m.matches(o.m)
            &&& forall|i: int| 0 <= i < 4 ==> #[trigger] final(top)@[4 * mb_x + i] == o.top[i]
            &&& forall|i: int| 0 <= i < 4 ==> #[trigger] final(left)@[i] == o.left[i]
        },
{
    proof {
        assert(data@.len() == data.len());
        assert(top@.len() == top.len());
    }
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g) && hdr.mode_matches(fh);
    let ghost t0 = ctx4(top@, 4 * mb_x);
    let ghost l0 = ctx4(left@, 0);
    let segment: usize = if hdr.update_map {
        if !br.get_bit(data, hdr.seg_probs[0]) {
            br.get_bit(data, hdr.seg_probs[1]) as usize
        } else {
            br.get_bit(data, hdr.seg_probs[2]) as usize + 2
        }
    } else {
        0
    };
    let ghost s1 = mb_segment(pt, g, fh).0;
    proof {
        assert(ok0 && !br.eof ==> br.rel(data@, p0, s1) && segment == mb_segment(pt, g, fh).1);
    }
    let skip = if hdr.use_skip_proba {
        br.get_bit(data, hdr.skip_p)
    } else {
        false
    };
    let ghost s2 = mb_skip(pt, s1, fh).0;
    proof {
        assert(ok0 && !br.eof ==> br.rel(data@, p0, s2) && skip == mb_skip(pt, s1, fh).1);
    }
    let is_i4x4 = !br.get_bit(data, 145);
    let ghost s3 = rd_bool(pt, s2, 145).0;
    proof {
        assert(ok0 && !br.eof ==> br.rel(data@, p0, s3) && !is_i4x4 == rd_bool(pt, s2, 145).1);
    }
    let mut imodes: [u8; 16] = [0; 16];
    let ghost mut cur = s3;
    if !is_i4x4 {
        let ymode: u8 = if br.get_bit(data, 156) {
            if br.get_bit(data, 128) {
                1
            } else {
                3
            }
        } else {
            if br.get_bit(data, 163) {
                2
            } else {
                0
            }
        };
        proof {
            cur = kf_ymode(pt, s3).0;
            assert(ok0 && !br.eof ==> br.rel(data@, p0, cur) && ymode == kf_ymode(pt, s3).1);
        }
        imodes[0] = ymode;
        let mut i: usize = 0;
        while i < 4
            invariant
                data@.len() <= usize::MAX,
                i <= 4,
                ymode < 4,
                4 * mb_x + 4 <= top@.len(),
                top@.len() == old(top)@.len(),
                forall|j: int| 0 <= j < top@.len() ==> top@[j] < 10,
                forall|j: int| 0 <= j < 4 ==> left@[j] < 10,
                forall|j: int| 0 <= j < top@.len() && !(4 * mb_x <= j < 4 * mb_x + 4) ==> top@[j] == old(top)@[j],
                forall|j: int| 0 <= j < i ==> #[trigger] top@[4 * mb_x + j] == ymode,
                forall|j: int| 0 <= j < i ==> #[trigger] left@[j] == ymode,
            decreases 4 - i,
        {
            store_at(top, 4 * mb_x + i, ymode);
            left[i] = ymode;
            i = i + 1;
        }
    } else {
        imodes = read_bmodes(br, data, top, left, mb_x, Ghost(p0), Ghost(s3));
        proof {
            cur = rd_bmodes(pt, s3, t0, l0, 16).s;
        }
    }
    let ghost b4 = *br;
    let uvmode: u8 = if !br.get_bit(data, 142) {
        0
    } else if !br.get_bit(data, 114) {
        2
    } else if br.get_bit(data, 183) {
        1
    } else {
        3
    };
    let m = MbModes { segment, skip, is_i4x4, imodes, uvmode };
    proof {
        if ok0 && !br.eof {
            let o = mb_modes(pt, g, fh, t0, l0);
            assert(b4.rel(data@, p0, cur));
            assert(br.rel(data@, p0, uv_mode(pt, cur).0) && uvmode == uv_mode(pt, cur).1);
            assert(o.s == uv_mode(pt, cur).0);
            assert(m.matches(o.m));
        }
    }
    m
}

/// The modes of a macroblock are in range.
pub open spec fn modes_ok(m: MbModes) -> bool {
    &&& m.segment < 4
    &&& m.uvmode < 4
    &&& forall|i: int| 0 <= i < 16 ==> m.imodes@[i] < 10
    &&& !m.is_i4x4 ==> m.imodes@[0] < 4
}

/// A mode context as the specification holds it.
pub open spec fn ctxn(sq: Seq<u8>) -> Seq<int> {
    Seq::new(sq.len(), |i: int| sq[i] as int)
}

/// `VP8ParseIntraModeRow`: the modes of one row of `mb_w` macroblocks,
/// into `modes`. They are the ones `vp8spec::row_modes` reads.
#[verifier::loop_isolation(false)]
pub fn parse_mode_row(
    br: &mut BoolReader,
    data: &[u8],
    hdr: &Header,
    top: &mut Vec<u8>,
    modes: &mut Vec<MbModes>,
    mb_w: usize,
    Ghost(p0): Ghost<int>,
    Ghost(g): Ghost<BoolState>,
    Ghost(fh): Ghost<FrameHeader>,
)
    requires
        old(br).inv(data@.len()),
        old(top)@.len() == 4 * mb_w,
        forall|i: int| 0 <= i < old(top)@.len() ==> old(top)@[i] < 10,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(top)@.len() == 4 * mb_w,
        forall|i: int| 0 <= i < final(top)@.len() ==> final(top)@[i] < 10,
        final(modes)@.len() == mb_w,
        forall|j: int| 0 <= j < mb_w ==> #[trigger] modes_ok(final(modes)@[j]),
        old(br).rel(data@, p0, g) && hdr.mode_matches(fh) && !final(br).eof ==> {
            let r = row_modes(part(data@, p0, old(br).end as int), g, fh, ctxn(old(top)@), mb_w as nat);
            &&& final(br).rel(data@, p0, r.s)
            &&& forall|j: int| 0 <= j < mb_w ==> (#[trigger] final(modes)@[j]).matches(r.mbs[j])
            &&& ctxn(final(top)@) == r.top
        },
{
    hide(mb_modes);
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g) && hdr.mode_matches(fh);
    let ghost t0 = ctxn(top@);
    let mut left_modes: [u8; 4] = [0; 4];
    modes.clear();
    let mut mb_x: usize = 0;
    while mb_x < mb_w
        invariant
            mb_x <= mb_w,
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            modes@.len() == mb_x,
            forall|j: int| 0 <= j < mb_x ==> #[trigger] modes_ok(modes@[j]),
            top@.len() == 4 * mb_w,
            forall|j: int| 0 <= j < top@.len() ==> top@[j] < 10,
            forall|j: int| 0 <= j < 4 ==> left_modes@[j] < 10,
            ok0 && !br.eof ==> {
                let r = row_modes(pt, g, fh, t0, mb_x as nat);
                &&& br.rel(data@, p0, r.s)
                &&& forall|j: int| 0 <= j < mb_x ==> (#[trigger] modes@[j]).matches(r.mbs[j])
                &&& ctxn(top@) == r.top
                &&& ctx4(left_modes@, 0) == r.left
            },
        decreases mb_w - mb_x,
    {
        let ghost r = row_modes(pt, g, fh, t0, mb_x as nat);
        let ghost top_b = top@;
        let ghost left_b = left_modes@;
        let ghost k = mb_x as int;
        let m = parse_intra_mode(br, data, hdr, top, &mut left_modes, mb_x, Ghost(p0), Ghost(r.s), Ghost(fh));
        proof {
            lemma_row_modes_shape(pt, g, fh, t0, mb_x as nat);
            lemma_row_modes_shape(pt, g, fh, t0, (mb_x + 1) as nat);
            assert((mb_x + 1 - 1) as nat == mb_x as nat);
            let r2 = row_modes(pt, g, fh, t0, (mb_x + 1) as nat);
            if ok0 && !br.eof {
                assert(ctx4(top_b, 4 * k) =~= r.top.subrange(4 * k, 4 * k + 4));
                let o = mb_modes(pt, r.s, fh, r.top.subrange(4 * k, 4 * k + 4), r.left);
                lemma_mb_modes_shape(pt, r.s, fh, r.top.subrange(4 * k, 4 * k + 4), r.left);
                assert(r2 == RowModes {
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
                });
                assert(ctx4(left_modes@, 0) =~= o.left);
                assert forall|i: int| 0 <= i < 4 * mb_w implies ctxn(top@)[i] == r2.top[i] by {
                    if 4 * k <= i < 4 * k + 4 {
                        assert(top@[4 * mb_x + (i - 4 * k)] == o.top[i - 4 * k]);
                    } else {
                        assert(top@[i] == top_b[i]);
                        assert(ctxn(top_b)[i] == r.top[i]);
                    }
                }
                assert(ctxn(top@) =~= r2.top);
            }
        }
        modes.push(m);
        mb_x = mb_x + 1;
    }
}

/// `33 * BANDS[n]`: a band's offset inside one type's probabilities.
pub const BAND33: [u16; 17] = [0, 33, 66, 99, 198, 132, 165, 198, 198, 198, 198, 198, 198, 198, 198, 231, 0];

/// Where token probabilities for type `t`, coefficient `n` and context
/// `ctx` start in the flattened table.
#[inline(always)]
pub fn pidx(t: usize, n: usize, ctx: usize) -> (r: usize)
    requires
        t < 4,
        n <= 16,
        ctx < 3,
    ensures
        r + 11 <= 1056,
        r == token_pidx(t as int, n as int, ctx as int),
{
    proof {
        assert(BANDS@ =~= seq![0u8, 1, 2, 3, 6, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7, 0]);
        assert(BAND33@ =~= seq![0u16, 33, 66, 99, 198, 132, 165, 198, 198, 198, 198, 198, 198, 198, 198, 231, 0]);
        assert(BAND33@[n as int] == 33 * BANDS@[n as int]);
    }
    t * 264 + BAND33[n] as usize + ctx * 11
}

/// A token probability table as the specification holds it.
pub open spec fn probs_are(proba: Seq<u8>, pr: Seq<int>) -> bool {
    forall|k: int| 0 <= k < proba.len() ==> #[trigger] proba[k] == pr[k]
}

/// The extra bits of a `dct_cat` token, with the probabilities in `tab`.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn read_extra(br: &mut BoolReader, data: &[u8], tab: &[u8], Ghost(p0): Ghost<int>, Ghost(g): Ghost<BoolState>) -> (v:
    i32)
    requires
        old(br).inv(data@.len()),
        1 <= tab@.len() <= 11,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        0 <= v < p2(tab@.len()),
        old(br).rel(data@, p0, g) && !final(br).eof ==> {
            let x = rd_extra(part(data@, p0, old(br).end as int), g, tab@, tab@.len());
            final(br).rel(data@, p0, x.0) && v == x.1 && final(br).range <= 254
        },
{
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g);
    proof {
        assert(tab@.len() == tab.len());
        assert(p2(11) == 2048) by (compute);
        assert(p2(0) == 1) by (compute);
    }
    let n = tab.len();
    let mut v: i32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == tab@.len(),
            n <= 11,
            0 <= v < p2(i as nat),
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            ok0 && !br.eof ==> br.rel(data@, p0, rd_extra(pt, g, tab@, i as nat).0) && v == rd_extra(
                pt,
                g,
                tab@,
                i as nat,
            ).1,
            ok0 && !br.eof && i >= 1 ==> br.range <= 254,
        decreases n - i,
    {
        proof {
            lemma_p2_mono(i as nat, 11);
            assert((i + 1 - 1) as nat == i as nat);
            assert(p2((i + 1) as nat) == 2 * p2(i as nat));
        }
        v = v + v + br.get_bit(data, tab[i]) as i32;
        i = i + 1;
    }
    v
}

/// `GetLargeValue`: a token above one, from probabilities at `p`.
fn get_large_value(
    br: &mut BoolReader,
    data: &[u8],
    proba: &Vec<u8>,
    p: usize,
    Ghost(p0): Ghost<int>,
    Ghost(g): Ghost<BoolState>,
    Ghost(pr): Ghost<Seq<int>>,
) -> (v: i32)
    requires
        old(br).inv(data@.len()),
        p + 11 <= proba@.len(),
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        2 <= v <= 2048 + 66,
        old(br).rel(data@, p0, g) && probs_are(proba@, pr) && !final(br).eof ==> {
            let x = large_value(part(data@, p0, old(br).end as int), g, pr, p as int);
            final(br).rel(data@, p0, x.0) && v == x.1 && final(br).range <= 254
        },
{
    proof {
        assert(data@.len() == data.len());
        assert(proba@.len() == proba.len());
        assert(p2(3) == 8) by (compute);
        assert(p2(4) == 16) by (compute);
        assert(p2(5) == 32) by (compute);
        assert(p2(11) == 2048) by (compute);
        assert(CAT3@ =~= pcat3());
        assert(CAT4@ =~= pcat4());
        assert(CAT5@ =~= pcat5());
        assert(CAT6@ =~= pcat6());
    }
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g) && probs_are(proba@, pr);
    if !br.get_bit(data, get(proba.as_slice(), p + 3)) {
        if !br.get_bit(data, get(proba.as_slice(), p + 4)) {
            2
        } else {
            3 + br.get_bit(data, get(proba.as_slice(), p + 5)) as i32
        }
    } else {
        if !br.get_bit(data, get(proba.as_slice(), p + 6)) {
            if !br.get_bit(data, get(proba.as_slice(), p + 7)) {
                5 + br.get_bit(data, 159) as i32
            } else {
                let a = 2 * br.get_bit(data, 165) as i32;
                7 + a + br.get_bit(data, 145) as i32
            }
        } else {
            let bit1 = br.get_bit(data, get(proba.as_slice(), p + 8)) as usize;
            let bit0 = br.get_bit(data, get(proba.as_slice(), p + 9 + bit1)) as usize;
            let ghost s6 = rd_bool(pt, rd_bool(pt, g, pr[p + 3]).0, pr[p + 6]).0;
            let ghost s8 = rd_bool(pt, s6, pr[p + 8]).0;
            let ghost s9 = rd_bool(pt, s8, pr[p + 9 + bit1]).0;
            proof {
                assert(ok0 && !br.eof ==> br.rel(data@, p0, s9) && (bit1 == 1) == rd_bool(pt, s6, pr[p + 8]).1 && (bit0
                    == 1) == rd_bool(pt, s8, pr[p + 9 + bit1]).1);
            }
            let cat = 2 * bit1 + bit0;
            if cat == 0 {
                read_extra(br, data, &CAT3, Ghost(p0), Ghost(s9)) + 3 + 8
            } else if cat == 1 {
                read_extra(br, data, &CAT4, Ghost(p0), Ghost(s9)) + 3 + 16
            } else if cat == 2 {
                read_extra(br, data, &CAT5, Ghost(p0), Ghost(s9)) + 3 + 32
            } else {
                read_extra(br, data, &CAT6, Ghost(p0), Ghost(s9)) + 3 + 64
            }
        }
    }
}

/// A block of sixteen coefficients as the specification holds it.
pub open spec fn blk16(out: Seq<i16>, o: int) -> Seq<int> {
    Seq::new(16, |i: int| out[o + i] as int)
}

/// `GetCoeffs`: the tokens of one 4x4 block of type `t`, from coefficient
/// `n0`, dequantized and stored in zigzag order at `out[o..o + 16]`.
/// Returns the position after the last nonzero coefficient read (16 if the
/// block ran to the end).
///
/// The block and the position are the ones `vp8spec::block_tokens` (RFC
/// 6386 section 13) reads.
pub fn get_coeffs(
    br: &mut BoolReader,
    data: &[u8],
    proba: &Vec<u8>,
    t: usize,
    ctx: usize,
    dq: [i32; 2],
    n0: usize,
    out: &mut [i16],
    o: usize,
    Ghost(p0): Ghost<int>,
    Ghost(g): Ghost<BoolState>,
    Ghost(pr): Ghost<Seq<int>>,
) -> (r: usize)
    requires
        old(br).inv(data@.len()),
        proba@.len() == 1056,
        t < 4,
        ctx < 3,
        n0 <= 1,
        o + 16 <= old(out)@.len(),
        0 <= dq[0] <= 1024,
        0 <= dq[1] <= 1024,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(out)@.len() == old(out)@.len(),
        n0 <= r <= 16,
        forall|j: int| 0 <= j < final(out)@.len() && !(o <= j < o + 16) ==> final(out)@[j] == old(out)@[j],
        old(br).rel(data@, p0, g) && probs_are(proba@, pr) && !final(br).eof ==> {
            let x = block_tokens(
                part(data@, p0, old(br).end as int),
                g,
                pr,
                t as int,
                n0 as int,
                ctx as int,
                true,
                dq[0] as int,
                dq[1] as int,
                blk16(old(out)@, o as int),
            );
            &&& final(br).rel(data@, p0, x.0)
            &&& blk16(final(out)@, o as int) == x.1
            &&& r == x.2
        },
{
    // A local copy, which stays in registers across the bit reads.
    let mut b = *br;
    let r = get_coeffs_in(&mut b, data, proba, t, ctx, dq, n0, out, o, Ghost(p0), Ghost(g), Ghost(pr));
    *br = b;
    r
}

#[inline(always)]
#[verifier::loop_isolation(false)]
fn get_coeffs_in(
    br: &mut BoolReader,
    data: &[u8],
    proba: &Vec<u8>,
    t: usize,
    ctx: usize,
    dq: [i32; 2],
    n0: usize,
    out: &mut [i16],
    o: usize,
    Ghost(p0): Ghost<int>,
    Ghost(g): Ghost<BoolState>,
    Ghost(pr): Ghost<Seq<int>>,
) -> (r: usize)
    requires
        old(br).inv(data@.len()),
        proba@.len() == 1056,
        t < 4,
        ctx < 3,
        n0 <= 1,
        o + 16 <= old(out)@.len(),
        0 <= dq[0] <= 1024,
        0 <= dq[1] <= 1024,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(out)@.len() == old(out)@.len(),
        n0 <= r <= 16,
        forall|j: int| 0 <= j < final(out)@.len() && !(o <= j < o + 16) ==> final(out)@[j] == old(out)@[j],
        old(br).rel(data@, p0, g) && probs_are(proba@, pr) && !final(br).eof ==> {
            let x = block_tokens(
                part(data@, p0, old(br).end as int),
                g,
                pr,
                t as int,
                n0 as int,
                ctx as int,
                true,
                dq[0] as int,
                dq[1] as int,
                blk16(old(out)@, o as int),
            );
            &&& final(br).rel(data@, p0, x.0)
            &&& blk16(final(out)@, o as int) == x.1
            &&& r == x.2
        },
{
    hide(block_tokens);
    hide(large_value);
    hide(token_pidx);
    let pr_s = proba.as_slice();
    proof {
        assert(data@.len() == data.len());
        assert(out@.len() == out.len());
        assert(pr_s@ == proba@);
        assert(ZIGZAG@ =~= seq![0u8, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15]);
    }
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g) && probs_are(proba@, pr);
    let ghost d0 = dq[0] as int;
    let ghost d1 = dq[1] as int;
    let ghost ti = t as int;
    // What the specification reads for the whole block; the loop keeps
    // "the rest of the block from here" equal to it.
    let ghost total = block_tokens(pt, g, pr, ti, n0 as int, ctx as int, true, d0, d1, blk16(out@, o as int));
    let ghost mut cur = g;
    let ghost mut cx = ctx as int;
    let mut n = n0;
    let mut p = pidx(t, n, ctx);
    while n < 16
        invariant
            data@.len() <= usize::MAX,
            out@.len() <= usize::MAX,
            n0 <= n <= 16,
            p + 11 <= 1056,
            proba@.len() == 1056,
            pr_s@ == proba@,
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            out@.len() == old(out)@.len(),
            o + 16 <= out@.len(),
            0 <= dq[0] <= 1024,
            0 <= dq[1] <= 1024,
            t < 4,
            0 <= cx < 3,
            forall|j: int| 0 <= j < out@.len() && !(o <= j < o + 16) ==> out@[j] == old(out)@[j],
            ok0 && !br.eof ==> {
                &&& br.rel(data@, p0, cur)
                &&& p == token_pidx(ti, n as int, cx)
                &&& total == block_tokens(pt, cur, pr, ti, n as int, cx, true, d0, d1, blk16(out@, o as int))
            },
        decreases 16 - n,
    {
        let ghost blk = blk16(out@, o as int);
        if !br.get_bit(data, get(pr_s, p)) {
            proof {
                if ok0 && !br.eof {
                    lemma_block_tokens_unfold(pt, cur, pr, ti, n as int, cx, true, d0, d1, blk);
                    assert(total == (bool_next(pt, cur, pr[p as int]), blk, n as int));
                }
            }
            return n;
        }
        let ghost n_in = n;
        proof {
            let c0 = cur;
            cur = bool_next(pt, c0, pr[p as int]);
            if ok0 && !br.eof {
                lemma_block_tokens_unfold(pt, c0, pr, ti, n as int, cx, true, d0, d1, blk);
                lemma_block_tokens_unfold(pt, cur, pr, ti, n as int, cx, false, d0, d1, blk);
                assert(total == block_tokens(pt, cur, pr, ti, n as int, cx, false, d0, d1, blk));
            }
        }
        while !br.get_bit(data, get(pr_s, p + 1))
            invariant
                n_in <= n,
                data@.len() <= usize::MAX,
                out@.len() <= usize::MAX,
                n0 <= n < 16,
                p + 11 <= 1056,
                proba@.len() == 1056,
                pr_s@ == proba@,
                out@.len() == old(out)@.len(),
                o + 16 <= out@.len(),
                br.inv(data@.len()),
                br.end == old(br).end,
                old(br).eof ==> br.eof,
                t < 4,
                0 <= cx < 3,
                blk == blk16(out@, o as int),
                forall|j: int| 0 <= j < out@.len() && !(o <= j < o + 16) ==> out@[j] == old(out)@[j],
                ok0 && !br.eof ==> {
                    &&& br.rel(data@, p0, cur)
                    &&& p == token_pidx(ti, n as int, cx)
                    &&& total == block_tokens(pt, cur, pr, ti, n as int, cx, false, d0, d1, blk)
                },
            decreases 16 - n,
        {
            proof {
                let c2 = bool_next(pt, cur, pr[p + 1]);
                if ok0 && !br.eof {
                    lemma_block_tokens_unfold(pt, cur, pr, ti, n as int, cx, false, d0, d1, blk);
                    assert(total == block_tokens(pt, c2, pr, ti, n + 1, 0, false, d0, d1, blk));
                }
                cur = c2;
                cx = 0;
            }
            n = n + 1;
            if n == 16 {
                proof {
                    if ok0 && !br.eof {
                        lemma_block_tokens_unfold(pt, cur, pr, ti, 16, 0, false, d0, d1, blk);
                        assert(total == (cur, blk, 16int));
                    }
                }
                return 16;
            }
            p = pidx(t, n, 0);
        }
        let ghost s1 = cur;
        let ghost s2 = bool_next(pt, cur, pr[p + 1]);
        let ghost p_in = p as int;
        let ghost cx_in = cx;
        let ghost br2 = *br;
        let big = br.get_bit(data, get(pr_s, p + 2));
        let ghost s3 = bool_next(pt, s2, pr[p + 2]);
        let v: i32 = if !big {
            p = pidx(t, n + 1, 1);
            1
        } else {
            let v = get_large_value(br, data, proba, p, Ghost(p0), Ghost(s3), Ghost(pr));
            p = pidx(t, n + 1, 2);
            v
        };
        let ghost s4 = if big {
            large_value(pt, s3, pr, p_in).0
        } else {
            s3
        };
        proof {
            if ok0 && !br.eof {
                assert(br2.rel(data@, p0, s2));
                assert(br.rel(data@, p0, s4));
                assert(br.range <= 254);
            }
        }
        let ghost br4 = *br;
        let s = br.get_signed(data, v);
        let d = if n > 0 {
            dq[1]
        } else {
            dq[0]
        };
        let c = (s as i16).wrapping_mul(d as i16);
        set16(out, o + ZIGZAG[n] as usize, c);
        proof {
            let s5 = bool_next(pt, s4, 128);
            let nb = blk.update(zigzag(n as int), c as int);
            assert(blk16(out@, o as int) =~= nb);
            if ok0 && !br.eof {
                let neg = bool_bit(s4, 128);
                let sv = if neg {
                    -(v as int)
                } else {
                    v as int
                };
                assert(s == sv);
                assert(c as int == wrap16s(sv * d));
                lemma_block_tokens_unfold(pt, s1, pr, ti, n as int, cx_in, false, d0, d1, blk);
                assert(total == block_tokens(
                    pt,
                    s5,
                    pr,
                    ti,
                    n + 1,
                    if big {
                        2int
                    } else {
                        1int
                    },
                    true,
                    d0,
                    d1,
                    nb,
                ));
            }
            cur = s5;
            cx = if big {
                2
            } else {
                1
            };
        }
        n = n + 1;
    }
    proof {
        if ok0 && !br.eof {
            lemma_block_tokens_unfold(pt, cur, pr, ti, 16, cx, true, d0, d1, blk16(out@, o as int));
            assert(total == (cur, blk16(out@, o as int), 16int));
        }
    }
    16
}


/// Per-column (or left) nonzero context: four Y bits, then two U and two V
/// bits (`VP8MB::nz`), and the Y2 bit (`nz_dc`).
#[derive(Clone, Copy)]
pub struct Nz {
    pub nz: u32,
    pub nz_dc: u32,
}

/// What `ParseResiduals` leaves for reconstruction.
pub struct Residuals {
    /// Two bits per 4x4 Y block (from the top left, most significant
    /// first): 3 full transform, 2 three-coefficient, 1 DC only, 0 none.
    pub non_zero_y: u32,
    /// The same for the four U then four V blocks, U in the low byte.
    pub non_zero_uv: u32,
}

/// The transform selector of a block whose tokens ended at position `nz`
/// and whose DC is nonzero or not: 3 for the full transform, 2 for the
/// first three coefficients, 1 for the DC alone, 0 for nothing.
pub open spec fn nz_code(nz: int, dc_nz: bool) -> u32 {
    if nz > 3 {
        3
    } else if nz > 1 {
        2
    } else if dc_nz {
        1
    } else {
        0
    }
}

/// The selector of block `n` in a word that holds two bits per block, the
/// first block's at bit `top`.
pub open spec fn ycode(b: u32, top: int, n: int) -> u32 {
    (b >> ((top - 2 * n) as u32)) & 3
}

/// Selector `k` claims no more than the block `cb` bears out.
pub open spec fn ksound(k: u32, cb: Seq<int>) -> bool {
    &&& k == 0 ==> zero_blk(cb)
    &&& k <= 1 ==> only_dc(cb)
    &&& k <= 2 ==> only_ac3(cb)
}

/// The selectors in `b` of the `nblk` blocks at `buf[base..]` are sound.
pub open spec fn sel_ok(b: u32, top: int, nblk: int, buf: Seq<i16>, base: int) -> bool {
    forall|n: int| 0 <= n < nblk ==> ksound(#[trigger] ycode(b, top, n), blk16(buf, base + 16 * n))
}

/// `buf[lo..hi]` is zero except, at most, at the blocks' DC places.
pub open spec fn ac_clear(buf: Seq<i16>, lo: int, hi: int) -> bool {
    forall|j: int| lo <= j < hi && j % 16 != 0 ==> buf[j] == 0
}

proof fn lemma_code_push(old: u32, c: u32, k: int)
    requires
        c <= 3,
        0 <= k <= 14,
    ensures
        forall|j: int| 0 <= j < k ==> #[trigger] ycode((old << 2u32) | c, 2 * k, j) == ycode(old, 2 * k - 2, j),
        ycode((old << 2u32) | c, 2 * k, k) == c,
{
    let new = (old << 2u32) | c;
    assert forall|j: int| 0 <= j < k implies #[trigger] ycode(new, 2 * k, j) == ycode(old, 2 * k - 2, j) by {
        let sh = (2 * k - 2 - 2 * j) as u32;
        let t = (2 * k - 2 * j) as u32;
        assert(sh <= 28 && t == sh + 2 && c <= 3 ==> (((old << 2u32) | c) >> t) & 3 == (old >> sh) & 3) by (bit_vector);
    }
    assert(c <= 3 ==> (((old << 2u32) | c) >> 0u32) & 3 == c) by (bit_vector);
    assert((2 * k - 2 * k) as u32 == 0u32);
}

proof fn lemma_row_push(old: u32, row: u32, k: int)
    requires
        row < 256,
        0 <= k <= 12,
    ensures
        forall|n: int| 0 <= n < k ==> #[trigger] ycode((old << 8u32) | row, 2 * k + 6, n) == ycode(old, 2 * k - 2, n),
        forall|n: int| k <= n < k + 4 ==> #[trigger] ycode((old << 8u32) | row, 2 * k + 6, n) == ycode(row, 6, n - k),
{
    let new = (old << 8u32) | row;
    assert forall|n: int| 0 <= n < k implies #[trigger] ycode(new, 2 * k + 6, n) == ycode(old, 2 * k - 2, n) by {
        let sh = (2 * k - 2 - 2 * n) as u32;
        let t = (2 * k + 6 - 2 * n) as u32;
        assert(sh <= 22 && t == sh + 8 && row < 256 ==> (((old << 8u32) | row) >> t) & 3 == (old >> sh) & 3)
            by (bit_vector);
    }
    assert forall|n: int| k <= n < k + 4 implies #[trigger] ycode(new, 2 * k + 6, n) == ycode(row, 6, n - k) by {
        let t = (2 * k + 6 - 2 * n) as u32;
        assert((6 - 2 * (n - k)) as u32 == t);
        assert(t <= 6 && row < 256 ==> (((old << 8u32) | row) >> t) & 3 == (row >> t) & 3) by (bit_vector);
    }
}

/// Selectors stay sound while their blocks stay as they are.
proof fn lemma_sel_keep(b: u32, top: int, nblk: int, buf0: Seq<i16>, buf1: Seq<i16>, base: int)
    requires
        sel_ok(b, top, nblk, buf0, base),
        forall|j: int| base <= j < base + 16 * nblk ==> buf1[j] == buf0[j],
    ensures
        sel_ok(b, top, nblk, buf1, base),
{
    assert forall|n: int| 0 <= n < nblk implies ksound(#[trigger] ycode(b, top, n), blk16(buf1, base + 16 * n)) by {
        assert(blk16(buf1, base + 16 * n) =~= blk16(buf0, base + 16 * n));
    }
}

/// One more block's selector, pushed in below the others.
proof fn lemma_sel_push(old: u32, c: u32, k: int, buf: Seq<i16>, base: int)
    requires
        c <= 3,
        0 <= k <= 14,
        sel_ok(old, 2 * k - 2, k, buf, base),
        ksound(c, blk16(buf, base + 16 * k)),
    ensures
        sel_ok((old << 2u32) | c, 2 * k, k + 1, buf, base),
{
    lemma_code_push(old, c, k);
    let new = (old << 2u32) | c;
    assert forall|n: int| 0 <= n < k + 1 implies ksound(#[trigger] ycode(new, 2 * k, n), blk16(buf, base + 16 * n)) by {
        if n < k {
            assert(ksound(ycode(old, 2 * k - 2, n), blk16(buf, base + 16 * n)));
        }
    }
}

/// A row of four luma blocks' selectors, pushed in below the rows above.
proof fn lemma_sel_row(old: u32, row: u32, k: int, buf: Seq<i16>)
    requires
        row < 256,
        0 <= k <= 12,
        sel_ok(old, 2 * k - 2, k, buf, 0),
        sel_ok(row, 6, 4, buf, 16 * k),
    ensures
        sel_ok((old << 8u32) | row, 2 * k + 6, k + 4, buf, 0),
{
    lemma_row_push(old, row, k);
    let new = (old << 8u32) | row;
    assert forall|n: int| 0 <= n < k + 4 implies ksound(#[trigger] ycode(new, 2 * k + 6, n), blk16(buf, 0 + 16 * n)) by {
        if n < k {
            assert(ksound(ycode(old, 2 * k - 2, n), blk16(buf, 0 + 16 * n)));
        } else {
            assert(ksound(ycode(row, 6, n - k), blk16(buf, 16 * k + 16 * (n - k))));
            assert(16 * k + 16 * (n - k) == 0 + 16 * n);
        }
    }
}

/// The selector `nz_code` gives a block just parsed is sound.
proof fn lemma_code_sound(
    pt: Seq<u8>,
    s: BoolState,
    pr: Seq<int>,
    t: int,
    first: int,
    ctx: int,
    d0: int,
    d1: int,
    cb: Seq<i16>,
    ca: Seq<i16>,
    at: int,
    nz: int,
)
    requires
        0 <= first <= 1,
        0 <= at,
        at % 16 == 0,
        at + 16 <= cb.len(),
        cb.len() == ca.len(),
        forall|j: int| at < j < at + 16 ==> cb[j] == 0,
        ({
            let bt = block_tokens(pt, s, pr, t, first, ctx, true, d0, d1, blk16(cb, at));
            blk16(ca, at) == bt.1 && nz == bt.2
        }),
    ensures
        ksound(nz_code(nz, ca[at] != 0), blk16(ca, at)),
{
    hide(block_tokens);
    lemma_block_sel(pt, s, pr, t, first, ctx, d0, d1, blk16(cb, at));
    assert(blk16(ca, at)[0] == ca[at]);
}

#[inline(always)]
fn nz_code_bits(nz_coeffs: u32, nz: usize, dc_nz: bool) -> (r: u32)
    ensures
        r == (nz_coeffs << 2u32) | nz_code(nz as int, dc_nz),
{
    let c: u32 = if nz > 3 {
        3
    } else if nz > 1 {
        2
    } else {
        dc_nz as u32
    };
    (nz_coeffs << 2u32) | c
}

/// A coefficient array as the specification holds it.
pub open spec fn c16(sq: Seq<i16>) -> Seq<int> {
    Seq::new(sq.len(), |i: int| sq[i] as int)
}

/// `x >> 3` is the floor of `x / 8`.
proof fn lemma_sar3(x: i32)
    requires
        -0x10_0000 <= x <= 0x10_0000,
    ensures
        (x >> 3u32) as int == (x as int) / 8,
{
    let q = x >> 3u32;
    assert(-0x10_0000 <= x <= 0x10_0000 ==> -0x2_0000 <= (x >> 3u32) <= 0x2_0000 && sub(x, mul(x >> 3u32, 8)) >= 0
        && sub(x, mul(x >> 3u32, 8)) < 8) by (bit_vector);
    assert(mul(q, 8) == q * 8);
    assert(sub(x, mul(q, 8)) == x - q * 8);
}

/// The first pass of the inverse WHT stores `iwht_col` down the columns.
proof fn lemma_wht_col(ip: Seq<int>, i: int)
    requires
        0 <= i < 4,
    ensures
        ({
            let c = iwht_col(ip, i);
            let m = iwht_mid(ip);
            m[i] == c.0 && m[4 + i] == c.1 && m[8 + i] == c.2 && m[12 + i] == c.3
        }),
{
    assert(i % 4 == i && (4 + i) % 4 == i && (8 + i) % 4 == i && (12 + i) % 4 == i);
    assert(i / 4 == 0 && (4 + i) / 4 == 1 && (8 + i) / 4 == 2 && (12 + i) / 4 == 3);
}

/// The second pass gives `iwht` along the rows.
proof fn lemma_wht_row(ip: Seq<int>, i: int)
    requires
        0 <= i < 4,
    ensures
        ({
            let r = iwht_row(iwht_mid(ip), i);
            let w = iwht(ip);
            w[4 * i] == wrap16s(r.0) && w[4 * i + 1] == wrap16s(r.1) && w[4 * i + 2] == wrap16s(r.2) && w[4 * i + 3]
                == wrap16s(r.3)
        }),
{
    let k = 4 * i;
    assert(k / 4 == i && (k + 1) / 4 == i && (k + 2) / 4 == i && (k + 3) / 4 == i);
    assert(k % 4 == 0 && (k + 1) % 4 == 1 && (k + 2) % 4 == 2 && (k + 3) % 4 == 3);
}

/// The vertical pass of `VP8TransformWHT`.
#[inline(always)]
fn wht_cols(input: &[i16; 16]) -> (tmp: [i32; 16])
    ensures
        forall|j: int| 0 <= j < 16 ==> -0x2_0000 <= #[trigger] tmp@[j] <= 0x2_0000,
        forall|j: int| 0 <= j < 16 ==> #[trigger] tmp@[j] == iwht_mid(c16(input@))[j],
{
    let ghost ip = c16(input@);
    let ghost mid = iwht_mid(ip);
    let mut tmp: [i32; 16] = [0; 16];
    let mut i: usize = 0;
    while i < 4
        invariant
            i <= 4,
            ip == c16(input@),
            mid == iwht_mid(ip),
            forall|j: int| 0 <= j < 16 ==> -0x2_0000 <= #[trigger] tmp@[j] <= 0x2_0000,
            forall|j: int| 0 <= j < 16 && j % 4 < i ==> #[trigger] tmp@[j] == mid[j],
        decreases 4 - i,
    {
        let a0 = input[i] as i32 + input[12 + i] as i32;
        let a1 = input[4 + i] as i32 + input[8 + i] as i32;
        let a2 = input[4 + i] as i32 - input[8 + i] as i32;
        let a3 = input[i] as i32 - input[12 + i] as i32;
        proof {
            lemma_wht_col(ip, i as int);
            assert(ip[i as int] == input@[i as int] && ip[4 + i] == input@[4 + i] && ip[8 + i] == input@[8 + i]
                && ip[12 + i] == input@[12 + i]);
        }
        tmp[i] = a0 + a1;
        tmp[8 + i] = a0 - a1;
        tmp[4 + i] = a3 + a2;
        tmp[12 + i] = a3 - a2;
        i = i + 1;
    }
    tmp
}

/// One row of the horizontal pass.
#[inline(always)]
#[verifier::rlimit(40)]
fn wht_row(tmp: &[i32; 16], i: usize, Ghost(ip): Ghost<Seq<int>>) -> (v: (i16, i16, i16, i16))
    requires
        i < 4,
        forall|j: int| 0 <= j < 16 ==> -0x2_0000 <= #[trigger] tmp@[j] <= 0x2_0000,
        forall|j: int| 0 <= j < 16 ==> #[trigger] tmp@[j] == iwht_mid(ip)[j],
    ensures
        v.0 == iwht(ip)[4 * i as int],
        v.1 == iwht(ip)[4 * i + 1],
        v.2 == iwht(ip)[4 * i + 2],
        v.3 == iwht(ip)[4 * i + 3],
{
    hide(iwht);
    hide(iwht_mid);
    let dc = tmp[4 * i] + 3;
    let a0 = dc + tmp[3 + 4 * i];
    let a1 = tmp[1 + 4 * i] + tmp[2 + 4 * i];
    let a2 = tmp[1 + 4 * i] - tmp[2 + 4 * i];
    let a3 = dc - tmp[3 + 4 * i];
    proof {
        lemma_sar3((a0 + a1) as i32);
        lemma_sar3((a3 + a2) as i32);
        lemma_sar3((a0 - a1) as i32);
        lemma_sar3((a3 - a2) as i32);
        lemma_wht_row(ip, i as int);
        assert(tmp@[4 * i as int] == iwht_mid(ip)[4 * i as int] && tmp@[4 * i + 1] == iwht_mid(ip)[4 * i + 1] && tmp@[4
            * i + 2] == iwht_mid(ip)[4 * i + 2] && tmp@[4 * i + 3] == iwht_mid(ip)[4 * i + 3]);
        let r = iwht_row(iwht_mid(ip), i as int);
        assert(r.0 == (a0 + a1) / 8 && r.1 == (a3 + a2) / 8 && r.2 == (a0 - a1) / 8 && r.3 == (a3 - a2) / 8);
        assert(forall|x: int| wrap16s(x) == crate::vp8dsp::wrap16(x));
    }
    (
        crate::vp8dsp::w16((a0 + a1) >> 3u32),
        crate::vp8dsp::w16((a3 + a2) >> 3u32),
        crate::vp8dsp::w16((a0 - a1) >> 3u32),
        crate::vp8dsp::w16((a3 - a2) >> 3u32),
    )
}

/// `VP8TransformWHT` (libwebp's C version): the inverse Walsh-Hadamard
/// transform of the Y2 block, writing each DC to `dst[16 * k]`. It is
/// RFC 6386 section 14.3's (`vp8spec::iwht`).
#[verifier::rlimit(40)]
pub fn transform_wht(input: &[i16; 16], dst: &mut [i16])
    requires
        old(dst)@.len() == 384,
    ensures
        final(dst)@.len() == 384,
        forall|k: int| 0 <= k < 16 ==> #[trigger] final(dst)@[16 * k] == iwht(c16(input@))[k],
        forall|j: int| 0 <= j < 384 && !(j < 256 && j % 16 == 0) ==> final(dst)@[j] == old(dst)@[j],
{
    let ghost ip = c16(input@);
    let ghost w = iwht(ip);
    let tmp = wht_cols(input);
    let mut i: usize = 0;
    while i < 4
        invariant
            i <= 4,
            dst@.len() == 384,
            ip == c16(input@),
            w == iwht(ip),
            forall|j: int| 0 <= j < 16 ==> -0x2_0000 <= #[trigger] tmp@[j] <= 0x2_0000,
            forall|j: int| 0 <= j < 16 ==> #[trigger] tmp@[j] == iwht_mid(ip)[j],
            forall|k: int| 0 <= k < 4 * i ==> #[trigger] dst@[16 * k] == w[k],
            forall|j: int| 0 <= j < 384 && !(j < 64 * i && j % 16 == 0) ==> dst@[j] == old(dst)@[j],
        decreases 4 - i,
    {
        let v = wht_row(&tmp, i, Ghost(ip));
        let base = 64 * i;
        let ghost d0 = dst@;
        set16(dst, base, v.0);
        set16(dst, base + 16, v.1);
        set16(dst, base + 32, v.2);
        set16(dst, base + 48, v.3);
        proof {
            assert forall|k: int| 0 <= k < 4 * (i + 1) implies #[trigger] dst@[16 * k] == w[k] by {
                if k >= 4 * i {
                    assert(k == 4 * i || k == 4 * i + 1 || k == 4 * i + 2 || k == 4 * i + 3);
                } else {
                    assert(dst@[16 * k] == d0[16 * k]);
                }
            }
            assert forall|j: int| 0 <= j < 384 && !(j < 64 * (i + 1) && j % 16 == 0) implies dst@[j] == old(dst)@[j] by {
                assert(dst@[j] == d0[j]);
            }
        }
        i = i + 1;
    }
}

/// The eight block flags of a nonzero context, packed as `VP8MB::nz`.
pub open spec fn nz_pack(c: Seq<bool>) -> int {
    b2i(c[0]) + 2 * b2i(c[1]) + 4 * b2i(c[2]) + 8 * b2i(c[3]) + 16 * b2i(c[4]) + 32 * b2i(c[5]) + 64 * b2i(c[6]) + 128
        * b2i(c[7])
}

/// The four luma flags of a context as the Y loop holds them after `x`
/// blocks of a row (or `x` rows): flags still to be read at the bottom,
/// flags already replaced at the top of the byte.
pub open spec fn pack4(c: Seq<bool>, x: int) -> int {
    let b0 = b2i(c[0]);
    let b1 = b2i(c[1]);
    let b2 = b2i(c[2]);
    let b3 = b2i(c[3]);
    if x == 0 {
        b0 + 2 * b1 + 4 * b2 + 8 * b3
    } else if x == 1 {
        b1 + 2 * b2 + 4 * b3 + 128 * b0
    } else if x == 2 {
        b2 + 2 * b3 + 64 * b0 + 128 * b1
    } else if x == 3 {
        b3 + 32 * b0 + 64 * b1 + 128 * b2
    } else {
        16 * b0 + 32 * b1 + 64 * b2 + 128 * b3
    }
}

/// The two flags of a chroma plane (at `off`) as the chroma loop holds
/// the top context after `x` blocks of a row, above `g` bits that belong
/// to the other plane.
pub open spec fn pack2(c: Seq<bool>, off: int, x: int, g: int) -> int {
    let b0 = b2i(c[off]);
    let b1 = b2i(c[off + 1]);
    if x == 0 {
        b0 + 2 * b1 + 4 * g
    } else if x == 1 {
        b1 + 2 * g + 8 * b0
    } else {
        g + 4 * b0 + 8 * b1
    }
}

/// The same for the left context after `y` rows.
pub open spec fn pack2l(c: Seq<bool>, off: int, y: int, h: int) -> int {
    let b0 = b2i(c[off]);
    let b1 = b2i(c[off + 1]);
    if y == 0 {
        b0 + 2 * b1 + 4 * h
    } else if y == 1 {
        b1 + 2 * h + 32 * b0
    } else {
        h + 16 * b0 + 32 * b1
    }
}

impl Nz {
    /// The packed context holds the flags `c`.
    pub open spec fn is(&self, c: Seq<bool>) -> bool {
        &&& c.len() == 9
        &&& self.nz == nz_pack(c)
        &&& self.nz_dc == b2i(c[8])
    }
}

proof fn lemma_plane_blocks_zero(
    pt: Seq<u8>,
    st: ResState,
    pr: Seq<int>,
    t: int,
    first: int,
    d0: int,
    d1: int,
    base: int,
    off: int,
    w: int,
)
    ensures
        plane_blocks(pt, st, pr, t, first, d0, d1, base, off, w, 0) == st,
{
}

proof fn lemma_pack4(c: Seq<bool>, x: int)
    requires
        0 <= x <= 4,
    ensures
        0 <= pack4(c, x) < 256,
        0 <= pack4(c, 0) < 16,
        x < 4 ==> pack4(c, x) % 2 == b2i(c[x]),
        x == 4 ==> pack4(c, x) / 16 == pack4(c, 0),
{
}

proof fn lemma_pack4_step(c: Seq<bool>, c2: Seq<bool>, x: int, f: bool)
    requires
        0 <= x < 4,
        c2[x] == f,
        forall|j: int| 0 <= j < 4 && j != x ==> c2[j] == c[j],
    ensures
        pack4(c, x) / 2 + 128 * b2i(f) == pack4(c2, x + 1),
{
    assert(c2[0] == c[0] || x == 0);
    assert(c2[1] == c[1] || x == 1);
    assert(c2[2] == c[2] || x == 2);
    assert(c2[3] == c[3] || x == 3);
}

proof fn lemma_pack2(c: Seq<bool>, off: int, x: int, g: int)
    requires
        0 <= x <= 2,
        0 <= g < 4,
    ensures
        0 <= pack2(c, off, x, g) < 16,
        pack2(c, off, 0, 0) == b2i(c[off]) + 2 * b2i(c[off + 1]),
        x < 2 ==> pack2(c, off, x, g) % 2 == b2i(c[off + x]),
        x == 2 ==> pack2(c, off, x, g) / 4 == pack2(c, off, 0, 0),
{
}

proof fn lemma_pack2_step(c: Seq<bool>, c2: Seq<bool>, off: int, x: int, g: int, f: bool)
    requires
        0 <= x < 2,
        0 <= g < 4,
        c2[off + x] == f,
        c2[off + 1 - x] == c[off + 1 - x],
    ensures
        pack2(c, off, x, g) / 2 + 8 * b2i(f) == pack2(c2, off, x + 1, g),
{
}

proof fn lemma_pack2l(c: Seq<bool>, off: int, y: int, h: int)
    requires
        0 <= y <= 2,
        0 <= h < 4,
    ensures
        0 <= pack2l(c, off, y, h) < 64,
        y < 2 ==> pack2l(c, off, y, h) % 2 == b2i(c[off + y]),
        y == 2 ==> pack2l(c, off, y, h) - pack2l(c, off, y, h) % 16 == 16 * b2i(c[off]) + 32 * b2i(c[off + 1]),
{
}

proof fn lemma_pack2l_step(c: Seq<bool>, c2: Seq<bool>, off: int, y: int, h: int, f: bool)
    requires
        0 <= y < 2,
        0 <= h < 4,
        c2[off + y] == f,
        c2[off + 1 - y] == c[off + 1 - y],
    ensures
        pack2l(c, off, y, h) / 2 + 32 * b2i(f) == pack2l(c2, off, y + 1, h),
{
}

/// One block of a plane, as the loops of `ParseResiduals` see it: with
/// the coefficients `cb` before and `ca` after `GetCoeffs`, the state after
/// `n + 1` blocks is the one after `n` with this block's result.
proof fn lemma_plane_step(
    pt: Seq<u8>,
    st: ResState,
    pr: Seq<int>,
    t: int,
    first: int,
    d0: int,
    d1: int,
    base: int,
    off: int,
    w: int,
    n: nat,
    cb: Seq<i16>,
    ca: Seq<i16>,
    nz: int,
    ctx: int,
)
    requires
        st.coeffs.len() == 384,
        st.top.len() == 9,
        st.left.len() == 9,
        (w == 4 && off == 0) || (w == 2 && (off == 4 || off == 6)),
        n < w * w,
        0 <= base,
        base + w * w <= 24,
        0 <= first <= 1,
        cb.len() == 384,
        ca.len() == 384,
        ({
            let e = plane_blocks(pt, st, pr, t, first, d0, d1, base, off, w, n);
            let at = 16 * (base + n);
            let bt = block_tokens(pt, e.s, pr, t, first, ctx, true, d0, d1, blk16(cb, at));
            &&& c16(cb) == e.coeffs
            &&& ctx == b2i(e.left[off + n as int / w]) + b2i(e.top[off + n as int % w])
            &&& blk16(ca, at) == bt.1
            &&& nz == bt.2
            &&& forall|j: int| 0 <= j < 384 && !(at <= j < at + 16) ==> ca[j] == cb[j]
        }),
    ensures
        ({
            let e = plane_blocks(pt, st, pr, t, first, d0, d1, base, off, w, n);
            let e2 = plane_blocks(pt, st, pr, t, first, d0, d1, base, off, w, (n + 1) as nat);
            let at = 16 * (base + n);
            let bt = block_tokens(pt, e.s, pr, t, first, ctx, true, d0, d1, blk16(cb, at));
            &&& e.top.len() == 9
            &&& e.left.len() == 9
            &&& e2.s == bt.0
            &&& c16(ca) == e2.coeffs
            &&& e2.top == e.top.update(off + n as int % w, nz > first)
            &&& e2.left == e.left.update(off + n as int / w, nz > first)
        }),
{
    hide(block_tokens);
    lemma_plane_blocks_frame(pt, st, pr, t, first, d0, d1, base, off, w, n);
    let e = plane_blocks(pt, st, pr, t, first, d0, d1, base, off, w, n);
    assert((n + 1 - 1) as nat == n);
    let e2 = plane_block(pt, e, pr, t, first, d0, d1, base, off, w, n as int);
    assert(plane_blocks(pt, st, pr, t, first, d0, d1, base, off, w, (n + 1) as nat) == e2);
    let at = 16 * (base + n);
    assert(blk16(cb, at) =~= e.coeffs.subrange(at, at + 16));
    let bt = block_tokens(pt, e.s, pr, t, first, ctx, true, d0, d1, blk16(cb, at));
    assert(c16(ca) =~= splice16(e.coeffs, at, bt.1)) by {
        assert forall|i: int| 0 <= i < 384 implies c16(ca)[i] == splice16(e.coeffs, at, bt.1)[i] by {
            if at <= i < at + 16 {
                assert(blk16(ca, at)[i - at] == ca[at + (i - at)]);
            } else {
                assert(ca[i] == cb[i]);
                assert(c16(cb)[i] == cb[i]);
            }
        }
    }
}

/// Some value of `buf[lo..hi]` is not zero.
pub open spec fn any16(buf: Seq<i16>, lo: int, hi: int) -> bool {
    exists|j: int| lo <= j < hi && 0 <= j < buf.len() && #[trigger] buf[j] != 0
}

proof fn lemma_any_keep(a: Seq<i16>, b: Seq<i16>, lo: int, hi: int, lo2: int, hi2: int)
    requires
        any16(a, lo, hi),
        lo2 <= lo,
        hi <= hi2,
        a.len() == b.len(),
        forall|j: int| lo <= j < hi && 0 <= j < a.len() ==> b[j] == a[j],
    ensures
        any16(b, lo2, hi2),
{
    let w = choose|j: int| lo <= j < hi && 0 <= j < a.len() && #[trigger] a[j] != 0;
    assert(b[w] != 0);
}

/// One more block of a plane keeps `plane_solid`'s promise: tokens past
/// the second position leave a nonzero coefficient.
proof fn lemma_solid_step(
    pt: Seq<u8>,
    st: ResState,
    pr: Seq<int>,
    t: int,
    first: int,
    d0: int,
    d1: int,
    base: int,
    off: int,
    w: int,
    n: nat,
    cb: Seq<i16>,
    ca: Seq<i16>,
    nz: int,
    ctx: int,
)
    requires
        0 <= base,
        cb.len() == 384,
        ca.len() == 384,
        16 * (base + n) + 16 <= 384,
        plane_solid(pt, st, pr, t, first, d0, d1, base, off, w, (n + 1) as nat),
        ({
            let e = plane_blocks(pt, st, pr, t, first, d0, d1, base, off, w, n);
            let at = 16 * (base + n);
            let bt = block_tokens(pt, e.s, pr, t, first, ctx, true, d0, d1, blk16(cb, at));
            &&& c16(cb) == e.coeffs
            &&& ctx == b2i(e.left[off + n as int / w]) + b2i(e.top[off + n as int % w])
            &&& blk16(ca, at) == bt.1
            &&& nz == bt.2
        }),
    ensures
        plane_solid(pt, st, pr, t, first, d0, d1, base, off, w, n),
        nz > 1 ==> any16(ca, 16 * (base + n), 16 * (base + n) + 16),
{
    hide(block_tokens);
    hide(plane_blocks);
    assert((n + 1 - 1) as nat == n);
    let e = plane_blocks(pt, st, pr, t, first, d0, d1, base, off, w, n);
    let at = 16 * (base + n);
    assert(blk16(cb, at) =~= e.coeffs.subrange(at, at + 16));
    let c = blk16(ca, at);
    if nz > 1 {
        assert(!zero_blk(c));
        if c[0] != 0 {
            assert(ca[at + 0] != 0);
        } else {
            let i = choose|i: int| 1 <= i < 16 && #[trigger] c[i] != 0;
            assert(ca[at + i] != 0);
        }
    }
}

/// The selector word after one more block: if it is not zero, some
/// coefficient so far is not.
proof fn lemma_any_step(cb: Seq<i16>, ca: Seq<i16>, lo: int, at: int, prev: bool, code: u32, nz: int)
    requires
        cb.len() == ca.len(),
        0 <= lo <= at,
        at + 16 <= ca.len(),
        forall|j: int| 0 <= j < cb.len() && !(at <= j < at + 16) ==> ca[j] == cb[j],
        prev ==> any16(cb, lo, at),
        code == nz_code(nz, ca[at] != 0),
        nz > 1 ==> any16(ca, at, at + 16),
    ensures
        prev || code != 0 ==> any16(ca, lo, at + 16),
{
    if prev {
        lemma_any_keep(cb, ca, lo, at, lo, at + 16);
    } else if code != 0 {
        if nz > 1 {
            lemma_any_keep(ca, ca, at, at + 16, lo, at + 16);
        } else {
            assert(ca[at] != 0);
        }
    }
}

/// Selectors that are all zero, and sound, mean a macroblock of zeros.
proof fn lemma_sels_zero(r: Residuals, buf: Seq<i16>)
    requires
        buf.len() == 384,
        sels_ok(r, buf),
        (r.non_zero_y | r.non_zero_uv) == 0,
    ensures
        !any_nz(c16(buf)),
{
    let (a, b) = (r.non_zero_y, r.non_zero_uv);
    assert((a | b) == 0 ==> a == 0 && b == 0) by (bit_vector);
    assert(0u32 & 0xff == 0 && (0u32 >> 8u32) & 0xff == 0) by (bit_vector);
    assert forall|j: int| 0 <= j < 384 implies buf[j] == 0 by {
        let (base, top, n) = if j < 256 {
            (0int, 30int, j / 16)
        } else if j < 320 {
            (256int, 6int, (j - 256) / 16)
        } else {
            (320int, 6int, (j - 320) / 16)
        };
        let sh = (top - 2 * n) as u32;
        assert((0u32 >> sh) & 3 == 0) by (bit_vector);
        assert(ycode(0u32, top, n) == 0);
        let c = blk16(buf, base + 16 * n);
        assert(ksound(ycode(0u32, top, n), c));
        let i = j - (base + 16 * n);
        assert(c[i] == buf[base + 16 * n + i]);
    }
    assert forall|j: int| 0 <= j < c16(buf).len() implies c16(buf)[j] == 0 by {
        assert(buf[j] == 0);
    }
}

/// The sixteen luma blocks of a macroblock (`ParseResiduals`' first loop).
/// `tnz` and `lnz` hold the four luma flags of the contexts; the new ones
/// are returned the same way, with the transform selectors of the blocks.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn resid_y(
    br: &mut BoolReader,
    data: &[u8],
    proba: &Vec<u8>,
    ac_type: usize,
    first: usize,
    dq: [i32; 2],
    tnz_in: u32,
    lnz_in: u32,
    coeffs: &mut [i16],
    Ghost(p0): Ghost<int>,
    Ghost(st): Ghost<ResState>,
    Ghost(pr): Ghost<Seq<int>>,
) -> (r: (u32, u32, u32))
    requires
        old(br).inv(data@.len()),
        proba@.len() == 1056,
        ac_type < 4,
        first <= 1,
        0 <= dq[0] <= 1024,
        0 <= dq[1] <= 1024,
        tnz_in < 16,
        lnz_in < 16,
        old(coeffs)@.len() == 384,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(coeffs)@.len() == 384,
        r.0 < 16,
        r.1 < 16,
        forall|j: int| 256 <= j < 384 ==> final(coeffs)@[j] == old(coeffs)@[j],
        old(br).rel(data@, p0, st.s) && probs_are(proba@, pr) && c16(old(coeffs)@) == st.coeffs && st.top.len() == 9
            && st.left.len() == 9 && tnz_in == pack4(st.top, 0) && lnz_in == pack4(st.left, 0) && ac_clear(
            old(coeffs)@,
            0,
            256,
        ) && !final(br).eof ==> {
            let e = plane_blocks(
                part(data@, p0, old(br).end as int),
                st,
                pr,
                ac_type as int,
                first as int,
                dq[0] as int,
                dq[1] as int,
                0,
                0,
                4,
                16,
            );
            &&& final(br).rel(data@, p0, e.s)
            &&& c16(final(coeffs)@) == e.coeffs
            &&& r.0 == pack4(e.top, 0)
            &&& r.1 == pack4(e.left, 0)
            &&& sel_ok(r.2, 30, 16, final(coeffs)@, 0)
            &&& plane_solid(
                part(data@, p0, old(br).end as int),
                st,
                pr,
                ac_type as int,
                first as int,
                dq[0] as int,
                dq[1] as int,
                0,
                0,
                4,
                16,
            ) && r.2 != 0 ==> any16(final(coeffs)@, 0, 256)
        },
{
    hide(block_tokens);
    hide(plane_blocks);
    hide(pack4);
    proof {
        assert(data@.len() == data.len());
        assert(coeffs@.len() == coeffs.len());
    }
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, st.s) && probs_are(proba@, pr) && c16(coeffs@) == st.coeffs && st.top.len() == 9
        && st.left.len() == 9 && tnz_in == pack4(st.top, 0) && lnz_in == pack4(st.left, 0) && ac_clear(coeffs@, 0, 256);
    let ghost ti = ac_type as int;
    let ghost fi = first as int;
    let ghost d0 = dq[0] as int;
    let ghost d1 = dq[1] as int;
    proof {
        lemma_plane_blocks_zero(pt, st, pr, ti, fi, d0, d1, 0, 0, 4);
    }
    let mut tnz = tnz_in;
    let mut lnz = lnz_in;
    let mut non_zero_y: u32 = 0;
    let mut dst: usize = 0;
    let mut y: usize = 0;
    while y < 4
        invariant
            data@.len() <= usize::MAX,
            coeffs@.len() <= usize::MAX,
            y <= 4,
            dst == 64 * y,
            coeffs@.len() == 384,
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            tnz < 16,
            lnz < 256,
            ok0 && !br.eof ==> {
                let e = plane_blocks(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, (4 * y) as nat);
                &&& br.rel(data@, p0, e.s)
                &&& c16(coeffs@) == e.coeffs
                &&& tnz == pack4(e.top, 0)
                &&& lnz == pack4(e.left, y as int)
                &&& sel_ok(non_zero_y, 8 * y - 2, 4 * y as int, coeffs@, 0)
                &&& plane_solid(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, (4 * y) as nat) && non_zero_y != 0 ==> any16(
                    coeffs@,
                    0,
                    dst as int,
                )
            },
            forall|j: int| 256 <= j < 384 ==> coeffs@[j] == old(coeffs)@[j],
            ok0 ==> ac_clear(coeffs@, dst as int, 256),
        decreases 4 - y,
    {
        let ghost e_row = plane_blocks(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, (4 * y) as nat);
        proof {
            lemma_pack4(e_row.left, y as int);
        }
        let mut l = lnz % 2;
        let mut nz_coeffs: u32 = 0;
        let mut x: usize = 0;
        while x < 4
            invariant
                data@.len() <= usize::MAX,
                coeffs@.len() <= usize::MAX,
                x <= 4,
                y < 4,
                dst == 64 * y + 16 * x,
                l <= 1,
                coeffs@.len() == 384,
                br.inv(data@.len()),
                br.end == old(br).end,
                old(br).eof ==> br.eof,
                tnz < 256,
                lnz < 256,
                ok0 && !br.eof ==> {
                    let e = plane_blocks(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, (4 * y + x) as nat);
                    &&& br.rel(data@, p0, e.s)
                    &&& c16(coeffs@) == e.coeffs
                    &&& tnz == pack4(e.top, x as int)
                    &&& lnz == pack4(e_row.left, y as int)
                    &&& l == b2i(e.left[y as int])
                    &&& forall|j: int| 0 <= j < 4 && j != y ==> #[trigger] e.left[j] == e_row.left[j]
                    &&& sel_ok(non_zero_y, 8 * y - 2, 4 * y as int, coeffs@, 0)
                    &&& sel_ok(nz_coeffs, 2 * x - 2, x as int, coeffs@, 64 * y as int)
                    &&& plane_solid(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, (4 * y + x) as nat) && (non_zero_y != 0
                        || nz_coeffs != 0) ==> any16(coeffs@, 0, dst as int)
                },
                forall|j: int| 256 <= j < 384 ==> coeffs@[j] == old(coeffs)@[j],
                ok0 ==> ac_clear(coeffs@, dst as int, 256),
                x == 0 ==> nz_coeffs == 0,
                x == 1 ==> nz_coeffs < 4,
                x == 2 ==> nz_coeffs < 16,
                x == 3 ==> nz_coeffs < 64,
                nz_coeffs < 256,
            decreases 4 - x,
        {
            let ghost n = (4 * y + x) as nat;
            let ghost e = plane_blocks(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, n);
            let ghost cb = coeffs@;
            let ctx = (l + tnz % 2) as usize;
            let nz = get_coeffs(br, data, proba, ac_type, ctx, dq, first, coeffs, dst, Ghost(p0), Ghost(e.s), Ghost(pr));
            let ghost tnz_b = tnz;
            l = (nz > first) as u32;
            proof {
                assert(tnz_b < 256 && l <= 1 ==> ((tnz_b >> 1u32) | (l << 7u32)) == tnz_b / 2 + 128 * l) by (bit_vector);
            }
            tnz = (tnz >> 1u32) | (l << 7u32);
            let ghost nzc0 = nz_coeffs;
            let ghost code = nz_code(nz as int, coeffs@[dst as int] != 0);
            nz_coeffs = nz_code_bits(nz_coeffs, nz, get16(coeffs, dst) != 0);
            proof {
                assert(code <= 3);
                assert(nzc0 < 64 && code <= 3 ==> ((nzc0 << 2u32) | code) < 256) by (bit_vector);
                assert(nzc0 < 16 && code <= 3 ==> ((nzc0 << 2u32) | code) < 64) by (bit_vector);
                assert(nzc0 < 4 && code <= 3 ==> ((nzc0 << 2u32) | code) < 16) by (bit_vector);
                assert(nzc0 == 0 && code <= 3 ==> ((nzc0 << 2u32) | code) < 4) by (bit_vector);
                if ok0 && !br.eof {
                    lemma_sel_keep(non_zero_y, 8 * y - 2, 4 * y as int, cb, coeffs@, 0);
                    lemma_sel_keep(nzc0, 2 * x - 2, x as int, cb, coeffs@, 64 * y as int);
                    lemma_code_sound(pt, e.s, pr, ti, fi, ctx as int, d0, d1, cb, coeffs@, dst as int, nz as int);
                    lemma_sel_push(nzc0, code, x as int, coeffs@, 64 * y as int);
                }
            }
            proof {
                assert(n as int / 4 == y && n as int % 4 == x);
                assert((4 * y + (x + 1)) as nat == (n + 1) as nat);
                if ok0 && !br.eof {
                    assert(st.coeffs.len() == 384);
                    lemma_pack4(e.top, x as int);
                    lemma_plane_step(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, n, cb, coeffs@, nz as int, ctx as int);
                    let e2 = plane_blocks(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, (n + 1) as nat);
                    lemma_pack4_step(e.top, e2.top, x as int, nz > first);
                    assert(l == b2i(e2.left[y as int]));
                    if plane_solid(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, (n + 1) as nat) {
                        lemma_solid_step(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, n, cb, coeffs@, nz as int, ctx as int);
                        let prev = non_zero_y != 0 || nzc0 != 0;
                        lemma_any_step(cb, coeffs@, 0, dst as int, prev, code, nz as int);
                        assert(((nzc0 << 2u32) | code) != 0 ==> nzc0 != 0 || code != 0) by (bit_vector);
                    }
                }
            }
            dst = dst + 16;
            x = x + 1;
        }
        proof {
            assert(tnz < 256 ==> (tnz >> 4u32) == tnz / 16) by (bit_vector);
            assert(lnz < 256 && l <= 1 ==> ((lnz >> 1u32) | (l << 7u32)) == lnz / 2 + 128 * l) by (bit_vector);
            assert((4 * (y + 1)) as nat == (4 * y + 4) as nat);
            if ok0 && !br.eof {
                let e = plane_blocks(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, (4 * y + 4) as nat);
                lemma_pack4(e.top, 4);
                lemma_pack4_step(e_row.left, e.left, y as int, e.left[y as int]);
            }
        }
        proof {
            if ok0 && !br.eof {
                lemma_sel_row(non_zero_y, nz_coeffs, 4 * y as int, coeffs@);
                let (a, b) = (non_zero_y, nz_coeffs);
                assert(((a << 8u32) | b) != 0 ==> a != 0 || b != 0) by (bit_vector);
            }
        }
        tnz = tnz >> 4u32;
        lnz = (lnz >> 1u32) | (l << 7u32);
        non_zero_y = (non_zero_y << 8u32) | nz_coeffs;
        y = y + 1;
    }
    proof {
        assert(lnz < 256 ==> (lnz >> 4u32) == lnz / 16) by (bit_vector);
        if ok0 && !br.eof {
            let e = plane_blocks(pt, st, pr, ti, fi, d0, d1, 0, 0, 4, 16);
            lemma_pack4(e.left, 4);
        }
    }
    (tnz, lnz >> 4u32, non_zero_y)
}

/// The four blocks of one chroma plane (`ParseResiduals`' second loop,
/// one round). `tnz_in` and `lnz_in` hold the plane's two flags at the
/// bottom, under at most two bits of the other plane.
#[inline(always)]
#[verifier::loop_isolation(false)]
fn resid_uv(
    br: &mut BoolReader,
    data: &[u8],
    proba: &Vec<u8>,
    dq: [i32; 2],
    tnz_in: u32,
    lnz_in: u32,
    coeffs: &mut [i16],
    dst0: usize,
    Ghost(p0): Ghost<int>,
    Ghost(st): Ghost<ResState>,
    Ghost(pr): Ghost<Seq<int>>,
    Ghost(off): Ghost<int>,
    Ghost(gt): Ghost<int>,
    Ghost(gl): Ghost<int>,
) -> (r: (u32, u32, u32))
    requires
        old(br).inv(data@.len()),
        proba@.len() == 1056,
        0 <= dq[0] <= 1024,
        0 <= dq[1] <= 1024,
        tnz_in < 16,
        lnz_in < 16,
        old(coeffs)@.len() == 384,
        (dst0 == 256 && off == 4) || (dst0 == 320 && off == 6),
        0 <= gt < 4,
        0 <= gl < 4,
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(coeffs)@.len() == 384,
        r.0 < 4,
        r.1 == 0 || r.1 == 16 || r.1 == 32 || r.1 == 48,
        r.2 < 256,
        forall|j: int| 0 <= j < 384 && !(dst0 <= j < dst0 + 64) ==> final(coeffs)@[j] == old(coeffs)@[j],
        old(br).rel(data@, p0, st.s) && probs_are(proba@, pr) && c16(old(coeffs)@) == st.coeffs && st.top.len() == 9
            && st.left.len() == 9 && tnz_in == pack2(st.top, off, 0, gt) && lnz_in == pack2l(st.left, off, 0, gl)
            && ac_clear(old(coeffs)@, dst0 as int, dst0 + 64) && !final(br).eof ==> {
            let e = plane_blocks(
                part(data@, p0, old(br).end as int),
                st,
                pr,
                2,
                0,
                dq[0] as int,
                dq[1] as int,
                dst0 as int / 16,
                off,
                2,
                4,
            );
            &&& final(br).rel(data@, p0, e.s)
            &&& c16(final(coeffs)@) == e.coeffs
            &&& r.0 == b2i(e.top[off]) + 2 * b2i(e.top[off + 1])
            &&& r.1 == 16 * b2i(e.left[off]) + 32 * b2i(e.left[off + 1])
            &&& sel_ok(r.2, 6, 4, final(coeffs)@, dst0 as int)
            &&& plane_solid(
                part(data@, p0, old(br).end as int),
                st,
                pr,
                2,
                0,
                dq[0] as int,
                dq[1] as int,
                dst0 as int / 16,
                off,
                2,
                4,
            ) && r.2 != 0 ==> any16(final(coeffs)@, dst0 as int, dst0 + 64)
        },
{
    hide(block_tokens);
    hide(plane_blocks);
    hide(pack2);
    hide(pack2l);
    proof {
        assert(data@.len() == data.len());
        assert(coeffs@.len() == coeffs.len());
    }
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, st.s) && probs_are(proba@, pr) && c16(coeffs@) == st.coeffs && st.top.len() == 9
        && st.left.len() == 9 && tnz_in == pack2(st.top, off, 0, gt) && lnz_in == pack2l(st.left, off, 0, gl)
        && ac_clear(coeffs@, dst0 as int, dst0 + 64);
    let ghost d0 = dq[0] as int;
    let ghost d1 = dq[1] as int;
    let ghost base = dst0 as int / 16;
    proof {
        lemma_plane_blocks_zero(pt, st, pr, 2, 0, d0, d1, base, off, 2);
    }
    let mut nz_coeffs: u32 = 0;
    let mut tnz = tnz_in;
    let mut lnz = lnz_in;
    let mut dst = dst0;
    let mut y: usize = 0;
    while y < 2
        invariant
            data@.len() <= usize::MAX,
            coeffs@.len() <= usize::MAX,
            y <= 2,
            dst == dst0 + 32 * y,
            coeffs@.len() == 384,
            br.inv(data@.len()),
            br.end == old(br).end,
            old(br).eof ==> br.eof,
            tnz < 16,
            lnz < 64,
            y == 2 ==> tnz < 4,
            ok0 && !br.eof ==> {
                let e = plane_blocks(pt, st, pr, 2, 0, d0, d1, base, off, 2, (2 * y) as nat);
                &&& br.rel(data@, p0, e.s)
                &&& c16(coeffs@) == e.coeffs
                &&& tnz == pack2(e.top, off, 0, if y == 0 {
                    gt
                } else {
                    0
                })
                &&& lnz == pack2l(e.left, off, y as int, gl)
                &&& sel_ok(nz_coeffs, 4 * y - 2, 2 * y as int, coeffs@, dst0 as int)
                &&& plane_solid(pt, st, pr, 2, 0, d0, d1, base, off, 2, (2 * y) as nat) && nz_coeffs != 0 ==> any16(
                    coeffs@,
                    dst0 as int,
                    dst as int,
                )
            },
            forall|j: int| 0 <= j < 384 && !(dst0 <= j < dst0 + 64) ==> coeffs@[j] == old(coeffs)@[j],
            ok0 ==> ac_clear(coeffs@, dst as int, dst0 + 64),
            2 * y == 0 ==> nz_coeffs == 0,
            2 * y == 1 ==> nz_coeffs < 4,
            2 * y == 2 ==> nz_coeffs < 16,
            2 * y == 3 ==> nz_coeffs < 64,
            nz_coeffs < 256,
        decreases 2 - y,
    {
        let ghost e_row = plane_blocks(pt, st, pr, 2, 0, d0, d1, base, off, 2, (2 * y) as nat);
        let ghost g = if y == 0 {
            gt
        } else {
            0int
        };
        proof {
            lemma_pack2l(e_row.left, off, y as int, gl);
        }
        let mut l = lnz % 2;
        let mut x: usize = 0;
        while x < 2
            invariant
                data@.len() <= usize::MAX,
                coeffs@.len() <= usize::MAX,
                x <= 2,
                y < 2,
                dst == dst0 + 32 * y + 16 * x,
                l <= 1,
                coeffs@.len() == 384,
                br.inv(data@.len()),
                br.end == old(br).end,
                old(br).eof ==> br.eof,
                tnz < 16,
                lnz < 64,
                ok0 && !br.eof ==> {
                    let e = plane_blocks(pt, st, pr, 2, 0, d0, d1, base, off, 2, (2 * y + x) as nat);
                    &&& br.rel(data@, p0, e.s)
                    &&& c16(coeffs@) == e.coeffs
                    &&& tnz == pack2(e.top, off, x as int, g)
                    &&& lnz == pack2l(e_row.left, off, y as int, gl)
                    &&& l == b2i(e.left[off + y])
                    &&& forall|j: int| 0 <= j < 2 && j != y ==> #[trigger] e.left[off + j] == e_row.left[off + j]
                    &&& sel_ok(nz_coeffs, 2 * (2 * y + x) - 2, 2 * y + x, coeffs@, dst0 as int)
                    &&& plane_solid(pt, st, pr, 2, 0, d0, d1, base, off, 2, (2 * y + x) as nat) && nz_coeffs != 0
                        ==> any16(coeffs@, dst0 as int, dst as int)
                },
                forall|j: int| 0 <= j < 384 && !(dst0 <= j < dst0 + 64) ==> coeffs@[j] == old(coeffs)@[j],
                ok0 ==> ac_clear(coeffs@, dst as int, dst0 + 64),
                2 * y + x == 0 ==> nz_coeffs == 0,
                2 * y + x == 1 ==> nz_coeffs < 4,
                2 * y + x == 2 ==> nz_coeffs < 16,
                2 * y + x == 3 ==> nz_coeffs < 64,
                nz_coeffs < 256,
            decreases 2 - x,
        {
            let ghost n = (2 * y + x) as nat;
            let ghost e = plane_blocks(pt, st, pr, 2, 0, d0, d1, base, off, 2, n);
            let ghost cb = coeffs@;
            let ctx = (l + tnz % 2) as usize;
            let nz = get_coeffs(br, data, proba, 2, ctx, dq, 0, coeffs, dst, Ghost(p0), Ghost(e.s), Ghost(pr));
            let ghost tnz_b = tnz;
            l = (nz > 0) as u32;
            proof {
                assert(tnz_b < 16 && l <= 1 ==> ((tnz_b >> 1u32) | (l << 3u32)) == tnz_b / 2 + 8 * l) by (bit_vector);
            }
            tnz = (tnz >> 1u32) | (l << 3u32);
            let ghost nzc0 = nz_coeffs;
            let ghost code = nz_code(nz as int, coeffs@[dst as int] != 0);
            nz_coeffs = nz_code_bits(nz_coeffs, nz, get16(coeffs, dst) != 0);
            proof {
                assert(code <= 3);
                assert(nzc0 < 64 && code <= 3 ==> ((nzc0 << 2u32) | code) < 256) by (bit_vector);
                assert(nzc0 < 16 && code <= 3 ==> ((nzc0 << 2u32) | code) < 64) by (bit_vector);
                assert(nzc0 < 4 && code <= 3 ==> ((nzc0 << 2u32) | code) < 16) by (bit_vector);
                assert(nzc0 == 0 && code <= 3 ==> ((nzc0 << 2u32) | code) < 4) by (bit_vector);
                assert(dst == dst0 + 16 * (2 * y + x));
                if ok0 && !br.eof {
                    lemma_sel_keep(nzc0, 2 * (2 * y + x) - 2, 2 * y + x, cb, coeffs@, dst0 as int);
                    lemma_code_sound(pt, e.s, pr, 2, 0, ctx as int, d0, d1, cb, coeffs@, dst as int, nz as int);
                    lemma_sel_push(nzc0, code, 2 * y + x, coeffs@, dst0 as int);
                }
            }
            proof {
                assert(n as int / 2 == y && n as int % 2 == x);
                assert((2 * y + (x + 1)) as nat == (n + 1) as nat);
                assert(16 * (base + n) == dst);
                if ok0 && !br.eof {
                    assert(st.coeffs.len() == 384);
                    lemma_pack2(e.top, off, x as int, g);
                    lemma_plane_step(pt, st, pr, 2, 0, d0, d1, base, off, 2, n, cb, coeffs@, nz as int, ctx as int);
                    let e2 = plane_blocks(pt, st, pr, 2, 0, d0, d1, base, off, 2, (n + 1) as nat);
                    lemma_pack2_step(e.top, e2.top, off, x as int, g, nz > 0);
                    assert(l == b2i(e2.left[off + y]));
                    if plane_solid(pt, st, pr, 2, 0, d0, d1, base, off, 2, (n + 1) as nat) {
                        lemma_solid_step(pt, st, pr, 2, 0, d0, d1, base, off, 2, n, cb, coeffs@, nz as int, ctx as int);
                        lemma_any_step(cb, coeffs@, dst0 as int, dst as int, nzc0 != 0, code, nz as int);
                        assert(((nzc0 << 2u32) | code) != 0 ==> nzc0 != 0 || code != 0) by (bit_vector);
                    }
                }
            }
            dst = dst + 16;
            x = x + 1;
        }
        proof {
            assert(tnz < 16 ==> (tnz >> 2u32) == tnz / 4) by (bit_vector);
            assert(lnz < 64 && l <= 1 ==> ((lnz >> 1u32) | (l << 5u32)) == lnz / 2 + 32 * l) by (bit_vector);
            assert((2 * (y + 1)) as nat == (2 * y + 2) as nat);
            if ok0 && !br.eof {
                let e = plane_blocks(pt, st, pr, 2, 0, d0, d1, base, off, 2, (2 * y + 2) as nat);
                lemma_pack2(e.top, off, 2, g);
                assert(e.left[off + (1 - y)] == e_row.left[off + (1 - y)]);
                lemma_pack2l_step(e_row.left, e.left, off, y as int, gl, e.left[off + y]);
            }
        }
        tnz = tnz >> 2u32;
        lnz = (lnz >> 1u32) | (l << 5u32);
        y = y + 1;
    }
    proof {
        assert(lnz < 64 ==> (lnz & 0xf0u32) == lnz - lnz % 16) by (bit_vector);
        assert(lnz < 64 ==> (lnz & 0xf0u32) == 0 || (lnz & 0xf0u32) == 16 || (lnz & 0xf0u32) == 32 || (lnz & 0xf0u32)
            == 48) by (bit_vector);
        if ok0 && !br.eof {
            let e = plane_blocks(pt, st, pr, 2, 0, d0, d1, base, off, 2, 4);
            lemma_pack2l(e.left, off, 2, gl);
            lemma_pack2(e.top, off, 0, 0);
        }
    }
    (tnz, lnz & 0xf0, nz_coeffs)
}

/// The transform selectors of a macroblock are sound for the buffer.
pub open spec fn sels_ok(r: Residuals, buf: Seq<i16>) -> bool {
    &&& sel_ok(r.non_zero_y, 30, 16, buf, 0)
    &&& sel_ok(r.non_zero_uv & 0xff, 6, 4, buf, 256)
    &&& sel_ok((r.non_zero_uv >> 8u32) & 0xff, 6, 4, buf, 320)
}

/// `ParseResiduals`: the coefficients of one macroblock into `coeffs`
/// (sixteen Y blocks, then four U and four V, sixteen each), updating the
/// nonzero contexts above (`top`) and to the left (`left`).
///
/// They are the ones `vp8spec::mb_residuals` reads (RFC 6386 sections 13
/// and 14.3) from the state `g`, with the header's probabilities `pr`, the
/// segment's factors `qs` and the contexts `tc` and `lc`.
#[verifier::loop_isolation(false)]
#[verifier::rlimit(50)]
pub fn parse_residuals(
    br: &mut BoolReader,
    data: &[u8],
    hdr: &Header,
    m: &MbModes,
    top: &mut Nz,
    left: &mut Nz,
    coeffs: &mut [i16],
    Ghost(p0): Ghost<int>,
    Ghost(g): Ghost<BoolState>,
    Ghost(pr): Ghost<Seq<int>>,
    Ghost(qs): Ghost<(int, int, int, int, int, int)>,
    Ghost(tc): Ghost<Seq<bool>>,
    Ghost(lc): Ghost<Seq<bool>>,
) -> (r: Residuals)
    requires
        old(br).inv(data@.len()),
        hdr.proba@.len() == 1056,
        m.segment < 4,
        old(coeffs)@.len() == 384,
        forall|s: int| 0 <= s < 4 ==> #[trigger] quant_ok(hdr.dqm@[s]),
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(coeffs)@.len() == 384,
        old(br).rel(data@, p0, g) && probs_are(hdr.proba@, pr) && quant_matches(hdr.dqm@[m.segment as int], qs) && old(
            top,
        ).is(tc) && old(left).is(lc) && !final(br).eof ==> {
            let e = mb_residuals(part(data@, p0, old(br).end as int), g, pr, qs, m.is_i4x4, tc, lc);
            &&& final(br).rel(data@, p0, e.s)
            &&& c16(final(coeffs)@) == e.coeffs
            &&& final(top).is(e.top)
            &&& final(left).is(e.left)
            &&& sels_ok(r, final(coeffs)@)
            &&& mb_solid(part(data@, p0, old(br).end as int), g, pr, qs, m.is_i4x4, tc, lc) && (r.non_zero_y
                | r.non_zero_uv) != 0 ==> any16(final(coeffs)@, 0, 384)
        },
{
    hide(block_tokens);
    hide(plane_blocks);
    hide(plane_solid);
    proof {
        assert(data@.len() == data.len());
        assert(coeffs@.len() == coeffs.len());
    }
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok0 = br.rel(data@, p0, g) && probs_are(hdr.proba@, pr) && quant_matches(hdr.dqm@[m.segment as int], qs)
        && top.is(tc) && left.is(lc);
    let q = hdr.dqm[m.segment];
    proof {
        assert(quant_ok(hdr.dqm@[m.segment as int]));
    }
    let mut k: usize = 0;
    while k < 384
        invariant
            data@.len() <= usize::MAX,
            coeffs@.len() <= usize::MAX,
            k <= 384,
            coeffs@.len() == 384,
            forall|j: int| 0 <= j < k ==> coeffs@[j] == 0,
        decreases 384 - k,
    {
        set16(coeffs, k, 0);
        k = k + 1;
    }
    let ghost cz = coeffs@;
    assert(forall|j: int| 0 <= j < 384 ==> cz[j] == 0);
    let ghost st0 = ResState { s: g, coeffs: Seq::new(384, |i: int| 0int), top: tc, left: lc };
    let ghost mut st1 = st0;
    proof {
        assert(c16(coeffs@) =~= st0.coeffs);
    }
    let top_nz0 = top.nz;
    let left_nz0 = left.nz;
    let first: usize;
    let ac_type: usize;
    if !m.is_i4x4 {
        let mut dc: [i16; 16] = [0; 16];
        let ctx = (top.nz_dc % 2 + left.nz_dc % 2) as usize;
        let ghost z16 = Seq::new(16, |i: int| 0int);
        proof {
            assert(blk16(dc@, 0) =~= z16);
        }
        let ghost cb = coeffs@;
        let nz = get_coeffs(br, data, &hdr.proba, 1, ctx, q.y2, 0, &mut dc, 0, Ghost(p0), Ghost(g), Ghost(pr));
        let b = (nz > 0) as u32;
        top.nz_dc = b;
        left.nz_dc = b;
        let ghost bt = block_tokens(pt, g, pr, 1, 0, ctx as int, true, q.y2@[0] as int, q.y2@[1] as int, z16);
        proof {
            lemma_block_tokens_frame(pt, g, pr, 1, 0, ctx as int, true, q.y2@[0] as int, q.y2@[1] as int, z16);
            if ok0 && !br.eof {
                assert(c16(dc@) =~= blk16(dc@, 0));
                assert(c16(dc@) == bt.1);
            }
        }
        assert(cb == cz);
        if nz > 1 {
            transform_wht(&dc, coeffs);
            assert(forall|j: int| 0 <= j < 384 && j % 16 != 0 ==> #[trigger] coeffs@[j] == cz[j]);
        } else {
            proof {
                lemma_sar3((dc@[0] as i32 + 3) as i32);
            }
            let dc0 = ((dc[0] as i32 + 3) >> 3u32) as i16;
            let mut i: usize = 0;
            while i < 256
                invariant
                    data@.len() <= usize::MAX,
                    coeffs@.len() <= usize::MAX,
                    i <= 256,
                    i % 16 == 0,
                    coeffs@.len() == 384,
                    forall|j: int| 0 <= j < i && j % 16 == 0 ==> coeffs@[j] == dc0,
                    forall|j: int| 0 <= j < 384 && !(j < i && j % 16 == 0) ==> coeffs@[j] == cb[j],
                decreases 256 - i,
            {
                set16(coeffs, i, dc0);
                i = i + 16;
            }
            assert(forall|j: int| 0 <= j < 384 && j % 16 != 0 ==> #[trigger] coeffs@[j] == cz[j]);
            proof {
                if ok0 && !br.eof {
                    assert forall|j: int| 1 <= j < 16 implies bt.1[j] == 0 by {
                        assert(zigzag(0) == 0);
                        assert(forall|k: int| 0 <= k < bt.2 ==> zigzag(k) != j);
                        assert(z16[j] == 0);
                    }
                    assert(bt.1[0] == dc@[0]);
                    lemma_iwht_dc(bt.1);
                    assert forall|k: int| 0 <= k < 16 implies #[trigger] coeffs@[16 * k] == iwht(bt.1)[k] by {
                        assert((16 * k) % 16 == 0);
                    }
                }
            }
        }
        proof {
            st1 = y2_block(pt, st0, pr, q.y2@[0] as int, q.y2@[1] as int);
            if ok0 && !br.eof {
                assert(ctx == b2i(lc[8]) + b2i(tc[8]));
                let w = iwht(bt.1);
                assert forall|i: int| 0 <= i < 384 implies c16(coeffs@)[i] == st1.coeffs[i] by {
                    if i < 256 && i % 16 == 0 {
                        assert(coeffs@[16 * (i / 16)] == w[i / 16]);
                    } else {
                        assert(coeffs@[i] == cb[i]);
                    }
                }
                assert(c16(coeffs@) =~= st1.coeffs);
                assert(st1.s == bt.0);
            }
        }
        assert(forall|j: int| 0 <= j < 384 && j % 16 != 0 ==> #[trigger] coeffs@[j] == cz[j]);
        first = 1;
        ac_type = 0;
    } else {
        first = 0;
        ac_type = 3;
    }
    proof {
        assert(top_nz0 < 256 ==> (top_nz0 & 0x0fu32) == top_nz0 % 16 && (top_nz0 >> 4u32) == top_nz0 / 16 && (top_nz0
            >> 6u32) == top_nz0 / 64) by (bit_vector);
        assert(left_nz0 < 256 ==> (left_nz0 & 0x0fu32) == left_nz0 % 16 && (left_nz0 >> 4u32) == left_nz0 / 16 && (
        left_nz0 >> 6u32) == left_nz0 / 64) by (bit_vector);
        assert((top_nz0 & 0x0fu32) < 16 && (left_nz0 & 0x0fu32) < 16) by (bit_vector);
        assert(((top_nz0 >> 4u32) & 0x0fu32) < 16 && ((left_nz0 >> 4u32) & 0x0fu32) < 16 && ((top_nz0 >> 6u32) & 3u32)
            < 4 && ((left_nz0 >> 6u32) & 3u32) < 4) by (bit_vector);
        assert(top_nz0 < 256 ==> ((top_nz0 >> 4u32) & 0x0fu32) == top_nz0 / 16 && ((top_nz0 >> 6u32) & 3u32) == top_nz0
            / 64) by (bit_vector);
        assert(left_nz0 < 256 ==> ((left_nz0 >> 4u32) & 0x0fu32) == left_nz0 / 16 && ((left_nz0 >> 6u32) & 3u32)
            == left_nz0 / 64) by (bit_vector);
    }
    let ghost ok1 = ok0 && !br.eof;
    assert(forall|j: int| 0 <= j < 384 && j % 16 != 0 ==> #[trigger] coeffs@[j] == cz[j]);
    assert(ac_clear(coeffs@, 0, 384));
    let ry = resid_y(
        br,
        data,
        &hdr.proba,
        ac_type,
        first,
        q.y1,
        top_nz0 & 0x0f,
        left_nz0 & 0x0f,
        coeffs,
        Ghost(p0),
        Ghost(st1),
        Ghost(pr),
    );
    let ghost ti = ac_type as int;
    let ghost fi = first as int;
    let ghost sy = plane_blocks(pt, st1, pr, ti, fi, qs.0, qs.1, 0, 0, 4, 16);
    let ghost ok2 = ok0 && !br.eof;
    let ghost c1 = coeffs@;
    assert(ac_clear(coeffs@, 256, 320));
    proof {
        if ok2 {
            lemma_plane_blocks_frame(pt, st1, pr, ti, fi, qs.0, qs.1, 0, 0, 4, 16);
        }
    }
    let ru = resid_uv(
        br,
        data,
        &hdr.proba,
        q.uv,
        (top_nz0 >> 4u32) & 0x0f,
        (left_nz0 >> 4u32) & 0x0f,
        coeffs,
        256,
        Ghost(p0),
        Ghost(sy),
        Ghost(pr),
        Ghost(4),
        Ghost(b2i(tc[6]) + 2 * b2i(tc[7])),
        Ghost(b2i(lc[6]) + 2 * b2i(lc[7])),
    );
    let ghost su = plane_blocks(pt, sy, pr, 2, 0, qs.4, qs.5, 16, 4, 2, 4);
    let ghost ok3 = ok0 && !br.eof;
    let ghost c2 = coeffs@;
    assert(ac_clear(coeffs@, 320, 384));
    proof {
        if ok3 {
            lemma_plane_blocks_frame(pt, sy, pr, 2, 0, qs.4, qs.5, 16, 4, 2, 4);
        }
    }
    let rv = resid_uv(
        br,
        data,
        &hdr.proba,
        q.uv,
        (top_nz0 >> 6u32) & 3,
        (left_nz0 >> 6u32) & 3,
        coeffs,
        320,
        Ghost(p0),
        Ghost(su),
        Ghost(pr),
        Ghost(6),
        Ghost(0),
        Ghost(0),
    );
    let ghost sv = plane_blocks(pt, su, pr, 2, 0, qs.4, qs.5, 20, 6, 2, 4);
    proof {
        if ok0 && !br.eof {
            lemma_plane_blocks_frame(pt, su, pr, 2, 0, qs.4, qs.5, 20, 6, 2, 4);
        }
        let (a, b, c) = (ry.0, ru.0, rv.0);
        assert(a < 16 && b < 4 && c < 4 ==> (a | ((b << 4u32) << 0u32) | ((c << 4u32) << 2u32)) == a + 16 * b + 64 * c)
            by (bit_vector);
        let (d, e, f) = (ry.1, ru.1, rv.1);
        assert(d < 16 && (e == 0 || e == 16 || e == 32 || e == 48) && (f == 0 || f == 16 || f == 32 || f == 48) ==> (d | (
        e << 0u32) | (f << 2u32)) == d + e + 4 * f) by (bit_vector);
    }
    let non_zero_uv = ru.2 | (rv.2 << 8u32);
    top.nz = ry.0 | ((ru.0 << 4u32) << 0u32) | ((rv.0 << 4u32) << 2u32);
    left.nz = ry.1 | (ru.1 << 0u32) | (rv.1 << 2u32);
    proof {
        if ok0 && !br.eof {
            let e = mb_residuals(pt, g, pr, qs, m.is_i4x4, tc, lc);
            assert(e == sv);
            assert(top.is(sv.top));
            assert(left.is(sv.left));
            lemma_sel_keep(ry.2, 30, 16, c1, c2, 0);
            lemma_sel_keep(ry.2, 30, 16, c2, coeffs@, 0);
            lemma_sel_keep(ru.2, 6, 4, c2, coeffs@, 256);
            let (ua, va) = (ru.2, rv.2);
            assert(ua < 256 && va < 256 ==> (ua | (va << 8u32)) & 0xff == ua && ((ua | (va << 8u32)) >> 8u32) & 0xff == va)
                by (bit_vector);
            let ya = ry.2;
            assert((ya | (ua | (va << 8u32))) != 0 ==> ya != 0 || ua != 0 || va != 0) by (bit_vector);
            if mb_solid(pt, g, pr, qs, m.is_i4x4, tc, lc) {
                if ya != 0 {
                    lemma_any_keep(c1, c2, 0, 256, 0, 256);
                    lemma_any_keep(c2, coeffs@, 0, 256, 0, 384);
                } else if ua != 0 {
                    lemma_any_keep(c2, coeffs@, 256, 320, 0, 384);
                } else if va != 0 {
                    lemma_any_keep(coeffs@, coeffs@, 320, 384, 0, 384);
                }
            }
        }
    }
    Residuals { non_zero_y: ry.2, non_zero_uv }
}

impl Header {
    /// The fields the coefficients depend on are the specification's.
    pub open spec fn tok_matches(&self, fh: FrameHeader) -> bool {
        &&& probs_are(self.proba@, fh.probs)
        &&& forall|i: int| 0 <= i < 4 ==> quant_matches(#[trigger] self.dqm@[i], seg_quant(fh, i))
        &&& self.use_skip_proba == fh.mb_no_coeff_skip
    }
}

/// What the frame's token loop needs of a header that matches.
pub proof fn lemma_header_parts(hdr: Header, file: Seq<u8>, pstart: int, fh: FrameHeader)
    requires
        hdr.matches(file, pstart, fh),
        hdr.proba@.len() == 1056,
    ensures
        hdr.tok_matches(fh),
        num_parts(fh) == hdr.num_parts,
        forall|p: int|
            0 <= p < hdr.num_parts ==> part(file, #[trigger] hdr.part_start@[p] as int, hdr.part_end@[p] as int)
                == tok_part(file, pstart, hdr.num_parts - 1, p),
{
    assert forall|p: int| 0 <= p < hdr.num_parts implies part(
        file,
        #[trigger] hdr.part_start@[p] as int,
        hdr.part_end@[p] as int,
    ) == tok_part(file, pstart, hdr.num_parts - 1, p) by {
        if p < hdr.num_parts - 1 {
            assert(hdr.part_end@[p] == part_begin(file, pstart, hdr.num_parts - 1, (p + 1) as nat));
        }
    }
}

/// The empty context.
pub proof fn lemma_nz_zero()
    ensures
        (Nz { nz: 0, nz_dc: 0 }).is(Seq::new(9, |i: int| false)),
{
}

/// The coefficients of one macroblock, or none if it is flagged as skipped
/// (`VP8DecodeMB`). Returns what reconstruction needs, and whether the
/// macroblock has no coefficient at all.
///
/// The contexts, and the coefficients of a macroblock that is not flagged,
/// are the ones `vp8spec::mb_tokens` gives.
pub fn mb_coeffs(
    br: &mut BoolReader,
    data: &[u8],
    hdr: &Header,
    m: &MbModes,
    top: &mut Nz,
    left: &mut Nz,
    coeffs: &mut [i16],
    Ghost(p0): Ghost<int>,
    Ghost(g): Ghost<BoolState>,
    Ghost(fh): Ghost<FrameHeader>,
    Ghost(ms): Ghost<MbModeSpec>,
    Ghost(tc): Ghost<Seq<bool>>,
    Ghost(lc): Ghost<Seq<bool>>,
) -> (r: (Residuals, bool))
    requires
        old(br).inv(data@.len()),
        hdr.proba@.len() == 1056,
        m.segment < 4,
        old(coeffs)@.len() == 384,
        forall|s: int| 0 <= s < 4 ==> #[trigger] quant_ok(hdr.dqm@[s]),
    ensures
        final(br).inv(data@.len()),
        final(br).end == old(br).end,
        old(br).eof ==> final(br).eof,
        final(coeffs)@.len() == 384,
        old(br).rel(data@, p0, g) && hdr.tok_matches(fh) && m.matches(ms) && old(top).is(tc) && old(left).is(lc)
            && !final(br).eof ==> {
            let e = mb_tokens(part(data@, p0, old(br).end as int), g, fh, ms, tc, lc);
            &&& final(br).rel(data@, p0, e.s)
            &&& final(top).is(e.top)
            &&& final(left).is(e.left)
            &&& !(fh.mb_no_coeff_skip && ms.skip) ==> c16(final(coeffs)@) == e.coeffs && sels_ok(r.0, final(coeffs)@)
            &&& fh.mb_no_coeff_skip && ms.skip ==> r.0.non_zero_y == 0 && r.0.non_zero_uv == 0
            &&& tok_solid(part(data@, p0, old(br).end as int), g, fh, ms, tc, lc) ==> r.1 == !any_nz(e.coeffs)
        },
{
    let ghost pt = part(data@, p0, br.end as int);
    let ghost ok = br.rel(data@, p0, g) && hdr.tok_matches(fh) && m.matches(ms) && top.is(tc) && left.is(lc);
    let skip0 = if hdr.use_skip_proba {
        m.skip
    } else {
        false
    };
    if !skip0 {
        let ghost qs = seg_quant(fh, m.segment as int);
        proof {
            if hdr.tok_matches(fh) {
                assert(quant_matches(hdr.dqm@[m.segment as int], qs));
            }
        }
        let res = parse_residuals(
            br,
            data,
            hdr,
            m,
            top,
            left,
            coeffs,
            Ghost(p0),
            Ghost(g),
            Ghost(fh.probs),
            Ghost(qs),
            Ghost(tc),
            Ghost(lc),
        );
        let s = (res.non_zero_y | res.non_zero_uv) == 0;
        proof {
            if ok && !br.eof && tok_solid(pt, g, fh, ms, tc, lc) {
                let e = mb_tokens(pt, g, fh, ms, tc, lc);
                if s {
                    lemma_sels_zero(res, coeffs@);
                } else {
                    let w = choose|j: int| 0 <= j < 384 && #[trigger] coeffs@[j] != 0;
                    assert(c16(coeffs@)[w] != 0);
                }
            }
        }
        (res, s)
    } else {
        let ghost e = mb_tokens(part(data@, p0, br.end as int), g, fh, ms, tc, lc);
        top.nz = 0;
        left.nz = 0;
        if !m.is_i4x4 {
            top.nz_dc = 0;
            left.nz_dc = 0;
        }
        proof {
            if hdr.tok_matches(fh) && m.matches(ms) && old(top).is(tc) && old(left).is(lc) {
                assert(top.is(e.top));
                assert(left.is(e.left));
                assert(!any_nz(e.coeffs));
            }
        }
        (Residuals { non_zero_y: 0, non_zero_uv: 0 }, true)
    }
}

} // verus!
