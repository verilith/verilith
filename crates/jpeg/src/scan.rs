//! One scan: its MCUs, restart intervals, and the coefficients they give.
use crate::bits::*;
use crate::block::*;
use crate::huff::*;
use crate::spec::*;
use crate::stream::*;
use crate::types::*;
use crate::prims::*;
use crate::work::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// The coefficients of the (up to three) components, 64 per block.
///
/// When `stream` is set (see `stream.rs`) the arrays are windows: the
/// block rows of MCU row `row` only. The whole arrays are then ghost
/// state, and the samples of the rows before the window are in the
/// planes `p0`, `p1`, `p2`, computed with the quantization tables `sq`.
pub struct Coefs {
    pub a0: Vec<i16>,
    pub a1: Vec<i16>,
    pub a2: Vec<i16>,
    pub stream: bool,
    pub row: u32,
    pub g0: Ghost<Seq<i16>>,
    pub g1: Ghost<Seq<i16>>,
    pub g2: Ghost<Seq<i16>>,
    pub p0: Vec<u8>,
    pub p1: Vec<u8>,
    pub p2: Vec<u8>,
    pub sq: [[u16; 64]; 3],
    pub rl: [u8; 1024],
    pub kt: [i16; 24],
}

/// Block rows of component `c` in an MCU row of a streamed scan.
pub open spec fn srows(f: Frame, c: int) -> int {
    if f.nc == 1 {
        1
    } else {
        f.comps[c].v as int
    }
}

/// MCU rows of a streamed scan.
pub open spec fn stotal(f: Frame) -> int {
    if f.nc == 1 {
        hb(f, 0)
    } else {
        mcuy(f)
    }
}

impl Coefs {
    /// The coefficients of a frame of `nc` components.
    pub open spec fn view(&self, nc: int) -> Seq<Seq<i16>> {
        if self.stream {
            if nc == 1 {
                seq![self.g0@]
            } else {
                seq![self.g0@, self.g1@, self.g2@]
            }
        } else if nc == 1 {
            seq![self.a0@]
        } else {
            seq![self.a0@, self.a1@, self.a2@]
        }
    }

    /// Each component's array is whole MCUs.
    pub open spec fn wf(&self, f: Frame) -> bool {
        if self.stream {
            self.swf(f)
        } else {
            &&& self.a0.len() == csize(f, 0)
            &&& f.nc == 3 ==> self.a1.len() == csize(f, 1) && self.a2.len() == csize(f, 2)
        }
    }

    /// Streaming holds each component as `win_ok` says.
    #[verifier::opaque]
    pub open spec fn swf(&self, f: Frame) -> bool {
        &&& forall|m: int| 0 <= m < 1024 ==> (#[trigger] self.rl[m]) == range_limit(m)
        &&& self.kt@ == crate::idct16::kt_spec()
        &&& self.g0@.len() <= usize::MAX
        &&& f.nc == 3 ==> self.g1@.len() <= usize::MAX && self.g2@.len() <= usize::MAX
        &&& win_ok(self.a0@, self.g0@, self.p0@, self.sq[0]@, cw(f, 0), ch(f, 0), wb(f, 0), hb(f, 0), srows(f, 0), self.row as int)
        &&& f.nc == 3 ==> {
            &&& win_ok(
                self.a1@,
                self.g1@,
                self.p1@,
                self.sq[1]@,
                cw(f, 1),
                ch(f, 1),
                wb(f, 1),
                hb(f, 1),
                srows(f, 1),
                self.row as int,
            )
            &&& win_ok(
                self.a2@,
                self.g2@,
                self.p2@,
                self.sq[2]@,
                cw(f, 2),
                ch(f, 2),
                wb(f, 2),
                hb(f, 2),
                srows(f, 2),
                self.row as int,
            )
        }
    }

    /// The quantization tables the planes were computed with.
    #[verifier::opaque]
    pub open spec fn sqv(&self) -> Seq<Seq<u16>> {
        seq![self.sq[0]@, self.sq[1]@, self.sq[2]@]
    }

    /// What a streamed scan needs at MCU row `my`: the window is that
    /// row's, and the scan is the one sequential scan of every component.
    pub open spec fn spre(&self, f: Frame, s: Scan, my: int) -> bool {
        self.stream ==> self.row == my && kind(f, s) is Base && s.ns == f.nc
    }
}

/// The length of component `c`'s coefficient array.
#[verifier::opaque]
pub open spec fn csize(f: Frame, c: int) -> int {
    64 * (cw(f, c) * ch(f, c))
}

/// The sizes that follow from a frame header.
#[derive(Clone, Copy)]
pub struct Geom {
    pub maxh: u32,
    pub maxv: u32,
    pub mcux: u32,
    pub mcuy: u32,
    /// Per component: the coefficient array's width and height in blocks,
    /// the blocks that hold image data, and the size in samples.
    pub cw: [u32; 3],
    pub ch: [u32; 3],
    pub wb: [u32; 3],
    pub hb: [u32; 3],
    pub dw: [u32; 3],
    pub dh: [u32; 3],
}

/// What `geom` needs of a frame: one or three components with sampling
/// factors 1 to 4, and a size that is not zero.
pub open spec fn frame_basic(f: Frame) -> bool {
    &&& f.nc == 1 || f.nc == 3
    &&& f.comps.len() == f.nc
    &&& 1 <= f.w <= 65535
    &&& 1 <= f.h <= 65535
    &&& forall|c: int| 0 <= c < f.nc ==> 1 <= (#[trigger] f.comps[c]).h <= 4 && 1 <= f.comps[c].v <= 4
}

impl Geom {
    pub open spec fn wf(&self, f: Frame) -> bool {
        &&& self.maxh == maxh(f)
        &&& self.maxv == maxv(f)
        &&& self.mcux == mcux(f)
        &&& self.mcuy == mcuy(f)
        &&& 1 <= self.maxh <= 4
        &&& 1 <= self.maxv <= 4
        &&& self.mcux <= 0x1_0020
        &&& self.mcuy <= 0x1_0020
        &&& forall|c: int|
            0 <= c < f.nc ==> {
                &&& (#[trigger] self.cw[c]) == cw(f, c)
                &&& self.ch[c] == ch(f, c)
                &&& self.wb[c] == wb(f, c)
                &&& self.hb[c] == hb(f, c)
                &&& self.dw[c] == dw(f, c)
                &&& self.dh[c] == dh(f, c)
                &&& self.wb[c] <= self.cw[c]
                &&& self.hb[c] <= self.ch[c]
                &&& self.cw[c] <= 0x4_0080
                &&& self.ch[c] <= 0x4_0080
            }
    }
}

/// One component's entry of a frame's geometry.
pub proof fn lemma_geom_c(f: Frame, g: Geom, c: int)
    requires
        g.wf(f),
        0 <= c < f.nc,
    ensures
        g.cw[c] == cw(f, c),
        g.ch[c] == ch(f, c),
        g.wb[c] == wb(f, c),
        g.hb[c] == hb(f, c),
        g.wb[c] <= g.cw[c],
        g.hb[c] <= g.ch[c],
        g.cw[c] <= 0x4_0080,
        g.ch[c] <= 0x4_0080,
{
    assert(g.cw[c] == cw(f, c));
}

/// `a <= ceil(a / b) * b`.
pub proof fn lemma_cdiv(a: int, b: int)
    requires
        a >= 0,
        b > 0,
    ensures
        a <= cdiv(a, b) * b,
        0 <= cdiv(a, b) <= a,
{
    lemma_fundamental_div_mod(a + b - 1, b);
    lemma_mod_bound(a + b - 1, b);
    let q = (a + b - 1) / b;
    assert(b * q == q * b) by (nonlinear_arith);
    assert(q >= 0 && q <= a) by (nonlinear_arith)
        requires
            a >= 0,
            b > 0,
            q == (a + b - 1) / b,
            a + b - 1 == b * q + (a + b - 1) % b,
            0 <= (a + b - 1) % b < b,
    ;
}

/// `ceil(a * k / b) <= ceil(a / b) * k`.
pub proof fn lemma_cdiv_mul(a: int, b: int, k: int)
    requires
        a >= 0,
        b > 0,
        k >= 0,
    ensures
        cdiv(a * k, b) <= cdiv(a, b) * k,
{
    lemma_cdiv(a, b);
    let m = cdiv(a, b);
    assert(a * k <= (m * k) * b) by (nonlinear_arith)
        requires
            a <= m * b,
            k >= 0,
            a >= 0,
    ;
    lemma_fundamental_div_mod_converse((m * k) * b + b - 1, b, m * k, b - 1);
    lemma_div_is_ordered(a * k + b - 1, (m * k) * b + b - 1, b);
}

pub fn geom(f: &FrameX) -> (g: Geom)
    requires
        frame_basic(f@),
    ensures
        g.wf(f@),
{
    let ghost fv = f@;
    assert(fv.comps[0] == f.comps[0]);
    let mut maxh_: u32 = f.comps[0].h as u32;
    let mut maxv_: u32 = f.comps[0].v as u32;
    if f.nc == 3 {
        assert(fv.comps[1] == f.comps[1] && fv.comps[2] == f.comps[2]);
        if f.comps[1].h as u32 > maxh_ {
            maxh_ = f.comps[1].h as u32;
        }
        if f.comps[2].h as u32 > maxh_ {
            maxh_ = f.comps[2].h as u32;
        }
        if f.comps[1].v as u32 > maxv_ {
            maxv_ = f.comps[1].v as u32;
        }
        if f.comps[2].v as u32 > maxv_ {
            maxv_ = f.comps[2].v as u32;
        }
    }
    let w = f.w as u32;
    let h = f.h as u32;
    let mcux_ = (w + 8 * maxh_ - 1) / (8 * maxh_);
    let mcuy_ = (h + 8 * maxv_ - 1) / (8 * maxv_);
    proof {
        lemma_cdiv(w as int, 8 * maxh_);
        lemma_cdiv(h as int, 8 * maxv_);
    }
    let mut g = Geom { maxh: maxh_, maxv: maxv_, mcux: mcux_, mcuy: mcuy_, cw: [0; 3], ch: [0; 3], wb: [0; 3], hb: [0; 3], dw: [0; 3], dh: [0; 3] };
    let mut c: usize = 0;
    while c < f.nc as usize
        invariant
            c <= f.nc <= 3,
            fv == f@,
            frame_basic(fv),
            w == f.w,
            h == f.h,
            g.maxh == maxh_ == maxh(fv),
            g.maxv == maxv_ == maxv(fv),
            g.mcux == mcux_ == mcux(fv),
            g.mcuy == mcuy_ == mcuy(fv),
            1 <= maxh_ <= 4,
            1 <= maxv_ <= 4,
            mcux_ <= 0x1_0020,
            mcuy_ <= 0x1_0020,
            forall|j: int|
                0 <= j < c ==> {
                    &&& (#[trigger] g.cw[j]) == cw(fv, j)
                    &&& g.ch[j] == ch(fv, j)
                    &&& g.wb[j] == wb(fv, j)
                    &&& g.hb[j] == hb(fv, j)
                    &&& g.dw[j] == dw(fv, j)
                    &&& g.dh[j] == dh(fv, j)
                    &&& g.wb[j] <= g.cw[j]
                    &&& g.hb[j] <= g.ch[j]
                    &&& g.cw[j] <= 0x4_0080
                    &&& g.ch[j] <= 0x4_0080
                },
        decreases 3 - c,
    {
        assert(fv.comps[c as int] == f.comps[c as int]);
        let ch_ = f.comps[c].h as u32;
        let cv = f.comps[c].v as u32;
        proof {
            lemma_cdiv_mul(w as int, 8 * maxh_, ch_ as int);
            lemma_cdiv_mul(h as int, 8 * maxv_, cv as int);
            assert(mcux_ * ch_ <= 0x4_0080 && mcuy_ * cv <= 0x4_0080 && w * ch_ <= 0x4_0000 && h * cv <= 0x4_0000)
                by (nonlinear_arith)
                requires
                    mcux_ <= 0x1_0020,
                    mcuy_ <= 0x1_0020,
                    w <= 65535,
                    h <= 65535,
                    1 <= ch_ <= 4,
                    1 <= cv <= 4,
            ;
        }
        g.cw[c] = mcux_ * ch_;
        g.ch[c] = mcuy_ * cv;
        g.wb[c] = (w * ch_ + 8 * maxh_ - 1) / (8 * maxh_);
        g.hb[c] = (h * cv + 8 * maxv_ - 1) / (8 * maxv_);
        g.dw[c] = (w * ch_ + maxh_ - 1) / maxh_;
        g.dh[c] = (h * cv + maxv_ - 1) / maxv_;
        proof {
            let ci = c as int;
            assert(g.cw[ci] == cw(fv, ci));
            assert(g.ch[ci] == ch(fv, ci));
            assert(g.wb[ci] == wb(fv, ci));
            assert(g.hb[ci] == hb(fv, ci));
            assert(g.dw[ci] == dw(fv, ci));
            assert(g.dh[ci] == dh(fv, ci));
            assert(g.wb[ci] <= g.cw[ci]);
            assert(g.hb[ci] <= g.ch[ci]);
        }
        c += 1;
    }
    assert(fv == f@);
    assert(g.maxh == maxh(fv) && g.maxv == maxv(fv) && g.mcux == mcux(fv) && g.mcuy == mcuy(fv));
    assert(1 <= g.maxh <= 4 && 1 <= g.maxv <= 4 && g.mcux <= 0x1_0020 && g.mcuy <= 0x1_0020);
    assert forall|c: int| 0 <= c < fv.nc implies {
        &&& (#[trigger] g.cw[c]) == cw(fv, c)
        &&& g.ch[c] == ch(fv, c)
        &&& g.wb[c] == wb(fv, c)
        &&& g.hb[c] == hb(fv, c)
        &&& g.dw[c] == dw(fv, c)
        &&& g.dh[c] == dh(fv, c)
        &&& g.wb[c] <= g.cw[c]
        &&& g.hb[c] <= g.ch[c]
        &&& g.cw[c] <= 0x4_0080
        &&& g.ch[c] <= 0x4_0080
    } by {}
    assert(g.wf(fv));
    g
}

/// The positions a scan's segments can start at, for a scan whose data
/// starts at `pi`: in the input or just past its end, or where the scan
/// itself started if that is further.
pub open spec fn seg_ok(d: Seq<u8>, pi: int, p: int) -> bool {
    &&& 0 <= p
    &&& pi <= d.len() + 0x1_0008
    &&& p <= d.len() + 2 || p == pi || (p == pi + 1 && (p - d.len()) % 2 == 0)
}

pub proof fn lemma_resync_le(d: Seq<u8>, m: u8, q: int, want: int)
    requires
        q <= d.len() + 2,
    ensures
        resync(d, m, q, want).0 <= d.len() + 2,
    decreases togo(q, d.len() as int + 1),
{
    if q > d.len() {
    } else if m < 0xC0 || m == 0xD0 + (want + 7) % 8 || m == 0xD0 + (want + 6) % 8 {
        lemma_marker_after(d, q);
        let (m2, q2) = marker_after(d, q);
        lemma_resync_le(d, m2, q2, want);
    }
}

/// Where a restart goes on from.
pub open spec fn restart_p(d: Seq<u8>, p: int, rst: int) -> (int, bool) {
    let (m, q) = marker_after(d, p);
    if m == 0xD0 + rst {
        (q, true)
    } else {
        resync(d, m, q, rst)
    }
}

pub proof fn lemma_restart_seg(d: Seq<u8>, pi: int, p: int, rst: int)
    requires
        seg_ok(d, pi, p),
        0 <= rst < 8,
    ensures
        seg_ok(d, pi, restart_p(d, p, rst).0),
{
    lemma_marker_after(d, p);
    let (m, q) = marker_after(d, p);
    lemma_resync_p(d, m, q, rst);
    if p <= d.len() {
        lemma_resync_le(d, m, q, rst);
    } else {
        assert(m == 0xD9);
        assert(resync(d, m, q, rst) == (q - 2, false));
    }
}

pub fn resync_x(data: &[u8], m: u8, q: usize, want: u8, Tracked(mt): Tracked<&mut Meter>) -> (r: (usize, bool))
    requires
        len_ok(data@),
        2 <= q <= data@.len() + 0x1_0020,
        want < 8,
    ensures
        (r.0 as int, r.1) == resync(data@, m, q as int, want as int),
        final(mt).n + 3 * q <= old(mt).n + 3 * r.0 + 6,
        q <= r.0 + 2,
{
    let mut mm = m;
    let mut qq = q;
    loop
        invariant
            len_ok(data@),
            2 <= qq <= data@.len() + 0x1_0020,
            want < 8,
            resync(data@, mm, qq as int, want as int) == resync(data@, m, q as int, want as int),
            q <= qq,
            mt.n + 3 * q <= old(mt).n + 3 * qq,
        decreases togo(qq as int, data@.len() as int + 1),
    {
        proof {
            lemma_marker_after(data@, qq as int);
        }
        if qq > data.len() {
            return (qq - 2, false);
        } else if mm < 0xC0 || mm == 0xD0 + (want + 7) % 8 || mm == 0xD0 + (want + 6) % 8 {
            let (m2, q2) = marker_after_x(data, qq, Tracked(mt));
            proof {
                mt.n = mt.n + 1;
            }
            mm = m2;
            qq = q2;
        } else if mm < 0xD0 || mm > 0xD7 || mm == 0xD0 + (want + 1) % 8 || mm == 0xD0 + (want + 2) % 8 {
            return (qq - 2, false);
        } else {
            return (qq, true);
        }
    }
}

/// The state of a scan between MCUs.
pub struct ScanSt {
    pub br: BitReader,
    pub pred: [i32; 3],
    pub eob: u32,
    pub insuf: bool,
    pub togo: i64,
    pub rst: u8,
}

/// The scan state of the specification that `st` stands for, over
/// coefficients `a`.
pub open spec fn ssv(st: ScanSt, a: Seq<Seq<i16>>) -> SS {
    SS {
        a,
        pred: seq![st.pred[0] as int, st.pred[1] as int, st.pred[2] as int],
        eob: st.eob as int,
        p: st.br.p0@,
        n: st.br.n@,
        insuf: st.insuf,
        togo: st.togo as int,
        rst: st.rst as int,
        ok: true,
    }
}

pub open spec fn kcode(k: Kind) -> int {
    match k {
        Kind::Base => 0,
        Kind::DcFirst => 1,
        Kind::DcRefine => 2,
        Kind::AcFirst => 3,
        Kind::AcRefine => 4,
    }
}

/// The part of `scan_ok` that does not depend on the tables or the MCU's
/// size: checked where the scan header is read.
pub open spec fn scan_pre(f: Frame, s: Scan) -> bool {
    scan_struct(f, s) && scan_params(f, s)
}

/// The scan's components are components of the frame, each once.
pub open spec fn scan_struct(f: Frame, s: Scan) -> bool {
    &&& 1 <= s.ns <= f.nc
    &&& forall|i: int| 0 <= i < s.ns ==> 0 <= (#[trigger] s.ci[i]) < f.nc
    &&& forall|i: int, j: int| 0 <= i < j < s.ns ==> s.ci[i] != s.ci[j]
}

/// The progression parameters are ones the decoder takes.
pub open spec fn scan_params(f: Frame, s: Scan) -> bool {
    match kind(f, s) {
        Kind::Base => true,
        Kind::DcFirst => s.se == 0 && s.al <= 13,
        Kind::DcRefine => s.se == 0 && s.al <= 13 && s.al == s.ah - 1,
        Kind::AcFirst => s.ss <= s.se < 64 && s.ns == 1 && s.al <= 13,
        Kind::AcRefine => s.ss <= s.se < 64 && s.ns == 1 && s.al <= 13 && s.al == s.ah - 1,
    }
}

/// The part of `scan_ok` about the Huffman tables.
pub open spec fn scan_tabs(f: Frame, t: Tables, s: Scan) -> bool {
    match kind(f, s) {
        Kind::Base => forall|i: int|
            0 <= i < s.ns ==> {
                &&& 0 <= (#[trigger] s.td[i]) < 4 && t.dcdef[s.td[i] as int] && huff_dc_ok(t.dc[s.td[i] as int])
                &&& 0 <= s.ta[i] < 4 && t.acdef[s.ta[i] as int] && huff_ok(t.ac[s.ta[i] as int])
            },
        Kind::DcFirst => forall|i: int|
            0 <= i < s.ns ==> 0 <= (#[trigger] s.td[i]) < 4 && t.dcdef[s.td[i] as int] && huff_dc_ok(
                t.dc[s.td[i] as int],
            ),
        Kind::DcRefine => true,
        _ => 0 <= s.ta[0] < 4 && t.acdef[s.ta[0] as int] && huff_ok(t.ac[s.ta[0] as int]),
    }
}

pub proof fn lemma_scan_ok(f: Frame, t: Tables, s: Scan)
    ensures
        scan_ok(f, t, s) <==> scan_pre(f, s) && mcu_blocks(f, s) <= 10 && scan_tabs(f, t, s),
{
}

/// Block `b` of an interleaved MCU belongs to scan component `i`, at
/// column `x` and row `y` of that component's part of the MCU.
pub open spec fn slot_ok(f: Frame, s: Scan, b: int, i: int, x: int, y: int) -> bool {
    let (i2, off) = blk_slot(f, s, b, 0);
    let c = s.ci[i2] as int;
    let h = f.comps[c].h as int;
    let v = f.comps[c].v as int;
    &&& i == i2
    &&& 0 <= i < s.ns
    &&& 0 <= off < h * v
    &&& x == off % h
    &&& y == off / h
}

/// What a scan needs that does not change from MCU to MCU.
pub struct ScanCtx {
    /// 0 sequential, 1 DC first, 2 DC refinement, 3 AC first, 4 AC
    /// refinement.
    pub kind: u8,
    pub nb: usize,
    /// For each block of an MCU: its component's index in the scan, and
    /// its column and row within the component's part of the MCU.
    pub bi: [u8; 10],
    pub bdx: [u8; 10],
    pub bdy: [u8; 10],
    pub dcd: [Derived; 3],
    pub acd: [Derived; 3],
}

impl ScanCtx {
    pub open spec fn wf(&self, f: Frame, t: Tables, s: Scan) -> bool {
        &&& self.kind == kcode(kind(f, s))
        &&& self.nb == mcu_blocks(f, s)
        &&& self.nb <= 10
        &&& s.ns == 1 ==> self.bi[0] == 0
        &&& s.ns > 1 ==> forall|b: int|
            0 <= b < self.nb ==> slot_ok(f, s, b, (#[trigger] self.bi[b]) as int, self.bdx[b] as int, self.bdy[b] as int)
        &&& scan_tabs(f, t, s)
        &&& (kind(f, s) is Base || kind(f, s) is DcFirst) ==> forall|i: int|
            0 <= i < s.ns ==> (#[trigger] self.dcd[i]).wf(t.dc[s.td[i] as int])
        &&& !(kind(f, s) is DcFirst || kind(f, s) is DcRefine) ==> forall|i: int|
            0 <= i < s.ns ==> (#[trigger] self.acd[i]).wf(t.ac[s.ta[i] as int])
    }
}

/// Blocks of scan component `k` in an interleaved MCU.
pub open spec fn nblk(f: Frame, s: Scan, k: int) -> int {
    f.comps[s.ci[k] as int].h as int * f.comps[s.ci[k] as int].v as int
}

pub proof fn lemma_blocks_mono(f: Frame, s: Scan, a: int, b: int)
    requires
        0 <= a <= b,
    ensures
        blocks_upto(f, s, a) <= blocks_upto(f, s, b),
    decreases b - a,
{
    if a < b {
        lemma_blocks_mono(f, s, a, b - 1);
        let h = f.comps[s.ci[b - 1] as int].h as int;
        let v = f.comps[s.ci[b - 1] as int].v as int;
        assert(h * v >= 0) by (nonlinear_arith)
            requires
                h >= 0,
                v >= 0,
        ;
    }
}

pub proof fn lemma_blk_slot(f: Frame, s: Scan, i: int, j: int, off: int)
    requires
        0 <= j <= i < s.ns,
        0 <= off < nblk(f, s, i),
    ensures
        blk_slot(f, s, blocks_upto(f, s, i) - blocks_upto(f, s, j) + off, j) == (i, off),
    decreases i - j,
{
    if j < i {
        lemma_blocks_mono(f, s, j + 1, i);
        assert(blocks_upto(f, s, j + 1) == blocks_upto(f, s, j) + nblk(f, s, j));
        lemma_blk_slot(f, s, i, j + 1, off);
    }
}

/// The tables and block layout of a scan, or `None` if the scan is not
/// one the decoder takes.
pub fn make_ctx(f: &FrameX, t: &Tabs, s: &ScanX) -> (r: Option<ScanCtx>)
    requires
        frame_basic(f@),
        scan_pre(f@, s@),
        s.ns <= 3,
    ensures
        r is Some <==> scan_ok(f@, t@, s@),
        r matches Some(cx) ==> cx.wf(f@, t@, s@),
{
    let ghost fv = f@;
    let ghost tv = t@;
    let ghost sv = s@;
    proof {
        lemma_scan_ok(fv, tv, sv);
    }
    let ns = s.ns as usize;
    let kd: u8 = if !f.prog {
        0
    } else if s.ss == 0 {
        if s.ah == 0 {
            1
        } else {
            2
        }
    } else if s.ah == 0 {
        3
    } else {
        4
    };
    let none = Derived { lim: [0; 17], off: [0; 17], ll: [0; 17], look: [0; 1024] };
    let mut cx = ScanCtx { kind: kd, nb: 0, bi: [0; 10], bdx: [0; 10], bdy: [0; 10], dcd: [none; 3], acd: [none; 3] };
    // Tables.
    let mut i: usize = 0;
    while i < ns
        invariant
            i <= ns == s.ns <= 3,
            fv == f@,
            tv == t@,
            sv == s@,
            kd == kcode(kind(fv, sv)),
            scan_pre(fv, sv),
            cx.kind == kd,
            cx.bi[0] == 0,
            forall|j: int|
                0 <= j < i && (kd == 0 || kd == 1) ==> {
                    &&& 0 <= (#[trigger] sv.td[j]) < 4
                    &&& tv.dcdef[sv.td[j]]
                    &&& huff_dc_ok(tv.dc[sv.td[j]])
                    &&& cx.dcd[j].wf(tv.dc[sv.td[j]])
                },
            forall|j: int|
                0 <= j < i && (kd == 0 || kd >= 3) ==> {
                    &&& 0 <= (#[trigger] sv.ta[j]) < 4
                    &&& tv.acdef[sv.ta[j]]
                    &&& huff_ok(tv.ac[sv.ta[j]])
                    &&& cx.acd[j].wf(tv.ac[sv.ta[j]])
                },
        decreases ns - i,
    {
        if kd == 0 || kd == 1 {
            let n = s.td[i] as usize;
            assert(sv.td[i as int] == n);
            if n >= 4 || !t.dcdef[n] {
                assert(!scan_tabs(fv, tv, sv)) by {
                    let x = sv.td[i as int];
                }
                return None;
            }
            assert(tv.dc[n as int] == t.dc[n as int]@);
            match derive(&t.dc[n], true) {
                Some(d) => {
                    cx.dcd[i] = d;
                },
                None => {
                    assert(!scan_tabs(fv, tv, sv)) by {
                    let x = sv.td[i as int];
                }
                    return None;
                },
            }
        }
        if kd == 0 || kd >= 3 {
            let n = s.ta[i] as usize;
            assert(sv.ta[i as int] == n);
            if n >= 4 || !t.acdef[n] {
                assert(!scan_tabs(fv, tv, sv)) by {
                    let x = sv.td[i as int];
                }
                return None;
            }
            assert(tv.ac[n as int] == t.ac[n as int]@);
            match derive(&t.ac[n], false) {
                Some(d) => {
                    cx.acd[i] = d;
                },
                None => {
                    assert(!scan_tabs(fv, tv, sv)) by {
                    let x = sv.td[i as int];
                }
                    return None;
                },
            }
        }
        i += 1;
    }
    assert(scan_tabs(fv, tv, sv));
    // The MCU's blocks.
    if ns == 1 {
        cx.nb = 1;
    } else {
        let mut nb: usize = 0;
        let mut i: usize = 0;
        while i < ns
            invariant
                i <= ns == s.ns <= 3,
                ns > 1,
                fv == f@,
                sv == s@,
                frame_basic(fv),
                scan_pre(fv, sv),
                nb == blocks_upto(fv, sv, i as int),
                nb <= 10,
                cx.kind == kd,
                forall|b: int|
                    0 <= b < nb ==> slot_ok(fv, sv, b, (#[trigger] cx.bi[b]) as int, cx.bdx[b] as int, cx.bdy[b] as int),
            decreases ns - i,
        {
            let c = s.ci[i] as usize;
            assert(sv.ci[i as int] == c);
            assert(fv.comps[c as int] == f.comps[c as int]);
            let h = f.comps[c].h;
            let v = f.comps[c].v;
            assert(1 <= (h as int) * (v as int) <= 16) by (nonlinear_arith)
                requires
                    1 <= h <= 4,
                    1 <= v <= 4,
            ;
            let n = (h as usize) * (v as usize);
            assert(blocks_upto(fv, sv, i + 1) == nb + n);
            if nb + n > 10 {
                proof {
                    lemma_blocks_mono(fv, sv, i + 1, ns as int);
                }
                return None;
            }
            let ghost nb0 = nb;
            let mut off: usize = 0;
            while off < n
                invariant
                    off <= n,
                    nb == nb0 + off,
                    nb0 + n <= 10,
                    i < ns == s.ns <= 3,
                    ns > 1,
                    fv == f@,
                    sv == s@,
                    1 <= n <= 16,
                    1 <= h <= 4,
                    1 <= v <= 4,
                    n == h as int * v as int,
                    sv.ci[i as int] == c,
                    fv.comps[c as int].h == h,
                    fv.comps[c as int].v == v,
                    nb0 == blocks_upto(fv, sv, i as int),
                    cx.kind == kd,
                    forall|b: int|
                        0 <= b < nb ==> slot_ok(
                            fv,
                            sv,
                            b,
                            (#[trigger] cx.bi[b]) as int,
                            cx.bdx[b] as int,
                            cx.bdy[b] as int,
                        ),
                decreases n - off,
            {
                proof {
                    lemma_blk_slot(fv, sv, i as int, 0, off as int);
                }
                cx.bi[nb] = i as u8;
                cx.bdx[nb] = (off % (h as usize)) as u8;
                cx.bdy[nb] = (off / (h as usize)) as u8;
                assert(slot_ok(fv, sv, nb as int, cx.bi[nb as int] as int, cx.bdx[nb as int] as int, cx.bdy[nb as int] as int));
                nb += 1;
                off += 1;
            }
            i += 1;
        }
        cx.nb = nb;
    }
    Some(cx)
}

} // verus!

verus! {

/// One block of a scan: block `o / 64` of component `c`, which is the
/// scan's component `i`.
pub open spec fn block_ss(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, i: int, c: int, o: int) -> SS {
    let e = ecs(d, st.p);
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
        Kind::DcRefine => {
            let (a2, n2) = dc_refine(e, st.n, s.al as int, st.a[c], o);
            SS { a: st.a.update(c, a2), n: n2, ..st }
        },
        Kind::AcFirst => {
            if st.eob > 0 {
                SS { eob: st.eob - 1, ..st }
            } else {
                let (a2, n2, run) = ac_first(
                    t.ac[s.ta[0] as int],
                    e,
                    st.n,
                    s.ss as int,
                    s.se as int,
                    s.al as int,
                    st.a[c],
                    o,
                );
                SS { a: st.a.update(c, a2), n: n2, eob: run, ..st }
            }
        },
        Kind::AcRefine => {
            if st.eob > 0 {
                let (a2, n2) = refine_rest(e, st.n, s.ss as int, s.se as int, s.al as int, st.a[c], o);
                SS { a: st.a.update(c, a2), n: n2, eob: st.eob - 1, ..st }
            } else {
                let (a2, n2, run) = ac_refine(
                    t.ac[s.ta[0] as int],
                    e,
                    st.n,
                    s.ss as int,
                    s.se as int,
                    s.al as int,
                    st.a[c],
                    o,
                );
                SS { a: st.a.update(c, a2), n: n2, eob: run, ..st }
            }
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
#[inline(always)]
fn block_x(
    data: &[u8],
    t: &Tabs,
    s: &ScanX,
    cx: &ScanCtx,
    st: &mut ScanSt,
    a: &mut Vec<i16>,
    o: usize,
    i: usize,
    Ghost(f): Ghost<Frame>,
    Ghost(av): Ghost<Seq<Seq<i16>>>,
    Ghost(c): Ghost<int>,
) -> (ok: bool)
    requires
        old(st).br.wf(data@),
        cx.wf(f, t@, s@),
        scan_pre(f, s@),
        s.ns <= 3,
        i < s.ns,
        0 <= c < av.len(),
        av[c] == old(a)@,
        o + 64 <= old(a).len(),
    ensures
        final(st).br.wf(data@),
        final(st).br.p0 == old(st).br.p0,
        final(st).insuf == old(st).insuf,
        final(st).togo == old(st).togo,
        final(st).rst == old(st).rst,
        final(a).len() == old(a).len(),
        ({
            let sp = block_ss(data@, f, t@, s@, ssv(*old(st), av), i as int, c, o as int);
            &&& sp.ok == ok
            &&& ok ==> ssv(*final(st), av.update(c, final(a)@)) == sp
        }),
{
    let ghost tv = t@;
    let ghost sv = s@;
    let ghost st0 = ssv(*st, av);
    let ghost sp = block_ss(data@, f, tv, sv, st0, i as int, c, o as int);
    let ghost ii = i as int;
    assert(sv.td[ii] == s.td[ii] && sv.ta[ii] == s.ta[ii] && sv.ta[0] == s.ta[0]);
    if cx.kind == 0 {
        assert(tv.dc[sv.td[ii]] == t.dc[s.td[ii] as int]@);
        assert(tv.ac[sv.ta[ii]] == t.ac[s.ta[ii] as int]@);
        assert(cx.dcd[ii].wf(tv.dc[sv.td[ii]]));
        assert(cx.acd[ii].wf(tv.ac[sv.ta[ii]]));
        let p = base_block_x(
            &mut st.br,
            data,
            sref(cx.dcd.as_slice(), i),
            sref(t.dc.as_slice(), sget(s.td.as_slice(), i) as usize),
            sref(cx.acd.as_slice(), i),
            sref(t.ac.as_slice(), sget(s.ta.as_slice(), i) as usize),
            sget(st.pred.as_slice(), i),
            a,
            o,
        );
        st.pred[i] = p;
        proof {
            let fin = ssv(*st, av.update(c, a@));
            assert(fin.pred =~= sp.pred);
            assert(fin == sp);
        }
        true
    } else if cx.kind == 1 {
        assert(tv.dc[sv.td[ii]] == t.dc[s.td[ii] as int]@);
        assert(cx.dcd[ii].wf(tv.dc[sv.td[ii]]));
        match dc_first_x(&mut st.br, data, &cx.dcd[i], &t.dc[s.td[i] as usize], st.pred[i], s.al, a, o) {
            Some(p) => {
                st.pred[i] = p;
                proof {
                    let fin = ssv(*st, av.update(c, a@));
                    assert(fin.pred =~= sp.pred);
                    assert(fin == sp);
                }
                true
            },
            None => false,
        }
    } else if cx.kind == 2 {
        dc_refine_x(&mut st.br, data, s.al, a, o);
        proof {
            let fin = ssv(*st, av.update(c, a@));
            assert(fin == sp);
        }
        true
    } else if cx.kind == 3 {
        assert(tv.ac[sv.ta[0]] == t.ac[s.ta[0] as int]@);
        assert(cx.acd[0].wf(tv.ac[sv.ta[0]]));
        if st.eob > 0 {
            st.eob -= 1;
            proof {
                assert(av.update(c, a@) =~= av);
            }
        } else {
            st.eob = ac_first_x(&mut st.br, data, &cx.acd[0], &t.ac[s.ta[0] as usize], s.ss, s.se, s.al, a, o);
        }
        proof {
            let fin = ssv(*st, av.update(c, a@));
            assert(fin == sp);
        }
        true
    } else {
        assert(tv.ac[sv.ta[0]] == t.ac[s.ta[0] as int]@);
        assert(cx.acd[0].wf(tv.ac[sv.ta[0]]));
        if st.eob > 0 {
            refine_rest_x(&mut st.br, data, s.ss as usize, s.se, s.al, a, o);
            st.eob -= 1;
        } else {
            st.eob = ac_refine_x(&mut st.br, data, &cx.acd[0], &t.ac[s.ta[0] as usize], s.ss, s.se, s.al, a, o);
        }
        proof {
            let fin = ssv(*st, av.update(c, a@));
            assert(fin == sp);
        }
        true
    }
}

} // verus!

verus! {

/// The blocks of MCU `m`.
pub open spec fn mcu_body(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int) -> SS {
    match kind(f, s) {
        Kind::AcFirst | Kind::AcRefine => mcu_ac(d, f, t, s, st, m),
        _ => mcu_dc(d, f, t, s, st, m, 0),
    }
}

/// MCUs per row and MCU rows of a scan.
pub open spec fn mcu_w(f: Frame, s: Scan) -> int {
    if s.ns == 1 {
        wb(f, s.ci[0] as int)
    } else {
        mcux(f)
    }
}

pub open spec fn mcu_h(f: Frame, s: Scan) -> int {
    if s.ns == 1 {
        hb(f, s.ci[0] as int)
    } else {
        mcuy(f)
    }
}

pub proof fn lemma_mcu_dc_notok(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int, b: int)
    requires
        !st.ok,
    ensures
        !mcu_dc(d, f, t, s, st, m, b).ok,
    decreases mcu_blocks(f, s) - b,
{
    if b < mcu_blocks(f, s) {
        lemma_mcu_dc_notok(d, f, t, s, mcu_dc_block(d, f, t, s, st, m, b), m, b + 1);
    }
}

pub proof fn lemma_scan_notok(d: Seq<u8>, f: Frame, t: Tables, s: Scan, st: SS, m: int)
    requires
        !st.ok,
    ensures
        !scan_from(d, f, t, s, st, m).ok,
    decreases scan_mcus(f, s) - m,
{
    if m < scan_mcus(f, s) {
        let st1 = if t.ri != 0 && st.togo == 0 {
            restart(d, t, st)
        } else {
            st
        };
        lemma_mcu_dc_notok(d, f, t, s, st1, m, 0);
        lemma_scan_notok(d, f, t, s, mcu_step(d, f, t, s, st, m), m + 1);
    }
}

/// Row `y`, column `x` of a `w` by `h` grid of blocks.
pub proof fn lemma_grid(y: int, x: int, h: int, w: int)
    requires
        0 <= y < h,
        0 <= x < w,
    ensures
        0 <= y * w <= y * w + x < w * h,
        64 * (y * w + x) + 64 <= 64 * (w * h),
{
    assert(0 <= y * w && y * w + w <= w * h) by (nonlinear_arith)
        requires
            0 <= y < h,
            0 < w,
    ;
}

/// Part `r` of unit `a`, each unit having `k` parts.
pub proof fn lemma_sub(a: int, r: int, n: int, k: int)
    requires
        0 <= a < n,
        0 <= r < k,
    ensures
        0 <= a * k <= a * k + r < n * k,
{
    assert(0 <= a * k && a * k + k <= n * k) by (nonlinear_arith)
        requires
            0 <= a < n,
            0 < k,
    ;
}

/// Component `c`'s coefficients are not more than a vector can hold.
pub open spec fn fits(f: Frame, c: int) -> bool {
    csize(f, c) <= usize::MAX
}

/// Block `b` of the MCU in row `my`, column `mx`: its component's index
/// in the scan and in the frame, and the block's number in the
/// component's coefficient array.
fn blk_idx_x(f: &FrameX, g: &Geom, s: &ScanX, cx: &ScanCtx, my: u32, mx: u32, b: usize, Ghost(tv): Ghost<Tables>) -> (r: (
    usize,
    usize,
    usize,
    usize,
))
    requires
        frame_basic(f@),
        g.wf(f@),
        scan_pre(f@, s@),
        s.ns <= 3,
        cx.wf(f@, tv, s@),
        forall|c: int| 0 <= c < f@.nc ==> fits(f@, c),
        b < cx.nb,
        my < mcu_h(f@, s@),
        mx < mcu_w(f@, s@),
    ensures
        r.0 < s.ns,
        r.1 == s@.ci[r.0 as int],
        r.1 < f@.nc,
        blk_index(f@, s@, my * mcu_w(f@, s@) + mx, b as int) == (r.0 as int, r.2 as int),
        64 * r.2 + 64 <= csize(f@, r.1 as int),
        // The block's number within the block rows of this MCU row.
        ({
            let vr = if s.ns == 1 {
                1
            } else {
                f@.comps[r.1 as int].v as int
            };
            &&& r.2 == cw(f@, r.1 as int) * (vr * my) + r.3
            &&& 64 * r.3 + 64 <= 64 * (cw(f@, r.1 as int) * vr)
        }),
{
    let ghost fv = f@;
    let ghost sv = s@;
    let ghost m = my * mcu_w(fv, sv) + mx;
    reveal(csize);
    let ns = s.ns as usize;
    let i = sget(cx.bi.as_slice(), b) as usize;
    proof {
        if ns > 1 {
            assert(slot_ok(fv, sv, b as int, cx.bi[b as int] as int, cx.bdx[b as int] as int, cx.bdy[b as int] as int));
        }
    }
    assert(i < ns);
    let c = sget(s.ci.as_slice(), i) as usize;
    assert(sv.ci[i as int] == c);
    assert(c < fv.nc);
    assert(fv.comps[c as int] == f.comps[c as int]);
    assert(g.wf(fv));
    let ghost ci = c as int;
    assert(0 <= ci < fv.nc);
    assert(g.cw[ci] == cw(fv, ci));
    assert(g.ch[ci] == ch(fv, ci));
    assert(fits(fv, ci));
    let cwc = sget(g.cw.as_slice(), c) as usize;
    let ghost cw_ = cw(fv, c as int);
    let ghost ch_ = ch(fv, c as int);
    let idx: usize;
    let lidx: usize;
    if ns == 1 {
        proof {
            let w = wb(fv, c as int);
            assert(g.wb[c as int] == w && g.hb[c as int] == hb(fv, c as int));
            assert(m == my * w + mx);
            lemma_fundamental_div_mod_converse(m, w, my as int, mx as int);
            lemma_grid(my as int, mx as int, ch_, cw_);
            assert(blk_index(fv, sv, m, b as int) == (0int, my * cw_ + mx));
        }
        idx = my as usize * cwc + mx as usize;
        lidx = mx as usize;
        proof {
            assert(g.wb[c as int] == wb(fv, c as int) && g.wb[c as int] <= g.cw[c as int]);
            assert(idx == cw_ * (1 * my) + lidx) by (nonlinear_arith)
                requires
                    idx == my * cw_ + mx,
                    lidx == mx,
            ;
            assert(cw_ * 1 == cw_) by (nonlinear_arith);
        }
    } else {
        let cp = sref(f.comps.as_slice(), c);
        let h = cp.h as usize;
        let v = cp.v as usize;
        let bx = sget(cx.bdx.as_slice(), b) as usize;
        let by = sget(cx.bdy.as_slice(), b) as usize;
        proof {
            let off = blk_slot(fv, sv, b as int, 0).1;
            assert(by < v) by {
                lemma_fundamental_div_mod(off, h as int);
                assert(off / (h as int) < v) by (nonlinear_arith)
                    requires
                        0 <= off < h * v,
                        h > 0,
                        off == h * (off / (h as int)) + off % (h as int),
                        0 <= off % (h as int),
                ;
            }
            lemma_mod_bound(off, h as int);
            let w = mcux(fv);
            lemma_fundamental_div_mod_converse(m, w, my as int, mx as int);
            lemma_sub(my as int, by as int, mcuy(fv), v as int);
            lemma_sub(mx as int, bx as int, mcux(fv), h as int);
            lemma_grid(my * v + by, mx * h + bx, ch_, cw_);
            assert(blk_index(fv, sv, m, b as int) == (i as int, (my * v + by) * cw_ + (mx * h + bx)));
        }
        idx = (my as usize * v + by) * cwc + mx as usize * h + bx;
        proof {
            lemma_sub(mx as int, bx as int, mcux(fv), h as int);
            lemma_grid(by as int, mx * h + bx, v as int, cw_);
            assert(by * cw_ <= 4 * 0x4_0080) by (nonlinear_arith)
                requires
                    0 <= by < 4,
                    0 <= cw_ <= 0x4_0080,
            ;
        }
        lidx = by * cwc + mx as usize * h + bx;
        proof {
            assert(idx == cw_ * (v * my) + lidx) by (nonlinear_arith)
                requires
                    idx == (my * v + by) * cw_ + mx * h + bx,
                    lidx == by * cw_ + mx * h + bx,
            ;
        }
    }
    (i, c, idx, lidx)
}

/// A block of a streamed scan decoded into the window `a` of component
/// `c`, at `lo`, is the block decoded into the whole array.
pub proof fn lemma_stream_block(
    d: Seq<u8>,
    f: Frame,
    t: Tables,
    s: Scan,
    ss: SS,
    i: int,
    c: int,
    a: Seq<i16>,
    pl: Seq<u8>,
    q: Seq<u16>,
    cwv: int,
    chh: int,
    wbv: int,
    hbv: int,
    vr: int,
    row: int,
    lo: int,
)
    requires
        kind(f, s) is Base,
        0 <= c < ss.a.len(),
        win_ok(a, ss.a[c], pl, q, cwv, chh, wbv, hbv, vr, row),
        vr * (row + 1) <= chh,
        0 <= lo,
        lo + 64 <= a.len(),
    ensures
        ({
            let go = wbase(cwv, vr, row) + lo;
            let sw = block_ss(d, f, t, s, SS { a: ss.a.update(c, a), ..ss }, i, c, lo);
            let sg = block_ss(d, f, t, s, ss, i, c, go);
            &&& sw.ok == sg.ok
            &&& sw.ok == ss.ok
            &&& sg == SS { a: ss.a.update(c, sg.a[c]), ..sw }
            &&& win_ok(sw.a[c], sg.a[c], pl, q, cwv, chh, wbv, hbv, vr, row)
            &&& 0 <= go
            &&& go + 64 <= ss.a[c].len()
        }),
{
    let e = ecs(d, ss.p);
    lemma_win_block(
        t.dc[s.td[i] as int],
        t.ac[s.ta[i] as int],
        e,
        ss.n,
        ss.pred[i],
        a,
        ss.a[c],
        pl,
        q,
        cwv,
        chh,
        wbv,
        hbv,
        vr,
        row,
        lo,
    );
    let go = wbase(cwv, vr, row) + lo;
    let sg = block_ss(d, f, t, s, ss, i, c, go);
    assert(sg.a =~= ss.a.update(c, sg.a[c]));
}

/// A block of a streamed scan into the window `a` of component `c`, at
/// `lo`. Returns the component's whole array as it is now.
#[inline(always)]
fn win_block_x(
    data: &[u8],
    t: &Tabs,
    s: &ScanX,
    cx: &ScanCtx,
    st: &mut ScanSt,
    a: &mut Vec<i16>,
    lo: usize,
    i: usize,
    Ghost(f): Ghost<Frame>,
    Ghost(gv): Ghost<Seq<Seq<i16>>>,
    Ghost(c): Ghost<int>,
    Ghost(pl): Ghost<Seq<u8>>,
    Ghost(q): Ghost<Seq<u16>>,
    Ghost(vr): Ghost<int>,
    Ghost(row): Ghost<int>,
) -> (r: (bool, Ghost<Seq<i16>>))
    requires
        old(st).br.wf(data@),
        cx.wf(f, t@, s@),
        scan_pre(f, s@),
        s.ns <= 3,
        i < s.ns,
        0 <= c < gv.len(),
        kind(f, s@) is Base,
        win_ok(old(a)@, gv[c], pl, q, cw(f, c), ch(f, c), wb(f, c), hb(f, c), vr, row),
        vr * (row + 1) <= ch(f, c),
        lo + 64 <= old(a).len(),
    ensures
        final(st).br.wf(data@),
        final(st).br.p0 == old(st).br.p0,
        final(st).insuf == old(st).insuf,
        final(st).togo == old(st).togo,
        final(st).rst == old(st).rst,
        win_ok(final(a)@, r.1@, pl, q, cw(f, c), ch(f, c), wb(f, c), hb(f, c), vr, row),
        r.1@.len() == gv[c].len(),
        ({
            let go = wbase(cw(f, c), vr, row) + lo;
            let sp = block_ss(data@, f, t@, s@, ssv(*old(st), gv), i as int, c, go);
            &&& sp.ok == r.0
            &&& r.0 ==> ssv(*final(st), gv.update(c, r.1@)) == sp
        }),
{
    hide(block_ss);
    hide(win_ok);
    let ghost ss = ssv(*st, gv);
    let ghost a0 = a@;
    let ghost go = wbase(cw(f, c), vr, row) + lo;
    let ghost sw = block_ss(data@, f, t@, s@, SS { a: ss.a.update(c, a0), ..ss }, i as int, c, lo as int);
    let ghost sg = block_ss(data@, f, t@, s@, ss, i as int, c, go);
    proof {
        lemma_stream_block(
            data@, f, t@, s@, ss, i as int, c, a0, pl, q, cw(f, c), ch(f, c), wb(f, c), hb(f, c), vr, row, lo as int,
        );
        assert(ssv(*st, gv.update(c, a0)) == SS { a: ss.a.update(c, a0), ..ss });
    }
    let ok = block_x(data, t, s, cx, st, a, lo, i, Ghost(f), Ghost(gv.update(c, a0)), Ghost(c));
    proof {
        assert(ok);
        assert(gv.update(c, a0).update(c, a@)[c] == a@);
        assert(sw.a[c] == a@);
        assert(sg.a[c].len() == gv[c].len()) by {
            reveal(win_ok);
        }
    }
    (ok, Ghost(sg.a[c]))
}

/// `one_block_x` for a streamed scan: the block is decoded into its
/// component's window.
fn one_block_s(
    data: &[u8],
    f: &FrameX,
    g: &Geom,
    t: &Tabs,
    s: &ScanX,
    cx: &ScanCtx,
    st: &mut ScanSt,
    co: &mut Coefs,
    my: u32,
    mx: u32,
    b: usize,
) -> (ok: bool)
    requires
        frame_basic(f@),
        g.wf(f@),
        scan_pre(f@, s@),
        s.ns <= 3,
        cx.wf(f@, t@, s@),
        old(co).wf(f@),
        old(st).br.wf(data@),
        my < mcu_h(f@, s@),
        mx < mcu_w(f@, s@),
        b < cx.nb,
        old(co).spre(f@, s@, my as int),
        old(co).stream,
    ensures
        final(co).wf(f@),
        final(co).stream == old(co).stream,
        final(co).sqv() == old(co).sqv(),
        final(co).row == old(co).row,
        final(st).br.wf(data@),
        final(st).br.p0 == old(st).br.p0,
        final(st).insuf == old(st).insuf,
        final(st).togo == old(st).togo,
        final(st).rst == old(st).rst,
        ({
            let m = my * mcu_w(f@, s@) + mx;
            let (i, idx) = blk_index(f@, s@, m, b as int);
            let sp = block_ss(data@, f@, t@, s@, ssv(*old(st), old(co).view(f@.nc)), i, s@.ci[i], idx * 64);
            &&& sp.ok == ok
            &&& ok ==> ssv(*final(st), final(co).view(f@.nc)) == sp
        }),
{
    hide(block_ss);
    hide(win_ok);
    reveal(Coefs::sqv);
    reveal(Coefs::swf);
    let ghost fv = f@;
    let ghost sv = s@;
    let ghost nc = fv.nc;
    reveal(csize);
    assert forall|c: int| 0 <= c < fv.nc implies fits(fv, c) by {
        reveal(win_ok);
        assert(c == 0 || c == 1 || c == 2);
    }
    let (i, c, idx, lidx) = blk_idx_x(f, g, s, cx, my, mx, b, Ghost(t@));
    assert(64 * lidx + 64 <= (if c == 0 {
        co.a0.len()
    } else if c == 1 {
        co.a1.len()
    } else {
        co.a2.len()
    })) by {
        reveal(win_ok);
    }
    let lo = lidx * 64;
    let ghost gv = co.view(nc);
    let ghost ss = ssv(*st, gv);
    let ghost ci = c as int;
    let ghost vr = srows(fv, ci);
    let ghost row = co.row as int;
    let ghost go = wbase(cw(fv, ci), vr, row) + lo;
    assert(go == idx * 64) by (nonlinear_arith)
        requires
            go == 64 * (cw(fv, ci) * (vr * row)) + lo,
            lo == lidx * 64,
            idx == cw(fv, ci) * (vr * my) + lidx,
            row == my,
    ;
    assert(vr * (row + 1) <= ch(fv, ci)) by {
        assert(g.cw[ci] == cw(fv, ci));
        assert(g.hb[ci] == hb(fv, ci) && g.ch[ci] == ch(fv, ci) && g.hb[ci] <= g.ch[ci]);
        if fv.nc != 1 {
            assert(vr * (row + 1) <= mcuy(fv) * vr) by (nonlinear_arith)
                requires
                    row + 1 <= mcuy(fv),
                    vr >= 1,
            ;
        }
    }
    if c == 0 {
        let r = win_block_x(
            data, t, s, cx, st, &mut co.a0, lo, i, Ghost(fv), Ghost(gv), Ghost(0), Ghost(co.p0@), Ghost(co.sq[0]@),
            Ghost(vr), Ghost(row),
        );
        proof {
            co.g0 = r.1;
            assert(co.view(nc) =~= gv.update(0, r.1@));
        }
        r.0
    } else if c == 1 {
        let r = win_block_x(
            data, t, s, cx, st, &mut co.a1, lo, i, Ghost(fv), Ghost(gv), Ghost(1), Ghost(co.p1@), Ghost(co.sq[1]@),
            Ghost(vr), Ghost(row),
        );
        proof {
            co.g1 = r.1;
            assert(co.view(nc) =~= gv.update(1, r.1@));
        }
        r.0
    } else {
        let r = win_block_x(
            data, t, s, cx, st, &mut co.a2, lo, i, Ghost(fv), Ghost(gv), Ghost(2), Ghost(co.p2@), Ghost(co.sq[2]@),
            Ghost(vr), Ghost(row),
        );
        proof {
            co.g2 = r.1;
            assert(co.view(nc) =~= gv.update(2, r.1@));
        }
        r.0
    }
}

/// Block `b` of the MCU in row `my`, column `mx`. Returns false if the
/// file is to be rejected.
fn one_block_x(
    data: &[u8],
    f: &FrameX,
    g: &Geom,
    t: &Tabs,
    s: &ScanX,
    cx: &ScanCtx,
    st: &mut ScanSt,
    co: &mut Coefs,
    my: u32,
    mx: u32,
    b: usize,
) -> (ok: bool)
    requires
        frame_basic(f@),
        g.wf(f@),
        scan_pre(f@, s@),
        s.ns <= 3,
        cx.wf(f@, t@, s@),
        old(co).wf(f@),
        old(st).br.wf(data@),
        my < mcu_h(f@, s@),
        mx < mcu_w(f@, s@),
        b < cx.nb,
        old(co).spre(f@, s@, my as int),
    ensures
        final(co).wf(f@),
        final(co).stream == old(co).stream,
        final(co).sqv() == old(co).sqv(),
        final(co).row == old(co).row,
        final(st).br.wf(data@),
        final(st).br.p0 == old(st).br.p0,
        final(st).insuf == old(st).insuf,
        final(st).togo == old(st).togo,
        final(st).rst == old(st).rst,
        ({
            let m = my * mcu_w(f@, s@) + mx;
            let (i, idx) = blk_index(f@, s@, m, b as int);
            let sp = block_ss(data@, f@, t@, s@, ssv(*old(st), old(co).view(f@.nc)), i, s@.ci[i], idx * 64);
            &&& sp.ok == ok
            &&& ok ==> ssv(*final(st), final(co).view(f@.nc)) == sp
        }),
{
    hide(block_ss);
    reveal(Coefs::sqv);
    if co.stream {
        return one_block_s(data, f, g, t, s, cx, st, co, my, mx, b);
    }
    let ghost fv = f@;
    let ghost nc = fv.nc;
    assert forall|c: int| 0 <= c < fv.nc implies fits(fv, c) by {
        assert(c == 0 || c == 1 || c == 2);
    }
    let (i, c, idx, _lidx) = blk_idx_x(f, g, s, cx, my, mx, b, Ghost(t@));
    let o = idx * 64;
    let ghost av = co.view(nc);
    let ok = if c == 0 {
        block_x(data, t, s, cx, st, &mut co.a0, o, i, Ghost(fv), Ghost(av), Ghost(0))
    } else if c == 1 {
        block_x(data, t, s, cx, st, &mut co.a1, o, i, Ghost(fv), Ghost(av), Ghost(1))
    } else {
        block_x(data, t, s, cx, st, &mut co.a2, o, i, Ghost(fv), Ghost(av), Ghost(2))
    };
    proof {
        if c == 0 {
            assert(av.update(0, co.a0@) =~= co.view(nc));
        } else if c == 1 {
            assert(av.update(1, co.a1@) =~= co.view(nc));
        } else {
            assert(av.update(2, co.a2@) =~= co.view(nc));
        }
    }
    ok
}

/// The blocks of the MCU in row `my`, column `mx`. Returns false if the
/// file is to be rejected.
fn mcu_x(
    data: &[u8],
    f: &FrameX,
    g: &Geom,
    t: &Tabs,
    s: &ScanX,
    cx: &ScanCtx,
    st: &mut ScanSt,
    co: &mut Coefs,
    my: u32,
    mx: u32,
) -> (ok: bool)
    requires
        frame_basic(f@),
        g.wf(f@),
        scan_pre(f@, s@),
        s.ns <= 3,
        cx.wf(f@, t@, s@),
        old(co).wf(f@),
        old(st).br.wf(data@),
        my < mcu_h(f@, s@),
        mx < mcu_w(f@, s@),
        old(co).spre(f@, s@, my as int),
    ensures
        final(co).wf(f@),
        final(co).stream == old(co).stream,
        final(co).sqv() == old(co).sqv(),
        final(co).row == old(co).row,
        final(st).br.wf(data@),
        final(st).br.p0 == old(st).br.p0,
        final(st).insuf == old(st).insuf,
        final(st).togo == old(st).togo,
        final(st).rst == old(st).rst,
        ({
            let m = my * mcu_w(f@, s@) + mx;
            let sp = mcu_body(data@, f@, t@, s@, ssv(*old(st), old(co).view(f@.nc)), m);
            &&& sp.ok == ok
            &&& ok ==> ssv(*final(st), final(co).view(f@.nc)) == sp
        }),
{
    let ghost d = data@;
    let ghost fv = f@;
    let ghost tv = t@;
    let ghost sv = s@;
    let ghost nc = fv.nc;
    let ghost m = my * mcu_w(fv, sv) + mx;
    let ghost st0 = ssv(*st, co.view(nc));
    let ghost dck = !(kind(fv, sv) is AcFirst || kind(fv, sv) is AcRefine);
    let mut b: usize = 0;
    while b < cx.nb
        invariant
            b <= cx.nb,
            s.ns <= 3,
            d == data@,
            fv == f@,
            tv == t@,
            sv == s@,
            nc == fv.nc,
            m == my * mcu_w(fv, sv) + mx,
            my < mcu_h(fv, sv),
            mx < mcu_w(fv, sv),
            frame_basic(fv),
            g.wf(fv),
            scan_pre(fv, sv),
            cx.wf(fv, tv, sv),
            co.wf(fv),
            co.stream == old(co).stream,
            co.sqv() == old(co).sqv(),
            co.row == old(co).row,
            co.spre(fv, sv, my as int),
            st.br.wf(d),
            st.br.p0 == old(st).br.p0,
            st.insuf == old(st).insuf,
            st.togo == old(st).togo,
            st.rst == old(st).rst,
            st0 == ssv(*old(st), old(co).view(nc)),
            dck == !(kind(fv, sv) is AcFirst || kind(fv, sv) is AcRefine),
            dck ==> mcu_dc(d, fv, tv, sv, ssv(*st, co.view(nc)), m, b as int) == mcu_dc(d, fv, tv, sv, st0, m, 0),
            !dck ==> if b == 0 {
                ssv(*st, co.view(nc)) == st0
            } else {
                ssv(*st, co.view(nc)) == mcu_ac(d, fv, tv, sv, st0, m)
            },
        decreases cx.nb - b,
    {
        let ghost cur = ssv(*st, co.view(nc));
        let ghost (i, idx) = blk_index(fv, sv, m, b as int);
        let ghost sp = block_ss(d, fv, tv, sv, cur, i, sv.ci[i], idx * 64);
        proof {
            if dck {
                assert(mcu_dc_block(d, fv, tv, sv, cur, m, b as int) == sp);
                assert(mcu_dc(d, fv, tv, sv, cur, m, b as int) == mcu_dc(d, fv, tv, sv, sp, m, b + 1));
            } else {
                assert(sv.ns == 1 && b == 0 && i == 0);
                assert(mcu_ac(d, fv, tv, sv, cur, m) == sp);
            }
        }
        let ok = one_block_x(data, f, g, t, s, cx, st, co, my, mx, b);
        if !ok {
            proof {
                if dck {
                    lemma_mcu_dc_notok(d, fv, tv, sv, sp, m, b + 1);
                }
            }
            return false;
        }
        b += 1;
    }
    true
}

/// A restart: on from the next restart marker, with the predictions and
/// the end-of-band run cleared.
fn restart_x(
    data: &[u8],
    t: &Tabs,
    st: &mut ScanSt,
    Ghost(pi): Ghost<int>,
    Ghost(a): Ghost<Seq<Seq<i16>>>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        old(st).br.wf(data@),
        seg_ok(data@, pi, old(st).br.p0@),
        old(st).rst < 8,
    ensures
        final(st).br.wf(data@),
        seg_ok(data@, pi, final(st).br.p0@),
        final(st).rst < 8,
        final(st).togo == t.ri,
        final(st).br.p0@ >= old(st).br.pos,
        ssv(*final(st), a) == restart(data@, t@, ssv(*old(st), a)),
        final(mt).n + 4 * old(st).br.p0@ <= old(mt).n + 4 * final(st).br.p0@ + 6,
{
    let ghost d = data@;
    let ghost p0 = st.br.p0@;
    let ghost st0 = ssv(*st, a);
    proof {
        lemma_marker_after(d, p0);
        lemma_restart_seg(d, pi, p0, st.rst as int);
        lemma_resync_p(d, marker_after(d, p0).0, marker_after(d, p0).1, st.rst as int);
    }
    // The reader's own steps, and the search for the marker.
    proof {
        mt.n = mt.n + st.br.wk@ as nat;
    }
    let ghost pos0 = st.br.pos as int;
    let (m, q) = marker_after_x(data, st.br.pos, Tracked(mt));
    proof {
        lemma_marker_after(d, pos0);
    }
    let (p2, taken) = if m == 0xD0 + st.rst {
        (q, true)
    } else {
        resync_x(data, m, q, st.rst, Tracked(mt))
    };
    assert((p2 as int, taken) == restart_p(d, p0, st.rst as int));
    st.br = BitReader::new(p2, Ghost(data@));
    st.pred = [0; 3];
    st.eob = 0;
    st.togo = t.ri as i64;
    st.rst = (st.rst + 1) % 8;
    if taken {
        st.insuf = false;
    }
    proof {
        let fin = ssv(*st, a);
        let sp = restart(d, t@, st0);
        assert(fin.pred =~= sp.pred);
        assert(fin == sp);
    }
}

/// MCU (`my`, `mx`) of a scan, after the restart that is due before it if
/// one is. Returns false if the file is to be rejected.
fn mcu_step_x(
    data: &[u8],
    f: &FrameX,
    g: &Geom,
    t: &Tabs,
    s: &ScanX,
    cx: &ScanCtx,
    st: &mut ScanSt,
    co: &mut Coefs,
    my: u32,
    mx: u32,
    Ghost(p): Ghost<int>,
    Tracked(mt): Tracked<&mut Meter>,
) -> (ok: bool)
    requires
        frame_basic(f@),
        g.wf(f@),
        scan_pre(f@, s@),
        s.ns <= 3,
        cx.wf(f@, t@, s@),
        old(co).wf(f@),
        old(co).spre(f@, s@, my as int),
        old(st).br.wf(data@),
        seg_ok(data@, p, old(st).br.p0@),
        old(st).rst < 8,
        -0x1_0000_0000_0000 <= old(st).togo <= 65535,
        my < mcu_h(f@, s@),
        mx < mcu_w(f@, s@),
    ensures
        final(co).wf(f@),
        final(co).stream == old(co).stream,
        final(co).sqv() == old(co).sqv(),
        final(co).row == old(co).row,
        final(st).br.wf(data@),
        seg_ok(data@, p, final(st).br.p0@),
        final(st).br.p0@ >= old(st).br.p0@,
        final(st).rst < 8,
        old(st).togo - 1 <= final(st).togo <= 65535,
        final(mt).n + 4 * old(st).br.p0@ <= old(mt).n + 4 * final(st).br.p0@ + 6,
        ({
            let m = my * mcu_w(f@, s@) + mx;
            let sp = mcu_step(data@, f@, t@, s@, ssv(*old(st), old(co).view(f@.nc)), m);
            &&& sp.ok == ok
            &&& ok ==> ssv(*final(st), final(co).view(f@.nc)) == sp
        }),
{
    let ghost d = data@;
    let ghost fv = f@;
    let ghost tv = t@;
    let ghost sv = s@;
    let ghost nc = fv.nc;
    let ghost m = my * mcu_w(fv, sv) + mx;
    let ghost cur0 = ssv(*st, co.view(nc));
    if t.ri != 0 && st.togo == 0 {
        restart_x(data, t, st, Ghost(p), Ghost(co.view(nc)), Tracked(mt));
    }
    let ghost st1 = ssv(*st, co.view(nc));
    assert(st1 == if tv.ri != 0 && cur0.togo == 0 {
        restart(d, tv, cur0)
    } else {
        cur0
    });
    if !(st.insuf && cx.kind != 2) {
        let ok = mcu_x(data, f, g, t, s, cx, st, co, my, mx);
        if !ok {
            proof {
                assert(!mcu_step(d, fv, tv, sv, cur0, m).ok);
            }
            return false;
        }
        if st.br.is_over() {
            st.insuf = true;
        }
    }
    st.togo -= 1;
    proof {
        assert(ssv(*st, co.view(nc)) == mcu_step(d, fv, tv, sv, cur0, m));
    }
    true
}

/// The end of an MCU row of a streamed scan: each component's samples go
/// to its plane and its window moves on.
/// The most work a scan does beyond 4 steps per byte: 7 per MCU and, per
/// MCU row, one and a streamed scan's `flush_row`.
pub open spec fn scan_work(f: Frame, s: Scan, stream: bool) -> int {
    7 * scan_mcus(f, s) + mcu_h(f, s) * ((if stream { rowc(f) } else { 0 }) + 1)
}

/// `scan_work` covers the work up to MCU (`my`, `mx`) of the scan.
pub proof fn lemma_scan_work(f: Frame, s: Scan, stream: bool, my: int, mx: int, fr: int)
    requires
        fr == (if stream { rowc(f) } else { 0 }),
        fr >= 0,
        0 <= mx <= mcu_w(f, s),
        0 <= my <= mcu_h(f, s),
        my * mcu_w(f, s) + mx <= scan_mcus(f, s),
        scan_mcus(f, s) == mcu_w(f, s) * mcu_h(f, s),
    ensures
        7 * (my * mcu_w(f, s) + mx) + my * (fr + 1) <= scan_work(f, s, stream),
{
    assert(my * (fr + 1) <= mcu_h(f, s) * (fr + 1)) by (nonlinear_arith)
        requires
            0 <= my <= mcu_h(f, s),
            fr >= 0,
    ;
}

/// The work bounds are not negative.
pub proof fn lemma_sw_nn(f: Frame, g: Geom, s: Scan, stream: bool)
    requires
        g.wf(f),
        frame_basic(f),
        scan_pre(f, s),
    ensures
        rowc(f) >= 0,
        scan_work(f, s, stream) >= 0,
        scan_mcus(f, s) == mcu_w(f, s) * mcu_h(f, s),
        mcu_w(f, s) >= 0,
        mcu_h(f, s) >= 0,
{
    let c = s.ci[0] as int;
    assert(0 <= c < f.nc);
    lemma_geom_c(f, g, c);
    lemma_geom_c(f, g, 0);
    let (c0, r0) = (cw(f, 0), srows(f, 0));
    assert(c0 * r0 >= 0) by (nonlinear_arith)
        requires
            c0 >= 0,
            r0 >= 0,
    ;
    if f.nc == 3 {
        assert(g.cw[1] == cw(f, 1) && g.cw[2] == cw(f, 2));
        let (c1, r1, c2, r2) = (cw(f, 1), srows(f, 1), cw(f, 2), srows(f, 2));
        assert(c1 * r1 >= 0 && c2 * r2 >= 0) by (nonlinear_arith)
            requires
                c1 >= 0,
                r1 >= 0,
                c2 >= 0,
                r2 >= 0,
        ;
    }
    let (w, h) = (mcu_w(f, s), mcu_h(f, s));
    let fr: int = if stream { rowc(f) } else { 0 };
    assert(w * h >= 0 && h * (fr + 1) >= 0) by (nonlinear_arith)
        requires
            w >= 0,
            h >= 0,
            fr >= 0,
    ;
}

/// A component's coefficient array has at least one block each way.
pub proof fn lemma_cw_pos(f: Frame, g: Geom, c: int)
    requires
        g.wf(f),
        frame_basic(f),
        0 <= c < f.nc,
    ensures
        cw(f, c) >= 1,
        ch(f, c) >= 1,
        cw(f, c) >= mcux(f),
        ch(f, c) >= mcuy(f),
        mcux(f) >= 1,
        mcuy(f) >= 1,
{
    assert(g.cw[c] == cw(f, c));
    lemma_cdiv(f.w as int, 8 * maxh(f));
    lemma_cdiv(f.h as int, 8 * maxv(f));
    let (a, b) = (mcux(f), mcuy(f));
    let (h, v) = (f.comps[c].h as int, f.comps[c].v as int);
    assert(a >= 1) by (nonlinear_arith)
        requires
            1 <= f.w as int <= a * (8 * maxh(f)),
            a >= 0,
    ;
    assert(b >= 1) by (nonlinear_arith)
        requires
            1 <= f.h as int <= b * (8 * maxv(f)),
            b >= 0,
    ;
    assert(a * h >= a && b * v >= b) by (nonlinear_arith)
        requires
            a >= 1,
            b >= 1,
            h >= 1,
            v >= 1,
    ;
}

/// A frame has a block.
pub proof fn lemma_fblk(f: Frame, g: Geom)
    requires
        g.wf(f),
        frame_basic(f),
    ensures
        fblk(f) >= 1,
{
    lemma_cw_pos(f, g, 0);
    let (c0, h0) = (cw(f, 0), ch(f, 0));
    assert(c0 * h0 >= 1) by (nonlinear_arith)
        requires
            c0 >= 1,
            h0 >= 1,
    ;
    if f.nc == 3 {
        lemma_cw_pos(f, g, 1);
        lemma_cw_pos(f, g, 2);
        let (c1, h1, c2, h2) = (cw(f, 1), ch(f, 1), cw(f, 2), ch(f, 2));
        assert(c1 * h1 >= 1 && c2 * h2 >= 1) by (nonlinear_arith)
            requires
                c1 >= 1,
                h1 >= 1,
                c2 >= 1,
                h2 >= 1,
        ;
    }
}

/// A scan's work is at most 74 steps per block of the frame (`stream`
/// only for the one scan of a sequential frame that has every component).
pub proof fn lemma_sw_le(f: Frame, g: Geom, s: Scan, stream: bool)
    requires
        g.wf(f),
        frame_basic(f),
        scan_pre(f, s),
        stream ==> s.ns == f.nc,
    ensures
        scan_work(f, s, stream) <= 74 * fblk(f),
        fblk(f) >= 1,
{
    lemma_sw_nn(f, g, s, stream);
    lemma_cw_pos(f, g, 0);
    let c = s.ci[0] as int;
    lemma_cw_pos(f, g, c);
    assert(g.cw[c] == cw(f, c));
    let (c0, h0) = (cw(f, 0), ch(f, 0));
    let mut tot: int = c0 * h0;
    if f.nc == 3 {
        lemma_cw_pos(f, g, 1);
        lemma_cw_pos(f, g, 2);
        let (c1, h1, c2, h2) = (cw(f, 1), ch(f, 1), cw(f, 2), ch(f, 2));
        assert(c1 * h1 >= 1 && c2 * h2 >= 1) by (nonlinear_arith)
            requires
                c1 >= 1,
                h1 >= 1,
                c2 >= 1,
                h2 >= 1,
        ;
    }
    assert(c0 * h0 >= 1) by (nonlinear_arith)
        requires
            c0 >= 1,
            h0 >= 1,
    ;
    let (cc, hc) = (cw(f, c), ch(f, c));
    assert(cc * hc <= fblk(f));
    let (w, h) = (mcu_w(f, s), mcu_h(f, s));
    // MCUs and MCU rows.
    if s.ns == 1 {
        assert(w <= cc && h <= hc);
    } else {
        assert(w <= c0 && h <= h0);
    }
    assert(w * h <= fblk(f) && h <= fblk(f)) by (nonlinear_arith)
        requires
            s.ns == 1 ==> w <= cc && h <= hc,
            s.ns != 1 ==> w <= c0 && h <= h0,
            cc * hc <= fblk(f),
            c0 * h0 <= fblk(f),
            0 <= w,
            0 <= h,
            1 <= cc,
            1 <= c0,
    ;
    if stream {
        if f.nc == 1 {
            assert(c == 0);
            assert(g.hb[0] == hb(f, 0));
            assert(rowc(f) * h <= 66 * fblk(f)) by (nonlinear_arith)
                requires
                    rowc(f) == 66 * c0,
                    h <= h0,
                    fblk(f) == c0 * h0,
                    c0 >= 1,
                    h >= 0,
            ;
        } else {
            let (c1, c2) = (cw(f, 1), cw(f, 2));
            let (v0, v1, v2) = (srows(f, 0), srows(f, 1), srows(f, 2));
            assert(h == mcuy(f));
            let (h0, h1, h2) = (ch(f, 0), ch(f, 1), ch(f, 2));
            assert(h0 == h * v0 && h1 == h * v1 && h2 == h * v2);
            assert((c0 * v0) * h == c0 * h0) by (nonlinear_arith)
                requires
                    h0 == h * v0,
            ;
            assert((c1 * v1) * h == c1 * h1) by (nonlinear_arith)
                requires
                    h1 == h * v1,
            ;
            assert((c2 * v2) * h == c2 * h2) by (nonlinear_arith)
                requires
                    h2 == h * v2,
            ;
            let (a0, a1, a2) = (c0 * v0, c1 * v1, c2 * v2);
            assert((66 * a0 + 66 * a1 + 66 * a2) * h == 66 * (a0 * h) + 66 * (a1 * h) + 66 * (a2 * h)) by (nonlinear_arith);
            assert(fblk(f) == c0 * h0 + c1 * h1 + c2 * h2);
            assert(rowc(f) == 66 * a0 + 66 * a1 + 66 * a2);
            assert(rowc(f) * h == 66 * fblk(f));
        }
    }
    let fr: int = if stream { rowc(f) } else { 0 };
    assert(h * (fr + 1) == h * fr + h) by (nonlinear_arith);
    assert(h * fr == fr * h) by (nonlinear_arith);
}

/// The work of `flush_row`.
pub open spec fn rowc(f: Frame) -> int {
    if f.nc == 1 {
        66 * cw(f, 0)
    } else {
        66 * (cw(f, 0) * srows(f, 0)) + 66 * (cw(f, 1) * srows(f, 1)) + 66 * (cw(f, 2) * srows(f, 2))
    }
}

fn flush_row(co: &mut Coefs, f: &FrameX, g: &Geom, Tracked(mt): Tracked<&mut Meter>)
    requires
        frame_basic(f@),
        g.wf(f@),
        old(co).stream,
        old(co).wf(f@),
        old(co).row < stotal(f@),
    ensures
        final(co).wf(f@),
        final(co).stream,
        final(co).row == old(co).row + 1,
        final(co).view(f@.nc) == old(co).view(f@.nc),
        final(co).sqv() == old(co).sqv(),
        final(mt).n <= old(mt).n + rowc(f@),
{
    reveal(Coefs::sqv);
    reveal(Coefs::swf);
    let ghost fv = f@;
    let row = co.row as usize;
    let nc = f.nc;
    assert(g.cw[0] == cw(fv, 0) && g.ch[0] == ch(fv, 0) && g.wb[0] == wb(fv, 0) && g.hb[0] == hb(fv, 0));
    assert(fv.comps[0] == f.comps[0]);
    assert(stotal(fv) <= 0x4_0080);
    let vr0: usize = if nc == 1 {
        1
    } else {
        f.comps[0].v as usize
    };
    assert(vr0 * (row + 1) <= ch(fv, 0)) by (nonlinear_arith)
        requires
            row + 1 <= stotal(fv),
            fv.nc == 1 ==> stotal(fv) <= ch(fv, 0) && vr0 == 1,
            fv.nc != 1 ==> ch(fv, 0) == stotal(fv) * vr0,
            vr0 >= 1,
    ;
    flush_x(
        &mut co.a0,
        &mut co.p0,
        &co.sq[0],
        &co.rl,
        &co.kt,
        g.cw[0] as usize,
        g.wb[0] as usize,
        g.hb[0] as usize,
        vr0,
        row,
        Ghost(co.g0@),
        Ghost(g.ch[0] as int),
        Tracked(mt),
    );
    if nc == 3 {
        proof {
            lemma_geom_c(fv, *g, 1);
            lemma_geom_c(fv, *g, 2);
        }
        assert(fv.comps[1] == f.comps[1] && fv.comps[2] == f.comps[2]);
        let vr1 = f.comps[1].v as usize;
        let vr2 = f.comps[2].v as usize;
        assert(vr1 * (row + 1) <= ch(fv, 1) && vr2 * (row + 1) <= ch(fv, 2)) by (nonlinear_arith)
            requires
                row + 1 <= mcuy(fv),
                ch(fv, 1) == mcuy(fv) * vr1,
                ch(fv, 2) == mcuy(fv) * vr2,
                vr1 >= 1,
                vr2 >= 1,
        ;
        flush_x(
            &mut co.a1,
            &mut co.p1,
            &co.sq[1],
            &co.rl,
        &co.kt,
            g.cw[1] as usize,
            g.wb[1] as usize,
            g.hb[1] as usize,
            vr1,
            row,
            Ghost(co.g1@),
            Ghost(g.ch[1] as int),
            Tracked(mt),
        );
        flush_x(
            &mut co.a2,
            &mut co.p2,
            &co.sq[2],
            &co.rl,
        &co.kt,
            g.cw[2] as usize,
            g.wb[2] as usize,
            g.hb[2] as usize,
            vr2,
            row,
            Ghost(co.g2@),
            Ghost(g.ch[2] as int),
            Tracked(mt),
        );
    }
    co.row = co.row + 1;
}

/// Decodes the scan whose entropy-coded data starts at `p`. Returns a
/// position from which the next marker is the one after the scan, or
/// `None` if the file is to be rejected.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn scan_x(
    data: &[u8],
    f: &FrameX,
    g: &Geom,
    t: &Tabs,
    s: &ScanX,
    co: &mut Coefs,
    p: usize,
    Tracked(mt): Tracked<&mut Meter>,
) -> (r: Option<usize>)
    requires
        len_ok(data@),
        p <= data@.len() + 0x1_0008,
        frame_basic(f@),
        g.wf(f@),
        scan_pre(f@, s@),
        s.ns <= 3,
        old(co).wf(f@),
        old(co).spre(f@, s@, 0),
    ensures
        final(co).wf(f@),
        final(co).stream == old(co).stream,
        final(co).sqv() == old(co).sqv(),
        final(co).stream && r is Some ==> final(co).row == stotal(f@),
        ({
            let sc = scan(data@, f@, t@, s@, old(co).view(f@.nc), p as int);
            &&& r is Some <==> scan_ok(f@, t@, s@) && sc.ok
            &&& r matches Some(pos) ==> {
                &&& final(co).view(f@.nc) == sc.a
                &&& marker_after(data@, pos as int) == marker_after(data@, sc.p)
                &&& p <= pos <= data@.len() + 0x1_0010
            }
        }),
        final(mt).n + 4 * p <= old(mt).n + 4 * (match r {
            Some(pos) => pos as int,
            None => data@.len() + 0x1_0020int,
        }) + scan_work(f@, s@, old(co).stream),
{
    let ghost d = data@;
    let ghost fv = f@;
    let ghost tv = t@;
    let ghost sv = s@;
    let ghost nc = fv.nc;
    let ghost total = scan(d, fv, tv, sv, co.view(nc), p as int);
    proof {
        lemma_sw_nn(fv, *g, sv, co.stream);
    }
    let cx = match make_ctx(f, t, s) {
        Some(cx) => cx,
        None => {
            return None;
        },
    };
    let ns = s.ns as usize;
    assert(sv.ci[0] == s.ci[0]);
    assert(s.ci[0] < fv.nc);
    assert(g.cw[s.ci[0] as int] == cw(fv, s.ci[0] as int));
    assert(g.wb[s.ci[0] as int] == wb(fv, s.ci[0] as int) && g.hb[s.ci[0] as int] == hb(fv, s.ci[0] as int));
    let mw: u32;
    let mh: u32;
    if ns == 1 {
        mw = g.wb[s.ci[0] as usize];
        mh = g.hb[s.ci[0] as usize];
    } else {
        mw = g.mcux;
        mh = g.mcuy;
    }
    assert(mw == mcu_w(fv, sv) && mh == mcu_h(fv, sv));
    assert(mw <= 0x4_0080 && mh <= 0x4_0080) by {
        let c = s.ci[0] as int;
        assert(g.cw[c] == cw(fv, c) && g.ch[c] == ch(fv, c));
        assert(fv.comps[c].h <= 4 && fv.comps[c].v <= 4);
        assert(mcux(fv) * (fv.comps[c].h as int) <= 0x4_0080 && mcuy(fv) * (fv.comps[c].v as int) <= 0x4_0080)
            by (nonlinear_arith)
            requires
                mcux(fv) <= 0x1_0020,
                mcuy(fv) <= 0x1_0020,
                0 <= fv.comps[c].h <= 4,
                0 <= fv.comps[c].v <= 4,
        ;
    }
    let ghost nm = mw * mh;
    assert(scan_mcus(fv, sv) == nm);
    assert(0 <= nm <= 0x4_0080 * 0x4_0080) by (nonlinear_arith)
        requires
            nm == mw * mh,
            mw <= 0x4_0080,
            mh <= 0x4_0080,
    ;
    let mut st = ScanSt { br: BitReader::new(p, Ghost(data@)), pred: [0; 3], eob: 0, insuf: false, togo: t.ri as i64, rst: 0 };
    proof {
        let init = ssv(st, co.view(nc));
        let lit = SS {
            a: co.view(nc),
            pred: seq![0int, 0int, 0int],
            eob: 0,
            p: p as int,
            n: 0,
            insuf: false,
            togo: tv.ri as int,
            rst: 0,
            ok: true,
        };
        assert(init.pred =~= lit.pred);
        assert(init == lit);
    }
    let ghost m0 = mt.n;
    let ghost fr: int = if co.stream { rowc(fv) } else { 0 };
    assert(fr >= 0);
    let mut my: u32 = 0;
    while my < mh
        invariant
            my <= mh,
            m0 == old(mt).n,
            fr == if old(co).stream { rowc(fv) } else { 0int },
            fr >= 0,
            mt.n + 4 * p <= m0 + 4 * st.br.p0@ + 7 * (my * mw) + my * (fr + 1),
            d == data@,
            fv == f@,
            tv == t@,
            sv == s@,
            nc == fv.nc,
            ns == s.ns <= 3,
            mw == mcu_w(fv, sv),
            mh == mcu_h(fv, sv),
            nm == mw * mh,
            nm == scan_mcus(fv, sv),
            nm <= 0x4_0080 * 0x4_0080,
            len_ok(d),
            frame_basic(fv),
            g.wf(fv),
            scan_pre(fv, sv),
            scan_ok(fv, tv, sv),
            cx.wf(fv, tv, sv),
            co.wf(fv),
            co.stream == old(co).stream,
            co.sqv() == old(co).sqv(),
            co.spre(fv, sv, my as int),
            co.stream ==> mh == stotal(fv),
            st.br.wf(d),
            seg_ok(d, p as int, st.br.p0@),
            st.br.p0@ >= p,
            st.rst < 8,
            -(my * mw) <= st.togo <= 65535,
            my * mw <= nm,
            total == scan(d, fv, tv, sv, old(co).view(nc), p as int),
            scan_from(d, fv, tv, sv, ssv(st, co.view(nc)), my * mw) == total,
        decreases mh - my,
    {
        let mut mx: u32 = 0;
        while mx < mw
            invariant
                mx <= mw,
                m0 == old(mt).n,
                fr == if old(co).stream { rowc(fv) } else { 0int },
                fr >= 0,
                mt.n + 4 * p <= m0 + 4 * st.br.p0@ + 7 * (my * mw + mx) + my * (fr + 1),
                my < mh,
                d == data@,
                fv == f@,
                tv == t@,
                sv == s@,
                nc == fv.nc,
                ns == s.ns <= 3,
                mw == mcu_w(fv, sv),
                mh == mcu_h(fv, sv),
                nm == mw * mh,
                nm == scan_mcus(fv, sv),
                nm <= 0x4_0080 * 0x4_0080,
                len_ok(d),
                frame_basic(fv),
                g.wf(fv),
                scan_pre(fv, sv),
                scan_ok(fv, tv, sv),
                cx.wf(fv, tv, sv),
                co.wf(fv),
                co.stream == old(co).stream,
                co.sqv() == old(co).sqv(),
                co.spre(fv, sv, my as int),
                co.stream ==> mh == stotal(fv),
                st.br.wf(d),
                seg_ok(d, p as int, st.br.p0@),
                st.br.p0@ >= p,
            st.br.p0@ >= p,
                st.rst < 8,
                -(my * mw + mx) <= st.togo <= 65535,
                my * mw + mx <= nm,
                total == scan(d, fv, tv, sv, old(co).view(nc), p as int),
                scan_from(d, fv, tv, sv, ssv(st, co.view(nc)), my * mw + mx) == total,
            decreases mw - mx,
        {
            let ghost m = my * mw + mx;
            let ghost cur0 = ssv(st, co.view(nc));
            proof {
                lemma_sub(my as int, mx as int, mh as int, mw as int);
                assert(mh * mw == mw * mh) by (nonlinear_arith);
                assert(m < nm);
            }
            let ok = mcu_step_x(data, f, g, t, s, &cx, &mut st, co, my, mx, Ghost(p as int), Tracked(mt));
            proof {
                mt.n = mt.n + 1;
            }
            if !ok {
                proof {
                    mt.n = mt.n + st.br.wk@ as nat;
                    lemma_scan_work(fv, sv, old(co).stream, my as int, mx as int + 1, fr);
                    lemma_scan_notok(d, fv, tv, sv, mcu_step(d, fv, tv, sv, cur0, m), m + 1);
                }
                return None;
            }
            proof {
                let nx = mcu_step(d, fv, tv, sv, cur0, m);
                assert(ssv(st, co.view(nc)) == nx);
                assert(scan_from(d, fv, tv, sv, cur0, m) == scan_from(d, fv, tv, sv, nx, m + 1));
                assert(my * mw + (mx + 1) == m + 1);
            }
            mx += 1;
        }
        proof {
            assert((my + 1) * mw == my * mw + mw) by (nonlinear_arith);
            assert((my + 1) * (fr + 1) == my * (fr + 1) + fr + 1) by (nonlinear_arith);
        }
        if co.stream {
            flush_row(co, f, g, Tracked(mt));
        }
        proof {
            mt.n = mt.n + 1;
        }
        my += 1;
    }
    proof {
        assert(mh * mw == mw * mh) by (nonlinear_arith);
        assert(ssv(st, co.view(nc)) == total);
        mt.n = mt.n + st.br.wk@ as nat;
        lemma_scan_work(fv, sv, old(co).stream, mh as int, 0, fr);
    }
    Some(st.br.pos)
}

} // verus!
