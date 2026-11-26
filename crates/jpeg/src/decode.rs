//! The decoder: a file to an image.
use crate::bits::*;
use crate::idct::*;
use crate::parse::*;
use crate::render::*;
use crate::scan::*;
use crate::spec::*;
use crate::stream::*;
use crate::types::*;
use crate::work::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// A decoded image: `nc` bytes per pixel (1 gray, or 3 red, green, blue),
/// rows top to bottom.
pub struct Picture {
    pub w: u32,
    pub h: u32,
    pub nc: u8,
    pub px: Vec<u8>,
}

impl View for Picture {
    type V = Image;

    open spec fn view(&self) -> Image {
        Image { w: self.w as int, h: self.h as int, nc: self.nc as int, px: self.px@ }
    }
}

/// What a decoder that has read a whole file holds.
pub open spec fn coded(st: DecX) -> Coded {
    Coded { f: st.f@, a: st.co.view(st.f@.nc), ql: qlv(st.ql), color: color_v(st.color) }
}

/// Reads a whole file's marker segments and scans. The ghost result is
/// the number of scans decoded and the blocks of the frame (0 if none).
pub fn decode_coefs(data: &[u8], Tracked(mt): Tracked<&mut Meter>) -> (r: (Result<DecX, Error>, Ghost<(nat, int)>))
    ensures
        match r.0 {
            Ok(st) => jpeg_coded(data@) == Some(coded(st)) && st.wf() && st.started,
            Err(Error::Invalid) => jpeg_coded(data@) is None,
            Err(Error::OutOfMemory) => true,
        },
        r.0 matches Ok(st) ==> r.1@.0 == st.nscan@ && r.1@.1 == fblk(st.f@),
        r.1@.1 >= 0,
        r.1@.0 <= data@.len() + 0x1_0010,
        final(mt).n <= old(mt).n + 4 * (data@.len() + 0x1_0020) + (r.1@.0 + 1) * scan_cost(r.1@.1) + 200,
{
    if data.len() >= usize::MAX - 0x2_0000 {
        return (Err(Error::OutOfMemory), Ghost((0, 0)));
    }
    if rd(data, 0) != 0xFF || rd(data, 1) != 0xD8 {
        return (Err(Error::Invalid), Ghost((0, 0)));
    }
    let mut st = dec_new();
    let r = run_x(data, &mut st, 2, Tracked(mt));
    let ghost g = (st.nscan@, blk(st));
    match r {
        Ok(()) => {
            proof {
                assert(st.has_f);
                assert(st@.ql =~= qlv(st.ql));
            }
            (Ok(st), Ghost(g))
        },
        Err(e) => (Err(e), Ghost(g)),
    }
}

/// The bound on `decode`'s work for an `n`-byte file of `s` scans whose
/// frame is stored in `b` blocks and has `px` pixels.
pub open spec fn jpeg_work(n: int, s: int, b: int, px: int) -> int {
    4 * (n + 0x1_0020) + (s + 1) * scan_cost(b) + render_cost_of(b, px) + 200
}

/// `work::render_cost` from the counts.
pub open spec fn render_cost_of(b: int, px: int) -> int {
    66 * b + 110 * px + 8
}

/// What the segments before the first scan say about a file.
pub struct Header {
    pub w: u16,
    pub h: u16,
    pub nc: u8,
    pub prog: bool,
    /// The sampling factors of each component.
    pub hs: [u8; 3],
    pub vs: [u8; 3],
    /// 0 gray, 1 YCbCr, 2 RGB.
    pub color: u8,
}

/// Reads the marker segments up to the first scan, with the same code that
/// `decode` reads them with. This is for callers that want an image's size
/// before decoding it; it is proven free of run-time errors and to end, and
/// nothing more is claimed of it: a file whose header it reads may still be
/// one `decode` rejects.
pub fn read_header(data: &[u8]) -> (r: Result<Header, Error>) {
    if data.len() >= usize::MAX - 0x2_0000 {
        return Err(Error::OutOfMemory);
    }
    if rd(data, 0) != 0xFF || rd(data, 1) != 0xD8 {
        return Err(Error::Invalid);
    }
    let mut st = dec_new();
    let mut p: usize = 2;
    let tracked mut wm = Meter { n: 0 };
    loop
        invariant
            len_ok(data@),
            p <= data@.len() + 0x1_0010,
            st.wf(),
        decreases data@.len() + 0x1_0010 - p,
    {
        let (m, _q) = marker_after_x(data, p, Tracked(&mut wm));
        if p < data.len() && m == 0xDA {
            if !st.has_f {
                return Err(Error::Invalid);
            }
            let f = st.f;
            let color: u8 = if f.nc == 1 {
                0
            } else if st.jfif {
                1
            } else if st.has_adobe {
                if st.adobe == 0 {
                    2
                } else {
                    1
                }
            } else if f.comps[0].id == 82 && f.comps[1].id == 71 && f.comps[2].id == 66 {
                2
            } else {
                1
            };
            return Ok(
                Header {
                    w: f.w,
                    h: f.h,
                    nc: f.nc,
                    prog: f.prog,
                    hs: [f.comps[0].h, f.comps[1].h, f.comps[2].h],
                    vs: [f.comps[0].v, f.comps[1].v, f.comps[2].v],
                    color,
                },
            );
        }
        match step_x(data, &mut st, p, Tracked(&mut wm)) {
            Ok(Some(p2)) => {
                p = p2;
            },
            Ok(None) => {
                return Err(Error::Invalid);
            },
            Err(e) => {
                return Err(e);
            },
        }
    }
}

/// One dimension of a component: the ratio to the frame's, and the
/// component's size in samples and in blocks.
pub proof fn lemma_dim(w: int, hc: int, hmax: int)
    requires
        w >= 1,
        1 <= hc <= 4,
        1 <= hmax <= 4,
        hmax % hc == 0,
    ensures
        1 <= hmax / hc <= 4,
        w <= cdiv(w * hc, hmax) * (hmax / hc),
        1 <= cdiv(w * hc, hmax) <= 8 * cdiv(w * hc, 8 * hmax),
        1 <= cdiv(w * hc, 8 * hmax),
{
    let hs = hmax / hc;
    lemma_fundamental_div_mod(hmax, hc);
    assert(hmax == hc * hs);
    assert(1 <= hs <= 4) by (nonlinear_arith)
        requires
            hmax == hc * hs,
            1 <= hc,
            1 <= hmax <= 4,
    ;
    let a = w * hc;
    assert(a >= 1) by (nonlinear_arith)
        requires
            a == w * hc,
            w >= 1,
            hc >= 1,
    ;
    let d = cdiv(a, hmax);
    let b = cdiv(a, 8 * hmax);
    lemma_cdiv(a, hmax);
    lemma_cdiv(a, 8 * hmax);
    assert(w <= d * hs) by (nonlinear_arith)
        requires
            w * hc <= d * hmax,
            hmax == hc * hs,
            hc >= 1,
    ;
    assert(d >= 1 && b >= 1) by (nonlinear_arith)
        requires
            a >= 1,
            a <= d * hmax,
            a <= b * (8 * hmax),
            hmax >= 1,
    ;
    assert(b * (8 * hmax) == (8 * b) * hmax) by (nonlinear_arith);
    lemma_fundamental_div_mod_converse((8 * b) * hmax + hmax - 1, hmax, 8 * b, hmax - 1);
    lemma_div_is_ordered(a + hmax - 1, (8 * b) * hmax + hmax - 1, hmax);
}

/// What upsampling needs of a component's sizes.
pub proof fn lemma_comp_geom(f: Frame, c: int)
    requires
        frame_ok(f),
        frame_basic(f),
        0 <= c < f.nc,
    ensures
        1 <= maxh(f) / f.comps[c].h as int <= 4,
        1 <= maxv(f) / f.comps[c].v as int <= 4,
        f.w <= dw(f, c) * (maxh(f) / f.comps[c].h as int),
        f.h <= dh(f, c) * (maxv(f) / f.comps[c].v as int),
        1 <= dw(f, c) <= 8 * wb(f, c),
        1 <= dh(f, c) <= 8 * hb(f, c),
        1 <= wb(f, c),
        1 <= hb(f, c),
{
    assert(1 <= f.comps[0].h <= 4 && 1 <= f.comps[0].v <= 4);
    if f.nc == 3 {
        assert(1 <= f.comps[1].h <= 4 && 1 <= f.comps[1].v <= 4);
        assert(1 <= f.comps[2].h <= 4 && 1 <= f.comps[2].v <= 4);
    }
    assert(1 <= f.comps[c].h <= 4 && 1 <= f.comps[c].v <= 4);
    lemma_dim(f.w, f.comps[c].h as int, maxh(f));
    lemma_dim(f.h, f.comps[c].v as int, maxv(f));
}

/// A component's samples, with what upsampling needs to know of them.
pub struct Plane<'a> {
    pub pl: &'a Vec<u8>,
    pub stride: usize,
    pub pw: usize,
    pub ph: usize,
    pub hs: usize,
    pub vs: usize,
    pub rows: Ghost<int>,
}

impl<'a> Plane<'a> {
    /// These are the samples of component `c` of `k`.
    pub open spec fn ok(&self, k: Coded, c: int) -> bool {
        &&& 0 <= c < k.f.comps.len()
        &&& plane_is(self.pl@, self.stride as int, self.rows@, k, c)
        &&& self.pw == dw(k.f, c)
        &&& self.ph == dh(k.f, c)
        &&& self.hs == maxh(k.f) / k.f.comps[c].h as int
        &&& self.vs == maxv(k.f) / k.f.comps[c].v as int
        &&& 1 <= self.hs <= 4
        &&& 1 <= self.vs <= 4
        &&& 1 <= self.pw <= self.stride
        &&& 1 <= self.ph <= self.rows@
        &&& k.f.w <= self.pw * self.hs
        &&& k.f.h <= self.ph * self.vs
    }
}

pub proof fn lemma_plane_is(pl: Seq<u8>, k: Coded, c: int, wbc: int, hbc: int)
    requires
        pl.len() == (8 * wbc) * (8 * hbc),
        forall|rr: int, x: int|
            0 <= rr < 8 * hbc && 0 <= x < 8 * wbc ==> #[trigger] pat(pl, 8 * wbc, rr, x) == psample(
                k.a[c],
                k.ql[c],
                cw(k.f, c),
                rr,
                x,
            ),
    ensures
        plane_is(pl, 8 * wbc, 8 * hbc, k, c),
{
    assert forall|rr: int, x: int| 0 <= rr < 8 * hbc && 0 <= x < 8 * wbc implies #[trigger] pat(pl, 8 * wbc, rr, x) as int
        == sample(k, c, rr, x) by {
        assert(pat(pl, 8 * wbc, rr, x) == psample(k.a[c], k.ql[c], cw(k.f, c), rr, x));
    }
}

/// `pl` holds the samples of component `c`'s blocks of image data.
pub open spec fn pl_ok(pl: Seq<u8>, k: Coded, c: int) -> bool {
    &&& pl.len() == (8 * wb(k.f, c)) * (8 * hb(k.f, c))
    &&& forall|rr: int, x: int|
        0 <= rr < 8 * hb(k.f, c) && 0 <= x < 8 * wb(k.f, c) ==> #[trigger] pat(pl, 8 * wb(k.f, c), rr, x) == psample(
            k.a[c],
            k.ql[c],
            cw(k.f, c),
            rr,
            x,
        )
}

/// A plane that a streamed scan has finished is the component's samples.
proof fn lemma_stream_pl(a: Seq<i16>, pl: Seq<u8>, k: Coded, c: int, vr: int, row: int)
    requires
        win_ok(a, k.a[c], pl, k.ql[c], cw(k.f, c), ch(k.f, c), wb(k.f, c), hb(k.f, c), vr, row),
        hb(k.f, c) <= vr * row,
    ensures
        pl_ok(pl, k, c),
{
    let st = 8 * wb(k.f, c);
    assert forall|rr: int, x: int| 0 <= rr < 8 * hb(k.f, c) && 0 <= x < st implies #[trigger] pat(pl, st, rr, x) == psample(
        k.a[c],
        k.ql[c],
        cw(k.f, c),
        rr,
        x,
    ) by {
        lemma_grid(rr, x, 8 * hb(k.f, c), st);
        lemma_fundamental_div_mod_converse(rr * st + x, st, rr, x);
        assert(pl[rr * st + x] == psample(k.a[c], k.ql[c], cw(k.f, c), rr, x));
    }
}

/// The samples of component `c` when its scans were not streamed (when
/// they were, the samples exist already and nothing is computed).
fn comp_buf(st: &DecX, c: usize, Tracked(mt): Tracked<&mut Meter>) -> (r: Option<Vec<u8>>)
    requires
        st.wf(),
        st.started,
        c < st.f.nc,
    ensures
        final(mt).n <= old(mt).n + 66 * cblk(st.f@, c as int),
        r matches Some(pl) ==> (!st.co.stream ==> pl_ok(pl@, coded(*st), c as int)),
{
    hide(psample);
    hide(wb);
    hide(hb);
    reveal(cblk);
    if st.co.stream {
        proof {
            crate::scan::lemma_cw_pos(st.f@, st.g, c as int);
            let (a, b) = (cw(st.f@, c as int), ch(st.f@, c as int));
            assert(a * b >= 0) by (nonlinear_arith)
                requires
                    a >= 1,
                    b >= 1,
            ;
        }
        return Some(Vec::new());
    }
    let ghost f = st.f@;
    let ghost ci = c as int;
    let g = st.g;
    proof {
        reveal(csize);
        lemma_comp_geom(f, ci);
        assert(g.cw[ci] == cw(f, ci));
        assert(g.ch[ci] == ch(f, ci) && g.wb[ci] == wb(f, ci) && g.hb[ci] == hb(f, ci));
        assert(g.wb[ci] <= g.cw[ci] && g.hb[ci] <= g.ch[ci] && g.cw[ci] <= 0x4_0080 && g.ch[ci] <= 0x4_0080);
    }
    let kt = crate::idct16::idct_consts();
    if c == 0 {
        plane_x(&st.co.a0, &st.ql[0], &kt, g.cw[0], g.wb[0], g.hb[0], Ghost(g.ch[0] as int), Tracked(mt))
    } else if c == 1 {
        plane_x(&st.co.a1, &st.ql[1], &kt, g.cw[1], g.wb[1], g.hb[1], Ghost(g.ch[1] as int), Tracked(mt))
    } else {
        plane_x(&st.co.a2, &st.ql[2], &kt, g.cw[2], g.wb[2], g.hb[2], Ghost(g.ch[2] as int), Tracked(mt))
    }
}

/// Component `c` as upsampling wants it: `buf` from `comp_buf`, or the
/// plane a streamed scan left.
fn comp_plane<'a>(st: &'a DecX, buf: &'a Vec<u8>, c: usize) -> (r: Plane<'a>)
    requires
        st.wf(),
        st.started,
        c < st.f.nc,
        !st.co.stream ==> pl_ok(buf@, coded(*st), c as int),
    ensures
        r.ok(coded(*st), c as int),
{
    hide(plane_is);
    hide(psample);
    hide(dw);
    hide(dh);
    hide(wb);
    hide(hb);
    hide(maxh);
    hide(maxv);
    hide(win_ok);
    let ghost f = st.f@;
    let ghost k = coded(*st);
    let ghost ci = c as int;
    let g = st.g;
    proof {
        lemma_comp_geom(f, ci);
        assert(g.cw[ci] == cw(f, ci));
        assert(g.ch[ci] == ch(f, ci) && g.wb[ci] == wb(f, ci) && g.hb[ci] == hb(f, ci) && g.dw[ci] == dw(f, ci) && g.dh[ci]
            == dh(f, ci));
        assert(g.wb[ci] <= g.cw[ci] && g.hb[ci] <= g.ch[ci] && g.cw[ci] <= 0x4_0080 && g.ch[ci] <= 0x4_0080);
        assert(f.comps[ci] == st.f.comps[ci]);
        assert(g.maxh == maxh(f) && g.maxv == maxv(f));
    }
    let pl: &Vec<u8> = if st.co.stream {
        proof {
            reveal(Coefs::swf);
            reveal(Coefs::sqv);
            let vr = srows(f, ci);
            assert(hb(f, ci) <= vr * stotal(f)) by {
                reveal(hb);
                if f.nc != 1 {
                    assert(ch(f, ci) == mcuy(f) * vr);
                    assert(mcuy(f) * vr == vr * mcuy(f)) by (nonlinear_arith);
                }
            }
            assert(k.ql[ci] == st.co.sq[ci]@);
        }
        if c == 0 {
            proof {
                lemma_stream_pl(st.co.a0@, st.co.p0@, k, 0, srows(f, 0), stotal(f));
            }
            &st.co.p0
        } else if c == 1 {
            proof {
                lemma_stream_pl(st.co.a1@, st.co.p1@, k, 1, srows(f, 1), stotal(f));
            }
            &st.co.p1
        } else {
            proof {
                lemma_stream_pl(st.co.a2@, st.co.p2@, k, 2, srows(f, 2), stotal(f));
            }
            &st.co.p2
        }
    } else {
        buf
    };
    proof {
        assert(pl_ok(pl@, k, ci));
        lemma_plane_is(pl@, k, ci, g.wb[ci] as int, g.hb[ci] as int);
    }
    Plane {
        pl,
        stride: 8 * g.wb[c] as usize,
        pw: g.dw[c] as usize,
        ph: g.dh[c] as usize,
        hs: (g.maxh / f_h(st, c) as u32) as usize,
        vs: (g.maxv / f_v(st, c) as u32) as usize,
        rows: Ghost(8 * (g.hb[ci] as int)),
    }
}

fn f_h(st: &DecX, c: usize) -> (r: u8)
    requires
        c < 3,
    ensures
        r == st.f.comps[c as int].h,
{
    st.f.comps[c].h
}

fn f_v(st: &DecX, c: usize) -> (r: u8)
    requires
        c < 3,
    ensures
        r == st.f.comps[c as int].v,
{
    st.f.comps[c].v
}

/// Row `y` of component `c` at the frame's resolution.
fn prow(p: &Plane, y: usize, w: usize, out: &mut Vec<u8>, Ghost(k): Ghost<Coded>, Ghost(c): Ghost<int>, Tracked(mt): Tracked<&mut Meter>)
    requires
        p.ok(k, c),
        w == k.f.w,
        y < k.f.h,
        old(out).len() == w,
    ensures
        final(mt).n <= old(mt).n + 2 * w + 32,
        final(out).len() == w,
        forall|x: int| 0 <= x < w ==> (#[trigger] final(out)[x]) as int == upsampled(k, c, y as int, x),
{
    hide(upsampled);
    hide(plane_is);
    up_row(p.pl, p.stride, p.pw, p.ph, p.hs, p.vs, y, w, out, Ghost(p.rows@), Ghost(k), Ghost(c), Tracked(mt));
}

/// Byte `i` of the image a decoder's coefficients give.
pub open spec fn pix(k: Coded, i: int) -> u8 {
    let w = k.f.w as int;
    let nc = k.f.nc as int;
    pixel(k, i / (w * nc), (i / nc) % w, i % nc) as u8
}

/// Byte `i` of row `y` of an image `w` wide with `nc` channels.
pub proof fn lemma_pix_idx(y: int, w: int, nc: int, t: int)
    requires
        y >= 0,
        w >= 1,
        nc == 1 || nc == 3,
        0 <= t < nc * w,
    ensures
        ({
            let i = y * (w * nc) + t;
            &&& i / (w * nc) == y
            &&& (i / nc) % w == t / nc
            &&& i % nc == t % nc
            &&& 0 <= t / nc < w
        }),
{
    let i = y * (w * nc) + t;
    let x = t / nc;
    let ch = t % nc;
    assert(w * nc == nc * w) by (nonlinear_arith);
    lemma_fundamental_div_mod_converse(i, w * nc, y, t);
    assert(i == (y * w + x) * nc + ch) by (nonlinear_arith)
        requires
            i == y * (w * nc) + t,
            t == nc * x + ch,
    ;
    assert(0 <= y * w) by (nonlinear_arith)
        requires
            y >= 0,
            w >= 1,
    ;
    lemma_fundamental_div_mod_converse(i, nc, y * w + x, ch);
    lemma_fundamental_div_mod_converse(y * w + x, w, y, x);
}

/// Row `y` of a grayscale image into `px`.
fn emit_gray(p0: &Plane, y: usize, w: usize, r0: &mut Vec<u8>, px: &mut [u8], Ghost(k): Ghost<Coded>, Tracked(mt): Tracked<&mut Meter>)
    requires
        p0.ok(k, 0),
        k.f.nc == 1,
        k.color == Color::Gray,
        w == k.f.w,
        w >= 1,
        y < k.f.h,
        old(r0).len() == w,
        y * w + w <= old(px)@.len(),
    ensures
        final(mt).n <= old(mt).n + 3 * w + 32,
        final(r0).len() == w,
        final(px)@.len() == old(px)@.len(),
        forall|i: int| y * w <= i < y * w + w ==> (#[trigger] final(px)@[i]) == pix(k, i),
        forall|i: int| 0 <= i < y * w || y * w + w <= i < final(px)@.len() ==> (#[trigger] final(px)@[i]) == old(px)@[i],
{
    hide(upsampled);
    let _ = px.len();
    prow(p0, y, w, r0, Ghost(k), Ghost(0), Tracked(mt));
    assert(0 <= y * w) by (nonlinear_arith)
        requires
            y >= 0,
            w >= 0,
    ;
    let o = y * w;
    gray_row(r0, w, px, o, Tracked(mt));
    proof {
        assert forall|i: int| y * w <= i < y * w + w implies (#[trigger] px@[i]) == pix(k, i) by {
            let t = i - o;
            lemma_pix_idx(y as int, w as int, 1, t);
            assert(px@[i] == r0[t]);
            assert(r0[t] as int == upsampled(k, 0, y as int, t));
        }
    }
}

/// Row `y` of a color image into `px`.
fn emit_color(
    p0: &Plane,
    p1: &Plane,
    p2: &Plane,
    ycc: bool,
    y: usize,
    w: usize,
    r0: &mut Vec<u8>,
    r1: &mut Vec<u8>,
    r2: &mut Vec<u8>,
    px: &mut [u8],
    Ghost(k): Ghost<Coded>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        p0.ok(k, 0),
        p1.ok(k, 1),
        p2.ok(k, 2),
        k.f.nc == 3,
        k.color == if ycc {
            Color::YCbCr
        } else {
            Color::Rgb
        },
        w == k.f.w,
        w >= 1,
        y < k.f.h,
        old(r0).len() == w,
        old(r1).len() == w,
        old(r2).len() == w,
        y * (w * 3) + w * 3 <= old(px)@.len(),
    ensures
        final(mt).n <= old(mt).n + 7 * w + 96,
        final(r0).len() == w,
        final(r1).len() == w,
        final(r2).len() == w,
        final(px)@.len() == old(px)@.len(),
        forall|i: int| y * (w * 3) <= i < y * (w * 3) + w * 3 ==> (#[trigger] final(px)@[i]) == pix(k, i),
        forall|i: int|
            0 <= i < y * (w * 3) || y * (w * 3) + w * 3 <= i < final(px)@.len() ==> (#[trigger] final(px)@[i]) == old(px)@[i],
{
    hide(upsampled);
    let _ = px.len();
    prow(p0, y, w, r0, Ghost(k), Ghost(0), Tracked(mt));
    prow(p1, y, w, r1, Ghost(k), Ghost(1), Tracked(mt));
    prow(p2, y, w, r2, Ghost(k), Ghost(2), Tracked(mt));
    assert(0 <= y * (w * 3)) by (nonlinear_arith)
        requires
            y >= 0,
            w >= 0,
    ;
    let o = y * (w * 3);
    if ycc {
        ycc_row(r0.as_slice(), r1.as_slice(), r2.as_slice(), w, px, o, Tracked(mt));
    } else {
        rgb_row(r0, r1, r2, w, px, o, Tracked(mt));
    }
    proof {
        assert forall|i: int| o <= i < o + w * 3 implies (#[trigger] px@[i]) == pix(k, i) by {
            let t = i - o;
            lemma_pix_idx(y as int, w as int, 3, t);
            let x = t / 3;
            assert(r0[x] as int == upsampled(k, 0, y as int, x));
            assert(r1[x] as int == upsampled(k, 1, y as int, x));
            assert(r2[x] as int == upsampled(k, 2, y as int, x));
            assert(px@[i] as int == chan(k.color, r0[x] as int, r1[x] as int, r2[x] as int, t % 3));
            assert(px@[i] as int == pixel(k, y as int, x, t % 3));
        }
    }
}

/// The rows of a grey picture.
fn gray_rows(p0: &Plane, w: usize, h: usize, r0: &mut Vec<u8>, px: &mut [u8], Ghost(k): Ghost<Coded>, Ghost(wn): Ghost<int>, Tracked(mt): Tracked<&mut Meter>)
    requires
        w == k.f.w,
        h == k.f.h,
        w >= 1,
        k.f.nc == 1,
        wn == w,
        k.color == Color::Gray,
        old(px)@.len() == h * wn,
        old(r0).len() == w,
        p0.ok(k, 0),
    ensures
        final(mt).n <= old(mt).n + h * (3 * w + 33),
        final(px)@.len() == old(px)@.len(),
        forall|i: int| 0 <= i < h * wn ==> (#[trigger] final(px)@[i]) == pix(k, i),
{
    hide(pix);
    hide(Plane::ok);
    let ghost m1 = mt.n;
    let mut y: usize = 0;
    while y < h
        invariant
            y <= h,
            mt.n <= m1 + y * (3 * w + 33),
            w == k.f.w,
            h == k.f.h,
            w >= 1,
            k.f.nc == 1,
            wn == w,
            k.color == Color::Gray,
            px@.len() == h * wn,
            r0.len() == w,
            p0.ok(k, 0),
            forall|i: int| 0 <= i < y * wn ==> (#[trigger] px@[i]) == pix(k, i),
        decreases h - y,
    {
        assert(0 <= y * wn && y * wn + wn <= h * wn && (y + 1) * wn == y * wn + wn) by (nonlinear_arith)
            requires
                0 <= y < h,
                wn >= 0,
        ;
        emit_gray(p0, y, w, r0, px, Ghost(k), Tracked(mt));
        y += 1;
        proof {
            mt.n = mt.n + 1;
            assert(y * (3 * w + 33) == (y - 1) * (3 * w + 33) + 3 * w + 33) by (nonlinear_arith);
        }
    }
}

/// The rows of a colour picture.
fn color_rows(
    p0: &Plane,
    p1: &Plane,
    p2: &Plane,
    ycc: bool,
    w: usize,
    h: usize,
    r0: &mut Vec<u8>,
    r1: &mut Vec<u8>,
    r2: &mut Vec<u8>,
    px: &mut [u8],
    Ghost(k): Ghost<Coded>,
    Ghost(wn): Ghost<int>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        w == k.f.w,
        h == k.f.h,
        w >= 1,
        k.f.nc == 3,
        wn == w * 3,
        k.color == if ycc {
            Color::YCbCr
        } else {
            Color::Rgb
        },
        old(px)@.len() == h * wn,
        old(r0).len() == w,
        old(r1).len() == w,
        old(r2).len() == w,
        p0.ok(k, 0),
        p1.ok(k, 1),
        p2.ok(k, 2),
    ensures
        final(mt).n <= old(mt).n + h * (7 * w + 97),
        final(px)@.len() == old(px)@.len(),
        forall|i: int| 0 <= i < h * wn ==> (#[trigger] final(px)@[i]) == pix(k, i),
{
    hide(pix);
    hide(Plane::ok);
    let ghost m1 = mt.n;
    let mut y: usize = 0;
    while y < h
        invariant
            y <= h,
            mt.n <= m1 + y * (7 * w + 97),
            w == k.f.w,
            h == k.f.h,
            w >= 1,
            k.f.nc == 3,
            wn == w * 3,
            k.color == if ycc {
                Color::YCbCr
            } else {
                Color::Rgb
            },
            px@.len() == h * wn,
            r0.len() == w,
            r1.len() == w,
            r2.len() == w,
            p0.ok(k, 0),
            p1.ok(k, 1),
            p2.ok(k, 2),
            forall|i: int| 0 <= i < y * wn ==> (#[trigger] px@[i]) == pix(k, i),
        decreases h - y,
    {
        assert(0 <= y * wn && y * wn + wn <= h * wn && (y + 1) * wn == y * wn + wn) by (nonlinear_arith)
            requires
                0 <= y < h,
                wn >= 0,
        ;
        emit_color(p0, p1, p2, ycc, y, w, r0, r1, r2, px, Ghost(k), Tracked(mt));
        y += 1;
        proof {
            mt.n = mt.n + 1;
            assert(y * (7 * w + 97) == (y - 1) * (7 * w + 97) + 7 * w + 97) by (nonlinear_arith);
        }
    }
}

/// The rows `render_to` writes are the specification's picture.
proof fn lemma_render_px(k: Coded, px: Seq<u8>, w: int, h: int, nc: int, wn: int)
    requires
        k.f.w == w,
        k.f.h == h,
        k.f.nc == nc,
        wn == w * nc,
        px.len() == h * wn,
        forall|i: int| 0 <= i < h * wn ==> (#[trigger] px[i]) == pix(k, i),
    ensures
        px == render(k).px,
{
    reveal(pix);
    let im = render(k);
    assert(k.f.w * k.f.h * k.f.nc == h * wn) by (nonlinear_arith)
        requires
            k.f.w == w,
            k.f.h == h,
            k.f.nc == nc,
            wn == w * nc,
    ;
    assert forall|i: int| 0 <= i < h * wn implies px[i] == im.px[i] by {
        assert(px[i] == pix(k, i));
    }
    assert(px =~= im.px);
}

/// The row loops' work fits in `render_to`'s bound.
proof fn lemma_render_rows(w: int, h: int, pp: int)
    requires
        w >= 1,
        h >= 1,
        pp == w * h,
    ensures
        3 * w + h * (7 * w + 97) <= 107 * pp,
        w + h * (3 * w + 33) <= 107 * pp,
{
    assert(3 * w + h * (7 * w + 97) <= 107 * (w * h)) by (nonlinear_arith)
        requires
            w >= 1,
            h >= 1,
    ;
    assert(w + h * (3 * w + 33) <= 107 * (w * h)) by (nonlinear_arith)
        requires
            w >= 1,
            h >= 1,
    ;
}

/// The parts of `render_to`'s work bound.
proof fn lemma_render_cost(f: Frame, g: Geom)
    requires
        g.wf(f),
        frame_basic(f),
    ensures
        f.nc == 1 ==> 66 * cblk(f, 0) == 66 * fblk(f),
        f.nc == 3 ==> 66 * cblk(f, 0) + 66 * cblk(f, 1) + 66 * cblk(f, 2) == 66 * fblk(f),
        cblk(f, 0) >= 0,
        f.nc == 3 ==> cblk(f, 1) >= 0 && cblk(f, 2) >= 0,
        f.w <= npx(f),
        f.h <= npx(f),
        npx(f) == f.w * f.h,
{
    reveal(cblk);
    crate::scan::lemma_cw_pos(f, g, 0);
    let (c0, h0) = (cw(f, 0), ch(f, 0));
    assert(c0 * h0 >= 1) by (nonlinear_arith)
        requires
            c0 >= 1,
            h0 >= 1,
    ;
    if f.nc == 3 {
        crate::scan::lemma_cw_pos(f, g, 1);
        crate::scan::lemma_cw_pos(f, g, 2);
        let (c1, h1, c2, h2) = (cw(f, 1), ch(f, 1), cw(f, 2), ch(f, 2));
        assert(c1 * h1 >= 1 && c2 * h2 >= 1) by (nonlinear_arith)
            requires
                c1 >= 1,
                h1 >= 1,
                c2 >= 1,
                h2 >= 1,
        ;
    }
    let (w, h) = (f.w, f.h);
    assert(w <= w * h && h <= w * h) by (nonlinear_arith)
        requires
            w >= 1,
            h >= 1,
    ;
}

/// The pixels a decoded file's coefficients give, into `px`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn render_to(st: &DecX, px: &mut [u8], Tracked(mt): Tracked<&mut Meter>) -> (r: Result<(), Error>)
    requires
        st.wf(),
        st.started,
        old(px)@.len() == st.f@.w * st.f@.h * st.f@.nc,
    ensures
        final(mt).n <= old(mt).n + 66 * fblk(st.f@) + 107 * npx(st.f@),
        final(px)@.len() == old(px)@.len(),
        match r {
            Ok(()) => final(px)@ == render(coded(*st)).px,
            Err(Error::Invalid) => false,
            Err(Error::OutOfMemory) => true,
        },
{
    hide(pix);
    hide(pl_ok);
    hide(Plane::ok);
    hide(fblk);
    hide(npx);
    let ghost k = coded(*st);
    let f = st.f;
    let w = f.w as usize;
    let h = f.h as usize;
    let nc = f.nc as usize;
    let ghost wn = (w * nc) as int;
    assert((w as u64) * (h as u64) <= 65535 * 65535 && (w as u64) * (h as u64) * (nc as u64) <= 65535 * 65535 * 3 && (
    w as u64) * (h as u64) * (nc as u64) == h * (w * nc)) by (nonlinear_arith)
        requires
            w <= 65535,
            h <= 65535,
            nc <= 3,
    ;
    let ghost plen = px@.len() as int;
    assert(st.f@.w == w && st.f@.h == h && st.f@.nc == nc);
    assert(plen == w * h * nc);
    assert(plen == h * wn) by (nonlinear_arith)
        requires
            plen == w * h * nc,
            wn == w * nc,
    ;
    let ghost m0 = mt.n;
    let ghost fv = st.f@;
    let ghost bb = fblk(fv);
    let ghost pp = npx(fv);
    proof {
        lemma_render_cost(fv, st.g);
    }
    let b0 = match comp_buf(st, 0, Tracked(mt)) {
        Some(v) => v,
        None => {
            return Err(Error::OutOfMemory);
        },
    };
    let p0 = comp_plane(st, &b0, 0);
    proof {
        mt.n = mt.n + w as nat;
    }
    let mut r0 = match alloc_u8(w) {
        Some(v) => v,
        None => {
            return Err(Error::OutOfMemory);
        },
    };
    if nc == 1 {
        assert(wn == w) by (nonlinear_arith)
            requires
                nc == 1,
                wn == w * nc,
        ;
        let ghost m1 = mt.n;
        gray_rows(&p0, w, h, &mut r0, px, Ghost(k), Ghost(wn), Tracked(mt));
    } else {
        let b1 = match comp_buf(st, 1, Tracked(mt)) {
            Some(v) => v,
            None => {
                return Err(Error::OutOfMemory);
            },
        };
        let b2 = match comp_buf(st, 2, Tracked(mt)) {
            Some(v) => v,
            None => {
                return Err(Error::OutOfMemory);
            },
        };
        let p1 = comp_plane(st, &b1, 1);
        let p2 = comp_plane(st, &b2, 2);
        proof {
            mt.n = mt.n + w as nat;
        }
        let mut r1 = match alloc_u8(w) {
            Some(v) => v,
            None => {
                return Err(Error::OutOfMemory);
            },
        };
        proof {
            mt.n = mt.n + w as nat;
        }
        let mut r2 = match alloc_u8(w) {
            Some(v) => v,
            None => {
                return Err(Error::OutOfMemory);
            },
        };
        let ycc = st.color == 1;
        let ghost m1 = mt.n;
        color_rows(&p0, &p1, &p2, ycc, w, h, &mut r0, &mut r1, &mut r2, px, Ghost(k), Ghost(wn), Tracked(mt));
    }
    proof {
        lemma_render_px(k, px@, w as int, h as int, nc as int, wn);
        lemma_render_rows(w as int, h as int, pp);
    }
    Ok(())
}

/// The number of bytes in the picture of a decoded file, if a `usize`
/// holds it.
pub fn pic_len(st: &DecX) -> (r: Option<usize>)
    requires
        st.wf(),
        st.started,
    ensures
        r matches Some(n) ==> n == st.f@.w * st.f@.h * st.f@.nc,
{
    let w = st.f.w as u64;
    let h = st.f.h as u64;
    let nc = st.f.nc as u64;
    assert(w * h <= 65535 * 65535 && w * h * nc <= 65535 * 65535 * 3) by (nonlinear_arith)
        requires
            w <= 65535,
            h <= 65535,
            nc <= 3,
    ;
    let total = w * h * nc;
    if total > usize::MAX as u64 {
        None
    } else {
        Some(total as usize)
    }
}

/// The picture a decoded file's coefficients give.
pub fn render_x(st: &DecX, Tracked(mt): Tracked<&mut Meter>) -> (r: Result<Picture, Error>)
    requires
        st.wf(),
        st.started,
    ensures
        final(mt).n <= old(mt).n + render_cost_of(fblk(st.f@), npx(st.f@)),
        r matches Ok(pic) ==> pic.w == st.f@.w && pic.h == st.f@.h,
        match r {
            Ok(pic) => pic@ == render(coded(*st)),
            Err(Error::Invalid) => false,
            Err(Error::OutOfMemory) => true,
        },
{
    let total = match pic_len(st) {
        Some(n) => n,
        None => {
            return Err(Error::OutOfMemory);
        },
    };
    proof {
        mt.n = mt.n + total as nat;
        let (w, h, nc) = (st.f@.w as int, st.f@.h as int, st.f@.nc as int);
        assert(w * h * nc <= 3 * (w * h)) by (nonlinear_arith)
            requires
                w >= 0,
                h >= 0,
                nc <= 3,
        ;
        assert(npx(st.f@) == w * h);
    }
    let mut px = match alloc_u8(total) {
        Some(v) => v,
        None => {
            return Err(Error::OutOfMemory);
        },
    };
    match render_to(st, px.as_mut_slice(), Tracked(mt)) {
        Ok(()) => Ok(Picture { w: st.f.w as u32, h: st.f.h as u32, nc: st.f.nc, px }),
        Err(e) => Err(e),
    }
}

/// Decodes a JPEG file: the image the specification gives it, or
/// `Invalid` when the specification gives it none.
pub fn decode(data: &[u8]) -> (r: Result<Picture, Error>)
    ensures
        match r {
            Ok(pic) => jpeg_decode(data@) == Some(pic@),
            Err(Error::Invalid) => jpeg_decode(data@) is None,
            Err(Error::OutOfMemory) => true,
        },
{
    decode_counted(data).0
}

/// `decode`, counting its steps: at most `jpeg_work(n, s, b, px)` for an
/// `n`-byte file with `s` scans (at most `n + 65552`) whose frame is
/// stored in `b` blocks and has `px` pixels (`b` and `px` are 0 when the
/// file has no frame). The ghost result is `(steps, s, b, px)`.
pub fn decode_counted(data: &[u8]) -> (r: (Result<Picture, Error>, Ghost<(nat, nat, int, int)>))
    ensures
        match r.0 {
            Ok(pic) => jpeg_decode(data@) == Some(pic@),
            Err(Error::Invalid) => jpeg_decode(data@) is None,
            Err(Error::OutOfMemory) => true,
        },
        r.1@.0 <= jpeg_work(data@.len() as int, r.1@.1 as int, r.1@.2, r.1@.3),
        r.1@.1 <= data@.len() + 0x1_0010,
        r.0 matches Ok(pic) ==> r.1@.3 == pic.w * pic.h,
{
    let tracked mut mt = Meter { n: 0 };
    let (c, Ghost(g)) = decode_coefs(data, Tracked(&mut mt));
    match c {
        Ok(st) => {
            let ghost px = npx(st.f@);
            proof {
                assert(px >= 0) by (nonlinear_arith)
                    requires
                        px == st.f@.w * st.f@.h,
                ;
            }
            let r = render_x(&st, Tracked(&mut mt));
            (r, Ghost((mt.n, g.0, g.1, px)))
        },
        Err(e) => {
            proof {
                assert(render_cost_of(g.1, 0) >= 0);
            }
            (Err(e), Ghost((mt.n, g.0, g.1, 0)))
        },
    }
}

/// `decode` into a buffer the caller has: the picture's bytes go to `out`
/// and its width, height and bytes per pixel are returned. `Ok(None)`
/// means `out` is not the picture's size; nothing is written then.
pub fn decode_to(data: &[u8], out: &mut [u8]) -> (r: Result<Option<(u32, u32, u8)>, Error>)
    ensures
        final(out)@.len() == old(out)@.len(),
        match r {
            Ok(Some(d)) => jpeg_decode(data@) == Some(
                Image { w: d.0 as int, h: d.1 as int, nc: d.2 as int, px: final(out)@ },
            ),
            Ok(None) => final(out)@ == old(out)@ && jpeg_decode(data@) is Some && jpeg_decode(data@).unwrap().px.len()
                != old(out)@.len(),
            Err(Error::Invalid) => jpeg_decode(data@) is None,
            Err(Error::OutOfMemory) => true,
        },
{
    let tracked mut mt = Meter { n: 0 };
    match decode_coefs(data, Tracked(&mut mt)).0 {
        Ok(st) => {
            let total = match pic_len(&st) {
                Some(n) => n,
                None => {
                    return Err(Error::OutOfMemory);
                },
            };
            if out.len() != total {
                return Ok(None);
            }
            match render_to(&st, out, Tracked(&mut mt)) {
                Ok(()) => Ok(Some((st.f.w as u32, st.f.h as u32, st.f.nc))),
                Err(e) => Err(e),
            }
        },
        Err(e) => Err(e),
    }
}

} // verus!
