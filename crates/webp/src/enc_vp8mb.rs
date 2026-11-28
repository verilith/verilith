//! The lossy encoder's pass over the macroblocks: it chooses each one's
//! modes and levels and reconstructs it exactly as the decoder will (with
//! the decoder's own `reconstruct_mb`), so later predictions see what the
//! decoder sees.
use crate::enc_vp8a::*;
use crate::vp8dsp::{pred_block, BPS};
use crate::vp8frame::*;
use crate::vp8parse::{transform_wht, MbModes, Residuals};
use crate::vp8tables::*;
use verilith_core::prims::*;
use vstd::prelude::*;

verus! {

/// The quantizers of a frame.
#[derive(Clone, Copy)]
pub struct Quants {
    pub y1dc: Qz,
    pub y1ac: Qz,
    pub y2dc: Qz,
    pub y2ac: Qz,
    pub uvdc: Qz,
    pub uvac: Qz,
}

pub open spec fn quants_ok(q: Quants) -> bool {
    &&& qz_ok(q.y1dc, 2047)
    &&& qz_ok(q.y1ac, 2047)
    &&& qz_ok(q.y2dc, 16383)
    &&& qz_ok(q.y2ac, 16383)
    &&& qz_ok(q.uvdc, 2047)
    &&& qz_ok(q.uvac, 2047)
}

/// The quantizers for index `qi`, as `seg_quant` gives them, with
/// libwebp's rounding biases.
pub fn quants(qi: usize) -> (r: Quants)
    requires
        qi < 128,
    ensures
        quants_ok(r),
        r.y1dc.q == spec_dc_table(qi as int),
        r.y1ac.q == spec_ac_table(qi as int),
        r.y2dc.q == spec_dc_table(qi as int) * 2,
        r.y2ac.q == (if spec_ac_table(qi as int) * 101581 / 65536 < 8 {
            8
        } else {
            spec_ac_table(qi as int) * 101581 / 65536
        }),
        r.uvdc.q == spec_dc_table(if qi > 117 {
            117
        } else {
            qi as int
        }),
        r.uvac.q == spec_ac_table(qi as int),
{
    let dc = dc_table(qi) as u32;
    let ac = ac_table(qi) as u32;
    let y2a = ac * 101581 / 65536;
    let y2ac = if y2a < 8 {
        8
    } else {
        y2a
    };
    let uq = if qi > 117 {
        117
    } else {
        qi
    };
    let uvdc = dc_table(uq) as u32;
    Quants {
        y1dc: qz(dc, 96, 2047),
        y1ac: qz(ac, 110, 2047),
        y2dc: qz(dc * 2, 96, 16383),
        y2ac: qz(y2ac, 108, 16383),
        uvdc: qz(uvdc, 110, 2047),
        uvac: qz(ac, 115, 2047),
    }
}

pub open spec fn lv_ok16(lv: Seq<i16>) -> bool {
    forall|i: int| 0 <= i < lv.len() ==> -2047 <= #[trigger] lv[i] <= 2047
}

/// Quantizes block `b` (coefficients `c[16 b..]` in raster order) from
/// zigzag position `first`: its levels into `lv[16 b..]` in zigzag order,
/// its coefficients into `co[16 b..]` in raster order. Returns where its
/// tokens end: one past the last nonzero level, or `first`.
fn quant_block(c: &[i32], b: usize, first: usize, zdc: Qz, zac: Qz, lv: &mut Vec<i16>, co: &mut Vec<i16>) -> (nz: usize)
    requires
        c@.len() >= 16 * b + 16,
        old(lv)@.len() == 400,
        old(co)@.len() == 384,
        b < 24,
        first <= 1,
        qz_ok(zdc, 2047),
        qz_ok(zac, 2047),
        lv_ok16(old(lv)@),
        forall|i: int| 0 <= i < c@.len() ==> -32768 <= #[trigger] c@[i] <= 32768,
    ensures
        final(lv)@.len() == 400,
        final(co)@.len() == 384,
        lv_ok16(final(lv)@),
        nz <= 16,
{
    let mut nz = first;
    let mut n = first;
    while n < 16
        invariant
            c@.len() >= 16 * b + 16,
            lv@.len() == 400,
            co@.len() == 384,
            b < 24,
            first <= n <= 16,
            nz <= n,
            qz_ok(zdc, 2047),
            qz_ok(zac, 2047),
            lv_ok16(lv@),
            forall|i: int| 0 <= i < c@.len() ==> -32768 <= #[trigger] c@[i] <= 32768,
        decreases 16 - n,
    {
        let j = ZIGZAG[n] as usize;
        let z = if n == 0 {
            zdc
        } else {
            zac
        };
        let (l, d) = quant(c[16 * b + j], z, Ghost(2047));
        lv.set(16 * b + n, l);
        co.set(16 * b + j, d);
        if l != 0 {
            nz = n + 1;
        }
        n = n + 1;
    }
    nz
}

/// The selector `nz_code` for a block whose tokens end at `nz`.
fn code(nz: usize, dc_nz: bool) -> (r: u32)
    ensures
        r <= 3,
{
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

/// Copies the source macroblock at `(mb_x, mb_y)` into `s`, at the places
/// the scratch block holds it.
fn load_src(s: &mut [u8], src: &Planes, mb_x: usize, mb_y: usize, mb_w: usize, mb_h: usize)
    requires
        old(s)@.len() == YUV_SIZE,
        src.mb_shape(mb_w as nat, mb_h as nat),
        mb_x < mb_w,
        mb_y < mb_h,
    ensures
        final(s)@.len() == YUV_SIZE,
{
    let mut j: usize = 0;
    while j < 16
        invariant
            j <= 16,
            s@.len() == YUV_SIZE,
            src.mb_shape(mb_w as nat, mb_h as nat),
            mb_x < mb_w,
            mb_y < mb_h,
        decreases 16 - j,
    {
        proof {
            lemma_row(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 16, j as int);
        }
        copy_n(s, Y_OFF + j * BPS, src.y.as_slice(), (16 * mb_y + j) * (16 * mb_w) + 16 * mb_x, 16);
        j = j + 1;
    }
    let mut j: usize = 0;
    while j < 8
        invariant
            j <= 8,
            s@.len() == YUV_SIZE,
            src.mb_shape(mb_w as nat, mb_h as nat),
            mb_x < mb_w,
            mb_y < mb_h,
        decreases 8 - j,
    {
        proof {
            lemma_row(mb_x as int, mb_y as int, mb_w as int, mb_h as int, 8, j as int);
        }
        copy_n(s, U_OFF + j * BPS, src.u.as_slice(), (8 * mb_y + j) * (8 * mb_w) + 8 * mb_x, 8);
        copy_n(s, V_OFF + j * BPS, src.v.as_slice(), (8 * mb_y + j) * (8 * mb_w) + 8 * mb_x, 8);
        j = j + 1;
    }
}

/// One macroblock's choices.
pub struct MbChoice {
    pub ymode: u8,
    pub uvmode: u8,
    pub skip: bool,
    /// 25 blocks of 16 levels in zigzag order: luma, U, V, Y2.
    pub lv: Vec<i16>,
}

pub open spec fn choice_ok(c: &MbChoice) -> bool {
    &&& c.ymode < 4
    &&& c.uvmode < 4
    &&& c.lv@.len() == 400
    &&& lv_ok16(c.lv@)
}

/// The luma or chroma mode with the least squared error, with the block
/// left predicted by it.
fn best_mode(t: &mut [u8], s: &[u8], mb_x: usize, mb_y: usize, luma: bool) -> (m: u8)
    requires
        old(t)@.len() == YUV_SIZE,
        s@.len() == YUV_SIZE,
    ensures
        final(t)@.len() == YUV_SIZE,
        m < 4,
{
    let mut best: u8 = 0;
    let mut be: u32 = u32::MAX;
    let mut m: u8 = 0;
    while m < 4
        invariant
            m <= 4,
            best < 4,
            t@.len() == YUV_SIZE,
            s@.len() == YUV_SIZE,
        decreases 4 - m,
    {
        let e = if luma {
            pred_block(t, Y_OFF, 16, check_mode(mb_x, mb_y, m));
            sse(s, t, Y_OFF, 16)
        } else {
            pred_block(t, U_OFF, 8, check_mode(mb_x, mb_y, m));
            pred_block(t, V_OFF, 8, check_mode(mb_x, mb_y, m));
            sse(s, t, U_OFF, 8) + sse(s, t, V_OFF, 8)
        };
        if e < be {
            be = e;
            best = m;
        }
        m = m + 1;
    }
    if luma {
        pred_block(t, Y_OFF, 16, check_mode(mb_x, mb_y, best));
    } else {
        pred_block(t, U_OFF, 8, check_mode(mb_x, mb_y, best));
        pred_block(t, V_OFF, 8, check_mode(mb_x, mb_y, best));
    }
    best
}

/// Chooses macroblock `(mb_x, mb_y)`'s modes and levels, and reconstructs
/// it in `ws` as the decoder will.
pub fn encode_mb(
    ws: &mut Vec<u8>,
    top_y: &Vec<u8>,
    top_u: &Vec<u8>,
    top_v: &Vec<u8>,
    src: &Planes,
    mb_x: usize,
    mb_y: usize,
    mb_w: usize,
    mb_h: usize,
    qs: Quants,
) -> (r: Option<MbChoice>)
    requires
        old(ws)@.len() == YUV_SIZE,
        top_y@.len() == 16 * mb_w,
        top_u@.len() == 8 * mb_w,
        top_v@.len() == 8 * mb_w,
        src.mb_shape(mb_w as nat, mb_h as nat),
        mb_x < mb_w,
        mb_y < mb_h,
        quants_ok(qs),
    ensures
        final(ws)@.len() == YUV_SIZE,
        r matches Some(c) ==> choice_ok(&c),
{
    // The scratch block as `reconstruct_mb` will set it up, to predict from.
    let mut t = ws.clone();
    proof {
        assert(t@.len() == YUV_SIZE);
    }
    if mb_x > 0 {
        rotate_left(t.as_mut_slice());
    }
    if mb_y > 0 {
        copy_n(t.as_mut_slice(), Y_OFF - BPS, top_y.as_slice(), 16 * mb_x, 16);
        copy_n(t.as_mut_slice(), U_OFF - BPS, top_u.as_slice(), 8 * mb_x, 8);
        copy_n(t.as_mut_slice(), V_OFF - BPS, top_v.as_slice(), 8 * mb_x, 8);
    }
    let mut s = match alloc_u8(YUV_SIZE) {
        Some(v) => v,
        None => return None,
    };
    load_src(s.as_mut_slice(), src, mb_x, mb_y, mb_w, mb_h);
    let ymode = best_mode(t.as_mut_slice(), s.as_slice(), mb_x, mb_y, true);
    let uvmode = best_mode(t.as_mut_slice(), s.as_slice(), mb_x, mb_y, false);
    // Forward transforms: sixteen luma blocks, then four U and four V.
    let mut c: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < 384
        invariant
            i <= 384,
            c@.len() == i,
            forall|k: int| 0 <= k < c@.len() ==> -32768 <= #[trigger] c@[k] <= 32768,
        decreases 384 - i,
    {
        c.push(0);
        i = i + 1;
    }
    let mut k: usize = 0;
    while k < 24
        invariant
            k <= 24,
            c@.len() == 384,
            t@.len() == YUV_SIZE,
            s@.len() == YUV_SIZE,
            forall|i: int| 0 <= i < c@.len() ==> -32768 <= #[trigger] c@[i] <= 32768,
        decreases 24 - k,
    {
        let d = if k < 16 {
            Y_OFF + 4 * (k % 4) + 4 * BPS * (k / 4)
        } else if k < 20 {
            U_OFF + 4 * ((k - 16) % 2) + 4 * BPS * ((k - 16) / 2)
        } else {
            V_OFF + 4 * ((k - 20) % 2) + 4 * BPS * ((k - 20) / 2)
        };
        let ghost c0 = c@;
        fdct(s.as_slice(), t.as_slice(), d, c.as_mut_slice(), 16 * k);
        proof {
            assert forall|i: int| 0 <= i < c@.len() implies -32768 <= #[trigger] c@[i] <= 32768 by {
                if !(16 * k <= i < 16 * k + 16) {
                    assert(c@[i] == c0[i]);
                }
            }
        }
        k = k + 1;
    }
    let mut lv = match alloc_i16(400) {
        Some(v) => v,
        None => return None,
    };
    let mut co = match alloc_i16(384) {
        Some(v) => v,
        None => return None,
    };
    // Y2: the transform of the luma DCs.
    let mut dc = [0i32; 16];
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            c@.len() == 384,
            forall|i: int| 0 <= i < c@.len() ==> -32768 <= #[trigger] c@[i] <= 32768,
            forall|i: int| 0 <= i < 16 ==> -4096 <= #[trigger] dc@[i] <= 4096,
        decreases 16 - k,
    {
        let x = c[16 * k];
        dc[k] = if x < -4096 {
            -4096
        } else if x > 4096 {
            4096
        } else {
            x
        };
        k = k + 1;
    }
    let y2 = fwht(&dc);
    // The luma DCs the decoder will compute must stay within 2047 (so
    // that every block's inverse DCT fits in 16 bits); in the rare case
    // that rounding pushes one past it, Y2 is quantized again within a
    // bound that guarantees it.
    let mut pass: usize = 0;
    while pass < 2
        invariant
            pass <= 2,
            lv@.len() == 400,
            co@.len() == 384,
            lv_ok16(lv@),
            quants_ok(qs),
            forall|k: int| 0 <= k < 16 ==> -32768 <= #[trigger] y2@[k] <= 32768,
        decreases 2 - pass,
    {
        let (zd, za) = if pass == 0 {
            (qs.y2dc, qs.y2ac)
        } else {
            (qz(qs.y2dc.q, 96, 1023), qz(qs.y2ac.q, 108, 1023))
        };
        let ghost cap: int = if pass == 0 {
            16383
        } else {
            1023
        };
        let mut y2q = [0i16; 16];
        let mut n: usize = 0;
        while n < 16
            invariant
                n <= 16,
                lv@.len() == 400,
                lv_ok16(lv@),
                qz_ok(zd, cap),
                qz_ok(za, cap),
                cap <= 16383,
                forall|k: int| 0 <= k < 16 ==> -32768 <= #[trigger] y2@[k] <= 32768,
            decreases 16 - n,
        {
            let j = ZIGZAG[n] as usize;
            let z = if n == 0 {
                zd
            } else {
                za
            };
            let (l, d) = quant(y2[j], z, Ghost(cap));
            lv.set(384 + n, l);
            y2q[j] = d;
            n = n + 1;
        }
        transform_wht(&y2q, co.as_mut_slice());
        let mut big = false;
        let mut k: usize = 0;
        while k < 16
            invariant
                k <= 16,
                co@.len() == 384,
            decreases 16 - k,
        {
            let x = co[16 * k];
            if x > 2047 || x < -2047 {
                big = true;
            }
            k = k + 1;
        }
        pass = if big {
            pass + 1
        } else {
            2
        };
    }
    // The luma blocks from position 1, then chroma.
    let mut nzy: u32 = 0;
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            c@.len() == 384,
            lv@.len() == 400,
            co@.len() == 384,
            lv_ok16(lv@),
            quants_ok(qs),
            forall|i: int| 0 <= i < c@.len() ==> -32768 <= #[trigger] c@[i] <= 32768,
        decreases 16 - k,
    {
        let nz = quant_block(c.as_slice(), k, 1, qs.y1dc, qs.y1ac, &mut lv, &mut co);
        let cd = code(nz, co[16 * k] != 0);
        nzy = (nzy << 2u32) | cd;
        k = k + 1;
    }
    let mut nzu: u32 = 0;
    let mut nzv: u32 = 0;
    let mut k: usize = 16;
    while k < 24
        invariant
            16 <= k <= 24,
            c@.len() == 384,
            lv@.len() == 400,
            co@.len() == 384,
            lv_ok16(lv@),
            quants_ok(qs),
            forall|i: int| 0 <= i < c@.len() ==> -32768 <= #[trigger] c@[i] <= 32768,
        decreases 24 - k,
    {
        let nz = quant_block(c.as_slice(), k, 0, qs.uvdc, qs.uvac, &mut lv, &mut co);
        let cd = code(nz, co[16 * k] != 0);
        if k < 20 {
            nzu = (nzu << 2u32) | cd;
        } else {
            nzv = (nzv << 2u32) | cd;
        }
        k = k + 1;
    }
    let mut any = false;
    let mut i: usize = 0;
    while i < 400
        invariant
            i <= 400,
            lv@.len() == 400,
        decreases 400 - i,
    {
        if lv[i] != 0 {
            any = true;
        }
        i = i + 1;
    }
    let skip = !any;
    let m = MbModes { segment: 0, skip, is_i4x4: false, imodes: [ymode, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], uvmode };
    let res = Residuals { non_zero_y: nzy, non_zero_uv: (nzu & 0xff) | ((nzv & 0xff) << 8u32) };
    reconstruct_mb(
        ws.as_mut_slice(),
        top_y,
        top_u,
        top_v,
        mb_x,
        mb_y,
        mb_w,
        &m,
        &res,
        co.as_slice(),
        Ghost(arbitrary()),
        Ghost(arbitrary()),
    );
    Some(MbChoice { ymode, uvmode, skip, lv })
}

} // verus!
