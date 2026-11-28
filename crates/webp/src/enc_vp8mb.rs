//! The lossy encoder's pass over the macroblocks: it chooses each one's
//! modes and levels and reconstructs it exactly as the decoder will (with
//! the decoder's own `reconstruct_mb`), so later predictions see what the
//! decoder sees.
use crate::enc_vp8a::*;
#[cfg(verus_only)]
use crate::enc_vp8tame::*;
#[cfg(verus_only)]
use crate::enc_vp8tok::*;
#[cfg(verus_only)]
use crate::enc_vp8w::{blk_lv, mb_lvs};
#[cfg(verus_only)]
use crate::vp8spec::*;
#[cfg(verus_only)]
use crate::vp8parse::c16;
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
        lv_dq(blk_lv(final(lv)@, b as int), first as int, zdc.q as int, zac.q as int, 2047),
        forall|i: int| 0 <= i < 400 && !(16 * b + first <= i < 16 * b + 16) ==> final(lv)@[i] == old(lv)@[i],
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
            forall|k: int| first <= k < n ==> -2047 <= #[trigger] blk_lv(lv@, b as int)[k] * dq_at(k, zdc.q as int, zac.q as int) <= 2047,
            forall|i: int| 0 <= i < 400 && !(16 * b + first <= i < 16 * b + n) ==> lv@[i] == old(lv)@[i],
        decreases 16 - n,
    {
        let j = ZIGZAG[n] as usize;
        let z = if n == 0 {
            zdc
        } else {
            zac
        };
        let (l, d) = quant(c[16 * b + j], z, Ghost(2047));
        let ghost l0 = lv@;
        lv.set(16 * b + n, l);
        proof {
            assert forall|k: int| first <= k < n + 1 implies -2047 <= #[trigger] blk_lv(lv@, b as int)[k] * dq_at(k, zdc.q as int, zac.q as int) <= 2047 by {
                if k < n {
                    assert(blk_lv(lv@, b as int)[k] == blk_lv(l0, b as int)[k]);
                } else {
                    assert(blk_lv(lv@, b as int)[k] == l as int);
                    assert(z.q == (if k > 0 { zac.q } else { zdc.q }));
                }
            }
        }
        co.set(16 * b + j, d);
        if l != 0 {
            nz = n + 1;
        }
        n = n + 1;
    }
    nz
}

/// The inverse of `zigzag`: the stream position of raster place `i`.
pub open spec fn unzz(i: int) -> int {
    seq![0int, 1, 5, 6, 2, 4, 7, 12, 3, 8, 11, 13, 9, 10, 14, 15][i]
}

proof fn lemma_unzz()
    ensures
        forall|k: int| 0 <= k < 16 ==> 0 <= #[trigger] zigzag(k) < 16 && unzz(zigzag(k)) == k,
        forall|i: int| 0 <= i < 16 ==> 0 <= #[trigger] unzz(i) < 16 && zigzag(unzz(i)) == i,
{
    let z = seq![0int, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15];
    let u = seq![0int, 1, 5, 6, 2, 4, 7, 12, 3, 8, 11, 13, 9, 10, 14, 15];
    assert(z[0] == 0 && z[1] == 1 && z[2] == 4 && z[3] == 8 && z[4] == 5 && z[5] == 2 && z[6] == 3 && z[7] == 6);
    assert(z[8] == 9 && z[9] == 12 && z[10] == 13 && z[11] == 10 && z[12] == 7 && z[13] == 11 && z[14] == 14 && z[15] == 15);
    assert(u[0] == 0 && u[1] == 1 && u[2] == 5 && u[3] == 6 && u[4] == 2 && u[5] == 4 && u[6] == 7 && u[7] == 12);
    assert(u[8] == 3 && u[9] == 8 && u[10] == 11 && u[11] == 13 && u[12] == 9 && u[13] == 10 && u[14] == 14 && u[15] == 15);
}

/// `tok_out` from position `n` sets each later place to its level times
/// its factor (a zero level leaves the zero there).
proof fn lemma_tok_out_form(out: Seq<int>, lv: Seq<int>, n: int, ce: bool, dc: int, ac: int)
    requires
        out.len() == 16,
        0 <= n <= 16,
        lv.len() == 16,
        forall|k: int| n <= k < 16 ==> out[#[trigger] zigzag(k)] == 0,
        lv_dq(lv, n, dc, ac, 0x7fff),
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] tok_out(out, lv, n, ce, dc, ac)[zigzag(k)] == if k >= n {
            lv[k] * dq_at(k, dc, ac)
        } else {
            out[zigzag(k)]
        },
    decreases 16 - n,
{
    lemma_unzz();
    if n >= 16 {
    } else if ce && rest_zero(lv, n) {
        assert forall|k: int| 0 <= k < 16 && k >= n implies lv[k] * dq_at(k, dc, ac) == out[zigzag(k)] by {
            assert(lv[k] == 0);
        }
    } else {
        let d = dq_at(n, dc, ac);
        assert(d == (if n > 0 {
            ac
        } else {
            dc
        }));
        assert(-0x7fff <= lv[n] * d <= 0x7fff);
        lemma_wrap_id(lv[n] * d);
        let o1 = if lv[n] == 0 {
            out
        } else {
            out.update(zigzag(n), wrap16s(lv[n] * d))
        };
        assert forall|k: int| n + 1 <= k < 16 implies o1[#[trigger] zigzag(k)] == 0 by {
            assert(unzz(zigzag(k)) == k);
            assert(zigzag(k) != zigzag(n));
        }
        assert(lv_dq(lv, n + 1, dc, ac, 0x7fff));
        lemma_tok_out_form(o1, lv, n + 1, lv[n] != 0, dc, ac);
        assert(tok_out(out, lv, n, ce, dc, ac) == tok_out(o1, lv, n + 1, lv[n] != 0, dc, ac));
        assert forall|k: int| 0 <= k < 16 implies #[trigger] tok_out(out, lv, n, ce, dc, ac)[zigzag(k)] == if k >= n {
            lv[k] * dq_at(k, dc, ac)
        } else {
            out[zigzag(k)]
        } by {
            if k != n {
                assert(unzz(zigzag(k)) == k);
                assert(zigzag(k) != zigzag(n));
                assert(o1[zigzag(k)] == out[zigzag(k)]);
            } else if lv[n] == 0 {
                assert(lv[k] * dq_at(k, dc, ac) == 0);
            }
        }
    }
}

/// Quantizes the Y2 block and computes, as the decoder will, the luma
/// DCs it gives (into `co`). True if they all stay within 2047.
fn quant_y2(y2: &[i32; 16], zd: Qz, za: Qz, lv: &mut Vec<i16>, co: &mut Vec<i16>, Ghost(cap): Ghost<int>) -> (ok: bool)
    requires
        old(lv)@.len() == 400,
        old(co)@.len() == 384,
        lv_ok16(old(lv)@),
        qz_ok(zd, cap),
        qz_ok(za, cap),
        0 <= cap <= 16383,
        forall|k: int| 0 <= k < 16 ==> -32768 <= #[trigger] y2@[k] <= 32768,
    ensures
        final(lv)@.len() == 400,
        final(co)@.len() == 384,
        lv_ok16(final(lv)@),
        forall|i: int| 0 <= i < 384 ==> final(lv)@[i] == old(lv)@[i],
        ok ==> within(y2_dcs(blk_lv(final(lv)@, 24), zd.q as int, za.q as int), 2047),
{
    let mut y2q = [0i16; 16];
    let ghost l0 = lv@;
    let mut n: usize = 0;
    while n < 16
        invariant
            n <= 16,
            lv@.len() == 400,
            lv_ok16(lv@),
            qz_ok(zd, cap),
            qz_ok(za, cap),
            0 <= cap <= 16383,
            forall|k: int| 0 <= k < 16 ==> -32768 <= #[trigger] y2@[k] <= 32768,
            forall|i: int| 0 <= i < 384 ==> lv@[i] == l0[i],
            forall|k: int| 0 <= k < n ==> #[trigger] y2q@[zigzag(k)] as int == lv@[384 + k] * dq_at(k, zd.q as int, za.q as int),
            forall|k: int| 0 <= k < n ==> -16383 <= #[trigger] (lv@[384 + k] * dq_at(k, zd.q as int, za.q as int)) <= 16383,
            forall|k: int| n <= k < 16 ==> #[trigger] y2q@[zigzag(k)] == 0,
        decreases 16 - n,
    {
        proof {
            lemma_unzz();
        }
        let j = ZIGZAG[n] as usize;
        proof {
            assert(j as int == zigzag(n as int));
        }
        let z = if n == 0 {
            zd
        } else {
            za
        };
        let (l, d) = quant(y2[j], z, Ghost(cap));
        let ghost q0 = y2q@;
        lv.set(384 + n, l);
        y2q[j] = d;
        proof {
            assert(z.q == (if n > 0 { za.q } else { zd.q }));
            assert forall|k: int| 0 <= k < 16 && k != n implies #[trigger] y2q@[zigzag(k)] == q0[zigzag(k)] by {
                assert(unzz(zigzag(k)) == k);
            }
        }
        n = n + 1;
    }
    let ghost l = blk_lv(lv@, 24);
    proof {
        lemma_unzz();
        assert(lv_dq(l, 0, zd.q as int, za.q as int, 0x7fff)) by {
            assert forall|k: int| 0 <= k < 16 implies -0x7fff <= #[trigger] l[k] * dq_at(k, zd.q as int, za.q as int) <= 0x7fff by {
                assert(l[k] == lv@[384 + k]);
            }
        }
        let zs = Seq::new(16, |i: int| 0int);
        lemma_tok_out_form(zs, l, 0, true, zd.q as int, za.q as int);
        let t = tok_out(zs, l, 0, true, zd.q as int, za.q as int);
        crate::enc_vp8tame::lemma_tok_out_len(zs, l, 0, true, zd.q as int, za.q as int);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] c16(y2q@)[i] == t[i] by {
            let k = unzz(i);
            assert(zigzag(k) == i);
            assert(t[zigzag(k)] == l[k] * dq_at(k, zd.q as int, za.q as int));
            assert(l[k] == lv@[384 + k]);
        }
        assert(c16(y2q@) =~= t);
    }
    transform_wht(&y2q, co.as_mut_slice());
    let mut ok = true;
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            co@.len() == 384,
            forall|i: int| 0 <= i < 16 ==> #[trigger] co@[16 * i] == iwht(c16(y2q@))[i],
            ok ==> forall|i: int| 0 <= i < k ==> -2047 <= #[trigger] iwht(c16(y2q@))[i] <= 2047,
        decreases 16 - k,
    {
        let x = co[16 * k];
        if x > 2047 || x < -2047 {
            ok = false;
        }
        k = k + 1;
    }
    proof {
        assert(iwht(c16(y2q@)) == y2_dcs(l, zd.q as int, za.q as int));
    }
    ok
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

pub open spec fn choice_shape(c: &MbChoice) -> bool {
    &&& c.ymode < 4
    &&& c.uvmode < 4
    &&& c.lv@.len() == 400
    &&& lv_ok16(c.lv@)
}

pub open spec fn choice_ok(c: &MbChoice, q: (int, int, int, int, int, int)) -> bool {
    &&& choice_shape(c)
    &&& mb_lv_ok(mb_lvs(c.lv@), q)
}

/// The dequantization factors of `qs`, as `seg_quant` lists them.
pub open spec fn qtuple(qs: Quants) -> (int, int, int, int, int, int) {
    (qs.y1dc.q as int, qs.y1ac.q as int, qs.y2dc.q as int, qs.y2ac.q as int, qs.uvdc.q as int, qs.uvac.q as int)
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
        r matches Some(c) ==> choice_ok(&c, qtuple(qs)),
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
    // that every block's inverse DCT fits in 16 bits). In the rare case
    // that rounding pushes one past it, Y2 is quantized again more
    // coarsely, and failing that, dropped.
    let mut ok = quant_y2(&y2, qs.y2dc, qs.y2ac, &mut lv, &mut co, Ghost(16383));
    if !ok {
        ok = quant_y2(&y2, qz(qs.y2dc.q, 96, 1023), qz(qs.y2ac.q, 108, 1023), &mut lv, &mut co, Ghost(1023));
    }
    if !ok {
        ok = quant_y2(&y2, qz(qs.y2dc.q, 96, 0), qz(qs.y2ac.q, 108, 0), &mut lv, &mut co, Ghost(0));
    }
    if !ok {
        return None;
    }
    let ghost l24 = blk_lv(lv@, 24);
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
            blk_lv(lv@, 24) == l24,
            forall|b: int| 0 <= b < k ==> lv_dq(#[trigger] blk_lv(lv@, b), 1, qs.y1dc.q as int, qs.y1ac.q as int, 2047),
        decreases 16 - k,
    {
        let ghost l0 = lv@;
        let nz = quant_block(c.as_slice(), k, 1, qs.y1dc, qs.y1ac, &mut lv, &mut co);
        proof {
            assert(blk_lv(lv@, 24) =~= blk_lv(l0, 24));
            assert forall|b: int| 0 <= b < k implies lv_dq(#[trigger] blk_lv(lv@, b), 1, qs.y1dc.q as int, qs.y1ac.q as int, 2047) by {
                assert(blk_lv(lv@, b) =~= blk_lv(l0, b));
            }
        }
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
            blk_lv(lv@, 24) == l24,
            forall|b: int| 0 <= b < 16 ==> lv_dq(#[trigger] blk_lv(lv@, b), 1, qs.y1dc.q as int, qs.y1ac.q as int, 2047),
            forall|b: int| 16 <= b < k ==> lv_dq(#[trigger] blk_lv(lv@, b), 0, qs.uvdc.q as int, qs.uvac.q as int, 2047),
        decreases 24 - k,
    {
        let ghost l0 = lv@;
        let nz = quant_block(c.as_slice(), k, 0, qs.uvdc, qs.uvac, &mut lv, &mut co);
        proof {
            assert(blk_lv(lv@, 24) =~= blk_lv(l0, 24));
            assert forall|b: int| 0 <= b < 16 implies lv_dq(#[trigger] blk_lv(lv@, b), 1, qs.y1dc.q as int, qs.y1ac.q as int, 2047) by {
                assert(blk_lv(lv@, b) =~= blk_lv(l0, b));
            }
            assert forall|b: int| 16 <= b < k implies lv_dq(#[trigger] blk_lv(lv@, b), 0, qs.uvdc.q as int, qs.uvac.q as int, 2047) by {
                assert(blk_lv(lv@, b) =~= blk_lv(l0, b));
            }
        }
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
    proof {
        let ls = mb_lvs(lv@);
        assert forall|b: int| 0 <= b < 25 implies #[trigger] ls[b] == blk_lv(lv@, b) by {}
        assert(ls[24] == l24);
    }
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
