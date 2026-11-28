//! The lossy encoder: a VP8 key frame in a RIFF container. The frame
//! header, the modes and the coefficient tokens are written by the
//! writers of `enc_vp8w`, whose read-back is proven in `enc_vp8frm`.
use crate::enc_vp8l::push_le32;
use crate::enc_vp8mb::*;
use crate::enc_vp8st::*;
use crate::enc_vp8w::*;
use crate::vp8frame::*;
#[cfg(verus_only)]
use crate::enc_vp8hdr::*;
use crate::vp8tables::*;
use verilith_core::prims::*;
use vstd::prelude::*;

verus! {

proof fn lemma_bytes(p: u32)
    ensures
        (p >> 16u32) & 0xff <= 255,
        (p >> 8u32) & 0xff <= 255,
        p & 0xff <= 255,
{
    assert((p >> 16u32) & 0xff <= 255) by (bit_vector);
    assert((p >> 8u32) & 0xff <= 255) by (bit_vector);
    assert(p & 0xff <= 255) by (bit_vector);
}

fn rgb(p: u32) -> (r: (u32, u32, u32))
    ensures
        r.0 <= 255 && r.1 <= 255 && r.2 <= 255,
{
    proof {
        lemma_bytes(p);
    }
    ((p >> 16u32) & 0xff, (p >> 8u32) & 0xff, p & 0xff)
}

/// The pixel at `(x, y)`, or the nearest one inside the image.
fn px_at(px: &[u32], w: usize, h: usize, x: usize, y: usize) -> (r: (u32, u32, u32))
    requires
        px@.len() == w * h,
        1 <= w < 0x4000,
        1 <= h < 0x4000,
    ensures
        r.0 <= 255 && r.1 <= 255 && r.2 <= 255,
{
    let sx = if x < w {
        x
    } else {
        w - 1
    };
    let sy = if y < h {
        y
    } else {
        h - 1
    };
    proof {
        assert(w * h < 0x1000_0000) by (nonlinear_arith)
            requires
                w < 0x4000,
                h < 0x4000,
        ;
        assert(sy * w + sx < w * h) by (nonlinear_arith)
            requires
                sx < w,
                sy < h,
        ;
    }
    rgb(px[sy * w + sx])
}

/// The image as YUV 4:2:0 planes (libwebp's `VP8RGBToY`/`U`/`V`, chroma
/// from the average of each 2x2 block), padded to whole macroblocks by
/// repeating the last row and column.
fn to_planes(px: &[u32], w: usize, h: usize) -> (r: Option<Planes>)
    requires
        px@.len() == w * h,
        1 <= w < 0x4000,
        1 <= h < 0x4000,
    ensures
        r matches Some(pl) ==> pl.mb_shape(((w + 15) / 16) as nat, ((h + 15) / 16) as nat),
{
    let mb_w = (w + 15) / 16;
    let mb_h = (h + 15) / 16;
    let ys = 16 * mb_w;
    let us = 8 * mb_w;
    proof {
        assert(ys * (16 * mb_h) <= 16 * 1024 * 16 * 1024) by (nonlinear_arith)
            requires
                ys <= 16 * 1024,
                mb_h <= 1024,
        ;
        assert(us * (8 * mb_h) <= 8 * 1024 * 8 * 1024) by (nonlinear_arith)
            requires
                us <= 8 * 1024,
                mb_h <= 1024,
        ;
    }
    let mut y = match alloc_u8(ys * (16 * mb_h)) {
        Some(v) => v,
        None => return None,
    };
    let mut u = match alloc_u8(us * (8 * mb_h)) {
        Some(v) => v,
        None => return None,
    };
    let mut v = match alloc_u8(us * (8 * mb_h)) {
        Some(v) => v,
        None => return None,
    };
    let mut j: usize = 0;
    while j < 16 * mb_h
        invariant
            j <= 16 * mb_h,
            px@.len() == w * h,
            1 <= w < 0x4000,
            1 <= h < 0x4000,
            mb_w == (w + 15) / 16,
            mb_h == (h + 15) / 16,
            ys == 16 * mb_w,
            y@.len() == ys * (16 * mb_h),
            ys * (16 * mb_h) <= 16 * 1024 * 16 * 1024,
        decreases 16 * mb_h - j,
    {
        let mut i: usize = 0;
        while i < ys
            invariant
                i <= ys,
                j < 16 * mb_h,
                px@.len() == w * h,
                1 <= w < 0x4000,
                1 <= h < 0x4000,
                mb_w == (w + 15) / 16,
                mb_h == (h + 15) / 16,
                ys == 16 * mb_w,
                y@.len() == ys * (16 * mb_h),
                ys * (16 * mb_h) <= 16 * 1024 * 16 * 1024,
            decreases ys - i,
        {
            let (r, g, b) = px_at(px, w, h, i, j);
            let l = (16839 * r + 33059 * g + 6420 * b + 1081344) / 65536;
            proof {
                assert(j * ys + i < ys * (16 * mb_h)) by (nonlinear_arith)
                    requires
                        i < ys,
                        j < 16 * mb_h,
                ;
            }
            y.set(j * ys + i, l as u8);
            i = i + 1;
        }
        j = j + 1;
    }
    let mut j: usize = 0;
    while j < 8 * mb_h
        invariant
            j <= 8 * mb_h,
            px@.len() == w * h,
            1 <= w < 0x4000,
            1 <= h < 0x4000,
            mb_w == (w + 15) / 16,
            mb_h == (h + 15) / 16,
            us == 8 * mb_w,
            us * (8 * mb_h) <= 8 * 1024 * 8 * 1024,
            u@.len() == us * (8 * mb_h),
            v@.len() == us * (8 * mb_h),
        decreases 8 * mb_h - j,
    {
        let mut i: usize = 0;
        while i < us
            invariant
                i <= us,
                j < 8 * mb_h,
                px@.len() == w * h,
                1 <= w < 0x4000,
                1 <= h < 0x4000,
                mb_w == (w + 15) / 16,
                mb_h == (h + 15) / 16,
                us == 8 * mb_w,
                us * (8 * mb_h) <= 8 * 1024 * 8 * 1024,
                u@.len() == us * (8 * mb_h),
                v@.len() == us * (8 * mb_h),
            decreases us - i,
        {
            let (r0, g0, b0) = px_at(px, w, h, 2 * i, 2 * j);
            let (r1, g1, b1) = px_at(px, w, h, 2 * i + 1, 2 * j);
            let (r2, g2, b2) = px_at(px, w, h, 2 * i, 2 * j + 1);
            let (r3, g3, b3) = px_at(px, w, h, 2 * i + 1, 2 * j + 1);
            let r = r0 + r1 + r2 + r3;
            let g = g0 + g1 + g2 + g3;
            let b = b0 + b1 + b2 + b3;
            let cu = (28800 * b + 33685504 - 9719 * r - 19081 * g) / 262144;
            let cv = (28800 * r + 33685504 - 24116 * g - 4684 * b) / 262144;
            proof {
                assert(j * us + i < us * (8 * mb_h)) by (nonlinear_arith)
                    requires
                        i < us,
                        j < 8 * mb_h,
                ;
            }
            u.set(j * us + i, cu as u8);
            v.set(j * us + i, cv as u8);
            i = i + 1;
        }
        j = j + 1;
    }
    Some(Planes { width: w, height: h, y, u, v, y_stride: ys, uv_stride: us })
}

/// `quality` (0 to 100) as a quantizer index, as libwebp maps it with
/// no segments: `127 (1 - c^(1/3))` for the linearized quality `c`.
fn q_index(quality: u32) -> (r: usize)
    ensures
        r < 128,
{
    let t: [u8; 101] = [
        127, 103, 96, 92, 89, 86, 83, 81, 79, 77, 75, 73, 72, 70, 69, 68, 66, 65, 64, 63,
        62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 51, 50, 49, 48, 48, 47, 46, 45,
        45, 44, 43, 43, 42, 41, 41, 40, 40, 39, 38, 38, 37, 37, 36, 36, 35, 35, 34, 33,
        33, 32, 32, 31, 31, 30, 30, 29, 29, 28, 28, 28, 27, 27, 26, 26, 24, 23, 22, 21,
        19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
        0,
    ];

    let k = if quality > 100 {
        100
    } else {
        quality
    };
    let r = t[k as usize] as usize;
    if r > 127 {
        127
    } else {
        r
    }
}

pub struct Frame {
    pub mb_w: usize,
    pub mb_h: usize,
    pub mbs: Vec<MbChoice>,
}

/// Chooses every macroblock, in raster order, reconstructing each as the
/// decoder will. `recon` gets the reconstructed planes (before any loop
/// filter).
pub fn choose_mbs(src: &Planes, mb_w: usize, mb_h: usize, qs: Quants, recon: &mut Planes) -> (r: Option<Vec<MbChoice>>)
    requires
        src.mb_shape(mb_w as nat, mb_h as nat),
        old(recon).mb_shape(mb_w as nat, mb_h as nat),
        quants_ok(qs),
    ensures
        r matches Some(v) ==> v@.len() == mb_w * mb_h && forall|i: int| 0 <= i < v@.len() ==> choice_ok(&#[trigger] v@[i]),
{
    let mut ws = match alloc_u8(YUV_SIZE) {
        Some(v) => v,
        None => return None,
    };
    let mut top_y = match alloc_u8(16 * mb_w) {
        Some(v) => v,
        None => return None,
    };
    let mut top_u = match alloc_u8(8 * mb_w) {
        Some(v) => v,
        None => return None,
    };
    let mut top_v = match alloc_u8(8 * mb_w) {
        Some(v) => v,
        None => return None,
    };
    let mut out: Vec<MbChoice> = Vec::new();
    let mut mb_y: usize = 0;
    while mb_y < mb_h
        invariant
            mb_y <= mb_h,
            src.mb_shape(mb_w as nat, mb_h as nat),
            recon.mb_shape(mb_w as nat, mb_h as nat),
            quants_ok(qs),
            ws@.len() == YUV_SIZE,
            top_y@.len() == 16 * mb_w,
            top_u@.len() == 8 * mb_w,
            top_v@.len() == 8 * mb_w,
            out@.len() == mb_y * mb_w,
            forall|i: int| 0 <= i < out@.len() ==> choice_ok(&#[trigger] out@[i]),
        decreases mb_h - mb_y,
    {
        init_row(ws.as_mut_slice(), mb_y);
        let mut mb_x: usize = 0;
        while mb_x < mb_w
            invariant
                mb_x <= mb_w,
                mb_y < mb_h,
                src.mb_shape(mb_w as nat, mb_h as nat),
                recon.mb_shape(mb_w as nat, mb_h as nat),
                quants_ok(qs),
                ws@.len() == YUV_SIZE,
                top_y@.len() == 16 * mb_w,
                top_u@.len() == 8 * mb_w,
                top_v@.len() == 8 * mb_w,
                out@.len() == mb_y * mb_w + mb_x,
                forall|i: int| 0 <= i < out@.len() ==> choice_ok(&#[trigger] out@[i]),
            decreases mb_w - mb_x,
        {
            let c = match encode_mb(&mut ws, &top_y, &top_u, &top_v, src, mb_x, mb_y, mb_w, mb_h, qs) {
                Some(c) => c,
                None => return None,
            };
            emit_mb(ws.as_slice(), &mut top_y, &mut top_u, &mut top_v, recon, mb_x, mb_y, mb_w, mb_h);
            out.push(c);
            mb_x = mb_x + 1;
        }
        proof {
            assert(mb_y * mb_w + mb_w == (mb_y + 1) * mb_w) by (nonlinear_arith);
        }
        mb_y = mb_y + 1;
    }
    proof {
        assert(mb_h * mb_w == mb_w * mb_h) by (nonlinear_arith);
    }
    Some(out)
}

/// The bits each token probability codes, over the frame.
fn count_all(mbs: &Vec<MbChoice>, mb_w: usize, mb_h: usize, skip_on: bool) -> (r: Vec<u32>)
    requires
        1 <= mb_w <= 1024,
        1 <= mb_h <= 1024,
        mbs@.len() == mb_w * mb_h,
        forall|i: int| 0 <= i < mbs@.len() ==> choice_ok(&#[trigger] mbs@[i]),
    ensures
        r@.len() == 2112,
{
    let mut st: Vec<u32> = Vec::new();
    let mut k: usize = 0;
    while k < 2112
        invariant
            k <= 2112,
            st@.len() == k,
        decreases 2112 - k,
    {
        st.push(0);
        k = k + 1;
    }
    let mut tops: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < 9 * mb_w
        invariant
            mb_w <= 1024,
            k <= 9 * mb_w,
            tops@.len() == k,
        decreases 9 * mb_w - k,
    {
        tops.push(false);
        k = k + 1;
    }
    let mut mb_y: usize = 0;
    while mb_y < mb_h
        invariant
            mb_y <= mb_h,
            mbs@.len() == mb_w * mb_h,
            mb_w <= 1024,
            mb_h <= 1024,
            tops@.len() == 9 * mb_w,
            st@.len() == 2112,
            forall|i: int| 0 <= i < mbs@.len() ==> choice_ok(&#[trigger] mbs@[i]),
        decreases mb_h - mb_y,
    {
        let mut left: Vec<bool> = vec![false, false, false, false, false, false, false, false, false];
        let mut mb_x: usize = 0;
        while mb_x < mb_w
            invariant
                mb_x <= mb_w,
                mb_y < mb_h,
                mbs@.len() == mb_w * mb_h,
                mb_w <= 1024,
                mb_h <= 1024,
                tops@.len() == 9 * mb_w,
                left@.len() == 9,
                st@.len() == 2112,
                forall|i: int| 0 <= i < mbs@.len() ==> choice_ok(&#[trigger] mbs@[i]),
            decreases mb_w - mb_x,
        {
            proof {
                assert(mb_y * mb_w + mb_x < mb_w * mb_h) by (nonlinear_arith)
                    requires
                        mb_x < mb_w,
                        mb_y < mb_h,
                ;
                assert(mb_w * mb_h <= 1024 * 1024) by (nonlinear_arith)
                    requires
                        mb_w <= 1024,
                        mb_h <= 1024,
                ;
            }
            let c = &mbs[mb_y * mb_w + mb_x];
            let mut top: Vec<bool> = Vec::new();
            let mut k: usize = 0;
            while k < 9
                invariant
                    k <= 9,
                    top@.len() == k,
                    tops@.len() == 9 * mb_w,
                    mb_w <= 1024,
                    mb_x < mb_w,
                decreases 9 - k,
            {
                top.push(tops[9 * mb_x + k]);
                k = k + 1;
            }
            if skip_on && c.skip {
                let mut k: usize = 0;
                while k < 9
                    invariant
                        k <= 9,
                        top@.len() == 9,
                        left@.len() == 9,
                    decreases 9 - k,
                {
                    top.set(k, false);
                    left.set(k, false);
                    k = k + 1;
                }
            } else {
                count_mb(&mut st, c.lv.as_slice(), &mut top, &mut left);
            }
            let mut k: usize = 0;
            while k < 9
                invariant
                    k <= 9,
                    top@.len() == 9,
                    tops@.len() == 9 * mb_w,
                    mb_w <= 1024,
                    mb_x < mb_w,
                decreases 9 - k,
            {
                tops.set(9 * mb_x + k, top[k]);
                k = k + 1;
            }
            mb_x = mb_x + 1;
        }
        mb_y = mb_y + 1;
    }
    st
}

/// Writes the frame: the first partition (header and modes) and the one
/// token partition.
pub fn write_parts(mbs: &Vec<MbChoice>, mb_w: usize, mb_h: usize, qi: usize) -> (r: Option<(Vec<u8>, Vec<u8>)>)
    requires
        1 <= mb_w <= 1024,
        1 <= mb_h <= 1024,
        qi < 128,
        mbs@.len() == mb_w * mb_h,
        forall|i: int| 0 <= i < mbs@.len() ==> choice_ok(&#[trigger] mbs@[i]),
{
    let n = mbs.len();
    let mut nskip: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == mbs@.len(),
            nskip <= i,
        decreases n - i,
    {
        if mbs[i].skip {
            nskip = nskip + 1;
        }
        i = i + 1;
    }
    let skip_on = nskip > 0;
    proof {
        assert(n >= 1) by (nonlinear_arith)
            requires
                n == mb_w * mb_h,
                mb_w >= 1,
                mb_h >= 1,
        ;
        assert(n <= 1024 * 1024) by (nonlinear_arith)
            requires
                n == mb_w * mb_h,
                mb_w <= 1024,
                mb_h <= 1024,
        ;
    }
    let ps = 255 * (n - nskip) / n;
    let pskip: u32 = if ps < 1 {
        1
    } else if ps > 254 {
        254
    } else {
        ps as u32
    };
    let st = count_all(mbs, mb_w, mb_h, skip_on);
    let probs = best_probs(&st);
    let mut w1 = EncW::new();
    put_hdr(&mut w1, 0, qi as u32, probs.as_slice(), skip_on, pskip);
    let ghost fh = fh_of(hparams(0, qi as u32, probs@, skip_on, pskip));
    let psk: u8 = if skip_on {
        pskip as u8
    } else {
        0
    };
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == mbs@.len(),
            w1.inv(),
            pskip < 256,
            fh == fh_of(hparams(0, qi as u32, probs@, skip_on, pskip)),
            psk == (if skip_on { pskip } else { 0 }),
            forall|i: int| 0 <= i < mbs@.len() ==> choice_ok(&#[trigger] mbs@[i]),
        decreases n - i,
    {
        let c = &mbs[i];
        put_mbm(&mut w1, skip_on, psk, c.skip, c.ymode, c.uvmode, Ghost(fh));
        i = i + 1;
    }
    let mut w2 = EncW::new();
    let mut tops: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < 9 * mb_w
        invariant
            mb_w <= 1024,
            k <= 9 * mb_w,
            tops@.len() == k,
        decreases 9 * mb_w - k,
    {
        tops.push(false);
        k = k + 1;
    }
    let mut mb_y: usize = 0;
    while mb_y < mb_h
        invariant
            mb_y <= mb_h,
            n == mbs@.len(),
            n == mb_w * mb_h,
            tops@.len() == 9 * mb_w,
            mb_w <= 1024,
            probs@.len() == 1056,
            w2.inv(),
            forall|i: int| 0 <= i < mbs@.len() ==> choice_ok(&#[trigger] mbs@[i]),
        decreases mb_h - mb_y,
    {
        let mut left: Vec<bool> = vec![false, false, false, false, false, false, false, false, false];
        let mut mb_x: usize = 0;
        while mb_x < mb_w
            invariant
                mb_x <= mb_w,
                mb_y < mb_h,
                n == mbs@.len(),
                n == mb_w * mb_h,
                tops@.len() == 9 * mb_w,
                mb_w <= 1024,
                left@.len() == 9,
                probs@.len() == 1056,
                w2.inv(),
                forall|i: int| 0 <= i < mbs@.len() ==> choice_ok(&#[trigger] mbs@[i]),
            decreases mb_w - mb_x,
        {
            proof {
                assert(mb_y * mb_w + mb_x < mb_w * mb_h) by (nonlinear_arith)
                    requires
                        mb_x < mb_w,
                        mb_y < mb_h,
                ;
            }
            let c = &mbs[mb_y * mb_w + mb_x];
            let mut top: Vec<bool> = Vec::new();
            let mut k: usize = 0;
            while k < 9
                invariant
                    k <= 9,
                    top@.len() == k,
                    tops@.len() == 9 * mb_w,
                    mb_w <= 1024,
                    left@.len() == 9,
                    mb_x < mb_w,
                decreases 9 - k,
            {
                top.push(tops[9 * mb_x + k]);
                k = k + 1;
            }
            if skip_on && c.skip {
                let mut k: usize = 0;
                while k < 9
                    invariant
                        k <= 9,
                        top@.len() == 9,
                        left@.len() == 9,
                    decreases 9 - k,
                {
                    top.set(k, false);
                    left.set(k, false);
                    k = k + 1;
                }
            } else {
                put_mb(&mut w2, probs.as_slice(), c.lv.as_slice(), &mut top, &mut left, Ghost(arbitrary()));
            }
            let mut k: usize = 0;
            while k < 9
                invariant
                    k <= 9,
                    top@.len() == 9,
                    tops@.len() == 9 * mb_w,
                    left@.len() == 9,
                    mb_w <= 1024,
                    mb_x < mb_w,
                decreases 9 - k,
            {
                tops.set(9 * mb_x + k, top[k]);
                k = k + 1;
            }
            mb_x = mb_x + 1;
        }
        mb_y = mb_y + 1;
    }
    if !w1.ok || !w2.ok {
        return None;
    }
    Some((w1.bw.finish(), w2.bw.finish()))
}

/// Encodes `px` (`w` by `h`, ARGB, alpha ignored) as a lossy WebP file at
/// `quality` 0 to 100.
pub fn encode_lossy(px: &[u32], w: usize, h: usize, quality: u32) -> (r: Option<Vec<u8>>)
    requires
        px@.len() == w * h,
{
    if w < 1 || h < 1 || w >= 0x4000 || h >= 0x4000 {
        return None;
    }
    let src = match to_planes(px, w, h) {
        Some(p) => p,
        None => return None,
    };
    let mb_w = (w + 15) / 16;
    let mb_h = (h + 15) / 16;
    let mut recon = match to_planes(px, w, h) {
        Some(p) => p,
        None => return None,
    };
    let qi = q_index(quality);
    let qs = quants(qi);
    let mbs = match choose_mbs(&src, mb_w, mb_h, qs, &mut recon) {
        Some(v) => v,
        None => return None,
    };
    let (p1, p2) = match write_parts(&mbs, mb_w, mb_h, qi) {
        Some(p) => p,
        None => return None,
    };
    if p1.len() >= 0x8_0000 || p2.len() >= 0x1000_0000 {
        return None;
    }
    let vp8 = 10 + p1.len() + p2.len();
    let pad = vp8 % 2;
    let mut out: Vec<u8> = Vec::new();
    out.push(b'R');
    out.push(b'I');
    out.push(b'F');
    out.push(b'F');
    push_le32(&mut out, (4 + 8 + vp8 + pad) as u32);
    out.push(b'W');
    out.push(b'E');
    out.push(b'B');
    out.push(b'P');
    out.push(b'V');
    out.push(b'P');
    out.push(b'8');
    out.push(b' ');
    push_le32(&mut out, vp8 as u32);
    let tag = ((p1.len() as u32) << 5u32) | 0x10;
    out.push((tag & 0xff) as u8);
    out.push(((tag >> 8u32) & 0xff) as u8);
    out.push(((tag >> 16u32) & 0xff) as u8);
    out.push(0x9d);
    out.push(0x01);
    out.push(0x2a);
    out.push((w & 0xff) as u8);
    out.push((w >> 8) as u8);
    out.push((h & 0xff) as u8);
    out.push((h >> 8) as u8);
    let mut i: usize = 0;
    while i < p1.len()
        decreases p1.len() - i,
    {
        out.push(p1[i]);
        i = i + 1;
    }
    let mut i: usize = 0;
    while i < p2.len()
        decreases p2.len() - i,
    {
        out.push(p2[i]);
        i = i + 1;
    }
    if pad == 1 {
        out.push(0);
    }
    Some(out)
}

} // verus!
