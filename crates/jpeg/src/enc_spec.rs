//! The specification of what the encoder codes: the file to audit, with
//! `spec.rs`, for the encoder. It follows libjpeg-turbo 3.2.1 with its
//! default settings (`jpeg_set_defaults`, `jpeg_set_quality` with
//! `force_baseline`, the slow integer DCT): its colour conversion
//! (`jccolor.c`), edge padding (`jcprepct.c`, `jcsample.c`), 2:1
//! downsampling (`jcsample.c`), forward DCT (`jfdctint.c`), quantization
//! (`jcdctmgr.c`) and the blocks it codes past the image's edge
//! (`jccoefct.c`). The theorem of `encode.rs` is that the file the encoder
//! writes decodes, under `spec::jpeg_coded`, to `enc_coded`.
use crate::enc_file::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Quantization tables (`jcparam.c`)
// ---------------------------------------------------------------------------
/// T.81 Annex K's tables, row-major.
pub const STD_LUM_Q: [u8; 64] = [
    16, 11, 10, 16, 24, 40, 51, 61, 12, 12, 14, 19, 26, 58, 60, 55, 14, 13, 16, 24, 40, 57, 69, 56, 14, 17, 22, 29,
    51, 87, 80, 62, 18, 22, 37, 56, 68, 109, 103, 77, 24, 35, 55, 64, 81, 104, 113, 92, 49, 64, 78, 87, 103, 121,
    120, 101, 72, 92, 95, 98, 112, 100, 103, 99,
];

pub const STD_CHR_Q: [u8; 64] = [
    17, 18, 24, 47, 99, 99, 99, 99, 18, 21, 26, 66, 99, 99, 99, 99, 24, 26, 56, 99, 99, 99, 99, 99, 47, 66, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99,
];

/// `jpeg_quality_scaling`: quality 1 to 100 as a percentage.
pub open spec fn qscale(quality: int) -> int {
    let q: int = if quality <= 0 {
        1
    } else if quality > 100 {
        100
    } else {
        quality
    };
    if q < 50 {
        5000int / q
    } else {
        200 - 2 * q
    }
}

/// One entry of `jpeg_add_quant_table` with `force_baseline`.
pub open spec fn qentry(basic: int, scale: int) -> u8 {
    let t = (basic * scale + 50) / 100;
    if t <= 0 {
        1u8
    } else if t > 255 {
        255u8
    } else {
        t as u8
    }
}

/// Quantization table `n` (0 luma, 1 chroma) for `quality`, row-major.
pub open spec fn qtab(quality: int, n: int) -> Seq<u8> {
    Seq::new(
        64,
        |i: int|
            qentry(
                if n == 0 {
                    STD_LUM_Q[i] as int
                } else {
                    STD_CHR_Q[i] as int
                },
                qscale(quality),
            ),
    )
}

// ---------------------------------------------------------------------------
// Samples
// ---------------------------------------------------------------------------
/// An RGB image, `bpp` bytes a pixel (3, or 4 with the fourth ignored),
/// rows top to bottom.
pub ghost struct Rgb {
    pub w: int,
    pub h: int,
    pub bpp: int,
    pub px: Seq<u8>,
}

pub open spec fn min(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

/// Channel `ch` of pixel (`y`, `x`).
pub open spec fn chan(im: Rgb, y: int, x: int, ch: int) -> int {
    im.px[(y * im.w + x) * im.bpp + ch] as int
}

/// `rgb_ycc_convert`: Y, Cb or Cr (`c` = 0, 1, 2) in 16-bit fixed point.
pub open spec fn ycc(r: int, g: int, b: int, c: int) -> int {
    if c == 0 {
        (19595 * r + 38470 * g + 7471 * b + 32768) / 65536
    } else if c == 1 {
        (-11059 * r - 21709 * g + 32768 * b + 8421375) / 65536
    } else {
        (32768 * r - 27439 * g - 5329 * b + 8421375) / 65536
    }
}

/// Component `c` at full resolution, the image's last row and column
/// repeated past its edges (`expand_right_edge`, `expand_bottom_edge`).
pub open spec fn full(im: Rgb, c: int, y: int, x: int) -> int {
    let yy = min(y, im.h - 1);
    let xx = min(x, im.w - 1);
    ycc(chan(im, yy, xx, 0), chan(im, yy, xx, 1), chan(im, yy, xx, 2), c)
}

/// Sample (`y`, `x`) of component `c` as coded. Without subsampling, the
/// full-resolution sample; with it, chroma is `h2v2_downsample`'s average
/// of a 2 by 2 square, with its alternating bias of 1 and 2, the rows past
/// the downsampled image's last repeating that one.
pub open spec fn samp(im: Rgb, sub: bool, c: int, y: int, x: int) -> int {
    if !sub || c == 0 {
        full(im, c, y, x)
    } else {
        let yy = min(y, (im.h + 1) / 2 - 1);
        (full(im, c, 2 * yy, 2 * x) + full(im, c, 2 * yy, 2 * x + 1) + full(im, c, 2 * yy + 1, 2 * x) + full(
            im,
            c,
            2 * yy + 1,
            2 * x + 1,
        ) + 1 + x % 2) / 4
    }
}

/// The 64 samples of block (`bx`, `by`) of component `c`, less 128.
pub open spec fn block_samples(im: Rgb, sub: bool, c: int, bx: int, by: int) -> Seq<int> {
    Seq::new(64, |i: int| samp(im, sub, c, 8 * by + i / 8, 8 * bx + i % 8) - 128)
}

// ---------------------------------------------------------------------------
// The forward DCT (`jfdctint.c`, `jpeg_fdct_islow`)
// ---------------------------------------------------------------------------
/// One pass over eight values. The first (`first`) keeps two more bits
/// of precision; the second takes them off and leaves the result scaled
/// by 8.
#[verifier::opaque]
pub open spec fn fdct_1d(d: Seq<int>, first: bool) -> Seq<int> {
    let tmp0 = d[0] + d[7];
    let tmp7 = d[0] - d[7];
    let tmp1 = d[1] + d[6];
    let tmp6 = d[1] - d[6];
    let tmp2 = d[2] + d[5];
    let tmp5 = d[2] - d[5];
    let tmp3 = d[3] + d[4];
    let tmp4 = d[3] - d[4];
    let tmp10 = tmp0 + tmp3;
    let tmp13 = tmp0 - tmp3;
    let tmp11 = tmp1 + tmp2;
    let tmp12 = tmp1 - tmp2;
    let sh: nat = if first {
        11
    } else {
        15
    };
    let o0 = if first {
        4 * (tmp10 + tmp11)
    } else {
        descale(tmp10 + tmp11, 2)
    };
    let o4 = if first {
        4 * (tmp10 - tmp11)
    } else {
        descale(tmp10 - tmp11, 2)
    };
    let z1 = (tmp12 + tmp13) * 4433;
    let o2 = descale(z1 + tmp13 * 6270, sh);
    let o6 = descale(z1 + tmp12 * (-15137), sh);
    let z1 = tmp4 + tmp7;
    let z2 = tmp5 + tmp6;
    let z3 = tmp4 + tmp6;
    let z4 = tmp5 + tmp7;
    let z5 = (z3 + z4) * 9633;
    let t4 = tmp4 * 2446;
    let t5 = tmp5 * 16819;
    let t6 = tmp6 * 25172;
    let t7 = tmp7 * 12299;
    let z1 = z1 * (-7373);
    let z2 = z2 * (-20995);
    let z3 = z3 * (-16069) + z5;
    let z4 = z4 * (-3196) + z5;
    let o7 = descale(t4 + z1 + z3, sh);
    let o5 = descale(t5 + z2 + z4, sh);
    let o3 = descale(t6 + z2 + z3, sh);
    let o1 = descale(t7 + z1 + z4, sh);
    seq![o0, o1, o2, o3, o4, o5, o6, o7]
}

/// The rows of the block after the first pass.
pub open spec fn fdct_rows(s: Seq<int>) -> Seq<int> {
    Seq::new(64, |i: int| fdct_1d(Seq::new(8, |j: int| s[8 * (i / 8) + j]), true)[i % 8])
}

/// The block's DCT, row-major, scaled by 8.
#[verifier::opaque]
pub open spec fn fdct(s: Seq<int>) -> Seq<int> {
    let r = fdct_rows(s);
    Seq::new(64, |i: int| fdct_1d(Seq::new(8, |j: int| r[8 * j + i % 8]), false)[i / 8])
}

// ---------------------------------------------------------------------------
// Quantization (`jcdctmgr.c`) and the blocks coded
// ---------------------------------------------------------------------------
pub open spec fn clamp_coef(v: int, k: int) -> int {
    let lo = if k == 0 {
        -1024
    } else {
        -1023
    };
    if v < lo {
        lo
    } else if v > 1023 {
        1023
    } else {
        v
    }
}

/// `t` (scaled by 8) divided by `q`, rounded to nearest, halves away from
/// zero. The result is kept in baseline range: DC from -1024 to 1023, AC
/// from -1023 to 1023 (for 8-bit samples it always is; libjpeg would stop
/// with an error, or write a symbol its AC table has no code for).
pub open spec fn quant(t: int, q: int, k: int) -> int {
    let d = 8 * q;
    let v = if t < 0 {
        -((-t + d / 2) / d)
    } else {
        (t + d / 2) / d
    };
    clamp_coef(v, k)
}

pub open spec fn qtab_of(quality: int, c: int) -> Seq<u8> {
    qtab(
        quality,
        if c == 0 {
            0
        } else {
            1
        },
    )
}

/// A block inside the image: its samples transformed and quantized.
pub open spec fn real_block(im: Rgb, sub: bool, quality: int, c: int, bx: int, by: int) -> Seq<i16> {
    let t = fdct(block_samples(im, sub, c, bx, by));
    let q = qtab_of(quality, c);
    Seq::new(64, |k: int| quant(t[k], q[k] as int, k) as i16)
}

/// The encoder's frame: `hv` 0x22 with subsampling, else 0x11.
pub open spec fn enc_frame_of(im: Rgb, sub: bool) -> Frame {
    frame_of(
        im.w,
        im.h,
        if sub {
            0x22u8
        } else {
            0x11u8
        },
    )
}

/// Block (`bx`, `by`) of component `c`. The blocks of an MCU that lie past
/// the image's blocks (only luma's, with subsampling) are libjpeg's dummy
/// blocks: AC zero, and the DC of the block before them in the MCU, which
/// comes down to the last real block of their row, or for a row past the
/// bottom, the last real block of the MCU's row above it.
pub open spec fn coef_block(im: Rgb, sub: bool, quality: int, c: int, bx: int, by: int) -> Seq<i16> {
    let f = enc_frame_of(im, sub);
    let wbc = wb(f, c);
    let hbc = hb(f, c);
    if bx < wbc && by < hbc {
        real_block(im, sub, quality, c, bx, by)
    } else {
        let h0 = f.comps[0].h as int;
        let dc = if by < hbc {
            real_block(im, sub, quality, c, wbc - 1, by)[0]
        } else {
            real_block(im, sub, quality, c, min(bx - bx % h0 + h0 - 1, wbc - 1), hbc - 1)[0]
        };
        Seq::new(64, |k: int| if k == 0 { dc } else { 0i16 })
    }
}

/// All the coefficients, laid out as the decoder holds them.
pub open spec fn enc_coefs(im: Rgb, sub: bool, quality: int) -> Seq<Seq<i16>> {
    let f = enc_frame_of(im, sub);
    Seq::new(
        3,
        |c: int|
            Seq::new(
                (64 * cw(f, c) * ch(f, c)) as nat,
                |j: int| coef_block(im, sub, quality, c, (j / 64) % cw(f, c), (j / 64) / cw(f, c))[j % 64],
            ),
    )
}

/// What the encoder's file decodes to.
pub open spec fn enc_coded(im: Rgb, sub: bool, quality: int) -> Coded {
    Coded {
        f: enc_frame_of(im, sub),
        a: enc_coefs(im, sub, quality),
        ql: seq![q16(qtab(quality, 0)), q16(qtab(quality, 1)), q16(qtab(quality, 1))],
        color: Color::YCbCr,
    }
}

} // verus!
