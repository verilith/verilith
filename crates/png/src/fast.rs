//! Direct output paths for non-interlaced images. There the reconstructed
//! image is already the native format, and 8-bit RGBA is one linear pass
//! over it (`spec::native`, `spec::rgba8`).
use crate::chunks::Header;
use crate::decode::PngX;
use crate::geom::*;
use crate::output::*;
use crate::passes::*;
use crate::prims::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The single image of a non-interlaced file: the first `h * rb` bytes of
/// the buffer.
pub proof fn lemma_flat(h: Ihdr, buf: Seq<u8>, off: Seq<usize>)
    requires
        bufs_ok(h, buf, off),
        h.interlace == 0,
    ensures
        npasses(h) == 1,
        pass_w(h, 0) == h.w,
        pass_h(h, 0) == h.h,
        row_bytes(h, h.w) >= 1,
        off[0] == 0,
        off[1] == h.h * row_bytes(h, h.w),
        h.h * row_bytes(h, h.w) <= buf.len(),
        imgs_of(h, buf, off)[0] == buf.subrange(0, h.h * row_bytes(h, h.w) as int),
{
    let rb = row_bytes(h, h.w);
    assert(pass_w(h, 0) == h.w);
    assert(pass_h(h, 0) == h.h);
    assert(pixel_bits(h) >= 1) by (nonlinear_arith)
        requires
            channels(h.ct) >= 1,
            h.depth >= 1,
            pixel_bits(h) == channels(h.ct) * h.depth,
    ;
    assert(h.w * pixel_bits(h) >= 1) by (nonlinear_arith)
        requires
            h.w >= 1,
            pixel_bits(h) >= 1,
    ;
    assert(rb >= 1);
    assert(h.h * (1 + rb) >= 1) by (nonlinear_arith)
        requires
            h.h >= 1,
    ;
    assert(pass_size(h, 0) != 0);
    reveal_with_fuel(img_off, 2);
    assert(img_off(h, 1) == img_size(h, 0));
    assert(off[0] == img_off(h, 0));
    assert(off[1] == img_off(h, 1));
}

/// A sample of an 8-bit non-interlaced image, by pixel number.
pub proof fn lemma_px8(h: Ihdr, imgs: Seq<Seq<u8>>, i: nat, c: nat)
    requires
        hdr_ok(h),
        h.interlace == 0,
        h.depth == 8,
        c < channels(h.ct),
    ensures
        row_bytes(h, h.w) == h.w * channels(h.ct),
        px_sample(h, imgs, i % h.w, i / h.w, c) == imgs[0][(i * channels(h.ct) + c) as int] as nat,
{
    let ch = channels(h.ct);
    let w = h.w;
    assert(w * pixel_bits(h) == (w * ch) * 8) by (nonlinear_arith)
        requires
            pixel_bits(h) == ch * 8,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (w * ch * 8 + 7) as int,
        8,
        (w * ch) as int,
        7,
    );
    let x = i % w;
    let y = i / w;
    assert(x / 1 == x);
    assert(y / 1 == y);
    assert(pass_w(h, 0) == w);
    vstd::arithmetic::div_mod::lemma_div_by_multiple((x * ch + c) as int, 8);
    assert((x * ch + c) * 8 / 8 == x * ch + c);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, w as int);
    assert(y * (w * ch) + (x * ch + c) == (y * w + x) * ch + c) by (nonlinear_arith);
    assert(y * w + x == i) by (nonlinear_arith)
        requires
            i == w * (i / w) + i % w,
            x == i % w,
            y == i / w,
    ;
}

/// `s[4 * i + j]`: byte `j` of pixel `i` of an RGBA image.
pub open spec fn quad(s: Seq<u8>, i: int, j: int) -> u8 {
    s[4 * i + j]
}

/// An RGBA image whose every pixel matches `spec::rgba_byte` is
/// `spec::rgba8`.
pub proof fn lemma_rgba_done(pv: Png, imgs: Seq<Seq<u8>>, out: Seq<u8>)
    requires
        pv.hdr.w >= 1,
        out.len() == 4 * (pv.hdr.w * pv.hdr.h),
        forall|i: int, j: int|
            0 <= i < pv.hdr.w * pv.hdr.h && 0 <= j < 4 ==> #[trigger] quad(out, i, j) == rgba_byte(
                pv,
                imgs,
                (i % pv.hdr.w as int) as nat,
                (i / pv.hdr.w as int) as nat,
                j as nat,
            ),
    ensures
        out == rgba8(pv, imgs),
{
    let w = pv.hdr.w;
    let r = rgba8(pv, imgs);
    assert(4 * w * pv.hdr.h == 4 * (w * pv.hdr.h)) by (nonlinear_arith);
    assert forall|k: int| 0 <= k < out.len() implies out[k] == r[k] by {
        let i = k / 4;
        let j = k % 4;
        assert(k == 4 * i + j);
        assert(quad(out, i, j) == out[k]);
        assert(i < w * pv.hdr.h);
    }
    assert(out =~= r);
}

/// The 8-bit RGBA value of a pixel whose first sample is `v`, for grey
/// (type 0) and palette (type 3) images (`spec::rgba_byte`).
pub open spec fn ent(png: Png, v: nat, j: nat) -> u8 {
    if png.hdr.ct == 3 {
        if j == 3 {
            match png.trns {
                Some(t) => if v < t.len() {
                    t[v as int]
                } else {
                    255u8
                },
                None => 255u8,
            }
        } else if 3 * v + 3 <= png.plte.len() {
            png.plte[(3 * v + j) as int]
        } else {
            0u8
        }
    } else if j < 3 {
        v as u8
    } else {
        match png.trns {
            Some(t) => if v == be16(t, 0) % 256 {
                0u8
            } else {
                255u8
            },
            None => 255u8,
        }
    }
}

/// The RGBA values of all 256 sample values, `ent(v, j)` at `4 * v + j`.
fn table(png: &PngX) -> (r: Vec<u8>)
    requires
        png.wf(),
        png.hdr.color_type == 0 || png.hdr.color_type == 3,
    ensures
        r@.len() == 1024,
        forall|v: int, j: int| 0 <= v < 256 && 0 <= j < 4 ==> #[trigger] quad(r@, v, j) == ent(png.view(), v as nat, j as nat),
{
    let ghost pv = png.view();
    let mut tab: Vec<u8> = vec![0u8; 1024];
    let ct = png.hdr.color_type;
    let key: u64 = match &png.trns {
        Some(t) => if ct == 0 {
            trns_val(t.as_slice(), 0, 8)
        } else {
            256
        },
        None => 256,
    };
    proof {
        crate::output::lemma_pow2_shift(8);
    }
    let mut v: usize = 0;
    while v < 256
        invariant
            png.wf(),
            pv == png.view(),
            ct == png.hdr.color_type,
            ct == 0 || ct == 3,
            ct == 0 ==> (png.trns matches Some(t) ==> key == be16(t@, 0) % 256),
            tab@.len() == 1024,
            v <= 256,
            forall|u: int, j: int| 0 <= u < v && 0 <= j < 4 ==> #[trigger] quad(tab@, u, j) == ent(pv, u as nat, j as nat),
        decreases 256 - v,
    {
        let (r, g, b, a): (u8, u8, u8, u8) = if ct == 3 {
            let a = match &png.trns {
                Some(t) => if v < t.len() {
                    t[v]
                } else {
                    255u8
                },
                None => 255u8,
            };
            let pl = &png.plte;
            if 3 * v + 3 <= pl.len() {
                (pl[3 * v], pl[3 * v + 1], pl[3 * v + 2], a)
            } else {
                (0, 0, 0, a)
            }
        } else {
            let a = match &png.trns {
                Some(_) => if v as u64 == key {
                    0u8
                } else {
                    255u8
                },
                None => 255u8,
            };
            (v as u8, v as u8, v as u8, a)
        };
        let ghost t0 = tab@;
        set(tab.as_mut_slice(), 4 * v, r);
        set(tab.as_mut_slice(), 4 * v + 1, g);
        set(tab.as_mut_slice(), 4 * v + 2, b);
        set(tab.as_mut_slice(), 4 * v + 3, a);
        proof {
            assert(r == ent(pv, v as nat, 0));
            assert(g == ent(pv, v as nat, 1));
            assert(b == ent(pv, v as nat, 2));
            assert(a == ent(pv, v as nat, 3));
            assert forall|u: int, j: int| 0 <= u < v + 1 && 0 <= j < 4 implies #[trigger] quad(tab@, u, j) == ent(pv, u as nat, j as nat) by {
                if u < v {
                    assert(quad(t0, u, j) == ent(pv, u as nat, j as nat));
                } else if j == 0 {
                } else if j == 1 {
                } else if j == 2 {
                } else {
                }
            }
        }
        v = v + 1;
    }
    tab
}

/// `out[4i..4i+4] = tab[4 src[i]..]` for `i < n`.
fn expand_indexed(src: &[u8], n: usize, tab: &[u8], out: &mut [u8])
    requires
        n <= src@.len(),
        tab@.len() == 1024,
        old(out)@.len() == 4 * n,
    ensures
        final(out)@.len() == 4 * n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 ==> #[trigger] quad(final(out)@, i, j) == quad(tab@, src@[i] as int, j),
{
    let _ = out.len();
    let mut i: usize = 0;
    let mut o: usize = 0;
    while i < n
        invariant
            n <= src@.len(),
            tab@.len() == 1024,
            out@.len() == 4 * n,
            4 * n <= usize::MAX,
            i <= n,
            o == 4 * i,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 4 ==> #[trigger] quad(out@, k, j) == quad(tab@, src@[k] as int, j),
        decreases n - i,
    {
        let t = 4 * get(src, i) as usize;
        let ghost o0 = out@;
        set(out, o, get(tab, t));
        set(out, o + 1, get(tab, t + 1));
        set(out, o + 2, get(tab, t + 2));
        set(out, o + 3, get(tab, t + 3));
        proof {
            assert forall|k: int, j: int| 0 <= k < i + 1 && 0 <= j < 4 implies #[trigger] quad(out@, k, j) == quad(tab@, src@[k] as int, j) by {
                if k < i {
                    assert(quad(o0, k, j) == quad(tab@, src@[k] as int, j));
                }
            }
        }
        i = i + 1;
        o = o + 4;
    }
}

/// The alpha of an RGB pixel against an optional transparent colour.
pub open spec fn alpha3(key: Option<(u8, u8, u8)>, r: u8, g: u8, b: u8) -> u8 {
    match key {
        Some((kr, kg, kb)) => if r == kr && g == kg && b == kb {
            0u8
        } else {
            255u8
        },
        None => 255u8,
    }
}

/// `src`'s `n` RGB pixels as RGBA.
fn expand_rgb(src: &[u8], n: usize, key: Option<(u8, u8, u8)>, out: &mut [u8])
    requires
        3 * n <= src@.len(),
        old(out)@.len() == 4 * n,
    ensures
        final(out)@.len() == 4 * n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 ==> #[trigger] quad(final(out)@, i, j) == if j < 3 {
            src@[3 * i + j]
        } else {
            alpha3(key, src@[3 * i], src@[3 * i + 1], src@[3 * i + 2])
        },
{
    let (has, kr, kg, kb) = match key {
        Some((r, g, b)) => (true, r, g, b),
        None => (false, 0, 0, 0),
    };
    let _ = out.len();
    let mut i: usize = 0;
    let mut s: usize = 0;
    let mut o: usize = 0;
    while i < n
        invariant
            3 * n <= src@.len(),
            out@.len() == 4 * n,
            4 * n <= usize::MAX,
            i <= n,
            s == 3 * i,
            o == 4 * i,
            has == key is Some,
            key matches Some(kk) ==> kk == (kr, kg, kb),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 4 ==> #[trigger] quad(out@, k, j) == if j < 3 {
                src@[3 * k + j]
            } else {
                alpha3(key, src@[3 * k], src@[3 * k + 1], src@[3 * k + 2])
            },
        decreases n - i,
    {
        let r = get(src, s);
        let g = get(src, s + 1);
        let b = get(src, s + 2);
        let a = if has && r == kr && g == kg && b == kb {
            0u8
        } else {
            255u8
        };
        let ghost o0 = out@;
        set(out, o, r);
        set(out, o + 1, g);
        set(out, o + 2, b);
        set(out, o + 3, a);
        proof {
            assert forall|k: int, j: int| 0 <= k < i + 1 && 0 <= j < 4 implies #[trigger] quad(out@, k, j) == if j < 3 {
                src@[3 * k + j]
            } else {
                alpha3(key, src@[3 * k], src@[3 * k + 1], src@[3 * k + 2])
            } by {
                if k < i {
                    assert(quad(o0, k, j) == quad(out@, k, j));
                }
            }
        }
        i = i + 1;
        s = s + 3;
        o = o + 4;
    }
}

/// `src`'s `n` grey-alpha pixels as RGBA.
fn expand_ga(src: &[u8], n: usize, out: &mut [u8])
    requires
        2 * n <= src@.len(),
        old(out)@.len() == 4 * n,
    ensures
        final(out)@.len() == 4 * n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 ==> #[trigger] quad(final(out)@, i, j) == if j < 3 {
            src@[2 * i]
        } else {
            src@[2 * i + 1]
        },
{
    let _ = out.len();
    let mut i: usize = 0;
    let mut s: usize = 0;
    let mut o: usize = 0;
    while i < n
        invariant
            2 * n <= src@.len(),
            out@.len() == 4 * n,
            4 * n <= usize::MAX,
            i <= n,
            s == 2 * i,
            o == 4 * i,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 4 ==> #[trigger] quad(out@, k, j) == if j < 3 {
                src@[2 * k]
            } else {
                src@[2 * k + 1]
            },
        decreases n - i,
    {
        let g = get(src, s);
        let a = get(src, s + 1);
        let ghost o0 = out@;
        set(out, o, g);
        set(out, o + 1, g);
        set(out, o + 2, g);
        set(out, o + 3, a);
        proof {
            assert forall|k: int, j: int| 0 <= k < i + 1 && 0 <= j < 4 implies #[trigger] quad(out@, k, j) == if j < 3 {
                src@[2 * k]
            } else {
                src@[2 * k + 1]
            } by {
                if k < i {
                    assert(quad(o0, k, j) == quad(out@, k, j));
                }
            }
        }
        i = i + 1;
        s = s + 2;
        o = o + 4;
    }
}

/// A sample of a 16-bit non-interlaced image, by pixel number.
pub proof fn lemma_px16(h: Ihdr, imgs: Seq<Seq<u8>>, i: nat, c: nat)
    requires
        hdr_ok(h),
        h.interlace == 0,
        h.depth == 16,
        c < channels(h.ct),
    ensures
        row_bytes(h, h.w) == 2 * (h.w * channels(h.ct)),
        px_sample(h, imgs, i % h.w, i / h.w, c) == be16(imgs[0], (2 * (i * channels(h.ct) + c)) as int),
        to8(16, be16(imgs[0], (2 * (i * channels(h.ct) + c)) as int)) == imgs[0][(2 * (i * channels(h.ct) + c)) as int],
{
    let ch = channels(h.ct);
    let w = h.w;
    assert(w * pixel_bits(h) == (2 * (w * ch)) * 8) by (nonlinear_arith)
        requires
            pixel_bits(h) == ch * 16,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (2 * (w * ch) * 8 + 7) as int,
        8,
        (2 * (w * ch)) as int,
        7,
    );
    let x = i % w;
    let y = i / w;
    assert(x / 1 == x);
    assert(y / 1 == y);
    assert(pass_w(h, 0) == w);
    vstd::arithmetic::div_mod::lemma_div_by_multiple((2 * (x * ch + c)) as int, 8);
    assert((x * ch + c) * 16 == (2 * (x * ch + c)) * 8) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, w as int);
    assert(y * (2 * (w * ch)) + 2 * (x * ch + c) == 2 * ((y * w + x) * ch + c)) by (nonlinear_arith);
    assert(y * w + x == i) by (nonlinear_arith)
        requires
            i == w * (i / w) + i % w,
            x == i % w,
            y == i / w,
    ;
    let k = 2 * (i * ch + c);
    let img = imgs[0];
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        be16(img, k as int) as int,
        256,
        img[k as int] as int,
        img[k + 1int] as int,
    );
}

/// `s[k..k + 2]` as a big-endian number.
fn be16_exec(s: &[u8], k: usize) -> (r: u16)
    requires
        k + 2 <= s@.len(),
    ensures
        r as nat == be16(s@, k as int),
{
    let _ = s.len();
    get(s, k) as u16 * 256 + get(s, k + 1) as u16
}

/// The alpha of a 16-bit RGB pixel against an optional transparent colour.
pub open spec fn alpha16(key: Option<(u16, u16, u16)>, r: nat, g: nat, b: nat) -> u8 {
    match key {
        Some((kr, kg, kb)) => if r == kr && g == kg && b == kb {
            0u8
        } else {
            255u8
        },
        None => 255u8,
    }
}

/// The high bytes of `src`'s `n` 16-bit pixels of `ch` channels as RGBA:
/// `ch` 1 grey (alpha from `key`), 2 grey-alpha, 3 RGB (alpha from `key`),
/// 4 RGBA.
pub open spec fn px16(src: Seq<u8>, ch: nat, key: Option<(u16, u16, u16)>, i: int, j: int) -> u8 {
    let b = 2 * ch * i;
    if ch == 4 {
        src[b + 2 * j]
    } else if ch == 3 {
        if j < 3 {
            src[b + 2 * j]
        } else {
            alpha16(key, be16(src, b), be16(src, b + 2), be16(src, b + 4))
        }
    } else if ch == 2 {
        if j < 3 {
            src[b]
        } else {
            src[b + 2]
        }
    } else if j < 3 {
        src[b]
    } else {
        alpha16(key, be16(src, b), be16(src, b), be16(src, b))
    }
}

/// `src`'s `n` 16-bit pixels of `ch` channels as 8-bit RGBA (`px16`).
#[verifier::rlimit(20)]
fn expand16(src: &[u8], n: usize, ch: usize, key: Option<(u16, u16, u16)>, out: &mut [u8])
    requires
        1 <= ch <= 4,
        2 * ch * n <= src@.len(),
        old(out)@.len() == 4 * n,
    ensures
        final(out)@.len() == 4 * n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 ==> #[trigger] quad(final(out)@, i, j) == px16(src@, ch as nat, key, i, j),
{
    let (has, kr, kg, kb) = match key {
        Some((r, g, b)) => (true, r, g, b),
        None => (false, 0, 0, 0),
    };
    let _ = out.len();
    let _ = src.len();
    let step = 2 * ch;
    let mut i: usize = 0;
    let mut s: usize = 0;
    let mut o: usize = 0;
    while i < n
        invariant
            1 <= ch <= 4,
            step == 2 * ch,
            2 * ch * n <= src@.len(),
            src@.len() <= usize::MAX,
            out@.len() == 4 * n,
            4 * n <= usize::MAX,
            i <= n,
            s == step * i,
            o == 4 * i,
            has == key is Some,
            key matches Some(kk) ==> kk == (kr, kg, kb),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 4 ==> #[trigger] quad(out@, k, j) == px16(src@, ch as nat, key, k, j),
        decreases n - i,
    {
        proof {
            assert(step * i + step <= step * n) by (nonlinear_arith)
                requires
                    i < n,
            ;
        }
        let (r, g, b, a) = if ch == 4 {
            (get(src, s), get(src, s + 2), get(src, s + 4), get(src, s + 6))
        } else if ch == 3 {
            let a = if has && be16_exec(src, s) == kr && be16_exec(src, s + 2) == kg && be16_exec(src, s + 4) == kb {
                0u8
            } else {
                255u8
            };
            (get(src, s), get(src, s + 2), get(src, s + 4), a)
        } else if ch == 2 {
            (get(src, s), get(src, s), get(src, s), get(src, s + 2))
        } else {
            let v = be16_exec(src, s);
            let a = if has && v == kr && v == kg && v == kb {
                0u8
            } else {
                255u8
            };
            (get(src, s), get(src, s), get(src, s), a)
        };
        let ghost o0 = out@;
        set(out, o, r);
        set(out, o + 1, g);
        set(out, o + 2, b);
        set(out, o + 3, a);
        proof {
            assert(2 * ch * i == s);
            assert forall|k: int, j: int| 0 <= k < i + 1 && 0 <= j < 4 implies #[trigger] quad(out@, k, j) == px16(src@, ch as nat, key, k, j) by {
                if k < i {
                    assert(quad(o0, k, j) == quad(out@, k, j));
                } else if j == 0 {
                } else if j == 1 {
                } else if j == 2 {
                } else {
                }
            }
        }
        proof {
            assert(step * i + step == step * (i + 1)) by (nonlinear_arith);
        }
        i = i + 1;
        s = s + step;
        o = o + 4;
    }
}

/// `spec::rgba8` of a non-interlaced 16-bit image.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn rgba8_flat16(png: &PngX, buf: &[u8], off: &[usize; 8], limit: usize) -> (r: Result<Vec<u8>, crate::decode::Error>)
    requires
        png.wf(),
        bufs_ok(png.hdr.view(), buf@, off@),
        png.hdr.view().interlace == 0,
        png.hdr.view().depth == 16,
    ensures
        r matches Ok(v) ==> v@ == rgba8(png.view(), imgs_of(png.hdr.view(), buf@, off@)),
        r matches Err(e) ==> e != crate::decode::Error::Invalid,
{
    let h = &png.hdr;
    let ghost hv = h.view();
    let ghost pv = png.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let ghost img = imgs[0];
    let w = h.width as u64;
    let hh = h.height as u64;
    let ct = h.color_type;
    let ch = crate::geom::channels_exec(ct) as usize;
    proof {
        lemma_flat(hv, buf@, off@);
        lemma_px16(hv, imgs, 0, 0);
        assert(w * hh <= 0x7fff_ffff * 0x7fff_ffff) by (nonlinear_arith)
            requires
                w <= 0x7fff_ffff,
                hh <= 0x7fff_ffff,
        ;
        assert(hh * (2 * (w * ch)) == 2 * ch * (w * hh)) by (nonlinear_arith);
        crate::output::lemma_pow2_shift(16);
    }
    let n = (w * hh) as usize;
    proof {
        assert forall|k: int| 0 <= k < 2 * ch * n implies #[trigger] img[k] == buf@[k] by {}
        assert(img =~= buf@.subrange(0, 2 * ch * n));
    }
    if 4 * n as u128 > limit as u128 {
        return Err(crate::decode::Error::TooLarge);
    }
    let mut out = match alloc_zeroed(4 * n) {
        Some(v) => v,
        None => return Err(crate::decode::Error::OutOfMemory),
    };
    let key: Option<(u16, u16, u16)> = match &png.trns {
        Some(t) => if ct == 2 {
            Some(
                (
                    trns_val(t.as_slice(), 0, 16) as u16,
                    trns_val(t.as_slice(), 2, 16) as u16,
                    trns_val(t.as_slice(), 4, 16) as u16,
                ),
            )
        } else if ct == 0 {
            let v = trns_val(t.as_slice(), 0, 16) as u16;
            Some((v, v, v))
        } else {
            None
        },
        None => None,
    };
    expand16(buf, n, ch, key, out.as_mut_slice());
    proof {
        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 implies #[trigger] quad(out@, i, j) == rgba_byte(
            pv,
            imgs,
            (i % w as int) as nat,
            (i / w as int) as nat,
            j as nat,
        ) by {
            assert(2 * ch * i + 2 * ch <= 2 * ch * n) by (nonlinear_arith)
                requires
                    i < n,
            ;
            assert(2 * (i * ch) == 2 * ch * i) by (nonlinear_arith);
            lemma_px16(hv, imgs, i as nat, 0);
            if ch >= 2 {
                lemma_px16(hv, imgs, i as nat, 1);
            }
            if ch >= 3 {
                lemma_px16(hv, imgs, i as nat, 2);
            }
            if ch >= 4 {
                lemma_px16(hv, imgs, i as nat, 3);
            }
            assert(quad(out@, i, j) == px16(buf@, ch as nat, key, i, j));
        }
        lemma_rgba_done(pv, imgs, out@);
    }
    Ok(out)
}

/// Whether `rgba8_flat` handles the image.
pub open spec fn flat8(h: Ihdr) -> bool {
    h.interlace == 0 && h.depth == 8
}

/// `spec::rgba8` of a non-interlaced 8-bit image. Takes the reconstructed
/// buffer and, for RGBA images, returns it as the result.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn rgba8_flat(png: &PngX, buf: Vec<u8>, off: &[usize; 8], limit: usize) -> (r: Result<Vec<u8>, crate::decode::Error>)
    requires
        png.wf(),
        bufs_ok(png.hdr.view(), buf@, off@),
        flat8(png.hdr.view()),
    ensures
        r matches Ok(v) ==> v@ == rgba8(png.view(), imgs_of(png.hdr.view(), buf@, off@)),
        r matches Err(e) ==> e != crate::decode::Error::Invalid,
{
    let h = &png.hdr;
    let ghost hv = h.view();
    let ghost pv = png.view();
    let ghost b0 = buf@;
    let ghost imgs = imgs_of(hv, buf@, off@);
    let ghost img = imgs[0];
    let w = h.width as u64;
    let hh = h.height as u64;
    let ct = h.color_type;
    proof {
        lemma_flat(hv, buf@, off@);
        lemma_px8(hv, imgs, 0, 0);
        assert(w * hh <= 0x7fff_ffff * 0x7fff_ffff) by (nonlinear_arith)
            requires
                w <= 0x7fff_ffff,
                hh <= 0x7fff_ffff,
        ;
        assert(hh * (w * channels(ct as nat)) == (w * hh) * channels(ct as nat)) by (nonlinear_arith);
        crate::output::lemma_pow2_shift(8);
    }
    let n = (w * hh) as usize;
    let ghost ch = channels(ct as nat);
    proof {
        assert(img.len() == n * ch);
        assert forall|k: int| 0 <= k < n * ch implies #[trigger] img[k] == buf@[k] by {}
    }
    if ct == 6 {
        // The image is already RGBA.
        let mut v = buf;
        v.truncate(4 * n);
        proof {
            assert forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 implies #[trigger] quad(v@, i, j) == rgba_byte(
                pv,
                imgs,
                (i % w as int) as nat,
                (i / w as int) as nat,
                j as nat,
            ) by {
                lemma_px8(hv, imgs, i as nat, j as nat);
                assert(4 * i + j < 4 * n);
            }
            lemma_rgba_done(pv, imgs, v@);
        }
        return Ok(v);
    }
    if 4 * n as u128 > limit as u128 {
        return Err(crate::decode::Error::TooLarge);
    }
    let mut out = match alloc_zeroed(4 * n) {
        Some(v) => v,
        None => return Err(crate::decode::Error::OutOfMemory),
    };
    if ct == 2 {
        let key = match &png.trns {
            Some(t) => Some(
                (
                    trns_val(t.as_slice(), 0, 8) as u8,
                    trns_val(t.as_slice(), 2, 8) as u8,
                    trns_val(t.as_slice(), 4, 8) as u8,
                ),
            ),
            None => None,
        };
        expand_rgb(buf.as_slice(), n, key, out.as_mut_slice());
        proof {
            assert forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 implies #[trigger] quad(out@, i, j) == rgba_byte(
                pv,
                imgs,
                (i % w as int) as nat,
                (i / w as int) as nat,
                j as nat,
            ) by {
                lemma_px8(hv, imgs, i as nat, 0);
                lemma_px8(hv, imgs, i as nat, 1);
                lemma_px8(hv, imgs, i as nat, 2);
                assert(3 * i + 2 < 3 * n);
            }
        }
    } else if ct == 4 {
        expand_ga(buf.as_slice(), n, out.as_mut_slice());
        proof {
            assert forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 implies #[trigger] quad(out@, i, j) == rgba_byte(
                pv,
                imgs,
                (i % w as int) as nat,
                (i / w as int) as nat,
                j as nat,
            ) by {
                lemma_px8(hv, imgs, i as nat, 0);
                lemma_px8(hv, imgs, i as nat, 1);
                assert(2 * i + 1 < 2 * n);
            }
        }
    } else {
        let tab = table(png);
        expand_indexed(buf.as_slice(), n, tab.as_slice(), out.as_mut_slice());
        proof {
            assert forall|i: int, j: int| 0 <= i < n && 0 <= j < 4 implies #[trigger] quad(out@, i, j) == rgba_byte(
                pv,
                imgs,
                (i % w as int) as nat,
                (i / w as int) as nat,
                j as nat,
            ) by {
                lemma_px8(hv, imgs, i as nat, 0);
                assert(quad(tab@, buf@[i] as int, j) == ent(pv, buf@[i] as nat, j as nat));
            }
        }
    }
    proof {
        lemma_rgba_done(pv, imgs, out@);
    }
    Ok(out)
}

/// `spec::native` of a non-interlaced image of whole-byte pixels: the
/// reconstructed buffer itself.
#[verifier::spinoff_prover]
pub fn native_flat(h: &Header, buf: Vec<u8>, off: &[usize; 8]) -> (r: Vec<u8>)
    requires
        bufs_ok(h.view(), buf@, off@),
        h.view().interlace == 0,
        pixel_bits(h.view()) >= 8,
    ensures
        r@ == native(h.view(), imgs_of(h.view(), buf@, off@)),
{
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let ghost b0 = buf@;
    proof {
        lemma_flat(hv, buf@, off@);
    }
    let n = off[1];
    let mut v = buf;
    v.truncate(n);
    proof {
        let rb = row_bytes(hv, hv.w) as int;
        let bits = pixel_bits(hv) as int;
        let bp = bits / 8;
        // Whole-byte pixels: bits is 8, 16, 24, 32, 48 or 64.
        assert(bits % 8 == 0 && bp >= 1) by {
            assert(hv.depth == 8 || hv.depth == 16);
        }
        assert(hv.w * bits == (hv.w * bp) * 8) by (nonlinear_arith)
            requires
                bits == bp * 8,
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            (hv.w * bp * 8 + 7) as int,
            8,
            (hv.w * bp) as int,
            7,
        );
        assert(rb == hv.w * bp);
        let s = native(hv, imgs);
        assert forall|k: int| 0 <= k < n implies #[trigger] v@[k] == s[k] by {
            let j = k % rb;
            let y = k / rb;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k, rb);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bp);
            let x = j / bp;
            assert(x / 1 == x);
            assert(y / 1 == y);
            assert(y * rb + x * bp + j % bp == k) by (nonlinear_arith)
                requires
                    k == rb * y + j,
                    j == bp * x + j % bp,
            ;
            assert(0 <= y < hv.h) by (nonlinear_arith)
                requires
                    0 <= k < hv.h * rb,
                    y == k / rb,
                    rb >= 1,
                    k == rb * y + j,
                    0 <= j < rb,
            ;
        }
        assert(v@ =~= s);
    }
    v
}

} // verus!
