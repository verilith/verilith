//! Output formats: the reconstructed passes turned into 8-bit RGBA or the
//! image's own format, proven to compute `spec::rgba8` and `spec::native`.
use crate::chunks::Header;
use crate::decode::PngX;
use crate::geom::*;
use crate::passes::*;
use crate::prims::*;
use crate::spec::*;
use crate::work::Meter;
use vstd::prelude::*;

verus! {

/// The Adam7 pass of pixel `(x, y)` (`spec::pass_of`), with the pass's
/// origin and spacing.
pub proof fn lemma_pass_of(h: Ihdr, x: nat, y: nat)
    requires
        h.interlace <= 1,
    ensures
        pass_of(h, x, y) < npasses(h),
        x % dx(h, pass_of(h, x, y)) == x0(h, pass_of(h, x, y)),
        y % dy(h, pass_of(h, x, y)) == y0(h, pass_of(h, x, y)),
        x0(h, pass_of(h, x, y)) < dx(h, pass_of(h, x, y)),
        y0(h, pass_of(h, x, y)) < dy(h, pass_of(h, x, y)),
{
    let p = pass_of(h, x, y);
    if h.interlace == 1 {
        assert(x % 2 == (x % 4) % 2) by (nonlinear_arith);
        assert(x % 4 == (x % 8) % 4) by (nonlinear_arith);
        assert(y % 2 == (y % 4) % 2) by (nonlinear_arith);
        assert(y % 4 == (y % 8) % 4) by (nonlinear_arith);
    }
}

pub proof fn lemma_bits(h: Ihdr)
    requires
        hdr_ok(h),
    ensures
        1 <= pixel_bits(h) <= 64,
        1 <= h.depth <= 16,
        1 <= channels(h.ct) <= 4,
{
    assert(1 <= channels(h.ct) * h.depth <= 64) by (nonlinear_arith)
        requires
            1 <= channels(h.ct) <= 4,
            1 <= h.depth <= 16,
    ;
}

/// A pixel of pass `p` lies inside the pass's reduced image.
pub proof fn lemma_in_pass(h: Ihdr, x: nat, y: nat)
    requires
        hdr_ok(h),
        x < h.w,
        y < h.h,
    ensures
        ({
            let p = pass_of(h, x, y);
            &&& x / dx(h, p) < pass_w(h, p)
            &&& y / dy(h, p) < pass_h(h, p)
            &&& pass_size(h, p) > 0
        }),
{
    lemma_pass_of(h, x, y);
    let p = pass_of(h, x, y);
    lemma_bits(h);
    lemma_coord(x, h.w, x0(h, p), dx(h, p));
    lemma_coord(y, h.h, y0(h, p), dy(h, p));
    let a = pass_h(h, p);
    let b = row_bytes(h, pass_w(h, p));
    assert(pass_w(h, p) >= 1);
    assert(b >= 1) by {
        assert(pass_w(h, p) * pixel_bits(h) >= 1) by (nonlinear_arith)
            requires
                pass_w(h, p) >= 1,
                pixel_bits(h) >= 1,
        ;
    }
    assert(a * (1 + b) > 0) by (nonlinear_arith)
        requires
            a >= 1,
            b >= 1,
    ;
}

proof fn lemma_coord(x: nat, w: nat, x0: nat, d: nat)
    requires
        x < w,
        x0 < d,
        x % d == x0,
    ensures
        w > x0,
        x / d < ((w - x0 + d - 1) as nat) / d,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, d as int);
    let q = x / d;
    assert(x == d * q + x0);
    assert(d * q + d <= w - x0 + d - 1 + 1);
    assert((q + 1) * d == d * q + d) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(((q + 1) * d) as int, (w - x0 + d - 1) as int, d as int);
    vstd::arithmetic::div_mod::lemma_div_by_multiple((q + 1) as int, d as int);
}

pub fn pass_of_exec(il: u8, x: u64, y: u64) -> (r: u64)
    requires
        il <= 1,
    ensures
        r == pass_of(Ihdr { w: 0, h: 0, depth: 0, ct: 0, interlace: il as nat }, x as nat, y as nat),
{
    if il == 0 {
        0
    } else if y % 2 == 1 {
        6
    } else if x % 2 == 1 {
        5
    } else if y % 4 == 2 {
        4
    } else if x % 4 == 2 {
        3
    } else if y % 8 == 4 {
        2
    } else if x % 8 == 4 {
        1
    } else {
        0
    }
}

/// `pow2_nat` as a shift.
pub proof fn lemma_pow2_shift(s: u64)
    requires
        s <= 16,
    ensures
        pow2_nat(s as nat) == (1u64 << s) as nat,
        s == 8 ==> pow2_nat(s as nat) == 256,
        s <= 8 ==> pow2_nat(s as nat) <= 256,
        pow2_nat(s as nat) >= 1,
        s == 16 ==> pow2_nat(s as nat) == 65536,
{
    reveal_with_fuel(pow2_nat, 17);
    assert(1u64 << 0u64 == 1) by (bit_vector);
    assert(1u64 << 1u64 == 2) by (bit_vector);
    assert(1u64 << 2u64 == 4) by (bit_vector);
    assert(1u64 << 3u64 == 8) by (bit_vector);
    assert(1u64 << 4u64 == 16) by (bit_vector);
    assert(1u64 << 5u64 == 32) by (bit_vector);
    assert(1u64 << 6u64 == 64) by (bit_vector);
    assert(1u64 << 7u64 == 128) by (bit_vector);
    assert(1u64 << 8u64 == 256) by (bit_vector);
    assert(1u64 << 9u64 == 512) by (bit_vector);
    assert(1u64 << 10u64 == 1024) by (bit_vector);
    assert(1u64 << 11u64 == 2048) by (bit_vector);
    assert(1u64 << 12u64 == 4096) by (bit_vector);
    assert(1u64 << 13u64 == 8192) by (bit_vector);
    assert(1u64 << 14u64 == 16384) by (bit_vector);
    assert(1u64 << 15u64 == 32768) by (bit_vector);
    assert(1u64 << 16u64 == 65536) by (bit_vector);
}

/// Sub-byte samples are whole within their byte.
proof fn lemma_sub_byte(x: nat, d: nat)
    requires
        d == 1 || d == 2 || d == 4,
    ensures
        (x * d) % 8 + d <= 8,
{
    if d == 1 {
    } else if d == 2 {
        assert((x * 2) % 8 == 2 * (x % 4)) by (nonlinear_arith);
    } else {
        assert((x * 4) % 8 == 4 * (x % 2)) by (nonlinear_arith);
    }
}

/// `spec::sample` of pass image `buf[base..]` (rows of `rb` bytes).
pub fn sample_exec(h: &Header, buf: &[u8], base: usize, rb: usize, pw: u64, ph: u64, x: u64, y: u64, c: u64) -> (r: u64)
    requires
        hdr_ok(h.view()),
        x < pw,
        y < ph,
        c < channels(h.view().ct),
        rb == row_bytes(h.view(), pw as nat),
        pw <= MAX_LEN,
        base + ph * rb <= buf@.len(),
    ensures
        r == sample(h.view(), buf@.subrange(base as int, base + ph * rb), rb as nat, x as nat, y as nat, c as nat),
        r < pow2_nat(h.view().depth),
{
    let ghost hv = h.view();
    let ghost img = buf@.subrange(base as int, base + ph * rb);
    let _ = buf.len();
    let d = h.bit_depth as u64;
    let ch = channels_exec(h.color_type);
    proof {
        lemma_bits(hv);
        assert((x * ch + c) * d <= 0x7fff_ffff * 64) by (nonlinear_arith)
            requires
                x < pw,
                pw <= 0x7fff_ffff,
                c < ch,
                ch <= 4,
                d <= 16,
        ;
        assert(x * ch <= 0x7fff_ffff * 4) by (nonlinear_arith)
            requires
                x < pw,
                pw <= 0x7fff_ffff,
                ch <= 4,
        ;
    }
    let k = (x * ch + c) * d;
    proof {
        // The sample's bits lie inside row `y`.
        assert((x * ch + c) * d + d <= pw * (ch * d)) by (nonlinear_arith)
            requires
                x < pw,
                c < ch,
        ;
        assert(k / 8 < rb) by {
            if d == 16 {
                assert(k + 16 <= pw * pixel_bits(hv));
            }
            assert(k + d <= pw * pixel_bits(hv));
            vstd::arithmetic::div_mod::lemma_div_is_ordered(k as int + 7, (pw * pixel_bits(hv) + 7) as int, 8);
        }
        assert(y * rb + rb <= ph * rb) by (nonlinear_arith)
            requires
                y < ph,
        ;
        // So `y` and the index fit a usize on 32-bit targets too.
        assert(rb >= 1);
        assert(ph <= ph * rb) by (nonlinear_arith)
            requires
                rb >= 1,
        ;
        lemma_pow2_shift(d);
    }
    let i = base + y as usize * rb + (k / 8) as usize;
    if d == 16 {
        proof {
            assert(k % 8 == 0 && (k + 16) / 8 == k / 8 + 2) by {
                assert(k == (x * ch + c) * 16);
                assert(k % 8 == 0) by (nonlinear_arith) requires k == (x * ch + c) * 16;
            }
            vstd::arithmetic::div_mod::lemma_div_is_ordered(k as int + 16, (pw * pixel_bits(hv) + 7) as int, 8);
            assert(k / 8 + 2 <= rb);
        }
        get(buf, i) as u64 * 256 + get(buf, i + 1) as u64
    } else if d == 8 {
        get(buf, i) as u64
    } else {
        proof {
            assert(ch == 1);
            assert(c == 0);
            assert((x * ch + c) * d == x * d) by (nonlinear_arith)
                requires
                    ch == 1,
                    c == 0,
            ;
            lemma_sub_byte(x as nat, d as nat);
            assert(k == x * d);
            assert(1u64 << d >= 1) by (bit_vector)
                requires
                    d < 64,
            ;
        }
        let s = 8 - k % 8 - d;
        proof {
            lemma_pow2_shift(s);
        }
        let v = get(buf, i) as u64;
        let m = (1u64 << d) - 1;
        proof {
            assert(v >> s == v / (1u64 << s)) by (bit_vector)
                requires
                    s <= 8,
            ;
            assert((v >> s) & m == (v >> s) % (1u64 << d)) by (bit_vector)
                requires
                    d <= 8,
                    m == (1u64 << d) - 1,
            ;
            assert((v >> s) & m < (1u64 << d)) by (bit_vector)
                requires
                    d <= 8,
                    m == (1u64 << d) - 1,
            ;
        }
        (v >> s) & m
    }
}

/// The reconstructed passes as `spec::pass_images` gives them.
pub open spec fn imgs_of(h: Ihdr, buf: Seq<u8>, off: Seq<usize>) -> Seq<Seq<u8>> {
    imgs_view(buf, off, npasses(h))
}

/// What the output stage needs: a valid header and the reconstructed
/// passes laid out at `off`.
pub open spec fn bufs_ok(h: Ihdr, buf: Seq<u8>, off: Seq<usize>) -> bool {
    &&& hdr_ok(h)
    &&& offs_ok(h, off)
    &&& buf.len() >= off[npasses(h) as int]
}

/// `spec::px_sample`.
pub fn px_sample_exec(h: &Header, buf: &[u8], off: &[usize; 8], x: u64, y: u64, c: u64) -> (r: u64)
    requires
        bufs_ok(h.view(), buf@, off@),
        x < h.width,
        y < h.height,
        c < channels(h.view().ct),
    ensures
        r == px_sample(h.view(), imgs_of(h.view(), buf@, off@), x as nat, y as nat, c as nat),
        r < pow2_nat(h.view().depth),
{
    let ghost hv = h.view();
    let p = pass_of_exec(h.interlace, x, y);
    proof {
        lemma_params_any(hv, h.interlace as nat, p as nat);
        lemma_in_pass(hv, x as nat, y as nat);
        lemma_pass_of(hv, x as nat, y as nat);
        assert(p == pass_of(hv, x as nat, y as nat));
    }
    let (_, _, dx, dy) = pass_params(h.interlace, p);
    let (pw, ph) = pass_dims(h, p);
    let rb = row_bytes_exec(h, pw);
    proof {
        crate::passes::lemma_off_mono(hv, (p + 1) as nat, npasses(hv));
        assert(img_size(hv, p as nat) == ph * rb);
        assert(off@[p + 1] == off@[p as int] + ph * rb);
        assert(imgs_of(hv, buf@, off@)[p as int] == buf@.subrange(off@[p as int] as int, off@[p as int] + ph * rb));
        // Within `off[p + 1]`, a usize, so `rb as usize` keeps it.
        assert(rb <= ph * rb) by (nonlinear_arith)
            requires
                ph >= 1,
        ;
    }
    sample_exec(h, buf, off[p as usize], rb as usize, pw, ph, x / dx, y / dy, c)
}

/// `spec::to8`.
pub fn to8_exec(d: u8, v: u64) -> (r: u8)
    requires
        d == 1 || d == 2 || d == 4 || d == 8 || d == 16,
        v < pow2_nat(d as nat),
    ensures
        r == to8(d as nat, v as nat),
{
    proof {
        reveal_with_fuel(pow2_nat, 17);
    }
    if d == 16 {
        (v / 256) as u8
    } else if d == 8 {
        v as u8
    } else if d == 4 {
        (v * 17) as u8
    } else if d == 2 {
        (v * 85) as u8
    } else {
        (v * 255) as u8
    }
}

/// `be16(t, i) % 2^d`.
pub fn trns_val(t: &[u8], i: usize, d: u8) -> (r: u64)
    requires
        i + 2 <= t@.len(),
        d == 1 || d == 2 || d == 4 || d == 8 || d == 16,
    ensures
        r == be16(t@, i as int) % pow2_nat(d as nat),
{
    proof {
        lemma_pow2_shift(d as u64);
    }
    let v = t[i] as u64 * 256 + t[i + 1] as u64;
    let m = 1u64 << d;
    v % m
}

/// Writes pixel `(x, y)` as 8-bit RGBA to `out[o..o + 4]`
/// (`spec::rgba_byte`).
#[verifier::rlimit(30)]
pub fn rgba_px(png: &PngX, buf: &[u8], off: &[usize; 8], x: u64, y: u64, out: &mut [u8], o: usize)
    requires
        png.wf(),
        bufs_ok(png.hdr.view(), buf@, off@),
        x < png.hdr.width,
        y < png.hdr.height,
        o + 4 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|j: int| 0 <= j < 4 ==> #[trigger] final(out)@[o + j] == rgba_byte(png.view(), imgs_of(png.hdr.view(), buf@, off@), x as nat, y as nat, j as nat),
        forall|k: int| 0 <= k < final(out)@.len() && !(o <= k < o + 4) ==> #[trigger] final(out)@[k] == old(out)@[k],
{
    let h = &png.hdr;
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let ghost pv = png.view();
    let d = h.bit_depth;
    let ct = h.color_type;
    proof {
        lemma_pow2_shift(d as u64);
    }
    let (r, g, b, a): (u8, u8, u8, u8) = if ct == 3 {
        let i = px_sample_exec(h, buf, off, x, y, 0);
        let a = match &png.trns {
            Some(t) => if (i as usize) < t.len() {
                t[i as usize]
            } else {
                255u8
            },
            None => 255u8,
        };
        let pl = &png.plte;
        if 3 * i + 3 <= pl.len() as u64 {
            (pl[3 * i as usize], pl[3 * i as usize + 1], pl[3 * i as usize + 2], a)
        } else {
            (0, 0, 0, a)
        }
    } else if ct == 0 || ct == 4 {
        let gv = px_sample_exec(h, buf, off, x, y, 0);
        let g8 = to8_exec(d, gv);
        let a = if ct == 4 {
            to8_exec(d, px_sample_exec(h, buf, off, x, y, 1))
        } else {
            match &png.trns {
                Some(t) => if gv == trns_val(t.as_slice(), 0, d) {
                    0u8
                } else {
                    255u8
                },
                None => 255u8,
            }
        };
        (g8, g8, g8, a)
    } else {
        let rv = px_sample_exec(h, buf, off, x, y, 0);
        let gv = px_sample_exec(h, buf, off, x, y, 1);
        let bv = px_sample_exec(h, buf, off, x, y, 2);
        let a = if ct == 6 {
            to8_exec(d, px_sample_exec(h, buf, off, x, y, 3))
        } else {
            match &png.trns {
                Some(t) => if rv == trns_val(t.as_slice(), 0, d) && gv == trns_val(t.as_slice(), 2, d)
                    && bv == trns_val(t.as_slice(), 4, d) {
                    0u8
                } else {
                    255u8
                },
                None => 255u8,
            }
        };
        (to8_exec(d, rv), to8_exec(d, gv), to8_exec(d, bv), a)
    };
    out[o] = r;
    out[o + 1] = g;
    out[o + 2] = b;
    out[o + 3] = a;
    proof {
        assert(r == rgba_byte(pv, imgs, x as nat, y as nat, 0));
        assert(g == rgba_byte(pv, imgs, x as nat, y as nat, 1));
        assert(b == rgba_byte(pv, imgs, x as nat, y as nat, 2));
        assert(a == rgba_byte(pv, imgs, x as nat, y as nat, 3));
        assert forall|j: int| 0 <= j < 4 implies #[trigger] out@[o + j] == rgba_byte(pv, imgs, x as nat, y as nat, j as nat) by {
            if j == 0 {
            } else if j == 1 {
            } else if j == 2 {
            } else {
            }
        }
    }
}

/// Index `4 * (y * w + x) + j` of a row-major RGBA image is byte `j` of
/// pixel `(x, y)`.
pub proof fn lemma_rgba_index(x: nat, y: nat, w: nat, j: nat)
    requires
        x < w,
        j < 4,
    ensures
        ({
            let k = 4 * (y * w + x) + j;
            &&& (k / 4) % w == x
            &&& (k / 4) / w == y
            &&& k % 4 == j
        }),
{
    let q = y * w + x;
    let k = 4 * q + j;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(k as int, 4, q as int, j as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(q as int, w as int, y as int, x as int);
}

/// The image as 8-bit RGBA (`spec::rgba8`), if it fits in `limit` bytes.
pub fn to_rgba8(png: &PngX, buf: &[u8], off: &[usize; 8], limit: usize, Tracked(m): Tracked<&mut Meter>, Tracked(a): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, crate::decode::Error>)
    requires
        png.wf(),
        bufs_ok(png.hdr.view(), buf@, off@),
    ensures
        r matches Ok(v) ==> v@ == rgba8(png.view(), imgs_of(png.hdr.view(), buf@, off@)),
        r matches Err(e) ==> e != crate::decode::Error::Invalid,
        old(a).n <= final(a).n <= old(a).n + limit,
        final(m).n + 12 * old(a).n <= old(m).n + 12 * final(a).n + 1000,
{
    let h = &png.hdr;
    let ghost pv = png.view();
    let ghost imgs = imgs_of(h.view(), buf@, off@);
    let w = h.width as u64;
    let hh = h.height as u64;
    proof {
        assert(4 * (w as u128) * (hh as u128) <= 4 * 0x7fff_ffff * 0x7fff_ffff) by (nonlinear_arith)
            requires
                w <= 0x7fff_ffff,
                hh <= 0x7fff_ffff,
        ;
    }
    if 4 * w as u128 * hh as u128 > limit as u128 {
        return Err(crate::decode::Error::TooLarge);
    }
    let n = (4 * w * hh) as usize;
    let mut out = match alloc_zeroed(n) {
        Some(v) => v,
        None => return Err(crate::decode::Error::OutOfMemory),
    };
    proof {
        a.n = (a.n + n) as nat;
        m.n = (m.n + n) as nat;
    }
    let ghost mo = m.n;
    let ghost spec_out = rgba8(pv, imgs);
    let mut y: u64 = 0;
    let mut o: usize = 0;
    proof {
        assert(4 * y * w == 0) by (nonlinear_arith)
            requires
                y == 0,
        ;
    }
    while y < hh
        invariant
            a.n == old(a).n + n,
            mo == old(m).n + n,
            4 * m.n <= 4 * mo + o + 4 * y,
            png.wf(),
            bufs_ok(h.view(), buf@, off@),
            h == &png.hdr,
            w == h.width,
            hh == h.height,
            n == 4 * w * hh,
            out@.len() == n,
            y <= hh,
            o == 4 * y * w,
            o <= n,
            spec_out.len() == n,
            spec_out == rgba8(pv, imgs),
            pv == png.view(),
            imgs == imgs_of(h.view(), buf@, off@),
            forall|i: int| 0 <= i < o ==> #[trigger] out@[i] == spec_out[i],
        decreases hh - y,
    {
        proof {
            m.n = m.n + 1;
        }
        let mut x: u64 = 0;
        proof {
            assert(4 * y * w + 4 * w <= n) by (nonlinear_arith)
                requires
                    y < hh,
                    n == 4 * w * hh,
            ;
        }
        while x < w
            invariant
                a.n == old(a).n + n,
                mo == old(m).n + n,
                4 * m.n <= 4 * mo + o + 4 * y + 4,
                png.wf(),
                bufs_ok(h.view(), buf@, off@),
                h == &png.hdr,
                w == h.width,
                hh == h.height,
                n == 4 * w * hh,
                out@.len() == n,
                y < hh,
                x <= w,
                4 * y * w + 4 * w <= n,
                o == 4 * y * w + 4 * x,
                spec_out == rgba8(pv, imgs),
                pv == png.view(),
                imgs == imgs_of(h.view(), buf@, off@),
                forall|i: int| 0 <= i < o ==> #[trigger] out@[i] == spec_out[i],
            decreases w - x,
        {
            let ghost o0 = out@;
            rgba_px(png, buf, off, x, y, out.as_mut_slice(), o);
            proof {
                assert(4 * y * w + 4 * x == 4 * (y * w + x)) by (nonlinear_arith);
                assert forall|i: int| 0 <= i < o + 4 implies #[trigger] out@[i] == spec_out[i] by {
                    if i >= o {
                        let j = (i - o) as nat;
                        lemma_rgba_index(x as nat, y as nat, w as nat, j);
                        assert(i == 4 * (y * w + x) + j);
                    } else {
                        assert(out@[i] == o0[i]);
                    }
                }
            }
            proof {
                m.n = m.n + 1;
            }
            x = x + 1;
            o = o + 4;
        }
        proof {
            assert(4 * y * w + 4 * w == 4 * (y + 1) * w) by (nonlinear_arith);
            assert(4 * (y + 1) * w <= n) by (nonlinear_arith)
                requires
                    y + 1 <= hh,
                    n == 4 * w * hh,
            ;
        }
        y = y + 1;
    }
    proof {
        assert(4 * y * w == 4 * w * hh) by (nonlinear_arith)
            requires
                y == hh,
        ;
        assert(4 * hh <= 4 * w * hh) by (nonlinear_arith)
            requires
                w >= 1,
        ;
        assert(spec_out.len() == n);
        assert(out@ =~= spec_out);
    }
    Ok(out)
}

pub proof fn lemma_pow2_add(a: nat, b: nat)
    ensures
        pow2_nat(a + b) == pow2_nat(a) * pow2_nat(b),
    decreases a,
{
    if a > 0 {
        let a1 = (a - 1) as nat;
        lemma_pow2_add(a1, b);
        assert(a1 + b + 1 == a + b);
        assert(pow2_nat(a + b) == 2 * pow2_nat(a1 + b));
        assert(pow2_nat(a) == 2 * pow2_nat(a1));
        assert(2 * (pow2_nat(a1) * pow2_nat(b)) == (2 * pow2_nat(a1)) * pow2_nat(b)) by (nonlinear_arith);
    } else {
        assert(pow2_nat(0) == 1);
        assert(a + b == b);
    }
}

/// The first `n` pixels of a packed byte fill its top `n * depth` bits:
/// the value stays below 256 and leaves room for the next pixel.
pub proof fn lemma_packed_bound(h: Ihdr, imgs: Seq<Seq<u8>>, j: nat, y: nat, n: nat)
    requires
        h.depth == 1 || h.depth == 2 || h.depth == 4,
        n * h.depth <= 8,
        forall|x: nat| x < h.w ==> #[trigger] px_sample(h, imgs, x, y, 0) < pow2_nat(h.depth),
    ensures
        packed(h, imgs, j, y, n) as nat + pow2_nat((8 - n * h.depth) as nat) <= 256,
    decreases n,
{
    reveal_with_fuel(pow2_nat, 9);
    if n > 0 {
        let t = (n - 1) as nat;
        let d = h.depth;
        assert(t * d <= 8) by (nonlinear_arith)
            requires
                n * d <= 8,
                t + 1 == n,
        ;
        lemma_packed_bound(h, imgs, j, y, t);
        let k = (8 - n * d) as nat;
        assert(n * d == t * d + d) by (nonlinear_arith)
            requires
                t + 1 == n,
        ;
        lemma_pow2_add(k, d);
        assert((8 - t * d) as nat == k + d);
        let x = j * (8nat / d) + t;
        let rest = packed(h, imgs, j, y, t);
        if x < h.w {
            let s = px_sample(h, imgs, x, y, 0);
            assert(s * pow2_nat(k) + pow2_nat(k) <= pow2_nat(d) * pow2_nat(k)) by (nonlinear_arith)
                requires
                    s < pow2_nat(d),
            ;
            assert(pow2_nat(k) >= 1) by {
                lemma_pow2_pos(k);
            }
            let v = rest as nat + s * pow2_nat(k);
            assert(pow2_nat(d) * pow2_nat(k) == pow2_nat(k + d)) by (nonlinear_arith)
                requires
                    pow2_nat(k + d) == pow2_nat(k) * pow2_nat(d),
            ;
            assert(v + pow2_nat(k) <= 256);
            assert((8 - (t + 1) * h.depth) as nat == k);
            assert(packed(h, imgs, j, y, n) as nat == v);
        } else {
            assert(pow2_nat(k) <= pow2_nat(k + d)) by {
                lemma_pow2_pos(k);
                assert(pow2_nat(d) >= 1) by {
                    lemma_pow2_pos(d);
                }
                assert(pow2_nat(k) * 1 <= pow2_nat(k) * pow2_nat(d)) by (nonlinear_arith)
                    requires
                        pow2_nat(d) >= 1,
                ;
            }
        }
    }
}

pub proof fn lemma_pow2_pos(n: nat)
    ensures
        pow2_nat(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow2_pos((n - 1) as nat);
    }
}

/// Every sample is below `2^depth`.
pub proof fn lemma_samples_bound(h: Ihdr, imgs: Seq<Seq<u8>>, y: nat)
    requires
        h.depth == 1 || h.depth == 2 || h.depth == 4,
    ensures
        forall|x: nat| x < h.w ==> #[trigger] px_sample(h, imgs, x, y, 0) < pow2_nat(h.depth),
{
    assert forall|x: nat| x < h.w implies #[trigger] px_sample(h, imgs, x, y, 0) < pow2_nat(h.depth) by {
        lemma_pow2_pos(h.depth);
    }
}

/// Byte `j` of row `y` in the image's own format (`spec::native_byte`).
pub fn native_byte_exec(h: &Header, buf: &[u8], off: &[usize; 8], j: u64, y: u64, Tracked(m): Tracked<&mut Meter>) -> (r: u8)
    requires
        bufs_ok(h.view(), buf@, off@),
        j < row_bytes(h.view(), h.view().w),
        y < h.height,
    ensures
        final(m).n <= old(m).n + 8,
        r == native_byte(h.view(), imgs_of(h.view(), buf@, off@), j as nat, y as nat),
{
    let bits = crate::geom::pixel_bits_exec(h);
    if bits >= 8 {
        native_wide(h, buf, off, j, y, bits)
    } else {
        native_packed(h, buf, off, j, y, Tracked(m))
    }
}

#[verifier::spinoff_prover]
fn native_wide(h: &Header, buf: &[u8], off: &[usize; 8], j: u64, y: u64, bits: u64) -> (r: u8)
    requires
        bufs_ok(h.view(), buf@, off@),
        j < row_bytes(h.view(), h.view().w),
        y < h.height,
        bits == pixel_bits(h.view()),
        bits >= 8,
    ensures
        r == native_byte(h.view(), imgs_of(h.view(), buf@, off@), j as nat, y as nat),
{
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let bp = bits / 8;
    let x = j / bp;
    proof {
        // `j < ceil(w * bits / 8)` and `bits` is a multiple of 8.
        crate::output::lemma_bits(hv);
        assert(bits % 8 == 0) by {
            assert(hv.depth == 8 || hv.depth == 16);
            assert(bits == channels(hv.ct) * hv.depth);
            assert((channels(hv.ct) * hv.depth) % 8 == 0) by (nonlinear_arith)
                requires
                    hv.depth == 8 || hv.depth == 16,
            ;
        }
        assert(row_bytes(hv, hv.w) == hv.w * bp) by {
            assert(hv.w * bits == 8 * (hv.w * bp)) by (nonlinear_arith)
                requires
                    bits == 8 * bp,
            ;
        }
        vstd::arithmetic::div_mod::lemma_div_is_ordered(j as int, (hv.w * bp - 1) as int, bp as int);
        assert((hv.w * bp - 1) / (bp as int) < hv.w) by {
            vstd::arithmetic::div_mod::lemma_div_by_multiple(hv.w as int, bp as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered((hv.w * bp - 1) as int, (hv.w * bp) as int, bp as int);
            assert((hv.w * bp - 1) / (bp as int) != hv.w) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod((hv.w * bp - 1) as int, bp as int);
                assert(bp * hv.w > hv.w * bp - 1) by (nonlinear_arith);
                if (hv.w * bp - 1) / (bp as int) == hv.w {
                    assert(bp * ((hv.w * bp - 1) / (bp as int)) <= hv.w * bp - 1);
                    assert(bp * hv.w <= hv.w * bp - 1);
                }
            }
        }
        assert(x < h.width);
    }
    let p = pass_of_exec(h.interlace, x, y);
    proof {
        crate::geom::lemma_params_any(hv, h.interlace as nat, p as nat);
        lemma_in_pass(hv, x as nat, y as nat);
        lemma_pass_of(hv, x as nat, y as nat);
    }
    let (_, _, dx, dy) = crate::geom::pass_params(h.interlace, p);
    let (pw, ph) = crate::geom::pass_dims(h, p);
    let rb = crate::geom::row_bytes_exec(h, pw);
    let sx = x / dx;
    let sy = y / dy;
    proof {
        crate::passes::lemma_off_mono(hv, (p + 1) as nat, npasses(hv));
        assert(img_size(hv, p as nat) == ph * rb);
        assert(row_bytes(hv, pw as nat) == pw * bp) by {
            assert(pw * bits == 8 * (pw * bp)) by (nonlinear_arith)
                requires
                    bits == 8 * bp,
            ;
        }
        assert(sy * rb + sx * bp + j % bp < ph * rb) by (nonlinear_arith)
            requires
                sy < ph,
                sx < pw,
                rb == pw * bp,
                j % bp < bp,
        ;
        assert(imgs[p as int] == buf@.subrange(off@[p as int] as int, off@[p as int] + ph * rb));
        // Below `off[p + 1]`, a usize: the cast and the sum keep the value on
        // 32-bit targets too.
        assert(off@[p + 1] == off@[p as int] + ph * rb);
    }
    buf[off[p as usize] + (sy * rb + sx * bp + j % bp) as usize]
}

/// One more pixel of a packed byte.
proof fn lemma_packed_step(h: Ihdr, imgs: Seq<Seq<u8>>, j: nat, y: nat, t: nat, acc: nat)
    requires
        h.depth == 1 || h.depth == 2 || h.depth == 4,
        (t + 1) * h.depth <= 8,
        acc == packed(h, imgs, j, y, t) as nat,
        forall|x: nat| x < h.w ==> #[trigger] px_sample(h, imgs, x, y, 0) < pow2_nat(h.depth),
    ensures
        ({
            let x = j * (8nat / h.depth) + t;
            let k = (8 - (t + 1) * h.depth) as nat;
            &&& x < h.w ==> acc + px_sample(h, imgs, x, y, 0) * pow2_nat(k) < 256
                && packed(h, imgs, j, y, t + 1) as nat == acc + px_sample(h, imgs, x, y, 0) * pow2_nat(k)
            &&& x >= h.w ==> packed(h, imgs, j, y, t + 1) as nat == acc
        }),
{
    let d = h.depth;
    let k = (8 - (t + 1) * d) as nat;
    assert(t * d <= 8) by (nonlinear_arith)
        requires
            (t + 1) * d <= 8,
    ;
    lemma_packed_bound(h, imgs, j, y, t);
    let x = j * (8nat / d) + t;
    if x < h.w {
        let s = px_sample(h, imgs, x, y, 0);
        assert(s * pow2_nat(k) + pow2_nat(k) <= pow2_nat(d) * pow2_nat(k)) by (nonlinear_arith)
            requires
                s < pow2_nat(d),
        ;
        lemma_pow2_add(k, d);
        assert((8 - t * d) as nat == k + d) by (nonlinear_arith)
            requires
                k == 8 - (t + 1) * d,
                (t + 1) * d <= 8,
        ;
        lemma_pow2_pos(k);
        assert(pow2_nat(k) * pow2_nat(d) == pow2_nat(d) * pow2_nat(k)) by (nonlinear_arith);
    }
}

#[verifier::spinoff_prover]
fn native_packed(h: &Header, buf: &[u8], off: &[usize; 8], j: u64, y: u64, Tracked(m): Tracked<&mut Meter>) -> (r: u8)
    requires
        bufs_ok(h.view(), buf@, off@),
        j < row_bytes(h.view(), h.view().w),
        y < h.height,
        pixel_bits(h.view()) < 8,
    ensures
        final(m).n <= old(m).n + 8,
        r == native_byte(h.view(), imgs_of(h.view(), buf@, off@), j as nat, y as nat),
{
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let d = h.bit_depth as u64;
    let per = 8 / d;
    let mut acc: u64 = 0;
    let mut t: u64 = 0;
    proof {
        reveal_with_fuel(pow2_nat, 9);
        assert(hv.ct == 0 || hv.ct == 3);
        assert(d == 1 || d == 2 || d == 4);
        lemma_samples_bound(hv, imgs, y as nat);
        assert(per * d == 8);
        crate::geom::lemma_row_bytes_bound(hv, hv.w);
        lemma_pow2_shift(d);
    }
    let ghost m0 = m.n;
    while t < per
        invariant
            m0 == old(m).n,
            m.n <= m0 + t,
            bufs_ok(hv, buf@, off@),
            hv == h.view(),
            imgs == imgs_of(hv, buf@, off@),
            d == hv.depth,
            d == 1 || d == 2 || d == 4,
            pow2_nat(d as nat) <= 256,
            per == 8u64 / d,
            per * d == 8,
            t <= per,
            y < h.height,
            j < row_bytes(hv, hv.w),
            row_bytes(hv, hv.w) <= 0x4_0000_0000,
            acc == packed(hv, imgs, j as nat, y as nat, t as nat) as nat,
            forall|x: nat| x < hv.w ==> #[trigger] px_sample(hv, imgs, x, y as nat, 0) < pow2_nat(hv.depth),
        decreases per - t,
    {
        proof {
            assert((t + 1) * d <= 8) by (nonlinear_arith)
                requires
                    t < per,
                    per * d == 8,
            ;
            lemma_packed_step(hv, imgs, j as nat, y as nat, t as nat, acc as nat);
            assert(j * per + t <= 0x4_0000_0000 * 8 + 8) by (nonlinear_arith)
                requires
                    j < 0x4_0000_0000,
                    per <= 8,
                    t < per,
            ;
            assert(per == 8nat / hv.depth);
        }
        let x = j * per + t;
        if x < h.width as u64 {
            let s = px_sample_exec(h, buf, off, x, y, 0);
            let sh = 8 - (t + 1) * d;
            proof {
                lemma_pow2_shift(sh);
                assert(s << sh == s * (1u64 << sh)) by (bit_vector)
                    requires
                        s < 256,
                        sh <= 8,
                ;
            }
            acc = acc + (s << sh);
        }
        proof {
            m.n = m.n + 1;
        }
        t = t + 1;
    }
    proof {
        assert(per == 8nat / hv.depth);
    }
    acc as u8
}

/// The image in its own format (`spec::native`), if it fits in `limit`
/// bytes.
pub fn to_native(h: &Header, buf: &[u8], off: &[usize; 8], limit: usize, Tracked(m): Tracked<&mut Meter>, Tracked(a): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, crate::decode::Error>)
    requires
        bufs_ok(h.view(), buf@, off@),
    ensures
        r matches Ok(v) ==> v@ == native(h.view(), imgs_of(h.view(), buf@, off@)),
        r matches Err(e) ==> e != crate::decode::Error::Invalid,
        old(a).n <= final(a).n <= old(a).n + limit,
        final(m).n + 12 * old(a).n <= old(m).n + 12 * final(a).n + 1000,
{
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let rb = crate::geom::row_bytes_exec(h, h.width as u64);
    let hh = h.height as u64;
    proof {
        assert(rb * hh <= 0x4_0000_0000 * 0x7fff_ffff) by (nonlinear_arith)
            requires
                rb <= 0x4_0000_0000,
                hh <= 0x7fff_ffff,
        ;
    }
    if rb as u128 * hh as u128 > limit as u128 {
        return Err(crate::decode::Error::TooLarge);
    }
    let n = (rb * hh) as usize;
    let mut out = match alloc_zeroed(n) {
        Some(v) => v,
        None => return Err(crate::decode::Error::OutOfMemory),
    };
    proof {
        a.n = (a.n + n) as nat;
        m.n = (m.n + n) as nat;
    }
    let ghost mo = m.n;
    let ghost spec_out = native(hv, imgs);
    let mut y: u64 = 0;
    let mut o: usize = 0;
    proof {
        assert(y * rb == 0) by (nonlinear_arith)
            requires
                y == 0,
        ;
    }
    while y < hh
        invariant
            a.n == old(a).n + n,
            mo == old(m).n + n,
            m.n <= mo + 9 * o + y,
            bufs_ok(hv, buf@, off@),
            hv == h.view(),
            imgs == imgs_of(hv, buf@, off@),
            rb == row_bytes(hv, hv.w),
            hh == h.height,
            n == rb * hh,
            out@.len() == n,
            y <= hh,
            o == y * rb,
            o <= n,
            spec_out.len() == n,
            spec_out == native(hv, imgs),
            forall|i: int| 0 <= i < o ==> #[trigger] out@[i] == spec_out[i],
        decreases hh - y,
    {
        proof {
            m.n = m.n + 1;
        }
        let mut j: u64 = 0;
        proof {
            assert(y * rb + rb <= n) by (nonlinear_arith)
                requires
                    y < hh,
                    n == rb * hh,
            ;
        }
        while j < rb
            invariant
                a.n == old(a).n + n,
                mo == old(m).n + n,
                m.n <= mo + 9 * o + y + 1,
                bufs_ok(hv, buf@, off@),
                hv == h.view(),
                imgs == imgs_of(hv, buf@, off@),
                rb == row_bytes(hv, hv.w),
                hh == h.height,
                n == rb * hh,
                out@.len() == n,
                y < hh,
                j <= rb,
                y * rb + rb <= n,
                o == y * rb + j,
                spec_out.len() == n,
                spec_out == native(hv, imgs),
                forall|i: int| 0 <= i < o ==> #[trigger] out@[i] == spec_out[i],
            decreases rb - j,
        {
            proof {
                m.n = m.n + 1;
            }
            let v = native_byte_exec(h, buf, off, j, y, Tracked(m));
            out.set(o, v);
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(o as int, rb as int, y as int, j as int);
            }
            j = j + 1;
            o = o + 1;
        }
        proof {
            assert(y * rb + rb == (y + 1) * rb) by (nonlinear_arith);
        }
        y = y + 1;
    }
    proof {
        assert(y * rb == rb * hh) by (nonlinear_arith)
            requires
                y == hh,
        ;
        assert(hh <= rb * hh) by (nonlinear_arith)
            requires
                rb >= 1,
        ;
        assert(out@ =~= spec_out);
    }
    Ok(out)
}

} // verus!
