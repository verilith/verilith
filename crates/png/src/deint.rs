//! Deinterlacing whole-byte pixels row by row (`spec::native` for an
//! interlaced image whose pixels are 8 or more bits). Odd rows come whole
//! from pass 7; even rows take each pixel from its pass with shifts in
//! place of divisions.
use crate::chunks::Header;
use crate::geom::*;
use crate::output::*;
use crate::passes::*;
use crate::prims::*;
use crate::spec::*;
use crate::work::Meter;
use vstd::prelude::*;

verus! {

/// Byte `k` of pixel `(x, y)` of the native image, from its pass.
pub proof fn lemma_native_at(h: Ihdr, imgs: Seq<Seq<u8>>, x: nat, y: nat, k: nat)
    requires
        hdr_ok(h),
        pixel_bits(h) >= 8,
        x < h.w,
        y < h.h,
        k < pixel_bits(h) / 8,
    ensures
        ({
            let bp = pixel_bits(h) / 8;
            let rb = row_bytes(h, h.w);
            let p = pass_of(h, x, y);
            &&& rb == h.w * bp
            &&& native(h, imgs).len() == rb * h.h
            &&& y * rb + x * bp + k < rb * h.h
            &&& native(h, imgs)[(y * rb + x * bp + k) as int] == imgs[p as int][((y / dy(h, p)) * row_bytes(
                h,
                pass_w(h, p),
            ) + (x / dx(h, p)) * bp + k) as int]
        }),
{
    let bits = pixel_bits(h);
    let bp = bits / 8;
    lemma_bits(h);
    assert(bits % 8 == 0) by {
        assert(h.depth == 8 || h.depth == 16);
        assert((channels(h.ct) * h.depth) % 8 == 0) by (nonlinear_arith)
            requires
                h.depth == 8 || h.depth == 16,
        ;
    }
    let rb = row_bytes(h, h.w);
    assert(h.w * bits + 7 == (h.w * bp) * 8 + 7) by (nonlinear_arith)
        requires
            bits == bp * 8,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((h.w * bp * 8 + 7) as int, 8, (h.w * bp) as int, 7);
    assert(rb == h.w * bp);
    let j = x * bp + k;
    assert(j < rb) by (nonlinear_arith)
        requires
            x < h.w,
            k < bp,
            rb == h.w * bp,
            j == x * bp + k,
    ;
    let i = y * rb + j;
    assert(i < rb * h.h) by (nonlinear_arith)
        requires
            y < h.h,
            j < rb,
            i == y * rb + j,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i as int, rb as int, y as int, j as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j as int, bp as int, x as int, k as int);
    assert(native(h, imgs)[i as int] == native_byte(h, imgs, j, y));
}

/// Pass `p`'s spacing as a shift: `dx(p) == 2^sx(p)`, `dy(p) == 2^sy(p)`.
pub open spec fn pw2(s: nat) -> nat {
    if s == 0 {
        1
    } else if s == 1 {
        2
    } else if s == 2 {
        4
    } else {
        8
    }
}

proof fn lemma_shr(v: u64, s: u64)
    requires
        s <= 3,
    ensures
        (v >> s) as nat == v as nat / pw2(s as nat),
{
    if s == 0 {
        assert(v >> 0u64 == v) by (bit_vector);
        assert(pw2(0) == 1);
        assert(v >> s == v >> 0u64);
    } else if s == 1 {
        assert(v >> 1u64 == v / 2) by (bit_vector);
        assert(v >> s == v >> 1u64);
    } else if s == 2 {
        assert(v >> 2u64 == v / 4) by (bit_vector);
        assert(v >> s == v >> 2u64);
    } else {
        assert(v >> 3u64 == v / 8) by (bit_vector);
        assert(v >> s == v >> 3u64);
    }
}

/// What the row loops need about the passes.
pub open spec fn tables_ok(h: Ihdr, buf: Seq<u8>, off: Seq<usize>, rbs: Seq<usize>, sx: Seq<u64>, sy: Seq<u64>) -> bool {
    &&& bufs_ok(h, buf, off)
    &&& h.interlace == 1
    &&& pixel_bits(h) >= 8
    &&& rbs.len() == 7 && sx.len() == 7 && sy.len() == 7
    &&& forall|p: int| 0 <= p < 7 ==> #[trigger] rbs[p] == row_bytes(h, pass_w(h, p as nat))
    &&& forall|p: int| 0 <= p < 7 ==> #[trigger] sx[p] <= 3 && pw2(sx[p] as nat) == dx(h, p as nat)
    &&& forall|p: int| 0 <= p < 7 ==> #[trigger] sy[p] <= 3 && pw2(sy[p] as nat) == dy(h, p as nat)
}

/// Where pixel `(x, y)`'s byte 0 is in the buffer.
#[inline(always)]
fn src_of(
    h: &Header,
    buf: &[u8],
    off: &[usize; 8],
    rbs: &[usize; 7],
    sx: &[u64; 7],
    sy: &[u64; 7],
    bp: usize,
    x: u64,
    y: u64,
) -> (r: usize)
    requires
        tables_ok(h.view(), buf@, off@, rbs@, sx@, sy@),
        bp == pixel_bits(h.view()) / 8,
        x < h.width,
        y < h.height,
    ensures
        ({
            let hv = h.view();
            let p = pass_of(hv, x as nat, y as nat);
            let imgs = imgs_of(hv, buf@, off@);
            let i = (y as nat / dy(hv, p)) * row_bytes(hv, pass_w(hv, p)) + (x as nat / dx(hv, p)) * bp;
            &&& r + bp <= buf@.len()
            &&& forall|k: int| 0 <= k < bp ==> #[trigger] buf@[r + k] == imgs[p as int][i + k]
        }),
{
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let p = pass_of_exec(1, x, y);
    proof {
        lemma_params_any(hv, 1, p as nat);
        lemma_in_pass(hv, x as nat, y as nat);
        lemma_pass_of(hv, x as nat, y as nat);
        lemma_bits(hv);
        lemma_shr(x, sx@[p as int]);
        lemma_shr(y, sy@[p as int]);
    }
    let qx = x >> sx[p as usize];
    let qy = y >> sy[p as usize];
    let rbp = rbs[p as usize];
    proof {
        let pw = pass_w(hv, p as nat);
        let ph = pass_h(hv, p as nat);
        let bits = pixel_bits(hv);
        assert(bits % 8 == 0) by {
            assert(hv.depth == 8 || hv.depth == 16);
            assert((channels(hv.ct) * hv.depth) % 8 == 0) by (nonlinear_arith)
                requires
                    hv.depth == 8 || hv.depth == 16,
            ;
        }
        assert(pw * bits + 7 == (pw * bp) * 8 + 7) by (nonlinear_arith)
            requires
                bits == bp * 8,
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((pw * bp * 8 + 7) as int, 8, (pw * bp) as int, 7);
        assert(rbp == pw * bp);
        crate::passes::lemma_off_mono(hv, (p + 1) as nat, npasses(hv));
        assert(img_size(hv, p as nat) == ph * rbp);
        assert(qy * rbp + qx * bp + bp <= ph * rbp) by (nonlinear_arith)
            requires
                qy < ph,
                qx < pw,
                rbp == pw * bp,
        ;
        assert(imgs[p as int] == buf@.subrange(off@[p as int] as int, off@[p as int] + ph * rbp));
        assert(pw <= hv.w && ph <= hv.h) by {
            crate::geom::lemma_ceil_div(hv.w as int, x0(hv, p as nat) as int, dx(hv, p as nat) as int);
            crate::geom::lemma_ceil_div(hv.h as int, y0(hv, p as nat) as int, dy(hv, p as nat) as int);
        }
        assert(rbp <= 0x4_0000_0000) by {
            crate::geom::lemma_row_bytes_bound(hv, pw);
        }
        assert(qy * rbp <= 0x7fff_ffff * 0x4_0000_0000) by (nonlinear_arith)
            requires
                qy < ph,
                ph <= 0x7fff_ffff,
                rbp <= 0x4_0000_0000,
        ;
    }
    off[p as usize] + qy as usize * rbp + qx as usize * bp
}

/// Even row `y`: each pixel from its pass.
#[inline(always)]
fn even_row(
    h: &Header,
    buf: &[u8],
    off: &[usize; 8],
    rbs: &[usize; 7],
    sx: &[u64; 7],
    sy: &[u64; 7],
    bp: usize,
    y: u64,
    out: &mut [u8],
    Ghost(goal): Ghost<Seq<u8>>,
    Tracked(m): Tracked<&mut Meter>,
)
    requires
        tables_ok(h.view(), buf@, off@, rbs@, sx@, sy@),
        bp == pixel_bits(h.view()) / 8,
        y < h.height,
        goal == native(h.view(), imgs_of(h.view(), buf@, off@)),
        old(out)@.len() == goal.len(),
        forall|i: int| 0 <= i < y * row_bytes(h.view(), h.view().w) ==> #[trigger] old(out)@[i] == goal[i],
    ensures
        final(m).n <= old(m).n + 2 * row_bytes(h.view(), h.view().w),
        final(out)@.len() == goal.len(),
        forall|i: int| 0 <= i < (y + 1) * row_bytes(h.view(), h.view().w) ==> #[trigger] final(out)@[i] == goal[i],
{
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let ghost rb = row_bytes(hv, hv.w);
    let w = h.width as u64;
    proof {
        lemma_native_at(hv, imgs, 0, y as nat, 0);
        lemma_bits(hv);
    }
    let _ = out.len();
    let _ = buf.len();
    proof {
        assert(w * bp <= rb);
        assert(y * rb + rb <= rb * hv.h) by (nonlinear_arith)
            requires
                y < hv.h,
        ;
        assert(y * (w * bp) == y * rb);
    }
    let mut o: usize = (y as usize) * (w as usize * bp);
    let mut x: u64 = 0;
    let ghost mr = m.n;
    while x < w
        invariant
            mr == old(m).n,
            m.n + y * rb <= mr + o + x,
            tables_ok(h.view(), buf@, off@, rbs@, sx@, sy@),
            hv == h.view(),
            imgs == imgs_of(hv, buf@, off@),
            rb == row_bytes(hv, hv.w),
            rb == hv.w * bp,
            w == h.width,
            bp == pixel_bits(hv) / 8,
            1 <= bp <= 8,
            y < h.height,
            goal == native(hv, imgs),
            out@.len() == goal.len(),
            goal.len() == rb * hv.h,
            out@.len() <= usize::MAX,
            buf@.len() <= usize::MAX,
            x <= w,
            o == y * rb + x * bp,
            forall|i: int| 0 <= i < o ==> #[trigger] out@[i] == goal[i],
        decreases w - x,
    {
        let s = src_of(h, buf, off, rbs, sx, sy, bp, x, y);
        proof {
            assert(y * rb + x * bp + bp <= rb * hv.h) by (nonlinear_arith)
                requires
                    x < hv.w,
                    y < hv.h,
                    rb == hv.w * bp,
            ;
        }
        proof {
            m.n = m.n + 1;
        }
        let mut k: usize = 0;
        while k < bp
            invariant
                mr == old(m).n,
                m.n + y * rb <= mr + o + k + x + 1,
                tables_ok(h.view(), buf@, off@, rbs@, sx@, sy@),
                hv == h.view(),
                imgs == imgs_of(hv, buf@, off@),
                rb == row_bytes(hv, hv.w),
                rb == hv.w * bp,
                bp == pixel_bits(hv) / 8,
                x < w,
                w == h.width,
                y < h.height,
                goal == native(hv, imgs),
                out@.len() == goal.len(),
                goal.len() == rb * hv.h,
                o == y * rb + x * bp,
                o + bp <= goal.len(),
                out@.len() <= usize::MAX,
                buf@.len() <= usize::MAX,
                s + bp <= buf@.len(),
                k <= bp,
                forall|kk: int| 0 <= kk < bp ==> #[trigger] buf@[s + kk] == imgs[pass_of(hv, x as nat, y as nat) as int][(
                y as nat / dy(hv, pass_of(hv, x as nat, y as nat))) * row_bytes(hv, pass_w(hv, pass_of(hv, x as nat, y as nat)))
                    + (x as nat / dx(hv, pass_of(hv, x as nat, y as nat))) * bp + kk],
                forall|i: int| 0 <= i < o + k ==> #[trigger] out@[i] == goal[i],
            decreases bp - k,
        {
            proof {
                lemma_native_at(hv, imgs, x as nat, y as nat, k as nat);
            }
            set(out, o + k, get(buf, s + k));
            proof {
                m.n = m.n + 1;
            }
            k = k + 1;
        }
        proof {
            assert(y * rb + x * bp + bp == y * rb + (x + 1) * bp) by (nonlinear_arith);
        }
        x = x + 1;
        o = o + bp;
    }
    proof {
        assert(y * rb + w * bp == (y + 1) * rb) by (nonlinear_arith)
            requires
                rb == w * bp,
        ;
        assert(w <= rb) by (nonlinear_arith)
            requires
                rb == w * bp,
                bp >= 1,
        ;
    }
}

/// Row `y / 2` of pass 7 is a whole output row, in the buffer at
/// `off[6] + (y / 2) * rb`.
#[verifier::spinoff_prover]
proof fn lemma_odd_src(h: Ihdr, buf: Seq<u8>, off: Seq<usize>, rbs: Seq<usize>, sx: Seq<u64>, sy: Seq<u64>, y: nat)
    requires
        tables_ok(h, buf, off, rbs, sx, sy),
        y < h.h,
        y % 2 == 1,
    ensures
        ({
            let rb = row_bytes(h, h.w);
            let s = off[6] + (y / 2) * rb;
            &&& rbs[6] == rb
            &&& rb == h.w * (pixel_bits(h) / 8)
            &&& (y / 2) * rb <= 0x7fff_ffff * 0x4_0000_0000
            &&& s + rb <= buf.len()
            &&& forall|j: int| 0 <= j < rb ==> #[trigger] buf[s + j] == imgs_of(h, buf, off)[6][(y / 2) * rb + j]
        }),
{
    let imgs = imgs_of(h, buf, off);
    let rb = row_bytes(h, h.w);
    let bp = pixel_bits(h) / 8;
    lemma_params_any(h, 1, 6);
    lemma_bits(h);
    lemma_native_at(h, imgs, 0, y, 0);
    assert(x0(h, 6) == 0 && dx(h, 6) == 1 && y0(h, 6) == 1 && dy(h, 6) == 2);
    assert(pass_w(h, 6) == h.w) by {
        assert((h.w + 1 - 1) as nat / 1 == h.w);
    }
    assert(rbs[6] == rb);
    let ph = pass_h(h, 6);
    assert(y / 2 < ph) by {
        assert(ph == (h.h as nat) / 2);
        assert(y / 2 < (h.h as nat) / 2) by (nonlinear_arith)
            requires
                y < h.h,
                y % 2 == 1,
        ;
    }
    crate::passes::lemma_off_mono(h, 7, npasses(h));
    assert(pass_size(h, 6) > 0) by {
        assert(ph >= 1 && h.w >= 1);
        assert(ph * (1 + rb) >= 1) by (nonlinear_arith)
            requires
                ph >= 1,
        ;
    }
    assert(img_size(h, 6) == ph * rb);
    assert((y / 2) * rb + rb <= ph * rb) by (nonlinear_arith)
        requires
            (y / 2) < ph,
    ;
    assert(imgs[6] == buf.subrange(off[6] as int, off[6] + ph * rb));
    assert(rb <= 0x4_0000_0000) by {
        crate::geom::lemma_row_bytes_bound(h, h.w);
    }
    assert((y / 2) * rb <= 0x7fff_ffff * 0x4_0000_0000) by (nonlinear_arith)
        requires
            y / 2 < ph,
            ph <= 0x7fff_ffff,
            rb <= 0x4_0000_0000,
    ;
}

/// Odd row `y`: the whole row is row `y / 2` of pass 7.
#[inline(always)]
fn odd_row(
    h: &Header,
    buf: &[u8],
    off: &[usize; 8],
    rbs: &[usize; 7],
    sx: &[u64; 7],
    sy: &[u64; 7],
    bp: usize,
    y: u64,
    out: &mut [u8],
    Ghost(goal): Ghost<Seq<u8>>,
    Tracked(m): Tracked<&mut Meter>,
)
    requires
        tables_ok(h.view(), buf@, off@, rbs@, sx@, sy@),
        bp == pixel_bits(h.view()) / 8,
        y < h.height,
        y % 2 == 1,
        goal == native(h.view(), imgs_of(h.view(), buf@, off@)),
        old(out)@.len() == goal.len(),
        forall|i: int| 0 <= i < y * row_bytes(h.view(), h.view().w) ==> #[trigger] old(out)@[i] == goal[i],
    ensures
        final(m).n <= old(m).n + 2 * row_bytes(h.view(), h.view().w),
        final(out)@.len() == goal.len(),
        forall|i: int| 0 <= i < (y + 1) * row_bytes(h.view(), h.view().w) ==> #[trigger] final(out)@[i] == goal[i],
{
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let ghost rb = row_bytes(hv, hv.w);
    let w = h.width as u64;
    proof {
        lemma_native_at(hv, imgs, 0, y as nat, 0);
        lemma_odd_src(hv, buf@, off@, rbs@, sx@, sy@, y as nat);
        lemma_shr(y, 1);
        lemma_params_any(hv, 1, 6);
        assert(y * rb + rb <= rb * hv.h) by (nonlinear_arith)
            requires
                y < hv.h,
        ;
        assert(y * rb + rb == (y + 1) * rb) by (nonlinear_arith);
    }
    let _ = out.len();
    let _ = buf.len();
    // The whole row is row `y / 2` of pass 7.
    let s = off[6] + (y >> 1) as usize * rbs[6];
    let n = w as usize * bp;
    let o = y as usize * n;
    let ghost o0 = out@;
    proof {
        m.n = (m.n + n) as nat;
    }
    copy(out, o, buf, s, n);
    proof {
        assert forall|i: int| 0 <= i < (y + 1) * rb implies #[trigger] out@[i] == goal[i] by {
            if i >= o {
                let j = (i - o) as nat;
                let x = j / (bp as nat);
                let k = j % (bp as nat);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j as int, bp as int);
                assert(j < rb) by (nonlinear_arith)
                    requires
                        i < (y + 1) * rb,
                        i == y * rb + j,
                ;
                assert(x < hv.w) by (nonlinear_arith)
                    requires
                        j == bp * x + k,
                        j < rb,
                        rb == hv.w * bp,
                        bp >= 1,
                ;
                lemma_pass_of(hv, x, y as nat);
                lemma_native_at(hv, imgs, x, y as nat, k);
                assert(x / 1 == x);
                assert(j == x * bp + k) by (nonlinear_arith)
                    requires
                        j == bp * x + k,
                ;
                assert(pass_of(hv, x, y as nat) == 6);
                assert(pass_w(hv, 6) == hv.w);
                assert(out@[i] == buf@[s + j]);
                assert(buf@[s + j] == imgs[6][(y / 2) * rb + j]);
            } else {
                assert(out@[i] == o0[i]);
            }
        }
    }
}

/// A pass's row of whole-byte pixels is no longer than a row of the image.
proof fn lemma_pass_row_le(hv: Ihdr, p: nat, bp: nat)
    requires
        hdr_ok(hv),
        hv.interlace == 1,
        p < 7,
        pixel_bits(hv) == 8 * bp,
    ensures
        row_bytes(hv, pass_w(hv, p)) <= hv.w * bp,
{
    let pw = pass_w(hv, p);
    let d = dx(hv, p);
    assert(1 <= d <= 8);
    if hv.w > x0(hv, p) {
        let t = (hv.w - x0(hv, p) + d - 1) as nat;
        assert(t <= hv.w * d) by (nonlinear_arith)
            requires
                t <= hv.w + d - 1,
                hv.w >= 1,
                d >= 1,
        ;
        vstd::arithmetic::div_mod::lemma_div_is_ordered(t as int, (hv.w * d) as int, d as int);
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(hv.w as int, d as int);
    }
    assert(pw <= hv.w);
    assert((pw * (8 * bp) + 7) / 8 == pw * bp) by (nonlinear_arith);
    assert(pw * bp <= hv.w * bp) by (nonlinear_arith)
        requires
            pw <= hv.w,
    ;
}

/// `spec::native` of an interlaced image of whole-byte pixels.
#[verifier::spinoff_prover]
pub fn deinterlace(h: &Header, buf: &[u8], off: &[usize; 8], limit: usize, Tracked(m): Tracked<&mut Meter>, Tracked(a): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, crate::decode::Error>)
    requires
        bufs_ok(h.view(), buf@, off@),
        h.view().interlace == 1,
        pixel_bits(h.view()) >= 8,
    ensures
        r matches Ok(v) ==> v@ == native(h.view(), imgs_of(h.view(), buf@, off@)),
        r matches Err(e) ==> e != crate::decode::Error::Invalid,
        old(a).n <= final(a).n <= old(a).n + limit,
        final(m).n + 12 * old(a).n <= old(m).n + 12 * final(a).n + 1000,
{
    let ghost hv = h.view();
    let ghost imgs = imgs_of(hv, buf@, off@);
    let ghost goal = native(hv, imgs);
    let bp = (crate::geom::pixel_bits_exec(h) / 8) as usize;
    let w = h.width as u64;
    let hh = h.height as u64;
    proof {
        lemma_bits(hv);
        lemma_native_at(hv, imgs, 0, 0, 0);
        assert(w * bp * hh <= 0x7fff_ffff * 8 * 0x7fff_ffff) by (nonlinear_arith)
            requires
                w <= 0x7fff_ffff,
                bp <= 8,
                hh <= 0x7fff_ffff,
        ;
        assert(w * bp <= 0x7fff_ffff * 8) by (nonlinear_arith)
            requires
                w <= 0x7fff_ffff,
                bp <= 8,
        ;
    }
    if (w * bp as u64) as u128 * hh as u128 > limit as u128 {
        return Err(crate::decode::Error::TooLarge);
    }
    proof {
        // Each partial product is at most `limit`, so fits a usize.
        assert(w * bp <= w * bp * hh) by (nonlinear_arith)
            requires
                hh >= 1,
        ;
        // Whole-byte pixels: a depth of 8 or 16.
        assert(hv.depth == 8 || hv.depth == 16) by {
            if hv.depth < 8 {
                assert(channels(hv.ct) == 1);
            }
        }
        assert(pixel_bits(hv) == 8 * bp) by (nonlinear_arith)
            requires
                pixel_bits(hv) == channels(hv.ct) * hv.depth,
                hv.depth == 8 || hv.depth == 16,
                bp == pixel_bits(hv) / 8,
        ;
    }
    let n = (w as usize * bp) * hh as usize;
    let mut out = match alloc_zeroed(n) {
        Some(v) => v,
        None => return Err(crate::decode::Error::OutOfMemory),
    };
    proof {
        a.n = (a.n + n) as nat;
        m.n = (m.n + n) as nat;
    }
    let ghost mo = m.n;
    let ghost a1 = a.n;
    let mut rbs: [usize; 7] = [0; 7];
    let sx: [u64; 7] = [3, 3, 2, 2, 1, 1, 0];
    let sy: [u64; 7] = [3, 3, 3, 2, 2, 1, 1];
    let mut p: u64 = 0;
    while p < 7
        invariant
            m.n == mo + p,
            a.n == a1,
            bufs_ok(hv, buf@, off@),
            hv == h.view(),
            hv.interlace == 1,
            p <= 7,
            rbs@.len() == 7,
            forall|q: int| 0 <= q < p ==> #[trigger] rbs@[q] == row_bytes(hv, pass_w(hv, q as nat)),
            pixel_bits(hv) == 8 * bp,
            w == hv.w,
            w * bp <= limit,
        decreases 7 - p,
    {
        let (pw, _) = crate::geom::pass_dims(h, p);
        proof {
            // At most `limit`, so the cast keeps it on 32-bit targets too.
            lemma_pass_row_le(hv, p as nat, bp as nat);
            assert(p as usize == p);
        }
        rbs[p as usize] = crate::geom::row_bytes_exec(h, pw) as usize;
        proof {
            m.n = m.n + 1;
        }
        p = p + 1;
    }
    proof {
        assert forall|q: int| 0 <= q < 7 implies #[trigger] sx@[q] <= 3 && pw2(sx@[q] as nat) == dx(hv, q as nat) by {}
        assert forall|q: int| 0 <= q < 7 implies #[trigger] sy@[q] <= 3 && pw2(sy@[q] as nat) == dy(hv, q as nat) by {}
    }
    let ghost my = m.n;
    let mut y: u64 = 0;
    while y < hh
        invariant
            my == mo + 7,
            a.n == a1,
            m.n <= my + 2 * (y * row_bytes(hv, hv.w)) + y,
            tables_ok(hv, buf@, off@, rbs@, sx@, sy@),
            hv == h.view(),
            hh == h.height,
            imgs == imgs_of(hv, buf@, off@),
            goal == native(hv, imgs),
            bp == pixel_bits(hv) / 8,
            out@.len() == goal.len(),
            y <= hh,
            forall|i: int| 0 <= i < y * row_bytes(hv, hv.w) ==> #[trigger] out@[i] == goal[i],
        decreases hh - y,
    {
        proof {
            m.n = m.n + 1;
            assert((y + 1) * row_bytes(hv, hv.w) == y * row_bytes(hv, hv.w) + row_bytes(hv, hv.w)) by (nonlinear_arith);
        }
        if y % 2 == 1 {
            odd_row_dispatch(h, buf, off, &rbs, &sx, &sy, bp, y, out.as_mut_slice(), Ghost(goal), Tracked(m));
        } else {
            even_row_dispatch(h, buf, off, &rbs, &sx, &sy, bp, y, out.as_mut_slice(), Ghost(goal), Tracked(m));
        }
        y = y + 1;
    }
    proof {
        lemma_native_at(hv, imgs, 0, 0, 0);
        assert(y * row_bytes(hv, hv.w) == goal.len()) by (nonlinear_arith)
            requires
                y == hv.h,
                goal.len() == row_bytes(hv, hv.w) * hv.h,
        ;
        assert(out@ =~= goal);
        assert(hh <= y * row_bytes(hv, hv.w)) by (nonlinear_arith)
            requires
                y == hh,
                row_bytes(hv, hv.w) >= 1,
        ;
    }
    Ok(out)
}

/// `odd_row` with the pixel size a constant.
fn odd_row_dispatch(
    h: &Header,
    buf: &[u8],
    off: &[usize; 8],
    rbs: &[usize; 7],
    sx: &[u64; 7],
    sy: &[u64; 7],
    bp: usize,
    y: u64,
    out: &mut [u8],
    Ghost(goal): Ghost<Seq<u8>>,
    Tracked(m): Tracked<&mut Meter>,
)
    requires
        tables_ok(h.view(), buf@, off@, rbs@, sx@, sy@),
        bp == pixel_bits(h.view()) / 8,
        y < h.height,
        y % 2 == 1,
        goal == native(h.view(), imgs_of(h.view(), buf@, off@)),
        old(out)@.len() == goal.len(),
        forall|i: int| 0 <= i < y * row_bytes(h.view(), h.view().w) ==> #[trigger] old(out)@[i] == goal[i],
    ensures
        final(m).n <= old(m).n + 2 * row_bytes(h.view(), h.view().w),
        final(out)@.len() == goal.len(),
        forall|i: int| 0 <= i < (y + 1) * row_bytes(h.view(), h.view().w) ==> #[trigger] final(out)@[i] == goal[i],
{
    odd_row(h, buf, off, rbs, sx, sy, bp, y, out, Ghost(goal), Tracked(m))
}

/// `even_row` with the pixel size a constant, so the byte loop unrolls.
fn even_row_dispatch(
    h: &Header,
    buf: &[u8],
    off: &[usize; 8],
    rbs: &[usize; 7],
    sx: &[u64; 7],
    sy: &[u64; 7],
    bp: usize,
    y: u64,
    out: &mut [u8],
    Ghost(goal): Ghost<Seq<u8>>,
    Tracked(m): Tracked<&mut Meter>,
)
    requires
        tables_ok(h.view(), buf@, off@, rbs@, sx@, sy@),
        bp == pixel_bits(h.view()) / 8,
        y < h.height,
        goal == native(h.view(), imgs_of(h.view(), buf@, off@)),
        old(out)@.len() == goal.len(),
        forall|i: int| 0 <= i < y * row_bytes(h.view(), h.view().w) ==> #[trigger] old(out)@[i] == goal[i],
    ensures
        final(m).n <= old(m).n + 2 * row_bytes(h.view(), h.view().w),
        final(out)@.len() == goal.len(),
        forall|i: int| 0 <= i < (y + 1) * row_bytes(h.view(), h.view().w) ==> #[trigger] final(out)@[i] == goal[i],
{
    if bp == 1 {
        even_row(h, buf, off, rbs, sx, sy, 1, y, out, Ghost(goal), Tracked(m))
    } else if bp == 2 {
        even_row(h, buf, off, rbs, sx, sy, 2, y, out, Ghost(goal), Tracked(m))
    } else if bp == 3 {
        even_row(h, buf, off, rbs, sx, sy, 3, y, out, Ghost(goal), Tracked(m))
    } else if bp == 4 {
        even_row(h, buf, off, rbs, sx, sy, 4, y, out, Ghost(goal), Tracked(m))
    } else if bp == 6 {
        even_row(h, buf, off, rbs, sx, sy, 6, y, out, Ghost(goal), Tracked(m))
    } else if bp == 8 {
        even_row(h, buf, off, rbs, sx, sy, 8, y, out, Ghost(goal), Tracked(m))
    } else {
        even_row(h, buf, off, rbs, sx, sy, bp, y, out, Ghost(goal), Tracked(m))
    }
}

/// The header of the same image stored without interlacing.
pub open spec fn flat_hdr(h: Ihdr) -> Ihdr {
    Ihdr { interlace: 0, ..h }
}

/// A sample read from the deinterlaced image equals the one read from its
/// pass.
#[verifier::spinoff_prover]
proof fn lemma_px_flat(h: Ihdr, imgs: Seq<Seq<u8>>, x: nat, y: nat, c: nat)
    requires
        hdr_ok(h),
        h.interlace == 1,
        h.depth == 8 || h.depth == 16,
        x < h.w,
        y < h.h,
        c < channels(h.ct),
    ensures
        px_sample(h, imgs, x, y, c) == sample(flat_hdr(h), native(h, imgs), row_bytes(h, h.w), x, y, c),
{
    let nv = native(h, imgs);
    let rb = row_bytes(h, h.w);
    let p = pass_of(h, x, y);
    let ch = channels(h.ct);
    let d = h.depth;
    let bp = pixel_bits(h) / 8;
    lemma_bits(h);
    assert(pixel_bits(h) == ch * d);
    assert(bp == ch * (d / 8)) by {
        assert(ch * d == (ch * (d / 8)) * 8) by (nonlinear_arith)
            requires
                d == 8 || d == 16,
        ;
        vstd::arithmetic::div_mod::lemma_div_by_multiple((ch * (d / 8)) as int, 8);
    }
    let qx = x / dx(h, p);
    let qy = y / dy(h, p);
    let rbp = row_bytes(h, pass_w(h, p));
    if d == 8 {
        let k = (x * ch + c) * 8;
        let k2 = (qx * ch + c) * 8;
        assert(k / 8 == x * bp + c) by {
            vstd::arithmetic::div_mod::lemma_div_by_multiple((x * ch + c) as int, 8);
        }
        assert(k2 / 8 == qx * bp + c) by {
            vstd::arithmetic::div_mod::lemma_div_by_multiple((qx * ch + c) as int, 8);
        }
        lemma_native_at(h, imgs, x, y, c);
    } else {
        let k = (x * ch + c) * 16;
        let k2 = (qx * ch + c) * 16;
        assert(k / 8 == x * bp + 2 * c) by {
            assert(k == (x * bp + 2 * c) * 8) by (nonlinear_arith)
                requires
                    k == (x * ch + c) * 16,
                    bp == ch * 2,
            ;
            vstd::arithmetic::div_mod::lemma_div_by_multiple((x * bp + 2 * c) as int, 8);
        }
        assert(k2 / 8 == qx * bp + 2 * c) by {
            assert(k2 == (qx * bp + 2 * c) * 8) by (nonlinear_arith)
                requires
                    k2 == (qx * ch + c) * 16,
                    bp == ch * 2,
            ;
            vstd::arithmetic::div_mod::lemma_div_by_multiple((qx * bp + 2 * c) as int, 8);
        }
        lemma_native_at(h, imgs, x, y, 2 * c);
        lemma_native_at(h, imgs, x, y, 2 * c + 1);
    }
}

/// RGBA from the deinterlaced image, read as a non-interlaced one, is the
/// RGBA of the interlaced image.
#[verifier::spinoff_prover]
pub proof fn lemma_rgba_flat(png: Png, imgs: Seq<Seq<u8>>, off0: Seq<usize>)
    requires
        hdr_ok(png.hdr),
        png.hdr.interlace == 1,
        png.hdr.depth == 8 || png.hdr.depth == 16,
        off0.len() == 8,
        off0[0] == 0,
        off0[1] == native(png.hdr, imgs).len(),
    ensures
        ({
            let h0 = flat_hdr(png.hdr);
            let nv = native(png.hdr, imgs);
            &&& bufs_ok(h0, nv, off0)
            &&& rgba8(png, imgs) == rgba8(Png { hdr: h0, ..png }, imgs_of(h0, nv, off0))
        }),
{
    let h = png.hdr;
    let h0 = flat_hdr(h);
    let nv = native(h, imgs);
    let rb = row_bytes(h, h.w);
    let png0 = Png { hdr: h0, ..png };
    lemma_bits(h);
    lemma_native_at(h, imgs, 0, 0, 0);
    assert(pass_w(h0, 0) == h.w) by {
        assert((h.w + 1 - 1) as nat / 1 == h.w);
    }
    assert(pass_h(h0, 0) == h.h) by {
        assert((h.h + 1 - 1) as nat / 1 == h.h);
    }
    assert(row_bytes(h0, h.w) == rb);
    assert(pass_size(h0, 0) > 0) by {
        assert(h.h * (1 + rb) >= 1) by (nonlinear_arith)
            requires
                h.h >= 1,
        ;
    }
    assert(img_off(h0, 1) == rb * h.h) by {
        reveal_with_fuel(img_off, 2);
        assert(h.h * rb == rb * h.h) by (nonlinear_arith);
    }
    assert(offs_ok(h0, off0));
    let imgs0 = imgs_of(h0, nv, off0);
    assert(imgs0[0] =~= nv);
    assert forall|x: nat, y: nat, c: nat| x < h.w && y < h.h && c < channels(h.ct) implies #[trigger] px_sample(h, imgs, x, y, c)
        == px_sample(h0, imgs0, x, y, c) by {
        lemma_px_flat(h, imgs, x, y, c);
        assert(x / 1 == x && y / 1 == y);
    }
    let w = h.w;
    assert forall|k: int| 0 <= k < rgba8(png, imgs).len() implies #[trigger] rgba8(png, imgs)[k] == rgba8(png0, imgs0)[k] by {
        let x = ((k / 4) % w as int) as nat;
        let y = ((k / 4) / w as int) as nat;
        let q = k / 4;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k, 4);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q, w as int);
        assert(q < w * h.h) by (nonlinear_arith)
            requires
                k < 4 * w * h.h,
                k == 4 * q + k % 4,
                0 <= k % 4,
        ;
        assert(y < h.h) by (nonlinear_arith)
            requires
                q == w * (q / (w as int)) + q % (w as int),
                0 <= q % (w as int),
                q < w * h.h,
                y == q / (w as int),
                w >= 1,
        ;
        assert(x < w);
        assert((k % 4) < 4);
    }
    assert(rgba8(png, imgs) =~= rgba8(png0, imgs0));
}

/// `spec::rgba8` of an interlaced 8- or 16-bit image: deinterlaced into
/// its own format, then converted as a non-interlaced image.
pub fn rgba8_interlaced(png: crate::decode::PngX, buf: &[u8], off: &[usize; 8], limit: usize, Tracked(m): Tracked<&mut Meter>, Tracked(a): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, crate::decode::Error>)
    requires
        png.wf(),
        bufs_ok(png.hdr.view(), buf@, off@),
        png.hdr.view().interlace == 1,
        png.hdr.view().depth == 8 || png.hdr.view().depth == 16,
    ensures
        r matches Ok(v) ==> v@ == rgba8(png.view(), imgs_of(png.hdr.view(), buf@, off@)),
        r matches Err(e) ==> e != crate::decode::Error::Invalid,
        old(a).n <= final(a).n <= old(a).n + 2 * limit,
        final(m).n + 12 * old(a).n <= old(m).n + 12 * final(a).n + 2000,
{
    let ghost pv = png.view();
    let ghost imgs = imgs_of(pv.hdr, buf@, off@);
    proof {
        lemma_bits(pv.hdr);
    }
    let nv = match deinterlace(&png.hdr, buf, off, limit, Tracked(m), Tracked(a)) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let n = nv.len();
    let off0: [usize; 8] = [0, n, n, n, n, n, n, n];
    let crate::decode::PngX { hdr, plte, trns } = png;
    let png0 = crate::decode::PngX {
        hdr: Header { width: hdr.width, height: hdr.height, bit_depth: hdr.bit_depth, color_type: hdr.color_type, interlace: 0 },
        plte,
        trns,
    };
    proof {
        lemma_rgba_flat(pv, imgs, off0@);
        assert(png0.view() == Png { hdr: flat_hdr(pv.hdr), ..pv });
    }
    if hdr.bit_depth == 8 {
        crate::fast::rgba8_flat(&png0, nv, &off0, limit, Tracked(m), Tracked(a))
    } else {
        crate::fast::rgba8_flat16(&png0, nv.as_slice(), &off0, limit, Tracked(m), Tracked(a))
    }
}

} // verus!
