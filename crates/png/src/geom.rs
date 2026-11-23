//! Image geometry: pass sizes, row sizes and offsets (`spec::pass_w`,
//! `spec::row_bytes`, `spec::pass_off`, `spec::raw_size`).
use crate::chunks::Header;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A header that `spec::parse_ihdr` accepts.
pub open spec fn hdr_ok(h: Ihdr) -> bool {
    &&& 1 <= h.w <= MAX_LEN
    &&& 1 <= h.h <= MAX_LEN
    &&& depth_ok(h.ct, h.depth)
    &&& h.interlace <= 1
}

pub fn channels_exec(ct: u8) -> (r: u64)
    ensures
        r == channels(ct as nat),
        1 <= r <= 4,
{
    if ct == 2 {
        3
    } else if ct == 4 {
        2
    } else if ct == 6 {
        4
    } else {
        1
    }
}

pub fn pixel_bits_exec(h: &Header) -> (r: u64)
    requires
        hdr_ok(h.view()),
    ensures
        r == pixel_bits(h.view()),
        1 <= r <= 64,
{
    let c = channels_exec(h.color_type);
    proof {
        assert(c * h.bit_depth <= 64) by (nonlinear_arith)
            requires
                c <= 4,
                h.bit_depth <= 16,
        ;
        assert(c * h.bit_depth >= 1) by (nonlinear_arith)
            requires
                c >= 1,
                h.bit_depth >= 1,
        ;
    }
    c * h.bit_depth as u64
}

/// `spec::row_bytes` for a width below 2^31.
pub fn row_bytes_exec(h: &Header, w: u64) -> (r: u64)
    requires
        hdr_ok(h.view()),
        w <= MAX_LEN,
    ensures
        r == row_bytes(h.view(), w as nat),
        r <= 0x4_0000_0000,
        w > 0 ==> r >= 1,
{
    let bits = pixel_bits_exec(h);
    proof {
        assert(w * bits <= 0x7fff_ffff * 64) by (nonlinear_arith)
            requires
                w <= 0x7fff_ffff,
                bits <= 64,
        ;
        assert(w > 0 ==> w * bits >= 1) by (nonlinear_arith)
            requires
                bits >= 1,
        ;
    }
    (w * bits + 7) / 8
}

pub proof fn lemma_row_bytes_bound(h: Ihdr, w: nat)
    requires
        hdr_ok(h),
        w <= MAX_LEN,
    ensures
        row_bytes(h, w) <= 0x4_0000_0000,
{
    assert(1 <= channels(h.ct) * h.depth <= 64) by (nonlinear_arith)
        requires
            1 <= channels(h.ct) <= 4,
            1 <= h.depth <= 16,
    ;
    assert(w * pixel_bits(h) <= 0x7fff_ffff * 64) by (nonlinear_arith)
        requires
            w <= 0x7fff_ffff,
            pixel_bits(h) <= 64,
    ;
}

pub fn filter_bpp_exec(h: &Header) -> (r: u64)
    requires
        hdr_ok(h.view()),
    ensures
        r == filter_bpp(h.view()),
        1 <= r <= 8,
{
    (pixel_bits_exec(h) + 7) / 8
}

/// Pass `p`'s origin and spacing: `(x0, y0, dx, dy)`.
pub fn pass_params(il: u8, p: u64) -> (r: (u64, u64, u64, u64))
    requires
        il <= 1,
        p < if il == 0 {
            1u64
        } else {
            7u64
        },
    ensures
        ({
            let h = Ihdr { w: 0, h: 0, depth: 0, ct: 0, interlace: il as nat };
            r.0 == x0(h, p as nat) && r.1 == y0(h, p as nat) && r.2 == dx(h, p as nat) && r.3 == dy(
                h,
                p as nat,
            )
        }),
        1 <= r.2 <= 8,
        1 <= r.3 <= 8,
        r.0 < 8,
        r.1 < 8,
{
    if il == 0 {
        (0, 0, 1, 1)
    } else if p == 0 {
        (0, 0, 8, 8)
    } else if p == 1 {
        (4, 0, 8, 8)
    } else if p == 2 {
        (0, 4, 4, 8)
    } else if p == 3 {
        (2, 0, 4, 4)
    } else if p == 4 {
        (0, 2, 2, 4)
    } else if p == 5 {
        (1, 0, 2, 2)
    } else {
        (0, 1, 1, 2)
    }
}

pub proof fn lemma_params_any(h: Ihdr, il: nat, p: nat)
    requires
        h.interlace == il,
    ensures
        x0(h, p) == x0(Ihdr { w: 0, h: 0, depth: 0, ct: 0, interlace: il }, p),
        y0(h, p) == y0(Ihdr { w: 0, h: 0, depth: 0, ct: 0, interlace: il }, p),
        dx(h, p) == dx(Ihdr { w: 0, h: 0, depth: 0, ct: 0, interlace: il }, p),
        dy(h, p) == dy(Ihdr { w: 0, h: 0, depth: 0, ct: 0, interlace: il }, p),
{
}

pub fn npasses_exec(h: &Header) -> (r: u64)
    ensures
        r == npasses(h.view()),
{
    if h.interlace == 0 {
        1
    } else {
        7
    }
}

pub proof fn lemma_ceil_div(n: int, x0: int, d: int)
    requires
        0 <= x0 < n,
        d >= 1,
    ensures
        (n - x0 + d - 1) / d <= n,
{
    assert(n - x0 + d - 1 <= n * d) by (nonlinear_arith)
        requires
            0 <= x0 < n,
            d >= 1,
    ;
    vstd::arithmetic::div_mod::lemma_div_is_ordered(n - x0 + d - 1, n * d, d);
    vstd::arithmetic::div_mod::lemma_div_by_multiple(n, d);
}

/// Pass `p`'s width and height.
pub fn pass_dims(h: &Header, p: u64) -> (r: (u64, u64))
    requires
        hdr_ok(h.view()),
        p < npasses(h.view()),
    ensures
        r.0 == pass_w(h.view(), p as nat),
        r.1 == pass_h(h.view(), p as nat),
        r.0 <= MAX_LEN,
        r.1 <= MAX_LEN,
{
    let (x0, y0, dx, dy) = pass_params(h.interlace, p);
    proof {
        lemma_params_any(h.view(), h.interlace as nat, p as nat);
    }
    let w = h.width as u64;
    let hh = h.height as u64;
    let pw = if w <= x0 {
        0
    } else {
        (w - x0 + dx - 1) / dx
    };
    let ph = if hh <= y0 {
        0
    } else {
        (hh - y0 + dy - 1) / dy
    };
    proof {
        if w > x0 {
            lemma_ceil_div(w as int, x0 as int, dx as int);
        }
        if hh > y0 {
            lemma_ceil_div(hh as int, y0 as int, dy as int);
        }
    }
    (pw, ph)
}

/// `spec::pass_size`, at most 2^31 * (2^34 + 1).
pub fn pass_size_exec(h: &Header, p: u64) -> (r: u128)
    requires
        hdr_ok(h.view()),
        p < npasses(h.view()),
    ensures
        r == pass_size(h.view(), p as nat),
        r <= 0x7fff_ffff * 0x4_0000_0001,
{
    let (pw, ph) = pass_dims(h, p);
    if pw == 0 || ph == 0 {
        0
    } else {
        let rb = row_bytes_exec(h, pw);
        proof {
            assert(ph * (1 + rb) <= 0x7fff_ffff * 0x4_0000_0001) by (nonlinear_arith)
                requires
                    ph <= 0x7fff_ffff,
                    rb <= 0x4_0000_0000,
            ;
        }
        ph as u128 * (1 + rb as u128)
    }
}

/// Offsets of the passes and the total: `r[p] == pass_off(p)` for
/// `p <= npasses`.
pub fn pass_offsets(h: &Header) -> (r: [u128; 8])
    requires
        hdr_ok(h.view()),
    ensures
        forall|p: int| 0 <= p <= npasses(h.view()) ==> #[trigger] r@[p] == pass_off(h.view(), p as nat),
        forall|p: int| 0 <= p <= npasses(h.view()) ==> #[trigger] r@[p] <= p * (0x7fff_ffff * 0x4_0000_0001),
{
    let mut r: [u128; 8] = [0; 8];
    let n = npasses_exec(h);
    let mut p: u64 = 0;
    while p < n
        invariant
            hdr_ok(h.view()),
            n == npasses(h.view()),
            n <= 7,
            p <= n,
            r@.len() == 8,
            forall|q: int| 0 <= q <= p ==> #[trigger] r@[q] == pass_off(h.view(), q as nat),
            forall|q: int| 0 <= q <= p ==> #[trigger] r@[q] <= q * (0x7fff_ffff * 0x4_0000_0001),
        decreases n - p,
    {
        let s = pass_size_exec(h, p);
        let v = r[p as usize] + s;
        r[p as usize + 1] = v;
        p = p + 1;
    }
    r
}

pub fn raw_size_exec(h: &Header) -> (r: u128)
    requires
        hdr_ok(h.view()),
    ensures
        r == raw_size(h.view()),
        r <= 7 * (0x7fff_ffff * 0x4_0000_0001),
{
    let offs = pass_offsets(h);
    let n = npasses_exec(h);
    offs[n as usize]
}

} // verus!
