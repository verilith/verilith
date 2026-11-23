//! Decoding the pixels of an entropy-coded image (§5.2), proven to compute
//! `spec::decode_with`.
use crate::bitreader::*;
use crate::codes::*;
use crate::huffman::*;
use verilith_core::prims::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use crate::slemmas::*;
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/// Why decoding stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The input is not a valid image (the spec rejects it).
    Bitstream,
    /// An allocation failed.
    OutOfMemory,
    /// A lossy (VP8) image, which vwebp does not decode.
    Unsupported,
}

pub const CODE_TO_PLANE: [u8; 120] = [
    0x18, 0x07, 0x17, 0x19, 0x28, 0x06, 0x27, 0x29, 0x16, 0x1a, 0x26, 0x2a, 0x38, 0x05, 0x37, 0x39,
    0x15, 0x1b, 0x36, 0x3a, 0x25, 0x2b, 0x48, 0x04, 0x47, 0x49, 0x14, 0x1c, 0x35, 0x3b, 0x46, 0x4a,
    0x24, 0x2c, 0x58, 0x45, 0x4b, 0x34, 0x3c, 0x03, 0x57, 0x59, 0x13, 0x1d, 0x56, 0x5a, 0x23, 0x2d,
    0x44, 0x4c, 0x55, 0x5b, 0x33, 0x3d, 0x68, 0x02, 0x67, 0x69, 0x12, 0x1e, 0x66, 0x6a, 0x22, 0x2e,
    0x54, 0x5c, 0x43, 0x4d, 0x65, 0x6b, 0x32, 0x3e, 0x78, 0x01, 0x77, 0x79, 0x53, 0x5d, 0x11, 0x1f,
    0x64, 0x6c, 0x42, 0x4e, 0x76, 0x7a, 0x21, 0x2f, 0x75, 0x7b, 0x31, 0x3f, 0x63, 0x6d, 0x52, 0x5e,
    0x00, 0x74, 0x7c, 0x41, 0x4f, 0x10, 0x20, 0x62, 0x6e, 0x30, 0x73, 0x7d, 0x51, 0x5f, 0x40, 0x72,
    0x7e, 0x61, 0x6f, 0x50, 0x71, 0x7f, 0x60, 0x70,
];

pub proof fn lemma_code_to_plane()
    ensures
        forall|i: int| 0 <= i < 120 ==> #[trigger] CODE_TO_PLANE@[i] as nat == code_to_plane()[i],
        code_to_plane().len() == 120,
{
    assert(forall|i: int| 0 <= i < 120 ==> #[trigger] CODE_TO_PLANE@[i] as nat == code_to_plane()[i]) by (compute);
}

// ---------------------------------------------------------------------------
// Small facts
// ---------------------------------------------------------------------------

/// Packing a pixel.
pub proof fn lemma_argb(a: u32, r: u32, g: u32, b: u32)
    requires
        a < 256,
        r < 256,
        g < 256,
        b < 256,
    ensures
        argb(a as nat, r as nat, g as nat, b as nat) == (a << 24u32) | (r << 16u32) | (g << 8u32) | b,
{
    assert((a << 24u32) | (r << 16u32) | (g << 8u32) | b == a * 0x100_0000 + r * 0x1_0000 + g * 0x100 + b)
        by (bit_vector)
        requires
            a < 256,
            r < 256,
            g < 256,
            b < 256,
    ;
}

/// The color cache index.
pub fn hash_exec(c: u32, cb: u32) -> (r: usize)
    requires
        1 <= cb <= 11,
    ensures
        r as nat == hash(c, cb as nat),
        r < pow2(cb as nat),
{
    let x: u64 = (c as u64) * 0x1e35a7bd;
    let y: u64 = x & 0xffff_ffff;
    let z: u64 = y >> ((32 - cb) as u64);
    proof {
        lemma2_to64();
        assert(lowmask(32) == 0xffff_ffffu64) by (bit_vector);
        crate::bitreader::lemma_and_mask(x, 32);
        assert(y as nat == (c as nat * 0x1e35a7bd) % 0x1_0000_0000);
        lemma_u64_shr_is_div(y, (32 - cb) as u64);
        lemma_pow2_adds(cb as nat, (32 - cb) as nat);
        lemma_pow2_pos((32 - cb) as nat);
        lemma_mul_is_commutative(pow2(cb as nat) as int, pow2((32 - cb) as nat) as int);
        assert(y < 0x1_0000_0000);
        lemma_multiply_divide_lt(y as int, pow2((32 - cb) as nat) as int, pow2(cb as nat) as int);
        lemma_pow2_strictly_increases(cb as nat, 12);
    }
    z as usize
}

/// Counting pixels by row and column.
pub proof fn lemma_xy_step(i: nat, w: nat, x: nat, y: nat)
    requires
        w > 0,
        x == i % w,
        y == i / w,
    ensures
        x + 1 < w ==> (i + 1) % w == x + 1 && (i + 1) / w == y,
        x + 1 >= w ==> (i + 1) % w == 0 && (i + 1) / w == y + 1,
{
    lemma_fundamental_div_mod(i as int, w as int);
    lemma_mod_bound(i as int, w as int);
    if x + 1 < w {
        lemma_fundamental_div_mod_converse((i + 1) as int, w as int, y as int, (x + 1) as int);
    } else {
        assert(i + 1 == w * (y + 1) + 0) by (nonlinear_arith)
            requires
                i == w * y + x,
                x + 1 == w,
        ;
        lemma_fundamental_div_mod_converse((i + 1) as int, w as int, (y + 1) as int, 0);
    }
}

/// The value and extra bits of a length or distance prefix code.
pub fn prefix_parts(s: u32) -> (r: (u32, u32))
    requires
        s < 40,
    ensures
        r.0 as nat == pfx_extra(s as nat),
        r.1 as nat == pfx_base(s as nat),
        r.0 <= 18,
        r.1 + pow2(r.0 as nat) <= 0x10_0000,
{
    if s < 4 {
        proof {
            lemma2_to64();
        }
        (0, s)
    } else {
        let e = (s - 2) >> 1;
        proof {
            assert(e == ((s - 2) as u32) / 2 && e <= 18) by (bit_vector)
                requires
                    4 <= s < 40,
                    e == ((s - 2) as u32) >> 1u32,
            ;
            assert(s & 1 == s % 2) by (bit_vector);
            if e < 18 {
                lemma_pow2_strictly_increases(e as nat, 18);
            }
            lemma2_to64();
            assert(pow2(18) == 0x4_0000) by {
                lemma2_to64();
            }
            assert((2 + s % 2) * pow2(e as nat) + pow2(e as nat) <= 4 * 0x4_0000) by (nonlinear_arith)
                requires
                    pow2(e as nat) <= 0x4_0000,
                    s % 2 <= 1,
            ;
            lemma_u32_shl_is_mul((2 + (s & 1)) as u32, e);
        }
        let base = (2 + (s & 1)) << e;
        (e, base)
    }
}

/// The distance in pixels of distance code `c`.
pub fn plane_dist(w: usize, c: u32) -> (r: usize)
    requires
        1 <= w <= 16384,
        1 <= c <= 0x10_0000,
    ensures
        r as nat == plane_to_dist(w as nat, c as nat),
        r >= 1,
{
    if c > 120 {
        (c - 120) as usize
    } else {
        proof {
            lemma_code_to_plane();
        }
        let dc = CODE_TO_PLANE[(c - 1) as usize] as i64;
        proof {
            assert(0 <= dc <= 0x7f) by {
                assert(forall|i: int| 0 <= i < 120 ==> #[trigger] CODE_TO_PLANE@[i] <= 0x7f) by (compute);
            }
        }
        let yo = dc / 16;
        let xo = 8 - dc % 16;
        proof {
            assert(0 <= yo <= 7);
            assert(yo * (w as i64) <= 7 * 16384) by (nonlinear_arith)
                requires
                    0 <= yo <= 7,
                    w <= 16384,
            ;
            assert(yo * (w as i64) >= 0) by (nonlinear_arith)
                requires
                    0 <= yo,
                    (w as i64) >= 0,
            ;
        }
        let d = yo * (w as i64) + xo;
        if d >= 1 {
            d as usize
        } else {
            1
        }
    }
}

// ---------------------------------------------------------------------------
// Backward references
// ---------------------------------------------------------------------------

/// The pixel a copy writes at offset `k`: the one `d` back.
pub proof fn lemma_copy_seg_step(out: Seq<u32>, d: nat, len: nat, k: nat)
    requires
        1 <= d <= out.len(),
        k < len,
    ensures
        (out + copy_seg(out, d, len))[out.len() + k - d] == copy_seg(out, d, len)[k as int],
{
    let n = out.len() as int;
    let seg = copy_seg(out, d, len);
    let full = out + seg;
    if k >= d {
        lemma_mod_sub_multiples_vanish(k as int, d as int);
        assert(full[n + k - d] == seg[k - d]);
        assert((k - d) % (d as int) == k as int % (d as int)) by {
            lemma_mod_sub_multiples_vanish(k as int, d as int);
        }
    } else {
        lemma_small_mod(k, d);
        assert(full[n + k - d] == out[n + k - d]);
    }
}

pub proof fn lemma_cache_all_step(cache: Seq<u32>, cb: nat, s: Seq<u32>, k: nat)
    requires
        k < s.len(),
    ensures
        cache_insert_all(cache, cb, s.subrange(0, k + 1 as int)) == cache_insert(
            cache_insert_all(cache, cb, s.subrange(0, k as int)),
            cb,
            s[k as int],
        ),
{
    assert(s.subrange(0, k + 1 as int).drop_last() == s.subrange(0, k as int));
}

/// Where the decoder stands in the image: its parameters, as the spec's
/// `Img`.
pub open spec fn img_of(w: nat, h: nat, cb: nat, gl: Seq<Seq<Seq<u8>>>, hb: nat, meta: Seq<u32>) -> Img {
    Img {
        w,
        npix: w * h,
        cb,
        groups: gl,
        hb,
        hx: if hb == 0 {
            0
        } else {
            subsample(w, hb)
        },
        meta,
    }
}

pub open spec fn meta_ok(w: nat, h: nat, hb: nat, meta: Seq<u32>, ngroups: nat) -> bool {
    hb == 0 || (2 <= hb <= 9 && meta.len() == subsample(w, hb) * subsample(h, hb) && forall|t: int|
        0 <= t < meta.len() ==> #[trigger] meta_code(meta[t]) < ngroups)
}

/// `subsample(n, b)` is `n` divided by `2^b`, rounded up.
pub fn subsample_exec(n: usize, b: u32) -> (r: usize)
    requires
        1 <= n <= 16384,
        b <= 9,
    ensures
        r as nat == subsample(n as nat, b as nat),
        1 <= r <= n,
        forall|x: nat| x < n ==> #[trigger] (x / pow2(b as nat)) < r,
{
    proof {
        lemma_pow2_strictly_increases(b as nat, 10);
        lemma2_to64();
        lemma_pow2_pos(b as nat);
        lemma_usize_shl_is_mul(1, b as usize);
    }
    let p = 1usize << b;
    let r = (n + p - 1) / p;
    proof {
        lemma_usize_shl_is_mul(1, b as usize);
        let pp = pow2(b as nat) as int;
        assert(r >= 1) by {
            lemma_div_is_ordered(pp, (n + pp - 1) as int, pp);
            lemma_div_basics(pp);
        }
        assert(r <= n) by {
            assert(n + pp - 1 <= n * pp) by (nonlinear_arith)
                requires
                    n >= 1,
                    pp >= 1,
            ;
            lemma_div_is_ordered((n + pp - 1) as int, (n * pp) as int, pp);
            lemma_div_multiples_vanish(n as int, pp);
            lemma_mul_is_commutative(n as int, pp);
        }
        assert forall|x: nat| x < n implies #[trigger] (x / pow2(b as nat)) < r by {
            lemma_fundamental_div_mod(x as int, pp);
            lemma_mod_bound(x as int, pp);
            let q = x as int / pp;
            assert((q + 1) * pp <= n + pp - 1) by (nonlinear_arith)
                requires
                    x == pp * q + x as int % pp,
                    x as int % pp >= 0,
                    x < n,
            ;
            lemma_div_multiples_vanish(q + 1, pp);
            lemma_div_is_ordered(((q + 1) * pp) as int, (n + pp - 1) as int, pp);
            lemma_mul_is_commutative(q + 1, pp);
        }
    }
    r
}

/// The group at pixel `(x, y)`.
#[inline(always)]
fn group_index(
    x: usize,
    y: usize,
    w: usize,
    h: usize,
    hb: u32,
    hx: usize,
    meta: &Vec<u32>,
    Ghost(i): Ghost<nat>,
    Ghost(ngroups): Ghost<nat>,
) -> (r: usize)
    requires
        1 <= w <= 16384,
        1 <= h <= 16384,
        x == i % (w as nat),
        y == i / (w as nat),
        y < h,
        meta_ok(w as nat, h as nat, hb as nat, meta@, ngroups),
        ngroups >= 1,
        hb == 0 ==> hx == 0,
        hb != 0 ==> hx == subsample(w as nat, hb as nat),
    ensures
        r < ngroups,
        hb == 0 ==> r == 0,
        hb != 0 ==> {
            let t = ((y as nat) / pow2(hb as nat)) * (hx as nat) + (x as nat) / pow2(hb as nat);
            0 <= t < meta@.len() && r == meta_code(meta@[t as int])
        },
{
    if hb == 0 {
        0
    } else {
        let ghost hy = subsample(h as nat, hb as nat);
        proof {
            lemma_mod_bound(i as int, w as int);
            lemma_pow2_strictly_increases(hb as nat, 10);
            lemma2_to64();
            lemma_pow2_pos(hb as nat);
        }
        let hy_e = subsample_exec(h, hb);
        let hx_e = subsample_exec(w, hb);
        let ty = y >> hb;
        let tx = x >> hb;
        proof {
            lemma_usize_shr_is_div(y, hb as usize);
            lemma_usize_shr_is_div(x, hb as usize);
            assert(ty < hy_e);
            assert(tx < hx_e);
            assert(ty * hx + tx < hy_e * hx_e) by (nonlinear_arith)
                requires
                    ty < hy_e,
                    tx < hx_e,
                    hx == hx_e,
            ;
            assert(hy_e * hx_e <= 16384 * 16384) by (nonlinear_arith)
                requires
                    hy_e <= 16384,
                    hx_e <= 16384,
            ;
            lemma_mul_is_commutative(hy_e as int, hx_e as int);
        }
        let t = ty * hx + tx;
        let m = meta[t];
        proof {
            assert(((m >> 8u32) & 0xffffu32) == (m / 0x100) % 0x1_0000) by (bit_vector);
            assert(meta_code(meta@[t as int]) < ngroups);
        }
        ((m >> 8) & 0xffff) as usize
    }
}

/// Inserts a pixel into the color cache.
#[inline(always)]
fn cache_put(cache: &mut Vec<u32>, cb: u32, c: u32)
    requires
        cb <= 11,
        old(cache)@.len() == cache_size(cb as nat),
    ensures
        final(cache)@ == cache_insert(old(cache)@, cb as nat, c),
        final(cache)@.len() == old(cache)@.len(),
{
    if cb > 0 {
        let k = hash_exec(c, cb);
        set32(cache.as_mut_slice(), k, c);
    }
}

/// Copies `len` pixels from `d` back, inserting each into the color cache.
fn copy_ref(out: &mut Vec<u32>, cache: &mut Vec<u32>, i: usize, d: usize, len: usize, cb: u32)
    requires
        1 <= d <= i,
        i + len <= old(out)@.len(),
        old(out)@.len() <= 0x1000_0000,
        cb <= 11,
        old(cache)@.len() == cache_size(cb as nat),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(0, (i + len) as int) == old(out)@.subrange(0, i as int) + copy_seg(
            old(out)@.subrange(0, i as int),
            d as nat,
            len as nat,
        ),
        final(cache)@ == cache_insert_all(
            old(cache)@,
            cb as nat,
            copy_seg(old(out)@.subrange(0, i as int), d as nat, len as nat),
        ),
        final(cache)@.len() == old(cache)@.len(),
{
    let ghost pre = old(out)@.subrange(0, i as int);
    let ghost seg = copy_seg(pre, d as nat, len as nat);
    let ghost full = pre + seg;
    let ghost c0 = cache@;
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            1 <= d <= i,
            i + len <= out@.len(),
            out@.len() == old(out)@.len(),
            out@.len() <= 0x1000_0000,
            cb <= 11,
            cache@.len() == cache_size(cb as nat),
            pre == old(out)@.subrange(0, i as int),
            seg == copy_seg(pre, d as nat, len as nat),
            full == pre + seg,
            forall|j: int| 0 <= j < i + k ==> #[trigger] out@[j] == full[j],
            cache@ == cache_insert_all(c0, cb as nat, seg.subrange(0, k as int)),
        decreases len - k,
    {
        let c = get32(out.as_slice(), i + k - d);
        proof {
            lemma_copy_seg_step(pre, d as nat, len as nat, k as nat);
            assert(c == seg[k as int]);
            lemma_cache_all_step(c0, cb as nat, seg, k as nat);
        }
        set32(out.as_mut_slice(), i + k, c);
        cache_put(cache, cb, c);
        k = k + 1;
    }
    assert(out@.subrange(0, (i + len) as int) =~= full);
    assert(seg.subrange(0, len as int) =~= seg);
}

/// Work charged for each pixel decoded.
pub open spec fn pix_cost() -> nat {
    110
}

/// The rest of `decode_pixels` after a length prefix code `256 + ls` ends
/// at `p1`.
#[verifier::opaque]
pub open spec fn backref_spec(b: Seq<u8>, p1: int, img: Img, out: Seq<u32>, cache: Seq<u32>, ls: nat) -> Option<(Seq<u32>, int)> {
    let g = group_at(img, out.len());
    match rd(b, p1, pfx_extra(ls)) {
        None => None,
        Some(x) => {
            let len = pfx_base(ls) + x + 1;
            match read_symbol(g[4], b, p1 + pfx_extra(ls)) {
                None => None,
                Some((ds, p3)) => match rd(b, p3, pfx_extra(ds)) {
                    None => None,
                    Some(y) => {
                        let d = plane_to_dist(img.w, pfx_base(ds) + y + 1);
                        if d > out.len() || len > img.npix - out.len() {
                            None
                        } else {
                            let seg = copy_seg(out, d, len);
                            decode_pixels(b, p3 + pfx_extra(ds), img, out + seg, cache_insert_all(cache, img.cb, seg))
                        }
                    },
                },
            }
        },
    }
}

/// The rest of `decode_pixels` after a green literal `s` ends at `p1`.
#[verifier::opaque]
pub open spec fn lit_rest(b: Seq<u8>, p1: int, img: Img, out: Seq<u32>, cache: Seq<u32>, s: nat) -> Option<(Seq<u32>, int)> {
    let g = group_at(img, out.len());
    match read_symbol(g[1], b, p1) {
        None => None,
        Some((r, p2)) => match read_symbol(g[2], b, p2) {
            None => None,
            Some((bl, p3)) => match read_symbol(g[3], b, p3) {
                None => None,
                Some((a, p4)) => {
                    let c = argb(a, r, s, bl);
                    decode_pixels(b, p4, img, out.push(c), cache_insert(cache, img.cb, c))
                },
            },
        },
    }
}

pub proof fn lemma_lit_unfold(b: Seq<u8>, p1: int, img: Img, out: Seq<u32>, cache: Seq<u32>, s: nat)
    ensures
        lit_rest(b, p1, img, out, cache, s) == match read_symbol(group_at(img, out.len())[1], b, p1) {
            None => None,
            Some((r, p2)) => match read_symbol(group_at(img, out.len())[2], b, p2) {
                None => None,
                Some((bl, p3)) => match read_symbol(group_at(img, out.len())[3], b, p3) {
                    None => None,
                    Some((a, p4)) => {
                        let c = argb(a, r, s, bl);
                        decode_pixels(b, p4, img, out.push(c), cache_insert(cache, img.cb, c))
                    },
                },
            },
        },
{
    reveal(lit_rest);
}

/// One step of `decode_pixels`.
pub proof fn lemma_dp_unfold(b: Seq<u8>, pos: int, img: Img, out: Seq<u32>, cache: Seq<u32>)
    requires
        out.len() < img.npix,
    ensures
        decode_pixels(b, pos, img, out, cache) == match read_symbol(group_at(img, out.len())[0], b, pos) {
            None => None,
            Some((s, p1)) => if s < 256 {
                lit_rest(b, p1, img, out, cache, s)
            } else if s < 280 {
                backref_spec(b, p1, img, out, cache, (s - 256) as nat)
            } else {
                let c = cache[s - 280];
                decode_pixels(b, p1, img, out.push(c), cache_insert(cache, img.cb, c))
            },
        },
{
    reveal(lit_rest);
    reveal(backref_spec);
}

pub proof fn lemma_dp_done(b: Seq<u8>, pos: int, img: Img, out: Seq<u32>, cache: Seq<u32>)
    requires
        out.len() >= img.npix,
    ensures
        decode_pixels(b, pos, img, out, cache) == Some((out, pos)),
{
}

/// The group the decoder looks up is the spec's.
pub proof fn lemma_group_at(img: Img, i: nat, w: usize, x: usize, y: usize, hb: u32, hx: usize, meta: Seq<u32>, gi: usize)
    requires
        img.w == w,
        w >= 1,
        img.hb == hb,
        img.hx == hx,
        img.meta == meta,
        x == i % (w as nat),
        y == i / (w as nat),
        hb == 0 ==> gi == 0,
        hb != 0 ==> {
            let t = ((y as nat) / pow2(hb as nat)) * (hx as nat) + (x as nat) / pow2(hb as nat);
            0 <= t < meta.len() && gi == meta_code(meta[t as int])
        },
    ensures
        group_at(img, i) == img.groups[gi as int],
{
    if hb != 0 {
        let t = ((y as nat) / pow2(hb as nat)) * (hx as nat) + (x as nat) / pow2(hb as nat);
        let xx = i % img.w;
        let yy = i / img.w;
        assert(xx == x);
        assert(yy == y);
        let p = pow2(img.hb);
        assert(p == pow2(hb as nat));
        assert(img.hx == hx);
        assert(yy / p == (y as nat) / pow2(hb as nat));
        assert(xx / p == (x as nat) / pow2(hb as nat));
        assert((yy / p) * img.hx + xx / p == t);
    }
}

/// What the decoding loop knows about the image.
pub open spec fn loop_ok(
    img: Img,
    w: usize,
    h: usize,
    npix: usize,
    cb: u32,
    groups: Seq<Group>,
    gl: Seq<Seq<Seq<u8>>>,
    hb: u32,
    hx: usize,
    meta: Seq<u32>,
) -> bool {
    &&& 1 <= w <= 16384
    &&& 1 <= h <= 16384
    &&& cb <= 11
    &&& npix == w * h
    &&& npix <= 16384 * 16384
    &&& groups_ok(groups, gl)
    &&& groups_shape(gl, cb as nat)
    &&& gl.len() >= 1
    &&& meta_ok(w as nat, h as nat, hb as nat, meta, gl.len())
    &&& img == img_of(w as nat, h as nat, cb as nat, gl, hb as nat, meta)
    &&& hb == 0 ==> hx == 0
    &&& hb != 0 ==> hx == subsample(w as nat, hb as nat)
}

/// Decodes a backward reference whose length prefix code `256 + ls` was read.
#[verifier::rlimit(50)]
fn backref(
    br: &mut BitReader,
    data: &[u8],
    out: &mut Vec<u32>,
    cache: &mut Vec<u32>,
    i: usize,
    ls: u32,
    dcode: &HCode,
    Ghost(dlens): Ghost<Seq<u8>>,
    w: usize,
    npix: usize,
    cb: u32,
    Ghost(img): Ghost<Img>,
) -> (r: Result<usize, Error>)
    requires
        old(br).ok(data@),
        ls < 24,
        hcode_ok(*dcode, dlens),
        dlens.len() == 40,
        dlens == group_at(img, i as nat)[4],
        1 <= w <= 16384,
        img.w == w,
        img.npix == npix,
        img.cb == cb,
        cb <= 11,
        i < npix,
        npix <= 16384 * 16384,
        old(out)@.len() == npix,
        old(cache)@.len() == cache_size(cb as nat),
    ensures
        final(br).ok(data@),
        final(out)@.len() == npix,
        final(cache)@.len() == cache_size(cb as nat),
        match r {
            Ok(i2) => i < i2 <= npix && decode_pixels(data@, final(br).pos(), img, final(out)@.subrange(0, i2 as int), final(cache)@)
                == backref_spec(data@, old(br).pos(), img, old(out)@.subrange(0, i as int), old(cache)@, ls as nat)
                && final(br).work@ + 1 + sym_cost() <= old(br).work@ + pix_cost() * (i2 - i),
            Err(e) => e == Error::Bitstream && backref_spec(data@, old(br).pos(), img, old(out)@.subrange(0, i as int), old(cache)@, ls as nat) is None
                && final(br).work@ + 1 + sym_cost() <= old(br).work@ + pix_cost(),
        },
        final(br).pos() >= old(br).pos(),
{
    hide(decode_pixels);
    reveal(backref_spec);
    let ghost b = data@;
    let ghost pre = old(out)@.subrange(0, i as int);
    let ghost wk = br.work@;
    proof {
        assert(pre.len() == i);
    }
    let (le, lbase) = prefix_parts(ls);
    let ghost lp = br.pos();
    let lx = match br.take(data, le) {
        Some(v) => v,
        None => return Err(Error::Bitstream),
    };
    proof {
        lemma_bits_bound(b, lp, le as nat);
    }
    let len = (lbase + lx + 1) as usize;
    let ds = match br.read_symbol(data, dcode, Ghost(dlens)) {
        Some(v) => v,
        None => return Err(Error::Bitstream),
    };
    let (de, dbase) = prefix_parts(ds);
    let ghost dp = br.pos();
    let dx = match br.take(data, de) {
        Some(v) => v,
        None => return Err(Error::Bitstream),
    };
    proof {
        lemma_bits_bound(b, dp, de as nat);
    }
    let d = plane_dist(w, dbase + dx + 1);
    if d > i || len > npix - i {
        return Err(Error::Bitstream);
    }
    copy_ref(out, cache, i, d, len, cb);
    br.work = Ghost(br.work@ + len as nat);
    proof {
        assert(br.work@ + 1 + sym_cost() <= wk + pix_cost() * len) by (nonlinear_arith)
            requires
                br.work@ <= wk + sym_cost() + 2 * refill_cost() + len,
                sym_cost() == 26,
                refill_cost() == 9,
                pix_cost() == 110,
                len >= 1,
        ;
    }
    Ok(i + len)
}

/// Decodes the pixels of one literal, backward reference or cache code.
#[verifier::rlimit(100)]
/// Decodes pixel `i` if it is a color cache symbol, or a literal whose four
/// codes are all in their tables: the common cases, with no per-symbol
/// input checks. At least 8 input bytes remain, so a refill leaves at least
/// 56 bits; a table code takes at most `MAX_ROOT` = 10, and `peek` needs 15
/// bits, so the reader refills once, first, if it has fewer than 45 bits.
/// Returns `false` with nothing changed otherwise.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
fn try_lit(
    br: &mut BitReader,
    data: &[u8],
    out: &mut Vec<u32>,
    cache: &mut Vec<u32>,
    i: usize,
    cb: u32,
    g: &Group,
    Ghost(img): Ghost<Img>,
) -> (r: bool)
    requires
        old(br).ok(data@),
        old(br).ip + 8 <= data@.len(),
        group_ok(*g, group_at(img, i as nat)),
        group_at(img, i as nat)[0].len() == alphabet(0, cb as nat),
        group_at(img, i as nat)[1].len() == 256,
        group_at(img, i as nat)[2].len() == 256,
        group_at(img, i as nat)[3].len() == 256,
        img.cb == cb,
        cb <= 11,
        i < img.npix,
        old(out)@.len() == img.npix,
        old(cache)@.len() == cache_size(cb as nat),
    ensures
        !r ==> *final(br) == *old(br) && final(out)@ == old(out)@ && final(cache)@ == old(cache)@,
        r ==> {
            &&& final(br).ok(data@)
            &&& final(br).pos() >= old(br).pos()
            &&& final(br).work@ <= old(br).work@ + 2 * refill_cost() + 4
            &&& final(out)@.len() == old(out)@.len()
            &&& final(cache)@.len() == old(cache)@.len()
            &&& decode_pixels(data@, final(br).pos(), img, final(out)@.subrange(0, i + 1), final(cache)@)
                == decode_pixels(data@, old(br).pos(), img, old(out)@.subrange(0, i as int), old(cache)@)
        },
{
    let ghost b = data@;
    let ghost gls = group_at(img, i as nat);
    let ghost pre = old(out)@.subrange(0, i as int);
    let ghost p0 = old(br).pos();
    proof {
        reveal(group_ok);
        assert(hcode_ok(g.codes@[0], gls[0]) && hcode_ok(g.codes@[1], gls[1]) && hcode_ok(g.codes@[2], gls[2])
            && hcode_ok(g.codes@[3], gls[3]));
        lemma_dp_unfold(b, p0, img, pre, old(cache)@);
    }
    let mut t = BitReader { buf: br.buf, cnt: br.cnt, ip: br.ip, work: Ghost(br.work@) };
    if t.cnt < 45 {
        t.refill(data);
    }
    proof {
        // A refill that reached the end of the input took at least 64 bits.
        assert(t.cnt >= 45);
        lemma_bits_bound(b, p0, t.cnt as nat);
    }
    let e0 = peek(&g.codes[0], t.buf, Ghost(b), Ghost(p0), Ghost(t.cnt as nat), Ghost(gls[0]));
    if e0 == LONG || ((e0 & 0xffff) >= 256 && (e0 & 0xffff) < 280) {
        return false;
    }
    let k0 = e0 >> 16;
    let s = e0 & 0xffff;
    proof {
        lemma_shr_bits(b, p0, t.cnt as nat, t.buf, k0 as u64);
    }
    t.buf = t.buf >> (k0 as u64);
    t.cnt = t.cnt - k0;
    t.work = Ghost(t.work@ + 1);
    let ghost p1 = t.pos();
    if s >= 280 {
        // A color cache symbol.
        proof {
            assert(gls[0].len() == alphabet(0, cb as nat));
            assert(cb > 0);
            assert(s - 280 < cache@.len());
        }
        let c = get32(cache.as_slice(), (s - 280) as usize);
        set32(out.as_mut_slice(), i, c);
        cache_put(cache, cb, c);
        *br = t;
        proof {
            assert(out@.subrange(0, i + 1) =~= pre.push(c));
        }
        return true;
    }
    proof {
        assert(t.cnt >= 35);
        lemma_bits_bound(b, p1, t.cnt as nat);
        lemma_lit_unfold(b, p1, img, pre, old(cache)@, s as nat);
    }
    let e1 = peek(&g.codes[1], t.buf, Ghost(b), Ghost(p1), Ghost(t.cnt as nat), Ghost(gls[1]));
    if e1 == LONG {
        return false;
    }
    let k1 = e1 >> 16;
    proof {
        lemma_shr_bits(b, p1, t.cnt as nat, t.buf, k1 as u64);
    }
    let buf = t.buf >> (k1 as u64);
    let ghost p2 = p1 + k1;
    let e2 = peek(&g.codes[2], buf, Ghost(b), Ghost(p2), Ghost((t.cnt - k1) as nat), Ghost(gls[2]));
    if e2 == LONG {
        return false;
    }
    let k2 = e2 >> 16;
    proof {
        lemma_shr_bits(b, p2, (t.cnt - k1) as nat, buf, k2 as u64);
    }
    let buf = buf >> (k2 as u64);
    let ghost p3 = p2 + k2;
    let e3 = peek(&g.codes[3], buf, Ghost(b), Ghost(p3), Ghost((t.cnt - k1 - k2) as nat), Ghost(gls[3]));
    if e3 == LONG {
        return false;
    }
    let k3 = e3 >> 16;
    proof {
        lemma_shr_bits(b, p3, (t.cnt - k1 - k2) as nat, buf, k3 as u64);
    }
    let buf = buf >> (k3 as u64);
    let r = e1 & 0xffff;
    let bl = e2 & 0xffff;
    let a = e3 & 0xffff;
    proof {
        lemma_argb(a, r, s, bl);
    }
    let c = (a << 24) | (r << 16) | (s << 8) | bl;
    set32(out.as_mut_slice(), i, c);
    cache_put(cache, cb, c);
    *br = BitReader { buf, cnt: t.cnt - k1 - k2 - k3, ip: t.ip, work: Ghost(t.work@ + 3) };
    proof {
        assert(out@.subrange(0, i + 1) =~= pre.push(c));
    }
    true
}

fn step(
    br: &mut BitReader,
    data: &[u8],
    out: &mut Vec<u32>,
    cache: &mut Vec<u32>,
    i: usize,
    x: usize,
    y: usize,
    w: usize,
    h: usize,
    npix: usize,
    cb: u32,
    groups: &Vec<Group>,
    Ghost(gl): Ghost<Seq<Seq<Seq<u8>>>>,
    hb: u32,
    hx: usize,
    meta: &Vec<u32>,
    Ghost(img): Ghost<Img>,
) -> (r: Result<usize, Error>)
    requires
        old(br).ok(data@),
        loop_ok(img, w, h, npix, cb, groups@, gl, hb, hx, meta@),
        i < npix,
        x == (i as nat) % (w as nat),
        y == (i as nat) / (w as nat),
        old(out)@.len() == npix,
        old(cache)@.len() == cache_size(cb as nat),
    ensures
        final(br).ok(data@),
        final(out)@.len() == npix,
        final(cache)@.len() == cache_size(cb as nat),
        match r {
            Ok(i2) => i < i2 <= npix && decode_pixels(data@, final(br).pos(), img, final(out)@.subrange(0, i2 as int), final(cache)@)
                == decode_pixels(data@, old(br).pos(), img, old(out)@.subrange(0, i as int), old(cache)@)
                && final(br).work@ <= old(br).work@ + pix_cost() * (i2 - i),
            Err(e) => e == Error::Bitstream && decode_pixels(data@, old(br).pos(), img, old(out)@.subrange(0, i as int), old(cache)@) is None
                && final(br).work@ <= old(br).work@ + pix_cost(),
        },
        final(br).pos() >= old(br).pos(),
{
    hide(decode_pixels);
    hide(group_at);
    let ghost b = data@;
    let ghost pre = old(out)@.subrange(0, i as int);
    let ghost wk = br.work@;
    proof {
        lemma_multiply_divide_lt(i as int, w as int, h as int);
    }
    let gi = group_index(x, y, w, h, hb, hx, meta, Ghost(i as nat), Ghost(gl.len()));
    let g = &groups[gi];
    let ghost gls = gl[gi as int];
    proof {
        reveal(group_ok);
        assert(group_ok(groups@[gi as int], gls));
        lemma_group_at(img, i as nat, w, x, y, hb, hx, meta@, gi);
        assert(gls.len() == 5);
        assert(gls[0].len() == alphabet(0, cb as nat));
        assert(gls[1].len() == 256 && gls[2].len() == 256 && gls[3].len() == 256);
        assert(gls[4].len() == 40);
        assert(forall|j: int| 0 <= j < 5 ==> #[trigger] hcode_ok(g.codes@[j], gls[j]));
        assert(hcode_ok(g.codes@[0], gls[0]) && hcode_ok(g.codes@[1], gls[1]) && hcode_ok(g.codes@[2], gls[2])
            && hcode_ok(g.codes@[3], gls[3]) && hcode_ok(g.codes@[4], gls[4]));
        assert(pre.len() == i);
        lemma_dp_unfold(b, old(br).pos(), img, pre, old(cache)@);
    }
    if br.ip <= data.len() && data.len() - br.ip >= 8 {
        if try_lit(br, data, out, cache, i, cb, g, Ghost(img)) {
            proof {
                assert(br.work@ <= wk + pix_cost()) by {
                    assert(refill_cost() == 9 && pix_cost() == 110);
                }
            }
            return Ok(i + 1);
        }
    }
    br.work = Ghost(br.work@ + 1);
    assert(br.pos() == old(br).pos());
    let ghost p0 = br.pos();
    let s = match br.read_symbol(data, &g.codes[0], Ghost(gls[0])) {
        Some(s) => s,
        None => return Err(Error::Bitstream),
    };
    assert(read_symbol(gls[0], b, p0) is Some);
    assert(read_symbol(gls[0], b, p0).unwrap().0 == s);
    if s < 256 {
        let ghost p1 = br.pos();
        proof {
            lemma_lit_unfold(b, p1, img, pre, old(cache)@, s as nat);
            assert(read_symbol(gls[0], b, old(br).pos()) == Some((s as nat, p1)));
            assert(decode_pixels(b, old(br).pos(), img, pre, old(cache)@) == lit_rest(b, p1, img, pre, old(cache)@, s as nat));
        }
        let r = match br.read_symbol(data, &g.codes[1], Ghost(gls[1])) {
            Some(v) => v,
            None => {
                proof {
                    assert(read_symbol(gls[1], b, p1) is None);
                    assert(group_at(img, pre.len())[1] == gls[1]);
                    assert(lit_rest(b, p1, img, pre, old(cache)@, s as nat) is None);
                }
                return Err(Error::Bitstream);
            },
        };
        let bl = match br.read_symbol(data, &g.codes[2], Ghost(gls[2])) {
            Some(v) => v,
            None => return Err(Error::Bitstream),
        };
        let a = match br.read_symbol(data, &g.codes[3], Ghost(gls[3])) {
            Some(v) => v,
            None => return Err(Error::Bitstream),
        };
        proof {
            lemma_argb(a, r, s, bl);
        }
        let c = (a << 24) | (r << 16) | (s << 8) | bl;
        set32(out.as_mut_slice(), i, c);
        cache_put(cache, cb, c);
        proof {
            assert(out@.subrange(0, i + 1) =~= pre.push(c));
            assert(br.work@ <= wk + pix_cost()) by {
                assert(sym_cost() == 26 && pix_cost() == 110);
            }
        }
        Ok(i + 1)
    } else if s < 280 {
        backref(br, data, out, cache, i, s - 256, &g.codes[4], Ghost(gls[4]), w, npix, cb, Ghost(img))
    } else {
        proof {
            assert(cb > 0);
            assert(s - 280 < cache@.len());
        }
        let c = get32(cache.as_slice(), (s - 280) as usize);
        set32(out.as_mut_slice(), i, c);
        cache_put(cache, cb, c);
        proof {
            assert(out@.subrange(0, i + 1) =~= pre.push(c));
            assert(br.work@ <= wk + pix_cost()) by {
                assert(sym_cost() == 26 && pix_cost() == 110);
            }
        }
        Ok(i + 1)
    }
}

/// Decodes the pixels of an entropy-coded image whose color cache bits,
/// prefix code groups and entropy image are read.
pub fn decode_image_data(
    br: &mut BitReader,
    data: &[u8],
    w: usize,
    h: usize,
    cb: u32,
    groups: &Vec<Group>,
    Ghost(gl): Ghost<Seq<Seq<Seq<u8>>>>,
    hb: u32,
    meta: &Vec<u32>,
) -> (r: Result<Vec<u32>, Error>)
    requires
        old(br).ok(data@),
        1 <= w <= 16384,
        1 <= h <= 16384,
        cb <= 11,
        groups_ok(groups@, gl),
        groups_shape(gl, cb as nat),
        gl.len() >= 1,
        meta_ok(w as nat, h as nat, hb as nat, meta@, gl.len()),
    ensures
        final(br).ok(data@),
        match decode_with(data@, old(br).pos(), w as nat, h as nat, cb as nat, gl, hb as nat, meta@) {
            Some((px, p)) => (r matches Ok(v) && v@ == px && final(br).pos() == p) || r == Err::<Vec<u32>, Error>(Error::OutOfMemory),
            None => r is Err,
        },
        r != Err::<Vec<u32>, Error>(Error::Unsupported),
        final(br).work@ <= old(br).work@ + pix_cost() * (w * h) as nat,
        final(br).pos() >= old(br).pos(),
{
    hide(decode_pixels);
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    let ghost img = img_of(w as nat, h as nat, cb as nat, gl, hb as nat, meta@);
    let ghost res = decode_with(b, p0, w as nat, h as nat, cb as nat, gl, hb as nat, meta@);
    proof {
        assert(w * h <= 16384 * 16384) by (nonlinear_arith)
            requires
                w <= 16384,
                h <= 16384,
        ;
        lemma2_to64();
    }
    let npix = w * h;
    let csz: usize = if cb == 0 {
        0
    } else {
        proof {
            lemma_usize_shl_is_mul(1, cb as usize);
            lemma_pow2_strictly_increases(cb as nat, 12);
        }
        1usize << cb
    };
    let mut out = match alloc_u32(npix) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut cache = match alloc_u32(csz) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let hx: usize = if hb == 0 {
        0
    } else {
        subsample_exec(w, hb)
    };
    proof {
        assert(out@.subrange(0, 0) =~= seq![]);
        assert(cache@ =~= Seq::new(cache_size(cb as nat), |i: int| 0u32));
    }
    let mut i: usize = 0;
    let mut x: usize = 0;
    let mut y: usize = 0;
    while i < npix
        invariant
            br.ok(b),
            b == data@,
            loop_ok(img, w, h, npix, cb, groups@, gl, hb, hx, meta@),
            i <= npix,
            x == (i as nat) % (w as nat),
            y == (i as nat) / (w as nat),
            out@.len() == npix,
            cache@.len() == cache_size(cb as nat),
            decode_pixels(b, br.pos(), img, out@.subrange(0, i as int), cache@) == res,
            res == decode_with(b, p0, w as nat, h as nat, cb as nat, gl, hb as nat, meta@),
            p0 == old(br).pos(),
            w0 == old(br).work@,
            br.pos() >= p0,
            br.work@ <= w0 + pix_cost() * i,
        decreases npix - i,
    {
        let ghost wk = br.work@;
        let i2 = match step(br, data, &mut out, &mut cache, i, x, y, w, h, npix, cb, groups, Ghost(gl), hb, hx, meta, Ghost(img)) {
            Ok(v) => v,
            Err(e) => {
                proof {
                    assert(br.work@ <= w0 + pix_cost() * npix) by (nonlinear_arith)
                        requires
                            br.work@ <= wk + pix_cost(),
                            wk <= w0 + pix_cost() * i,
                            i < npix,
                    ;
                }
                return Err(e);
            },
        };
        proof {
            assert(br.work@ <= w0 + pix_cost() * i2) by (nonlinear_arith)
                requires
                    br.work@ <= wk + pix_cost() * (i2 - i),
                    wk <= w0 + pix_cost() * i,
                    i < i2,
            ;
            lemma_xy_step(i as nat, w as nat, x as nat, y as nat);
        }
        if i2 == i + 1 {
            if x + 1 < w {
                x = x + 1;
            } else {
                x = 0;
                y = y + 1;
            }
        } else {
            x = i2 % w;
            y = i2 / w;
        }
        i = i2;
    }
    proof {
        lemma_dp_done(b, br.pos(), img, out@.subrange(0, i as int), cache@);
        assert(out@.subrange(0, i as int) =~= out@);
    }
    Ok(out)
}

/// The pixels decoded are the image's.
pub proof fn lemma_decode_with_len(b: Seq<u8>, pos: int, w: nat, h: nat, cb: nat, gl: Seq<Seq<Seq<u8>>>, hb: nat, meta: Seq<u32>)
    ensures
        decode_with(b, pos, w, h, cb, gl, hb, meta) matches Some((px, p)) ==> px.len() == w * h && p >= pos,
{
    crate::slemmas::lemma_dp_len(b, pos, img_of(w, h, cb, gl, hb, meta), seq![], Seq::new(cache_size(cb), |i: int| 0u32));
}

} // verus!

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::Bitstream => "not a valid WebP image",
            Error::OutOfMemory => "out of memory",
            Error::Unsupported => "unsupported WebP image",
        })
    }
}

impl std::error::Error for Error {}
