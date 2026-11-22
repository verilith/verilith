//! Pixel arithmetic of the transforms (§4), proven to match the spec.
#[cfg(verus_only)]
use crate::pixels::lemma_argb;
#[cfg(verus_only)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// `x`, through an empty `asm!` the optimizer cannot see into. It keeps a
/// per-channel value in a general register, so LLVM's SLP vectorizer does
/// not pack the four channels into NEON lanes: on AArch64 the moves
/// between the register files cost more than the vector saves, and they
/// sit on the pixel-to-pixel dependency chain.
#[verifier::external_body]
#[inline(always)]
pub fn opaque32(x: u32) -> (r: u32)
    ensures
        r == x,
{
    #[allow(unused_mut)]
    let mut m = x;
    #[cfg(target_arch = "aarch64")]
    unsafe {
        core::arch::asm!("/* {0:w} */", inout(reg) m, options(pure, nomem, nostack, preserves_flags));
    }
    #[cfg(target_arch = "x86_64")]
    unsafe {
        core::arch::asm!("/* {0:e} */", inout(reg) m, options(pure, nomem, nostack, preserves_flags));
    }
    m
}

/// The four channels of a pixel.
#[inline(always)]
pub fn chans(c: u32) -> (r: (u32, u32, u32, u32))
    ensures
        r.0 == alpha(c) && r.1 == red(c) && r.2 == green(c) && r.3 == blue(c),
        r.0 < 256 && r.1 < 256 && r.2 < 256 && r.3 < 256,
{
    proof {
        assert(c >> 24u32 < 256 && (c >> 16u32) & 0xffu32 < 256 && (c >> 8u32) & 0xffu32 < 256 && c & 0xffu32 < 256)
            by (bit_vector);
    }
    (c >> 24, (c >> 16) & 0xff, (c >> 8) & 0xff, c & 0xff)
}

/// A pixel from its channels.
#[inline(always)]
pub fn pack(a: u32, r: u32, g: u32, b: u32) -> (c: u32)
    requires
        a < 256,
        r < 256,
        g < 256,
        b < 256,
    ensures
        c == argb(a as nat, r as nat, g as nat, b as nat),
{
    proof {
        lemma_argb(a, r, g, b);
    }
    (a << 24) | (r << 16) | (g << 8) | b
}

/// The channels of `argb(a, r, g, b)`.
pub proof fn lemma_chans_argb(a: nat, r: nat, g: nat, b: nat)
    requires
        a < 256,
        r < 256,
        g < 256,
        b < 256,
    ensures
        alpha(argb(a, r, g, b)) == a,
        red(argb(a, r, g, b)) == r,
        green(argb(a, r, g, b)) == g,
        blue(argb(a, r, g, b)) == b,
{
    let (a3, r3, g3, b3) = (a as u32, r as u32, g as u32, b as u32);
    lemma_argb(a3, r3, g3, b3);
    let c = argb(a, r, g, b);
    assert(c == (a3 << 24u32) | (r3 << 16u32) | (g3 << 8u32) | b3);
    assert({
        let c = (a3 << 24u32) | (r3 << 16u32) | (g3 << 8u32) | b3;
        c >> 24u32 == a3 && (c >> 16u32) & 0xffu32 == r3 && (c >> 8u32) & 0xffu32 == g3 && c & 0xffu32 == b3
    }) by (bit_vector)
        requires
            a3 < 256,
            r3 < 256,
            g3 < 256,
            b3 < 256,
    ;
}

#[inline(always)]
pub fn add_px_exec(x: u32, y: u32) -> (r: u32)
    ensures
        r == add_px(x, y),
{
    let (a1, r1, g1, b1) = chans(x);
    let (a2, r2, g2, b2) = chans(y);
    pack((a1 + a2) % 256, (r1 + r2) % 256, (g1 + g2) % 256, (b1 + b2) % 256)
}

#[inline(always)]
pub fn avg2_exec(x: u32, y: u32) -> (r: u32)
    ensures
        r == avg2(x, y),
{
    let (a1, r1, g1, b1) = chans(x);
    let (a2, r2, g2, b2) = chans(y);
    pack((a1 + a2) / 2, (r1 + r2) / 2, (g1 + g2) / 2, (b1 + b2) / 2)
}

#[inline(always)]
fn clamp_exec(x: i32) -> (r: u32)
    ensures
        r as nat == clamp(x as int),
        r < 256,
{
    if x < 0 {
        0
    } else if x > 255 {
        255
    } else {
        x as u32
    }
}

#[inline(always)]
fn half_exec(x: i32) -> (r: i32)
    requires
        -1000 <= x <= 1000,
    ensures
        r as int == half_c(x as int),
{
    if x >= 0 {
        x / 2
    } else {
        -((-x) / 2)
    }
}

#[inline(always)]
pub fn clamp_add_sub_full_exec(x: u32, y: u32, z: u32) -> (r: u32)
    ensures
        r == clamp_add_sub_full(x, y, z),
{
    let (a1, r1, g1, b1) = chans(x);
    let (a2, r2, g2, b2) = chans(y);
    let (a3, r3, g3, b3) = chans(z);
    pack(
        clamp_exec(a1 as i32 + a2 as i32 - a3 as i32),
        clamp_exec(r1 as i32 + r2 as i32 - r3 as i32),
        clamp_exec(g1 as i32 + g2 as i32 - g3 as i32),
        clamp_exec(b1 as i32 + b2 as i32 - b3 as i32),
    )
}

#[inline(always)]
fn cash(a: u32, b: u32) -> (r: u32)
    requires
        a < 256,
        b < 256,
    ensures
        r as nat == clamp(a + half_c(a - b)),
        r < 256,
{
    opaque32(clamp_exec(a as i32 + half_exec(a as i32 - b as i32)))
}

#[inline(always)]
pub fn clamp_add_sub_half_exec(x: u32, y: u32) -> (r: u32)
    ensures
        r == clamp_add_sub_half(x, y),
{
    let (a1, r1, g1, b1) = chans(x);
    let (a2, r2, g2, b2) = chans(y);
    pack(cash(a1, a2), cash(r1, r2), cash(g1, g2), cash(b1, b2))
}

/// `absd` as a `u32` kept in a general register (`opaque32`).
#[inline(always)]
fn absd_g(a: u32, b: u32) -> (r: u32)
    requires
        a < 256,
        b < 256,
    ensures
        r as int == abs(a - b),
        r < 256,
{
    opaque32(absd(a, b) as u32)
}

#[inline(always)]
fn absd(a: u32, b: u32) -> (r: i32)
    requires
        a < 256,
        b < 256,
    ensures
        r as int == abs(a - b),
        0 <= r < 256,
{
    let d = a as i32 - b as i32;
    if d < 0 {
        -d
    } else {
        d
    }
}

#[inline(always)]
pub fn select_exec(l: u32, t: u32, tl: u32) -> (r: u32)
    ensures
        r == select(l, t, tl),
{
    let (la, lr, lg, lb) = chans(l);
    let (ta, tr, tg, tb) = chans(t);
    let (ca, cr, cg, cb) = chans(tl);
    let pl = absd(ta, ca) + absd(tr, cr) + absd(tg, cg) + absd(tb, cb);
    let pt = absd(la, ca) + absd(lr, cr) + absd(lg, cg) + absd(lb, cb);
    if pl < pt {
        l
    } else {
        t
    }
}

/// `add_px(s, select(l, t, tl))`, with both sums formed before the
/// choice, so the choice is the only step that waits for the distances.
#[inline(always)]
pub fn select_add_exec(s: u32, l: u32, t: u32, tl: u32) -> (r: u32)
    ensures
        r == add_px(s, select(l, t, tl)),
{
    let cl = crate::vpx::add_px_swar(s, l);
    let ct = crate::vpx::add_px_swar(s, t);
    let (la, lr, lg, lb) = chans(l);
    let (ta, tr, tg, tb) = chans(t);
    let (ca, cr, cg, cb) = chans(tl);
    let pl = absd_g(ta, ca) + absd_g(tr, cr) + absd_g(tg, cg) + absd_g(tb, cb);
    let pt = absd_g(la, ca) + absd_g(lr, cr) + absd_g(lg, cg) + absd_g(lb, cb);
    if pl < pt {
        cl
    } else {
        ct
    }
}

/// Predictor mode `m` (`spec::predict_mode`).
pub fn predict_mode_exec(m: u32, l: u32, t: u32, tr: u32, tl: u32) -> (r: u32)
    ensures
        r == predict_mode(m as nat, l, t, tr, tl),
{
    match m {
        1 => l,
        2 => t,
        3 => tr,
        4 => tl,
        5 => avg2_exec(avg2_exec(l, tr), t),
        6 => avg2_exec(l, tl),
        7 => avg2_exec(l, t),
        8 => avg2_exec(tl, t),
        9 => avg2_exec(t, tr),
        10 => avg2_exec(avg2_exec(l, tl), avg2_exec(t, tr)),
        11 => select_exec(l, t, tl),
        12 => clamp_add_sub_full_exec(l, t, tl),
        13 => clamp_add_sub_half_exec(avg2_exec(l, t), tl),
        _ => 0xff00_0000,
    }
}

/// `ColorTransformDelta` (`spec::delta`).
#[inline(always)]
fn delta_exec(t: u32, c: u32) -> (r: i32)
    requires
        t < 256,
        c < 256,
    ensures
        r as int == delta(t, c),
        -512 <= r <= 512,
{
    let st: i32 = if t < 128 {
        t as i32
    } else {
        t as i32 - 256
    };
    let sc: i32 = if c < 128 {
        c as i32
    } else {
        c as i32 - 256
    };
    proof {
        assert(-16384 <= st * sc <= 16384) by (nonlinear_arith)
            requires
                -128 <= st < 128,
                -128 <= sc < 128,
        ;
    }
    let p = st * sc;
    // p >> 5, rounding down: shifted to be nonnegative first.
    let q = ((p + 16384) as u32 / 32) as i32 - 512;
    proof {
        let pi = p as int;
        assert(q == pi / 32) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pi, 32);
            vstd::arithmetic::div_mod::lemma_mod_bound(pi, 32);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(pi + 16384, 32, pi / 32 + 512, pi % 32);
        }
    }
    q
}

/// Undoes the color transform on one pixel (`spec::uncolor`).
#[inline(always)]
pub fn uncolor_exec(c: u32, e: u32) -> (r: u32)
    ensures
        r == uncolor(c, e),
{
    let (a, red_c, g, b) = chans(c);
    let g2r = e & 0xff;
    let g2b = (e >> 8) & 0xff;
    let r2b = (e >> 16) & 0xff;
    proof {
        assert(e & 0xffu32 < 256 && (e >> 8u32) & 0xffu32 < 256 && (e >> 16u32) & 0xffu32 < 256) by (bit_vector);
    }
    let nr = ((red_c as i32 + delta_exec(g2r, g) + 512) as u32) % 256;
    let nb = ((b as i32 + delta_exec(g2b, g) + delta_exec(r2b, nr) + 1024) as u32) % 256;
    proof {
        let snr = (red_c + delta(g2r, g)) % 256;
        assert(nr == snr) by {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish((red_c + delta(g2r, g)) as int, 256);
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish((red_c + delta(g2r, g) + 256) as int, 256);
        }
        let sb = blue(c) + delta(g2b, green(c)) + delta(r2b, nr);
        assert(nb == sb % 256) by {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(sb, 256);
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(sb + 256, 256);
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(sb + 512, 256);
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(sb + 768, 256);
        }
    }
    pack(a, nr, g, nb)
}

/// Undoes subtract green on one pixel (`spec::add_green`).
#[inline(always)]
pub fn add_green_exec(c: u32) -> (r: u32)
    ensures
        r == add_green(c),
{
    let (a, red_c, g, b) = chans(c);
    pack(a, (red_c + g) % 256, g, (b + g) % 256)
}

} // verus!
