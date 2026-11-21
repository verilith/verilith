//! The coefficients of one block, for each kind of scan.
use crate::bits::*;
use crate::huff::*;
use crate::num::*;
use crate::prims::*;
use crate::spec::*;
use crate::types::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// `2^a <= 2^b` for `a <= b`.
pub proof fn lemma_pow2_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
        pow2(a) >= 1,
{
    lemma_pow2_pos(a);
    if a < b {
        lemma_pow2_strictly_increases(a, b);
    }
}

/// A symbol split into its run and size.
#[inline(always)]
pub fn run_size(sym: u8) -> (r: (usize, u32))
    ensures
        r.0 == sym as int / 16,
        r.1 == sym as int % 16,
        r.0 <= 15,
        r.1 <= 15,
{
    assert((sym >> 4) == sym / 16 && (sym & 15) == sym % 16) by (bit_vector);
    ((sym >> 4) as usize, (sym & 15) as u32)
}

/// `v * 2^al` as a coefficient.
#[inline(always)]
pub fn shl16(v: i64, al: u8) -> (r: i16)
    requires
        al <= 13,
        -0x1_0000_0000 < v < 0x1_0000_0000,
    ensures
        r == wrap16(v * pow2(al as nat)) as i16,
{
    proof {
        lemma_pow2_le(al as nat, 13);
        lemma2_to64();
    }
    let m = pw2(al as u32) as i64;
    assert(-0x2000_0000_0000 < v * m < 0x2000_0000_0000) by (nonlinear_arith)
        requires
            -0x1_0000_0000 < v < 0x1_0000_0000,
            1 <= m <= 8192,
    ;
    let x = v * m;
    proof {
        lemma_wrap16(x);
    }
    x as i16
}

/// `2^al` as a coefficient.
#[inline(always)]
pub fn bit16_x(al: u8) -> (r: i16)
    requires
        al <= 13,
    ensures
        r == bit16(al as int),
        r == pow2(al as nat),
        1 <= r <= 8192,
{
    proof {
        lemma_pow2_le(al as nat, 13);
        lemma2_to64();
    }
    pw2(al as u32) as i16
}

/// An end-of-band run of `r` extra bits.
#[inline(always)]
pub fn eob_run(br: &mut BitReader, data: &[u8], r: usize) -> (run: u32)
    requires
        old(br).wf(data@),
        r <= 14,
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        final(br).n@ == old(br).n@ + r,
        run == pow2(r as nat) + ebits(old(br).e(data@), old(br).n@, r as nat) - 1,
        old(br).over() ==> final(br).over(),
{
    proof {
        lemma_ebits_bound(br.e(data@), br.n@, r as nat);
        lemma_pow2_le(r as nat, 14);
        lemma2_to64();
    }
    let mut run: u32 = pw2(r as u32) as u32;
    if r != 0 {
        run += br.get_r(data, r as u32);
    }
    run - 1
}

/// A block of a baseline scan (see `base_block_i`), with the bit reader
/// copied into a local for the duration so that it lives in registers.
#[inline(never)]
pub fn base_block_x(
    br: &mut BitReader,
    data: &[u8],
    dd: &Derived,
    dt: &HuffTab,
    ad: &Derived,
    at: &HuffTab,
    pred: i32,
    a: &mut Vec<i16>,
    o: usize,
) -> (r: i32)
    requires
        old(br).wf(data@),
        dd.wf(dt@),
        huff_dc_ok(dt@),
        ad.wf(at@),
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, r as int, final(br).n@) == base_block(
            dt@,
            at@,
            old(br).e(data@),
            old(br).n@,
            pred as int,
            old(a)@,
            o as int,
        ),
{
    // On a copy of the reader, so that its fields stay in registers. The
    // DC difference is read as an AC symbol and its value are: a size
    // below 16, then that many bits.
    let mut b = *br;
    let diff = dc_diff_r(&mut b, data, dd, dt);
    let p64 = pred as i64 + diff as i64;
    let p = p64 as i32;
    proof {
        lemma_wrap32(p64);
        lemma_wrap16(p as i64);
    }
    vset(a, o, p as i16);
    base_ac_i(&mut b, data, ad, at, a, o);
    *br = b;
    p
}

/// The AC coefficients of a baseline block.
#[inline(always)]
fn base_ac_i(br: &mut BitReader, data: &[u8], ad: &Derived, at: &HuffTab, a: &mut Vec<i16>, o: usize)
    requires
        old(br).wf(data@),
        ad.wf(at@),
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, final(br).n@) == base_ac(at@, old(br).e(data@), old(br).n@, 1, old(a)@, o as int),
{
    let ghost e = br.e(data@);
    let ghost a1 = a@;
    let ghost n1 = br.n@;
    let mut k: usize = 1;
    while k < 64
        invariant
            1 <= k <= 79,
            br.wf(data@),
            ad.wf(at@),
            br.p0 == old(br).p0,
            e == br.e(data@),
            e == old(br).e(data@),
            n1 == old(br).n@,
            a1 == old(a)@,
            old(br).over() ==> br.over(),
            a.len() == old(a).len(),
            o + 64 <= a.len(),
            base_ac(at@, e, br.n@, k as int, a@, o as int) == base_ac(at@, e, n1, 1, a1, o as int),
        decreases 80 - k,
    {
        let ghost np = br.n@;
        let ghost ap = a@;
        let (sym, v) = decode_ac(br, data, ad, at);
        let (r, s) = run_size(sym);
        if s != 0 {
            vset(a, o + zzx(k + r), v as i16);
            k += r + 1;
        } else if r != 15 {
            proof {
                assert(base_ac(at@, e, np, k as int, ap, o as int) == (ap, br.n@));
            }
            return;
        } else {
            k += 16;
        }
    }
}

/// Returns the new prediction, or `None` if it left 32 bits.
pub fn dc_first_x(
    br: &mut BitReader,
    data: &[u8],
    dd: &Derived,
    dt: &HuffTab,
    pred: i32,
    al: u8,
    a: &mut Vec<i16>,
    o: usize,
) -> (r: Option<i32>)
    requires
        old(br).wf(data@),
        dd.wf(dt@),
        huff_dc_ok(dt@),
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        ({
            let sp = dc_first(dt@, old(br).e(data@), old(br).n@, pred as int, al as int, old(a)@, o as int);
            &&& final(a)@ == sp.0
            &&& final(br).n@ == sp.2
            &&& r is Some == sp.3
            &&& r matches Some(p) ==> p == sp.1
        }),
{
    let diff = dc_diff_x(br, data, dd, dt);
    let p = pred as i64 + diff as i64;
    vset(a, o, shl16(p, al));
    if p < -0x8000_0000 || p > 0x7fff_ffff {
        None
    } else {
        Some(p as i32)
    }
}

pub fn dc_refine_x(br: &mut BitReader, data: &[u8], al: u8, a: &mut Vec<i16>, o: usize)
    requires
        old(br).wf(data@),
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, final(br).n@) == dc_refine(old(br).e(data@), old(br).n@, al as int, old(a)@, o as int),
{
    if bit1(br, data) == 1 {
        let c = a[o];
        vset(a, o, c | bit16_x(al));
    }
}

/// Returns the end-of-band run.
#[inline(always)]
fn ac_first_i(
    br: &mut BitReader,
    data: &[u8],
    ad: &Derived,
    at: &HuffTab,
    ss: u8,
    se: u8,
    al: u8,
    a: &mut Vec<i16>,
    o: usize,
) -> (res: u32)
    requires
        old(br).wf(data@),
        ad.wf(at@),
        se <= 63,
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, final(br).n@, res as int) == ac_first(
            at@,
            old(br).e(data@),
            old(br).n@,
            ss as int,
            se as int,
            al as int,
            old(a)@,
            o as int,
        ),
{
    let ghost e = br.e(data@);
    let ghost n0 = br.n@;
    let mut k: usize = ss as usize;
    while k <= se as usize
        invariant
            k <= 300,
            se <= 63,
            al <= 13,
            br.wf(data@),
            ad.wf(at@),
            br.p0 == old(br).p0,
            e == br.e(data@),
            e == old(br).e(data@),
            old(br).over() ==> br.over(),
            n0 == old(br).n@,
            a.len() == old(a).len(),
            o + 64 <= a.len(),
            ac_first(at@, e, br.n@, k as int, se as int, al as int, a@, o as int) == ac_first(
                at@,
                e,
                n0,
                ss as int,
                se as int,
                al as int,
                old(a)@,
                o as int,
            ),
        decreases 300 - k,
    {
        let (sym, v) = decode_ac(br, data, ad, at);
        let (r, s) = run_size(sym);
        if s != 0 {
            vset(a, o + zzx(k + r), shl16(v as i64, al));
            k += r + 1;
        } else if r == 15 {
            k += 16;
        } else {
            return eob_run(br, data, r);
        }
    }
    0
}

/// `ac_first_i` with the bit reader copied into a local for the duration, so
/// that it lives in registers.
#[inline(never)]
pub fn ac_first_x(
    br: &mut BitReader,
    data: &[u8],
    ad: &Derived,
    at: &HuffTab,
    ss: u8,
    se: u8,
    al: u8,
    a: &mut Vec<i16>,
    o: usize,
) -> (res: u32)
    requires
        old(br).wf(data@),
        ad.wf(at@),
        se <= 63,
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, final(br).n@, res as int) == ac_first(
            at@,
            old(br).e(data@),
            old(br).n@,
            ss as int,
            se as int,
            al as int,
            old(a)@,
            o as int,
        ),
{
    let mut b = *br;
    let r = ac_first_i(&mut b, data, ad, at, ss, se, al, a, o);
    *br = b;
    r
}

#[inline(always)]
pub fn refine_coef_x(c: i16, bit: i32, al: u8) -> (r: i16)
    requires
        al <= 13,
    ensures
        r == refine_coef(c, bit as int, al as int),
{
    let p1 = bit16_x(al);
    if bit == 1 && c & p1 == 0 {
        if c >= 0 {
            let x = c as i64 + p1 as i64;
            proof {
                lemma_wrap16(x);
            }
            x as i16
        } else {
            let x = c as i64 - p1 as i64;
            proof {
                lemma_wrap16(x);
            }
            x as i16
        }
    } else {
        c
    }
}

/// Returns the `k` the pass stopped at.
#[inline(always)]
fn refine_skip_i(
    br: &mut BitReader,
    data: &[u8],
    k: usize,
    se: u8,
    r: usize,
    al: u8,
    a: &mut Vec<i16>,
    o: usize,
) -> (res: usize)
    requires
        old(br).wf(data@),
        k <= se + 1,
        se <= 63,
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        k <= res <= se + 1,
        (final(a)@, final(br).n@, res as int) == refine_skip(
            old(br).e(data@),
            old(br).n@,
            k as int,
            se as int,
            r as int,
            al as int,
            old(a)@,
            o as int,
        ),
{
    let ghost e = br.e(data@);
    let ghost n0 = br.n@;
    let mut kk = k;
    let mut rr = r;
    while kk <= se as usize
        invariant
            k <= kk <= se + 1,
            se <= 63,
            al <= 13,
            br.wf(data@),
            br.p0 == old(br).p0,
            e == br.e(data@),
            e == old(br).e(data@),
            old(br).over() ==> br.over(),
            n0 == old(br).n@,
            a.len() == old(a).len(),
            o + 64 <= a.len(),
            refine_skip(e, br.n@, kk as int, se as int, rr as int, al as int, a@, o as int) == refine_skip(
                e,
                n0,
                k as int,
                se as int,
                r as int,
                al as int,
                old(a)@,
                o as int,
            ),
        decreases se + 1 - kk,
    {
        let i = o + zzx(kk);
        let c = a[i];
        if c != 0 {
            let b = bit1_r(br, data);
            vset(a, i, refine_coef_x(c, b, al));
        } else if rr == 0 {
            return kk;
        } else {
            rr -= 1;
        }
        kk += 1;
    }
    kk
}

#[inline(always)]
fn refine_rest_i(br: &mut BitReader, data: &[u8], k: usize, se: u8, al: u8, a: &mut Vec<i16>, o: usize)
    requires
        old(br).wf(data@),
        k <= se + 1,
        se <= 63,
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, final(br).n@) == refine_rest(
            old(br).e(data@),
            old(br).n@,
            k as int,
            se as int,
            al as int,
            old(a)@,
            o as int,
        ),
{
    let ghost e = br.e(data@);
    let ghost n0 = br.n@;
    let mut kk = k;
    while kk <= se as usize
        invariant
            k <= kk <= se + 1,
            se <= 63,
            al <= 13,
            br.wf(data@),
            br.p0 == old(br).p0,
            e == br.e(data@),
            e == old(br).e(data@),
            old(br).over() ==> br.over(),
            n0 == old(br).n@,
            a.len() == old(a).len(),
            o + 64 <= a.len(),
            refine_rest(e, br.n@, kk as int, se as int, al as int, a@, o as int) == refine_rest(
                e,
                n0,
                k as int,
                se as int,
                al as int,
                old(a)@,
                o as int,
            ),
        decreases se + 1 - kk,
    {
        let i = o + zzx(kk);
        let c = a[i];
        if c != 0 {
            let b = bit1_r(br, data);
            vset(a, i, refine_coef_x(c, b, al));
        }
        kk += 1;
    }
}

/// `refine_rest_i` with the bit reader copied into a local for the duration, so
/// that it lives in registers.
#[inline(never)]
pub fn refine_rest_x(br: &mut BitReader, data: &[u8], k: usize, se: u8, al: u8, a: &mut Vec<i16>, o: usize)
    requires
        old(br).wf(data@),
        k <= se + 1,
        se <= 63,
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, final(br).n@) == refine_rest(
            old(br).e(data@),
            old(br).n@,
            k as int,
            se as int,
            al as int,
            old(a)@,
            o as int,
        ),
{
    let mut b = *br;
    refine_rest_i(&mut b, data, k, se, al, a, o);
    *br = b;
}

/// Returns the end-of-band run.
#[inline(always)]
fn ac_refine_i(
    br: &mut BitReader,
    data: &[u8],
    ad: &Derived,
    at: &HuffTab,
    ss: u8,
    se: u8,
    al: u8,
    a: &mut Vec<i16>,
    o: usize,
) -> (res: u32)
    requires
        old(br).wf(data@),
        ad.wf(at@),
        se <= 63,
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, final(br).n@, res as int) == ac_refine(
            at@,
            old(br).e(data@),
            old(br).n@,
            ss as int,
            se as int,
            al as int,
            old(a)@,
            o as int,
        ),
{
    let ghost e = br.e(data@);
    let ghost n0 = br.n@;
    let mut k: usize = ss as usize;
    while k <= se as usize
        invariant
            k <= 300,
            se <= 63,
            al <= 13,
            br.wf(data@),
            ad.wf(at@),
            br.p0 == old(br).p0,
            e == br.e(data@),
            e == old(br).e(data@),
            old(br).over() ==> br.over(),
            n0 == old(br).n@,
            a.len() == old(a).len(),
            o + 64 <= a.len(),
            ac_refine(at@, e, br.n@, k as int, se as int, al as int, a@, o as int) == ac_refine(
                at@,
                e,
                n0,
                ss as int,
                se as int,
                al as int,
                old(a)@,
                o as int,
            ),
        decreases 300 - k,
    {
        let sym = decode_sym(br, data, ad, at);
        let (r, s) = run_size(sym);
        if s != 0 {
            let m = bit16_x(al);
            let v: i16 = if bit1_r(br, data) == 1 {
                m
            } else {
                -m
            };
            let k2 = refine_skip_i(br, data, k, se, r, al, a, o);
            assert(k2 >= k);
            vset(a, o + zzx(k2), v);
            k = k2 + 1;
        } else if r == 15 {
            let k2 = refine_skip_i(br, data, k, se, 15, al, a, o);
            assert(k2 >= k);
            k = k2 + 1;
        } else {
            let run = eob_run(br, data, r);
            refine_rest_i(br, data, k, se, al, a, o);
            return run;
        }
    }
    0
}

/// `ac_refine_i` with the bit reader copied into a local for the duration, so
/// that it lives in registers.
#[inline(never)]
pub fn ac_refine_x(
    br: &mut BitReader,
    data: &[u8],
    ad: &Derived,
    at: &HuffTab,
    ss: u8,
    se: u8,
    al: u8,
    a: &mut Vec<i16>,
    o: usize,
) -> (res: u32)
    requires
        old(br).wf(data@),
        ad.wf(at@),
        se <= 63,
        al <= 13,
        o + 64 <= old(a).len(),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        final(a).len() == old(a).len(),
        (final(a)@, final(br).n@, res as int) == ac_refine(
            at@,
            old(br).e(data@),
            old(br).n@,
            ss as int,
            se as int,
            al as int,
            old(a)@,
            o as int,
        ),
{
    let mut b = *br;
    let r = ac_refine_i(&mut b, data, ad, at, ss, se, al, a, o);
    *br = b;
    r
}

} // verus!

