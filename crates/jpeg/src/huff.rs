//! Huffman tables: checking one, and decoding with it.
use crate::bits::*;
use crate::spec::*;
use crate::types::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

pub proof fn lemma_hbase_nonneg(t: HuffTable, l: int)
    ensures
        0 <= hbase(t, l),
    decreases l,
{
    if l > 1 {
        lemma_hbase_nonneg(t, l - 1);
    }
}

pub proof fn lemma_hbase_mono(t: HuffTable, a: int, b: int)
    requires
        a <= b,
    ensures
        hbase(t, a) <= hbase(t, b),
        0 <= hbase(t, a),
    decreases b - a,
{
    lemma_hbase_nonneg(t, a);
    if a < b {
        lemma_hbase_mono(t, a, b - 1);
        lemma_hbase_nonneg(t, b - 1);
    }
}

pub proof fn lemma_hfirst_nonneg(t: HuffTable, l: int)
    ensures
        0 <= hfirst(t, l),
    decreases l,
{
    if l > 1 {
        lemma_hfirst_nonneg(t, l - 1);
    }
}

pub const P2: [i32; 17] = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536];

/// `2^s`.
#[inline(always)]
pub fn pw2(s: u32) -> (r: i32)
    requires
        s <= 16,
    ensures
        r == pow2(s as nat),
{
    proof {
        lemma2_to64();
    }
    P2[s as usize]
}

/// Prepares a table for decoding, or `None` if it is not usable. A DC
/// table (`dc`) must not have a symbol above 15.
pub fn derive(t: &HuffTab, dc: bool) -> (r: Option<Derived>)
    ensures
        r is Some <==> (if dc {
            huff_dc_ok(t@)
        } else {
            huff_ok(t@)
        }),
        r matches Some(d) ==> d.wf(t@),
{
    let mut lim = [0i32; 17];
    let mut off = [0i32; 17];
    let mut ll = [0u32; 17];
    let mut code: i32 = 0;
    let mut base: i32 = 0;
    let mut l: usize = 1;
    while l <= 16
        invariant
            1 <= l <= 17,
            code == hfirst(t@, l as int),
            base == hbase(t@, l as int),
            0 <= code <= pow2(l as nat),
            0 <= base <= 256,
            forall|k: int| 1 <= k < l ==> hfirst(t@, k) + #[trigger] hcount(t@, k) < pow2(k as nat),
            forall|k: int|
                1 <= k < l ==> (#[trigger] lim[k]) == hfirst(t@, k) + hcount(t@, k) && off[k] == hbase(t@, k) - hfirst(
                    t@,
                    k,
                ) && ll[k] == lim[k] * pow2((16 - k) as nat) && 0 <= lim[k],
        decreases 17 - l,
    {
        let n = t.counts[l - 1] as i32;
        proof {
            lemma2_to64();
            lemma_pow2_unfold((l + 1) as nat);
            if l < 16 {
                lemma_pow2_strictly_increases(l as nat, 16);
            }
            assert(hcount(t@, l as int) == n);
        }
        if code + n >= pw2(l as u32) || base + n > 256 {
            proof {
                if base + n > 256 {
                    lemma_hbase_mono(t@, l + 1, 17);
                    assert(hbase(t@, 17) > 256);
                } else {
                    assert(!(hfirst(t@, l as int) + hcount(t@, l as int) < pow2(l as nat)));
                }
                assert(!huff_ok(t@));
            }
            return None;
        }
        let up = pw2(16 - l as u32);
        proof {
            lemma_pow2_adds(l as nat, (16 - l) as nat);
            lemma_pow2_pos((16 - l) as nat);
            assert(0 <= (code + n) * up < 0x1_0000) by (nonlinear_arith)
                requires
                    0 <= code + n < pow2(l as nat),
                    up == pow2((16 - l) as nat),
                    up > 0,
                    pow2(l as nat) * pow2((16 - l) as nat) == 0x1_0000,
            ;
        }
        let ghost lim0 = lim;
        let ghost off0 = off;
        let ghost ll0 = ll;
        let cn = code + n;
        let prod = cn * up;
        lim[l] = cn;
        ll[l] = prod as u32;
        off[l] = base - code;
        proof {
            assert(ll[l as int] == lim[l as int] * pow2((16 - l) as nat));
            assert forall|k: int| 1 <= k < l + 1 implies (#[trigger] lim[k]) == hfirst(t@, k) + hcount(t@, k) && off[k]
                == hbase(t@, k) - hfirst(t@, k) && ll[k] == lim[k] * pow2((16 - k) as nat) && 0 <= lim[k] by {
                if k < l {
                    assert(lim[k] == lim0[k] && off[k] == off0[k] && ll[k] == ll0[k]);
                }
            }
        }
        base += n;
        code = 2 * (code + n);
        l += 1;
    }
    if dc {
        let mut i: usize = 0;
        while i < base as usize
            invariant
                dc,
                i <= base,
                base == hbase(t@, 17),
                base <= 256,
                forall|k: int| 0 <= k < i ==> #[trigger] t@.vals[k] <= 15,
            decreases base - i,
        {
            if t.vals[i] > 15 {
                proof {
                    assert(t@.vals[i as int] > 15);
                    assert(!huff_dc_ok(t@));
                }
                return None;
            }
            i += 1;
        }
    }
    let look = build_look(&ll, &off, &t.vals, Ghost(lim@));
    Some(Derived { lim, off, ll, look })
}

/// The lookahead table: what the next 10 bits decode to, when a code of
/// 10 bits or fewer starts them.
fn build_look(ll: &[u32; 17], off: &[i32; 17], vals: &[u8; 256], Ghost(lim): Ghost<Seq<i32>>) -> (look: [u16; 1024])
    requires
        lim.len() == 17,
        forall|k: int| 1 <= k <= 16 ==> 0 <= #[trigger] lim[k] && ll[k] == lim[k] * pow2((16 - k) as nat),
    ensures
        forall|p: int| 0 <= p < 1024 ==> look_ok(#[trigger] look[p] as int, p, ll@, off@, vals@),
{
    let mut look = [0u16; 1024];
    let mut p: usize = 0;
    // The length for a window never falls as the window grows, so the
    // search for it carries on from the last one.
    let mut l: usize = 1;
    while p < 1024
        invariant
            p <= 1024,
            1 <= l <= 11,
            forall|j: int| 1 <= j < l ==> (#[trigger] ll[j]) <= p * 64,
            lim.len() == 17,
            forall|k: int| 1 <= k <= 16 ==> 0 <= #[trigger] lim[k] && ll[k] == lim[k] * pow2((16 - k) as nat),
            forall|q: int| 0 <= q < p ==> look_ok(#[trigger] look[q] as int, q, ll@, off@, vals@),
        decreases 1024 - p,
    {
        let w = (p as u32) << 6;
        assert(w == p * 64) by (bit_vector)
            requires
                w == (p as u32) << 6,
                p < 1024,
        ;
        while l <= 10 && w >= ll[l]
            invariant
                1 <= l <= 11,
                forall|j: int| 1 <= j < l ==> (#[trigger] ll[j]) <= w,
            decreases 11 - l,
        {
            l += 1;
        }
        let mut e: u16 = 0;
        if l <= 10 {
            let c = (w >> (16 - l as u32)) as i64 + off[l] as i64;
            if 0 <= c && c < 256 {
                let sym = vals[c as usize] as u16;
                e = ((l as u16) << 8) | sym;
                proof {
                    let lu = l as u16;
                    assert(e / 256 == lu && e % 256 == sym && e != 0) by (bit_vector)
                        requires
                            e == (lu << 8) | sym,
                            1 <= lu <= 10,
                            sym < 256,
                    ;
                    lemma_u32_shr_is_div(w, (16 - l) as u32);
                    lemma_look_top(w as int, lim[l as int] as int, l as int);
                    assert(0 <= lim[l as int] && ll[l as int] == lim[l as int] * pow2((16 - l) as nat));
                    assert((w >> ((16 - l) as u32)) as int == (p * 64) / (pow2((16 - l) as nat) as int));
                    assert(look_ok(e as int, p as int, ll@, off@, vals@));
                }
            }
        }
        assert(look_ok(e as int, p as int, ll@, off@, vals@));
        look[p] = e;
        p += 1;
    }
    look
}

/// A multiple of 64 below the limit of a length up to 10 is a whole 64
/// below it.
proof fn lemma_look_top(w: int, lim: int, l: int)
    requires
        1 <= l <= 10,
        w % 64 == 0,
        0 <= w < lim * pow2((16 - l) as nat),
    ensures
        w + 64 <= lim * pow2((16 - l) as nat),
{
    let m = pow2((10 - l) as nat) as int;
    lemma_pow2_adds((10 - l) as nat, 6);
    lemma2_to64();
    assert(pow2((16 - l) as nat) == m * 64);
    let p = w / 64;
    assert(w == p * 64);
    assert(lim * (m * 64) == (lim * m) * 64) by (nonlinear_arith);
    assert(p < lim * m) by (nonlinear_arith)
        requires
            p * 64 < (lim * m) * 64,
    ;
    assert((p + 1) * 64 <= (lim * m) * 64) by (nonlinear_arith)
        requires
            p + 1 <= lim * m,
    ;
}

/// The first `l` bits of a 16-bit window, for `l` up to 10, are the first
/// `l` of its top 10.
proof fn lemma_look_code(v: int, l: int)
    requires
        0 <= v < 0x1_0000,
        1 <= l <= 10,
    ensures
        ((v / 64) * 64) / (pow2((16 - l) as nat) as int) == v / (pow2((16 - l) as nat) as int),
{
    let m = pow2((10 - l) as nat) as int;
    lemma_pow2_adds(6, (10 - l) as nat);
    lemma_pow2_pos((10 - l) as nat);
    lemma2_to64();
    assert(pow2((16 - l) as nat) == 64 * m);
    let p = v / 64;
    lemma_div_denominator(v, 64, m);
    lemma_div_denominator(p * 64, 64, m);
    assert((p * 64) / 64 == p);
}

/// A window at or above the limits of all lengths below `l` holds no code
/// shorter than `l`.
proof fn lemma_dec_skip(t: HuffTable, e: Seq<u8>, n0: int, l: int)
    requires
        1 <= l <= 16,
        forall|j: int| 1 <= j < l ==> ebits(e, n0, 16) >= (hfirst(t, j) + #[trigger] hcount(t, j)) * pow2((16 - j) as nat),
    ensures
        hdec(t, e, n0, l, ebits(e, n0, l as nat)) == huff(t, e, n0),
        hfirst(t, l) <= ebits(e, n0, l as nat),
    decreases l,
{
    if l == 1 {
        lemma_dec_start(t, e, n0);
    } else {
        lemma_dec_skip(t, e, n0, l - 1);
        assert(ebits(e, n0, 16) >= (hfirst(t, l - 1) + hcount(t, l - 1)) * pow2((16 - (l - 1)) as nat));
        lemma_dec_more(t, e, n0, l - 1);
    }
}

/// With a code at least the first of its length, DECODE gives 0 or one of
/// the table's symbols.
pub proof fn lemma_hdec_sym(t: HuffTable, e: Seq<u8>, n: int, l: int, code: int)
    requires
        huff_ok(t),
        1 <= l <= 17,
        hfirst(t, l) <= code,
    ensures
        hdec(t, e, n, l, code).0 == 0 || exists|i: int|
            0 <= i < hbase(t, 17) && hdec(t, e, n, l, code).0 == #[trigger] t.vals[i] as int,
    decreases 17 - l,
{
    if l > 16 {
    } else if code < hfirst(t, l) + hcount(t, l) {
        let i = hbase(t, l) + code - hfirst(t, l);
        lemma_hbase_mono(t, l + 1, 17);
        lemma_hbase_mono(t, l, l);
        assert(0 <= i < hbase(t, 17) && hdec(t, e, n, l, code).0 == t.vals[i] as int);
    } else {
        lemma_ebit_01(e, n + l);
        lemma_hdec_sym(t, e, n, l + 1, 2 * code + ebit(e, n + l));
    }
}

/// A DC symbol is at most 15.
pub proof fn lemma_huff_dc(t: HuffTable, e: Seq<u8>, n: int)
    requires
        huff_dc_ok(t),
    ensures
        0 <= huff(t, e, n).0 <= 15,
{
    lemma_ebit_01(e, n);
    lemma_hdec_sym(t, e, n, 1, ebit(e, n));
    lemma_huff(t, e, n);
}

/// One bit.
#[inline(always)]
pub fn bit1(br: &mut BitReader, data: &[u8]) -> (r: i32)
    requires
        old(br).wf(data@),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        final(br).e(data@) == old(br).e(data@),
        final(br).n@ == old(br).n@ + 1,
        r == ebit(old(br).e(data@), old(br).n@),
        r == 0 || r == 1,
        old(br).over() ==> final(br).over(),
{
    proof {
        reveal_with_fuel(ebits, 2);
        lemma_ebit_01(br.e(data@), br.n@);
    }
    br.get(data, 1) as i32
}

/// One bit, for a reader that its caller keeps in registers.
#[inline(always)]
pub fn bit1_r(br: &mut BitReader, data: &[u8]) -> (r: i32)
    requires
        old(br).wf(data@),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        final(br).e(data@) == old(br).e(data@),
        final(br).n@ == old(br).n@ + 1,
        r == ebit(old(br).e(data@), old(br).n@),
        r == 0 || r == 1,
        old(br).over() ==> final(br).over(),
{
    proof {
        reveal_with_fuel(ebits, 2);
        lemma_ebit_01(br.e(data@), br.n@);
    }
    br.get_r(data, 1) as i32
}

/// A 16-bit window of the input, split after its first `l` bits.
pub proof fn lemma_window(e: Seq<u8>, n0: int, l: int)
    requires
        1 <= l <= 16,
    ensures
        ({
            let m = pow2((16 - l) as nat) as int;
            let c = ebits(e, n0, l as nat);
            let r = ebits(e, n0 + l, (16 - l) as nat);
            &&& ebits(e, n0, 16) == c * m + r
            &&& 0 <= r < m
            &&& 0 <= c < pow2(l as nat)
        }),
{
    lemma_ebits_split(e, n0, l as nat, (16 - l) as nat);
    lemma_ebits_bound(e, n0 + l, (16 - l) as nat);
    lemma_ebits_bound(e, n0, l as nat);
    assert((l as nat + (16 - l) as nat) as nat == 16);
}

/// Decoding starts from the first bit.
pub proof fn lemma_dec_start(t: HuffTable, e: Seq<u8>, n0: int)
    ensures
        hdec(t, e, n0, 1, ebits(e, n0, 1)) == huff(t, e, n0),
        hfirst(t, 1) <= ebits(e, n0, 1),
{
    reveal_with_fuel(ebits, 2);
    lemma_ebit_01(e, n0);
}

/// A window at or above the limit of length `l` holds no code that short.
pub proof fn lemma_dec_more(t: HuffTable, e: Seq<u8>, n0: int, l: int)
    requires
        1 <= l <= 16,
        ebits(e, n0, 16) >= (hfirst(t, l) + hcount(t, l)) * pow2((16 - l) as nat),
    ensures
        l == 16 ==> hdec(t, e, n0, l, ebits(e, n0, l as nat)) == (0int, n0 + 17),
        l < 16 ==> hdec(t, e, n0, l, ebits(e, n0, l as nat)) == hdec(t, e, n0, l + 1, ebits(e, n0, (l + 1) as nat)),
        l < 16 ==> hfirst(t, l + 1) <= ebits(e, n0, (l + 1) as nat),
{
    let c = ebits(e, n0, l as nat);
    let m = pow2((16 - l) as nat) as int;
    let r = ebits(e, n0 + l, (16 - l) as nat);
    let lim = hfirst(t, l) + hcount(t, l);
    lemma_window(e, n0, l);
    assert(c >= lim) by (nonlinear_arith)
        requires
            c * m + r >= lim * m,
            0 <= r < m,
    ;
    assert(ebits(e, n0, (l + 1) as nat) == 2 * c + ebit(e, n0 + l));
    lemma_ebit_01(e, n0 + l);
    assert(hdec(t, e, n0, l, c) == hdec(t, e, n0, l + 1, 2 * c + ebit(e, n0 + l)));
}

/// A window below the limit of length `l` starts with a code of that
/// length, if it holds none shorter.
pub proof fn lemma_dec_done(t: HuffTable, e: Seq<u8>, n0: int, l: int)
    requires
        1 <= l <= 16,
        ebits(e, n0, 16) < (hfirst(t, l) + hcount(t, l)) * pow2((16 - l) as nat),
    ensures
        ({
            let c = ebits(e, n0, 16) / (pow2((16 - l) as nat) as int);
            &&& c == ebits(e, n0, l as nat)
            &&& c < hfirst(t, l) + hcount(t, l)
            &&& hdec(t, e, n0, l, c) == (t.vals[hbase(t, l) + c - hfirst(t, l)] as int, n0 + l)
        }),
{
    let c = ebits(e, n0, l as nat);
    let m = pow2((16 - l) as nat) as int;
    let r = ebits(e, n0 + l, (16 - l) as nat);
    let lim = hfirst(t, l) + hcount(t, l);
    lemma_window(e, n0, l);
    assert(c < lim) by (nonlinear_arith)
        requires
            c * m + r < lim * m,
            0 <= r < m,
    ;
    lemma_fundamental_div_mod_converse(ebits(e, n0, 16), m, c, r);
}

/// A `look` entry that is not 0 is the next symbol and its length.
proof fn lemma_look_hit(t: HuffTable, d: Derived, e: Seq<u8>, n0: int, en: int)
    requires
        d.wf(t),
        en == d.look[ebits(e, n0, 16) / 64],
        en != 0,
    ensures
        1 <= en / 256 <= 10,
        0 <= ebits(e, n0, 16) / 64 < 1024,
        huff(t, e, n0) == (en % 256, n0 + en / 256),
{
    let v = ebits(e, n0, 16);
    let p = v / 64;
    let l = en / 256;
    lemma_ebits_bound(e, n0, 16);
    lemma2_to64();
    assert(look_ok(d.look[p] as int, p, d.ll@, d.off@, t.vals));
    assert forall|j: int| 1 <= j < l implies v >= (hfirst(t, j) + #[trigger] hcount(t, j)) * pow2((16 - j) as nat) by {
        assert(d.lim[j] == hfirst(t, j) + hcount(t, j));
        assert(d.ll@[j] <= p * 64);
    }
    lemma_dec_skip(t, e, n0, l);
    assert(d.lim[l] == hfirst(t, l) + hcount(t, l) && d.off[l] == hbase(t, l) - hfirst(t, l));
    lemma_dec_done(t, e, n0, l);
    lemma_look_code(v, l);
}

/// The next symbol.
#[inline(never)]
pub fn decode(br: &mut BitReader, data: &[u8], d: &Derived, t: &HuffTab) -> (r: u8)
    requires
        old(br).wf(data@),
        d.wf(t@),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        r as int == huff(t@, old(br).e(data@), old(br).n@).0,
        final(br).n@ == huff(t@, old(br).e(data@), old(br).n@).1,
        old(br).over() ==> final(br).over(),
{
    hide(hdec);
    hide(huff);
    hide(BitReader::wf);
    let ghost e = br.e(data@);
    let ghost n0 = br.n@;
    // The next 16 bits: the code is the shortest prefix of them below its
    // length's limit.
    let v = br.peek16(data);
    proof {
        lemma_ebits_bound(e, n0, 16);
        lemma2_to64();
        lemma_u32_shr_is_div(v, 6);
    }
    // Most codes are 10 bits or fewer, and the table has those.
    let en = d.look[(v >> 6) as usize];
    if en != 0 {
        let l = (en >> 8) as u32;
        proof {
            assert(en >> 8 == en / 256 && en & 255 == en % 256) by (bit_vector);
            lemma_look_hit(t@, *d, e, n0, en as int);
        }
        let _ = br.get(data, l);
        return (en & 255) as u8;
    }
    proof {
        lemma_dec_start(t@, e, n0);
    }
    let mut l: usize = 1;
    while l <= 16 && v >= d.ll[l]
        invariant
            1 <= l <= 17,
            d.wf(t@),
            v as int == ebits(e, n0, 16),
            l <= 16 ==> hdec(t@, e, n0, l as int, ebits(e, n0, l as nat)) == huff(t@, e, n0),
            l <= 16 ==> hfirst(t@, l as int) <= ebits(e, n0, l as nat),
            l == 17 ==> huff(t@, e, n0) == (0int, n0 + 17),
        decreases 17 - l,
    {
        proof {
            assert(d.lim[l as int] == hfirst(t@, l as int) + hcount(t@, l as int) && d.ll[l as int] == d.lim[l as int] * pow2(
                (16 - l) as nat,
            ));
            lemma_dec_more(t@, e, n0, l as int);
        }
        l += 1;
    }
    if l > 16 {
        // No code of 16 bits or fewer: libjpeg takes 17 bits and gives 0.
        assert(huff(t@, e, n0) == (0int, n0 + 17));
        let _ = br.get(data, 16);
        assert(br.n@ == n0 + 16);
        let _ = br.get(data, 1);
        assert(br.n@ == n0 + 17);
        return 0;
    }
    let code = (v >> (16 - l as u32)) as i32;
    proof {
        assert(d.lim[l as int] == hfirst(t@, l as int) + hcount(t@, l as int) && d.ll[l as int] == d.lim[l as int] * pow2(
            (16 - l) as nat,
        ) && d.off[l as int] == hbase(t@, l as int) - hfirst(t@, l as int));
        lemma_dec_done(t@, e, n0, l as int);
        lemma_u32_shr_is_div(v, (16 - l) as u32);
        lemma_hbase_mono(t@, l + 1, 17);
        lemma_hbase_mono(t@, l as int, l as int);
    }
    let _ = br.get(data, l as u32);
    t.vals[(code + d.off[l]) as usize]
}

/// The last `s` of `l + s` bits are the `s` bits after the first `l`.
proof fn lemma_tail(e: Seq<u8>, n0: int, l: nat, s: nat)
    ensures
        ebits(e, n0, l + s) % (pow2(s) as int) == ebits(e, n0 + l, s),
        0 <= ebits(e, n0 + l, s) < pow2(s),
{
    lemma_ebits_split(e, n0, l, s);
    lemma_ebits_bound(e, n0 + l, s);
    lemma_ebits_bound(e, n0, l);
    lemma_pow2_pos(s);
    lemma_fundamental_div_mod_converse(ebits(e, n0, l + s), pow2(s) as int, ebits(e, n0, l), ebits(e, n0 + l, s));
}

/// The next AC symbol and, when its size is not 0, the value that follows
/// it. A short code and its value are taken from the input in one step.
#[inline(always)]
pub fn decode_ac(br: &mut BitReader, data: &[u8], d: &Derived, t: &HuffTab) -> (r: (u8, i32))
    requires
        old(br).wf(data@),
        d.wf(t@),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        old(br).over() ==> final(br).over(),
        r.0 as int == huff(t@, old(br).e(data@), old(br).n@).0,
        ({
            let n1 = huff(t@, old(br).e(data@), old(br).n@).1;
            let s = r.0 as int % 16;
            if s != 0 {
                &&& r.1 == extend(ebits(old(br).e(data@), n1, s as nat), s)
                &&& final(br).n@ == n1 + s
                &&& -0x8000 < r.1 < 0x8000
            } else {
                final(br).n@ == n1
            }
        }),
{
    hide(hdec);
    hide(huff);
    hide(BitReader::wf);
    let ghost e = br.e(data@);
    let ghost n0 = br.n@;
    let v = br.peek16w(data);
    proof {
        lemma_ebits_bound(e, n0, 16);
        lemma2_to64();
        lemma_u32_shr_is_div(v, 6);
    }
    let en = d.look[(v >> 6) as usize];
    let l = (en >> 8) as u32;
    let s = (en & 15) as u32;
    assert(en >> 8 == en / 256 && en & 255 == en % 256 && en & 15 == (en % 256) % 16 && (en & 15) <= 15) by (bit_vector);
    if en != 0 {
        proof {
            lemma_look_hit(t@, *d, e, n0, en as int);
        }
        // One read for the code and the value after it, whether or not
        // there is a value: the 32 bits `peek16w` left are enough.
        let b = br.get2_have(Ghost(data), l, s);
        if s == 0 {
            return ((en & 255) as u8, 0);
        }
        proof {
            lemma_ebits_bound(e, n0 + l, s as nat);
            lemma_pow2_le(s as nat, 15);
            lemma2_to64();
        }
        let x = extend_x(b as i32, s);
        return ((en & 255) as u8, x);
    }
    let mut tb = *br;
    let sym = decode(&mut tb, data, d, t);
    *br = tb;
    let s2 = (sym & 15) as u32;
    assert(sym & 15 == sym % 16) by (bit_vector);
    if s2 != 0 {
        proof {
            lemma_ebits_bound(br.e(data@), br.n@, s2 as nat);
            lemma_pow2_le(s2 as nat, 15);
            lemma2_to64();
        }
        let x = extend_x(br.get_r(data, s2) as i32, s2);
        (sym, x)
    } else {
        (sym, 0)
    }
}

/// The next symbol, for a reader that its caller keeps in registers: a
/// short code comes from the lookup table, a long one from `decode` on a
/// copy.
#[inline(always)]
pub fn decode_sym(br: &mut BitReader, data: &[u8], d: &Derived, t: &HuffTab) -> (r: u8)
    requires
        old(br).wf(data@),
        d.wf(t@),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        r as int == huff(t@, old(br).e(data@), old(br).n@).0,
        final(br).n@ == huff(t@, old(br).e(data@), old(br).n@).1,
        old(br).over() ==> final(br).over(),
{
    hide(hdec);
    hide(huff);
    hide(BitReader::wf);
    let ghost e = br.e(data@);
    let ghost n0 = br.n@;
    let v = br.peek16w(data);
    proof {
        lemma_ebits_bound(e, n0, 16);
        lemma2_to64();
        lemma_u32_shr_is_div(v, 6);
    }
    let en = d.look[(v >> 6) as usize];
    let l = (en >> 8) as u32;
    assert(en >> 8 == en / 256 && en & 255 == en % 256) by (bit_vector);
    if en != 0 {
        proof {
            lemma_look_hit(t@, *d, e, n0, en as int);
        }
        let _ = br.get_have(Ghost(data), l);
        return (en & 255) as u8;
    }
    let mut tb = *br;
    let sym = decode(&mut tb, data, d, t);
    *br = tb;
    sym
}

/// `pow2` is monotonic.
proof fn lemma_pow2_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
{
    if a < b {
        lemma_pow2_strictly_increases(a, b);
    }
}

/// A value of `s` bits, read and extended.
#[inline(always)]
pub fn receive_extend(br: &mut BitReader, data: &[u8], s: u32) -> (v: i32)
    requires
        old(br).wf(data@),
        1 <= s <= 15,
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        final(br).n@ == old(br).n@ + s,
        v == extend(ebits(old(br).e(data@), old(br).n@, s as nat), s as int),
        -0x8000 < v < 0x8000,
        old(br).over() ==> final(br).over(),
{
    proof {
        lemma_ebits_bound(br.e(data@), br.n@, s as nat);
        lemma_pow2_le(s as nat, 15);
        lemma2_to64();
    }
    let b = br.get(data, s);
    extend_x(b as i32, s)
}

/// EXTEND: the signed value of the `s`-bit field `v`, `1 <= s <= 16`.
#[inline(always)]
pub fn extend_x(v: i32, s: u32) -> (r: i32)
    requires
        1 <= s <= 16,
        0 <= v < pow2(s as nat),
    ensures
        r == extend(v as int, s as int),
        -pow2(s as nat) < r < pow2(s as nat),
{
    proof {
        lemma_pow2_unfold(s as nat);
        lemma2_to64();
        if s < 16 {
            lemma_pow2_strictly_increases(s as nat, 16);
        }
    }
    let half = (1u32 << (s - 1)) as i32;
    let full = (1u32 << s) as i32;
    proof {
        lemma_u32_shl_is_mul(1, (s - 1) as u32);
        lemma_u32_shl_is_mul(1, s);
        lemma_pow2_strictly_increases((s - 1) as nat, 31);
        lemma_pow2_strictly_increases(s as nat, 31);
        assert(half == pow2((s - 1) as nat) && full == pow2(s as nat));
    }
    if v < half {
        v - full + 1
    } else {
        v
    }
}

/// A DC difference.
pub fn dc_diff_x(br: &mut BitReader, data: &[u8], d: &Derived, t: &HuffTab) -> (r: i32)
    requires
        old(br).wf(data@),
        d.wf(t@),
        huff_dc_ok(t@),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        r as int == dc_diff(t@, old(br).e(data@), old(br).n@).0,
        final(br).n@ == dc_diff(t@, old(br).e(data@), old(br).n@).1,
        old(br).over() ==> final(br).over(),
        -0x8000 < r < 0x8000,
{
    proof {
        lemma_huff_dc(t@, br.e(data@), br.n@);
    }
    let s = decode(br, data, d, t) as u32;
    if s == 0 {
        0
    } else {
        proof {
            lemma_ebits_bound(br.e(data@), br.n@, s as nat);
            lemma2_to64();
            if s < 15 {
                lemma_pow2_strictly_increases(s as nat, 15);
            }
        }
        extend_x(br.get(data, s) as i32, s)
    }
}

/// `dc_diff_x` for a reader that its caller keeps in registers: the
/// difference is read as an AC symbol and its value are, a size below 16
/// and then that many bits.
#[inline(always)]
pub fn dc_diff_r(br: &mut BitReader, data: &[u8], d: &Derived, t: &HuffTab) -> (r: i32)
    requires
        old(br).wf(data@),
        d.wf(t@),
        huff_dc_ok(t@),
    ensures
        final(br).wf(data@),
        final(br).p0 == old(br).p0,
        r as int == dc_diff(t@, old(br).e(data@), old(br).n@).0,
        final(br).n@ == dc_diff(t@, old(br).e(data@), old(br).n@).1,
        old(br).over() ==> final(br).over(),
        -0x8000 < r < 0x8000,
{
    proof {
        lemma_huff_dc(t@, br.e(data@), br.n@);
    }
    let (sym, v) = decode_ac(br, data, d, t);
    if sym == 0 {
        0
    } else {
        v
    }
}

} // verus!


