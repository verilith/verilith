//! The encoder's one scan: a baseline, interleaved scan of the three
//! components, luma sampled 1 or 2 times as finely as chroma each way.
//! Proven: the bits of the scan, written MCU by MCU, block by block, decode
//! under the specification's `scan` to exactly the coefficients coded.
use crate::enc_bits::*;
use crate::enc_huff::*;
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The frame and the scan
// ---------------------------------------------------------------------------
/// The frames this encoder writes: sequential, three components with
/// identifiers 1, 2 and 3, luma sampled `h` by `v` (each 1 or 2), chroma 1
/// by 1; luma uses quantization table 0, chroma table 1.
pub open spec fn enc_frame(f: Frame) -> bool {
    &&& !f.prog
    &&& f.nc == 3
    &&& 1 <= f.w <= 65500
    &&& 1 <= f.h <= 65500
    &&& f.comps.len() == 3
    &&& f.comps[0].h == 1 || f.comps[0].h == 2
    &&& f.comps[0].v == 1 || f.comps[0].v == 2
    &&& f.comps[1].h == 1 && f.comps[1].v == 1
    &&& f.comps[2].h == 1 && f.comps[2].v == 1
}

/// The one scan: all three components, luma with DC and AC tables 0,
/// chroma with tables 1.
pub open spec fn enc_scan_hdr() -> Scan {
    Scan {
        ns: 3,
        ci: seq![0int, 1int, 2int],
        td: seq![0int, 1int, 1int],
        ta: seq![0int, 1int, 1int],
        ss: 0,
        se: 63,
        ah: 0,
        al: 0,
    }
}

/// The encoding tables, by table number (0 luma, 1 chroma).
pub ghost struct Codes {
    pub dco: Seq<Seq<u16>>,
    pub dsi: Seq<Seq<u8>>,
    pub aco: Seq<Seq<u16>>,
    pub asi: Seq<Seq<u8>>,
}

/// The tables a decoder holds agree with the codes.
pub open spec fn codes_ready(t: Tables, k: Codes) -> bool {
    &&& k.dco.len() == 2 && k.dsi.len() == 2 && k.aco.len() == 2 && k.asi.len() == 2
    &&& t.dc.len() == 4 && t.ac.len() == 4
    &&& forall|i: int| 0 <= i < 2 ==> dc_ready(t.dc[i], #[trigger] k.dco[i], k.dsi[i])
    &&& forall|i: int| 0 <= i < 2 ==> ac_ready(t.ac[i], #[trigger] k.aco[i], k.asi[i])
}

/// Block `idx` of component `c`.
pub open spec fn blk(a: Seq<Seq<i16>>, c: int, idx: int) -> Seq<i16> {
    a[c].subrange(64 * idx, 64 * idx + 64)
}

/// Coefficients this encoder can code: DC from -1024 to 1023, AC from
/// -1023 to 1023, in arrays of the frame's sizes.
pub open spec fn coefs_ok(f: Frame, a: Seq<Seq<i16>>) -> bool {
    &&& a.len() == 3
    &&& forall|c: int| 0 <= c < 3 ==> (#[trigger] a[c]).len() == 64 * cw(f, c) * ch(f, c)
    &&& forall|c: int, j: int|
        0 <= c < 3 && 0 <= j < a[c].len() ==> -1024 <= #[trigger] a[c][j] <= 1023 && (j % 64 != 0 ==> a[c][j]
            != -1024)
}

/// The bits of MCU `m` from its block `b`, with the DC predictions
/// `preds`; and the predictions after it.
pub open spec fn enc_mcu(f: Frame, k: Codes, a: Seq<Seq<i16>>, m: int, b: int, preds: Seq<int>) -> (
    Seq<bool>,
    Seq<int>,
)
    decreases mcu_blocks(f, enc_scan_hdr()) - b,
{
    let s = enc_scan_hdr();
    if b >= mcu_blocks(f, s) || b < 0 {
        (Seq::empty(), preds)
    } else {
        let (i, idx) = blk_index(f, s, m, b);
        let ti = s.td[i];
        let bl = blk(a, i, idx);
        let bits = block_bits(k.dco[ti], k.dsi[ti], k.aco[ti], k.asi[ti], bl, preds[i]);
        let r = enc_mcu(f, k, a, m, b + 1, preds.update(i, bl[0] as int));
        (bits + r.0, r.1)
    }
}

/// The bits of the first `m` MCUs, and the predictions after them.
pub open spec fn enc_upto(f: Frame, k: Codes, a: Seq<Seq<i16>>, m: int) -> (Seq<bool>, Seq<int>)
    decreases m,
{
    if m <= 0 {
        (Seq::empty(), seq![0int, 0int, 0int])
    } else {
        let p = enc_upto(f, k, a, m - 1);
        let q = enc_mcu(f, k, a, m - 1, 0, p.1);
        (p.0 + q.0, q.1)
    }
}

/// The MCUs of the scan.
pub open spec fn n_mcus(f: Frame) -> int {
    mcux(f) * mcuy(f)
}

// ---------------------------------------------------------------------------
// Block geometry
// ---------------------------------------------------------------------------
/// The MCU block `idx` of component `c` is in.
pub open spec fn mcu_of(f: Frame, c: int, idx: int) -> int {
    let w = cw(f, c);
    ((idx / w) / f.comps[c].v as int) * mcux(f) + (idx % w) / f.comps[c].h as int
}

/// Its place among the MCU's blocks.
pub open spec fn slot_of(f: Frame, c: int, idx: int) -> int {
    let w = cw(f, c);
    let h = f.comps[0].h as int;
    let v = f.comps[0].v as int;
    if c == 0 {
        ((idx / w) % v) * h + (idx % w) % h
    } else {
        h * v + c - 1
    }
}

/// The component of the MCU's block `b`.
pub open spec fn comp_of(f: Frame, b: int) -> int {
    let n0 = f.comps[0].h as int * f.comps[0].v as int;
    if b < n0 {
        0
    } else {
        b - n0 + 1
    }
}

pub proof fn lemma_geom(f: Frame)
    requires
        enc_frame(f),
    ensures
        maxh(f) == f.comps[0].h,
        maxv(f) == f.comps[0].v,
        mcux(f) >= 1,
        mcuy(f) >= 1,
        cw(f, 0) == mcux(f) * f.comps[0].h,
        ch(f, 0) == mcuy(f) * f.comps[0].v,
        cw(f, 1) == mcux(f) && cw(f, 2) == mcux(f),
        ch(f, 1) == mcuy(f) && ch(f, 2) == mcuy(f),
        mcu_blocks(f, enc_scan_hdr()) == f.comps[0].h * f.comps[0].v + 2,
        scan_mcus(f, enc_scan_hdr()) == n_mcus(f),
        n_mcus(f) >= 1,
{
    let s = enc_scan_hdr();
    reveal_with_fuel(blocks_upto, 4);
    assert(mcux(f) >= 1) by {
        let d = 8 * maxh(f);
        assert(d >= 8);
        lemma_div_pos_is_pos(f.w as int + d - 1, d);
        assert(f.w as int + d - 1 >= d);
        lemma_div_is_ordered(d, f.w as int + d - 1, d);
        lemma_div_basics(d);
    }
    assert(mcuy(f) >= 1) by {
        let d = 8 * maxv(f);
        lemma_div_is_ordered(d, f.h as int + d - 1, d);
        lemma_div_basics(d);
    }
    assert(n_mcus(f) >= 1) by (nonlinear_arith)
        requires
            mcux(f) >= 1,
            mcuy(f) >= 1,
    ;
    assert(cw(f, 1) == mcux(f) * 1);
    assert(ch(f, 1) == mcuy(f) * 1);
    assert(cw(f, 2) == mcux(f) * 1);
    assert(ch(f, 2) == mcuy(f) * 1);
}

/// The blocks of an MCU, component by component.
pub proof fn lemma_slot(f: Frame, b: int)
    requires
        enc_frame(f),
        0 <= b < f.comps[0].h * f.comps[0].v + 2,
    ensures
        blk_slot(f, enc_scan_hdr(), b, 0) == (comp_of(f, b), if comp_of(f, b) == 0 {
            b
        } else {
            0
        }),
        0 <= comp_of(f, b) < 3,
{
    reveal_with_fuel(blk_slot, 3);
}

/// Block `b` of MCU `m`: its component, and where it is.
#[verifier::rlimit(40)]
pub proof fn lemma_fwd(f: Frame, m: int, b: int)
    requires
        enc_frame(f),
        0 <= m < n_mcus(f),
        0 <= b < f.comps[0].h * f.comps[0].v + 2,
    ensures
        ({
            let (i, idx) = blk_index(f, enc_scan_hdr(), m, b);
            let c = comp_of(f, b);
            &&& i == c
            &&& 0 <= idx < cw(f, c) * ch(f, c)
            &&& mcu_of(f, c, idx) == m
            &&& slot_of(f, c, idx) == b
        }),
{
    let s = enc_scan_hdr();
    lemma_geom(f);
    lemma_slot(f, b);
    let c = comp_of(f, b);
    let off = if c == 0 {
        b
    } else {
        0
    };
    let h = f.comps[c].h as int;
    let v = f.comps[c].v as int;
    let mx = mcux(f);
    let my = mcuy(f);
    let w = cw(f, c);
    lemma_fundamental_div_mod(m, mx);
    lemma_mod_bound(m, mx);
    lemma_div_pos_is_pos(m, mx);
    let qm = m / mx;
    let rm = m % mx;
    assert(qm < my) by {
        assert(n_mcus(f) == mx * my);
        lemma_multiply_divide_lt(m, mx, my);
    }
    assert(0 <= off < h * v);
    lemma_fundamental_div_mod(off, h);
    lemma_mod_bound(off, h);
    let oy = off / h;
    let ox = off % h;
    assert(0 <= oy < v) by {
        lemma_div_pos_is_pos(off, h);
        lemma_multiply_divide_lt(off, h, v);
    }
    let x = rm * h + ox;
    let y = qm * v + oy;
    assert(w == mx * h);
    assert(h >= 1 && v >= 1);
    assert(0 <= x < w) by (nonlinear_arith)
        requires
            0 <= rm < mx,
            0 <= ox < h,
            w == mx * h,
            h >= 1,
            x == rm * h + ox,
    ;
    assert(0 <= y < my * v) by (nonlinear_arith)
        requires
            0 <= qm < my,
            0 <= oy < v,
            v >= 1,
            y == qm * v + oy,
    ;
    assert(ch(f, c) == my * v);
    let idx = y * w + x;
    assert(blk_index(f, s, m, b) == (c, idx));
    assert(0 <= idx < w * ch(f, c)) by (nonlinear_arith)
        requires
            0 <= x < w,
            0 <= y < ch(f, c),
            idx == y * w + x,
    ;
    assert(idx / w == y && idx % w == x) by {
        lemma_fundamental_div_mod_converse(idx, w, y, x);
    }
    assert(y / v == qm && y % v == oy) by {
        lemma_fundamental_div_mod_converse(y, v, qm, oy);
    }
    assert(x / h == rm && x % h == ox) by {
        lemma_fundamental_div_mod_converse(x, h, rm, ox);
    }
    assert(mcu_of(f, c, idx) == qm * mx + rm);
    assert(qm * mx + rm == m) by {
        lemma_mul_is_commutative(qm, mx);
    }
    if c == 0 {
        assert(slot_of(f, c, idx) == oy * h + ox);
        assert(oy * h + ox == off) by {
            lemma_mul_is_commutative(oy, h);
        }
    }
}

/// Every block is block `slot_of` of MCU `mcu_of`.
#[verifier::rlimit(40)]
pub proof fn lemma_inv(f: Frame, c: int, idx: int)
    requires
        enc_frame(f),
        0 <= c < 3,
        0 <= idx < cw(f, c) * ch(f, c),
    ensures
        0 <= mcu_of(f, c, idx) < n_mcus(f),
        0 <= slot_of(f, c, idx) < f.comps[0].h * f.comps[0].v + 2,
        comp_of(f, slot_of(f, c, idx)) == c,
        blk_index(f, enc_scan_hdr(), mcu_of(f, c, idx), slot_of(f, c, idx)) == (c, idx),
{
    let s = enc_scan_hdr();
    lemma_geom(f);
    let h = f.comps[c].h as int;
    let v = f.comps[c].v as int;
    let h0 = f.comps[0].h as int;
    let v0 = f.comps[0].v as int;
    let mx = mcux(f);
    let my = mcuy(f);
    let w = cw(f, c);
    assert(w == mx * h);
    assert(ch(f, c) == my * v);
    assert(h >= 1 && v >= 1);
    assert(w >= 1) by (nonlinear_arith)
        requires
            w == mx * h,
            mx >= 1,
            h >= 1,
    ;
    lemma_fundamental_div_mod(idx, w);
    lemma_mod_bound(idx, w);
    lemma_div_pos_is_pos(idx, w);
    let y = idx / w;
    let x = idx % w;
    assert(y < my * v) by {
        lemma_multiply_divide_lt(idx, w, ch(f, c));
    }
    lemma_fundamental_div_mod(y, v);
    lemma_mod_bound(y, v);
    lemma_div_pos_is_pos(y, v);
    lemma_fundamental_div_mod(x, h);
    lemma_mod_bound(x, h);
    lemma_div_pos_is_pos(x, h);
    let qy = y / v;
    let ry = y % v;
    let qx = x / h;
    let rx = x % h;
    assert(qy < my) by {
        lemma_mul_is_commutative(my, v);
        lemma_multiply_divide_lt(y, v, my);
    }
    assert(qx < mx) by {
        lemma_mul_is_commutative(mx, h);
        lemma_multiply_divide_lt(x, h, mx);
    }
    let m = qy * mx + qx;
    assert(0 <= m < n_mcus(f)) by (nonlinear_arith)
        requires
            0 <= qy < my,
            0 <= qx < mx,
            m == qy * mx + qx,
            n_mcus(f) == mx * my,
    ;
    assert(mcu_of(f, c, idx) == m);
    assert(m / mx == qy && m % mx == qx) by {
        lemma_mul_is_commutative(qy, mx);
        lemma_fundamental_div_mod_converse(m, mx, qy, qx);
    }
    let b = slot_of(f, c, idx);
    if c == 0 {
        assert(b == ry * h + rx);
        assert(0 <= b < h * v) by (nonlinear_arith)
            requires
                0 <= ry < v,
                0 <= rx < h,
                b == ry * h + rx,
        ;
        assert(b / h == ry && b % h == rx) by {
            lemma_mul_is_commutative(ry, h);
            lemma_fundamental_div_mod_converse(b, h, ry, rx);
        }
    } else {
        assert(h == 1 && v == 1);
        assert(rx == 0 && ry == 0);
        assert(0 <= h0 * v0 <= 4) by (nonlinear_arith)
            requires
                1 <= h0 <= 2,
                1 <= v0 <= 2,
        ;
    }
    lemma_slot(f, b);
    let off = if c == 0 {
        b
    } else {
        0
    };
    assert(off / h == ry && off % h == rx);
    assert(qx * h + rx == x) by {
        lemma_mul_is_commutative(qx, h);
    }
    assert(qy * v + ry == y) by {
        lemma_mul_is_commutative(qy, v);
    }
    assert(y * w + x == idx) by {
        lemma_mul_is_commutative(y, w);
    }
}

// ---------------------------------------------------------------------------
// Decoding the scan
// ---------------------------------------------------------------------------
/// Block `idx` of component `c` comes before block `b` of MCU `m`.
pub open spec fn before(f: Frame, c: int, idx: int, m: int, b: int) -> bool {
    mcu_of(f, c, idx) < m || (mcu_of(f, c, idx) == m && slot_of(f, c, idx) < b)
}

/// The coefficients once the blocks before block `b` of MCU `m` are
/// decoded: the others are still zero.
pub open spec fn part(f: Frame, a: Seq<Seq<i16>>, m: int, b: int) -> Seq<Seq<i16>> {
    Seq::new(
        3,
        |c: int| Seq::new(a[c].len(), |j: int| if before(f, c, j / 64, m, b) { a[c][j] } else { 0i16 }),
    )
}

/// The state of the decoder at block `b` of MCU `m`.
pub open spec fn sst(f: Frame, a: Seq<Seq<i16>>, m: int, b: int, preds: Seq<int>, n: int, p0: int, togo: int) -> SS {
    SS { a: part(f, a, m, b), pred: preds, eob: 0, p: p0, n, insuf: false, togo, rst: 0, ok: true }
}

/// What the decoder needs to know about the bits and tables.
pub open spec fn scan_pre(d: Seq<u8>, f: Frame, t: Tables, k: Codes, a: Seq<Seq<i16>>, p0: int) -> bool {
    let e = ecs(d, p0);
    let all = enc_upto(f, k, a, n_mcus(f)).0;
    &&& enc_frame(f)
    &&& codes_ready(t, k)
    &&& coefs_ok(f, a)
    &&& t.ri == 0
    &&& bits_at(e, 0, all)
    &&& all.len() <= 8 * e.len()
}

pub proof fn lemma_preds_ok(f: Frame, k: Codes, a: Seq<Seq<i16>>, m: int)
    requires
        enc_frame(f),
        coefs_ok(f, a),
        0 <= m <= n_mcus(f),
    ensures
        enc_upto(f, k, a, m).1.len() == 3,
        forall|i: int| 0 <= i < 3 ==> -1024 <= #[trigger] enc_upto(f, k, a, m).1[i] <= 1023,
    decreases m,
{
    if m > 0 {
        lemma_preds_ok(f, k, a, m - 1);
        lemma_mcu_preds(f, k, a, m - 1, 0, enc_upto(f, k, a, m - 1).1);
    }
}

pub proof fn lemma_mcu_preds(f: Frame, k: Codes, a: Seq<Seq<i16>>, m: int, b: int, preds: Seq<int>)
    requires
        enc_frame(f),
        coefs_ok(f, a),
        0 <= m < n_mcus(f),
        0 <= b,
        preds.len() == 3,
        forall|i: int| 0 <= i < 3 ==> -1024 <= #[trigger] preds[i] <= 1023,
    ensures
        enc_mcu(f, k, a, m, b, preds).1.len() == 3,
        forall|i: int| 0 <= i < 3 ==> -1024 <= #[trigger] enc_mcu(f, k, a, m, b, preds).1[i] <= 1023,
    decreases mcu_blocks(f, enc_scan_hdr()) - b,
{
    lemma_geom(f);
    if b < mcu_blocks(f, enc_scan_hdr()) {
        lemma_fwd(f, m, b);
        let (i, idx) = blk_index(f, enc_scan_hdr(), m, b);
        let bl = blk(a, i, idx);
        assert(64 * idx + 64 <= a[i].len()) by (nonlinear_arith)
            requires
                0 <= idx < cw(f, i) * ch(f, i),
                a[i].len() == 64 * cw(f, i) * ch(f, i),
        ;
        assert(bl[0] == a[i][64 * idx]);
        lemma_mcu_preds(f, k, a, m, b + 1, preds.update(i, bl[0] as int));
    }
}

/// The bits of the first `m + 1` MCUs start with those of the first `m`,
/// then MCU `m`'s.
pub proof fn lemma_upto_prefix(f: Frame, k: Codes, a: Seq<Seq<i16>>, m: int, mm: int)
    requires
        0 <= m < mm,
    ensures
        ({
            let p = enc_upto(f, k, a, m);
            let q = enc_mcu(f, k, a, m, 0, p.1);
            enc_upto(f, k, a, mm).0.subrange(0, (p.0.len() + q.0.len()) as int) == p.0 + q.0
        }),
        enc_upto(f, k, a, m + 1).0.len() <= enc_upto(f, k, a, mm).0.len(),
    decreases mm - m,
{
    let p = enc_upto(f, k, a, m);
    let q = enc_mcu(f, k, a, m, 0, p.1);
    if mm == m + 1 {
        assert(enc_upto(f, k, a, mm).0 =~= p.0 + q.0);
        assert((p.0 + q.0).subrange(0, (p.0.len() + q.0.len()) as int) =~= p.0 + q.0);
    } else {
        lemma_upto_prefix(f, k, a, m, mm - 1);
        let r = enc_upto(f, k, a, mm - 1);
        let z = enc_mcu(f, k, a, mm - 1, 0, r.1);
        assert(enc_upto(f, k, a, mm).0 == r.0 + z.0);
        assert((r.0 + z.0).subrange(0, (p.0.len() + q.0.len()) as int) =~= r.0.subrange(0, (p.0.len() + q.0.len()) as int));
    }
}

proof fn lemma_bits_at_sub(e: Seq<u8>, all: Seq<bool>, x: Seq<bool>, y: Seq<bool>, n: int)
    requires
        bits_at(e, 0, all),
        n == x.len(),
        x.len() + y.len() <= all.len(),
        all.subrange(0, (x.len() + y.len()) as int) == x + y,
    ensures
        bits_at(e, n, y),
{
    assert forall|i: int| 0 <= i < y.len() implies ebit(e, n + i) == b2i(#[trigger] y[i]) as int by {
        assert(all[n + i] == (x + y)[n + i]);
        assert(ebit(e, 0 + (n + i)) == b2i(all[n + i]) as int);
    }
}

/// One block of an MCU.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_mcu_block(
    d: Seq<u8>,
    f: Frame,
    t: Tables,
    k: Codes,
    a: Seq<Seq<i16>>,
    p0: int,
    m: int,
    b: int,
    preds: Seq<int>,
    n: int,
    togo: int,
)
    requires
        scan_pre(d, f, t, k, a, p0),
        0 <= m < n_mcus(f),
        0 <= b < mcu_blocks(f, enc_scan_hdr()),
        preds.len() == 3,
        forall|i: int| 0 <= i < 3 ==> -1024 <= #[trigger] preds[i] <= 1023,
        bits_at(ecs(d, p0), n, enc_mcu(f, k, a, m, b, preds).0),
    ensures
        ({
            let s = enc_scan_hdr();
            let (i, idx) = blk_index(f, s, m, b);
            let bl = blk(a, i, idx);
            let bits = block_bits(k.dco[s.td[i]], k.dsi[s.td[i]], k.aco[s.td[i]], k.asi[s.td[i]], bl, preds[i]);
            &&& mcu_dc_block(d, f, t, s, sst(f, a, m, b, preds, n, p0, togo), m, b) == sst(
                f,
                a,
                m,
                b + 1,
                preds.update(i, bl[0] as int),
                n + bits.len(),
                p0,
                togo,
            )
            &&& enc_mcu(f, k, a, m, b, preds) == (bits + enc_mcu(f, k, a, m, b + 1, preds.update(i, bl[0] as int)).0,
                enc_mcu(f, k, a, m, b + 1, preds.update(i, bl[0] as int)).1)
            &&& bits_at(ecs(d, p0), n + bits.len(), enc_mcu(f, k, a, m, b + 1, preds.update(i, bl[0] as int)).0)
            &&& 0 <= i < 3
            &&& -1024 <= bl[0] <= 1023
        }),
{
    let s = enc_scan_hdr();
    let e = ecs(d, p0);
    lemma_geom(f);
    lemma_fwd(f, m, b);
    let (i, idx) = blk_index(f, s, m, b);
    let c = i;
    let ti = s.td[i];
    assert(ti == s.ta[i]);
    assert(0 <= ti < 2);
    let bl = blk(a, c, idx);
    let o = 64 * idx;
    let len = a[c].len() as int;
    assert(o + 64 <= len) by (nonlinear_arith)
        requires
            0 <= idx < cw(f, c) * ch(f, c),
            len == 64 * cw(f, c) * ch(f, c),
            o == 64 * idx,
    ;
    assert(bl.len() == 64);
    assert(block_ok(bl)) by {
        assert forall|j: int| 1 <= j < 64 implies -1024 < #[trigger] bl[j] < 1024 by {
            assert(bl[j] == a[c][o + j]);
            assert((o + j) % 64 == j) by {
                lemma_fundamental_div_mod_converse(o + j, 64, idx, j);
            }
        }
    }
    assert(bl[0] == a[c][o]);
    let bits = block_bits(k.dco[ti], k.dsi[ti], k.aco[ti], k.asi[ti], bl, preds[i]);
    let st = sst(f, a, m, b, preds, n, p0, togo);
    let rest = enc_mcu(f, k, a, m, b + 1, preds.update(i, bl[0] as int));
    assert(enc_mcu(f, k, a, m, b, preds) == (bits + rest.0, rest.1));
    lemma_bits_at_cat(e, n, bits, rest.0);
    let cur = part(f, a, m, b)[c];
    assert forall|j: int| 0 <= j < 64 implies #[trigger] cur[o + j] == 0 by {
        assert((o + j) / 64 == idx) by {
            lemma_fundamental_div_mod_converse(o + j, 64, idx, j);
        }
    }
    assert(dc_ready(t.dc[ti], k.dco[ti], k.dsi[ti]));
    assert(ac_ready(t.ac[ti], k.aco[ti], k.asi[ti]));
    lemma_block(t.dc[ti], k.dco[ti], k.dsi[ti], t.ac[ti], k.aco[ti], k.asi[ti], e, n, bl, preds[i], cur, o);
    let a2 = put_block(cur, o, bl);
    let nxt = part(f, a, m, b + 1);
    assert(a2 =~= nxt[c]) by {
        assert forall|j: int| 0 <= j < len implies #[trigger] a2[j] == nxt[c][j] by {
            let q = j / 64;
            lemma_fundamental_div_mod(j, 64);
            lemma_mod_bound(j, 64);
            if o <= j < o + 64 {
                assert(q == idx) by {
                    lemma_fundamental_div_mod_converse(j, 64, idx, j - o);
                }
                assert(a2[j] == bl[j - o]);
                assert(bl[j - o] == a[c][j]);
            } else {
                assert(q != idx);
                assert(0 <= q < cw(f, c) * ch(f, c)) by {
                    lemma_div_pos_is_pos(j, 64);
                    assert(len == 64 * (cw(f, c) * ch(f, c))) by (nonlinear_arith)
                        requires
                            len == 64 * cw(f, c) * ch(f, c),
                    ;
                    lemma_multiply_divide_lt(j, 64, cw(f, c) * ch(f, c));
                }
                if mcu_of(f, c, q) == m && slot_of(f, c, q) == b {
                    lemma_inv(f, c, q);
                    assert(false);
                }
            }
        }
    }
    assert forall|c2: int| 0 <= c2 < 3 && c2 != c implies #[trigger] nxt[c2] =~= part(f, a, m, b)[c2] by {
        assert forall|j: int| 0 <= j < a[c2].len() implies nxt[c2][j] == part(f, a, m, b)[c2][j] by {
            let q = j / 64;
            if mcu_of(f, c2, q) == m && slot_of(f, c2, q) == b {
                assert(0 <= q < cw(f, c2) * ch(f, c2)) by {
                    lemma_div_pos_is_pos(j, 64);
                    assert(a[c2].len() == 64 * (cw(f, c2) * ch(f, c2))) by (nonlinear_arith)
                        requires
                            a[c2].len() == 64 * cw(f, c2) * ch(f, c2),
                    ;
                    lemma_multiply_divide_lt(j, 64, cw(f, c2) * ch(f, c2));
                }
                lemma_inv(f, c2, q);
                assert(comp_of(f, b) == c2);
                assert(false);
            }
        }
    }
    let st2 = mcu_dc_block(d, f, t, s, st, m, b);
    assert(kind(f, s) is Base);
    assert(st2.a =~= nxt);
}

/// The blocks of MCU `m` from `b`.
pub proof fn lemma_mcu(
    d: Seq<u8>,
    f: Frame,
    t: Tables,
    k: Codes,
    a: Seq<Seq<i16>>,
    p0: int,
    m: int,
    b: int,
    preds: Seq<int>,
    n: int,
    togo: int,
)
    requires
        scan_pre(d, f, t, k, a, p0),
        0 <= m < n_mcus(f),
        0 <= b <= mcu_blocks(f, enc_scan_hdr()),
        preds.len() == 3,
        forall|i: int| 0 <= i < 3 ==> -1024 <= #[trigger] preds[i] <= 1023,
        bits_at(ecs(d, p0), n, enc_mcu(f, k, a, m, b, preds).0),
    ensures
        mcu_dc(d, f, t, enc_scan_hdr(), sst(f, a, m, b, preds, n, p0, togo), m, b) == sst(
            f,
            a,
            m + 1,
            0,
            enc_mcu(f, k, a, m, b, preds).1,
            n + enc_mcu(f, k, a, m, b, preds).0.len(),
            p0,
            togo,
        ),
    decreases mcu_blocks(f, enc_scan_hdr()) - b,
{
    let s = enc_scan_hdr();
    lemma_geom(f);
    if b < mcu_blocks(f, s) {
        lemma_mcu_block(d, f, t, k, a, p0, m, b, preds, n, togo);
        let (i, idx) = blk_index(f, s, m, b);
        let bl = blk(a, i, idx);
        let bits = block_bits(k.dco[s.td[i]], k.dsi[s.td[i]], k.aco[s.td[i]], k.asi[s.td[i]], bl, preds[i]);
        lemma_mcu(d, f, t, k, a, p0, m, b + 1, preds.update(i, bl[0] as int), n + bits.len(), togo);
    } else {
        lemma_part_next(f, a, m, b);
    }
}

proof fn lemma_part_next(f: Frame, a: Seq<Seq<i16>>, m: int, b: int)
    requires
        enc_frame(f),
        coefs_ok(f, a),
        b == mcu_blocks(f, enc_scan_hdr()),
    ensures
        part(f, a, m, b) == part(f, a, m + 1, 0),
{
    lemma_geom(f);
    assert(part(f, a, m, b) =~= part(f, a, m + 1, 0)) by {
        assert forall|c: int| 0 <= c < 3 implies part(f, a, m, b)[c] =~= part(f, a, m + 1, 0)[c] by {
            assert forall|j: int| 0 <= j < a[c].len() implies part(f, a, m, b)[c][j] == part(f, a, m + 1, 0)[c][j] by {
                let q = j / 64;
                if mcu_of(f, c, q) == m {
                    assert(0 <= q < cw(f, c) * ch(f, c)) by {
                        lemma_div_pos_is_pos(j, 64);
                        assert(a[c].len() == 64 * (cw(f, c) * ch(f, c))) by (nonlinear_arith)
                            requires
                                a[c].len() == 64 * cw(f, c) * ch(f, c),
                        ;
                        lemma_multiply_divide_lt(j, 64, cw(f, c) * ch(f, c));
                    }
                    lemma_inv(f, c, q);
                }
            }
        }
    }
}

/// MCUs `m..` of the scan.
pub proof fn lemma_scan_from(d: Seq<u8>, f: Frame, t: Tables, k: Codes, a: Seq<Seq<i16>>, p0: int, m: int)
    requires
        scan_pre(d, f, t, k, a, p0),
        0 <= m <= n_mcus(f),
    ensures
        scan_from(
            d,
            f,
            t,
            enc_scan_hdr(),
            sst(f, a, m, 0, enc_upto(f, k, a, m).1, enc_upto(f, k, a, m).0.len() as int, p0, -m),
            m,
        ) == sst(
            f,
            a,
            n_mcus(f),
            0,
            enc_upto(f, k, a, n_mcus(f)).1,
            enc_upto(f, k, a, n_mcus(f)).0.len() as int,
            p0,
            -n_mcus(f),
        ),
    decreases n_mcus(f) - m,
{
    let s = enc_scan_hdr();
    lemma_geom(f);
    if m < n_mcus(f) {
        let p = enc_upto(f, k, a, m);
        let q = enc_mcu(f, k, a, m, 0, p.1);
        let all = enc_upto(f, k, a, n_mcus(f)).0;
        let e = ecs(d, p0);
        lemma_upto_prefix(f, k, a, m, n_mcus(f));
        lemma_bits_at_sub(e, all, p.0, q.0, p.0.len() as int);
        lemma_preds_ok(f, k, a, m);
        let st = sst(f, a, m, 0, p.1, p.0.len() as int, p0, -m);
        lemma_mcu(d, f, t, k, a, p0, m, 0, p.1, p.0.len() as int, -m);
        let x = mcu_dc(d, f, t, s, st, m, 0);
        assert(x == sst(f, a, m + 1, 0, q.1, (p.0.len() + q.0.len()) as int, p0, -m));
        assert(enc_upto(f, k, a, m + 1) == (p.0 + q.0, q.1));
        assert(x.n <= 8 * e.len());
        assert(mcu_step(d, f, t, s, st, m) == sst(f, a, m + 1, 0, q.1, (p.0.len() + q.0.len()) as int, p0, -(m + 1)));
        lemma_scan_from(d, f, t, k, a, p0, m + 1);
    }
}

/// The whole scan decodes to the coefficients.
pub proof fn lemma_scan(d: Seq<u8>, f: Frame, t: Tables, k: Codes, a: Seq<Seq<i16>>, p0: int)
    requires
        scan_pre(d, f, t, k, a, p0),
    ensures
        scan(
            d,
            f,
            t,
            enc_scan_hdr(),
            Seq::new(f.nc as nat, |c: int| Seq::new((64 * cw(f, c) * ch(f, c)) as nat, |j: int| 0i16)),
            p0,
        ).a == a,
        scan(
            d,
            f,
            t,
            enc_scan_hdr(),
            Seq::new(f.nc as nat, |c: int| Seq::new((64 * cw(f, c) * ch(f, c)) as nat, |j: int| 0i16)),
            p0,
        ).ok,
        scan(
            d,
            f,
            t,
            enc_scan_hdr(),
            Seq::new(f.nc as nat, |c: int| Seq::new((64 * cw(f, c) * ch(f, c)) as nat, |j: int| 0i16)),
            p0,
        ).p == p0,
{
    let s = enc_scan_hdr();
    lemma_geom(f);
    let z = Seq::new(f.nc as nat, |c: int| Seq::new((64 * cw(f, c) * ch(f, c)) as nat, |j: int| 0i16));
    assert(z =~= part(f, a, 0, 0)) by {
        assert forall|c: int| 0 <= c < 3 implies z[c] =~= part(f, a, 0, 0)[c] by {
            assert forall|j: int| 0 <= j < a[c].len() implies part(f, a, 0, 0)[c][j] == 0 by {
                let q = j / 64;
                lemma_div_pos_is_pos(j, 64);
                assert(mcu_of(f, c, q) >= 0) by {
                    let w = cw(f, c);
                    assert(w >= 1) by (nonlinear_arith)
                        requires
                            w == mcux(f) * f.comps[c].h as int,
                            mcux(f) >= 1,
                            f.comps[c].h >= 1,
                    ;
                    lemma_div_pos_is_pos(q, w);
                    lemma_mod_bound(q, w);
                    lemma_div_pos_is_pos(q / w, f.comps[c].v as int);
                    lemma_div_pos_is_pos(q % w, f.comps[c].h as int);
                    assert((q / w) / f.comps[c].v as int * mcux(f) >= 0) by (nonlinear_arith)
                        requires
                            (q / w) / f.comps[c].v as int >= 0,
                            mcux(f) >= 0,
                    ;
                }
                if c == 0 {
                    let w = cw(f, c);
                    assert(w >= 1) by (nonlinear_arith)
                        requires
                            w == mcux(f) * f.comps[c].h as int,
                            mcux(f) >= 1,
                            f.comps[c].h >= 1,
                    ;
                    lemma_div_pos_is_pos(q, w);
                    lemma_mod_bound(q / w, f.comps[0].v as int);
                    lemma_mod_bound(q % w, f.comps[0].h as int);
                    lemma_mod_bound(q, w);
                    assert(slot_of(f, c, q) >= 0) by (nonlinear_arith)
                        requires
                            slot_of(f, c, q) == ((q / w) % f.comps[0].v as int) * f.comps[0].h as int + (q % w)
                                % f.comps[0].h as int,
                            (q / w) % f.comps[0].v as int >= 0,
                            (q % w) % f.comps[0].h as int >= 0,
                            f.comps[0].h >= 1,
                    ;
                }
            }
        }
    }
    let st0 = SS {
        a: z,
        pred: seq![0int, 0int, 0int],
        eob: 0,
        p: p0,
        n: 0,
        insuf: false,
        togo: t.ri as int,
        rst: 0,
        ok: true,
    };
    assert(enc_upto(f, k, a, 0) == (Seq::<bool>::empty(), seq![0int, 0int, 0int]));
    assert(st0 == sst(f, a, 0, 0, seq![0int, 0int, 0int], 0, p0, 0));
    lemma_scan_from(d, f, t, k, a, p0, 0);
    assert(part(f, a, n_mcus(f), 0) =~= a) by {
        assert forall|c: int| 0 <= c < 3 implies part(f, a, n_mcus(f), 0)[c] =~= a[c] by {
            assert forall|j: int| 0 <= j < a[c].len() implies part(f, a, n_mcus(f), 0)[c][j] == a[c][j] by {
                let q = j / 64;
                assert(0 <= q < cw(f, c) * ch(f, c)) by {
                    lemma_div_pos_is_pos(j, 64);
                    assert(a[c].len() == 64 * (cw(f, c) * ch(f, c))) by (nonlinear_arith)
                        requires
                            a[c].len() == 64 * cw(f, c) * ch(f, c),
                    ;
                    lemma_multiply_divide_lt(j, 64, cw(f, c) * ch(f, c));
                }
                lemma_inv(f, c, q);
            }
        }
    }
}

} // verus!
