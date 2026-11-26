//! Streaming for files of a single sequential scan: the scan is decoded
//! one MCU row at a time into a window of each component's coefficients,
//! and the row's samples are computed from the window before it is reused.
//! The whole coefficient arrays of the specification are kept only as
//! ghost state. Nothing is left to compute from them: a later scan of such
//! a file is an error (T.81 allows one scan per component of a sequential
//! frame), so the samples are final when the scan ends.
use crate::idct::*;
use crate::prims::*;
use crate::work::*;
#[cfg(verus_only)]
use crate::scan::lemma_grid;
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// The start of the window of MCU row `row` in a component's coefficients:
/// `vr` block rows of `cw` blocks per MCU row.
pub open spec fn wbase(cw: int, vr: int, row: int) -> int {
    64 * (cw * (vr * row))
}

/// What streaming holds of one component after `row` MCU rows.
///
/// `g` is the component's whole coefficient array, `cw` by `chh` blocks;
/// `a` is the window, the `vr` block rows of MCU row `row`; `pl` is the
/// component's plane of samples, `8 * wb` by `8 * hb`, whose rows above the
/// window's are done.
pub open spec fn win_ok(
    a: Seq<i16>,
    g: Seq<i16>,
    pl: Seq<u8>,
    q: Seq<u16>,
    cw: int,
    chh: int,
    wb: int,
    hb: int,
    vr: int,
    row: int,
) -> bool {
    &&& 1 <= wb <= cw
    &&& 1 <= hb <= chh
    &&& 1 <= vr
    &&& 0 <= row
    &&& g.len() == 64 * (cw * chh)
    &&& a.len() == 64 * (cw * vr)
    &&& pl.len() == (8 * wb) * (8 * hb)
    &&& win_same(a, g, cw, chh, vr, row)
    &&& win_tail(g, cw, vr, row)
    &&& win_done(g, pl, q, cw, wb, vr, row)
}

/// The window is that part of the array, while there is such a part.
pub open spec fn win_same(a: Seq<i16>, g: Seq<i16>, cw: int, chh: int, vr: int, row: int) -> bool {
    vr * (row + 1) <= chh ==> forall|j: int| 0 <= j < a.len() ==> (#[trigger] a[j]) == g[wbase(cw, vr, row) + j]
}

/// The array is zero after the window.
pub open spec fn win_tail(g: Seq<i16>, cw: int, vr: int, row: int) -> bool {
    forall|j: int| wbase(cw, vr, row + 1) <= j < g.len() ==> (#[trigger] g[j]) == 0
}

/// The plane's rows above the window's hold the samples.
pub open spec fn win_done(g: Seq<i16>, pl: Seq<u8>, q: Seq<u16>, cw: int, wb: int, vr: int, row: int) -> bool {
    forall|j: int|
        0 <= j < pl.len() && j / (8 * wb) < 8 * (vr * row) ==> (#[trigger] pl[j]) == psample(
            g,
            q,
            cw,
            j / (8 * wb),
            j % (8 * wb),
        )
}

pub proof fn lemma_zz(k: int)
    requires
        0 <= k < 80,
    ensures
        0 <= zz(k) <= 63,
{
}

/// The AC coefficients of a block depend on the block's own 64
/// coefficients and change only those.
pub proof fn lemma_base_ac_win(t: HuffTable, e: Seq<u8>, n: int, k: int, a1: Seq<i16>, o1: int, a2: Seq<i16>, o2: int)
    requires
        0 <= k,
        0 <= o1,
        o1 + 64 <= a1.len(),
        0 <= o2,
        o2 + 64 <= a2.len(),
        forall|j: int| o1 <= j < o1 + 64 ==> (#[trigger] a1[j]) == a2[j - o1 + o2],
    ensures
        ({
            let r1 = base_ac(t, e, n, k, a1, o1);
            let r2 = base_ac(t, e, n, k, a2, o2);
            &&& r1.1 == r2.1
            &&& r1.0.len() == a1.len()
            &&& r2.0.len() == a2.len()
            &&& forall|j: int| o1 <= j < o1 + 64 ==> (#[trigger] r1.0[j]) == r2.0[j - o1 + o2]
            &&& forall|j: int| 0 <= j < a1.len() && !(o1 <= j < o1 + 64) ==> (#[trigger] r1.0[j]) == a1[j]
            &&& forall|j: int| 0 <= j < a2.len() && !(o2 <= j < o2 + 64) ==> (#[trigger] r2.0[j]) == a2[j]
        }),
    decreases togo(k, 64),
{
    if k < 64 {
        lemma_huff(t, e, n);
        let (sym, n1) = huff(t, e, n);
        let r = sym / 16;
        let s = sym % 16;
        if s != 0 {
            let v = extend(ebits(e, n1, s as nat), s);
            lemma_zz(k + r);
            let z = zz(k + r);
            let b1 = a1.update(o1 + z, #[verifier::truncate] (v as i16));
            let b2 = a2.update(o2 + z, #[verifier::truncate] (v as i16));
            assert forall|j: int| o1 <= j < o1 + 64 implies (#[trigger] b1[j]) == b2[j - o1 + o2] by {
                assert(a1[j] == a2[j - o1 + o2]);
            }
            lemma_base_ac_win(t, e, n1 + s, k + r + 1, b1, o1, b2, o2);
        } else if r == 15 {
            lemma_base_ac_win(t, e, n1, k + 16, a1, o1, a2, o2);
        }
    }
}

/// A sequential block depends on the block's own 64 coefficients and
/// changes only those.
pub proof fn lemma_base_block_win(
    dct: HuffTable,
    act: HuffTable,
    e: Seq<u8>,
    n: int,
    pred: int,
    a1: Seq<i16>,
    o1: int,
    a2: Seq<i16>,
    o2: int,
)
    requires
        0 <= o1,
        o1 + 64 <= a1.len(),
        0 <= o2,
        o2 + 64 <= a2.len(),
        forall|j: int| o1 <= j < o1 + 64 ==> (#[trigger] a1[j]) == a2[j - o1 + o2],
    ensures
        ({
            let r1 = base_block(dct, act, e, n, pred, a1, o1);
            let r2 = base_block(dct, act, e, n, pred, a2, o2);
            &&& r1.1 == r2.1
            &&& r1.2 == r2.2
            &&& r1.0.len() == a1.len()
            &&& r2.0.len() == a2.len()
            &&& forall|j: int| o1 <= j < o1 + 64 ==> (#[trigger] r1.0[j]) == r2.0[j - o1 + o2]
            &&& forall|j: int| 0 <= j < a1.len() && !(o1 <= j < o1 + 64) ==> (#[trigger] r1.0[j]) == a1[j]
            &&& forall|j: int| 0 <= j < a2.len() && !(o2 <= j < o2 + 64) ==> (#[trigger] r2.0[j]) == a2[j]
        }),
{
    let (diff, n1) = dc_diff(dct, e, n);
    let p = wrap32(pred + diff);
    let b1 = a1.update(o1, wrap16(p) as i16);
    let b2 = a2.update(o2, wrap16(p) as i16);
    assert forall|j: int| o1 <= j < o1 + 64 implies (#[trigger] b1[j]) == b2[j - o1 + o2] by {
        assert(a1[j] == a2[j - o1 + o2]);
    }
    lemma_base_ac_win(act, e, n1, 1, b1, o1, b2, o2);
}

/// A sample depends only on its block's coefficients.
pub proof fn lemma_psample_same(g1: Seq<i16>, g2: Seq<i16>, q: Seq<u16>, cw: int, r: int, x: int)
    requires
        forall|j: int|
            64 * ((r / 8) * cw + x / 8) <= j < 64 * ((r / 8) * cw + x / 8) + 64 ==> (#[trigger] g1[j]) == g2[j],
    ensures
        psample(g1, q, cw, r, x) == psample(g2, q, cw, r, x),
{
    let o = 64 * ((r / 8) * cw + x / 8);
    assert forall|k: int| 0 <= k < 64 implies dequant(g1, o, q)[k] == dequant(g2, o, q)[k] by {
        assert(g1[o + k] == g2[o + k]);
    }
    assert(dequant(g1, o, q) =~= dequant(g2, o, q));
}

/// Decoding a block of the window's MCU row into the window is decoding it
/// into the array: `lo` is the block's place in the window.
pub proof fn lemma_win_block(
    dct: HuffTable,
    act: HuffTable,
    e: Seq<u8>,
    n: int,
    pred: int,
    a: Seq<i16>,
    g: Seq<i16>,
    pl: Seq<u8>,
    q: Seq<u16>,
    cw: int,
    chh: int,
    wb: int,
    hb: int,
    vr: int,
    row: int,
    lo: int,
)
    requires
        win_ok(a, g, pl, q, cw, chh, wb, hb, vr, row),
        vr * (row + 1) <= chh,
        0 <= lo,
        lo + 64 <= a.len(),
    ensures
        ({
            let go = wbase(cw, vr, row) + lo;
            let r1 = base_block(dct, act, e, n, pred, a, lo);
            let r2 = base_block(dct, act, e, n, pred, g, go);
            &&& 0 <= go
            &&& go + 64 <= g.len()
            &&& r1.1 == r2.1
            &&& r1.2 == r2.2
            &&& win_ok(r1.0, r2.0, pl, q, cw, chh, wb, hb, vr, row)
        }),
{
    let base = wbase(cw, vr, row);
    let go = base + lo;
    let r1 = base_block(dct, act, e, n, pred, a, lo);
    let r2 = base_block(dct, act, e, n, pred, g, go);
    assert(0 <= base && base + 64 * (cw * vr) <= 64 * (cw * chh) && wbase(cw, vr, row + 1) == base + 64 * (cw * vr))
        by (nonlinear_arith)
        requires
            base == 64 * (cw * (vr * row)),
            wbase(cw, vr, row + 1) == 64 * (cw * (vr * (row + 1))),
            vr * (row + 1) <= chh,
            cw >= 1,
            vr >= 1,
            row >= 0,
    ;
    assert forall|j: int| lo <= j < lo + 64 implies (#[trigger] a[j]) == g[j - lo + go] by {}
    lemma_base_block_win(dct, act, e, n, pred, a, lo, g, go);
    assert forall|j: int| 0 <= j < r1.0.len() implies (#[trigger] r1.0[j]) == r2.0[base + j] by {
        if lo <= j < lo + 64 {
            assert(r1.0[j] == r2.0[j - lo + go]);
        } else {
            assert(r1.0[j] == a[j]);
            assert(r2.0[base + j] == g[base + j]);
        }
    }
    assert forall|j: int| wbase(cw, vr, row + 1) <= j < r2.0.len() implies (#[trigger] r2.0[j]) == 0 by {
        assert(r2.0[j] == g[j]);
    }
    let st = 8 * wb;
    assert forall|j: int| 0 <= j < pl.len() && j / st < 8 * (vr * row) implies (#[trigger] pl[j]) == psample(
        r2.0,
        q,
        cw,
        j / st,
        j % st,
    ) by {
        let r = j / st;
        let x = j % st;
        lemma_mod_bound(j, st);
        let bo = 64 * ((r / 8) * cw + x / 8);
        assert(r >= 0) by (nonlinear_arith)
            requires
                j >= 0,
                st > 0,
                r == j / st,
        ;
        assert(0 <= bo && bo + 64 <= base) by (nonlinear_arith)
            requires
                bo == 64 * ((r / 8) * cw + x / 8),
                base == 64 * (cw * (vr * row)),
                0 <= r / 8 < vr * row,
                0 <= x / 8 < cw,
        ;
        assert forall|jj: int| bo <= jj < bo + 64 implies (#[trigger] g[jj]) == r2.0[jj] by {
            assert(r2.0[jj] == g[jj]);
        }
        lemma_psample_same(g, r2.0, q, cw, r, x);
    }
}

/// Zeros the window.
fn win_zero(a: &mut Vec<i16>, Tracked(mt): Tracked<&mut Meter>)
    ensures
        final(a).len() == old(a).len(),
        forall|j: int| 0 <= j < final(a).len() ==> (#[trigger] final(a)[j]) == 0,
        final(mt).n == old(mt).n + old(a).len(),
{
    let n = a.len();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            a.len() == n,
            forall|i: int| 0 <= i < j ==> (#[trigger] a[i]) == 0,
            mt.n == old(mt).n + j,
        decreases n - j,
    {
        vset(a, j, 0i16);
        j += 1;
        proof {
            mt.n = mt.n + 1;
        }
    }
}

/// The end of MCU row `row`: the samples of the window's blocks go to the
/// plane, and the window becomes the next MCU row's, zeros.
#[inline(never)]
pub fn flush_x(
    a: &mut Vec<i16>,
    pl: &mut Vec<u8>,
    q: &[u16; 64],
    rl: &[u8; 1024],
    kt: &[i16; 24],
    cw: usize,
    wb: usize,
    hb: usize,
    vr: usize,
    row: usize,
    Ghost(g): Ghost<Seq<i16>>,
    Ghost(chh): Ghost<int>,
    Tracked(mt): Tracked<&mut Meter>,
)
    requires
        win_ok(old(a)@, g, old(pl)@, q@, cw as int, chh, wb as int, hb as int, vr as int, row as int),
        vr * (row + 1) <= chh,
        chh <= 0x4_0080,
        cw <= 0x4_0080,
        forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
        kt@ == crate::idct16::kt_spec(),
    ensures
        win_ok(final(a)@, g, final(pl)@, q@, cw as int, chh, wb as int, hb as int, vr as int, row + 1),
        final(mt).n <= old(mt).n + 66 * (cw * vr),
{
    let stride = 8 * wb;
    let ghost st = stride as int;
    let ghost base = wbase(cw as int, vr as int, row as int);
    let ghost cwi = cw as int;
    assert(0 <= vr * row && vr * row + vr <= chh && base == 64 * (cwi * (vr * row)) && 0 <= base && base + 64 * (cwi * vr)
        <= 64 * (cwi * chh) && wbase(cwi, vr as int, row + 1) == base + 64 * (cwi * vr)) by (nonlinear_arith)
        requires
            base == 64 * (cwi * (vr * row)),
            wbase(cwi, vr as int, row + 1) == 64 * (cwi * (vr * (row + 1))),
            vr * (row + 1) <= chh,
            cwi >= 1,
            vr >= 1,
            row >= 0,
    ;
    let by0 = vr * row;
    let mut ly: usize = 0;
    while ly < vr
        invariant
            ly <= vr,
            mt.n <= old(mt).n + ly * (wb + 1),
            by0 == vr * row,
            by0 + vr <= chh <= 0x4_0080,
            st == stride == 8 * wb,
            cwi == cw <= 0x4_0080,
            1 <= wb <= cw,
            1 <= hb <= chh,
            a@ == old(a)@,
            a.len() == 64 * (cw * vr),
            g.len() == 64 * (cwi * chh),
            pl.len() == st * (8 * hb),
            base == 64 * (cwi * by0),
            0 <= base,
            base + 64 * (cwi * vr) <= 64 * (cwi * chh),
            forall|j: int| 0 <= j < a.len() ==> (#[trigger] a[j]) == g[base + j],
            forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
            kt@ == crate::idct16::kt_spec(),
            forall|j: int|
                0 <= j < pl.len() && j / st < 8 * (by0 + ly) ==> (#[trigger] pl[j]) == psample(g, q@, cwi, j / st, j % st),
        decreases vr - ly,
    {
        let by = by0 + ly;
        let ghost m1 = mt.n;
        if by < hb {
            let mut bx: usize = 0;
            while bx < wb
                invariant
                    bx <= wb,
                    mt.n <= m1 + bx,
                    ly < vr,
                    by == by0 + ly,
                    by < hb,
                    by0 + vr <= chh <= 0x4_0080,
                    st == stride == 8 * wb,
                    cwi == cw <= 0x4_0080,
                    1 <= wb <= cw,
                    1 <= hb <= chh,
                    a@ == old(a)@,
                    a.len() == 64 * (cw * vr),
                    g.len() == 64 * (cwi * chh),
                    pl.len() == st * (8 * hb),
                    base == 64 * (cwi * by0),
                    0 <= base,
                    base + 64 * (cwi * vr) <= 64 * (cwi * chh),
                    forall|j: int| 0 <= j < a.len() ==> (#[trigger] a[j]) == g[base + j],
                    forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
                    kt@ == crate::idct16::kt_spec(),
                    forall|j: int|
                        0 <= j < pl.len() && (j / st < 8 * by || (j / st < 8 * by + 8 && j % st < 8 * bx)) ==> (
                        #[trigger] pl[j]) == psample(g, q@, cwi, j / st, j % st),
                decreases wb - bx,
            {
                proof {
                    lemma_grid(ly as int, bx as int, vr as int, cwi);
                    assert((8 * by + 8) * st <= st * (8 * hb)) by (nonlinear_arith)
                        requires
                            by < hb,
                            st >= 0,
                    ;
                }
                let lo = 64 * (ly * cw + bx);
                let ghost out0 = pl@;
                let blk = idct_into(pl, a, lo, q, rl, kt, 8 * by, 8 * bx, stride);
                let ghost go = 64 * (by * cwi + bx);
                proof {
                    assert(go == base + lo) by (nonlinear_arith)
                        requires
                            go == 64 * (by * cwi + bx),
                            lo == 64 * (ly * cwi + bx),
                            base == 64 * (cwi * by0),
                            by == by0 + ly,
                    ;
                    assert forall|k: int| 0 <= k < 64 implies dequant(a@, lo as int, q@)[k] == dequant(g, go, q@)[k] by {
                        assert(a[lo + k] == g[base + (lo + k)]);
                    }
                    assert(dequant(a@, lo as int, q@) =~= dequant(g, go, q@));
                }
                proof {
                    lemma_block_stored(out0, pl@, blk@, g, q@, cwi, st, by as int, bx as int);
                }
                bx += 1;
                proof {
                    mt.n = mt.n + 1;
                }
            }
            proof {
                assert forall|j: int| 0 <= j < pl.len() && j / st < 8 * (by + 1) implies (#[trigger] pl[j]) == psample(
                    g,
                    q@,
                    cwi,
                    j / st,
                    j % st,
                ) by {
                    lemma_mod_bound(j, st);
                }
            }
        } else {
            proof {
                assert forall|j: int| 0 <= j < pl.len() && j / st < 8 * (by + 1) implies (#[trigger] pl[j]) == psample(
                    g,
                    q@,
                    cwi,
                    j / st,
                    j % st,
                ) by {
                    assert(j / st < 8 * hb) by (nonlinear_arith)
                        requires
                            0 <= j < st * (8 * hb),
                            st > 0,
                    ;
                }
            }
        }
        ly += 1;
        proof {
            mt.n = mt.n + 1;
            assert(ly * (wb + 1) == (ly - 1) * (wb + 1) + wb + 1) by (nonlinear_arith);
        }
    }
    win_zero(a, Tracked(mt));
    assert(vr * (wb + 1) + 64 * (cw * vr) <= 66 * (cw * vr)) by (nonlinear_arith)
        requires
            1 <= wb <= cw,
            vr >= 0,
    ;
    proof {
        let nb = wbase(cwi, vr as int, row + 1);
        assert(8 * (vr * (row + 1)) == 8 * (by0 + vr)) by (nonlinear_arith)
            requires
                by0 == vr * row,
        ;
        if vr * (row + 2) <= chh {
            assert(nb + 64 * (cwi * vr) <= 64 * (cwi * chh)) by (nonlinear_arith)
                requires
                    nb == 64 * (cwi * (vr * (row + 1))),
                    vr * (row + 2) <= chh,
                    cwi >= 1,
            ;
            assert forall|j: int| 0 <= j < a.len() implies (#[trigger] a[j]) == g[nb + j] by {
                assert(g[nb + j] == 0);
            }
        }
        assert(wbase(cwi, vr as int, row + 2) >= nb) by (nonlinear_arith)
            requires
                nb == 64 * (cwi * (vr * (row + 1))),
                wbase(cwi, vr as int, row + 2) == 64 * (cwi * (vr * (row + 2))),
                cwi >= 1,
                vr >= 1,
        ;
    }
}

} // verus!
