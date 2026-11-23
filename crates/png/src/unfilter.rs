//! Reconstruction of filtered rows (§9), proven to compute `spec::recon`
//! and `spec::recon_rows`.
use crate::prims::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The row above: `rb` bytes of `dst` at `pv`, or zeros for the first row.
pub open spec fn prev_row(dst: Seq<u8>, pv: int, has_prev: bool, rb: nat) -> Seq<u8> {
    if has_prev {
        dst.subrange(pv, pv + rb)
    } else {
        zeros(rb)
    }
}

/// The Paeth predictor in a form with a short dependency on `a` (the
/// formulation the Rust `png` crate uses for decoding).
#[inline(always)]
pub fn paeth_exec(a: u8, b: u8, c: u8) -> (r: u8)
    ensures
        r == paeth(a, b, c),
{
    let thresh = c as i16 * 3 - (a as i16 + b as i16);
    let lo = if a < b {
        a
    } else {
        b
    };
    let hi = if a < b {
        b
    } else {
        a
    };
    let t0 = if hi as i16 <= thresh {
        lo
    } else {
        c
    };
    if thresh <= lo as i16 {
        hi
    } else {
        t0
    }
}

#[inline(always)]
pub fn predict_exec(ft: u8, a: u8, b: u8, c: u8) -> (r: u8)
    ensures
        r == predict(ft, a, b, c),
{
    if ft == 1 {
        a
    } else if ft == 2 {
        b
    } else if ft == 3 {
        ((a as u16 + b as u16) / 2) as u8
    } else if ft == 4 {
        paeth_exec(a, b, c)
    } else {
        0
    }
}

/// `(x + y) % 256`.
#[inline(always)]
pub fn add8(x: u8, y: u8) -> (r: u8)
    ensures
        r == ((x as nat + y as nat) % 256) as u8,
{
    let s = x as u16 + y as u16;
    if s >= 256 {
        (s - 256) as u8
    } else {
        s as u8
    }
}

/// Reconstructs one row in place: the `rb` filtered bytes at `buf[src]`,
/// filter type `ft`, into `buf[dst..dst + rb]` (`dst <= src`, so each byte
/// is read before it can be overwritten), with the row above at `buf[pv]`
/// (if `has_prev`).
pub fn unfilter_row(
    buf: &mut [u8],
    src: usize,
    dst: usize,
    pv: usize,
    has_prev: bool,
    rb: usize,
    bpp: usize,
    ft: u8,
)
    requires
        src + rb <= old(buf)@.len(),
        dst <= src,
        has_prev ==> pv + rb <= dst,
        1 <= bpp <= 8,
    ensures
        final(buf)@.len() == old(buf)@.len(),
        final(buf)@.subrange(dst as int, dst + rb) == recon(
            ft,
            prev_row(old(buf)@, pv as int, has_prev, rb as nat),
            old(buf)@.subrange(src as int, src + rb),
            bpp as nat,
            rb as nat,
        ),
        forall|k: int|
            0 <= k < final(buf)@.len() && !(dst <= k < dst + rb) ==> #[trigger] final(buf)@[k] == old(
                buf,
            )@[k],
{
    // Each filter type and pixel size gets its own copy of the loop, with
    // the predictor's dispatch and the left-neighbour distance constant.
    if ft == 0 {
        if bpp == 1 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 1, 0)
        } else if bpp == 2 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 2, 0)
        } else if bpp == 3 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 3, 0)
        } else if bpp == 4 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 4, 0)
        } else if bpp == 6 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 6, 0)
        } else if bpp == 8 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 8, 0)
        } else {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, bpp, 0)
        }
    } else if ft == 1 {
        if bpp == 1 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 1, 1)
        } else if bpp == 2 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 2, 1)
        } else if bpp == 3 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 3, 1)
        } else if bpp == 4 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 4, 1)
        } else if bpp == 6 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 6, 1)
        } else if bpp == 8 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 8, 1)
        } else {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, bpp, 1)
        }
    } else if ft == 2 {
        if bpp == 1 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 1, 2)
        } else if bpp == 2 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 2, 2)
        } else if bpp == 3 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 3, 2)
        } else if bpp == 4 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 4, 2)
        } else if bpp == 6 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 6, 2)
        } else if bpp == 8 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 8, 2)
        } else {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, bpp, 2)
        }
    } else if ft == 3 {
        if bpp == 1 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 1, 3)
        } else if bpp == 2 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 2, 3)
        } else if bpp == 3 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 3, 3)
        } else if bpp == 4 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 4, 3)
        } else if bpp == 6 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 6, 3)
        } else if bpp == 8 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 8, 3)
        } else {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, bpp, 3)
        }
    } else if ft == 4 {
        if bpp == 1 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 1, 4)
        } else if bpp == 2 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 2, 4)
        } else if bpp == 3 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 3, 4)
        } else if bpp == 4 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 4, 4)
        } else if bpp == 6 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 6, 4)
        } else if bpp == 8 {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, 8, 4)
        } else {
            unfilter_row_h(buf, src, dst, pv, has_prev, rb, bpp, 4)
        }
    } else {
        unfilter_row_h(buf, src, dst, pv, has_prev, rb, bpp, ft)
    }
}

#[inline(always)]
fn unfilter_row_h(
    buf: &mut [u8],
    src: usize,
    dst: usize,
    pv: usize,
    has_prev: bool,
    rb: usize,
    bpp: usize,
    ft: u8,
)
    requires
        src + rb <= old(buf)@.len(),
        dst <= src,
        has_prev ==> pv + rb <= dst,
        1 <= bpp <= 8,
    ensures
        final(buf)@.len() == old(buf)@.len(),
        final(buf)@.subrange(dst as int, dst + rb) == recon(
            ft,
            prev_row(old(buf)@, pv as int, has_prev, rb as nat),
            old(buf)@.subrange(src as int, src + rb),
            bpp as nat,
            rb as nat,
        ),
        forall|k: int|
            0 <= k < final(buf)@.len() && !(dst <= k < dst + rb) ==> #[trigger] final(buf)@[k] == old(
                buf,
            )@[k],
{
    if has_prev {
        unfilter_row_g(buf, src, dst, pv, true, rb, bpp, ft)
    } else {
        unfilter_row_g(buf, src, dst, pv, false, rb, bpp, ft)
    }
}

#[inline(always)]
fn unfilter_row_g(
    buf: &mut [u8],
    src: usize,
    dst: usize,
    pv: usize,
    has_prev: bool,
    rb: usize,
    bpp: usize,
    ft: u8,
)
    requires
        src + rb <= old(buf)@.len(),
        dst <= src,
        has_prev ==> pv + rb <= dst,
        1 <= bpp <= 8,
    ensures
        final(buf)@.len() == old(buf)@.len(),
        final(buf)@.subrange(dst as int, dst + rb) == recon(
            ft,
            prev_row(old(buf)@, pv as int, has_prev, rb as nat),
            old(buf)@.subrange(src as int, src + rb),
            bpp as nat,
            rb as nat,
        ),
        forall|k: int|
            0 <= k < final(buf)@.len() && !(dst <= k < dst + rb) ==> #[trigger] final(buf)@[k] == old(
                buf,
            )@[k],
{
    let ghost prev = prev_row(buf@, pv as int, has_prev, rb as nat);
    let ghost cur = buf@.subrange(src as int, src + rb);
    let ghost d_in = buf@;
    let mut i: usize = 0;
    let _ = buf.len();
    proof {
        assert(buf@.subrange(dst as int, dst as int) =~= recon(ft, prev, cur, bpp as nat, 0));
    }
    // The first pixel has nothing to its left; the rest of the row runs
    // without that test.
    let first = if bpp < rb {
        bpp
    } else {
        rb
    };
    while i < first
        invariant
            src + rb <= buf@.len(),
            dst <= src,
            buf@.len() <= usize::MAX,
            has_prev ==> pv + rb <= dst,
            1 <= bpp <= 8,
            i <= first,
            first <= rb,
            first <= bpp,
            buf@.len() == d_in.len(),
            prev == prev_row(d_in, pv as int, has_prev, rb as nat),
            cur == d_in.subrange(src as int, src + rb),
            buf@.subrange(dst as int, dst + i) == recon(ft, prev, cur, bpp as nat, i as nat),
            forall|k: int| 0 <= k < buf@.len() && !(dst <= k < dst + i) ==> #[trigger] buf@[k] == d_in[k],
        decreases first - i,
    {
        recon_step(buf, src, dst, pv, has_prev, rb, bpp, ft, i, false, Ghost(prev), Ghost(cur), Ghost(d_in));
        i = i + 1;
    }
    if (ft == 1 || ft == 3 || ft == 4) && i == bpp {
        i = unfilter_reg(buf, src, dst, pv, has_prev, rb, bpp, ft, Ghost(prev), Ghost(cur), Ghost(d_in));
    }
    while i < rb
        invariant
            src + rb <= buf@.len(),
            dst <= src,
            buf@.len() <= usize::MAX,
            has_prev ==> pv + rb <= dst,
            1 <= bpp <= 8,
            i <= rb,
            first <= i,
            first == bpp || first == rb,
            buf@.len() == d_in.len(),
            prev == prev_row(d_in, pv as int, has_prev, rb as nat),
            cur == d_in.subrange(src as int, src + rb),
            buf@.subrange(dst as int, dst + i) == recon(ft, prev, cur, bpp as nat, i as nat),
            forall|k: int| 0 <= k < buf@.len() && !(dst <= k < dst + i) ==> #[trigger] buf@[k] == d_in[k],
        decreases rb - i,
    {
        recon_step(buf, src, dst, pv, has_prev, rb, bpp, ft, i, true, Ghost(prev), Ghost(cur), Ghost(d_in));
        i = i + 1;
    }
}

/// Reconstructs whole pixels from byte `bpp` on, keeping the left and
/// upper-left pixels in registers (they are otherwise re-read from memory
/// just after being written, which puts a store-to-load forward on the
/// critical path). Returns how far it got.
#[inline(always)]
#[verifier::spinoff_prover]
fn unfilter_reg(
    buf: &mut [u8],
    src: usize,
    dst: usize,
    pv: usize,
    has_prev: bool,
    rb: usize,
    bpp: usize,
    ft: u8,
    Ghost(prev): Ghost<Seq<u8>>,
    Ghost(cur): Ghost<Seq<u8>>,
    Ghost(d_in): Ghost<Seq<u8>>,
) -> (r: usize)
    requires
        src + rb <= old(buf)@.len(),
        dst <= src,
        old(buf)@.len() <= usize::MAX,
        has_prev ==> pv + rb <= dst,
        1 <= bpp <= 8,
        bpp <= rb,
        old(buf)@.len() == d_in.len(),
        prev == prev_row(d_in, pv as int, has_prev, rb as nat),
        cur == d_in.subrange(src as int, src + rb),
        old(buf)@.subrange(dst as int, dst + bpp) == recon(ft, prev, cur, bpp as nat, bpp as nat),
        forall|k: int| 0 <= k < old(buf)@.len() && !(dst <= k < dst + bpp) ==> #[trigger] old(buf)@[k] == d_in[k],
    ensures
        bpp <= r <= rb,
        final(buf)@.len() == d_in.len(),
        final(buf)@.subrange(dst as int, dst + r) == recon(ft, prev, cur, bpp as nat, r as nat),
        forall|k: int| 0 <= k < final(buf)@.len() && !(dst <= k < dst + r) ==> #[trigger] final(buf)@[k] == d_in[k],
{
    let mut a: [u8; 8] = [0; 8];
    let mut c: [u8; 8] = [0; 8];
    let mut k: usize = 0;
    while k < bpp
        invariant
            src + rb <= buf@.len(),
            has_prev ==> pv + rb <= dst,
            1 <= bpp <= 8,
            bpp <= rb,
            k <= bpp,
            buf@.len() == d_in.len(),
            prev == prev_row(d_in, pv as int, has_prev, rb as nat),
            buf@.subrange(dst as int, dst + bpp) == recon(ft, prev, cur, bpp as nat, bpp as nat),
            forall|q: int| 0 <= q < buf@.len() && !(dst <= q < dst + bpp) ==> #[trigger] buf@[q] == d_in[q],
            dst <= src,
            buf@.len() <= usize::MAX,
            forall|q: int| #![trigger a@[q]] 0 <= q < k ==> a@[q] == buf@[dst + q] && c@[q] == prev[q],
        decreases bpp - k,
    {
        let va = get(buf, dst + k);
        let vc = if has_prev {
            get(buf, pv + k)
        } else {
            0
        };
        proof {
            if has_prev {
                assert(buf@[pv + k] == d_in[pv + k]);
            }
            assert(vc == prev[k as int]);
        }
        let ghost a0 = a@;
        let ghost c0 = c@;
        a[k] = va;
        c[k] = vc;
        proof {
            assert forall|q: int| #![trigger a@[q]] 0 <= q < k + 1 implies a@[q] == buf@[dst + q] && c@[q] == prev[q] by {
                if q < k {
                    assert(a@[q] == a0[q]);
                    assert(c@[q] == c0[q]);
                }
            }
        }
        k = k + 1;
    }
    let mut i: usize = bpp;
    while i <= rb - bpp
        invariant
            src + rb <= buf@.len(),
            dst <= src,
            buf@.len() <= usize::MAX,
            has_prev ==> pv + rb <= dst,
            1 <= bpp <= 8,
            bpp <= i <= rb,
            buf@.len() == d_in.len(),
            prev == prev_row(d_in, pv as int, has_prev, rb as nat),
            cur == d_in.subrange(src as int, src + rb),
            buf@.subrange(dst as int, dst + i) == recon(ft, prev, cur, bpp as nat, i as nat),
            forall|q: int| 0 <= q < buf@.len() && !(dst <= q < dst + i) ==> #[trigger] buf@[q] == d_in[q],
            forall|q: int| #![trigger a@[q]] 0 <= q < bpp ==> a@[q] == buf@[dst + i - bpp + q] && c@[q] == prev[i - bpp + q],
        decreases rb - i,
    {
        let mut k: usize = 0;
        while k < bpp
            invariant
                src + rb <= buf@.len(),
                dst <= src,
                buf@.len() <= usize::MAX,
                has_prev ==> pv + rb <= dst,
                1 <= bpp <= 8,
                bpp <= i,
                i + bpp <= rb,
                k <= bpp,
                buf@.len() == d_in.len(),
                prev == prev_row(d_in, pv as int, has_prev, rb as nat),
                cur == d_in.subrange(src as int, src + rb),
                buf@.subrange(dst as int, dst + i + k) == recon(ft, prev, cur, bpp as nat, (i + k) as nat),
                forall|q: int| 0 <= q < buf@.len() && !(dst <= q < dst + i + k) ==> #[trigger] buf@[q] == d_in[q],
                forall|q: int| #![trigger a@[q]] 0 <= q < k ==> a@[q] == buf@[dst + i + q] && c@[q] == prev[i + q],
                forall|q: int| #![trigger a@[q]] k <= q < bpp ==> a@[q] == buf@[dst + i - bpp + q] && c@[q] == prev[i - bpp + q],
            decreases bpp - k,
        {
            let ghost b0 = buf@;
            proof {
                assert(a@[k as int] == b0.subrange(dst as int, dst + i + k)[i + k - bpp]);
            }
            let (v, b) = recon_step_reg(buf, src, dst, pv, has_prev, rb, bpp, ft, i + k, a[k], c[k], Ghost(prev), Ghost(cur), Ghost(d_in));
            proof {
                assert forall|q: int| #![trigger a@[q]] 0 <= q < bpp implies (q < k ==> a@[q] == buf@[dst + i + q]) && (k < q ==> a@[q] == buf@[dst + i - bpp + q]) by {
                    if q < k {
                        assert(buf@[dst + i + q] == b0[dst + i + q]);
                    }
                    if k < q {
                        assert(buf@[dst + i - bpp + q] == b0[dst + i - bpp + q]);
                    }
                }
            }
            let ghost a0 = a@;
            let ghost c0 = c@;
            a[k] = v;
            c[k] = b;
            proof {
                assert(a@[k as int] == v && v == buf@[dst + i + k]);
                assert(c@[k as int] == b && b == prev[i + k]);
                assert forall|q: int| #![trigger a@[q]] 0 <= q < bpp implies (q <= k ==> a@[q] == buf@[dst + i + q] && c@[q] == prev[i + q]) && (k < q ==> a@[q] == buf@[dst + i - bpp + q] && c@[q] == prev[i - bpp + q]) by {
                    if q != k {
                        assert(a@[q] == a0[q]);
                        assert(c@[q] == c0[q]);
                    }
                }
            }
            k = k + 1;
        }
        proof {
            assert(k == bpp);
            assert(forall|q: int| #![trigger a@[q]] 0 <= q < k ==> a@[q] == buf@[dst + i + q] && c@[q] == prev[i + q]);
            assert forall|q: int| #![trigger a@[q]] 0 <= q < bpp implies a@[q] == buf@[dst + (i + bpp) - bpp + q] && c@[q] == prev[(i + bpp) - bpp + q] by {
                assert(k == bpp);
                assert(0 <= q < k);
                assert(a@[q] == buf@[dst + i + q]);
                assert(c@[q] == prev[i + q]);
                assert(dst + (i + bpp) - bpp + q == dst + i + q);
            }
        }
        i = i + bpp;
    }
    i
}

/// `recon_step` for `i >= bpp` with the left and upper-left bytes given;
/// returns the new byte and the upper byte.
#[inline(always)]
fn recon_step_reg(
    buf: &mut [u8],
    src: usize,
    dst: usize,
    pv: usize,
    has_prev: bool,
    rb: usize,
    bpp: usize,
    ft: u8,
    i: usize,
    a: u8,
    c: u8,
    Ghost(prev): Ghost<Seq<u8>>,
    Ghost(cur): Ghost<Seq<u8>>,
    Ghost(d_in): Ghost<Seq<u8>>,
) -> (r: (u8, u8))
    requires
        src + rb <= old(buf)@.len(),
        dst <= src,
        old(buf)@.len() <= usize::MAX,
        has_prev ==> pv + rb <= dst,
        1 <= bpp <= 8,
        bpp <= i < rb,
        old(buf)@.len() == d_in.len(),
        prev == prev_row(d_in, pv as int, has_prev, rb as nat),
        cur == d_in.subrange(src as int, src + rb),
        old(buf)@.subrange(dst as int, dst + i) == recon(ft, prev, cur, bpp as nat, i as nat),
        forall|k: int| 0 <= k < old(buf)@.len() && !(dst <= k < dst + i) ==> #[trigger] old(buf)@[k] == d_in[k],
        a == old(buf)@[dst + i - bpp],
        c == prev[i - bpp],
    ensures
        final(buf)@.len() == d_in.len(),
        final(buf)@.subrange(dst as int, dst + i + 1) == recon(ft, prev, cur, bpp as nat, (i + 1) as nat),
        forall|k: int| 0 <= k < final(buf)@.len() && !(dst <= k < dst + i + 1) ==> #[trigger] final(buf)@[k] == d_in[k],
        r.0 == final(buf)@[dst + i],
        r.1 == prev[i as int],
        forall|k: int| 0 <= k < final(buf)@.len() && k != dst + i ==> #[trigger] final(buf)@[k] == old(buf)@[k],
{
    let x = get(buf, src + i);
    let b = if has_prev {
        get(buf, pv + i)
    } else {
        0
    };
    let v = add8(x, predict_exec(ft, a, b, c));
    let ghost d0 = buf@;
    proof {
        let rc = recon(ft, prev, cur, bpp as nat, i as nat);
        assert(rc.len() == i) by {
            lemma_recon_len(ft, prev, cur, bpp as nat, i as nat);
        }
        assert(a == d0.subrange(dst as int, dst + i)[i - bpp]);
        assert(a == rc[i - bpp]);
        assert(b == prev[i as int]);
        assert(x == d_in[src + i]);
        assert(x == cur[i as int]);
    }
    set(buf, dst + i, v);
    proof {
        assert(buf@.subrange(dst as int, dst + i + 1) =~= d0.subrange(dst as int, dst + i).push(v));
    }
    (v, b)
}

/// Reconstructs byte `i` of the row, given bytes `0..i`; `left` says
/// whether there is a byte `bpp` to the left.
#[inline(always)]
fn recon_step(
    buf: &mut [u8],
    src: usize,
    dst: usize,
    pv: usize,
    has_prev: bool,
    rb: usize,
    bpp: usize,
    ft: u8,
    i: usize,
    left: bool,
    Ghost(prev): Ghost<Seq<u8>>,
    Ghost(cur): Ghost<Seq<u8>>,
    Ghost(d_in): Ghost<Seq<u8>>,
)
    requires
        src + rb <= old(buf)@.len(),
        dst <= src,
        old(buf)@.len() <= usize::MAX,
        has_prev ==> pv + rb <= dst,
        1 <= bpp <= 8,
        i < rb,
        left == (i >= bpp),
        old(buf)@.len() == d_in.len(),
        prev == prev_row(d_in, pv as int, has_prev, rb as nat),
        cur == d_in.subrange(src as int, src + rb),
        old(buf)@.subrange(dst as int, dst + i) == recon(ft, prev, cur, bpp as nat, i as nat),
        forall|k: int| 0 <= k < old(buf)@.len() && !(dst <= k < dst + i) ==> #[trigger] old(buf)@[k] == d_in[k],
    ensures
        final(buf)@.len() == d_in.len(),
        final(buf)@.subrange(dst as int, dst + i + 1) == recon(ft, prev, cur, bpp as nat, (i + 1) as nat),
        forall|k: int| 0 <= k < final(buf)@.len() && !(dst <= k < dst + i + 1) ==> #[trigger] final(buf)@[k] == d_in[k],
{
    let x = get(buf, src + i);
    let a = if left {
        get(buf, dst + i - bpp)
    } else {
        0
    };
    let b = if has_prev {
        get(buf, pv + i)
    } else {
        0
    };
    let c = if has_prev && left {
        get(buf, pv + i - bpp)
    } else {
        0
    };
    let v = add8(x, predict_exec(ft, a, b, c));
    let ghost d0 = buf@;
    proof {
        let rc = recon(ft, prev, cur, bpp as nat, i as nat);
        assert(rc.len() == i) by {
            lemma_recon_len(ft, prev, cur, bpp as nat, i as nat);
        }
        if i >= bpp {
            assert(a == d0.subrange(dst as int, dst + i)[i - bpp]);
            assert(a == rc[i - bpp]);
        }
        if has_prev {
            assert(b == prev[i as int]);
            if i >= bpp {
                assert(c == prev[i - bpp]);
            }
        } else {
            assert(b == prev[i as int]);
        }
        assert(x == d_in[src + i]);
        assert(x == cur[i as int]);
    }
    set(buf, dst + i, v);
    proof {
        assert(buf@.subrange(dst as int, dst + i + 1) =~= d0.subrange(dst as int, dst + i).push(v));
    }
}

pub proof fn lemma_recon_len(ft: u8, prev: Seq<u8>, cur: Seq<u8>, bpp: nat, n: nat)
    ensures
        recon(ft, prev, cur, bpp, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_recon_len(ft, prev, cur, bpp, (n - 1) as nat);
    }
}


pub proof fn lemma_rows_len(raw: Seq<u8>, off: int, rb: nat, bpp: nat, n: nat)
    ensures
        recon_rows(raw, off, rb, bpp, n) matches Some(s) ==> s.len() == n * rb,
    decreases n,
{
    if n > 0 {
        lemma_rows_len(raw, off, rb, bpp, (n - 1) as nat);
        if let Some(s) = recon_rows(raw, off, rb, bpp, n) {
            let done = recon_rows(raw, off, rb, bpp, (n - 1) as nat).unwrap();
            let i = off + (n - 1) * (rb + 1);
            let prev = if n == 1 {
                zeros(rb)
            } else {
                done.subrange((n - 2) * rb, (n - 1) * rb)
            };
            lemma_recon_len(raw[i], prev, raw.subrange(i + 1, i + 1 + rb), bpp, rb);
            assert((n - 1) * rb + rb == n * rb) by (nonlinear_arith);
        }
    }
}

/// Rows past an invalid filter type do not help.
pub proof fn lemma_rows_none(raw: Seq<u8>, off: int, rb: nat, bpp: nat, y: nat, n: nat)
    requires
        y <= n,
        recon_rows(raw, off, rb, bpp, y) is None,
    ensures
        recon_rows(raw, off, rb, bpp, n) is None,
    decreases n - y,
{
    if y < n {
        lemma_rows_none(raw, off, rb, bpp, y + 1, n);
    }
}

/// Earlier rows are a prefix of later ones.
pub proof fn lemma_rows_prefix(raw: Seq<u8>, off: int, rb: nat, bpp: nat, y: nat, n: nat)
    requires
        y <= n,
        recon_rows(raw, off, rb, bpp, n) is Some,
    ensures
        recon_rows(raw, off, rb, bpp, y) matches Some(s) && s == recon_rows(raw, off, rb, bpp, n).unwrap().subrange(
            0,
            (y * rb) as int,
        ),
    decreases n - y,
{
    lemma_rows_len(raw, off, rb, bpp, y);
    lemma_rows_len(raw, off, rb, bpp, n);
    if y == n {
        assert(recon_rows(raw, off, rb, bpp, n).unwrap().subrange(0, (n * rb) as int) =~= recon_rows(raw, off, rb, bpp, n).unwrap());
    } else {
        if recon_rows(raw, off, rb, bpp, y) is None {
            lemma_rows_none(raw, off, rb, bpp, y, n);
        }
        lemma_rows_prefix(raw, off, rb, bpp, y + 1, n);
        lemma_rows_len(raw, off, rb, bpp, y + 1);
        let s1 = recon_rows(raw, off, rb, bpp, y + 1).unwrap();
        let s0 = recon_rows(raw, off, rb, bpp, y).unwrap();
        assert(y * rb <= (y + 1) * rb) by (nonlinear_arith);
        assert(s1.subrange(0, (y * rb) as int) =~= s0);
        let full = recon_rows(raw, off, rb, bpp, n).unwrap();
        assert((y + 1) * rb <= n * rb) by (nonlinear_arith) requires y + 1 <= n;
        assert(full.subrange(0, ((y + 1) * rb) as int).subrange(0, (y * rb) as int) =~= full.subrange(0, (y * rb) as int));
    }
}

/// Reconstructs `n` rows of `rb` bytes in place: the filtered rows at
/// `buf[off]` (each a filter byte and `rb` bytes) become rows at `buf[o]`,
/// `o <= off` (`spec::recon_rows`). Returns `false` at an invalid filter
/// type. Bytes before `o` and from the end of the filtered rows on are
/// left alone.
pub fn unfilter_rows(buf: &mut [u8], off: usize, rb: usize, bpp: usize, n: usize, o: usize) -> (ok: bool)
    requires
        off + n * (rb + 1) <= old(buf)@.len(),
        o <= off,
        1 <= bpp <= 8,
    ensures
        final(buf)@.len() == old(buf)@.len(),
        match recon_rows(old(buf)@, off as int, rb as nat, bpp as nat, n as nat) {
            Some(s) => ok && final(buf)@.subrange(o as int, o + n * rb) == s,
            None => !ok,
        },
        forall|k: int|
            0 <= k < final(buf)@.len() && (k < o || k >= off + n * (rb + 1)) ==> #[trigger] final(buf)@[k] == old(
                buf,
            )@[k],
{
    let _ = buf.len();
    let ghost raw = buf@;
    let mut y: usize = 0;
    let mut ro = off;
    let mut wo = o;
    proof {
        assert(buf@.subrange(o as int, o as int) =~= Seq::<u8>::empty());
        assert(n * rb <= n * (rb + 1)) by (nonlinear_arith);
    }
    while y < n
        invariant
            off + n * (rb + 1) <= raw.len(),
            o <= off,
            raw == old(buf)@,
            buf@.len() == raw.len(),
            raw.len() <= usize::MAX,
            1 <= bpp <= 8,
            y <= n,
            ro == off + y * (rb + 1),
            wo == o + y * rb,
            y * rb <= n * rb,
            y * rb <= y * (rb + 1),
            recon_rows(raw, off as int, rb as nat, bpp as nat, y as nat) matches Some(s)
                && buf@.subrange(o as int, wo as int) == s,
            forall|k: int|
                0 <= k < buf@.len() && (k < o || k >= ro) ==> #[trigger] buf@[k] == raw[k],
        decreases n - y,
    {
        proof {
            assert(y * (rb + 1) + (rb + 1) <= n * (rb + 1)) by (nonlinear_arith) requires y < n;
            assert(y * rb + rb <= n * rb) by (nonlinear_arith) requires y < n;
            assert((y + 1) * (rb + 1) == y * (rb + 1) + (rb + 1)) by (nonlinear_arith);
            assert((y + 1) * rb == y * rb + rb) by (nonlinear_arith);
            lemma_rows_len(raw, off as int, rb as nat, bpp as nat, y as nat);
        }
        let ft = get(buf, ro);
        if ft > 4 {
            proof {
                lemma_rows_none(raw, off as int, rb as nat, bpp as nat, (y + 1) as nat, n as nat);
            }
            return false;
        }
        let ghost d0 = buf@;
        let ghost s = recon_rows(raw, off as int, rb as nat, bpp as nat, y as nat).unwrap();
        proof {
            if y > 0 {
                assert(y * rb >= rb) by (nonlinear_arith) requires y >= 1;
            }
        }
        let pv = if y > 0 {
            wo - rb
        } else {
            0
        };
        proof {
            assert(d0.subrange(ro + 1, ro + 1 + rb) =~= raw.subrange(ro + 1, ro + 1 + rb));
        }
        unfilter_row(buf, ro + 1, wo, pv, y > 0, rb, bpp, ft);
        proof {
            let prev = prev_row(d0, pv as int, y > 0, rb as nat);
            if y > 0 {
                assert((y - 1) * rb == y * rb - rb) by (nonlinear_arith) requires y >= 1;
                assert(prev =~= s.subrange((y - 1) * rb, y * rb));
            }
            assert(raw[ro as int] == ft);
            assert(buf@.subrange(o as int, wo + rb) =~= d0.subrange(o as int, wo as int) + buf@.subrange(wo as int, wo + rb));
            assert((y + 1) * rb <= n * rb) by (nonlinear_arith) requires y + 1 <= n;
            assert((y + 1) * rb <= (y + 1) * (rb + 1)) by (nonlinear_arith);
        }
        y = y + 1;
        ro = ro + rb + 1;
        wo = wo + rb;
    }
    true
}

} // verus!
