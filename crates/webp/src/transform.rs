//! Reading the transforms (§4), proven to compute `spec::read_transforms`.
use crate::bitreader::*;
use crate::image::*;
use crate::pixels::*;
use crate::pxops::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// A transform as decoded (`spec::Transform`).
pub enum XForm {
    Predictor { bits: u32, w: usize, data: Vec<u32> },
    Color { bits: u32, w: usize, data: Vec<u32> },
    SubtractGreen,
    ColorIndexing { bits: u32, w: usize, palette: Vec<u32> },
}

pub open spec fn tview(t: XForm) -> Transform {
    match t {
        XForm::Predictor { bits, w, data } => Transform::Predictor { bits: bits as nat, w: w as nat, data: data@ },
        XForm::Color { bits, w, data } => Transform::Color { bits: bits as nat, w: w as nat, data: data@ },
        XForm::SubtractGreen => Transform::SubtractGreen,
        XForm::ColorIndexing { bits, w, palette } => Transform::ColorIndexing {
            bits: bits as nat,
            w: w as nat,
            palette: palette@,
        },
    }
}

pub open spec fn tviews(ts: Seq<XForm>) -> Seq<Transform> {
    Seq::new(ts.len(), |i: int| tview(ts[i]))
}

/// The width after transform `t` of an image `w` wide.
pub open spec fn next_w(t: Transform, w: nat) -> nat {
    match t {
        Transform::ColorIndexing { bits, .. } => subsample(w, bits),
        _ => w,
    }
}

/// The width after the first `k` transforms.
pub open spec fn width_at(ts: Seq<Transform>, w: nat, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        w
    } else {
        next_w(ts[k - 1], width_at(ts, w, (k - 1) as nat))
    }
}

/// The palette size for `bits` bits of bundling.
pub open spec fn pal_size(bits: nat) -> nat {
    pow2((8nat / pow2(bits)) as nat)
}

/// A transform read for an image `w` wide and `h` high.
pub open spec fn wf_t(t: Transform, w: nat, h: nat) -> bool {
    match t {
        Transform::Predictor { bits, w: tw, data } => tw == w && 2 <= bits <= 9 && data.len() == subsample(w, bits)
            * subsample(h, bits),
        Transform::Color { bits, w: tw, data } => tw == w && 2 <= bits <= 9 && data.len() == subsample(w, bits)
            * subsample(h, bits),
        Transform::SubtractGreen => true,
        Transform::ColorIndexing { bits, w: tw, palette } => tw == w && bits <= 3 && palette.len() == pal_size(bits),
    }
}

/// The transforms fit together.
pub open spec fn chain_ok(ts: Seq<Transform>, w: nat, h: nat) -> bool {
    &&& forall|k: int|
        0 <= k < ts.len() ==> wf_t(#[trigger] ts[k], width_at(ts, w, k as nat), h) && 1 <= width_at(ts, w, k as nat)
            <= 16384
    &&& 1 <= width_at(ts, w, ts.len()) <= 16384
}

pub proof fn lemma_width_at_push(ts: Seq<Transform>, t: Transform, w: nat, k: nat)
    requires
        k <= ts.len(),
    ensures
        width_at(ts.push(t), w, k) == width_at(ts, w, k),
    decreases k,
{
    if k > 0 {
        lemma_width_at_push(ts, t, w, (k - 1) as nat);
        assert(ts.push(t)[k - 1] == ts[k - 1]);
    }
}

pub proof fn lemma_chain_push(ts: Seq<Transform>, t: Transform, w: nat, h: nat)
    requires
        chain_ok(ts, w, h),
        wf_t(t, width_at(ts, w, ts.len()), h),
        1 <= next_w(t, width_at(ts, w, ts.len())) <= 16384,
    ensures
        chain_ok(ts.push(t), w, h),
        width_at(ts.push(t), w, ts.len() + 1) == next_w(t, width_at(ts, w, ts.len())),
{
    let nt = ts.push(t);
    lemma_width_at_push(ts, t, w, ts.len());
    assert forall|k: int| 0 <= k < nt.len() implies wf_t(#[trigger] nt[k], width_at(nt, w, k as nat), h) && 1
        <= width_at(nt, w, k as nat) <= 16384 by {
        lemma_width_at_push(ts, t, w, k as nat);
        if k < ts.len() {
            assert(nt[k] == ts[k]);
        }
    }
    assert(nt[ts.len() as int] == t);
}

/// The predictor or color transform data after its kind (§4.1, §4.2).
pub open spec fn pc_spec(b: Seq<u8>, pos: int, w: nat, h: nat) -> Option<(nat, Seq<u32>, int)> {
    match rd(b, pos, 3) {
        None => None,
        Some(x) => {
            let tb = x + 2;
            match decode_sub(b, pos + 3, subsample(w, tb), subsample(h, tb)) {
                None => None,
                Some((data, p)) => Some((tb, data, p)),
            }
        },
    }
}

pub open spec fn bundle_bits(n: nat) -> nat {
    if n > 16 {
        0
    } else if n > 4 {
        1
    } else if n > 2 {
        2
    } else {
        3
    }
}

/// The color indexing transform data after its kind (§4.4): bundling bits
/// and the expanded palette.
pub open spec fn ci_spec(b: Seq<u8>, pos: int) -> Option<(nat, Seq<u32>, int)> {
    match rd(b, pos, 8) {
        None => None,
        Some(x) => {
            let n = x + 1;
            let wb = bundle_bits(n);
            match decode_sub(b, pos + 8, n, 1) {
                None => None,
                Some((pal, p)) => Some((wb, expand(pal, pow2((8nat / pow2(wb)) as nat)), p)),
            }
        },
    }
}

pub open spec fn seen_kind(ts: Seq<Transform>, t: nat) -> bool {
    exists|j: int| 0 <= j < ts.len() && kind(#[trigger] ts[j]) == t
}

/// One step of `read_transforms`, its parts named.
pub proof fn lemma_rt_unfold(b: Seq<u8>, pos: int, w: nat, h: nat, ts: Seq<Transform>)
    ensures
        read_transforms(b, pos, w, h, ts) == match rd(b, pos, 1) {
            None => None,
            Some(more) => if more == 0 {
                Some((ts, w, pos + 1))
            } else {
                match rd(b, pos + 1, 2) {
                    None => None,
                    Some(t) => if ts.len() >= 4 || seen_kind(ts, t) {
                        None
                    } else if t == 0 || t == 1 {
                        match pc_spec(b, pos + 3, w, h) {
                            None => None,
                            Some((tb, data, p)) => read_transforms(
                                b,
                                p,
                                w,
                                h,
                                ts.push(
                                    if t == 0 {
                                        Transform::Predictor { bits: tb, w, data }
                                    } else {
                                        Transform::Color { bits: tb, w, data }
                                    },
                                ),
                            ),
                        }
                    } else if t == 2 {
                        read_transforms(b, pos + 3, w, h, ts.push(Transform::SubtractGreen))
                    } else {
                        match ci_spec(b, pos + 3) {
                            None => None,
                            Some((wb, pal, p)) => read_transforms(
                                b,
                                p,
                                subsample(w, wb),
                                h,
                                ts.push(Transform::ColorIndexing { bits: wb, w, palette: pal }),
                            ),
                        }
                    },
                }
            },
        },
{
}

/// The transform of kind `t` whose data starts at `pos`.
pub open spec fn one_spec(b: Seq<u8>, pos: int, t: nat, w: nat, h: nat) -> Option<(Transform, int)> {
    if t == 0 || t == 1 {
        match pc_spec(b, pos, w, h) {
            None => None,
            Some((tb, data, p)) => Some(
                (
                    if t == 0 {
                        Transform::Predictor { bits: tb, w, data }
                    } else {
                        Transform::Color { bits: tb, w, data }
                    },
                    p,
                ),
            ),
        }
    } else if t == 2 {
        Some((Transform::SubtractGreen, pos))
    } else {
        match ci_spec(b, pos) {
            None => None,
            Some((wb, pal, p)) => Some((Transform::ColorIndexing { bits: wb, w, palette: pal }, p)),
        }
    }
}

pub proof fn lemma_rt_unfold2(b: Seq<u8>, pos: int, w: nat, h: nat, ts: Seq<Transform>)
    ensures
        read_transforms(b, pos, w, h, ts) == match rd(b, pos, 1) {
            None => None,
            Some(more) => if more == 0 {
                Some((ts, w, pos + 1))
            } else {
                match rd(b, pos + 1, 2) {
                    None => None,
                    Some(t) => if ts.len() >= 4 || seen_kind(ts, t) {
                        None
                    } else {
                        match one_spec(b, pos + 3, t, w, h) {
                            None => None,
                            Some((x, p)) => read_transforms(b, p, next_w(x, w), h, ts.push(x)),
                        }
                    },
                }
            },
        },
{
    lemma_rt_unfold(b, pos, w, h, ts);
}

pub proof fn lemma_seen_push(ts: Seq<Transform>, x: Transform, k: nat)
    ensures
        seen_kind(ts.push(x), k) <==> (seen_kind(ts, k) || kind(x) == k),
{
    let nt = ts.push(x);
    if seen_kind(ts, k) {
        let j = choose|j: int| 0 <= j < ts.len() && kind(#[trigger] ts[j]) == k;
        assert(nt[j] == ts[j]);
    }
    if kind(x) == k {
        assert(nt[ts.len() as int] == x);
    }
    if seen_kind(nt, k) {
        let j = choose|j: int| 0 <= j < nt.len() && kind(#[trigger] nt[j]) == k;
        if j < ts.len() {
            assert(nt[j] == ts[j]);
        }
    }
}

/// The palette expanded (`spec::expand`).
fn expand_exec(pal: &Vec<u32>, size: usize) -> (r: Vec<u32>)
    requires
        size <= 256,
    ensures
        r@ == expand(pal@, size as nat),
{
    let mut out: Vec<u32> = Vec::with_capacity(size);
    let mut i: usize = 0;
    while i < size
        invariant
            i <= size,
            out@ == expand(pal@, i as nat),
        decreases size - i,
    {
        proof {
            lemma_expand_len(pal@, i as nat);
        }
        let c = if i >= pal.len() {
            0
        } else if i == 0 {
            pal[0]
        } else {
            add_px_exec(pal[i], out[i - 1])
        };
        out.push(c);
        i = i + 1;
    }
    out
}

pub proof fn lemma_expand_len(pal: Seq<u32>, n: nat)
    ensures
        expand(pal, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_expand_len(pal, (n - 1) as nat);
    }
}

/// Work charged per transform read.
pub open spec fn xform_cost(w: nat, h: nat) -> nat {
    pix_cost() * (w * h + 512) + bit_cost()
}

/// Reads a predictor or color transform's data.
fn read_pc(br: &mut BitReader, data: &[u8], w: usize, h: usize) -> (r: Result<(u32, Vec<u32>), Error>)
    requires
        old(br).ok(data@),
        1 <= w <= 16384,
        1 <= h <= 16384,
    ensures
        final(br).ok(data@),
        match pc_spec(data@, old(br).pos(), w as nat, h as nat) {
            Some((tb, d, p)) => (r matches Ok((tb2, d2)) && tb2 == tb && d2@ == d && final(br).pos() == p && 2 <= tb
                <= 9 && d.len() == subsample(w as nat, tb) * subsample(h as nat, tb)) || r == Err::<(u32, Vec<u32>), Error>(
                Error::OutOfMemory,
            ),
            None => r is Err,
        },
        r != Err::<(u32, Vec<u32>), Error>(Error::Unsupported),
        final(br).pos() >= old(br).pos(),
        final(br).work@ <= old(br).work@ + bit_cost() * (final(br).pos() - old(br).pos()) + xform_cost(
            w as nat,
            h as nat,
        ),
{
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    proof {
        lemma_bit_cost(0);
        assert(xform_cost(w as nat, h as nat) >= pix_cost() * (w * h) as nat + bit_cost()) by (nonlinear_arith)
            requires
                xform_cost(w as nat, h as nat) == pix_cost() * (w * h + 512) + bit_cost(),
        ;
        assert(pix_cost() * (w * h) as nat >= 0);
    }
    let x = match br.take(data, 3) {
        Some(v) => v,
        None => return Err(Error::Bitstream),
    };
    proof {
        verilith_core::bits::lemma_bits_bound(b, p0, 3);
        lemma2_to64();
    }
    let tb = x + 2;
    let sw = subsample_exec(w, tb);
    let sh = subsample_exec(h, tb);
    let ghost p1 = br.pos();
    let ghost w1 = br.work@;
    let d = match decode_sub_exec(br, data, sw, sh) {
        Ok(v) => v,
        Err(e) => {
            proof {
                lemma_sub_work(br.work@ as int, w1 as int, w0 as int, br.pos(), p1, p0, sw as nat, sh as nat, w as nat, h as nat);
            }
            return Err(e);
        },
    };
    proof {
        lemma_sub_work(br.work@ as int, w1 as int, w0 as int, br.pos(), p1, p0, sw as nat, sh as nat, w as nat, h as nat);
    }
    Ok((tb, d))
}

proof fn lemma_sub_work(wn: int, w1: int, w0: int, pn: int, p1: int, p0: int, sw: nat, sh: nat, w: nat, h: nat)
    requires
        sw <= w,
        sh <= h,
        wn <= w1 + bit_cost() * (pn - p1) + pix_cost() * (sw * sh) + bit_cost(),
        w1 <= w0 + refill_cost(),
        p1 >= p0 + 1,
        pn >= p1,
        bit_cost() >= 1000,
        refill_cost() == 9,
    ensures
        wn <= w0 + bit_cost() * (pn - p0) + xform_cost(w, h),
{
    assert(sw * sh <= w * h) by (nonlinear_arith)
        requires
            sw <= w,
            sh <= h,
    ;
    assert(pix_cost() * (sw * sh) <= pix_cost() * (w * h + 512)) by (nonlinear_arith)
        requires
            sw * sh <= w * h,
    ;
    assert(bit_cost() * (pn - p0) == bit_cost() * (pn - p1) + bit_cost() * (p1 - p0)) by (nonlinear_arith);
    assert(bit_cost() * (p1 - p0) >= bit_cost()) by (nonlinear_arith)
        requires
            p1 - p0 >= 1,
    ;
}

/// Reads a color indexing transform's palette; returns the bundling bits
/// and the palette expanded.
fn read_ci(br: &mut BitReader, data: &[u8]) -> (r: Result<(u32, Vec<u32>), Error>)
    requires
        old(br).ok(data@),
    ensures
        final(br).ok(data@),
        match ci_spec(data@, old(br).pos()) {
            Some((wb, pal, p)) => (r matches Ok((wb2, pal2)) && wb2 == wb && pal2@ == pal && final(br).pos() == p && wb
                <= 3 && pal.len() == pal_size(wb)) || r == Err::<(u32, Vec<u32>), Error>(Error::OutOfMemory),
            None => r is Err,
        },
        r != Err::<(u32, Vec<u32>), Error>(Error::Unsupported),
        final(br).pos() >= old(br).pos(),
        final(br).work@ <= old(br).work@ + bit_cost() * (final(br).pos() - old(br).pos()) + xform_cost(1, 1),
{
    hide(decode_sub);
    hide(expand);
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    proof {
        lemma_bit_cost(0);
    }
    let x = match br.take(data, 8) {
        Some(v) => v,
        None => return Err(Error::Bitstream),
    };
    proof {
        verilith_core::bits::lemma_bits_bound(b, p0, 8);
        lemma2_to64();
    }
    let n = (x + 1) as usize;
    let wb: u32 = if n > 16 {
        0
    } else if n > 4 {
        1
    } else if n > 2 {
        2
    } else {
        3
    };
    let ghost p1 = br.pos();
    let ghost w1 = br.work@;
    let pal = match decode_sub_exec(br, data, n, 1) {
        Ok(v) => v,
        Err(e) => {
            proof {
                lemma_pal_work(br.work@ as int, w1 as int, w0 as int, br.pos(), p1, p0, n as nat, 0);
            }
            return Err(e);
        },
    };
    let size: usize = if wb == 0 {
        256
    } else if wb == 1 {
        16
    } else if wb == 2 {
        4
    } else {
        2
    };
    proof {
        lemma_pal_size(wb, size);
    }
    let palette = expand_exec(&pal, size);
    br.work = Ghost(br.work@ + size as nat);
    proof {
        lemma_expand_len(pal@, size as nat);
        lemma_pal_work(br.work@ as int, w1 as int, w0 as int, br.pos(), p1, p0, n as nat, size as nat);
    }
    Ok((wb, palette))
}

/// The palette size for `wb` bundling bits, as `read_ci` computes it.
proof fn lemma_pal_size(wb: u32, size: usize)
    requires
        wb <= 3,
        size == if wb == 0 {
            256usize
        } else if wb == 1 {
            16usize
        } else if wb == 2 {
            4usize
        } else {
            2usize
        },
    ensures
        size == pow2((8nat / pow2(wb as nat)) as nat),
{
    lemma2_to64();
    assert(pow2(0) == 1 && pow2(1) == 2 && pow2(2) == 4 && pow2(3) == 8 && pow2(4) == 16 && pow2(8) == 256);
}

proof fn lemma_pal_work(wn: int, w1: int, w0: int, pn: int, p1: int, p0: int, n: nat, size: nat)
    requires
        n <= 256,
        size <= 256,
        wn <= w1 + bit_cost() * (pn - p1) + pix_cost() * (n * 1) + bit_cost() + size,
        w1 <= w0 + refill_cost(),
        p1 >= p0 + 8,
        pn >= p1,
        bit_cost() >= 1000,
        refill_cost() == 9,
    ensures
        wn <= w0 + bit_cost() * (pn - p0) + xform_cost(1, 1),
{
    assert(bit_cost() * (pn - p0) == bit_cost() * (pn - p1) + bit_cost() * (p1 - p0)) by (nonlinear_arith);
    assert(bit_cost() * (p1 - p0) >= bit_cost()) by (nonlinear_arith)
        requires
            p1 - p0 >= 1,
    ;
}

/// Reads the data of a transform of kind `t`; returns it and the image
/// width after it.
fn read_one(br: &mut BitReader, data: &[u8], t: u32, cw: usize, h: usize) -> (r: Result<(XForm, usize), Error>)
    requires
        old(br).ok(data@),
        t < 4,
        1 <= cw <= 16384,
        1 <= h <= 16384,
    ensures
        final(br).ok(data@),
        match one_spec(data@, old(br).pos(), t as nat, cw as nat, h as nat) {
            Some((x, p)) => (r matches Ok((v, ncw)) && tview(v) == x && final(br).pos() == p && ncw == next_w(x, cw as nat)
                && 1 <= ncw <= cw && wf_t(x, cw as nat, h as nat) && kind(x) == t) || r == Err::<(XForm, usize), Error>(
                Error::OutOfMemory,
            ),
            None => r is Err,
        },
        r != Err::<(XForm, usize), Error>(Error::Unsupported),
        final(br).pos() >= old(br).pos(),
        final(br).work@ <= old(br).work@ + bit_cost() * (final(br).pos() - old(br).pos()) + xform_cost(
            cw as nat,
            h as nat,
        ),
{
    proof {
        lemma_xc_mono(1, cw as nat, h as nat);
        assert(bit_cost() * 0 == 0);
    }
    if t == 0 || t == 1 {
        let (tb, d) = match read_pc(br, data, cw, h) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        if t == 0 {
            Ok((XForm::Predictor { bits: tb, w: cw, data: d }, cw))
        } else {
            Ok((XForm::Color { bits: tb, w: cw, data: d }, cw))
        }
    } else if t == 2 {
        Ok((XForm::SubtractGreen, cw))
    } else {
        let (wb, pal) = match read_ci(br, data) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        let ncw = subsample_exec(cw, wb);
        Ok((XForm::ColorIndexing { bits: wb, w: cw, palette: pal }, ncw))
    }
}

/// Reads the transforms (`spec::read_transforms` from no transforms):
/// returns them and the width of the image they apply to.
pub fn read_transforms_exec(br: &mut BitReader, data: &[u8], w: usize, h: usize) -> (r: Result<(Vec<XForm>, usize), Error>)
    requires
        old(br).ok(data@),
        1 <= w <= 16384,
        1 <= h <= 16384,
    ensures
        final(br).ok(data@),
        match read_transforms(data@, old(br).pos(), w as nat, h as nat, seq![]) {
            Some((ts, xw, p)) => (r matches Ok((v, xw2)) && tviews(v@) == ts && xw2 == xw && final(br).pos() == p
                && chain_ok(ts, w as nat, h as nat) && width_at(ts, w as nat, ts.len()) == xw && ts.len() <= 4) || r
                == Err::<(Vec<XForm>, usize), Error>(Error::OutOfMemory),
            None => r is Err,
        },
        r != Err::<(Vec<XForm>, usize), Error>(Error::Unsupported),
        final(br).pos() >= old(br).pos(),
        final(br).work@ <= old(br).work@ + bit_cost() * (final(br).pos() - old(br).pos()) + 4 * xform_cost(
            w as nat,
            h as nat,
        ) + bit_cost(),
{
    hide(read_transforms);
    hide(decode_sub);
    hide(xform_cost);
    hide(one_spec);
    hide(chain_ok);
    hide(tviews);
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    let ghost res = read_transforms(b, p0, w as nat, h as nat, seq![]);
    let ghost xc = xform_cost(w as nat, h as nat);
    let mut ts: Vec<XForm> = Vec::new();
    let mut seen: [bool; 4] = [false; 4];
    let mut cw = w;
    proof {
        lemma_bit_cost(0);
        reveal(tviews);
        reveal(chain_ok);
        assert(tviews(ts@) =~= seq![]);
        reveal(xform_cost);
        assert(xc >= bit_cost()) by (nonlinear_arith)
            requires
                xc == pix_cost() * (w * h + 512) + bit_cost(),
        ;
    }
    loop
        invariant
            br.ok(b),
            b == data@,
            1 <= w <= 16384,
            1 <= h <= 16384,
            p0 == old(br).pos(),
            w0 == old(br).work@,
            res == read_transforms(b, p0, w as nat, h as nat, seq![]),
            xc == xform_cost(w as nat, h as nat),
            xc >= bit_cost(),
            bit_cost() >= 1000,
            refill_cost() == 9,
            ts@.len() <= 4,
            read_transforms(b, br.pos(), cw as nat, h as nat, tviews(ts@)) == res,
            chain_ok(tviews(ts@), w as nat, h as nat),
            width_at(tviews(ts@), w as nat, ts@.len()) == cw,
            tviews(ts@).len() == ts@.len(),
            1 <= cw <= 16384,
            cw <= w,
            forall|k: int| 0 <= k < 4 ==> (seen@[k] <==> seen_kind(tviews(ts@), k as nat)),
            br.pos() >= p0,
            br.work@ <= w0 + bit_cost() * (br.pos() - p0) + ts@.len() * xc,
        decreases 4 - ts@.len(),
    {
        let ghost pos = br.pos();
        let ghost wk = br.work@;
        let ghost tv = tviews(ts@);
        proof {
            lemma_rt_unfold2(b, pos, cw as nat, h as nat, tv);
        }
        let more = match br.take(data, 1) {
            Some(v) => v,
            None => {
                proof {
                    lemma_fail_work(br.work@ as int, wk as int, w0 as int, br.pos(), pos, p0, ts@.len(), xc);
                }
                return Err(Error::Bitstream);
            },
        };
        if more == 0 {
            proof {
                lemma_step_work(br.work@ as int, wk as int, w0 as int, br.pos(), pos, p0, ts@.len(), xc, 0);
            }
            return Ok((ts, cw));
        }
        let ghost pt = br.pos();
        let t = match br.take(data, 2) {
            Some(v) => v,
            None => {
                proof {
                    lemma_fail_work(br.work@ as int, wk as int, w0 as int, br.pos(), pos, p0, ts@.len(), xc);
                }
                return Err(Error::Bitstream);
            },
        };
        proof {
            verilith_core::bits::lemma_bits_bound(b, pt, 2);
            lemma2_to64();
            lemma_step_work(br.work@ as int, wk as int, w0 as int, br.pos(), pos, p0, ts@.len(), xc, refill_cost() as int);
        }
        if ts.len() >= 4 || seen[t as usize] {
            proof {
                lemma_fail_work(br.work@ as int, br.work@ as int, w0 as int, br.pos(), br.pos(), p0, ts@.len(), xc);
            }
            return Err(Error::Bitstream);
        }
        let ghost p3 = br.pos();
        let ghost w3 = br.work@;
        proof {
            lemma_xc_mono(cw as nat, w as nat, h as nat);
        }
        let (x, ncw) = match read_one(br, data, t, cw, h) {
            Ok(v) => v,
            Err(e) => {
                proof {
                    lemma_fail_work2(br.work@ as int, w3 as int, w0 as int, br.pos(), p3, p0, ts@.len(), xc, xform_cost(cw as nat, h as nat));
                }
                return Err(e);
            },
        };
        proof {
            lemma_fail_work2(br.work@ as int, w3 as int, w0 as int, br.pos(), p3, p0, ts@.len(), xc, xform_cost(cw as nat, h as nat));
        }
        let ghost ts0 = ts@;
        ts.push(x);
        seen[t as usize] = true;
        proof {
            reveal(tviews);
            let ntv = tviews(ts@);
            assert(ntv =~= tv.push(tview(x)));
            reveal(chain_ok);
            lemma_chain_push(tv, tview(x), w as nat, h as nat);
            assert forall|k: int| 0 <= k < 4 implies (seen@[k] <==> seen_kind(ntv, k as nat)) by {
                lemma_seen_push(tv, tview(x), k as nat);
            }
            assert(br.work@ <= w0 + bit_cost() * (br.pos() - p0) + ts@.len() * xc) by (nonlinear_arith)
                requires
                    br.work@ <= w0 + bit_cost() * (br.pos() - p0) + ts0.len() * xc + xc,
                    ts@.len() == ts0.len() + 1,
            ;
        }
        cw = ncw;
    }
}

pub proof fn lemma_xc_mono(cw: nat, w: nat, h: nat)
    requires
        cw <= w,
    ensures
        xform_cost(cw, h) <= xform_cost(w, h),
{
    assert(cw * h <= w * h) by (nonlinear_arith)
        requires
            cw <= w,
    ;
    assert(pix_cost() * (cw * h + 512) <= pix_cost() * (w * h + 512)) by (nonlinear_arith)
        requires
            cw * h <= w * h,
    ;
}

/// A failed read: within this transform's charge.
proof fn lemma_fail_work(wn: int, wk: int, w0: int, pn: int, pk: int, p0: int, len: nat, xc: nat)
    requires
        wn <= wk + 2 * refill_cost(),
        wk <= w0 + bit_cost() * (pk - p0) + len * xc,
        pn >= pk,
        pk >= p0,
        len <= 4,
        xc >= bit_cost(),
        bit_cost() >= 1000,
        refill_cost() == 9,
    ensures
        wn <= w0 + bit_cost() * (pn - p0) + 4 * xc + bit_cost(),
{
    assert(bit_cost() * (pn - p0) >= bit_cost() * (pk - p0)) by (nonlinear_arith)
        requires
            pn >= pk,
            bit_cost() >= 0,
    ;
    assert(len * xc <= 4 * xc) by (nonlinear_arith)
        requires
            len <= 4,
    ;
}

/// A successful take of at least one bit pays for itself.
proof fn lemma_step_work(wn: int, wk: int, w0: int, pn: int, pk: int, p0: int, len: nat, xc: nat, extra: int)
    requires
        wn <= wk + refill_cost() + extra,
        0 <= extra <= refill_cost(),
        wk <= w0 + bit_cost() * (pk - p0) + len * xc,
        pn >= pk + 1,
        pk >= p0,
        bit_cost() >= 1000,
        refill_cost() == 9,
    ensures
        wn <= w0 + bit_cost() * (pn - p0) + len * xc,
        wn <= w0 + bit_cost() * (pn - p0) + 4 * xc + bit_cost() || len > 4,
{
    assert(bit_cost() * (pn - p0) >= bit_cost() * (pk - p0) + bit_cost()) by (nonlinear_arith)
        requires
            pn >= pk + 1,
            bit_cost() >= 0,
    ;
    if len <= 4 {
        assert(len * xc <= 4 * xc) by (nonlinear_arith)
            requires
                len <= 4,
        ;
    }
}

/// Reading a transform's data, successfully or not, within its charge.
proof fn lemma_fail_work2(wn: int, w3: int, w0: int, pn: int, p3: int, p0: int, len: nat, xc: nat, c: nat)
    requires
        wn <= w3 + bit_cost() * (pn - p3) + c,
        c <= xc,
        w3 <= w0 + bit_cost() * (p3 - p0) + len * xc,
        pn >= p3,
        p3 >= p0,
        len <= 3,
    ensures
        wn <= w0 + bit_cost() * (pn - p0) + len * xc + xc,
        wn <= w0 + bit_cost() * (pn - p0) + 4 * xc + bit_cost(),
{
    assert(bit_cost() * (pn - p0) == bit_cost() * (pn - p3) + bit_cost() * (p3 - p0)) by (nonlinear_arith);
    assert(len * xc + xc <= 4 * xc) by (nonlinear_arith)
        requires
            len <= 3,
    ;
}

} // verus!
