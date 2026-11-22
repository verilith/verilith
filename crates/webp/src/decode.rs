//! The VP8L bitstream (§3, §7), proven to compute `spec::vp8l_decode`.
use crate::bitreader::*;
use crate::image::*;
use crate::pixels::*;
use crate::transform::*;
use crate::undo::*;
#[cfg(verus_only)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub proof fn lemma_unpredict_len(res: Seq<u32>, w: nat, bits: nat, data: Seq<u32>, n: nat)
    ensures
        unpredict(res, w, bits, data, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_unpredict_len(res, w, bits, data, (n - 1) as nat);
    }
}

/// Undoing a transform restores the width before it.
pub proof fn lemma_undo_len(t: Transform, px: Seq<u32>, h: nat, wk: nat)
    requires
        wf_t(t, wk, h),
        px.len() == next_w(t, wk) * h,
    ensures
        undo(t, px, h).len() == wk * h,
        t == Transform::SubtractGreen ==> undo(t, px, h) == undo(t, px, 0),
{
    if let Transform::Predictor { bits, w, data } = t {
        lemma_unpredict_len(px, w, bits, data, px.len());
    }
}

pub proof fn lemma_undo_all_step(ts: Seq<Transform>, k: nat, px: Seq<u32>, h: nat)
    requires
        1 <= k <= ts.len(),
    ensures
        undo_all(ts.subrange(0, k as int), px, h) == undo_all(ts.subrange(0, k - 1), undo(ts[k - 1], px, h), h),
{
    assert(ts.subrange(0, k as int).drop_last() =~= ts.subrange(0, k - 1));
    assert(ts.subrange(0, k as int).last() == ts[k - 1]);
}

pub proof fn lemma_chain_at(ts: Seq<Transform>, w: nat, h: nat, k: nat)
    requires
        chain_ok(ts, w, h),
        k < ts.len(),
    ensures
        wf_t(ts[k as int], width_at(ts, w, k), h),
        1 <= width_at(ts, w, k) <= 16384,
        width_at(ts, w, k + 1) == next_w(ts[k as int], width_at(ts, w, k)),
{
}

/// Transforms never widen the image.
pub proof fn lemma_width_le(ts: Seq<Transform>, w: nat, h: nat, k: nat)
    requires
        chain_ok(ts, w, h),
        k <= ts.len(),
    ensures
        width_at(ts, w, k) <= w,
    decreases k,
{
    if k > 0 {
        lemma_width_le(ts, w, h, (k - 1) as nat);
        lemma_chain_at(ts, w, h, (k - 1) as nat);
        if let Transform::ColorIndexing { bits, .. } = ts[k - 1] {
            lemma_sub_bound(width_at(ts, w, (k - 1) as nat), bits, 0);
        }
    }
}

/// Undoes the transforms (`spec::undo_all`); fails only for lack of
/// memory.
pub fn undo_all_exec(ts: &Vec<XForm>, px: Vec<u32>, Ghost(w): Ghost<nat>, h: usize) -> (r: Option<Vec<u32>>)
    requires
        1 <= h <= 16384,
        chain_ok(tviews(ts@), w, h as nat),
        px@.len() == width_at(tviews(ts@), w, ts@.len()) * h,
    ensures
        r matches Some(v) ==> v@ == undo_all(tviews(ts@), px@, h as nat) && v@.len() == w * h,
{
    hide(undo);
    hide(undo_all);
    hide(chain_ok);
    hide(width_at);
    let ghost tv = tviews(ts@);
    let ghost res = undo_all(tv, px@, h as nat);
    let mut cur = px;
    let mut k = ts.len();
    proof {
        assert(tv.subrange(0, k as int) =~= tv);
    }
    while k > 0
        invariant
            1 <= h <= 16384,
            tv == tviews(ts@),
            chain_ok(tv, w, h as nat),
            k <= ts@.len(),
            cur@.len() == width_at(tv, w, k as nat) * h,
            undo_all(tv.subrange(0, k as int), cur@, h as nat) == res,
        decreases k,
    {
        let ghost wk = width_at(tv, w, (k - 1) as nat);
        let ghost t = tv[k - 1];
        let ghost before = cur@;
        proof {
            lemma_chain_at(tv, w, h as nat, (k - 1) as nat);
            lemma_undo_all_step(tv, k as nat, before, h as nat);
            lemma_undo_len(t, before, h as nat, wk);
            assert(t == tview(ts@[k - 1]));
        }
        match &ts[k - 1] {
            XForm::Predictor { bits, w: tw, data } => {
                undo_predict(&mut cur, *tw, h, *bits, data);
            },
            XForm::Color { bits, w: tw, data } => {
                undo_color(&mut cur, *tw, h, *bits, data);
            },
            XForm::SubtractGreen => {
                undo_sg(&mut cur);
            },
            XForm::ColorIndexing { bits, w: tw, palette } => {
                cur = match undo_index(&cur, *tw, h, *bits, palette) {
                    Some(v) => v,
                    None => return None,
                };
            },
        }
        proof {
            assert(cur@ == undo(t, before, h as nat));
            assert(cur@.len() == wk * h);
        }
        k = k - 1;
    }
    proof {
        assert(tv.subrange(0, 0) =~= seq![]);
        reveal(undo_all);
        reveal(width_at);
    }
    Some(cur)
}

/// `vp8l_decode` on a bitstream already padded to 8 bytes.
pub open spec fn vp8l_bits(b: Seq<u8>) -> Option<Image> {
    match vp8l_header(b) {
        None => None,
        Some((w, h, a)) => match read_transforms(b, 40, w, h, seq![]) {
            None => None,
            Some((ts, xw, p)) => match decode_main(b, p, xw, h) {
                None => None,
                Some((px, q)) => Some(Image { w, h, px: undo_all(ts, px, h) }),
            },
        },
    }
}

/// The work charged for decoding an image `w` by `h` from `len` bytes:
/// linear in both.
pub open spec fn decode_cost(len: nat, w: nat, h: nat) -> nat {
    bit_cost() * (8 * len) + 4 * xform_cost(w, h) + pix_cost() * main_pix(w, h) + 3 * bit_cost() + 5 * refill_cost()
}

/// The image size in the header, or 1 by 1 without one.
pub open spec fn hdr_dims(b: Seq<u8>) -> (nat, nat) {
    match vp8l_header(b) {
        Some((w, h, a)) => (w, h),
        None => (1, 1),
    }
}

/// A decoded image: width, height, ARGB pixels.
pub struct Decoded {
    pub w: usize,
    pub h: usize,
    pub px: Vec<u32>,
}

/// Decodes a VP8L bitstream of at least 8 bytes (`vp8l_bits`). Also
/// returns the work done, within `decode_cost`.
pub fn vp8l_decode_bits(b: &[u8]) -> (r: (Result<Decoded, Error>, Ghost<nat>))
    requires
        b@.len() >= 8,
    ensures
        match vp8l_bits(b@) {
            Some(img) => (r.0 matches Ok(d) && d.w == img.w && d.h == img.h && d.px@ == img.px) || r.0 is Err && r.0
                == Err::<Decoded, Error>(Error::OutOfMemory),
            None => r.0 is Err,
        },
        r.0 != Err::<Decoded, Error>(Error::Unsupported),
        r.0 matches Ok(d) ==> d.px@.len() == d.w * d.h && 1 <= d.w <= 16384 && 1 <= d.h <= 16384,
        r.1@ <= decode_cost(b@.len(), hdr_dims(b@).0, hdr_dims(b@).1),
{
    hide(read_transforms);
    hide(decode_main);
    hide(undo_all);
    hide(xform_cost);
    hide(chain_ok);
    hide(tviews);
    hide(width_at);
    let ghost bb = b@;
    let mut br = BitReader::new(b);
    let sig = br.take(b, 8);
    let wm = br.take(b, 14);
    let hm = br.take(b, 14);
    let a = br.take(b, 1);
    let v = br.take(b, 3);
    proof {
        lemma_bit_cost(0);
        assert(br.work@ <= 5 * refill_cost());
        assert(decode_cost(b@.len(), hdr_dims(b@).0, hdr_dims(b@).1) >= 5 * refill_cost());
        assert(rd(bb, 0, 8) is Some && rd(bb, 8, 14) is Some && rd(bb, 22, 14) is Some && rd(bb, 36, 1) is Some && rd(
            bb,
            37,
            3,
        ) is Some);
    }
    let (sig, wm, hm, v) = match (sig, wm, hm, v) {
        (Some(s), Some(x), Some(y), Some(z)) => (s, x, y, z),
        _ => return (Err(Error::Bitstream), Ghost(br.work@)),
    };
    if sig != 0x2f || v != 0 {
        return (Err(Error::Bitstream), Ghost(br.work@));
    }
    proof {
        verilith_core::bits::lemma_bits_bound(bb, 8, 14);
        verilith_core::bits::lemma_bits_bound(bb, 22, 14);
        vstd::arithmetic::power2::lemma2_to64();
    }
    let w = (wm + 1) as usize;
    let h = (hm + 1) as usize;
    let ghost p1 = br.pos();
    let ghost w1 = br.work@;
    let (ts, xw) = match read_transforms_exec(&mut br, b, w, h) {
        Ok(x) => x,
        Err(e) => {
            proof {
                lemma_cost_bound(br.work@ as int, w1 as int, br.pos(), b@.len(), w as nat, h as nat, 0, 0);
            }
            return (Err(e), Ghost(br.work@));
        },
    };
    let ghost p2 = br.pos();
    let ghost w2 = br.work@;
    proof {
        reveal(tviews);
        reveal(chain_ok);
        lemma_width_le(tviews(ts@), w as nat, h as nat, ts@.len());
    }
    let px = match decode_main_exec(&mut br, b, xw, h) {
        Ok(x) => x,
        Err(e) => {
            proof {
                lemma_cost_bound2(br.work@ as int, w2 as int, w1 as int, br.pos(), p2, b@.len(), w as nat, h as nat, xw as nat);
            }
            return (Err(e), Ghost(br.work@));
        },
    };
    proof {
        lemma_cost_bound2(br.work@ as int, w2 as int, w1 as int, br.pos(), p2, b@.len(), w as nat, h as nat, xw as nat);
    }
    let ghost work = br.work@;
    match undo_all_exec(&ts, px, Ghost(w as nat), h) {
        Some(out) => {
            proof {
                assert(width_at(tviews(ts@), w as nat, ts@.len()) == xw);
            }
            (Ok(Decoded { w, h, px: out }), Ghost(work))
        },
        None => (Err(Error::OutOfMemory), Ghost(work)),
    }
}

/// The costs so far, within `decode_cost`.
proof fn lemma_cost_bound(wn: int, w1: int, pn: int, len: nat, w: nat, h: nat, extra: nat, p1x: int)
    requires
        1 <= w <= 16384,
        1 <= h <= 16384,
        w1 <= 5 * refill_cost(),
        wn <= w1 + bit_cost() * (pn - 40) + 4 * xform_cost(w, h) + bit_cost(),
        pn <= 8 * len,
        pn >= 40,
    ensures
        wn <= decode_cost(len, w, h),
{
    assert(bit_cost() * (pn - 40) <= bit_cost() * (8 * len)) by (nonlinear_arith)
        requires
            pn - 40 <= 8 * len,
            pn >= 40,
    ;
    assert(pix_cost() * main_pix(w, h) >= 0);
}

proof fn lemma_cost_bound2(wn: int, w2: int, w1: int, pn: int, p2: int, len: nat, w: nat, h: nat, xw: nat)
    requires
        1 <= w <= 16384,
        1 <= h <= 16384,
        1 <= xw <= w,
        w1 <= 5 * refill_cost(),
        w2 <= w1 + bit_cost() * (p2 - 40) + 4 * xform_cost(w, h) + bit_cost(),
        wn <= w2 + bit_cost() * (pn - p2) + pix_cost() * main_pix(xw, h) + 2 * bit_cost(),
        pn <= 8 * len,
        pn >= p2,
        p2 >= 40,
    ensures
        wn <= decode_cost(len, w, h),
{
    assert(bit_cost() * (pn - 40) <= bit_cost() * (8 * len)) by (nonlinear_arith)
        requires
            pn - 40 <= 8 * len,
            pn >= 40,
    ;
    assert(bit_cost() * (p2 - 40) + bit_cost() * (pn - p2) == bit_cost() * (pn - 40)) by (nonlinear_arith);
    assert(xw * h <= w * h) by (nonlinear_arith)
        requires
            xw <= w,
    ;
    assert(pix_cost() * main_pix(xw, h) <= pix_cost() * main_pix(w, h)) by (nonlinear_arith)
        requires
            xw * h <= w * h,
            main_pix(xw, h) == 3 * (xw * h),
            main_pix(w, h) == 3 * (w * h),
    ;
}

} // verus!
