//! The lossless encoder: a VP8L bitstream in a RIFF container, proven to
//! decode to the input pixels (`spec::webp_decode`).
use crate::enc_bw::*;
use crate::enc_code::*;
use crate::enc_img::*;
#[cfg(verus_only)]
use crate::enc_lem::*;
use crate::enc_lz::tokenize;
use crate::enc_pred::{choose_modes, pow2_x, residuals};
#[cfg(verus_only)]
use crate::enc_pred::modes_fit;
use crate::enc_tok::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The bitstream
// ---------------------------------------------------------------------------
/// The header (§3.2): signature, size, alpha hint, version.
pub open spec fn hdr_bits(w: nat, h: nat, a: nat) -> Seq<nat> {
    fld(0x2f, 8) + (fld((w - 1) as nat, 14) + (fld((h - 1) as nat, 14) + (fld(a, 1) + fld(0, 3))))
}

/// An entropy-coded image as the encoder writes it: its prefix code
/// lengths `g`, sent with the code-length codes `cls`, then its tokens.
pub struct ImgCode {
    pub cls: Seq<Seq<u8>>,
    pub g: Seq<Seq<u8>>,
    pub toks: Seq<Tok>,
}

/// The image's codes and tokens, without color cache or meta codes.
pub open spec fn img_bits(c: ImgCode) -> Seq<nat> {
    gbits(c.cls, c.g, 5) + tbits(c.g, c.toks, 0)
}

/// What the readback of an `ImgCode` of width `w` needs.
pub open spec fn img_ok(w: nat, c: ImgCode) -> bool {
    &&& gfits(c.cls, c.g)
    &&& group_ok(c.g)
    &&& toks_ok(w, c.toks)
    &&& forall|j: int| 0 <= j < c.toks.len() ==> tok_fits(c.g, #[trigger] c.toks[j])
}

/// A predictor transform: block size `2^tb` and the coded mode image.
pub struct PredCode {
    pub tb: nat,
    pub c: ImgCode,
}

pub open spec fn sg_bits(sg: bool) -> Seq<nat> {
    if sg {
        fld(1, 1) + fld(2, 2)
    } else {
        Seq::empty()
    }
}

pub open spec fn pr_bits(pr: Option<PredCode>) -> Seq<nat> {
    match pr {
        None => Seq::empty(),
        Some(p) => fld(1, 1) + (fld(0, 2) + (fld((p.tb - 2) as nat, 3) + (fld(0, 1) + img_bits(p.c)))),
    }
}

/// The transform list: subtract green if `sg`, then the predictor if any.
pub open spec fn tr_bits(sg: bool, pr: Option<PredCode>) -> Seq<nat> {
    sg_bits(sg) + (pr_bits(pr) + fld(0, 1))
}

pub open spec fn pr_ok(w: nat, h: nat, pr: Option<PredCode>) -> bool {
    match pr {
        None => true,
        Some(p) => {
            &&& 2 <= p.tb <= 9
            &&& subsample(w, p.tb) >= 1
            &&& img_ok(subsample(w, p.tb), p.c)
            &&& play(subsample(w, p.tb), p.c.toks).len() == subsample(w, p.tb) * subsample(h, p.tb)
        },
    }
}

/// The transforms `tr_bits(sg, pr)` reads back as.
pub open spec fn tlist(w: nat, sg: bool, pr: Option<PredCode>) -> Seq<Transform> {
    let s = if sg {
        seq![Transform::SubtractGreen]
    } else {
        Seq::<Transform>::empty()
    };
    match pr {
        None => s,
        Some(p) => s.push(Transform::Predictor { bits: p.tb, w, data: play(subsample(w, p.tb), p.c.toks) }),
    }
}

/// The pixels decoded after undoing the transforms `tr_bits(sg)` names.
pub open spec fn undo_sg(sg: bool, p: Seq<u32>) -> Seq<u32> {
    if sg {
        Seq::new(p.len(), |i: int| add_green(p[i]))
    } else {
        p
    }
}

/// The pixels decoded after undoing the transforms `tr_bits(sg, pr)` names.
pub open spec fn undo_pl(w: nat, sg: bool, pr: Option<PredCode>, p: Seq<u32>) -> Seq<u32> {
    undo_sg(
        sg,
        match pr {
            None => p,
            Some(q) => unpredict(p, w, q.tb, play(subsample(w, q.tb), q.c.toks), p.len()),
        },
    )
}

/// An image with at most subtract green and the predictor, and without
/// color cache or meta prefix codes.
pub open spec fn plain_bits(w: nat, h: nat, a: nat, sg: bool, pr: Option<PredCode>, c: ImgCode) -> Seq<nat> {
    hdr_bits(w, h, a) + (tr_bits(sg, pr) + (fld(0, 1) + (fld(0, 1) + img_bits(c))))
}

/// `img_bits` reads back as one group of codes, then the pixels.
proof fn lemma_img(b: Seq<u8>, u: Seq<nat>, w: nat, h: nat, c: ImgCode, rest: Seq<nat>)
    requires
        img_ok(w, c),
        play(w, c.toks).len() == w * h,
        ext(b, u + (img_bits(c) + rest)),
    ensures
        read_groups(b, u.len() as int, 0, 1) == Some((seq![c.g], (u.len() + gbits(c.cls, c.g, 5).len()) as int)),
        decode_with(b, (u.len() + gbits(c.cls, c.g, 5).len()) as int, w, h, 0, seq![c.g], 0, seq![]) == Some(
            (play(w, c.toks), (u.len() + img_bits(c).len()) as int),
        ),
{
    hide(ext);
    hide(gfits);
    hide(group_ok);
    hide(decode_pixels);
    hide(read_group_codes);
    let gb = gbits(c.cls, c.g, 5);
    let tb = tbits(c.g, c.toks, 0);
    assert(u + (img_bits(c) + rest) =~= u + (gb + (tb + rest)));
    lemma_group(b, u, c.cls, c.g, 5, tb + rest);
    assert(c.g.take(5) =~= c.g) by {
        reveal(gfits);
    }
    assert(read_groups(b, u.len() as int, 0, 1) == Some((seq![c.g], (u.len() + gb.len()) as int))) by {
        reveal_with_fuel(read_groups, 2);
        assert(Seq::<Seq<Seq<u8>>>::empty().push(c.g) =~= seq![c.g]);
    }
    let u4 = u + gb;
    assert(u + (gb + (tb + rest)) =~= u4 + (tb + rest));
    assert(c.toks.take(0) =~= Seq::<Tok>::empty());
    let cache = Seq::new(cache_size(0), |i: int| 0u32);
    lemma_toks(b, u4, w, c.g, c.toks, 0, cache, rest);
    assert(img_of(w, play(w, c.toks).len(), c.g) == Img {
        w,
        npix: w * h,
        cb: 0,
        groups: seq![c.g],
        hb: 0,
        hx: 0,
        meta: seq![],
    });
}

/// A subresolution image: no color cache, then `img_bits`.
proof fn lemma_sub(b: Seq<u8>, u: Seq<nat>, w: nat, h: nat, c: ImgCode, rest: Seq<nat>)
    requires
        img_ok(w, c),
        play(w, c.toks).len() == w * h,
        ext(b, u + (fld(0, 1) + (img_bits(c) + rest))),
    ensures
        decode_sub(b, u.len() as int, w, h) == Some((play(w, c.toks), (u.len() + 1 + img_bits(c).len()) as int)),
{
    hide(ext);
    hide(fld);
    hide(rd);
    hide(img_bits);
    hide(img_ok);
    hide(decode_with);
    lemma2_to64();
    lemma_rd(b, u, 0, 1, img_bits(c) + rest);
    assert(read_cache_bits(b, u.len() as int) == Some((0nat, (u.len() + 1) as int)));
    let u1 = u + fld(0, 1);
    assert(u + (fld(0, 1) + (img_bits(c) + rest)) =~= u1 + (img_bits(c) + rest));
    lemma_img(b, u1, w, h, c, rest);
}

/// The main image: no color cache, no meta codes, then `img_bits`.
proof fn lemma_main(b: Seq<u8>, u: Seq<nat>, w: nat, h: nat, c: ImgCode, rest: Seq<nat>)
    requires
        img_ok(w, c),
        play(w, c.toks).len() == w * h,
        ext(b, u + (fld(0, 1) + (fld(0, 1) + (img_bits(c) + rest)))),
    ensures
        decode_main(b, u.len() as int, w, h) == Some((play(w, c.toks), (u.len() + 2 + img_bits(c).len()) as int)),
{
    hide(ext);
    hide(fld);
    hide(rd);
    hide(img_bits);
    hide(img_ok);
    hide(decode_with);
    lemma2_to64();
    let z = fld(0, 1);
    lemma_rd(b, u, 0, 1, z + (img_bits(c) + rest));
    assert(read_cache_bits(b, u.len() as int) == Some((0nat, (u.len() + 1) as int)));
    let u1 = u + z;
    assert(u + (z + (z + (img_bits(c) + rest))) =~= u1 + (z + (img_bits(c) + rest)));
    lemma_rd(b, u1, 0, 1, img_bits(c) + rest);
    let u2 = u1 + z;
    assert(u1 + (z + (img_bits(c) + rest)) =~= u2 + (img_bits(c) + rest));
    lemma_img(b, u2, w, h, c, rest);
}

proof fn lemma_step_end(b: Seq<u8>, u: Seq<nat>, w: nat, h: nat, ts: Seq<Transform>, rest: Seq<nat>)
    requires
        ext(b, u + (fld(0, 1) + rest)),
    ensures
        read_transforms(b, u.len() as int, w, h, ts) == Some((ts, w, (u.len() + 1) as int)),
{
    hide(ext);
    hide(fld);
    hide(rd);
    lemma2_to64();
    lemma_rd(b, u, 0, 1, rest);
}

proof fn lemma_step_sg(b: Seq<u8>, u: Seq<nat>, w: nat, h: nat, ts: Seq<Transform>, rest: Seq<nat>)
    requires
        ext(b, u + (sg_bits(true) + rest)),
        ts.len() < 4,
        forall|j: int| 0 <= j < ts.len() ==> kind(#[trigger] ts[j]) != 2,
    ensures
        read_transforms(b, u.len() as int, w, h, ts) == read_transforms(b, (u.len() + 3) as int, w, h, ts.push(Transform::SubtractGreen)),
        sg_bits(true).len() == 3,
{
    hide(ext);
    hide(fld);
    hide(rd);
    hide(decode_sub);
    hide(subsample);
    lemma2_to64();
    let f1 = fld(1, 1);
    let f2 = fld(2, 2);
    assert(u + (sg_bits(true) + rest) =~= u + (f1 + (f2 + rest)));
    lemma_rd(b, u, 1, 1, f2 + rest);
    assert(u + (f1 + (f2 + rest)) =~= (u + f1) + (f2 + rest));
    lemma_rd(b, u + f1, 2, 2, rest);
    assert(!(exists|j: int| 0 <= j < ts.len() && kind(#[trigger] ts[j]) == 2));
}

proof fn lemma_step_pr(b: Seq<u8>, u: Seq<nat>, w: nat, h: nat, ts: Seq<Transform>, p: PredCode, rest: Seq<nat>)
    requires
        ext(b, u + (pr_bits(Some(p)) + rest)),
        pr_ok(w, h, Some(p)),
        ts.len() < 4,
        forall|j: int| 0 <= j < ts.len() ==> kind(#[trigger] ts[j]) != 0,
    ensures
        read_transforms(b, u.len() as int, w, h, ts) == read_transforms(
            b,
            (u.len() + pr_bits(Some(p)).len()) as int,
            w,
            h,
            ts.push(Transform::Predictor { bits: p.tb, w, data: play(subsample(w, p.tb), p.c.toks) }),
        ),
{
    hide(ext);
    hide(fld);
    hide(rd);
    hide(img_bits);
    hide(img_ok);
    hide(decode_sub);
    lemma2_to64();
    let f1 = fld(1, 1);
    let f2 = fld(0, 2);
    let f3 = fld((p.tb - 2) as nat, 3);
    let z = fld(0, 1);
    let ib = img_bits(p.c);
    assert(u + (pr_bits(Some(p)) + rest) =~= u + (f1 + (f2 + (f3 + (z + (ib + rest))))));
    lemma_rd(b, u, 1, 1, f2 + (f3 + (z + (ib + rest))));
    let u1 = u + f1;
    assert(u + (f1 + (f2 + (f3 + (z + (ib + rest))))) =~= u1 + (f2 + (f3 + (z + (ib + rest)))));
    lemma_rd(b, u1, 0, 2, f3 + (z + (ib + rest)));
    let u2 = u1 + f2;
    assert(u1 + (f2 + (f3 + (z + (ib + rest)))) =~= u2 + (f3 + (z + (ib + rest))));
    lemma_rd(b, u2, (p.tb - 2) as nat, 3, z + (ib + rest));
    let u3 = u2 + f3;
    assert(u2 + (f3 + (z + (ib + rest))) =~= u3 + (z + (ib + rest)));
    lemma_sub(b, u3, subsample(w, p.tb), subsample(h, p.tb), p.c, rest);
    assert(!(exists|j: int| 0 <= j < ts.len() && kind(#[trigger] ts[j]) == 0));
    assert(z.len() == 1) by {
        reveal(fld);
        lemma_bits_of(0, 1);
    }
    assert(pr_bits(Some(p)) == f1 + (f2 + (f3 + (z + ib))));
    assert(pr_bits(Some(p)).len() == 7 + ib.len());
}

/// `tr_bits` reads back as its transforms.
proof fn lemma_tr(b: Seq<u8>, hd: Seq<nat>, w: nat, h: nat, sg: bool, pr: Option<PredCode>, rest: Seq<nat>)
    requires
        hd.len() == 40,
        pr_ok(w, h, pr),
        ext(b, hd + (tr_bits(sg, pr) + rest)),
    ensures
        read_transforms(b, 40, w, h, seq![]) == Some((tlist(w, sg, pr), w, (40 + tr_bits(sg, pr).len()) as int)),
{
    hide(ext);
    hide(fld);
    hide(rd);
    hide(pr_bits);
    hide(sg_bits);
    hide(pr_ok);
    hide(read_transforms);
    hide(tlist);
    hide(play);
    hide(subsample);
    hide(img_bits);
    let z = fld(0, 1);
    let sb = sg_bits(sg);
    let pb = pr_bits(pr);
    let s0 = Seq::<Transform>::empty();
    let s1 = if sg {
        seq![Transform::SubtractGreen]
    } else {
        s0
    };
    assert(hd + (tr_bits(sg, pr) + rest) =~= hd + (sb + (pb + (z + rest))));
    assert(z.len() == 1) by {
        reveal(fld);
        lemma_bits_of(0, 1);
    }
    assert(tr_bits(sg, pr).len() == sb.len() + pb.len() + 1);
    let u1 = hd + sb;
    assert(hd + (sb + (pb + (z + rest))) =~= u1 + (pb + (z + rest)));
    if sg {
        lemma_step_sg(b, hd, w, h, s0, pb + (z + rest));
        assert(s0.push(Transform::SubtractGreen) =~= s1);
    } else {
        assert(sb =~= Seq::<nat>::empty()) by {
            reveal(sg_bits);
        }
        assert(u1 =~= hd);
    }
    assert(read_transforms(b, 40, w, h, s0) == read_transforms(b, u1.len() as int, w, h, s1));
    let u2 = u1 + pb;
    assert(u1 + (pb + (z + rest)) =~= u2 + (z + rest));
    match pr {
        Some(p) => {
            assert(pb == pr_bits(Some(p)));
            assert(pr_ok(w, h, Some(p)));
            lemma_step_pr(b, u1, w, h, s1, p, z + rest);
            let s2 = s1.push(Transform::Predictor { bits: p.tb, w, data: play(subsample(w, p.tb), p.c.toks) });
            lemma_step_end(b, u2, w, h, s2, rest);
            assert(tlist(w, sg, pr) == s2) by {
                reveal(tlist);
            }
        },
        None => {
            assert(pb =~= Seq::<nat>::empty()) by {
                reveal(pr_bits);
            }
            assert(u2 =~= u1);
            lemma_step_end(b, u2, w, h, s1, rest);
            assert(tlist(w, sg, pr) == s1) by {
                reveal(tlist);
            }
        },
    }
}

proof fn lemma_undo(w: nat, h: nat, sg: bool, pr: Option<PredCode>, px: Seq<u32>)
    ensures
        undo_all(tlist(w, sg, pr), px, h) == undo_pl(w, sg, pr, px),
{
    let s0 = Seq::<Transform>::empty();
    let s1 = if sg {
        seq![Transform::SubtractGreen]
    } else {
        s0
    };
    let q = match pr {
        None => px,
        Some(p) => unpredict(px, w, p.tb, play(subsample(w, p.tb), p.c.toks), px.len()),
    };
    match pr {
        None => {},
        Some(p) => {
            let t = Transform::Predictor { bits: p.tb, w, data: play(subsample(w, p.tb), p.c.toks) };
            assert(s1.push(t).drop_last() =~= s1);
            assert(undo(t, px, h) == q);
            assert(undo_all(s1.push(t), px, h) == undo_all(s1, q, h));
        },
    }
    if sg {
        assert(s1.drop_last() =~= s0);
        assert(undo_all(s1, q, h) == undo_all(s0, undo(Transform::SubtractGreen, q, h), h));
    }
    assert(undo_all(s1, q, h) == undo_sg(sg, q));
}

proof fn lemma_hdr(b: Seq<u8>, w: nat, h: nat, a: nat, rest: Seq<nat>)
    requires
        1 <= w <= 0x4000,
        1 <= h <= 0x4000,
        a < 2,
        ext(b, hdr_bits(w, h, a) + rest),
    ensures
        vp8l_header(b) == Some((w, h, a)),
        hdr_bits(w, h, a).len() == 40,
{
    hide(ext);
    hide(fld);
    hide(rd);
    lemma2_to64();
    let e = Seq::<nat>::empty();
    let f0 = fld(0x2f, 8);
    let f1 = fld((w - 1) as nat, 14);
    let f2 = fld((h - 1) as nat, 14);
    let f3 = fld(a, 1);
    let f4 = fld(0, 3);
    assert(hdr_bits(w, h, a) + rest =~= e + (f0 + (f1 + (f2 + (f3 + (f4 + rest))))));
    lemma_rd(b, e, 0x2f, 8, f1 + (f2 + (f3 + (f4 + rest))));
    assert(e + (f0 + (f1 + (f2 + (f3 + (f4 + rest))))) =~= (e + f0) + (f1 + (f2 + (f3 + (f4 + rest)))));
    lemma_rd(b, e + f0, (w - 1) as nat, 14, f2 + (f3 + (f4 + rest)));
    assert((e + f0) + (f1 + (f2 + (f3 + (f4 + rest)))) =~= (e + f0 + f1) + (f2 + (f3 + (f4 + rest))));
    lemma_rd(b, e + f0 + f1, (h - 1) as nat, 14, f3 + (f4 + rest));
    assert((e + f0 + f1) + (f2 + (f3 + (f4 + rest))) =~= (e + f0 + f1 + f2) + (f3 + (f4 + rest)));
    lemma_rd(b, e + f0 + f1 + f2, a, 1, f4 + rest);
    assert((e + f0 + f1 + f2) + (f3 + (f4 + rest)) =~= (e + f0 + f1 + f2 + f3) + (f4 + rest));
    lemma_rd(b, e + f0 + f1 + f2 + f3, 0, 3, rest);
}

/// The theorem for the bitstream.
#[verifier::spinoff_prover]
pub proof fn lemma_plain(b: Seq<u8>, w: nat, h: nat, a: nat, sg: bool, pr: Option<PredCode>, c: ImgCode)
    requires
        1 <= w <= 0x4000,
        1 <= h <= 0x4000,
        a < 2,
        b.len() >= 8,
        img_ok(w, c),
        pr_ok(w, h, pr),
        play(w, c.toks).len() == w * h,
        ext(b, plain_bits(w, h, a, sg, pr, c)),
    ensures
        vp8l_decode(b) == Some(Image { w, h, px: undo_pl(w, sg, pr, play(w, c.toks)) }),
{
    hide(ext);
    hide(fld);
    hide(rd);
    hide(img_ok);
    hide(pr_ok);
    hide(img_bits);
    hide(tr_bits);
    hide(undo_pl);
    hide(decode_main);
    hide(read_transforms);
    hide(undo_all);
    let hd = hdr_bits(w, h, a);
    let tr = tr_bits(sg, pr);
    let z = fld(0, 1);
    let ib = img_bits(c);
    let e = Seq::<nat>::empty();
    assert(pad(b) == b);
    lemma_hdr(b, w, h, a, tr + (z + (z + ib)));
    lemma_tr(b, hd, w, h, sg, pr, z + (z + ib));
    let u1 = hd + tr;
    assert(hd + (tr + (z + (z + ib))) =~= u1 + (z + (z + (ib + e))));
    lemma_main(b, u1, w, h, c, e);
    lemma_undo(w, h, sg, pr, play(w, c.toks));
}

// ---------------------------------------------------------------------------
// The container
// ---------------------------------------------------------------------------
proof fn lemma_ext_more(b: Seq<u8>, e: Seq<u8>, w: Seq<nat>)
    requires
        ext(b, w),
    ensures
        ext(b + e, w),
{
    assert forall|k: int| 0 <= k < w.len() implies #[trigger] bit(b + e, k) == w[k] by {
        assert(bit(b, k) == w[k]);
        assert((b + e)[k / 8] == b[k / 8]);
    }
}

fn push_le32(v: &mut Vec<u8>, x: u32)
    ensures
        final(v)@.len() == old(v)@.len() + 4,
        final(v)@ == old(v)@ + seq![(x & 0xff) as u8, ((x >> 8) & 0xff) as u8, ((x >> 16) & 0xff) as u8, (x >> 24) as u8],
        x == (x & 0xff) + 256 * (((x >> 8) & 0xff) + 256 * (((x >> 16) & 0xff) + 256 * (x >> 24))),
        (x & 0xff) < 256 && ((x >> 8) & 0xff) < 256 && ((x >> 16) & 0xff) < 256 && (x >> 24) < 256,
{
    let ghost o = v@;
    v.push((x & 0xff) as u8);
    v.push(((x >> 8) & 0xff) as u8);
    v.push(((x >> 16) & 0xff) as u8);
    v.push((x >> 24) as u8);
    proof {
        assert(v@ =~= o + seq![(x & 0xff) as u8, ((x >> 8) & 0xff) as u8, ((x >> 16) & 0xff) as u8, (x >> 24) as u8]);
        assert(x == (x & 0xff) + 256 * (((x >> 8) & 0xff) + 256 * (((x >> 16) & 0xff) + 256 * (x >> 24)))) by (bit_vector);
        assert((x & 0xff) < 256 && ((x >> 8) & 0xff) < 256 && ((x >> 16) & 0xff) < 256 && (x >> 24) < 256) by (bit_vector);
    }
}

fn push4(v: &mut Vec<u8>, a: u8, b: u8, c: u8, d: u8)
    ensures
        final(v)@ == old(v)@ + seq![a, b, c, d],
{
    let ghost o = v@;
    v.push(a);
    v.push(b);
    v.push(c);
    v.push(d);
    proof {
        assert(v@ =~= o + seq![a, b, c, d]);
    }
}

/// The RIFF header before a VP8L chunk of `n` bytes.
pub open spec fn riff_hdr(d: Seq<u8>, n: nat) -> bool {
    &&& d.len() >= 20
    &&& tag(d, 0, riff_tag())
    &&& le_n(d, 4, 4) == 12 + n
    &&& tag(d, 8, webp_tag())
    &&& tag(d, 12, vp8l_tag())
    &&& le_n(d, 16, 4) == n
}

/// A VP8L chunk in a RIFF file is read from offset 20.
#[verifier::spinoff_prover]
proof fn lemma_container(d: Seq<u8>, img: Image)
    requires
        riff_hdr(d, (d.len() - 20) as nat),
        28 <= d.len() <= 0x1000_0000,
        d[20] == 0x2f,
        d[24] < 32,
        vp8l_decode(d.subrange(20, d.len() as int)) == Some(img),
        img.w <= 0x4000 && img.h <= 0x4000,
    ensures
        webp_decode(d) == Some(img),
{
    hide(vp8l_header);
    hide(skip_chunks);
    hide(le_n);
    hide(tag);
    hide(vp8l_signature);
    hide(pad);
    hide(vp8l_decode);
    let s = d.subrange(20, d.len() as int);
    let n = (d.len() - 20) as nat;
    assert(!tag(d, 12, vp8x_tag())) by {
        reveal(tag);
        assert(d.subrange(12, 16)[3] != vp8x_tag()[3]);
    }
    assert(!tag(d, 12, alph_tag())) by {
        reveal(tag);
        assert(d.subrange(12, 16)[0] != alph_tag()[0]);
    }
    assert(!tag(d, 12, vp8_tag())) by {
        reveal(tag);
        assert(d.subrange(12, 16)[3] != vp8_tag()[3]);
    }
    assert(tag(d, 12, vp8l_tag()) && tag(d, 0, riff_tag()) && tag(d, 8, webp_tag()));
    assert(le_n(d, 4, 4) == 12 + n && le_n(d, 16, 4) == n);
    assert(vp8l_header(pad(s)) is Some) by {
        reveal(vp8l_decode);
    }
    assert(vp8l_signature(d, 20)) by {
        reveal(vp8l_signature);
    }
    assert(parse_headers(d) == Parsed::Lossless(20));
}

// ---------------------------------------------------------------------------
// The encoder
// ---------------------------------------------------------------------------
/// The encoder's output decodes to its input.
#[verifier::spinoff_prover]
proof fn lemma_file(
    d: Seq<u8>,
    hdr: Seq<u8>,
    data: Seq<u8>,
    d0: Seq<u8>,
    all: Seq<nat>,
    bits: Seq<nat>,
    wn: nat,
    hn: nat,
    a: nat,
    sg: bool,
    pr: Option<PredCode>,
    c: ImgCode,
    px: Seq<u32>,
)
    requires
        1 <= wn <= 0x4000,
        1 <= hn <= 0x4000,
        a < 2,
        d == hdr + data,
        hdr.len() == 20,
        hdr.subrange(0, 4) == riff_tag(),
        hdr.subrange(8, 12) == webp_tag(),
        hdr.subrange(12, 16) == vp8l_tag(),
        hdr[4] as nat + 256 * (hdr[5] as nat + 256 * (hdr[6] as nat + 256 * hdr[7] as nat)) == 12 + data.len(),
        hdr[16] as nat + 256 * (hdr[17] as nat + 256 * (hdr[18] as nat + 256 * hdr[19] as nat)) == data.len(),
        8 <= data.len() <= 0x0fff_0000,
        data[0] == 0x2f,
        data[4] < 32,
        data == d0 || data == d0 + seq![0u8],
        bytes_hold(d0, all),
        all.len() >= bits.len(),
        all.subrange(0, bits.len() as int) == bits,
        bits == plain_bits(wn, hn, a, sg, pr, c),
        img_ok(wn, c),
        pr_ok(wn, hn, pr),
        undo_pl(wn, sg, pr, play(wn, c.toks)) == px,
        play(wn, c.toks).len() == wn * hn,
        px.len() == wn * hn,
    ensures
        webp_decode(d) == Some(Image { w: wn, h: hn, px }),
{
    hide(plain_bits);
    hide(img_ok);
    hide(pr_ok);
    hide(undo_pl);
    hide(play);
    hide(webp_decode);
    hide(vp8l_decode);
    hide(bytes_hold);
    hide(ext);
    assert(d.subrange(20, d.len() as int) =~= data);
    lemma_hold_ext(d0, all);
    assert(all =~= bits + all.subrange(bits.len() as int, all.len() as int));
    lemma_ext_prefix(d0, bits, all.subrange(bits.len() as int, all.len() as int));
    if data != d0 {
        lemma_ext_more(d0, seq![0u8], bits);
    }
    lemma_plain(data, wn, hn, a, sg, pr, c);
    assert(px.len() == wn * hn);
    assert(riff_hdr(d, (d.len() - 20) as nat)) by {
        assert(d.subrange(0, 4) =~= hdr.subrange(0, 4));
        assert(d.subrange(8, 12) =~= hdr.subrange(8, 12));
        assert(d.subrange(12, 16) =~= hdr.subrange(12, 16));
        reveal_with_fuel(le_n, 5);
        assert(le_n(d, 4, 4) == d[4] as nat + 256 * (d[5] as nat + 256 * (d[6] as nat + 256 * d[7] as nat)));
        assert(le_n(d, 16, 4) == d[16] as nat + 256 * (d[17] as nat + 256 * (d[18] as nat + 256 * d[19] as nat)));
    }
    lemma_container(d, Image { w: wn, h: hn, px });
}

/// Encodes `w * h` ARGB pixels (`0xAARRGGBB`, row by row) as a lossless
/// WebP file. `None` only if the size is out of range (1 to 16384 each way)
/// or, never seen in practice, a code does not fit.
pub fn encode_lossless(px: &[u32], w: u32, h: u32) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> webp_decode(out@) == Some(Image { w: w as nat, h: h as nat, px: px@ }),
{
    let sg = prefer_sg(px);
    // The predictor wins on photos; LZ77 alone often wins on screenshots
    // and drawings, so both are tried.
    let a = encode_with(px, w, h, sg, 4);
    let b = encode_with(px, w, h, sg, 0);
    match (a, b) {
        (Some(x), Some(y)) => if x.len() <= y.len() {
            Some(x)
        } else {
            Some(y)
        },
        (Some(x), None) => Some(x),
        (None, y) => y,
    }
}

/// `c` with green subtracted from red and blue (§4.3), undone by
/// `add_green`.
pub fn sub_green(c: u32) -> (r: u32)
    ensures
        add_green(r) == c,
{
    let a = c >> 24;
    let rr = (c >> 16) & 0xff;
    let g = (c >> 8) & 0xff;
    let b = c & 0xff;
    proof {
        assert(rr < 256 && g < 256 && b < 256) by (bit_vector)
            requires
                rr == (c >> 16) & 0xff,
                g == (c >> 8) & 0xff,
                b == c & 0xff,
        ;
    }
    let t1 = rr + 256 - g;
    let t2 = b + 256 - g;
    let r2 = t1 & 0xff;
    let b2 = t2 & 0xff;
    let r = (a << 24) | (r2 << 16) | (g << 8) | b2;
    proof {
        assert(r2 == t1 % 256 && b2 == t2 % 256 && r2 < 256 && b2 < 256) by (bit_vector)
            requires
                r2 == t1 & 0xff,
                b2 == t2 & 0xff,
        ;
        assert(alpha(r) == a && red(r) == r2 && green(r) == g && blue(r) == b2) by (bit_vector)
            requires
                a == c >> 24,
                r2 < 256,
                g < 256,
                b2 < 256,
                r == (a << 24) | (r2 << 16) | (g << 8) | b2,
        ;
        assert((r2 + g) % 256 == rr && (b2 + g) % 256 == b) by (nonlinear_arith)
            requires
                t1 == rr + 256 - g,
                t2 == b + 256 - g,
                r2 == t1 % 256,
                b2 == t2 % 256,
                rr < 256,
                g < 256,
                b < 256,
        ;
        assert(c >> 24u32 < 256 && (c >> 16u32) & 0xffu32 < 256 && (c >> 8u32) & 0xffu32 < 256 && c & 0xffu32 < 256)
            by (bit_vector);
        lemma_argb_chans(c);
    }
    r
}

/// Whether subtracting green looks like it helps: it does when red and
/// blue follow green, so that their differences from it take fewer
/// distinct values (compared on histograms of a sample of the pixels).
fn prefer_sg(px: &[u32]) -> bool {
    if px.len() > 0x1000_0000 {
        return false;
    }
    let mut h0: Vec<u32> = Vec::new();
    let mut h1: Vec<u32> = Vec::new();
    let mut k: usize = 0;
    while k < 512
        invariant
            k <= 512,
            h0@.len() == k,
            h1@.len() == k,
            forall|j: int| 0 <= j < k ==> #[trigger] h0@[j] == 0,
            forall|j: int| 0 <= j < k ==> #[trigger] h1@[j] == 0,
        decreases 512 - k,
    {
        h0.push(0);
        h1.push(0);
        k = k + 1;
    }
    let step: usize = if px.len() > 65536 {
        px.len() / 65536
    } else {
        1
    };
    let mut i: usize = 0;
    while i < px.len()
        invariant
            h0@.len() == 512,
            h1@.len() == 512,
            step >= 1,
            px.len() <= 0x1000_0000,
            i <= px.len(),
            forall|j: int| 0 <= j < 512 ==> #[trigger] h0@[j] <= i,
            forall|j: int| 0 <= j < 512 ==> #[trigger] h1@[j] <= i,
        decreases px.len() - i,
    {
        let c = px[i];
        let r = (c >> 16) & 0xff;
        let g = (c >> 8) & 0xff;
        let b = c & 0xff;
        proof {
            assert(r < 256 && g < 256 && b < 256) by (bit_vector)
                requires
                    r == (c >> 16) & 0xff,
                    g == (c >> 8) & 0xff,
                    b == c & 0xff,
            ;
        }
        let t1 = r + 256 - g;
        let t2 = b + 256 - g;
        let r2 = t1 & 0xff;
        let b2 = t2 & 0xff;
        proof {
            assert(r2 < 256 && b2 < 256) by (bit_vector)
                requires
                    r2 == t1 & 0xff,
                    b2 == t2 & 0xff,
            ;
        }
        let ir = r as usize;
        let ib = 256 + b as usize;
        let jr = r2 as usize;
        let jb = 256 + b2 as usize;
        h0.set(ir, h0[ir] + 1);
        h0.set(ib, h0[ib] + 1);
        h1.set(jr, h1[jr] + 1);
        h1.set(jb, h1[jb] + 1);
        i = if step >= px.len() - i {
            px.len()
        } else {
            i + step
        };
    }
    concentration(&h1) > concentration(&h0)
}

/// About 16 log2 `c` (0 for 0): the integer part from the top bit, the
/// next four bits as the fraction.
fn ilog16(c: u64) -> (r: u64)
    requires
        c <= 0x1000_0000,
    ensures
        r <= 16 * 28 + 15,
{
    let mut n: u64 = 0;
    let mut x = c;
    while x >= 2 && n < 28
        invariant
            n <= 28,
        decreases 28 - n,
    {
        x = x >> 1;
        n = n + 1;
    }
    let f = ((c << 4) >> n) & 15;
    assert(f <= 15) by (bit_vector)
        requires
            f == ((c << 4) >> n) & 15,
    ;
    16 * n + f
}

/// The sum of `c * log2 c` over a histogram's counts, which is larger the
/// fewer bits the values it counts take to code (for the same total).
fn concentration(h: &Vec<u32>) -> u64
    requires
        h@.len() == 512,
        forall|j: int| 0 <= j < 512 ==> #[trigger] h@[j] <= 0x1000_0000,
{
    let mut s: u64 = 0;
    let mut j: usize = 0;
    while j < 512
        invariant
            j <= 512,
            h@.len() == 512,
            forall|j: int| 0 <= j < 512 ==> #[trigger] h@[j] <= 0x1000_0000,
            s <= j * (0x1000_0000 * 463),
        decreases 512 - j,
    {
        let c = h[j] as u64;
        let l = ilog16(c);
        proof {
            assert(c * l <= 0x1000_0000 * 463) by (nonlinear_arith)
                requires
                    c <= 0x1000_0000,
                    l <= 463,
            ;
            assert(s + c * l <= (j + 1) * (0x1000_0000 * 463)) by (nonlinear_arith)
                requires
                    s <= j * (0x1000_0000 * 463),
                    c * l <= 0x1000_0000 * 463,
            ;
        }
        s = s + c * l;
        j = j + 1;
    }
    s
}

/// Every pixel with green subtracted (`sub_green`).
fn sub_green_all(px: &[u32]) -> (r: Vec<u32>)
    ensures
        undo_sg(true, r@) == px@,
{
    let mut out: Vec<u32> = Vec::with_capacity(px.len());
    let mut i: usize = 0;
    while i < px.len()
        invariant
            i <= px.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> add_green(#[trigger] out@[k]) == px@[k],
        decreases px.len() - i,
    {
        out.push(sub_green(px[i]));
        i = i + 1;
    }
    assert(undo_sg(true, out@) =~= px@);
    out
}

/// Tokenizes `src`, builds its codes and writes them and the tokens.
fn write_img(bw: &mut BitWriter, src: &[u32], w: u32) -> (r: (bool, Ghost<ImgCode>))
    requires
        old(bw).wf(),
        1 <= w,
        src@.len() <= 0x1000_0000,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        r.0 ==> final(bw).bits() == old(bw).bits() + img_bits(r.1@) && img_ok(w as nat, r.1@) && play(
            w as nat,
            r.1@.toks,
        ) == src@,
{
    hide(gfits);
    hide(group_ok);
    hide(toks_ok);
    hide(tok_fits);
    hide(play);
    hide(gbits);
    hide(tbits);
    hide(lens_of);
    let ghost none = ImgCode { cls: seq![], g: seq![], toks: seq![] };
    let toks = tokenize(src, w, 32);
    let hist = histograms(&toks);
    let mut hs: Vec<HCode> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal_with_fuel(cache_size, 1);
    }
    while k < 5
        invariant
            hist@.len() == 5,
            forall|k: int| 0 <= k < 5 ==> (#[trigger] hist@[k])@.len() == alphabet(k as nat, 0),
            alphabet(0, 0) == 280,
            k <= 5,
            hs@.len() == k,
            *bw == *old(bw),
            bw.wf(),
            bw.sent() == old(bw).sent(),
            forall|j: int| 0 <= j < k ==> (#[trigger] hs@[j]).ok() && valid_code(hs@[j].lens@) && hs@[j].lens@.len()
                == alphabet(j as nat, 0),
        decreases 5 - k,
    {
        match code_for(&hist[k]) {
            Some(c) => hs.push(c),
            None => return (false, Ghost(none)),
        }
        k = k + 1;
    }
    let ghost g = lens_of(hs@);
    let ghost b0 = bw.bits();
    let (ok, Ghost(cls)) = write_group(bw, &hs);
    if !ok {
        return (false, Ghost(none));
    }
    if !write_toks(bw, &toks, &hs) {
        return (false, Ghost(none));
    }
    let ghost c = ImgCode { cls, g, toks: toks@ };
    proof {
        assert(group_ok(g)) by {
            reveal(group_ok);
            reveal(lens_of);
            assert forall|k: int| 0 <= k < 5 implies #[trigger] g[k].len() == alphabet(k as nat, 0) && lens_ok(g[k]) by {
                assert(hs@[k].ok());
            }
        }
        assert(bw.bits() =~= b0 + img_bits(c));
    }
    (true, Ghost(c))
}

/// The transform list after the header: subtract green if `sg`, the
/// predictor with mode image `modes` if `pbits` is not 0.
#[verifier::spinoff_prover]
fn write_trs(bw: &mut BitWriter, modes: &[u32], w: u32, h: u32, sg: bool, pbits: u32) -> (r: (bool, Ghost<Option<PredCode>>))
    requires
        old(bw).wf(),
        1 <= w <= 0x4000,
        1 <= h <= 0x4000,
        pbits == 0 || 2 <= pbits <= 9,
        modes@.len() <= 0x1000_0000,
        pbits != 0 ==> modes_fit(modes@, w as nat, h as nat, pbits as nat),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        r.0 ==> {
            &&& final(bw).bits() == old(bw).bits() + sg_bits(sg) + pr_bits(r.1@)
            &&& pr_ok(w as nat, h as nat, r.1@)
            &&& match r.1@ {
                None => pbits == 0,
                Some(p) => p.tb == pbits && play(subsample(w as nat, p.tb), p.c.toks) == modes@,
            }
        },
{
    hide(img_ok);
    hide(img_bits);
    hide(play);
    hide(pr_bits);
    hide(sg_bits);
    hide(pr_ok);
    hide(subsample);
    hide(modes_fit);
    proof {
        lemma2_to64();
    }
    let wu = w as usize;
    let pr_on = pbits != 0;
    let ghost bh = bw.bits();
    if sg {
        bw.put(1, 1);
        bw.put(2, 2);
    }
    let ghost bs = bw.bits();
    proof {
        reveal(sg_bits);
        assert(bs =~= bh + sg_bits(sg));
    }
    let ghost mut pr: Option<PredCode> = None;
    if pr_on {
        let pb = pow2_x(pbits);
        let sw = (wu + pb - 1) / pb;
        if sw == 0 {
            return (false, Ghost(None));
        }
        bw.put(1, 1);
        bw.put(0, 2);
        bw.put(pbits - 2, 3);
        bw.put(0, 1);
        let (ok, Ghost(pc)) = write_img(bw, modes, sw as u32);
        if !ok {
            return (false, Ghost(None));
        }
        proof {
            pr = Some(PredCode { tb: pbits as nat, c: pc });
            assert(sw as nat == subsample(w as nat, pbits as nat)) by {
                reveal(subsample);
            }
            assert(bw.bits() =~= bs + pr_bits(pr)) by {
                reveal(pr_bits);
            }
            assert(pr_ok(w as nat, h as nat, pr)) by {
                reveal(pr_ok);
                reveal(modes_fit);
            }
        }
    } else {
        proof {
            assert(bw.bits() =~= bs + pr_bits(pr)) by {
                reveal(pr_bits);
            }
            assert(pr_ok(w as nat, h as nat, pr)) by {
                reveal(pr_ok);
            }
        }
    }
    proof {
        assert(bw.bits() =~= bh + sg_bits(sg) + pr_bits(pr));
    }
    (true, Ghost(pr))
}

/// The VP8L bitstream for `main` (and the mode image `modes` if
/// `pbits` is not 0), still in the bit writer.
#[verifier::spinoff_prover]
fn stream(main: &[u32], modes: &[u32], w: u32, h: u32, a: u32, sg: bool, pbits: u32) -> (r: Option<
    (BitWriter, Ghost<Option<PredCode>>, Ghost<ImgCode>),
>)
    requires
        1 <= w <= 0x4000,
        1 <= h <= 0x4000,
        a < 2,
        pbits == 0 || 2 <= pbits <= 9,
        main@.len() <= 0x1000_0000,
        modes@.len() <= 0x1000_0000,
        pbits != 0 ==> modes_fit(modes@, w as nat, h as nat, pbits as nat),
    ensures
        r matches Some((bw, pr, mc)) ==> {
            &&& bw.wf()
            &&& bw.sent() == Seq::<u8>::empty()
            &&& bw.bits() == plain_bits(w as nat, h as nat, a as nat, sg, pr@, mc@)
            &&& img_ok(w as nat, mc@)
            &&& play(w as nat, mc@.toks) == main@
            &&& pr_ok(w as nat, h as nat, pr@)
            &&& match pr@ {
                None => pbits == 0,
                Some(p) => p.tb == pbits && play(subsample(w as nat, p.tb), p.c.toks) == modes@,
            }
        },
{
    hide(img_ok);
    hide(img_bits);
    hide(play);
    hide(plain_bits);
    hide(pr_bits);
    hide(sg_bits);
    hide(hdr_bits);
    hide(tr_bits);
    hide(pr_ok);
    hide(subsample);
    hide(modes_fit);
    let wu = w as usize;
    let pr_on = pbits != 0;
    let mut bw = BitWriter::new(main.len() + 1024);
    proof {
        lemma2_to64();
    }
    bw.put(0x2f, 8);
    bw.put(w - 1, 14);
    bw.put(h - 1, 14);
    bw.put(a, 1);
    bw.put(0, 3);
    let ghost bh = bw.bits();
    proof {
        reveal(hdr_bits);
        assert(bh =~= hdr_bits(w as nat, h as nat, a as nat));
    }
    let (ok, Ghost(pr)) = write_trs(&mut bw, modes, w, h, sg, pbits);
    if !ok {
        return None;
    }
    let ghost bp = bw.bits();
    proof {
        assert(bp == hdr_bits(w as nat, h as nat, a as nat) + sg_bits(sg) + pr_bits(pr));
    }
    bw.put(0, 1);
    bw.put(0, 1);
    bw.put(0, 1);
    let (ok, Ghost(mc)) = write_img(&mut bw, main, w);
    if !ok {
        return None;
    }
    proof {
        let z = fld(0, 1);
        let ib = img_bits(mc);
        assert(bw.bits() =~= bp + z + z + z + ib);
        reveal(plain_bits);
        reveal(tr_bits);
        assert(bp + z + z + z + ib =~= hdr_bits(w as nat, h as nat, a as nat) + (tr_bits(sg, pr) + (z + (z + ib))));
    }
    Some((bw, Ghost(pr), Ghost(mc)))
}

/// `encode_lossless`, with the subtract-green transform if `sg` and the
/// predictor transform with `2^pbits` blocks unless `pbits` is 0.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn encode_with(px: &[u32], w: u32, h: u32, sg: bool, pbits: u32) -> (r: Option<Vec<u8>>)
    requires
        pbits == 0 || 2 <= pbits <= 9,
    ensures
        r matches Some(out) ==> webp_decode(out@) == Some(Image { w: w as nat, h: h as nat, px: px@ }),
{
    hide(undo_sg);
    hide(add_green);
    hide(img_ok);
    hide(img_bits);
    hide(play);
    hide(webp_decode);
    hide(bytes_hold);
    hide(unpredict);
    if w == 0 || h == 0 || w > 0x4000 || h > 0x4000 {
        return None;
    }
    assert((w as nat) * (h as nat) <= 0x1000_0000) by (nonlinear_arith)
        requires
            w <= 0x4000,
            h <= 0x4000,
    ;
    if px.len() as u64 != (w as u64) * (h as u64) {
        return None;
    }
    let sgv: Vec<u32> = if sg {
        sub_green_all(px)
    } else {
        Vec::new()
    };
    let src: &[u32] = if sg {
        sgv.as_slice()
    } else {
        px
    };
    assert(undo_sg(sg, src@) == px@ && src@.len() == px@.len()) by {
        reveal(undo_sg);
    }
    let wu = w as usize;
    let hu = h as usize;
    let pr_on = pbits != 0;
    let modes: Vec<u32> = if pr_on {
        choose_modes(src, wu, hu, pbits)
    } else {
        Vec::new()
    };
    let resv: Vec<u32> = if pr_on {
        residuals(src, wu, hu, pbits, modes.as_slice())
    } else {
        Vec::new()
    };
    let main: &[u32] = if pr_on {
        resv.as_slice()
    } else {
        src
    };
    assert(main@.len() == src@.len());
    if modes.len() > 0x1000_0000 {
        return None;
    }
    // Alpha hint: whether any pixel is not opaque.
    let mut a: u32 = 0;
    let mut i: usize = 0;
    while i < px.len()
        invariant
            a < 2,
        decreases px.len() - i,
    {
        if px[i] < 0xff00_0000 {
            a = 1;
        }
        i = i + 1;
    }
    let (mut bw, Ghost(pr), Ghost(mc)) = match stream(main, modes.as_slice(), w, h, a, sg, pbits) {
        Some(t) => t,
        None => return None,
    };
    proof {
        assert(pr_ok(w as nat, h as nat, pr));
        assert(undo_pl(w as nat, sg, pr, play(w as nat, mc.toks)) == px@);
    }
    let ghost bits = bw.bits();
    let (mut data, Ghost(all)) = bw.finish();
    proof {
        assert(bw.sent() == Seq::<u8>::empty());
        assert(Seq::<u8>::empty() + data@ =~= data@);
    }
    let ghost d0 = data@;
    if data.len() % 2 == 1 {
        data.push(0);
        proof {
            assert(data@ =~= d0 + seq![0u8]);
        }
    }
    let n = data.len();
    if n < 8 || n > 0x0fff_0000 || data[0] != 0x2f || data[4] >= 32 {
        return None;
    }
    let mut out: Vec<u8> = Vec::with_capacity(n + 20);
    push4(&mut out, 0x52, 0x49, 0x46, 0x46);
    push_le32(&mut out, 12 + n as u32);
    push4(&mut out, 0x57, 0x45, 0x42, 0x50);
    push4(&mut out, 0x56, 0x50, 0x38, 0x4c);
    push_le32(&mut out, n as u32);
    let ghost hdr = out@;
    proof {
        assert(hdr + data@.subrange(0, 0) =~= hdr);
        assert(hdr.subrange(0, 4) =~= riff_tag());
        assert(hdr.subrange(8, 12) =~= webp_tag());
        assert(hdr.subrange(12, 16) =~= vp8l_tag());
    }
    let mut j: usize = 0;
    while j < n
        invariant
            n == data@.len(),
            j <= n,
            out@ == hdr + data@.subrange(0, j as int),
        decreases n - j,
    {
        out.push(data[j]);
        proof {
            assert(out@ =~= hdr + data@.subrange(0, j + 1));
        }
        j = j + 1;
    }
    proof {
        assert(data@.subrange(0, n as int) =~= data@);
    }
    proof {
        lemma_file(out@, hdr, data@, d0, all, bits, w as nat, h as nat, a as nat, sg, pr, mc, px@);
    }
    Some(out)
}

} // verus!
