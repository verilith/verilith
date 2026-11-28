//! The lossless encoder: a VP8L bitstream in a RIFF container, proven to
//! decode to the input pixels (`spec::webp_decode`).
use crate::enc_bw::*;
use crate::enc_code::*;
use crate::enc_img::*;
#[cfg(verus_only)]
use crate::enc_lem::*;
use crate::enc_lz::tokenize;
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

/// The transform list: subtract green alone if `sg`, else none.
pub open spec fn tr_bits(sg: bool) -> Seq<nat> {
    if sg {
        fld(1, 1) + (fld(2, 2) + fld(0, 1))
    } else {
        fld(0, 1)
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

/// An image with at most the subtract-green transform, and without color
/// cache or meta prefix codes.
pub open spec fn plain_bits(w: nat, h: nat, a: nat, sg: bool, cls: Seq<Seq<u8>>, g: Seq<Seq<u8>>, toks: Seq<Tok>) -> Seq<nat> {
    hdr_bits(w, h, a) + (tr_bits(sg) + (fld(0, 1) + (fld(0, 1) + (gbits(cls, g, 5) + tbits(g, toks, 0)))))
}

/// `tr_bits` reads back as its transforms.
proof fn lemma_tr(b: Seq<u8>, hd: Seq<nat>, w: nat, h: nat, sg: bool, rest: Seq<nat>)
    requires
        hd.len() == 40,
        ext(b, hd + (tr_bits(sg) + rest)),
    ensures
        read_transforms(b, 40, w, h, seq![]) == Some((if sg { seq![Transform::SubtractGreen] } else { Seq::<Transform>::empty() }, w, (40 + tr_bits(sg).len()) as int)),
        tr_bits(sg).len() == if sg { 4int } else { 1int },
{
    hide(ext);
    hide(fld);
    hide(rd);
    lemma2_to64();
    let z = fld(0, 1);
    if sg {
        let f1 = fld(1, 1);
        let f2 = fld(2, 2);
        assert(hd + (tr_bits(sg) + rest) =~= hd + (f1 + (f2 + (z + rest))));
        lemma_rd(b, hd, 1, 1, f2 + (z + rest));
        assert(hd + (f1 + (f2 + (z + rest))) =~= (hd + f1) + (f2 + (z + rest)));
        lemma_rd(b, hd + f1, 2, 2, z + rest);
        assert((hd + f1) + (f2 + (z + rest)) =~= (hd + f1 + f2) + (z + rest));
        lemma_rd(b, hd + f1 + f2, 0, 1, rest);
        let ts = Seq::<Transform>::empty().push(Transform::SubtractGreen);
        assert(ts =~= seq![Transform::SubtractGreen]);
        assert(read_transforms(b, 43, w, h, ts) == Some((ts, w, 44int)));
        assert(!(exists|j: int| 0 <= j < 0 && kind(#[trigger] Seq::<Transform>::empty()[j]) == 2));
        assert(read_transforms(b, 40, w, h, seq![]) == read_transforms(b, 43, w, h, ts));
    } else {
        lemma_rd(b, hd, 0, 1, rest);
    }
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
pub proof fn lemma_plain(b: Seq<u8>, w: nat, h: nat, a: nat, sg: bool, cls: Seq<Seq<u8>>, g: Seq<Seq<u8>>, toks: Seq<Tok>)
    requires
        1 <= w <= 0x4000,
        1 <= h <= 0x4000,
        a < 2,
        b.len() >= 8,
        gfits(cls, g),
        group_ok(g),
        toks_ok(w, toks),
        forall|j: int| 0 <= j < toks.len() ==> tok_fits(g, #[trigger] toks[j]),
        play(w, toks).len() == w * h,
        ext(b, plain_bits(w, h, a, sg, cls, g, toks)),
    ensures
        vp8l_decode(b) == Some(Image { w, h, px: undo_sg(sg, play(w, toks)) }),
{
    hide(ext);
    hide(fld);
    hide(rd);
    hide(gfits);
    hide(group_ok);
    hide(decode_pixels);
    hide(read_group_codes);
    lemma_pow2_small();
    let hd = hdr_bits(w, h, a);
    let gb = gbits(cls, g, 5);
    let tb = tbits(g, toks, 0);
    let z = fld(0, 1);
    let tr = tr_bits(sg);
    assert(pad(b) == b);
    lemma_hdr(b, w, h, a, tr + (z + (z + (gb + tb))));
    lemma_tr(b, hd, w, h, sg, z + (z + (gb + tb)));
    let o: int = tr.len() as int;
    // No color cache, no meta codes.
    let u1 = hd + tr;
    assert(hd + (tr + (z + (z + (gb + tb)))) =~= u1 + (z + (z + (gb + tb))));
    lemma_rd(b, u1, 0, 1, z + (gb + tb));
    assert(read_cache_bits(b, 40 + o) == Some((0nat, 41 + o)));
    let u2 = u1 + z;
    assert(u1 + (z + (z + (gb + tb))) =~= u2 + (z + (gb + tb)));
    lemma_rd(b, u2, 0, 1, gb + tb);
    let u3 = u2 + z;
    assert(u2 + (z + (gb + tb)) =~= u3 + (gb + tb));
    assert(u3.len() == 42 + o);
    lemma_group(b, u3, cls, g, 5, tb);
    assert(g.take(5) =~= g) by {
        reveal(gfits);
    }
    let p2 = (u3.len() + gb.len()) as int;
    assert(read_groups(b, 42 + o, 0, 1) == Some((seq![g], p2))) by {
        reveal_with_fuel(read_groups, 2);
        assert(Seq::<Seq<Seq<u8>>>::empty().push(g) =~= seq![g]);
    }
    let u4 = u3 + gb;
    assert(u3 + (gb + tb) =~= u4 + (tb + Seq::<nat>::empty()));
    assert(toks.take(0) =~= Seq::<Tok>::empty());
    let cache = Seq::new(cache_size(0), |i: int| 0u32);
    lemma_toks(b, u4, w, g, toks, 0, cache, Seq::<nat>::empty());
    assert(img_of(w, play(w, toks).len(), g) == Img {
        w,
        npix: w * h,
        cb: 0,
        groups: seq![g],
        hb: 0,
        hx: 0,
        meta: seq![],
    });
    assert(decode_main(b, 40 + o, w, h) == Some((play(w, toks), (u4.len() + tb.len()) as int)));
    if sg {
        let ts = seq![Transform::SubtractGreen];
        assert(ts.drop_last() =~= Seq::<Transform>::empty());
        assert(undo_all(ts, play(w, toks), h) == undo_all(Seq::<Transform>::empty(), undo(Transform::SubtractGreen, play(w, toks), h), h));
        assert(undo_all(ts, play(w, toks), h) == undo_sg(sg, play(w, toks)));
    } else {
        assert(undo_all(Seq::<Transform>::empty(), play(w, toks), h) == play(w, toks));
    }
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
    cls: Seq<Seq<u8>>,
    g: Seq<Seq<u8>>,
    toks: Seq<Tok>,
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
        bits == plain_bits(wn, hn, a, sg, cls, g, toks),
        gfits(cls, g),
        group_ok(g),
        toks_ok(wn, toks),
        forall|j: int| 0 <= j < toks.len() ==> tok_fits(g, #[trigger] toks[j]),
        undo_sg(sg, play(wn, toks)) == px,
        play(wn, toks).len() == wn * hn,
    ensures
        webp_decode(d) == Some(Image { w: wn, h: hn, px }),
{
    hide(plain_bits);
    hide(gfits);
    hide(group_ok);
    hide(toks_ok);
    hide(tok_fits);
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
    lemma_plain(data, wn, hn, a, sg, cls, g, toks);
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
    encode_with(px, w, h, sg)
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

/// `encode_lossless`, with the subtract-green transform if `sg`.
fn encode_with(px: &[u32], w: u32, h: u32, sg: bool) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(out) ==> webp_decode(out@) == Some(Image { w: w as nat, h: h as nat, px: px@ }),
{
    hide(undo_sg);
    hide(add_green);
    hide(gfits);
    hide(group_ok);
    hide(toks_ok);
    hide(tok_fits);
    hide(play);
    hide(webp_decode);
    hide(bytes_hold);
    hide(gbits);
    hide(tbits);
    hide(lens_of);
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
            forall|j: int| 0 <= j < k ==> (#[trigger] hs@[j]).ok() && valid_code(hs@[j].lens@) && hs@[j].lens@.len()
                == alphabet(j as nat, 0),
        decreases 5 - k,
    {
        match code_for(&hist[k]) {
            Some(c) => hs.push(c),
            None => return None,
        }
        k = k + 1;
    }
    let ghost g = lens_of(hs@);
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
    let mut bw = BitWriter::new(px.len() + 1024);
    proof {
        lemma2_to64();
    }
    bw.put(0x2f, 8);
    bw.put(w - 1, 14);
    bw.put(h - 1, 14);
    bw.put(a, 1);
    bw.put(0, 3);
    if sg {
        bw.put(1, 1);
        bw.put(2, 2);
        bw.put(0, 1);
    } else {
        bw.put(0, 1);
    }
    bw.put(0, 1);
    bw.put(0, 1);
    let ghost b0 = bw.bits();
    let (ok, Ghost(cls)) = write_group(&mut bw, &hs);
    if !ok {
        return None;
    }
    if !write_toks(&mut bw, &toks, &hs) {
        return None;
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
        assert(bits =~= plain_bits(w as nat, h as nat, a as nat, sg, cls, g, toks@));
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
        assert(group_ok(g)) by {
            reveal(group_ok);
            reveal(lens_of);
            assert forall|k: int| 0 <= k < 5 implies #[trigger] g[k].len() == alphabet(k as nat, 0) && lens_ok(g[k]) by {
                assert(hs@[k].ok());
            }
        }
        lemma_file(out@, hdr, data@, d0, all, bits, w as nat, h as nat, a as nat, sg, cls, g, toks@, px@);
    }
    Some(out)
}

} // verus!
