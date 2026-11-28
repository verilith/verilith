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

/// An image without transforms, color cache or meta prefix codes.
pub open spec fn plain_bits(w: nat, h: nat, a: nat, cls: Seq<Seq<u8>>, g: Seq<Seq<u8>>, toks: Seq<Tok>) -> Seq<nat> {
    hdr_bits(w, h, a) + (fld(0, 1) + (fld(0, 1) + (fld(0, 1) + (gbits(cls, g, 5) + tbits(g, toks, 0)))))
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
pub proof fn lemma_plain(b: Seq<u8>, w: nat, h: nat, a: nat, cls: Seq<Seq<u8>>, g: Seq<Seq<u8>>, toks: Seq<Tok>)
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
        ext(b, plain_bits(w, h, a, cls, g, toks)),
    ensures
        vp8l_decode(b) == Some(Image { w, h, px: play(w, toks) }),
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
    assert(pad(b) == b);
    lemma_hdr(b, w, h, a, z + (z + (z + (gb + tb))));
    // No transforms.
    lemma_rd(b, hd, 0, 1, z + (z + (gb + tb)));
    assert(read_transforms(b, 40, w, h, seq![]) == Some((Seq::<Transform>::empty(), w, 41int)));
    // No color cache, no meta codes.
    let u1 = hd + z;
    assert(hd + (z + (z + (z + (gb + tb)))) =~= u1 + (z + (z + (gb + tb))));
    lemma_rd(b, u1, 0, 1, z + (gb + tb));
    assert(read_cache_bits(b, 41) == Some((0nat, 42int)));
    let u2 = u1 + z;
    assert(u1 + (z + (z + (gb + tb))) =~= u2 + (z + (gb + tb)));
    lemma_rd(b, u2, 0, 1, gb + tb);
    let u3 = u2 + z;
    assert(u2 + (z + (gb + tb)) =~= u3 + (gb + tb));
    assert(u3.len() == 43);
    lemma_group(b, u3, cls, g, 5, tb);
    assert(g.take(5) =~= g) by {
        reveal(gfits);
    }
    let p2 = (u3.len() + gb.len()) as int;
    assert(read_groups(b, 43, 0, 1) == Some((seq![g], p2))) by {
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
    assert(decode_main(b, 41, w, h) == Some((play(w, toks), (u4.len() + tb.len()) as int)));
    assert(undo_all(Seq::<Transform>::empty(), play(w, toks), h) == play(w, toks));
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
        bits == plain_bits(wn, hn, a, cls, g, toks),
        gfits(cls, g),
        group_ok(g),
        toks_ok(wn, toks),
        forall|j: int| 0 <= j < toks.len() ==> tok_fits(g, #[trigger] toks[j]),
        play(wn, toks) == px,
        px.len() == wn * hn,
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
    lemma_plain(data, wn, hn, a, cls, g, toks);
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
    let toks = tokenize(px, w, 32);
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
    bw.put(0, 1);
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
        assert(bits =~= plain_bits(w as nat, h as nat, a as nat, cls, g, toks@));
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
        lemma_file(out@, hdr, data@, d0, all, bits, w as nat, h as nat, a as nat, cls, g, toks@, px@);
    }
    Some(out)
}

} // verus!
