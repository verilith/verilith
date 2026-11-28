//! Pixel tokens (literals and backward references) of an entropy-coded
//! image, their bits, and the proof that `spec::decode_pixels` reads them
//! back (RFC 9649 §5.2.2).
use crate::enc_bw::*;
use crate::enc_code::*;
#[cfg(verus_only)]
use crate::enc_lem::*;
#[cfg(verus_only)]
use crate::pixels::lemma_argb;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// A token: a literal pixel `v` (`len == 0`), or `len` pixels copied from
/// distance code `v`. A copy also carries its length's prefix code `lc` and
/// extra bits `lx`, and its distance code's prefix code `dc` and extra bits
/// `dx`.
#[derive(Clone, Copy)]
pub struct Tok {
    /// Copy length; 0 for a literal.
    pub len: u32,
    /// The literal pixel, or the distance code.
    pub v: u32,
    /// The length's prefix code.
    pub lc: u32,
    /// The length's extra bits.
    pub lx: u32,
    /// The distance code's prefix code.
    pub dc: u32,
    /// The distance code's extra bits.
    pub dx: u32,
}

// ---------------------------------------------------------------------------
// What tokens decode to
// ---------------------------------------------------------------------------
/// The pixels after token `t`, in an image `w` wide.
pub open spec fn step(w: nat, out: Seq<u32>, t: Tok) -> Seq<u32> {
    if t.len == 0 {
        out.push(t.v)
    } else {
        out + copy_seg(out, plane_to_dist(w, t.v as nat), t.len as nat)
    }
}

/// Token `t` can follow the pixels `out`.
pub open spec fn tok_ok(w: nat, out: Seq<u32>, t: Tok) -> bool {
    t.len != 0 ==> {
        &&& t.lc < 24
        &&& (t.lx as nat) < pow2(pfx_extra(t.lc as nat))
        &&& pfx_base(t.lc as nat) + t.lx + 1 == t.len
        &&& t.dc < 40
        &&& (t.dx as nat) < pow2(pfx_extra(t.dc as nat))
        &&& pfx_base(t.dc as nat) + t.dx + 1 == t.v
        &&& 1 <= plane_to_dist(w, t.v as nat) <= out.len()
    }
}

/// The pixels the tokens decode to.
pub open spec fn play(w: nat, toks: Seq<Tok>) -> Seq<u32>
    decreases toks.len(),
{
    if toks.len() == 0 {
        seq![]
    } else {
        step(w, play(w, toks.drop_last()), toks.last())
    }
}

pub open spec fn toks_ok(w: nat, toks: Seq<Tok>) -> bool
    decreases toks.len(),
{
    toks.len() == 0 || (toks_ok(w, toks.drop_last()) && tok_ok(w, play(w, toks.drop_last()), toks.last()))
}

// ---------------------------------------------------------------------------
// Their bits
// ---------------------------------------------------------------------------
/// The symbol of code `k` that token `t` sends, if it sends one.
pub open spec fn tsym(t: Tok, k: int) -> Option<int> {
    if t.len == 0 {
        if k == 0 {
            Some(green(t.v) as int)
        } else if k == 1 {
            Some(red(t.v) as int)
        } else if k == 2 {
            Some(blue(t.v) as int)
        } else if k == 3 {
            Some(alpha(t.v) as int)
        } else {
            None
        }
    } else {
        if k == 0 {
            Some(256 + t.lc as int)
        } else if k == 4 {
            Some(t.dc as int)
        } else {
            None
        }
    }
}

/// The five codes of a group can send symbol `s` with code `k`.
pub open spec fn sym_fits(g: Seq<Seq<u8>>, k: int, s: int) -> bool {
    &&& 0 <= s < g[k].len()
    &&& 1 <= g[k][s]
    &&& used(g[k]) == 1 ==> first_used(g[k], 0) == s
}

pub open spec fn tok_fits(g: Seq<Seq<u8>>, t: Tok) -> bool {
    forall|k: int| 0 <= k < 5 ==> (#[trigger] tsym(t, k) matches Some(s) ==> sym_fits(g, k, s))
}

/// A group of five codes for an image without a color cache.
pub open spec fn group_ok(g: Seq<Seq<u8>>) -> bool {
    &&& g.len() == 5
    &&& forall|k: int| 0 <= k < 5 ==> #[trigger] g[k].len() == alphabet(k as nat, 0)
    &&& forall|k: int| 0 <= k < 5 ==> lens_ok(#[trigger] g[k])
}

pub open spec fn tok_bits(g: Seq<Seq<u8>>, t: Tok) -> Seq<nat> {
    if t.len == 0 {
        code_of(g[0], green(t.v) as int) + (code_of(g[1], red(t.v) as int) + (code_of(g[2], blue(t.v) as int)
            + code_of(g[3], alpha(t.v) as int)))
    } else {
        code_of(g[0], 256 + t.lc as int) + (fld(t.lx as nat, pfx_extra(t.lc as nat)) + (code_of(g[4], t.dc as int)
            + fld(t.dx as nat, pfx_extra(t.dc as nat))))
    }
}

/// The bits of tokens `i..`.
pub open spec fn tbits(g: Seq<Seq<u8>>, toks: Seq<Tok>, i: int) -> Seq<nat>
    decreases toks.len() - i,
{
    if i >= toks.len() || i < 0 {
        Seq::empty()
    } else {
        tok_bits(g, toks[i]) + tbits(g, toks, i + 1)
    }
}

// ---------------------------------------------------------------------------
// Reading them back
// ---------------------------------------------------------------------------
pub proof fn lemma_argb_chans(c: u32)
    ensures
        argb(alpha(c) as nat, red(c) as nat, green(c) as nat, blue(c) as nat) == c,
{
    assert(c >> 24u32 < 256 && (c >> 16u32) & 0xffu32 < 256 && (c >> 8u32) & 0xffu32 < 256 && c & 0xffu32 < 256)
        by (bit_vector);
    lemma_argb(alpha(c), red(c), green(c), blue(c));
    assert(((c >> 24u32) << 24u32) | (((c >> 16u32) & 0xffu32) << 16u32) | (((c >> 8u32) & 0xffu32) << 8u32) | (c
        & 0xffu32) == c) by (bit_vector);
}

pub proof fn lemma_no_cache(cache: Seq<u32>, px: Seq<u32>)
    ensures
        cache_insert_all(cache, 0, px) == cache,
    decreases px.len(),
{
    if px.len() > 0 {
        lemma_no_cache(cache, px.drop_last());
    }
}

/// The image the tokens are decoded as.
pub open spec fn img_of(w: nat, npix: nat, g: Seq<Seq<u8>>) -> Img {
    Img { w, npix, cb: 0, groups: seq![g], hb: 0, hx: 0, meta: seq![] }
}

/// One token read back.
#[verifier::spinoff_prover]
proof fn lemma_tok_lit(b: Seq<u8>, u: Seq<nat>, w: nat, npix: nat, g: Seq<Seq<u8>>, out: Seq<u32>, t: Tok, cache: Seq<u32>, rest: Seq<nat>)
    requires
        group_ok(g),
        tok_ok(w, out, t),
        t.len == 0,
        tok_fits(g, t),
        out.len() < npix,
        step(w, out, t).len() <= npix,
        ext(b, u + (tok_bits(g, t) + rest)),
    ensures
        decode_pixels(b, u.len() as int, img_of(w, npix, g), out, cache) == decode_pixels(
            b,
            (u.len() + tok_bits(g, t).len()) as int,
            img_of(w, npix, g),
            step(w, out, t),
            cache,
        ),
{
    hide(ext);
    hide(code_of);
    hide(fld);
    hide(read_symbol);
    hide(rd);
    hide(lens_ok);
    hide(used);
    hide(first_used);
    hide(copy_seg);
    hide(plane_to_dist);
    let img = img_of(w, npix, g);
    assert(group_at(img, out.len()) == g);
    lemma_pow2_small();
    assert(alphabet(0, 0) == 280 && alphabet(1, 0) == 256 && alphabet(4, 0) == 40) by {
        reveal_with_fuel(cache_size, 1);
    }
    assert(tsym(t, 0) matches Some(s) ==> sym_fits(g, 0, s));
    assert(tsym(t, 4) matches Some(s) ==> sym_fits(g, 4, s));
    assert(tsym(t, 1) matches Some(s) ==> sym_fits(g, 1, s));
    assert(tsym(t, 2) matches Some(s) ==> sym_fits(g, 2, s));
    assert(tsym(t, 3) matches Some(s) ==> sym_fits(g, 3, s));
    assert(lens_ok(g[0]) && lens_ok(g[1]) && lens_ok(g[2]) && lens_ok(g[3]) && lens_ok(g[4]));
        let c = t.v;
        let (sg, sr, sb, sa) = (green(c) as int, red(c) as int, blue(c) as int, alpha(c) as int);
        assert(sg < 256 && sr < 256 && sb < 256 && sa < 256) by {
            assert(c >> 24u32 < 256 && (c >> 16u32) & 0xffu32 < 256 && (c >> 8u32) & 0xffu32 < 256 && c & 0xffu32
                < 256) by (bit_vector);
        }
        let (c0, c1, c2, c3) = (code_of(g[0], sg), code_of(g[1], sr), code_of(g[2], sb), code_of(g[3], sa));
        let u1 = u + c0;
        let u2 = u1 + c1;
        let u3 = u2 + c2;
        assert(u + (tok_bits(g, t) + rest) =~= u + (c0 + ((c1 + (c2 + c3)) + rest)));
        lemma_sym(b, u, g[0], sg, (c1 + (c2 + c3)) + rest);
        assert(u + (c0 + ((c1 + (c2 + c3)) + rest)) =~= u1 + (c1 + ((c2 + c3) + rest)));
        lemma_sym(b, u1, g[1], sr, (c2 + c3) + rest);
        assert(u1 + (c1 + ((c2 + c3) + rest)) =~= u2 + (c2 + (c3 + rest)));
        lemma_sym(b, u2, g[2], sb, c3 + rest);
        assert(u2 + (c2 + (c3 + rest)) =~= u3 + (c3 + rest));
        lemma_sym(b, u3, g[3], sa, rest);
        lemma_argb_chans(c);
        assert(tok_bits(g, t).len() == c0.len() + c1.len() + c2.len() + c3.len());
}

/// One token read back.
#[verifier::spinoff_prover]
proof fn lemma_tok_copy(b: Seq<u8>, u: Seq<nat>, w: nat, npix: nat, g: Seq<Seq<u8>>, out: Seq<u32>, t: Tok, cache: Seq<u32>, rest: Seq<nat>)
    requires
        group_ok(g),
        tok_ok(w, out, t),
        t.len != 0,
        tok_fits(g, t),
        out.len() < npix,
        step(w, out, t).len() <= npix,
        ext(b, u + (tok_bits(g, t) + rest)),
    ensures
        decode_pixels(b, u.len() as int, img_of(w, npix, g), out, cache) == decode_pixels(
            b,
            (u.len() + tok_bits(g, t).len()) as int,
            img_of(w, npix, g),
            step(w, out, t),
            cache,
        ),
{
    hide(ext);
    hide(code_of);
    hide(fld);
    hide(read_symbol);
    hide(rd);
    hide(lens_ok);
    hide(used);
    hide(first_used);
    hide(copy_seg);
    hide(plane_to_dist);
    let img = img_of(w, npix, g);
    assert(group_at(img, out.len()) == g);
    lemma_pow2_small();
    assert(alphabet(0, 0) == 280 && alphabet(1, 0) == 256 && alphabet(4, 0) == 40) by {
        reveal_with_fuel(cache_size, 1);
    }
    assert(tsym(t, 0) matches Some(s) ==> sym_fits(g, 0, s));
    assert(tsym(t, 4) matches Some(s) ==> sym_fits(g, 4, s));
    assert(tsym(t, 1) matches Some(s) ==> sym_fits(g, 1, s));
    assert(tsym(t, 2) matches Some(s) ==> sym_fits(g, 2, s));
    assert(tsym(t, 3) matches Some(s) ==> sym_fits(g, 3, s));
    assert(lens_ok(g[0]) && lens_ok(g[1]) && lens_ok(g[2]) && lens_ok(g[3]) && lens_ok(g[4]));
        let ls = t.lc as nat;
        let el = pfx_extra(ls);
        let ds = t.dc as nat;
        let ed = pfx_extra(ds);
        let c0 = code_of(g[0], 256 + ls as int);
        let f1 = fld(t.lx as nat, el);
        let c4 = code_of(g[4], ds as int);
        let f2 = fld(t.dx as nat, ed);
        let u1 = u + c0;
        let u2 = u1 + f1;
        let u3 = u2 + c4;
        assert(u + (tok_bits(g, t) + rest) =~= u + (c0 + ((f1 + (c4 + f2)) + rest)));
        lemma_sym(b, u, g[0], 256 + ls as int, (f1 + (c4 + f2)) + rest);
        assert(u + (c0 + ((f1 + (c4 + f2)) + rest)) =~= u1 + (f1 + ((c4 + f2) + rest)));
        lemma_rd(b, u1, t.lx as nat, el, (c4 + f2) + rest);
        assert(u1 + (f1 + ((c4 + f2) + rest)) =~= u2 + (c4 + (f2 + rest)));
        lemma_sym(b, u2, g[4], ds as int, f2 + rest);
        assert(u2 + (c4 + (f2 + rest)) =~= u3 + (f2 + rest));
        lemma_rd(b, u3, t.dx as nat, ed, rest);
        let d = plane_to_dist(w, t.v as nat);
        let seg = copy_seg(out, d, t.len as nat);
        lemma_no_cache(cache, seg);
        assert(seg.len() == t.len) by {
            reveal(copy_seg);
        }
        assert(step(w, out, t) == out + seg);
        assert(pfx_base(ls) + t.lx + 1 == t.len);
        assert(pfx_base(ds) + t.dx + 1 == t.v);
        assert(rd(b, u1.len() as int, el) == Some(t.lx as nat));
        assert(tok_bits(g, t).len() == c0.len() + f1.len() + c4.len() + f2.len());
        assert((256 + ls) as nat - 256 == ls);
}

/// One token read back.
#[verifier::spinoff_prover]
pub proof fn lemma_tok(b: Seq<u8>, u: Seq<nat>, w: nat, npix: nat, g: Seq<Seq<u8>>, out: Seq<u32>, t: Tok, cache: Seq<u32>, rest: Seq<nat>)
    requires
        group_ok(g),
        tok_ok(w, out, t),
        tok_fits(g, t),
        out.len() < npix,
        step(w, out, t).len() <= npix,
        ext(b, u + (tok_bits(g, t) + rest)),
    ensures
        decode_pixels(b, u.len() as int, img_of(w, npix, g), out, cache) == decode_pixels(
            b,
            (u.len() + tok_bits(g, t).len()) as int,
            img_of(w, npix, g),
            step(w, out, t),
            cache,
        ),
{
    if t.len == 0 {
        lemma_tok_lit(b, u, w, npix, g, out, t, cache, rest);
    } else {
        lemma_tok_copy(b, u, w, npix, g, out, t, cache, rest);
    }
}

proof fn lemma_play_take(w: nat, toks: Seq<Tok>, i: int)
    requires
        0 <= i < toks.len(),
    ensures
        play(w, toks.take(i + 1)) == step(w, play(w, toks.take(i)), toks[i]),
        toks_ok(w, toks.take(i + 1)) == (toks_ok(w, toks.take(i)) && tok_ok(w, play(w, toks.take(i)), toks[i])),
{
    assert(toks.take(i + 1).drop_last() =~= toks.take(i));
}

proof fn lemma_step_grows(w: nat, out: Seq<u32>, t: Tok)
    ensures
        step(w, out, t).len() > out.len(),
{
}

/// Prefixes of good tokens are good, and decode to fewer pixels.
proof fn lemma_prefix(w: nat, toks: Seq<Tok>, i: int, j: int)
    requires
        0 <= i <= j <= toks.len(),
        toks_ok(w, toks.take(j)),
    ensures
        toks_ok(w, toks.take(i)),
        play(w, toks.take(i)).len() + (j - i) <= play(w, toks.take(j)).len(),
    decreases j - i,
{
    if i < j {
        lemma_play_take(w, toks, j - 1);
        lemma_step_grows(w, play(w, toks.take(j - 1)), toks[j - 1]);
        lemma_prefix(w, toks, i, j - 1);
    }
}

/// The theorem: tokens `i..` read back.
pub proof fn lemma_toks(b: Seq<u8>, u: Seq<nat>, w: nat, g: Seq<Seq<u8>>, toks: Seq<Tok>, i: int, cache: Seq<u32>, rest: Seq<nat>)
    requires
        group_ok(g),
        toks_ok(w, toks),
        forall|j: int| 0 <= j < toks.len() ==> tok_fits(g, #[trigger] toks[j]),
        0 <= i <= toks.len(),
        ext(b, u + (tbits(g, toks, i) + rest)),
    ensures
        decode_pixels(b, u.len() as int, img_of(w, play(w, toks).len(), g), play(w, toks.take(i)), cache) == Some(
            (play(w, toks), (u.len() + tbits(g, toks, i).len()) as int),
        ),
    decreases toks.len() - i,
{
    hide(decode_pixels);
    hide(step);
    hide(tok_ok);
    hide(tok_fits);
    hide(ext);
    hide(group_ok);
    let n = toks.len() as int;
    let npix = play(w, toks).len();
    assert(toks.take(n) =~= toks);
    if i == n {
        assert(tbits(g, toks, i) =~= Seq::<nat>::empty());
        reveal_with_fuel(decode_pixels, 1);
    } else {
        let t = toks[i];
        let out = play(w, toks.take(i));
        lemma_play_take(w, toks, i);
        lemma_prefix(w, toks, i + 1, n);
        lemma_prefix(w, toks, i, i + 1);
        assert(tbits(g, toks, i) == tok_bits(g, t) + tbits(g, toks, i + 1));
        assert(u + (tbits(g, toks, i) + rest) =~= u + (tok_bits(g, t) + (tbits(g, toks, i + 1) + rest)));
        lemma_tok(b, u, w, npix, g, out, t, cache, tbits(g, toks, i + 1) + rest);
        let u1 = u + tok_bits(g, t);
        assert(u + (tok_bits(g, t) + (tbits(g, toks, i + 1) + rest)) =~= u1 + (tbits(g, toks, i + 1) + rest));
        lemma_toks(b, u1, w, g, toks, i + 1, cache, rest);
    }
}

} // verus!
