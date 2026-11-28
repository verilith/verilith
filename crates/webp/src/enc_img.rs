//! Writing an entropy-coded image without color cache or meta prefix codes:
//! its five prefix codes and its tokens, proven to read back under
//! `spec::read_group_codes` and `spec::decode_with`.
use crate::codes::CL_ORDER;
#[cfg(verus_only)]
use crate::codes::lemma_cl_order;
use crate::enc_bw::*;
use crate::enc_code::*;
use crate::enc_hl::huff_lens;
#[cfg(verus_only)]
use crate::enc_lem::*;
#[cfg(verus_only)]
use crate::enc_llc::*;
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
// One code
// ---------------------------------------------------------------------------
/// Writes the code lengths of `h` as a normal code (`enc_llc::normal_bits`).
/// Returns false, having written nothing useful, if the code length code
/// does not fit (never seen in practice).
pub fn write_code(bw: &mut BitWriter, h: &HCode) -> (r: (bool, Ghost<Seq<u8>>))
    requires
        old(bw).wf(),
        h.ok(),
        valid_code(h.lens@),
        1 <= h.lens@.len() <= 1024,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        r.0 ==> final(bw).bits() == old(bw).bits() + normal_bits(r.1@, h.lens@) && cl_fits(r.1@, h.lens@),
{
    let n = h.lens.len();
    let ghost lens = h.lens@;
    // Histogram of the lengths.
    let mut cf: Vec<u32> = vec![0u32; 19];
    let mut i: usize = 0;
    while i < n
        invariant
            n == lens.len(),
            lens == h.lens@,
            n <= 1024,
            h.ok(),
            i <= n,
            cf@.len() == 19,
            forall|s: int| 0 <= s < 19 ==> #[trigger] cf@[s] <= i,
            bw.wf(),
            bw.bits() == old(bw).bits(),
            bw.sent() == old(bw).sent(),
        decreases n - i,
    {
        let l = h.lens[i] as usize;
        assert(lens[i as int] as nat <= MAX_BITS);
        cf.set(l, cf[l] + 1);
        i = i + 1;
    }
    let cl = huff_lens(cf.as_slice(), 7);
    let mut s: usize = 0;
    while s < 19
        invariant
            cl@.len() == 19,
            s <= 19,
            bw.wf(),
            bw.bits() == old(bw).bits(),
            bw.sent() == old(bw).sent(),
            forall|t: int| 0 <= t < s ==> #[trigger] cl@[t] < 8,
        decreases 19 - s,
    {
        if cl[s] >= 8 {
            return (false, Ghost(Seq::empty()));
        }
        s = s + 1;
    }
    let ghost clv = cl@;
    let clh = match make_code(cl) {
        Some(c) => c,
        None => return (false, Ghost(Seq::empty())),
    };
    assert(clh.lens@ == clv);
    // Every length has a code.
    let mut i: usize = 0;
    while i < n
        invariant
            n == lens.len(),
            lens == h.lens@,
            h.ok(),
            clh.ok(),
            clh.lens@ == clv,
            clv.len() == 19,
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] lens[j] < 16 && 1 <= clv[lens[j] as int],
            clh.nused == 1 ==> forall|j: int| 0 <= j < i ==> #[trigger] lens[j] as int == first_used(clv, 0),
            bw.wf(),
            bw.bits() == old(bw).bits(),
            bw.sent() == old(bw).sent(),
        decreases n - i,
    {
        let l = h.lens[i] as usize;
        assert(lens[i as int] as nat <= MAX_BITS);
        if clh.lens[l] == 0 {
            return (false, Ghost(Seq::empty()));
        }
        if clh.nused == 1 && l != clh.one {
            return (false, Ghost(Seq::empty()));
        }
        i = i + 1;
    }
    // The bits.
    let ghost b0 = bw.bits();
    proof {
        lemma_pow2_small();
        lemma_cl_order();
    }
    bw.put(0, 1);
    bw.put(15, 4);
    let ghost b1 = bw.bits();
    let mut k: usize = 0;
    while k < 19
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            clh.lens@ == clv,
            clv.len() == 19,
            forall|t: int| 0 <= t < 19 ==> #[trigger] clv[t] < 8,
            forall|i: int| 0 <= i < 19 ==> #[trigger] CL_ORDER@[i] as nat == cl_order()[i],
            forall|i: int| 0 <= i < 19 ==> #[trigger] cl_order()[i] < 19,
            k <= 19,
            bw.bits() == b1 + cl_fields(clv, k as int),
            pow2(3) == 8,
        decreases 19 - k,
    {
        let o = CL_ORDER[k] as usize;
        let v = clh.lens[o] as u32;
        bw.put(v, 3);
        proof {
            assert(cl_fields(clv, k + 1) == cl_fields(clv, k as int) + fld(clv[o as int] as nat, 3));
            assert(bw.bits() =~= b1 + cl_fields(clv, k + 1));
        }
        k = k + 1;
    }
    bw.put(0, 1);
    let ghost b2 = bw.bits();
    let mut i: usize = 0;
    while i < n
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            n == lens.len(),
            lens == h.lens@,
            clh.ok(),
            clh.lens@ == clv,
            clv.len() == 19,
            forall|j: int| 0 <= j < n ==> #[trigger] lens[j] < 16 && 1 <= clv[lens[j] as int],
            clh.nused == 1 ==> forall|j: int| 0 <= j < n ==> #[trigger] lens[j] as int == first_used(clv, 0),
            i <= n,
            bw.bits() == b2 + lens_syms(clv, lens, i as int),
        decreases n - i,
    {
        let l = h.lens[i] as usize;
        assert(lens[i as int] < 16 && 1 <= clv[lens[i as int] as int]);
        let (c, nb) = clh.sym(l);
        bw.put64(c, nb);
        proof {
            assert(lens_syms(clv, lens, i + 1) == lens_syms(clv, lens, i as int) + code_of(clv, lens[i as int] as int));
            assert(bw.bits() =~= b2 + lens_syms(clv, lens, i + 1));
        }
        i = i + 1;
    }
    proof {
        assert(bw.bits() =~= b0 + normal_bits(clv, lens));
    }
    (true, Ghost(clv))
}

// ---------------------------------------------------------------------------
// A group of five codes
// ---------------------------------------------------------------------------
/// The bits of the first `j` codes of a group.
pub open spec fn gbits(cls: Seq<Seq<u8>>, g: Seq<Seq<u8>>, j: int) -> Seq<nat>
    decreases j,
{
    if j <= 0 {
        Seq::empty()
    } else {
        gbits(cls, g, j - 1) + normal_bits(cls[j - 1], g[j - 1])
    }
}

pub open spec fn gfits(cls: Seq<Seq<u8>>, g: Seq<Seq<u8>>) -> bool {
    &&& cls.len() == 5
    &&& g.len() == 5
    &&& forall|k: int| 0 <= k < 5 ==> cl_fits(#[trigger] cls[k], g[k]) && g[k].len() == alphabet(k as nat, 0)
}

/// The first `j` codes read back.
pub proof fn lemma_group(b: Seq<u8>, u: Seq<nat>, cls: Seq<Seq<u8>>, g: Seq<Seq<u8>>, j: int, rest: Seq<nat>)
    requires
        gfits(cls, g),
        0 <= j <= 5,
        ext(b, u + (gbits(cls, g, j) + rest)),
    ensures
        read_group_codes(b, u.len() as int, 0, j as nat) == Some((g.take(j), (u.len() + gbits(cls, g, j).len()) as int)),
    decreases j,
{
    hide(read_code);
    hide(normal_bits);
    hide(cl_fits);
    hide(ext);
    if j == 0 {
        assert(g.take(0) =~= seq![]);
    } else {
        let nb = normal_bits(cls[j - 1], g[j - 1]);
        assert(u + (gbits(cls, g, j) + rest) =~= u + (gbits(cls, g, j - 1) + (nb + rest)));
        lemma_group(b, u, cls, g, j - 1, nb + rest);
        let u1 = u + gbits(cls, g, j - 1);
        assert(u + (gbits(cls, g, j - 1) + (nb + rest)) =~= u1 + (nb + rest));
        assert(cl_fits(cls[j - 1], g[j - 1]));
        lemma_normal(b, u1, cls[j - 1], g[j - 1], rest);
        assert(g.take(j - 1).push(g[j - 1]) =~= g.take(j));
        assert(read_group_codes(b, u.len() as int, 0, j as nat) == match read_group_codes(b, u.len() as int, 0, (j - 1) as nat) {
            None => None,
            Some((cs, p)) => match read_code(b, p, alphabet((j - 1) as nat, 0)) {
                None => None,
                Some((lens, q)) => Some((cs.push(lens), q)),
            },
        });
    }
}

/// The lengths of a group's codes.
pub open spec fn lens_of(hs: Seq<HCode>) -> Seq<Seq<u8>> {
    Seq::new(hs.len(), |k: int| hs[k].lens@)
}

/// Writes the five codes of a group.
pub fn write_group(bw: &mut BitWriter, hs: &Vec<HCode>) -> (r: (bool, Ghost<Seq<Seq<u8>>>))
    requires
        old(bw).wf(),
        hs@.len() == 5,
        forall|k: int| 0 <= k < 5 ==> (#[trigger] hs@[k]).ok() && valid_code(hs@[k].lens@) && hs@[k].lens@.len()
            == alphabet(k as nat, 0),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        r.0 ==> final(bw).bits() == old(bw).bits() + gbits(r.1@, lens_of(hs@), 5) && gfits(r.1@, lens_of(hs@)),
{
    let ghost g = lens_of(hs@);
    let ghost b0 = bw.bits();
    let ghost mut cls: Seq<Seq<u8>> = Seq::empty();
    proof {
        reveal_with_fuel(cache_size, 1);
    }
    let mut k: usize = 0;
    while k < 5
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            hs@.len() == 5,
            g == lens_of(hs@),
            forall|k: int| 0 <= k < 5 ==> (#[trigger] hs@[k]).ok() && valid_code(hs@[k].lens@) && hs@[k].lens@.len()
                == alphabet(k as nat, 0),
            alphabet(0, 0) == 280,
            k <= 5,
            cls.len() == k,
            forall|j: int| 0 <= j < k ==> cl_fits(#[trigger] cls[j], g[j]),
            bw.bits() == b0 + gbits(cls, g, k as int),
        decreases 5 - k,
    {
        let (ok, Ghost(cl)) = write_code(bw, &hs[k]);
        if !ok {
            return (false, Ghost(Seq::empty()));
        }
        proof {
            let c2 = cls.push(cl);
            assert(gbits(c2, g, k as int) == gbits(cls, g, k as int)) by {
                lemma_gbits_ext(cls, c2, g, k as int);
            }
            assert(gbits(c2, g, k + 1) == gbits(c2, g, k as int) + normal_bits(cl, g[k as int]));
            assert(bw.bits() =~= b0 + gbits(c2, g, k + 1));
            cls = c2;
        }
        k = k + 1;
    }
    (true, Ghost(cls))
}

proof fn lemma_gbits_ext(a: Seq<Seq<u8>>, c: Seq<Seq<u8>>, g: Seq<Seq<u8>>, j: int)
    requires
        0 <= j <= a.len(),
        j <= c.len(),
        forall|i: int| 0 <= i < j ==> a[i] == c[i],
    ensures
        gbits(c, g, j) == gbits(a, g, j),
    decreases j,
{
    if j > 0 {
        lemma_gbits_ext(a, c, g, j - 1);
    }
}

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------
/// The symbol of code `k` a token sends.
#[inline(always)]
fn put_sym(bw: &mut BitWriter, h: &HCode, s: usize, Ghost(g): Ghost<Seq<Seq<u8>>>, Ghost(k): Ghost<int>) -> (r: bool)
    requires
        old(bw).wf(),
        h.ok(),
        0 <= k < g.len(),
        g[k] == h.lens@,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        r ==> sym_fits(g, k, s as int) && final(bw).bits() == old(bw).bits() + code_of(h.lens@, s as int),
{
    if s >= h.lens.len() || h.lens[s] == 0 || (h.nused == 1 && s != h.one) {
        return false;
    }
    let (c, n) = h.sym(s);
    bw.put64(c, n);
    true
}

/// Writes one token.
fn put_tok(bw: &mut BitWriter, t: Tok, hs: &Vec<HCode>, Ghost(g): Ghost<Seq<Seq<u8>>>) -> (r: bool)
    requires
        old(bw).wf(),
        hs@.len() == 5,
        forall|k: int| 0 <= k < 5 ==> (#[trigger] hs@[k]).ok(),
        g == lens_of(hs@),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        r ==> final(bw).bits() == old(bw).bits() + tok_bits(g, t) && tok_fits(g, t),
{
    proof {
        lemma_pow2_small();
    }
    let ghost w0 = bw.bits();
    assert(g[0] == hs@[0].lens@ && g[1] == hs@[1].lens@ && g[2] == hs@[2].lens@ && g[3] == hs@[3].lens@
        && g[4] == hs@[4].lens@);
    if t.len == 0 {
        let c = t.v;
        let (a, r, gr, b) = crate::pxops::chans(c);
        if !put_sym(bw, &hs[0], gr as usize, Ghost(g), Ghost(0)) {
            return false;
        }
        if !put_sym(bw, &hs[1], r as usize, Ghost(g), Ghost(1)) {
            return false;
        }
        if !put_sym(bw, &hs[2], b as usize, Ghost(g), Ghost(2)) {
            return false;
        }
        if !put_sym(bw, &hs[3], a as usize, Ghost(g), Ghost(3)) {
            return false;
        }
        proof {
            assert(bw.bits() =~= w0 + tok_bits(g, t));
            assert(tok_fits(g, t));
        }
    } else {
        if t.lc >= 24 || t.dc >= 40 {
            return false;
        }
        let (_b1, n1) = crate::enc_lz::pfx_info(t.lc);
        let (_b2, n2) = crate::enc_lz::pfx_info(t.dc);
        proof {
            vstd::arithmetic::power2::lemma2_to64();
        }
        if n1 > 18 || n2 > 18 || t.lx >= (1u32 << n1) || t.dx >= (1u32 << n2) {
            return false;
        }
        proof {
            vstd::bits::lemma_u32_shl_is_mul(1, n1);
            vstd::bits::lemma_u32_shl_is_mul(1, n2);
            if n1 < 18 {
                lemma_pow2_strictly_increases(n1 as nat, 18);
            }
            if n2 < 18 {
                lemma_pow2_strictly_increases(n2 as nat, 18);
            }
        }
        if !put_sym(bw, &hs[0], 256 + t.lc as usize, Ghost(g), Ghost(0)) {
            return false;
        }
        bw.put(t.lx, n1);
        if !put_sym(bw, &hs[4], t.dc as usize, Ghost(g), Ghost(4)) {
            return false;
        }
        bw.put(t.dx, n2);
        proof {
            assert(bw.bits() =~= w0 + tok_bits(g, t));
            assert(tok_fits(g, t));
        }
    }
    true
}

/// Writes the tokens with the codes of a group.
pub fn write_toks(bw: &mut BitWriter, toks: &Vec<Tok>, hs: &Vec<HCode>) -> (r: bool)
    requires
        old(bw).wf(),
        hs@.len() == 5,
        forall|k: int| 0 <= k < 5 ==> (#[trigger] hs@[k]).ok(),
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        r ==> final(bw).bits() == old(bw).bits() + tbits(lens_of(hs@), toks@, 0) && forall|j: int|
            0 <= j < toks@.len() ==> tok_fits(lens_of(hs@), #[trigger] toks@[j]),
{
    let ghost g = lens_of(hs@);
    let ghost b0 = bw.bits();
    let n = toks.len();
    let mut i: usize = 0;
    proof {
        lemma_pow2_small();
        assert(tbits(g, toks@, 0) =~= Seq::<nat>::empty() + tbits(g, toks@, 0));
    }
    while i < n
        invariant
            bw.wf(),
            bw.sent() == old(bw).sent(),
            n == toks@.len(),
            hs@.len() == 5,
            g == lens_of(hs@),
            forall|k: int| 0 <= k < 5 ==> (#[trigger] hs@[k]).ok(),
            i <= n,
            forall|j: int| 0 <= j < i ==> tok_fits(g, #[trigger] toks@[j]),
            bw.bits() + tbits(g, toks@, i as int) == b0 + tbits(g, toks@, 0),
        decreases n - i,
    {
        let t = toks[i];
        let ghost w0 = bw.bits();
        if !put_tok(bw, t, hs, Ghost(g)) {
            return false;
        }
        proof {
            assert(tbits(g, toks@, i as int) == tok_bits(g, t) + tbits(g, toks@, i + 1));
            assert(bw.bits() + tbits(g, toks@, i + 1) =~= w0 + tbits(g, toks@, i as int));
        }
        i = i + 1;
    }
    proof {
        assert(tbits(g, toks@, n as int) =~= Seq::<nat>::empty());
        assert(bw.bits() =~= bw.bits() + tbits(g, toks@, n as int));
        assert(Seq::<nat>::empty() + tbits(g, toks@, 0) =~= tbits(g, toks@, 0));
    }
    true
}

// ---------------------------------------------------------------------------
// Histograms and codes
// ---------------------------------------------------------------------------
#[inline(always)]
fn bump(h: &mut Vec<u32>, s: usize)
    requires
        s < old(h)@.len(),
    ensures
        final(h)@.len() == old(h)@.len(),
{
    let v = h[s];
    h.set(s, v.saturating_add(1));
}

/// Counts the symbols the tokens send with each of the five codes.
pub fn histograms(toks: &Vec<Tok>) -> (r: Vec<Vec<u32>>)
    ensures
        r@.len() == 5,
        forall|k: int| 0 <= k < 5 ==> (#[trigger] r@[k])@.len() == alphabet(k as nat, 0),
{
    let mut h0: Vec<u32> = vec![0u32; 280];
    let mut h1: Vec<u32> = vec![0u32; 256];
    let mut h2: Vec<u32> = vec![0u32; 256];
    let mut h3: Vec<u32> = vec![0u32; 256];
    let mut h4: Vec<u32> = vec![0u32; 40];
    let n = toks.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == toks@.len(),
            h0@.len() == 280,
            h1@.len() == 256,
            h2@.len() == 256,
            h3@.len() == 256,
            h4@.len() == 40,
            i <= n,
        decreases n - i,
    {
        let t = toks[i];
        if t.len == 0 {
            let (a, r, g, b) = crate::pxops::chans(t.v);
            bump(&mut h0, g as usize);
            bump(&mut h1, r as usize);
            bump(&mut h2, b as usize);
            bump(&mut h3, a as usize);
        } else {
            if t.lc < 24 {
                bump(&mut h0, 256 + t.lc as usize);
            }
            if t.dc < 40 {
                bump(&mut h4, t.dc as usize);
            }
        }
        i = i + 1;
    }
    proof {
        reveal_with_fuel(cache_size, 1);
    }
    let mut r: Vec<Vec<u32>> = Vec::new();
    r.push(h0);
    r.push(h1);
    r.push(h2);
    r.push(h3);
    r.push(h4);
    r
}

/// A prefix code for a histogram: Huffman lengths of at most 15 bits. An
/// empty histogram gets a code for symbol 0.
pub fn code_for(freq: &Vec<u32>) -> (r: Option<HCode>)
    requires
        1 <= freq@.len() <= 1024,
    ensures
        r matches Some(h) ==> h.ok() && valid_code(h.lens@) && h.lens@.len() == freq@.len(),
{
    let n = freq.len();
    let mut any = false;
    let mut i: usize = 0;
    while i < n
        invariant
            n == freq@.len(),
            i <= n,
        decreases n - i,
    {
        if freq[i] != 0 {
            any = true;
        }
        i = i + 1;
    }
    let lens = if any {
        huff_lens(freq.as_slice(), 15)
    } else {
        let mut l = vec![0u8; n];
        l.set(0, 1);
        l
    };
    let ghost lv = lens@;
    match make_code(lens) {
        Some(h) => Some(h),
        None => None,
    }
}

} // verus!
