//! Finding backward references: turns pixels into tokens, proven to decode
//! back to the same pixels (`enc_tok::play`).
use crate::enc_tok::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Prefix codes of lengths and distances (§5.2.2)
// ---------------------------------------------------------------------------
/// Prefix code `c`'s base and number of extra bits.
#[inline(always)]
pub fn pfx_info(c: u32) -> (r: (u32, u32))
    requires
        c < 40,
    ensures
        r.0 == pfx_base(c as nat),
        r.1 == pfx_extra(c as nat),
        r.1 <= 18,
        r.0 < 0x10_0000,
{
    if c < 4 {
        (c, 0)
    } else {
        let nb = (c - 2) / 2;
        let m = 2 + c % 2;
        proof {
            lemma2_to64();
            if nb < 18 {
                lemma_pow2_strictly_increases(nb as nat, 18);
            }
            assert(pow2(nb as nat) <= 0x40000);
            assert(m * pow2(nb as nat) <= 3 * 0x40000) by (nonlinear_arith)
                requires
                    m <= 3,
                    pow2(nb as nat) <= 0x40000,
            ;
            lemma_u32_shl_is_mul(m, nb);
        }
        (m << nb, nb)
    }
}

/// The prefix code, extra bit count and extra bits of a length or distance
/// code value `v`.
#[inline(always)]
pub fn prefix(v: u32) -> (r: Option<(u32, u32, u32)>)
    ensures
        r matches Some((c, nb, x)) ==> {
            &&& c < 40
            &&& nb == pfx_extra(c as nat)
            &&& nb <= 18
            &&& (x as nat) < pow2(nb as nat)
            &&& pfx_base(c as nat) + x + 1 == v
        },
{
    if v == 0 {
        return None;
    }
    let x = v - 1;
    let guess: u32 = if x < 4 {
        x
    } else {
        let lz = x.leading_zeros();
        if lz >= 30 {
            return None;
        }
        let hb = 31 - lz;
        let sh = hb - 1;
        let sb = (x >> sh) & 1;
        assert(sb <= 1) by (bit_vector)
            requires
                sb == (x >> sh) & 1,
        ;
        2 * hb + sb
    };
    if guess >= 40 {
        return None;
    }
    let (base, nb) = pfx_info(guess);
    proof {
        lemma2_to64();
        if nb < 18 {
            lemma_pow2_strictly_increases(nb as nat, 18);
        }
        lemma_u32_shl_is_mul(1, nb);
    }
    let size = 1u32 << nb;
    if base <= x && x - base < size {
        Some((guess, nb, x - base))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Copies
// ---------------------------------------------------------------------------
/// A copy at distance `d` of `len` pixels, each equal to the one `d` back,
/// appends those pixels.
pub proof fn lemma_copy(px: Seq<u32>, i: int, d: int, len: int)
    requires
        1 <= d <= i,
        0 <= len,
        i + len <= px.len(),
        forall|k: int| 0 <= k < len ==> #[trigger] px[i + k] == px[i + k - d],
    ensures
        px.subrange(0, i) + copy_seg(px.subrange(0, i), d as nat, len as nat) =~= px.subrange(0, i + len),
{
    let out = px.subrange(0, i);
    assert forall|k: int| 0 <= k < len implies #[trigger] copy_seg(out, d as nat, len as nat)[k] == px[i + k] by {
        lemma_copy_at(px, i, d, len, k);
    }
}

proof fn lemma_copy_at(px: Seq<u32>, i: int, d: int, len: int, k: int)
    requires
        1 <= d <= i,
        0 <= k < len,
        i + len <= px.len(),
        forall|k: int| 0 <= k < len ==> #[trigger] px[i + k] == px[i + k - d],
    ensures
        px[i - d + k % d] == px[i + k],
    decreases k,
{
    if k < d {
        vstd::arithmetic::div_mod::lemma_small_mod(k as nat, d as nat);
        assert(px[i + k] == px[i + k - d]);
    } else {
        lemma_copy_at(px, i, d, len, k - d);
        vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(k, d);
        assert(px[i + k] == px[i + k - d]);
        assert(i + (k - d) == i + k - d);
    }
}

/// The distance code of distance `d`: the pixel above and the pixel to the
/// left have short codes; others are `d + 120`.
#[inline(always)]
fn dist_code(d: u32, w: u32) -> (v: u32)
    requires
        1 <= d <= 0x10_0000 - 120,
        1 <= w,
    ensures
        1 <= v <= 0x10_0000,
        plane_to_dist(w as nat, v as nat) == d,
{
    if d == w {
        assert(code_to_plane()[0] == 0x18);
        let ghost dc = code_to_plane()[0];
        assert(dc / 16 == 1 && dc % 16 == 8);
        assert((dc / 16) * (w as nat) + 8 - (dc % 16) as int == w);
        1
    } else if d == 1 {
        assert(code_to_plane()[1] == 0x07);
        let ghost dc = code_to_plane()[1];
        assert(dc / 16 == 0 && dc % 16 == 7);
        assert((dc / 16) * (w as nat) + 8 - (dc % 16) as int == 1);
        2
    } else {
        d + 120
    }
}

/// How many pixels from `i` equal those from `j`, up to `max`.
#[inline(always)]
fn match_len(px: &[u32], i: usize, j: usize, max: usize) -> (r: usize)
    requires
        j < i,
        i + max <= px@.len(),
    ensures
        r <= max,
        forall|k: int| 0 <= k < r ==> px@[j + k] == #[trigger] px@[i + k],
{
    let n = px.len();
    let mut k: usize = 0;
    while k < max
        invariant
            n == px@.len(),
            k <= max,
            j < i,
            i + max <= px@.len(),
            forall|m: int| 0 <= m < k ==> px@[j + m] == #[trigger] px@[i + m],
        decreases max - k,
    {
        assert(j + k < i + k);
        if px[j + k] != px[i + k] {
            break;
        }
        k = k + 1;
    }
    k
}

// ---------------------------------------------------------------------------
// The match finder
// ---------------------------------------------------------------------------
const HASH_BITS: u32 = 16;
const HASH_SIZE: usize = 0x10000;
const EMPTY: u32 = 0xffff_ffff;
const MAX_LEN: usize = 4096;
const MAX_DIST: usize = 0x10_0000 - 120;
const MIN_LEN: usize = 3;

#[inline(always)]
fn hash2(a: u32, b: u32) -> (r: usize)
    ensures
        r < HASH_SIZE,
{
    let h = ((a as u64) | ((b as u64) << 32u64)).wrapping_mul(0x9E37_79B9_7F4A_7C15u64);
    let r = h >> 48u64;
    assert(h >> 48u64 < 0x10000) by (bit_vector);
    r as usize
}

#[inline(always)]
fn insert(head: &mut Vec<u32>, prev: &mut Vec<u32>, px: &[u32], p: usize)
    requires
        old(head)@.len() == HASH_SIZE,
        old(prev)@.len() == px@.len(),
        p + 1 < px@.len(),
        px@.len() < 0xffff_ffff,
    ensures
        final(head)@.len() == HASH_SIZE,
        final(prev)@.len() == px@.len(),
{
    let h = hash2(px[p], px[p + 1]);
    prev.set(p, head[h]);
    head.set(h, p as u32);
}

/// Follows the hash chain of pixel `i` for up to `chain` candidates,
/// keeping the longest match (`best` pixels at distance `bd` so far).
fn walk(px: &[u32], head: &Vec<u32>, prev: &Vec<u32>, i: usize, max: usize, chain: u32, best0: usize, bd0: usize) -> (r: (usize, usize))
    requires
        i + 1 < px@.len(),
        i + max <= px@.len(),
        head@.len() == HASH_SIZE,
        prev@.len() == px@.len(),
        best0 < max,
        best0 > 0 ==> 1 <= bd0 <= i && bd0 <= MAX_DIST,
        forall|k: int| 0 <= k < best0 ==> px@[i - bd0 + k] == #[trigger] px@[i + k],
    ensures
        r.0 <= max,
        r.0 > 0 ==> 1 <= r.1 <= i && r.1 <= MAX_DIST,
        forall|k: int| 0 <= k < r.0 ==> px@[i - r.1 + k] == #[trigger] px@[i + k],
{
    let n = px.len();
    let mut best = best0;
    let mut bd = bd0;
    let h = hash2(px[i], px[i + 1]);
    let mut j = head[h];
    let mut left = chain;
    while left > 0 && j != EMPTY && (j as usize) < i && i - (j as usize) <= MAX_DIST && best < max
        invariant
            n == px@.len(),
            i < n,
            i + max <= n,
            best <= max,
            best > 0 ==> 1 <= bd <= i && bd <= MAX_DIST,
            forall|k: int| 0 <= k < best ==> px@[i - bd + k] == #[trigger] px@[i + k],
            prev@.len() == n,
        decreases left,
    {
        let jj = j as usize;
        if px[jj + best] == px[i + best] {
            let l = match_len(px, i, jj, max);
            if l > best {
                best = l;
                bd = i - jj;
            }
        }
        left = left - 1;
        j = prev[jj];
    }
    (best, bd)
}

/// Enters pixels `i..i + len` in the hash chains.
fn insert_run(head: &mut Vec<u32>, prev: &mut Vec<u32>, px: &[u32], i: usize, len: usize)
    requires
        old(head)@.len() == HASH_SIZE,
        old(prev)@.len() == px@.len(),
        i + len <= px@.len(),
        px@.len() <= 0x1000_0000,
    ensures
        final(head)@.len() == HASH_SIZE,
        final(prev)@.len() == px@.len(),
{
    let n = px.len();
    let mut p = i;
    while p < i + len
        invariant
            n == px@.len(),
            n <= 0x1000_0000,
            i + len <= n,
            head@.len() == HASH_SIZE,
            prev@.len() == n,
        decreases i + len - p,
    {
        if p + 1 < n {
            insert(head, prev, px, p);
        }
        p = p + 1;
    }
}

/// Tokens for the pixels of an image `w` wide: literals, and copies found
/// along hash chains of up to `chain` candidates, plus the pixel to the left
/// and the pixel above.
pub fn tokenize(px: &[u32], w: u32, chain: u32) -> (r: Vec<Tok>)
    requires
        1 <= w,
        px@.len() <= 0x1000_0000,
    ensures
        toks_ok(w as nat, r@),
        play(w as nat, r@) == px@,
{
    let n = px.len();
    let mut toks: Vec<Tok> = Vec::with_capacity(n / 2 + 1);
    let mut head: Vec<u32> = vec![EMPTY; HASH_SIZE];
    let mut prev: Vec<u32> = vec![EMPTY; n];
    let ghost gw = w as nat;
    let mut i: usize = 0;
    proof {
        assert(px@.subrange(0, 0) =~= Seq::<u32>::empty());
    }
    while i < n
        invariant
            n == px@.len(),
            n <= 0x1000_0000,
            i <= n,
            1 <= w,
            gw == w as nat,
            head@.len() == HASH_SIZE,
            prev@.len() == n,
            toks_ok(gw, toks@),
            play(gw, toks@) == px@.subrange(0, i as int),
        decreases n - i,
    {
        let max = if n - i < MAX_LEN {
            n - i
        } else {
            MAX_LEN
        };
        let mut best: usize = 0;
        let mut bd: usize = 0;
        // The pixel to the left, and the pixel above.
        if i >= 1 {
            let l = match_len(px, i, i - 1, max);
            if l > best {
                best = l;
                bd = 1;
            }
        }
        if i >= w as usize && (w as usize) <= MAX_DIST && best < max {
            let l = match_len(px, i, i - w as usize, max);
            if l > best {
                best = l;
                bd = w as usize;
            }
        }
        // The hash chain.
        if i + 1 < n && best < max {
            let (b2, d2) = walk(px, &head, &prev, i, max, chain, best, bd);
            best = b2;
            bd = d2;
        }
        let mut emitted = false;
        if best >= MIN_LEN {
            let v = dist_code(bd as u32, w);
            match (prefix(best as u32), prefix(v)) {
                (Some((lc, _ln, lx)), Some((dc, _dn, dx))) => {
                    if lc < 24 {
                        let t = Tok { len: best as u32, v, lc, lx, dc, dx };
                        proof {
                            let ghost o = toks@;
                            assert(toks@.push(t).drop_last() =~= o);
                            assert forall|k: int| 0 <= k < best implies #[trigger] px@[i + k] == px@[i + k
                                - bd] by {
                                assert(px@[i - bd + k] == px@[i + k]);
                            }
                            lemma_copy(px@, i as int, bd as int, best as int);
                        }
                        toks.push(t);
                        insert_run(&mut head, &mut prev, px, i, best);
                        i = i + best;
                        emitted = true;
                    }
                },
                _ => {},
            }
        }
        if !emitted {
            let t = Tok { len: 0, v: px[i], lc: 0, lx: 0, dc: 0, dx: 0 };
            proof {
                assert(toks@.push(t).drop_last() =~= toks@);
                assert(px@.subrange(0, i as int).push(px@[i as int]) =~= px@.subrange(0, i + 1));
            }
            toks.push(t);
            if i + 1 < n {
                insert(&mut head, &mut prev, px, i);
            }
            i = i + 1;
        }
    }
    proof {
        assert(px@.subrange(0, n as int) =~= px@);
    }
    toks
}

} // verus!
