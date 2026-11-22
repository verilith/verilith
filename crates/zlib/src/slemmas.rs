//! Proofs the streaming decoder builds on. The spec decodes a stream from
//! its first byte into an empty output; a stream decoder sees its input a
//! piece at a time and keeps only the last 32 KiB of output. Two facts
//! bridge the gap:
//!
//! - Shifting: decoding `b` from bit `p + 8d` is decoding `b` without its
//!   first `d` bytes from bit `p`.
//! - The window: decoding after output `P ++ w` gives `P ++` what decoding
//!   after `w` gives, as long as `w` holds at least the 32 KiB that matches
//!   can reach back.
#[cfg(verus_only)]
use crate::ilemmas::*;
#[cfg(verus_only)]
use crate::inflate::*;
#[cfg(verus_only)]
use crate::huffman::{ALPHA_DIST, ALPHA_LIT};
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Shifting
// ---------------------------------------------------------------------------

/// `b` without its first `d` bytes.
pub open spec fn skip(b: Seq<u8>, d: int) -> Seq<u8> {
    b.subrange(d, b.len() as int)
}

/// A decoding result in the coordinates of `skip(b, d)`, from one in those
/// of `b`.
pub open spec fn sh(r: Option<(int, Seq<u8>)>, d: int) -> Option<(int, Seq<u8>)> {
    match r {
        None => None,
        Some((p, o)) => Some((p - 8 * d, o)),
    }
}

pub open spec fn sh3(r: Option<(int, Seq<u8>, Seq<u8>)>, d: int) -> Option<(int, Seq<u8>, Seq<u8>)> {
    match r {
        None => None,
        Some((p, x, y)) => Some((p - 8 * d, x, y)),
    }
}

pub proof fn lemma_skip_skip(b: Seq<u8>, d: int, e: int)
    requires
        0 <= d,
        0 <= e,
        d + e <= b.len(),
    ensures
        skip(skip(b, d), e) == skip(b, d + e),
{
    assert(skip(skip(b, d), e) =~= skip(b, d + e));
}

pub proof fn lemma_shift_bit(b: Seq<u8>, d: int, k: int)
    requires
        0 <= d <= b.len(),
        0 <= k < nbits(skip(b, d)),
    ensures
        bit(skip(b, d), k) == bit(b, k + 8 * d),
{
    lemma_fundamental_div_mod(k, 8);
    lemma_fundamental_div_mod_converse(k + 8 * d, 8, k / 8 + d, k % 8);
    assert(k / 8 < b.len() - d) by {
        lemma_div_is_ordered(k, 8 * (b.len() - d) - 1, 8);
        lemma_fundamental_div_mod_converse(8 * (b.len() - d) - 1, 8, b.len() - d - 1, 7);
    }
}

pub proof fn lemma_shift_bits(b: Seq<u8>, d: int, p: int, n: nat)
    requires
        0 <= d <= b.len(),
        0 <= p,
        p + n <= nbits(skip(b, d)),
    ensures
        bits(skip(b, d), p, n) == bits(b, p + 8 * d, n),
    decreases n,
{
    if n > 0 {
        lemma_shift_bit(b, d, p);
        lemma_shift_bits(b, d, p + 1, (n - 1) as nat);
        assert(p + 1 + 8 * d == p + 8 * d + 1);
    }
}

pub proof fn lemma_shift_code_bits(b: Seq<u8>, d: int, p: int, n: nat)
    requires
        0 <= d <= b.len(),
        0 <= p,
        p + n <= nbits(skip(b, d)),
    ensures
        code_bits(skip(b, d), p, n) == code_bits(b, p + 8 * d, n),
    decreases n,
{
    if n > 0 {
        lemma_shift_bit(b, d, p + n - 1);
        lemma_shift_code_bits(b, d, p, (n - 1) as nat);
        assert(p + n - 1 + 8 * d == p + 8 * d + n - 1);
    }
}

pub proof fn lemma_shift_decode_from(lens: Seq<u8>, b: Seq<u8>, d: int, p: int, l: nat)
    requires
        0 <= d <= b.len(),
        0 <= p,
    ensures
        decode_from(lens, skip(b, d), p, l) == decode_from(lens, b, p + 8 * d, l),
    decreases MAX_BITS + 1 - l,
{
    if l <= MAX_BITS && p + l <= nbits(skip(b, d)) {
        lemma_shift_code_bits(b, d, p, l);
        lemma_shift_decode_from(lens, b, d, p, l + 1);
    }
}

pub proof fn lemma_shift_decode(lens: Seq<u8>, b: Seq<u8>, d: int, p: int)
    requires
        0 <= d <= b.len(),
        0 <= p,
    ensures
        decode(lens, skip(b, d), p) == decode(lens, b, p + 8 * d),
{
    lemma_shift_decode_from(lens, b, d, p, 1);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_shift_codes(b: Seq<u8>, d: int, p: int, out: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>)
    requires
        0 <= d <= b.len(),
        0 <= p,
    ensures
        inflate_codes(skip(b, d), p, out, lit, dist) == sh(inflate_codes(b, p + 8 * d, out, lit, dist), d),
    decreases nbits(skip(b, d)) - p,
{
    let s = skip(b, d);
    let q = p + 8 * d;
    lemma_shift_decode(lit, b, d, p);
    match decode(lit, s, p) {
        None => {},
        Some((sym, l)) => {
            let p1 = p + l;
            if !advances(s, p, p1) {
            } else if sym < 256 {
                lemma_shift_codes(b, d, p1, out.push(sym as u8), lit, dist);
                assert(p1 + 8 * d == q + l);
            } else if sym == 256 {
            } else if sym > 285 {
            } else {
                let le = len_extra()[sym - 257];
                let p2 = p1 + le;
                if p2 <= nbits(s) {
                    lemma_shift_bits(b, d, p1, le);
                    lemma_shift_decode(dist, b, d, p2);
                    assert(p2 + 8 * d == q + l + le);
                    match decode(dist, s, p2) {
                        None => {},
                        Some((ds, dl)) => {
                            let p3 = p2 + dl;
                            if ds < 30 {
                                let de = dist_extra()[ds as int];
                                let p4 = p3 + de;
                                if p4 <= nbits(s) {
                                    lemma_shift_bits(b, d, p3, de);
                                }
                                assert(p3 + 8 * d == q + l + le + dl);
                                assert(p4 + 8 * d == q + l + le + dl + de);
                                if advances(s, p, p4) {
                                    let len = len_base()[sym - 257] + bits(s, p1, le);
                                    let dd = dist_base()[ds as int] + bits(s, p3, de);
                                    if dd <= out.len() {
                                        lemma_shift_codes(b, d, p4, copy_match(out, dd, len), lit, dist);
                                    }
                                }
                            }
                        },
                    }
                }
            }
        },
    }
}

pub proof fn lemma_shift_stored(b: Seq<u8>, d: int, p: int, out: Seq<u8>)
    requires
        0 <= d <= b.len(),
        0 <= p,
    ensures
        inflate_stored(skip(b, d), p, out) == sh(inflate_stored(b, p + 8 * d, out), d),
{
    let s = skip(b, d);
    let i = (p + 7) / 8;
    lemma_fundamental_div_mod(p + 7, 8);
    lemma_fundamental_div_mod_converse(p + 8 * d + 7, 8, i + d, (p + 7) % 8);
    if i + 4 <= s.len() {
        assert(s[i] == b[i + d]);
        assert(s[i + 1] == b[i + d + 1]);
        assert(s[i + 2] == b[i + d + 2]);
        assert(s[i + 3] == b[i + d + 3]);
        let len = s[i] as int + 256 * s[i + 1] as int;
        if i + 4 + len <= s.len() {
            assert(s.subrange(i + 4, i + 4 + len) =~= b.subrange(i + d + 4, i + d + 4 + len));
            assert(8 * (i + d + 4 + len) - 8 * d == 8 * (i + 4 + len));
        }
    }
}

pub proof fn lemma_shift_stored_rest(b: Seq<u8>, d: int, p: int, n: nat, out: Seq<u8>)
    requires
        0 <= d <= b.len(),
        0 <= p,
    ensures
        stored_rest(skip(b, d), p, n, out) == sh(stored_rest(b, p + 8 * d, n, out), d),
{
    let s = skip(b, d);
    let i = p / 8;
    lemma_fundamental_div_mod(p, 8);
    lemma_fundamental_div_mod_converse(p + 8 * d, 8, i + d, p % 8);
    if i + n <= s.len() {
        assert(s.subrange(i, i + n) =~= b.subrange(i + d, i + d + n));
        assert(8 * (i + d + n) - 8 * d == 8 * (i + n));
    }
}

pub proof fn lemma_shift_clen_lens(b: Seq<u8>, d: int, p: int, hclen: nat)
    requires
        0 <= d <= b.len(),
        0 <= p,
        hclen <= 19,
        p + 3 * hclen <= nbits(skip(b, d)),
    ensures
        clen_lens(skip(b, d), p, hclen) == clen_lens(b, p + 8 * d, hclen),
{
    assert forall|s: int| 0 <= s < 19 && clen_slot()[s] < hclen implies bits(
        skip(b, d),
        p + 3 * clen_slot()[s],
        3,
    ) == bits(b, p + 8 * d + 3 * clen_slot()[s], 3) by {
        lemma_shift_bits(b, d, p + 3 * clen_slot()[s], 3);
        assert(p + 3 * clen_slot()[s] + 8 * d == p + 8 * d + 3 * clen_slot()[s]);
    }
    assert(clen_lens(skip(b, d), p, hclen) =~= clen_lens(b, p + 8 * d, hclen));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_shift_read_lens(cl: Seq<u8>, b: Seq<u8>, d: int, p: int, lens: Seq<u8>, total: nat)
    requires
        0 <= d <= b.len(),
        0 <= p,
    ensures
        read_lens(cl, skip(b, d), p, lens, total) == sh(read_lens(cl, b, p + 8 * d, lens, total), d),
    decreases total - lens.len(),
{
    let s = skip(b, d);
    if lens.len() < total {
        lemma_shift_decode(cl, b, d, p);
        match decode(cl, s, p) {
            None => {},
            Some((sym, l)) => {
                let p1 = p + l;
                lemma_decode_from_end(cl, s, p, 1);
                assert(p1 + 8 * d == p + 8 * d + l);
                if sym < 16 {
                    lemma_shift_read_lens(cl, b, d, p1, lens.push(sym as u8), total);
                } else if sym == 16 && lens.len() == 0 {
                } else {
                    let e: nat = if sym == 16 {
                        2
                    } else if sym == 17 {
                        3
                    } else {
                        7
                    };
                    let base: nat = if sym == 16 {
                        3
                    } else if sym == 17 {
                        3
                    } else {
                        11
                    };
                    let v: u8 = if sym == 16 {
                        lens.last()
                    } else {
                        0
                    };
                    if p1 + e <= nbits(s) {
                        lemma_shift_bits(b, d, p1, e);
                        let rep = base + bits(s, p1, e);
                        assert(p1 + e + 8 * d == p + 8 * d + l + e);
                        if lens.len() + rep <= total {
                            lemma_shift_read_lens(cl, b, d, p1 + e, lens + Seq::new(rep, |i: int| v), total);
                        }
                    }
                }
            },
        }
    }
}

pub proof fn lemma_shift_read_dynamic(b: Seq<u8>, d: int, p: int)
    requires
        0 <= d <= b.len(),
        0 <= p,
    ensures
        read_dynamic(skip(b, d), p) == sh3(read_dynamic(b, p + 8 * d), d),
{
    let s = skip(b, d);
    let q = p + 8 * d;
    if p + 14 <= nbits(s) {
        lemma_shift_bits(b, d, p, 5);
        lemma_shift_bits(b, d, p + 5, 5);
        lemma_shift_bits(b, d, p + 10, 4);
        assert(p + 5 + 8 * d == q + 5);
        assert(p + 10 + 8 * d == q + 10);
        let hlit = bits(s, p, 5) + 257;
        let hdist = bits(s, p + 5, 5) + 1;
        let hclen = bits(s, p + 10, 4) + 4;
        lemma_bits_bound(s, p + 10, 4);
        lemma2_to64();
        let p0 = p + 14;
        if !(hlit > 286 || hdist > 30 || p0 + 3 * hclen > nbits(s)) {
            lemma_shift_clen_lens(b, d, p0, hclen);
            assert(p0 + 8 * d == q + 14);
            assert(p0 + 3 * hclen + 8 * d == q + 14 + 3 * hclen);
            lemma_shift_read_lens(clen_lens(s, p0, hclen), b, d, p0 + 3 * hclen, Seq::empty(), hlit + hdist);
        }
    }
}

/// A dynamic block header ends after it starts.
pub proof fn lemma_read_dynamic_pos(b: Seq<u8>, p: int)
    ensures
        read_dynamic(b, p) matches Some((p2, x, y)) ==> p2 >= p,
{
    if p + 14 <= nbits(b) {
        let hlit = bits(b, p, 5) + 257;
        let hdist = bits(b, p + 5, 5) + 1;
        let hclen = bits(b, p + 10, 4) + 4;
        lemma_read_lens_end(clen_lens(b, p + 14, hclen), b, p + 14 + 3 * hclen, Seq::empty(), hlit + hdist);
    }
}

/// The result of a block body, as the spec continues it.
pub proof fn lemma_shift_after(b: Seq<u8>, d: int, last: bool, r: Option<(int, Seq<u8>)>)
    requires
        0 <= d <= b.len(),
        r matches Some((p, o)) ==> p >= 8 * d,
    ensures
        after(skip(b, d), last, sh(r, d)) == sh(after(b, last, r), d),
{
    reveal(after);
    if let Some((p, o)) = r {
        assert(sh(r, d) == Some((p - 8 * d, o)));
        if !last {
            lemma_shift_blocks(b, d, p - 8 * d, o);
            assert(p - 8 * d + 8 * d == p);
            assert(after(skip(b, d), last, sh(r, d)) == inflate_blocks(skip(b, d), p - 8 * d, o));
            assert(after(b, last, r) == inflate_blocks(b, p, o));
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_shift_blocks(b: Seq<u8>, d: int, p: int, out: Seq<u8>)
    requires
        0 <= d <= b.len(),
        0 <= p,
    ensures
        inflate_blocks(skip(b, d), p, out) == sh(inflate_blocks(b, p + 8 * d, out), d),
    decreases nbits(skip(b, d)) - p,
{
    let s = skip(b, d);
    let q = p + 8 * d;
    if p + 3 <= nbits(s) {
        lemma_shift_bits(b, d, p, 1);
        lemma_shift_bits(b, d, p + 1, 2);
        assert(p + 1 + 8 * d == q + 1);
        let btype = bits(s, p + 1, 2);
        let p3 = p + 3;
        assert(p3 + 8 * d == q + 3);
        let r = if btype == 0 {
            inflate_stored(s, p3, out)
        } else if btype == 1 {
            inflate_codes(s, p3, out, fixed_lit_lens(), fixed_dist_lens())
        } else if btype == 2 {
            match read_dynamic(s, p3) {
                None => None,
                Some((p2, lit, dist)) => inflate_codes(s, p2, out, lit, dist),
            }
        } else {
            None
        };
        let r0 = if btype == 0 {
            inflate_stored(b, q + 3, out)
        } else if btype == 1 {
            inflate_codes(b, q + 3, out, fixed_lit_lens(), fixed_dist_lens())
        } else if btype == 2 {
            match read_dynamic(b, q + 3) {
                None => None,
                Some((p2, lit, dist)) => inflate_codes(b, p2, out, lit, dist),
            }
        } else {
            None
        };
        if btype == 0 {
            lemma_shift_stored(b, d, p3, out);
        } else if btype == 1 {
            lemma_shift_codes(b, d, p3, out, fixed_lit_lens(), fixed_dist_lens());
        } else if btype == 2 {
            lemma_shift_read_dynamic(b, d, p3);
            if let Some((p2, lit, dist)) = read_dynamic(s, p3) {
                lemma_read_dynamic_pos(s, p3);
                lemma_shift_codes(b, d, p2, out, lit, dist);
                assert(p2 + 8 * d == read_dynamic(b, q + 3)->Some_0.0);
            }
        }
        assert(r == sh(r0, d));
        if let Some((p2, out2)) = r {
            if bits(s, p, 1) != 1 && advances(s, p, p2) {
                lemma_shift_blocks(b, d, p2, out2);
                assert(p2 + 8 * d == r0->Some_0.0);
            }
        }
    }
}

/// `s1` is `s2` with its input moved `d` bytes on: what is left to decode
/// is the same, in the coordinates of `skip(b, d)`.
pub open spec fn moved(s1: Inflater, s2: Inflater, d: int) -> bool {
    &&& s2.in_pos == s1.in_pos + d
    &&& s1.buf == s2.buf
    &&& s1.cnt == s2.cnt
    &&& s1.same_but_bits(&s2)
}

pub proof fn lemma_shift_inv(s1: Inflater, s2: Inflater, b: Seq<u8>, d: int)
    requires
        0 <= d <= b.len(),
        moved(s1, s2, d),
        s2.inv(b),
        s1.cnt <= 8 * s1.in_pos,
    ensures
        s1.inv(skip(b, d)),
        s1.pos() + 8 * d == s2.pos(),
{
    lemma_shift_bits(b, d, s1.pos(), s1.cnt as nat);
}

pub proof fn lemma_shift_rest(s1: Inflater, s2: Inflater, b: Seq<u8>, d: int, o: Seq<u8>)
    requires
        0 <= d <= b.len(),
        moved(s1, s2, d),
        s1.pos() >= 0,
    ensures
        s1.rest(skip(b, d), o) == sh(s2.rest(b, o), d),
{
    reveal(Inflater::rest);
    let p = s1.pos();
    assert(s2.pos() == p + 8 * d);
    if s1.mode == MODE_HEADER {
        if !s1.last {
            lemma_shift_blocks(b, d, p, o);
        }
    } else if s1.mode == MODE_STORED {
        lemma_shift_stored_rest(b, d, p, s1.stored_left as nat, o);
        let r = stored_rest(b, p + 8 * d, s1.stored_left as nat, o);
        lemma_fundamental_div_mod(p + 8 * d, 8);
        lemma_shift_after(b, d, s1.last, r);
    } else if s1.mode == MODE_CODES {
        let o2 = copy_match(o, s1.copy_dist as nat, s1.copy_len as nat);
        lemma_shift_codes(b, d, p, o2, s1.lit_lens@, s1.dist_lens@);
        lemma_codes_end(b, p + 8 * d, o2, s1.lit_lens@, s1.dist_lens@);
        lemma_shift_after(b, d, s1.last, inflate_codes(b, p + 8 * d, o2, s1.lit_lens@, s1.dist_lens@));
    }
}

// ---------------------------------------------------------------------------
// The window
// ---------------------------------------------------------------------------

/// How far back a match can reach (§3.2.5).
pub spec const MAX_DIST: nat = 32768;

/// A decoding result with `p` before its output.
pub open spec fn pre(pfx: Seq<u8>, r: Option<(int, Seq<u8>)>) -> Option<(int, Seq<u8>)> {
    match r {
        None => None,
        Some((q, o)) => Some((q, pfx + o)),
    }
}

pub proof fn lemma_win_copy(pfx: Seq<u8>, w: Seq<u8>, d: nat, len: nat)
    requires
        1 <= d <= w.len(),
    ensures
        copy_match(pfx + w, d, len) == pfx + copy_match(w, d, len),
    decreases len,
{
    if len > 0 {
        let x = w[w.len() - d];
        assert((pfx + w)[(pfx + w).len() - d] == x);
        assert((pfx + w).push(x) =~= pfx + w.push(x));
        lemma_win_copy(pfx, w.push(x), d, (len - 1) as nat);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_win_codes(b: Seq<u8>, p: int, pfx: Seq<u8>, w: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>)
    requires
        w.len() >= MAX_DIST,
    ensures
        inflate_codes(b, p, pfx + w, lit, dist) == pre(pfx, inflate_codes(b, p, w, lit, dist)),
    decreases nbits(b) - p,
{
    match decode(lit, b, p) {
        None => {},
        Some((sym, l)) => {
            let p1 = p + l;
            if !advances(b, p, p1) {
            } else if sym < 256 {
                assert((pfx + w).push(sym as u8) =~= pfx + w.push(sym as u8));
                lemma_win_codes(b, p1, pfx, w.push(sym as u8), lit, dist);
            } else if sym == 256 {
            } else if sym > 285 {
            } else {
                let le = len_extra()[sym - 257];
                let len = len_base()[sym - 257] + bits(b, p1, le);
                let p2 = p1 + le;
                if p2 <= nbits(b) {
                    match decode(dist, b, p2) {
                        None => {},
                        Some((ds, dl)) => {
                            let p3 = p2 + dl;
                            if ds < 30 {
                                let de = dist_extra()[ds as int];
                                let dd = dist_base()[ds as int] + bits(b, p3, de);
                                let p4 = p3 + de;
                                lemma_dist_max(b, ds, p3);
                                if advances(b, p, p4) {
                                    lemma_win_copy(pfx, w, dd, len);
                                    lemma_copy_match_len(w, dd, len);
                                    lemma_win_codes(b, p4, pfx, copy_match(w, dd, len), lit, dist);
                                }
                            }
                        },
                    }
                }
            }
        },
    }
}

pub proof fn lemma_win_stored(b: Seq<u8>, p: int, pfx: Seq<u8>, w: Seq<u8>)
    ensures
        inflate_stored(b, p, pfx + w) == pre(pfx, inflate_stored(b, p, w)),
{
    let i = (p + 7) / 8;
    if i + 4 <= b.len() {
        let len = b[i] as int + 256 * b[i + 1] as int;
        if i + 4 + len <= b.len() {
            assert(pfx + w + b.subrange(i + 4, i + 4 + len) =~= pfx + (w + b.subrange(i + 4, i + 4 + len)));
        }
    }
}

pub proof fn lemma_win_stored_rest(b: Seq<u8>, p: int, n: nat, pfx: Seq<u8>, w: Seq<u8>)
    ensures
        stored_rest(b, p, n, pfx + w) == pre(pfx, stored_rest(b, p, n, w)),
{
    let i = p / 8;
    if i + n <= b.len() {
        assert(pfx + w + b.subrange(i, i + n) =~= pfx + (w + b.subrange(i, i + n)));
    }
}

pub proof fn lemma_win_block(b: Seq<u8>, p: int, pfx: Seq<u8>, w: Seq<u8>)
    requires
        w.len() >= MAX_DIST,
    ensures
        block(b, p, pfx + w) == pre(pfx, block(b, p, w)),
{
    reveal(block);
    let btype = bits(b, p + 1, 2);
    if btype == 0 {
        lemma_win_stored(b, p + 3, pfx, w);
    } else if btype == 1 {
        lemma_win_codes(b, p + 3, pfx, w, fixed_lit_lens(), fixed_dist_lens());
    } else if btype == 2 {
        if let Some((p2, lit, dist)) = read_dynamic(b, p + 3) {
            lemma_win_codes(b, p2, pfx, w, lit, dist);
        }
    }
}

pub proof fn lemma_win_blocks(b: Seq<u8>, p: int, pfx: Seq<u8>, w: Seq<u8>)
    requires
        w.len() >= MAX_DIST,
    ensures
        inflate_blocks(b, p, pfx + w) == pre(pfx, inflate_blocks(b, p, w)),
    decreases nbits(b) - p,
{
    if 0 <= p && p + 3 <= nbits(b) {
        lemma_blocks_unfold(b, p, pfx + w);
        lemma_blocks_unfold(b, p, w);
        lemma_win_block(b, p, pfx, w);
        lemma_block_output(b, p, w);
        reveal(after);
        if let Some((p2, o2)) = block(b, p, w) {
            if bits(b, p, 1) != 1 {
                lemma_win_blocks(b, p2, pfx, o2);
            }
        }
    }
}

pub proof fn lemma_win_after(b: Seq<u8>, last: bool, pfx: Seq<u8>, r: Option<(int, Seq<u8>)>)
    requires
        r matches Some((p, o)) ==> o.len() >= MAX_DIST,
    ensures
        after(b, last, pre(pfx, r)) == pre(pfx, after(b, last, r)),
{
    reveal(after);
    if let Some((p, o)) = r {
        if !last {
            lemma_win_blocks(b, p, pfx, o);
        }
    }
}

/// What is left to decode after output `pfx ++ w` is `pfx ++` what is left
/// after `w`.
pub proof fn lemma_win_rest(s: Inflater, b: Seq<u8>, pfx: Seq<u8>, w: Seq<u8>)
    requires
        w.len() >= MAX_DIST,
        s.mode == MODE_CODES && s.copy_len > 0 ==> 1 <= s.copy_dist <= MAX_DIST,
    ensures
        s.rest(b, pfx + w) == pre(pfx, s.rest(b, w)),
{
    reveal(Inflater::rest);
    let p = s.pos();
    if s.mode == MODE_HEADER {
        if !s.last {
            lemma_win_blocks(b, p, pfx, w);
        }
    } else if s.mode == MODE_STORED {
        lemma_win_stored_rest(b, p, s.stored_left as nat, pfx, w);
        lemma_win_after(b, s.last, pfx, stored_rest(b, p, s.stored_left as nat, w));
    } else if s.mode == MODE_CODES {
        let o2 = copy_match(w, s.copy_dist as nat, s.copy_len as nat);
        if s.copy_len > 0 {
            lemma_win_copy(pfx, w, s.copy_dist as nat, s.copy_len as nat);
        } else {
            assert(copy_match(pfx + w, s.copy_dist as nat, 0) == pfx + w);
            assert(copy_match(w, s.copy_dist as nat, 0) == w);
        }
        lemma_copy_match_len(w, s.copy_dist as nat, s.copy_len as nat);
        lemma_win_codes(b, p, pfx, o2, s.lit_lens@, s.dist_lens@);
        lemma_codes_end(b, p, o2, s.lit_lens@, s.dist_lens@);
        lemma_win_after(b, s.last, pfx, inflate_codes(b, p, o2, s.lit_lens@, s.dist_lens@));
    } else {
    }
}

// ---------------------------------------------------------------------------
// Prefixes
// ---------------------------------------------------------------------------

pub proof fn lemma_prefix_bits(x: Seq<u8>, b: Seq<u8>, p: int, n: nat)
    requires
        prefix(x, b),
        0 <= p,
        p + n <= nbits(x),
    ensures
        bits(x, p, n) == bits(b, p, n),
    decreases n,
{
    if n > 0 {
        lemma_fundamental_div_mod(p, 8);
        assert(p / 8 < x.len()) by {
            lemma_div_is_ordered(p, 8 * x.len() - 1, 8);
            lemma_fundamental_div_mod_converse(8 * x.len() - 1, 8, x.len() - 1, 7);
        }
        lemma_prefix_index(x, b, p / 8);
        lemma_prefix_bits(x, b, p + 1, (n - 1) as nat);
    }
}

/// The decoder's invariant only looks at the input it has read.
pub proof fn lemma_inv_prefix(s: Inflater, x: Seq<u8>, b: Seq<u8>)
    requires
        prefix(x, b),
        s.in_pos <= x.len(),
        s.cnt <= 8 * s.in_pos,
    ensures
        s.inv(x) == s.inv(b),
        s.bits_ok(x) == s.bits_ok(b),
{
    lemma_prefix_bits(x, b, s.pos(), s.cnt as nat);
}

pub proof fn lemma_prefix_skip(x: Seq<u8>, b: Seq<u8>, d: int)
    requires
        prefix(x, b),
        0 <= d <= x.len(),
    ensures
        prefix(skip(x, d), skip(b, d)),
{
    assert(skip(x, d) =~= skip(b, d).subrange(0, x.len() - d));
}

pub proof fn lemma_prefix_trans(x: Seq<u8>, y: Seq<u8>, b: Seq<u8>)
    requires
        prefix(x, y),
        prefix(y, b),
    ensures
        prefix(x, b),
{
    assert(x =~= b.subrange(0, x.len() as int)) by {
        assert forall|i: int| 0 <= i < x.len() implies x[i] == b[i] by {
            lemma_prefix_index(x, y, i);
            lemma_prefix_index(y, b, i);
        }
    }
}

proof fn lemma_after_grows(b: Seq<u8>, last: bool, r: Option<(int, Seq<u8>)>, o: Seq<u8>)
    requires
        r matches Some((q, o1)) ==> q >= 0 && o.len() <= o1.len(),
    ensures
        after(b, last, r) matches Some((_, o2)) ==> o.len() <= o2.len(),
{
    reveal(after);
    if let Some((q, o1)) = r {
        if !last {
            lemma_blocks_output(b, q, o1);
        }
    }
}

/// Decoding only appends to the output: whatever is left to decode after
/// output `o` ends with output at least as long as `o`.
#[verifier::spinoff_prover]
pub proof fn lemma_rest_grows(s: Inflater, b: Seq<u8>, o: Seq<u8>)
    requires
        s.pos() >= 0,
    ensures
        s.rest(b, o) matches Some((_, o2)) ==> o.len() <= o2.len(),
{
    reveal(Inflater::rest);
    let p = s.pos();
    if s.mode == MODE_HEADER {
        if !s.last {
            lemma_blocks_output(b, p, o);
        }
    } else if s.mode == MODE_STORED {
        let r = stored_rest(b, p, s.stored_left as nat, o);
        assert(r matches Some((q, o1)) ==> q >= 0 && o.len() <= o1.len());
        lemma_after_grows(b, s.last, r, o);
        assert(s.rest(b, o) == after(b, s.last, r));
    } else if s.mode == MODE_CODES {
        let o1 = copy_match(o, s.copy_dist as nat, s.copy_len as nat);
        lemma_copy_match_len(o, s.copy_dist as nat, s.copy_len as nat);
        lemma_codes_end(b, p, o1, s.lit_lens@, s.dist_lens@);
        let r = inflate_codes(b, p, o1, s.lit_lens@, s.dist_lens@);
        lemma_after_grows(b, s.last, r, o);
        assert(s.rest(b, o) == after(b, s.last, r));
    }
}


/// Decoding blocks ends after it starts.
pub proof fn lemma_blocks_pos(b: Seq<u8>, pos: int, out: Seq<u8>)
    ensures
        inflate_blocks(b, pos, out) matches Some((e, _)) ==> e > pos,
    decreases nbits(b) - pos,
{
    if 0 <= pos && pos + 3 <= nbits(b) {
        lemma_blocks_unfold(b, pos, out);
        lemma_block_end(b, pos, out);
        reveal(after);
        match block(b, pos, out) {
            None => {},
            Some((p, o)) => {
                if bits(b, pos, 1) != 1 {
                    lemma_blocks_pos(b, p, o);
                }
            },
        }
    }
}

/// What follows a block ends no earlier than the block.
pub proof fn lemma_after_pos(b: Seq<u8>, last: bool, p: int, o: Seq<u8>)
    ensures
        after(b, last, Some((p, o))) matches Some((e, _)) ==> e >= p,
{
    reveal(after);
    if !last {
        lemma_blocks_pos(b, p, o);
    }
}

/// The stream ends no earlier than where the decoder is.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn lemma_rest_pos(s: Inflater, b: Seq<u8>, o: Seq<u8>)
    requires
        s.pos() >= 0,
        s.mode == MODE_STORED ==> s.pos() % 8 == 0,
    ensures
        s.rest(b, o) matches Some((e, _)) ==> e >= s.pos(),
{
    reveal(Inflater::rest);
    let p = s.pos();
    if s.mode == MODE_HEADER {
        if !s.last {
            lemma_blocks_pos(b, p, o);
        }
    } else if s.mode == MODE_STORED {
        let r = stored_rest(b, p, s.stored_left as nat, o);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p, 8);
        lemma_after_none(b, s.last);
        if let Some((q, o2)) = r {
            assert(q >= p);
            lemma_after_pos(b, s.last, q, o2);
        }
    } else if s.mode == MODE_CODES {
        let o1 = copy_match(o, s.copy_dist as nat, s.copy_len as nat);
        lemma_codes_end(b, p, o1, s.lit_lens@, s.dist_lens@);
        let r = inflate_codes(b, p, o1, s.lit_lens@, s.dist_lens@);
        lemma_after_none(b, s.last);
        if let Some((q, o2)) = r {
            lemma_after_pos(b, s.last, q, o2);
        }
    }
}


/// Decoding a symbol that ends inside a prefix of the input reads only the
/// prefix.
pub proof fn lemma_decode_prefix(lens: Seq<u8>, x: Seq<u8>, b: Seq<u8>, pos: int, l: nat)
    requires
        prefix(x, b),
        0 <= pos,
        l >= 1,
    ensures
        decode_from(lens, b, pos, l) matches Some((s, k)) ==> (pos + k <= nbits(x) ==> decode_from(lens, x, pos, l)
            == decode_from(lens, b, pos, l)),
    decreases MAX_BITS + 1 - l,
{
    lemma_decode_from_end(lens, b, pos, l);
    if l <= MAX_BITS && pos + l <= nbits(b) && pos + l <= nbits(x) {
        verilith_core::huffman::lemma_code_bits_rev(b, pos, l, l);
        verilith_core::huffman::lemma_code_bits_rev(x, pos, l, l);
        lemma_prefix_bits(x, b, pos, l);
        lemma_decode_prefix(lens, x, b, pos, l + 1);
    }
}

/// A symbol the decoder found missing from the input `x` (absent, or
/// running past its end) needs bits past the end of `x` in any longer
/// input.
pub proof fn lemma_decode_past(lens: Seq<u8>, x: Seq<u8>, b: Seq<u8>, pos: int, which: u8)
    requires
        prefix(x, b),
        0 <= pos,
        match decode(lens, x, pos) {
            None => true,
            Some((s, k)) => pos + k + extra_of(which, s) > nbits(x),
        },
    ensures
        decode(lens, b, pos) matches Some((s, k)) ==> pos + k + extra_of(which, s) > nbits(x),
{
    lemma_decode_prefix(lens, x, b, pos, 1);
}


/// The bits a repeat code length symbol takes after its code.
pub open spec fn rep_bits(s: nat) -> nat {
    if s < 16 {
        0
    } else if s == 16 {
        2
    } else if s == 17 {
        3
    } else {
        7
    }
}

/// Reading code lengths ends after the next symbol and its repeat bits.
pub proof fn lemma_read_lens_step(cl: Seq<u8>, b: Seq<u8>, pos: int, lens: Seq<u8>, total: nat)
    requires
        lens.len() < total,
    ensures
        read_lens(cl, b, pos, lens, total) matches Some((p2, _)) ==> (decode(cl, b, pos) matches Some((s, k))
            && p2 >= pos + k + rep_bits(s)),
{
    match decode(cl, b, pos) {
        None => {},
        Some((sym, l)) => {
            let p1 = pos + l;
            if sym < 16 {
                lemma_read_lens_end(cl, b, p1, lens.push(sym as u8), total);
            } else if !(sym == 16 && lens.len() == 0) {
                let e: nat = if sym == 16 { 2 } else if sym == 17 { 3 } else { 7 };
                let base: nat = if sym == 16 { 3 } else if sym == 17 { 3 } else { 11 };
                let v: u8 = if sym == 16 { lens.last() } else { 0 };
                let rep = base + bits(b, p1, e);
                if !(p1 + e > nbits(b) || lens.len() + rep > total) {
                    lemma_read_lens_end(cl, b, p1 + e, lens + Seq::new(rep, |i: int| v), total);
                }
            }
        },
    }
}


/// A dynamic header ends after its fixed fields and code length code.
pub proof fn lemma_read_dynamic_end(b: Seq<u8>, p: int)
    ensures
        read_dynamic(b, p) matches Some((p2, _, _)) ==> p2 >= p + 14 + 3 * (bits(b, p + 10, 4) + 4),
{
    if p + 14 <= nbits(b) {
        let hlit = bits(b, p, 5) + 257;
        let hdist = bits(b, p + 5, 5) + 1;
        let hclen = bits(b, p + 10, 4) + 4;
        lemma_read_lens_end(clen_lens(b, p + 14, hclen), b, p + 14 + 3 * hclen, Seq::empty(), hlit + hdist);
    }
}


/// Blocks end after the first block's 3 header bits.
pub proof fn lemma_blocks_hdr(b: Seq<u8>, pos: int, out: Seq<u8>)
    ensures
        inflate_blocks(b, pos, out) matches Some((e, _)) ==> e >= pos + 3,
{
    if 0 <= pos && pos + 3 <= nbits(b) {
        lemma_blocks_unfold(b, pos, out);
        lemma_after_none(b, bits(b, pos, 1) == 1);
        reveal(block);
        let p = pos + 3;
        let btype = bits(b, pos + 1, 2);
        let r = block(b, pos, out);
        if btype == 0 {
            let i = (p + 7) / 8;
            assert(8 * i >= p);
        } else if btype == 1 {
            lemma_codes_end(b, p, out, fixed_lit_lens(), fixed_dist_lens());
        } else if btype == 2 {
            lemma_read_dynamic_pos(b, p);
            if let Some((p2, lit, dist)) = read_dynamic(b, p) {
                lemma_codes_end(b, p2, out, lit, dist);
            }
        }
        if let Some((q, o2)) = r {
            assert(q >= p);
            lemma_after_pos(b, bits(b, pos, 1) == 1, q, o2);
        }
    }
}


pub proof fn lemma_blocks_hdr_past(b: Seq<u8>, pos: int, n: int)
    requires
        pos + 3 > n,
    ensures
        forall|o: Seq<u8>| #[trigger] crate::inflate::past(inflate_blocks(b, pos, o), n),
{
    assert forall|o: Seq<u8>| #[trigger] crate::inflate::past(inflate_blocks(b, pos, o), n) by {
        lemma_blocks_hdr(b, pos, o);
    }
}


/// A block body that decodes needs its first symbol, with its extra bits
/// and (for a match) the distance symbol and its extra bits.
pub proof fn lemma_codes_first(b: Seq<u8>, pos: int, out: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>)
    ensures
        inflate_codes(b, pos, out, lit, dist) matches Some((e, _)) ==> (decode(lit, b, pos) matches Some((s, k))
            && e >= pos + k + extra_of(ALPHA_LIT, s) && (257 <= s <= 285 ==> (decode(
            dist,
            b,
            pos + k + extra_of(ALPHA_LIT, s),
        ) matches Some((ds, dl)) && e >= pos + k + extra_of(ALPHA_LIT, s) + dl + extra_of(ALPHA_DIST, ds)))),
{
    match decode(lit, b, pos) {
        None => {},
        Some((sym, l)) => {
            let p1 = pos + l;
            if !advances(b, pos, p1) {
            } else if sym < 256 {
                lemma_codes_end(b, p1, out.push(sym as u8), lit, dist);
            } else if sym == 256 {
            } else if sym > 285 {
            } else {
                let le = len_extra()[sym - 257];
                let len = len_base()[sym - 257] + bits(b, p1, le);
                let p2 = p1 + le;
                assert(extra_of(ALPHA_LIT, sym) == le);
                if p2 <= nbits(b) {
                    match decode(dist, b, p2) {
                        None => {},
                        Some((ds, dl)) => {
                            let p3 = p2 + dl;
                            if ds < 30 {
                                let de = dist_extra()[ds as int];
                                let d = dist_base()[ds as int] + bits(b, p3, de);
                                let p4 = p3 + de;
                                assert(extra_of(ALPHA_DIST, ds) == de);
                                if advances(b, pos, p4) && d <= out.len() {
                                    lemma_codes_end(b, p4, copy_match(out, d, len), lit, dist);
                                }
                            }
                        },
                    }
                }
            }
        },
    }
}

/// A stored block with bytes left ends past the decoder's position.
pub proof fn lemma_stored_rest_past(b: Seq<u8>, last: bool, pos: int, n: nat, o: Seq<u8>)
    requires
        n >= 1,
        pos >= 0,
        pos % 8 == 0,
    ensures
        crate::inflate::past(after(b, last, stored_rest(b, pos, n, o)), pos),
{
    lemma_after_none(b, last);
    if let Some((q, o2)) = stored_rest(b, pos, n, o) {
        assert(q > pos);
        lemma_after_pos(b, last, q, o2);
    }
}

} // verus!
