//! The block compressor: a greedy LZ77 parse with a hash table of recent
//! positions (liblz4's fast algorithm), proven to produce a block that
//! `spec::seqs` decodes back to the input, and that follows the format's
//! end-of-block rules.
//!
//! The proof does not depend on what the hash table holds: a candidate it
//! offers is used only after its four bytes have been compared with the
//! input's, so stale or colliding entries cost compression, never
//! correctness. The table stores positions truncated to 16 bits, which is
//! all a 64 KiB window needs.
use crate::spec::*;
use verilith_core::lz::{copy_lits, eq_len, load32};
#[cfg(verus_only)]
use verilith_core::lz::{lemma_le_digit, lemma_lz_copy_is, lemma_lz_copy_len, placed};
#[cfg(verus_only)]
use verilith_core::prims::le_bytes;
use verilith_core::prims::{copy16_in, get, load_u64_le, set};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// liblz4's `LZ4_MAX_INPUT_SIZE`.
pub const MAX_INPUT: usize = 0x7E000000;

/// The hash table for inputs up to 64 KiB: 8192 16-bit positions (16 KiB,
/// as liblz4's).
pub const HASH_SIZE: usize = 8192;

/// The hash table for larger inputs: 4096 32-bit positions (16 KiB, as
/// liblz4's).
pub const BIG_SIZE: usize = 4096;

/// Room that is always enough for a block of `n` bytes.
pub open spec fn bound(n: int) -> int {
    n + n / 255 + 16
}

// ---------------------------------------------------------------------------
// What the compressor writes, as sequences of bytes
// ---------------------------------------------------------------------------

/// The extension bytes for the value `n`: 255s, then the rest.
pub open spec fn enc_ext(n: nat) -> Seq<u8>
    decreases n,
{
    if n >= 255 {
        seq![255u8] + enc_ext((n - 255) as nat)
    } else {
        seq![n as u8]
    }
}

/// The bytes after the token for a length field holding `n`.
pub open spec fn enc_len(n: nat) -> Seq<u8> {
    if n < 15 {
        Seq::empty()
    } else {
        enc_ext((n - 15) as nat)
    }
}

/// The token's 4 bits for a length field holding `n`.
pub open spec fn nib(n: nat) -> nat {
    if n < 15 {
        n
    } else {
        15
    }
}

/// A sequence: literals, then a match of `ml` bytes `off` back.
pub open spec fn enc_seq(lits: Seq<u8>, off: nat, ml: nat) -> Seq<u8> {
    seq![(nib(lits.len()) * 16 + nib((ml - 4) as nat)) as u8] + enc_len(lits.len()) + lits + seq![
        (off % 256) as u8,
        (off / 256) as u8,
    ] + enc_len((ml - 4) as nat)
}

/// The last sequence: literals only.
pub open spec fn enc_last(lits: Seq<u8>) -> Seq<u8> {
    seq![(nib(lits.len()) * 16) as u8] + enc_len(lits.len()) + lits
}

pub proof fn lemma_enc_ext_len(n: nat)
    ensures
        enc_ext(n).len() == n / 255 + 1,
    decreases n,
{
    if n >= 255 {
        lemma_enc_ext_len((n - 255) as nat);
    }
}

/// `ext_len` reads back what `enc_ext` wrote.
proof fn lemma_enc_ext(s: Seq<u8>, i: int, n: nat)
    requires
        0 <= i,
        i + enc_ext(n).len() <= s.len(),
        s.subrange(i, i + enc_ext(n).len()) == enc_ext(n),
    ensures
        ext_len(s, i) == Some((n, i + enc_ext(n).len())),
    decreases n,
{
    let e = enc_ext(n);
    lemma_enc_ext_len(n);
    assert(s[i] == s.subrange(i, i + e.len())[0]);
    if n >= 255 {
        let r = enc_ext((n - 255) as nat);
        assert(e[0] == 255);
        assert(e.len() == 1 + r.len());
        assert(s.subrange(i + 1, i + 1 + r.len()) =~= r) by {
            assert forall|x: int| 0 <= x < r.len() implies s.subrange(i + 1, i + 1 + r.len())[x] == r[x] by {
                assert(s.subrange(i, i + e.len())[x + 1] == e[x + 1]);
            }
        }
        lemma_enc_ext(s, i + 1, (n - 255) as nat);
    } else {
        assert(e[0] == n as u8);
    }
}

/// `read_len` reads back what the token and `enc_len` hold.
proof fn lemma_enc_len(s: Seq<u8>, i: int, n: nat)
    requires
        0 <= i,
        i + enc_len(n).len() <= s.len(),
        s.subrange(i, i + enc_len(n).len()) == enc_len(n),
    ensures
        read_len(s, i, nib(n)) == Some((n, i + enc_len(n).len())),
{
    if n >= 15 {
        lemma_enc_ext(s, i, (n - 15) as nat);
    }
}

/// Decoding a sequence the compressor wrote: its literals, then its match.
proof fn lemma_seq_step(s: Seq<u8>, i: int, out: Seq<u8>, strict: Option<nat>, lits: Seq<u8>, off: nat, ml: nat)
    requires
        0 <= i,
        i + enc_seq(lits, off, ml).len() <= s.len(),
        s.subrange(i, i + enc_seq(lits, off, ml).len()) == enc_seq(lits, off, ml),
        1 <= off <= 65535,
        off <= out.len() + lits.len(),
        ml >= 4,
        rules(strict, (out.len() + lits.len()) as int, (out.len() + lits.len() + ml) as int),
    ensures
        seqs(s, i, out, strict) == seqs(s, i + enc_seq(lits, off, ml).len(), lz_copy(out + lits, off as int, ml), strict),
{
    let e = enc_seq(lits, off, ml);
    let ll = lits.len();
    let mc = (ml - 4) as nat;
    let a = enc_len(ll);
    let b = enc_len(mc);
    let j = i + 1 + a.len();
    let k = j + ll;
    let m = k + 2 + b.len();
    let tok = (nib(ll) * 16 + nib(mc)) as u8;
    assert(e.len() == 1 + a.len() + ll + 2 + b.len());
    assert forall|x: int| 0 <= x < e.len() implies s[i + x] == e[x] by {
        assert(s.subrange(i, i + e.len())[x] == e[x]);
    }
    assert(s[i] == tok) by {
        assert(e[0] == tok);
    }
    assert((tok / 16) as nat == nib(ll) && (tok % 16) as nat == nib(mc));
    assert(s.subrange(i + 1, i + 1 + a.len()) =~= a) by {
        assert forall|x: int| 0 <= x < a.len() implies s[i + 1 + x] == a[x] by {
            assert(e[1 + x] == a[x]);
        }
    }
    lemma_enc_len(s, i + 1, ll);
    assert(s.subrange(j, j + ll) =~= lits) by {
        assert forall|x: int| 0 <= x < ll implies s[j + x] == lits[x] by {
            assert(e[1 + a.len() + x] == lits[x]);
        }
    }
    assert(s[k] == (off % 256) as u8) by {
        assert(e[(1 + a.len() + ll) as int] == (off % 256) as u8);
    }
    assert(s[k + 1] == (off / 256) as u8) by {
        assert(e[(1 + a.len() + ll + 1) as int] == (off / 256) as u8);
    }
    assert(le16(s, k) == off);
    assert(s.subrange(k + 2, k + 2 + b.len()) =~= b) by {
        assert forall|x: int| 0 <= x < b.len() implies s[k + 2 + x] == b[x] by {
            assert(e[1 + a.len() + ll + 2 + x] == b[x]);
        }
    }
    lemma_enc_len(s, k + 2, mc);
    assert(mc + 4 == ml);
}

/// Decoding the last sequence.
proof fn lemma_seq_last(s: Seq<u8>, i: int, out: Seq<u8>, strict: Option<nat>, lits: Seq<u8>)
    requires
        0 <= i,
        i + enc_last(lits).len() == s.len(),
        s.subrange(i, i + enc_last(lits).len()) == enc_last(lits),
        strict matches Some(t) ==> out.len() + lits.len() == t,
    ensures
        seqs(s, i, out, strict) == Some(out + lits),
{
    let e = enc_last(lits);
    let ll = lits.len();
    let a = enc_len(ll);
    let j = i + 1 + a.len();
    let tok = (nib(ll) * 16) as u8;
    assert(e.len() == 1 + a.len() + ll);
    assert forall|x: int| 0 <= x < e.len() implies s[i + x] == e[x] by {
        assert(s.subrange(i, i + e.len())[x] == e[x]);
    }
    assert(s[i] == tok) by {
        assert(e[0] == tok);
    }
    assert((tok / 16) as nat == nib(ll));
    assert(s.subrange(i + 1, i + 1 + a.len()) =~= a) by {
        assert forall|x: int| 0 <= x < a.len() implies s[i + 1 + x] == a[x] by {
            assert(e[1 + x] == a[x]);
        }
    }
    lemma_enc_len(s, i + 1, ll);
    assert(s.subrange(j, j + ll) =~= lits) by {
        assert forall|x: int| 0 <= x < ll implies s[j + x] == lits[x] by {
            assert(e[1 + a.len() + x] == lits[x]);
        }
    }
}

/// `s` starts with `p`.
pub open spec fn extends(p: Seq<u8>, s: Seq<u8>) -> bool {
    p.len() <= s.len() && s.subrange(0, p.len() as int) == p
}

/// The compressor's invariant: whatever is written after `p`, decoding
/// the whole from `hist` is decoding from the end of `p` with `out`.
pub open spec fn reach(p: Seq<u8>, hist: Seq<u8>, out: Seq<u8>, strict: Option<nat>) -> bool {
    forall|s: Seq<u8>| #[trigger]
        extends(p, s) ==> seqs(s, 0, hist, strict) == seqs(s, p.len() as int, out, strict)
}

proof fn lemma_reach_step(
    p: Seq<u8>,
    hist: Seq<u8>,
    out: Seq<u8>,
    strict: Option<nat>,
    lits: Seq<u8>,
    off: nat,
    ml: nat,
)
    requires
        reach(p, hist, out, strict),
        1 <= off <= 65535,
        off <= out.len() + lits.len(),
        ml >= 4,
        rules(strict, (out.len() + lits.len()) as int, (out.len() + lits.len() + ml) as int),
    ensures
        reach(p + enc_seq(lits, off, ml), hist, lz_copy(out + lits, off as int, ml), strict),
{
    let e = enc_seq(lits, off, ml);
    let p2 = p + e;
    assert forall|s: Seq<u8>| #[trigger] extends(p2, s) implies seqs(s, 0, hist, strict) == seqs(
        s,
        p2.len() as int,
        lz_copy(out + lits, off as int, ml),
        strict,
    ) by {
        assert(s.subrange(0, p.len() as int) =~= p) by {
            assert forall|x: int| 0 <= x < p.len() implies s[x] == p[x] by {
                assert(s.subrange(0, p2.len() as int)[x] == p2[x]);
            }
        }
        assert(extends(p, s));
        assert(s.subrange(p.len() as int, (p.len() + e.len()) as int) =~= e) by {
            assert forall|x: int| 0 <= x < e.len() implies s[p.len() + x] == e[x] by {
                assert(s.subrange(0, p2.len() as int)[p.len() + x] == p2[p.len() + x]);
            }
        }
        lemma_seq_step(s, p.len() as int, out, strict, lits, off, ml);
    }
}

proof fn lemma_reach_last(p: Seq<u8>, hist: Seq<u8>, out: Seq<u8>, strict: Option<nat>, lits: Seq<u8>)
    requires
        reach(p, hist, out, strict),
        strict matches Some(t) ==> out.len() + lits.len() == t,
    ensures
        seqs(p + enc_last(lits), 0, hist, strict) == Some(out + lits),
{
    let e = enc_last(lits);
    let s = p + e;
    assert(s.subrange(0, p.len() as int) =~= p);
    assert(extends(p, s));
    assert(s.subrange(p.len() as int, (p.len() + e.len()) as int) =~= e);
    lemma_seq_last(s, p.len() as int, out, strict, lits);
}

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// Writes `enc_ext(v)` at `d`.
fn put_ext(dst: &mut [u8], d: usize, v: usize) -> (d2: usize)
    requires
        d + v / 255 + 1 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        d2 == d + v / 255 + 1,
        final(dst)@.subrange(0, d2 as int) == old(dst)@.subrange(0, d as int) + enc_ext(v as nat),
{
    let n = dst.len();
    let mut p = d;
    let mut r = v;
    let ghost goal = old(dst)@.subrange(0, d as int) + enc_ext(v as nat);
    while r >= 255
        invariant
            dst@.len() == old(dst)@.len(),
            n == dst@.len(),
            p + r / 255 + 1 <= dst@.len(),
            p + r / 255 == d + v / 255,
            dst@.subrange(0, p as int) + enc_ext(r as nat) == goal,
        decreases r,
    {
        let ghost before = dst@;
        set(dst, p, 255);
        proof {
            assert(dst@.subrange(0, p + 1) + enc_ext((r - 255) as nat) =~= before.subrange(0, p as int) + enc_ext(
                r as nat,
            ));
        }
        p = p + 1;
        r = r - 255;
    }
    let ghost before = dst@;
    set(dst, p, r as u8);
    proof {
        assert(dst@.subrange(0, p + 1) =~= before.subrange(0, p as int) + enc_ext(r as nat));
    }
    p + 1
}

/// How many extension bytes a length field holding `n` takes.
fn ext_bytes(n: usize) -> (r: usize)
    ensures
        r == enc_len(n as nat).len(),
        r <= n / 255 + 1,
        r == if n >= 15 {
            (n - 15) / 255 + 1
        } else {
            0
        },
{
    proof {
        if n >= 15 {
            lemma_enc_ext_len((n - 15) as nat);
        }
    }
    if n >= 15 {
        (n - 15) / 255 + 1
    } else {
        0
    }
}

/// Writes a sequence at `d`: the literals `input[anchor..anchor + ll]`,
/// then a match of `ml` bytes `off` back. `None` if it does not fit.
#[inline(always)]
fn emit_seq(dst: &mut [u8], d: usize, input: &[u8], anchor: usize, ll: usize, off: usize, ml: usize) -> (r: Option<
    usize,
>)
    requires
        d <= old(dst)@.len(),
        anchor + ll <= input@.len(),
        ll <= MAX_INPUT,
        4 <= ml <= MAX_INPUT,
        1 <= off <= 65535,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(d2) ==> d2 <= final(dst)@.len() && final(dst)@.subrange(0, d2 as int) == old(dst)@.subrange(
            0,
            d as int,
        ) + enc_seq(input@.subrange(anchor as int, anchor + ll), off as nat, ml as nat),
        r.is_none() ==> final(dst)@ == old(dst)@,
{
    let mc = ml - 4;
    let lx = ext_bytes(ll);
    let mx = ext_bytes(mc);
    let need = 1 + lx + ll + 2 + mx;
    if need > dst.len() - d {
        return None;
    }
    let l4: u8 = if ll < 15 {
        ll as u8
    } else {
        15
    };
    let m4: u8 = if mc < 15 {
        mc as u8
    } else {
        15
    };
    let ghost lits = input@.subrange(anchor as int, anchor + ll);
    let ghost pre = dst@.subrange(0, d as int);
    let tok = (l4 << 4) | m4;
    proof {
        assert((l4 << 4) | m4 == l4 * 16 + m4) by (bit_vector)
            requires
                l4 < 16,
                m4 < 16,
        ;
    }
    set(dst, d, tok);
    let mut p = d + 1;
    assert(dst@.subrange(0, p as int) =~= pre + seq![tok]);
    if ll >= 15 {
        p = put_ext(dst, p, ll - 15);
    }
    assert(dst@.subrange(0, p as int) =~= pre + seq![tok] + enc_len(ll as nat));
    let ghost s1 = dst@;
    copy_lits(dst, p, input, anchor, ll);
    proof {
        assert(dst@.subrange(0, p + ll) =~= s1.subrange(0, p as int) + lits);
    }
    p = p + ll;
    let ghost s2 = dst@;
    proof {
        assert(off & 0xff == off % 256 && off >> 8 == off / 256) by (bit_vector);
    }
    set(dst, p, (off & 0xff) as u8);
    set(dst, p + 1, (off >> 8) as u8);
    proof {
        assert(dst@.subrange(0, p + 2) =~= s2.subrange(0, p as int) + seq![(off % 256) as u8, (off / 256) as u8]);
    }
    p = p + 2;
    let ghost s3 = dst@;
    if mc >= 15 {
        p = put_ext(dst, p, mc - 15);
    }
    proof {
        assert(dst@.subrange(0, p as int) =~= s3.subrange(0, p - mx) + enc_len(mc as nat));
        assert(dst@.subrange(0, p as int) =~= pre + enc_seq(lits, off as nat, ml as nat));
    }
    Some(p)
}

/// Writes the last sequence at `d`: the literals
/// `input[anchor..anchor + ll]`. `None` if it does not fit.
fn emit_last(dst: &mut [u8], d: usize, input: &[u8], anchor: usize, ll: usize) -> (r: Option<usize>)
    requires
        d <= old(dst)@.len(),
        anchor + ll <= input@.len(),
        ll <= MAX_INPUT,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(d2) ==> d2 <= final(dst)@.len() && final(dst)@.subrange(0, d2 as int) == old(dst)@.subrange(
            0,
            d as int,
        ) + enc_last(input@.subrange(anchor as int, anchor + ll)),
        d + 1 + enc_len(ll as nat).len() + ll <= old(dst)@.len() ==> r.is_some(),
        r.is_none() ==> final(dst)@ == old(dst)@,
{
    let lx = ext_bytes(ll);
    let need = 1 + lx + ll;
    if need > dst.len() - d {
        return None;
    }
    let l4: u8 = if ll < 15 {
        ll as u8
    } else {
        15
    };
    let ghost lits = input@.subrange(anchor as int, anchor + ll);
    let ghost pre = dst@.subrange(0, d as int);
    let tok = l4 << 4;
    proof {
        assert(l4 << 4 == l4 * 16) by (bit_vector)
            requires
                l4 < 16,
        ;
    }
    set(dst, d, tok);
    let mut p = d + 1;
    assert(dst@.subrange(0, p as int) =~= pre + seq![tok]);
    if ll >= 15 {
        p = put_ext(dst, p, ll - 15);
    }
    assert(dst@.subrange(0, p as int) =~= pre + seq![tok] + enc_len(ll as nat));
    let ghost s1 = dst@;
    copy_lits(dst, p, input, anchor, ll);
    proof {
        assert(dst@.subrange(0, p + ll) =~= s1.subrange(0, p as int) + lits);
        assert(dst@.subrange(0, p + ll) =~= pre + enc_last(lits));
    }
    Some(p + ll)
}

/// Writes a sequence at `d` as `emit_seq` does, without checking for
/// room, which the caller has. The literals go 16 bytes at a time when
/// they are short, which may write past them (never past the 16 bytes the
/// caller has room for).
#[inline(always)]
fn emit_fast(dst: &mut [u8], d: usize, input: &[u8], anchor: usize, ll: usize, off: usize, ml: usize) -> (d2: usize)
    requires
        anchor + ll <= input@.len(),
        ll <= MAX_INPUT,
        4 <= ml <= MAX_INPUT,
        1 <= off <= 65535,
        d + 1 + enc_len(ll as nat).len() + ll + 2 + enc_len((ml - 4) as nat).len() <= old(dst)@.len(),
        d + 1 + enc_len(ll as nat).len() + 16 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        d2 == d + 1 + enc_len(ll as nat).len() + ll + 2 + enc_len((ml - 4) as nat).len(),
        final(dst)@.subrange(0, d2 as int) == old(dst)@.subrange(0, d as int) + enc_seq(
            input@.subrange(anchor as int, anchor + ll),
            off as nat,
            ml as nat,
        ),
{
    let n = input.len();
    let dn = dst.len();
    let mc = ml - 4;
    proof {
        if ll >= 15 {
            lemma_enc_ext_len((ll - 15) as nat);
        }
        if mc >= 15 {
            lemma_enc_ext_len((mc - 15) as nat);
        }
    }
    let l4: u8 = if ll < 15 {
        ll as u8
    } else {
        15
    };
    let m4: u8 = if mc < 15 {
        mc as u8
    } else {
        15
    };
    let ghost lits = input@.subrange(anchor as int, anchor + ll);
    let ghost pre = dst@.subrange(0, d as int);
    let ghost mx = enc_len(mc as nat).len();
    let tok = (l4 << 4) | m4;
    proof {
        assert((l4 << 4) | m4 == l4 * 16 + m4) by (bit_vector)
            requires
                l4 < 16,
                m4 < 16,
        ;
    }
    set(dst, d, tok);
    let mut p = d + 1;
    assert(dst@.subrange(0, p as int) =~= pre + seq![tok]);
    if ll >= 15 {
        p = put_ext(dst, p, ll - 15);
    }
    assert(dst@.subrange(0, p as int) =~= pre + seq![tok] + enc_len(ll as nat));
    let ghost s1 = dst@;
    if ll <= 16 && n - anchor >= 16 {
        copy16_in(dst, p, input, anchor);
    } else {
        copy_lits(dst, p, input, anchor, ll);
    }
    proof {
        assert(dst@.subrange(0, p + ll) =~= s1.subrange(0, p as int) + lits);
    }
    p = p + ll;
    let ghost s2 = dst@;
    proof {
        assert(off & 0xff == off % 256 && off >> 8 == off / 256) by (bit_vector);
    }
    set(dst, p, (off & 0xff) as u8);
    set(dst, p + 1, (off >> 8) as u8);
    proof {
        assert(dst@.subrange(0, p + 2) =~= s2.subrange(0, p as int) + seq![(off % 256) as u8, (off / 256) as u8]);
    }
    p = p + 2;
    let ghost s3 = dst@;
    if mc >= 15 {
        p = put_ext(dst, p, mc - 15);
    }
    proof {
        assert(dst@.subrange(0, p as int) =~= s3.subrange(0, p - mx) + enc_len(mc as nat));
        assert(dst@.subrange(0, p as int) =~= pre + enc_seq(lits, off as nat, ml as nat));
    }
    p
}

/// Why a buffer of `bound(n)` bytes never fills. A sequence that covers
/// `ll + ml` input bytes takes at most 256/255 times as many, so the
/// output position `d` stays under 256/255 of the input position `a`, and
/// the 16 bytes `bound` adds cover what the last 12 input bytes cannot.
proof fn lemma_room(d: int, a: int, ll: int, ml: int, n: int, len: int, lx: int, mx: int)
    requires
        0 <= d,
        0 <= a,
        0 <= ll,
        4 <= ml,
        255 * d <= 256 * a,
        a + ll + 12 <= n,
        a + ll + ml + 5 <= n,
        len >= bound(n),
        lx == if ll >= 15 {
            (ll - 15) / 255 + 1
        } else {
            0
        },
        mx == if ml >= 19 {
            (ml - 19) / 255 + 1
        } else {
            0
        },
    ensures
        d + 1 + lx + ll + 2 + mx <= len,
        d + 1 + lx + 16 <= len,
        255 * (d + 1 + lx + ll + 2 + mx) <= 256 * (a + ll + ml),
{
    assert(255 * lx <= ll + 240);
    assert(255 * mx <= if ml >= 19 {
        ml + 236
    } else {
        0
    });
    assert(255 * (n / 255) >= n - 254);
}

/// The same for the literals that end a block.
proof fn lemma_room_last(d: int, a: int, ll: int, n: int, len: int, lx: int)
    requires
        0 <= d,
        0 <= a,
        0 <= ll,
        255 * d <= 256 * a,
        a + ll == n,
        len >= bound(n),
        lx == if ll >= 15 {
            (ll - 15) / 255 + 1
        } else {
            0
        },
    ensures
        d + 1 + lx + ll <= len,
{
    assert(255 * lx <= ll + 240);
    assert(255 * (n / 255) >= n - 254);
}

// ---------------------------------------------------------------------------
// Finding matches
// ---------------------------------------------------------------------------

/// liblz4's hash of four bytes.
#[inline(always)]
fn hash4(x: u32) -> (h: usize)
    ensures
        h < HASH_SIZE,
{
    let m = x.wrapping_mul(2654435761u32);
    assert(m >> 19 < 8192) by (bit_vector);
    (m >> 19) as usize
}

/// liblz4's hash of five bytes, which it uses on larger inputs: fewer
/// short matches that cost more than they save.
#[inline(always)]
fn hash5(x: u64) -> (h: usize)
    ensures
        h < BIG_SIZE,
{
    let m = (x << 24).wrapping_mul(889523592379u64);
    assert(m >> 52 < 4096) by (bit_vector);
    (m >> 52) as usize
}

/// Equal 4-byte loads are four equal bytes.
proof fn lemma_load_eq(s: Seq<u8>, a: int, b: int)
    requires
        0 <= a,
        0 <= b,
        a + 4 <= s.len(),
        b + 4 <= s.len(),
        le_bytes(s, a, 4) == le_bytes(s, b, 4),
    ensures
        forall|k: int| 0 <= k < 4 ==> #[trigger] s[a + k] == s[b + k],
{
    assert forall|k: int| 0 <= k < 4 implies #[trigger] s[a + k] == s[b + k] by {
        lemma_le_digit(s, a, 4, k as nat);
        lemma_le_digit(s, b, 4, k as nat);
    }
}

/// The low half of an 8-byte load is the 4-byte load.
proof fn lemma_low32(s: Seq<u8>, i: int, w: u64)
    requires
        0 <= i,
        i + 8 <= s.len(),
        w as nat == le_bytes(s, i, 8),
    ensures
        (w & 0xffff_ffff) as nat == le_bytes(s, i, 4),
{
    reveal_with_fuel(le_bytes, 9);
    let a = le_bytes(s, i, 4);
    let b = le_bytes(s, i + 4, 4);
    assert(le_bytes(s, i, 8) == a + 0x1_0000_0000 * b);
    assert(a < 0x1_0000_0000);
    assert(w & 0xffff_ffff == w % 0x1_0000_0000) by (bit_vector);
}

/// Writes the sequence for a match found at `ip` with the four bytes at
/// `cand`: stretches it backwards over the pending literals and forwards
/// as far as the input agrees, then writes the literals and the match.
/// Gives the new output and input positions, or `None` if `dst` is full.
///
/// `roomy` says `dst` has `bound` bytes, and then nothing is checked.
#[inline(always)]
fn put_match(
    input: &[u8],
    start: usize,
    end: usize,
    anchor: usize,
    ip: usize,
    cand: usize,
    dst: &mut [u8],
    base: usize,
    d: usize,
    roomy: bool,
    Ghost(hist): Ghost<Seq<u8>>,
    Ghost(strict): Ghost<Option<nat>>,
) -> (r: Option<(usize, usize)>)
    requires
        start <= anchor <= ip,
        ip + 12 <= end <= input@.len(),
        end - start <= MAX_INPUT,
        cand < ip,
        ip - cand <= 65535,
        le_bytes(input@, cand as int, 4) == le_bytes(input@, ip as int, 4),
        base <= d <= old(dst)@.len(),
        hist == input@.subrange(0, start as int),
        strict == Some(end as nat),
        reach(old(dst)@.subrange(base as int, d as int), hist, input@.subrange(0, anchor as int), strict),
        roomy ==> 255 * (d - base) <= 256 * (anchor - start) && old(dst)@.len() - base >= bound(end - start),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
        roomy ==> r.is_some(),
        r matches Some((d2, ip2)) ==> {
            &&& d <= d2 <= final(dst)@.len()
            &&& ip + 4 <= ip2 <= end - 5
            &&& reach(final(dst)@.subrange(base as int, d2 as int), hist, input@.subrange(0, ip2 as int), strict)
            &&& roomy ==> 255 * (d2 - base) <= 256 * (ip2 - start)
        },
{
    proof {
        lemma_load_eq(input@, cand as int, ip as int);
    }
    let ra = ip - anchor;
    let rc = cand;
    let maxb = if ra < rc {
        ra
    } else {
        rc
    };
    let mut b: usize = 0;
    while b < maxb && get(input, ip - b - 1) == get(input, cand - b - 1)
        invariant
            b <= maxb,
            maxb <= ip - anchor,
            maxb <= cand,
            cand < ip,
            ip + 12 <= input@.len(),
            forall|k: int| -(b as int) <= k < 4 ==> #[trigger] input@[cand + k] == input@[ip + k],
        decreases maxb - b,
    {
        proof {
            let k0 = -(b as int) - 1;
            assert(input@[cand + k0] == input@[ip + k0]);
        }
        b = b + 1;
    }
    let ip0 = ip - b;
    let more = eq_len(input, cand + 4, ip + 4, end - 5 - (ip + 4));
    let ml = b + 4 + more;
    let ll = ip0 - anchor;
    let off = ip - cand;
    let ghost lits = input@.subrange(anchor as int, ip0 as int);
    let ghost out0 = input@.subrange(0, anchor as int);
    let ghost p0 = dst@.subrange(base as int, d as int);
    let ghost before = dst@;
    let dn = dst.len();
    // Room for the sequence however its lengths are written, and for the
    // 16 bytes a short literal copy writes.
    assert(ll + ml <= MAX_INPUT);
    proof {
        if ll >= 15 {
            lemma_enc_ext_len((ll - 15) as nat);
        }
        if ml >= 19 {
            lemma_enc_ext_len((ml - 19) as nat);
        }
    }
    assert(ll >> 7 == ll / 128 && ml >> 7 == ml / 128) by (bit_vector);
    let fast = roomy || ll + (ll >> 7) + (ml >> 7) + 24 <= dn - d;
    let d2 = if fast {
        if roomy {
            proof {
            if ll >= 15 {
                lemma_enc_ext_len((ll - 15) as nat);
            }
            if ml >= 19 {
                lemma_enc_ext_len((ml - 19) as nat);
            }
            lemma_room(
                d - base,
                anchor - start,
                ll as int,
                ml as int,
                end - start,
                dst@.len() - base,
                enc_len(ll as nat).len() as int,
                enc_len((ml - 4) as nat).len() as int,
            );
            }
        }
        emit_fast(dst, d, input, anchor, ll, off, ml)
    } else {
        match emit_seq(dst, d, input, anchor, ll, off, ml) {
            None => {
                return None;
            },
            Some(x) => x,
        }
    };
    proof {
        let e = enc_seq(lits, off as nat, ml as nat);
        assert(d2 <= dst@.len());
        assert(dst@.subrange(0, d2 as int).len() == (before.subrange(0, d as int) + e).len());
        assert(d2 == d + e.len());
        assert forall|x: int| 0 <= x < d2 implies #[trigger] dst@[x] == (before.subrange(0, d as int) + e)[x] by {
            assert(dst@.subrange(0, d2 as int)[x] == (before.subrange(0, d as int) + e)[x]);
        }
        assert(dst@.subrange(0, base as int) =~= before.subrange(0, base as int));
        assert(dst@.subrange(base as int, d2 as int) =~= p0 + e);
        let o = input@.subrange(0, ip0 as int);
        let r = input@.subrange(0, ip0 + ml);
        assert(out0 + lits =~= o);
        assert forall|j: int| o.len() <= j < r.len() implies #[trigger] r[j] == r[j - off] by {
            let k = j - ip;
            if k < 4 {
                assert(input@[cand + k] == input@[ip + k]);
            } else {
                assert(input@[cand + 4 + (k - 4)] == input@[ip + 4 + (k - 4)]);
            }
        }
        lemma_lz_copy_is(o, r, off as int, ml as nat);
        lemma_reach_step(p0, hist, out0, strict, lits, off as nat, ml as nat);
    }
    Some((d2, ip0 + ml))
}

/// Writes the literals that end the block.
#[inline(always)]
fn finish(
    input: &[u8],
    start: usize,
    end: usize,
    anchor: usize,
    dst: &mut [u8],
    base: usize,
    d: usize,
    roomy: bool,
    Ghost(hist): Ghost<Seq<u8>>,
    Ghost(strict): Ghost<Option<nat>>,
) -> (r: Option<usize>)
    requires
        start <= anchor <= end <= input@.len(),
        end - start <= MAX_INPUT,
        base <= d <= old(dst)@.len(),
        hist == input@.subrange(0, start as int),
        strict == Some(end as nat),
        reach(old(dst)@.subrange(base as int, d as int), hist, input@.subrange(0, anchor as int), strict),
        roomy ==> 255 * (d - base) <= 256 * (anchor - start) && old(dst)@.len() - base >= bound(end - start),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
        roomy ==> r.is_some(),
        r matches Some(n) ==> base <= n <= final(dst)@.len() && block_strict(
            final(dst)@.subrange(base as int, n as int),
            input@.subrange(0, start as int),
            (end - start) as nat,
        ) == Some(input@.subrange(0, end as int)),
{
    let ghost p0 = dst@.subrange(base as int, d as int);
    let ghost before = dst@;
    let ghost out0 = input@.subrange(0, anchor as int);
    let ghost lits = input@.subrange(anchor as int, end as int);
    let ll = end - anchor;
    proof {
        if roomy {
            if ll >= 15 {
                lemma_enc_ext_len((ll - 15) as nat);
            }
            lemma_room_last(
                d - base,
                anchor - start,
                ll as int,
                end - start,
                dst@.len() - base,
                enc_len(ll as nat).len() as int,
            );
        }
    }
    match emit_last(dst, d, input, anchor, ll) {
        None => None,
        Some(n) => {
            proof {
                let e = enc_last(lits);
                assert(dst@.subrange(0, n as int).len() == (before.subrange(0, d as int) + e).len());
                assert(n == d + e.len());
                assert forall|x: int| 0 <= x < n implies #[trigger] dst@[x] == (before.subrange(0, d as int) + e)[x] by {
                    assert(dst@.subrange(0, n as int)[x] == (before.subrange(0, d as int) + e)[x]);
                }
                assert(dst@.subrange(0, base as int) =~= before.subrange(0, base as int));
                assert(dst@.subrange(base as int, n as int) =~= p0 + e);
                lemma_reach_last(p0, hist, out0, strict, lits);
                assert(out0 + lits =~= input@.subrange(0, end as int));
            }
            Some(n)
        },
    }
}

/// The compressor for inputs that, with their history, are at most
/// 64 KiB: positions fit in 16 bits, so the table holds them whole and
/// every entry is a place to look, with nothing to check but its bytes.
#[inline(always)]
fn core_small(
    input: &[u8],
    start: usize,
    end: usize,
    dst: &mut [u8],
    base: usize,
    accel: usize,
    roomy: bool,
) -> (r: Option<usize>)
    requires
        start <= end <= input@.len(),
        end <= 65536,
        1 <= accel <= 65537,
        base <= old(dst)@.len(),
        roomy ==> old(dst)@.len() - base >= bound(end - start),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
        roomy ==> r.is_some(),
        r matches Some(n) ==> base <= n <= final(dst)@.len() && block_strict(
            final(dst)@.subrange(base as int, n as int),
            input@.subrange(0, start as int),
            (end - start) as nat,
        ) == Some(input@.subrange(0, end as int)),
{
    let ghost hist = input@.subrange(0, start as int);
    let ghost strict = Some(end as nat);
    let mut anchor = start;
    let mut d: usize = base;
    proof {
        assert(input@.subrange(0, anchor as int) == hist);
        assert(dst@.subrange(base as int, base as int).len() == 0);
    }
    if end - start >= 13 {
        let mut table = [0u16;HASH_SIZE];
        // A match may not start after `mflimit`.
        let mflimit = end - 12;
        // The first position has nothing before it to match.
        let h0 = hash4(load32(input, start));
        table[h0] = start as u16;
        let mut ip = start + 1;
        loop
            invariant_except_break
                start < ip <= mflimit,
                forall|h: int| 0 <= h < HASH_SIZE ==> (#[trigger] table@[h]) < ip,
            invariant
                dst@.len() == old(dst)@.len(),
                start <= anchor <= ip,
                anchor <= end,
                end <= input@.len(),
                end <= 65536,
                end - start >= 13,
                mflimit == end - 12,
                base <= d <= dst@.len(),
                dst@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
                1 <= accel <= 65537,
                hist == input@.subrange(0, start as int),
                strict == Some(end as nat),
                reach(dst@.subrange(base as int, d as int), hist, input@.subrange(0, anchor as int), strict),
                roomy ==> 255 * (d - base) <= 256 * (anchor - start) && dst@.len() - base >= bound(end - start),
            decreases end - anchor,
        {
            // Look for four bytes seen before, stepping faster the longer
            // nothing is found.
            let mut cand: usize = 0;
            let mut found = false;
            let mut nb: usize = accel << 6;
            assert(64 <= accel << 6 <= 0x40_0040) by (bit_vector)
                requires
                    1 <= accel <= 65537,
            ;
            let ghost ip0 = ip;
            loop
                invariant_except_break
                    !found,
                    ip <= mflimit,
                    forall|h: int| 0 <= h < HASH_SIZE ==> (#[trigger] table@[h]) < ip,
                invariant
                    start <= anchor <= ip,
                    start <= ip0 <= ip,
                    end <= input@.len(),
                    end - start <= MAX_INPUT,
                    end <= 65536,
                    mflimit == end - 12,
                    end - start >= 13,
                    64 <= nb <= 0x40_0040 + (ip - ip0),
                    forall|h: int| 0 <= h < HASH_SIZE ==> (#[trigger] table@[h]) <= ip,
                ensures
                    found ==> ip <= mflimit && cand < ip && le_bytes(input@, cand as int, 4) == le_bytes(
                        input@,
                        ip as int,
                        4,
                    ),
                decreases mflimit - ip,
            {
                let x = load32(input, ip);
                let h = hash4(x);
                let e = table[h] as usize;
                table[h] = ip as u16;
                if load32(input, e) == x {
                    cand = e;
                    found = true;
                    break ;
                }
                let step = nb >> 6;
                assert(nb >> 6 >= 1 && nb >> 6 <= nb) by (bit_vector)
                    requires
                        nb >= 64,
                ;
                nb = nb + 1;
                ip = ip + step;
                if ip > mflimit {
                    break ;
                }
            }
            if !found {
                break ;
            }
            match put_match(input, start, end, anchor, ip, cand, dst, base, d, roomy, Ghost(hist), Ghost(strict)) {
                None => {
                    return None;
                },
                Some((d2, ip2)) => {
                    d = d2;
                    ip = ip2;
                    anchor = ip2;
                },
            }
            if ip > mflimit {
                break ;
            }
            // Remember a position inside the match.
            let h2 = hash4(load32(input, ip - 2));
            table[h2] = (ip - 2) as u16;
        }
    }
    finish(input, start, end, anchor, dst, base, d, roomy, Ghost(hist), Ghost(strict))
}

/// The compressor for larger inputs. The table holds 32-bit positions
/// counted from the start of `input`, all of them before the one being looked at, so an
/// entry is a place to look once it is seen to be within 64 KiB.
#[inline(always)]
fn core_big(
    input: &[u8],
    start: usize,
    end: usize,
    dst: &mut [u8],
    base: usize,
    table: &mut [u32; BIG_SIZE],
    accel: usize,
    roomy: bool,
) -> (r: Option<usize>)
    requires
        start <= end <= input@.len(),
        end - start <= MAX_INPUT,
        end <= 0xf000_0000,
        1 <= accel <= 65537,
        forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] old(table)@[h]) <= start,
        base <= old(dst)@.len(),
        roomy ==> old(dst)@.len() - base >= bound(end - start),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
        roomy ==> r.is_some(),
        forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] final(table)@[h]) <= end,
        r matches Some(n) ==> base <= n <= final(dst)@.len() && block_strict(
            final(dst)@.subrange(base as int, n as int),
            input@.subrange(0, start as int),
            (end - start) as nat,
        ) == Some(input@.subrange(0, end as int)),
{
    let ghost hist = input@.subrange(0, start as int);
    let ghost strict = Some(end as nat);
    let mut anchor = start;
    let mut d: usize = base;
    proof {
        assert(input@.subrange(0, anchor as int) == hist);
        assert(dst@.subrange(base as int, base as int).len() == 0);
    }
    if end - start >= 13 {
        // A match may not start after `mflimit`.
        let mflimit = end - 12;
        // The first position has nothing new before it to match.
        let h0 = hash5(load_u64_le(input, start));
        table[h0] = start as u32;
        let mut ip = start + 1;
        loop
            invariant_except_break
                start < ip <= mflimit,
                forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] table@[h]) < ip,
            invariant
                dst@.len() == old(dst)@.len(),
                start <= anchor <= ip,
                anchor <= end,
                end <= input@.len(),
                end - start <= MAX_INPUT,
                end <= 0xf000_0000,
                end - start >= 13,
                mflimit == end - 12,
                base <= d <= dst@.len(),
                dst@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
                1 <= accel <= 65537,
                hist == input@.subrange(0, start as int),
                strict == Some(end as nat),
                forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] table@[h]) <= end,
                reach(dst@.subrange(base as int, d as int), hist, input@.subrange(0, anchor as int), strict),
                roomy ==> 255 * (d - base) <= 256 * (anchor - start) && dst@.len() - base >= bound(end - start),
            decreases end - anchor,
        {
            // Look for four bytes seen before, stepping faster the longer
            // nothing is found.
            let mut cand: usize = 0;
            let mut found = false;
            let mut nb: usize = accel << 6;
            assert(64 <= accel << 6 <= 0x40_0040) by (bit_vector)
                requires
                    1 <= accel <= 65537,
            ;
            let ghost ip0 = ip;
            loop
                invariant_except_break
                    !found,
                    ip <= mflimit,
                    forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] table@[h]) < ip,
                invariant
                    start <= anchor <= ip,
                    start <= ip0 <= ip,
                    end <= input@.len(),
                    end - start <= MAX_INPUT,
                    end <= 0xf000_0000,
                    mflimit == end - 12,
                    end - start >= 13,
                    64 <= nb <= 0x40_0040 + (ip - ip0),
                    forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] table@[h]) <= end,
                    forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] table@[h]) <= ip,
                ensures
                    found ==> ip <= mflimit && cand < ip && ip - cand <= 65535 && le_bytes(input@, cand as int, 4) == le_bytes(
                        input@,
                        ip as int,
                        4,
                    ),
                decreases mflimit - ip,
            {
                let w = load_u64_le(input, ip);
                assert(w & 0xffff_ffff <= 0xffff_ffff) by (bit_vector);
                let x = (w & 0xffff_ffff) as u32;
                proof {
                    lemma_low32(input@, ip as int, w);
                }
                let h = hash5(w);
                let cur = ip;
                let e = table[h] as usize;
                table[h] = cur as u32;
                if cur - e <= 65535 && load32(input, e) == x {
                    cand = e;
                    found = true;
                    break ;
                }
                let step = nb >> 6;
                assert(nb >> 6 >= 1 && nb >> 6 <= nb) by (bit_vector)
                    requires
                        nb >= 64,
                ;
                nb = nb + 1;
                ip = ip + step;
                if ip > mflimit {
                    break ;
                }
            }
            if !found {
                break ;
            }
            match put_match(input, start, end, anchor, ip, cand, dst, base, d, roomy, Ghost(hist), Ghost(strict)) {
                None => {
                    return None;
                },
                Some((d2, ip2)) => {
                    d = d2;
                    ip = ip2;
                    anchor = ip2;
                },
            }
            if ip > mflimit {
                break ;
            }
            // Remember a position inside the match.
            let h2 = hash5(load_u64_le(input, ip - 2));
            table[h2] = (ip - 2) as u32;
        }
    }
    finish(input, start, end, anchor, dst, base, d, roomy, Ghost(hist), Ghost(strict))
}

/// Whether `len` bytes are room enough for any block of `n`.
#[inline(always)]
fn has_room(len: usize, n: usize) -> (r: bool)
    requires
        n <= MAX_INPUT,
    ensures
        r == (len >= bound(n as int)),
{
    len >= n + n / 255 + 16
}

/// Compresses `input[start..end]` into `dst` from `base` on as one block,
/// when it and its history `input[lo..start]` are at most 64 KiB together.
///
/// `Some(n)`: `dst[base..n]` is a block that decodes to
/// `input[start..end]` after that history, and follows the end-of-block
/// rules. `None`: `dst` is too small, which `bound(end - start)` bytes
/// after `base` never are. `dst[..base]` is left as it was.
pub fn compress_small(
    input: &[u8],
    lo: usize,
    start: usize,
    end: usize,
    dst: &mut [u8],
    base: usize,
    accel: usize,
) -> (r: Option<usize>)
    requires
        lo <= start <= end <= input@.len(),
        end - lo <= 65536,
        1 <= accel <= 65537,
        base <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
        old(dst)@.len() - base >= bound(end - start) ==> r.is_some(),
        r matches Some(n) ==> base <= n <= final(dst)@.len() && block_strict(
            final(dst)@.subrange(base as int, n as int),
            input@.subrange(lo as int, start as int),
            (end - start) as nat,
        ) == Some(input@.subrange(lo as int, end as int)),
{
    let w = slice_subrange(input, lo, end);
    proof {
        assert(w@.subrange(0, start - lo) =~= input@.subrange(lo as int, start as int));
        assert(w@.subrange(0, end - lo) =~= input@.subrange(lo as int, end as int));
    }
    if has_room(dst.len() - base, end - start) {
        core_small(w, start - lo, end - lo, dst, base, accel, true)
    } else {
        core_small(w, start - lo, end - lo, dst, base, accel, false)
    }
}

/// Compresses `input[start..end]` into `dst` from `base` on as one block.
/// Matches may reach back to `lo`: `input[lo..start]` is the history the
/// decoder will have (earlier blocks, or nothing when `lo == start`).
///
/// `Some(n)`: `dst[base..n]` is a block that decodes to
/// `input[start..end]` after that history, and follows the end-of-block
/// rules. `None`: `dst` is too small, which `bound(end - start)` bytes
/// after `base` never are. `dst[..base]` is left as it was.
///
/// `table` holds positions counted from `lo`, none past `start`: all
/// zeros, or what an earlier call with the same `input` and `lo` left.
/// `accel` is liblz4's acceleration (1 is the default): larger skips
/// through incompressible data faster.
pub fn compress_block(
    input: &[u8],
    lo: usize,
    start: usize,
    end: usize,
    dst: &mut [u8],
    base: usize,
    table: &mut [u32; BIG_SIZE],
    accel: usize,
) -> (r: Option<usize>)
    requires
        lo <= start <= end <= input@.len(),
        end - start <= MAX_INPUT,
        end - lo <= 0xf000_0000,
        1 <= accel <= 65537,
        base <= old(dst)@.len(),
        forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] old(table)@[h]) <= start - lo,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
        old(dst)@.len() - base >= bound(end - start) ==> r.is_some(),
        forall|h: int| 0 <= h < BIG_SIZE ==> (#[trigger] final(table)@[h]) <= end - lo,
        r matches Some(n) ==> base <= n <= final(dst)@.len() && block_strict(
            final(dst)@.subrange(base as int, n as int),
            input@.subrange(lo as int, start as int),
            (end - start) as nat,
        ) == Some(input@.subrange(lo as int, end as int)),
{
    if end - lo <= 65536 {
        compress_small(input, lo, start, end, dst, base, accel)
    } else {
        let w = slice_subrange(input, lo, end);
        proof {
            assert(w@.subrange(0, start - lo) =~= input@.subrange(lo as int, start as int));
            assert(w@.subrange(0, end - lo) =~= input@.subrange(lo as int, end as int));
        }
        if has_room(dst.len() - base, end - start) {
            core_big(w, start - lo, end - lo, dst, base, table, accel, true)
        } else {
            core_big(w, start - lo, end - lo, dst, base, table, accel, false)
        }
    }
}

} // verus!

verus! {

/// liblz4's `LZ4_compressBound`: room that is always enough for a block
/// of `n` bytes (0 if `n` is over `MAX_INPUT`).
pub fn compress_bound(n: usize) -> (r: usize)
    ensures
        n <= MAX_INPUT ==> r == bound(n as int),
{
    if n > MAX_INPUT {
        0
    } else {
        n + n / 255 + 16
    }
}

/// Compresses `input` into `dst` as one block. `Some(n)`: `dst[..n]` is
/// a block that decodes to `input` and follows the end-of-block rules.
/// `None`: `input` is longer than `MAX_INPUT`, or `dst` is too small,
/// which `compress_bound(input.len())` bytes never are.
pub fn compress_into(input: &[u8], dst: &mut [u8], accel: usize) -> (r: Option<usize>)
    ensures
        final(dst)@.len() == old(dst)@.len(),
        input@.len() <= MAX_INPUT && old(dst)@.len() >= bound(input@.len() as int) ==> r.is_some(),
        r matches Some(n) ==> n <= final(dst)@.len() && block_strict(
            final(dst)@.subrange(0, n as int),
            Seq::empty(),
            input@.len(),
        ) == Some(input@),
{
    let n = input.len();
    if n > MAX_INPUT {
        return None;
    }
    let a = if accel < 1 {
        1
    } else if accel > 65537 {
        65537
    } else {
        accel
    };
    proof {
        assert(input@.subrange(0, 0) =~= Seq::empty());
        assert(input@.subrange(0, n as int) =~= input@);
    }
    if n <= 65536 {
        compress_small(input, 0, 0, n, dst, 0, a)
    } else {
        let mut table = [0u32;BIG_SIZE];
        compress_block(input, 0, 0, n, dst, 0, &mut table, a)
    }
}

/// Compresses `input` into `dst` from `base` on as one block at the
/// default speed, leaving `dst[..base]` as it was. `Some(n)`:
/// `dst[base..n]` is a block that decodes to `input`. `None`: `input` is
/// longer than `MAX_INPUT`, or `dst` is too small.
pub fn compress_at(input: &[u8], dst: &mut [u8], base: usize) -> (r: Option<usize>)
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(n) ==> base <= n <= final(dst)@.len() && final(dst)@.subrange(0, base as int) == old(
            dst,
        )@.subrange(0, base as int) && block_strict(
            final(dst)@.subrange(base as int, n as int),
            Seq::empty(),
            input@.len(),
        ) == Some(input@),
{
    let n = input.len();
    if n > MAX_INPUT || base > dst.len() {
        return None;
    }
    proof {
        assert(input@.subrange(0, 0) =~= Seq::empty());
        assert(input@.subrange(0, n as int) =~= input@);
    }
    if n <= 65536 {
        compress_small(input, 0, 0, n, dst, base, 1)
    } else {
        let mut table = [0u32;BIG_SIZE];
        compress_block(input, 0, 0, n, dst, base, &mut table, 1)
    }
}

/// A match copies the same bytes whatever comes before its history.
pub proof fn lemma_lz_copy_pre(pre: Seq<u8>, out: Seq<u8>, off: int, n: nat)
    requires
        1 <= off <= out.len(),
    ensures
        lz_copy(pre + out, off, n) == pre + lz_copy(out, off, n),
    decreases n,
{
    if n > 0 {
        let x = out[out.len() - off];
        assert((pre + out)[(pre + out).len() - off] == x);
        assert((pre + out).push(x) =~= pre + out.push(x));
        lemma_lz_copy_pre(pre, out.push(x), off, (n - 1) as nat);
    }
}

/// A block decodes the same with more history before the history it was
/// made for.
pub proof fn lemma_seqs_pre(s: Seq<u8>, i: int, pre: Seq<u8>, out: Seq<u8>, t: nat)
    ensures
        seqs(s, i, out, Some(t)) matches Some(o) ==> seqs(s, i, pre + out, Some(t + pre.len())) == Some(pre + o),
    decreases s.len() - i,
{
    if 0 <= i < s.len() {
        let token = s[i];
        match read_len(s, i + 1, (token / 16) as nat) {
            None => {},
            Some((ll, j)) => {
                lemma_ext_len_next(s, i + 1);
                if j + ll <= s.len() {
                    let lits = s.subrange(j, j + ll);
                    let out1 = out + lits;
                    assert((pre + out) + lits =~= pre + out1);
                    let k = j + ll;
                    if k != s.len() && k + 2 <= s.len() {
                        lemma_ext_len_next(s, k + 2);
                        let off = le16(s, k);
                        match read_len(s, k + 2, (token % 16) as nat) {
                            None => {},
                            Some((ml, m)) => {
                                if off != 0 && off <= out1.len() {
                                    lemma_lz_copy_pre(pre, out1, off as int, ml + 4);
                                    lemma_seqs_pre(s, m, pre, lz_copy(out1, off as int, ml + 4), t);
                                }
                            },
                        }
                    }
                }
            },
        }
    }
}

/// A block that follows the end-of-block rules is a block.
pub proof fn lemma_strict_block(s: Seq<u8>, i: int, out: Seq<u8>, t: nat)
    ensures
        seqs(s, i, out, Some(t)) matches Some(o) ==> seqs(s, i, out, None) == Some(o),
    decreases s.len() - i,
{
    if 0 <= i < s.len() {
        let token = s[i];
        match read_len(s, i + 1, (token / 16) as nat) {
            None => {},
            Some((ll, j)) => {
                lemma_ext_len_next(s, i + 1);
                if j + ll <= s.len() {
                    let out1 = out + s.subrange(j, j + ll);
                    let k = j + ll;
                    if k != s.len() && k + 2 <= s.len() {
                        lemma_ext_len_next(s, k + 2);
                        let off = le16(s, k);
                        match read_len(s, k + 2, (token % 16) as nat) {
                            None => {},
                            Some((ml, m)) => {
                                lemma_strict_block(s, m, lz_copy(out1, off as int, ml + 4), t);
                            },
                        }
                    }
                }
            },
        }
    }
}

} // verus!
