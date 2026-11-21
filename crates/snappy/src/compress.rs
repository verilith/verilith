//! The compressor: the input is cut into 64 KiB fragments, each parsed
//! greedily with a hash table of recent positions (as google/snappy
//! does), proven to produce a buffer that `spec::decompress` turns back
//! into the input.
//!
//! The proof does not depend on what the hash table holds: a candidate it
//! offers is used only after its four bytes have been compared with the
//! input's, so stale or colliding entries cost compression, never
//! correctness.
use crate::spec::*;
use verilith_core::lz::{copy_lits, eq_len, load32};
#[cfg(verus_only)]
use verilith_core::lz::{lemma_le_digit, lemma_lz_copy_is, lemma_lz_copy_len, lemma_word_byte, placed};
#[cfg(verus_only)]
use verilith_core::prims::le_bytes;
use verilith_core::prims::{copy16_in, load_u64_le, pick, get, set};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The hash table: 16384 positions inside a fragment.
pub const HASH_SIZE: usize = 16384;

/// A fragment: matches stay inside it, so offsets fit in 16 bits.
pub const FRAGMENT: usize = 65536;

// ---------------------------------------------------------------------------
// What the compressor writes, as sequences of bytes
// ---------------------------------------------------------------------------

/// The preamble for the length `n`.
pub open spec fn enc_varint(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 128 {
        seq![n as u8]
    } else {
        seq![(n % 128 + 128) as u8] + enc_varint(n / 128)
    }
}

/// What still fits in a varint after `k` bytes.
pub open spec fn varint_limit(k: nat) -> nat {
    if k == 0 {
        0x1_0000_0000
    } else if k == 1 {
        0x200_0000
    } else if k == 2 {
        0x4_0000
    } else if k == 3 {
        0x800
    } else if k == 4 {
        0x10
    } else {
        0
    }
}

/// `varint` reads back what `enc_varint` wrote.
proof fn lemma_varint(s: Seq<u8>, i: int, k: nat, n: nat)
    requires
        0 <= i,
        i + enc_varint(n).len() <= s.len(),
        s.subrange(i, i + enc_varint(n).len()) == enc_varint(n),
        n < varint_limit(k),
    ensures
        varint(s, i, k) == Some((n, i + enc_varint(n).len())),
    decreases n,
{
    let e = enc_varint(n);
    assert(s[i] == s.subrange(i, i + e.len())[0]);
    if n >= 128 {
        let r = enc_varint(n / 128);
        assert(e[0] == (n % 128 + 128) as u8);
        assert(e.len() == 1 + r.len());
        assert(s.subrange(i + 1, i + 1 + r.len()) =~= r) by {
            assert forall|x: int| 0 <= x < r.len() implies s.subrange(i + 1, i + 1 + r.len())[x] == r[x] by {
                assert(s.subrange(i, i + e.len())[x + 1] == e[x + 1]);
            }
        }
        lemma_varint(s, i + 1, k + 1, n / 128);
    } else {
        assert(e[0] == n as u8);
    }
}

/// A literal element (1 to 65536 bytes).
pub open spec fn enc_lit(lits: Seq<u8>) -> Seq<u8> {
    let n1 = (lits.len() - 1) as nat;
    if n1 < 60 {
        seq![(n1 * 4) as u8] + lits
    } else if n1 < 256 {
        seq![240u8, n1 as u8] + lits
    } else {
        seq![244u8, (n1 % 256) as u8, (n1 / 256) as u8] + lits
    }
}

/// A copy element (4 to 64 bytes from 1 to 65535 back).
pub open spec fn enc_copy(off: nat, len: nat) -> Seq<u8> {
    if len < 12 && off < 2048 {
        seq![(1 + (len - 4) * 4 + (off / 256) * 32) as u8, (off % 256) as u8]
    } else {
        seq![(2 + (len - 1) * 4) as u8, (off % 256) as u8, (off / 256) as u8]
    }
}

/// Decoding a literal the compressor wrote.
proof fn lemma_lit_step(s: Seq<u8>, i: int, out: Seq<u8>, n: nat, lits: Seq<u8>)
    requires
        0 <= i,
        i + enc_lit(lits).len() <= s.len(),
        s.subrange(i, i + enc_lit(lits).len()) == enc_lit(lits),
        1 <= lits.len() <= 65536,
    ensures
        elems(s, i, out, n) == elems(s, i + enc_lit(lits).len(), out + lits, n),
{
    let e = enc_lit(lits);
    let n1 = (lits.len() - 1) as nat;
    let nb: int = if n1 < 60 {
        0
    } else if n1 < 256 {
        1
    } else {
        2
    };
    assert(e.len() == 1 + nb + lits.len());
    assert forall|x: int| 0 <= x < e.len() implies s[i + x] == e[x] by {
        assert(s.subrange(i, i + e.len())[x] == e[x]);
    }
    assert(s[i] == e[0]);
    let j = i + 1 + nb;
    assert(s.subrange(j, j + lits.len()) =~= lits) by {
        assert forall|x: int| 0 <= x < lits.len() implies s[j + x] == lits[x] by {
            assert(e[1 + nb + x] == lits[x]);
        }
    }
    reveal_with_fuel(le, 3);
    if n1 >= 60 {
        assert(s[i + 1] == e[1]);
        if n1 >= 256 {
            assert(s[i + 2] == e[2]);
            assert(le(s, i + 1, 2) == n1);
        } else {
            assert(le(s, i + 1, 1) == n1);
        }
    }
}

/// Decoding a copy the compressor wrote.
#[verifier::rlimit(200)]
proof fn lemma_copy_step(s: Seq<u8>, i: int, out: Seq<u8>, n: nat, off: nat, len: nat)
    requires
        0 <= i,
        i + enc_copy(off, len).len() <= s.len(),
        s.subrange(i, i + enc_copy(off, len).len()) == enc_copy(off, len),
        1 <= off <= 65535,
        off <= out.len(),
        4 <= len <= 64,
    ensures
        elems(s, i, out, n) == elems(s, i + enc_copy(off, len).len(), lz_copy(out, off as int, len), n),
{
    let e = enc_copy(off, len);
    assert forall|x: int| 0 <= x < e.len() implies s[i + x] == e[x] by {
        assert(s.subrange(i, i + e.len())[x] == e[x]);
    }
    assert(s[i] == e[0]);
    assert(s[i + 1] == e[1]);
    reveal_with_fuel(le, 3);
    if len < 12 && off < 2048 {
        let tag = (1 + (len - 4) * 4 + (off / 256) * 32) as nat;
        assert(tag % 4 == 1);
        assert((tag / 4) % 8 == len - 4);
        assert((tag / 4) / 8 == off / 256);
    } else {
        assert(s[i + 2] == e[2]);
        let tag = (2 + (len - 1) * 4) as nat;
        assert(tag % 4 == 2);
        assert(tag / 4 == len - 1);
        assert(le(s, i + 1, 2) == off);
    }
}

/// `s` starts with `p`.
pub open spec fn extends(p: Seq<u8>, s: Seq<u8>) -> bool {
    p.len() <= s.len() && s.subrange(0, p.len() as int) == p
}

/// The compressor's invariant: whatever is written after `p`, decoding
/// the elements from `i0` is decoding from the end of `p` with `out`.
pub open spec fn reach(p: Seq<u8>, i0: int, out: Seq<u8>, n: nat) -> bool {
    forall|s: Seq<u8>| #[trigger]
        extends(p, s) ==> elems(s, i0, Seq::empty(), n) == elems(s, p.len() as int, out, n)
}

proof fn lemma_reach_lit(p: Seq<u8>, i0: int, out: Seq<u8>, n: nat, lits: Seq<u8>)
    requires
        reach(p, i0, out, n),
        1 <= lits.len() <= 65536,
    ensures
        reach(p + enc_lit(lits), i0, out + lits, n),
{
    let e = enc_lit(lits);
    let p2 = p + e;
    assert forall|s: Seq<u8>| #[trigger] extends(p2, s) implies elems(s, i0, Seq::empty(), n) == elems(
        s,
        p2.len() as int,
        out + lits,
        n,
    ) by {
        assert forall|x: int| 0 <= x < p2.len() implies s[x] == p2[x] by {
            assert(s.subrange(0, p2.len() as int)[x] == p2[x]);
        }
        assert(s.subrange(0, p.len() as int) =~= p);
        assert(extends(p, s));
        assert(s.subrange(p.len() as int, (p.len() + e.len()) as int) =~= e);
        lemma_lit_step(s, p.len() as int, out, n, lits);
    }
}

proof fn lemma_reach_copy(p: Seq<u8>, i0: int, out: Seq<u8>, n: nat, off: nat, len: nat)
    requires
        reach(p, i0, out, n),
        1 <= off <= 65535,
        off <= out.len(),
        4 <= len <= 64,
    ensures
        reach(p + enc_copy(off, len), i0, lz_copy(out, off as int, len), n),
{
    let e = enc_copy(off, len);
    let p2 = p + e;
    assert forall|s: Seq<u8>| #[trigger] extends(p2, s) implies elems(s, i0, Seq::empty(), n) == elems(
        s,
        p2.len() as int,
        lz_copy(out, off as int, len),
        n,
    ) by {
        assert forall|x: int| 0 <= x < p2.len() implies s[x] == p2[x] by {
            assert(s.subrange(0, p2.len() as int)[x] == p2[x]);
        }
        assert(s.subrange(0, p.len() as int) =~= p);
        assert(extends(p, s));
        assert(s.subrange(p.len() as int, (p.len() + e.len()) as int) =~= e);
        lemma_copy_step(s, p.len() as int, out, n, off, len);
    }
}

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// Writes the literal `input[a..a + len]` at `d`. `None` if it may not
/// fit.
#[inline(always)]
fn emit_literal(dst: &mut [u8], d: usize, input: &[u8], a: usize, len: usize) -> (r: Option<usize>)
    requires
        d <= old(dst)@.len(),
        a + len <= input@.len(),
        1 <= len <= 65536,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(d2) ==> d2 <= final(dst)@.len() && final(dst)@.subrange(0, d2 as int) == old(dst)@.subrange(
            0,
            d as int,
        ) + enc_lit(input@.subrange(a as int, a + len)),
{
    let ghost lits = input@.subrange(a as int, a + len);
    let ghost pre = dst@.subrange(0, d as int);
    // The usual literal: one tag byte and one 16-byte copy.
    if len <= 16 && dst.len() - d >= 17 && input.len() - a >= 16 {
        set(dst, d, ((len - 1) * 4) as u8);
        copy16_in(dst, d + 1, input, a);
        assert(dst@.subrange(0, d + 1 + len) =~= pre + enc_lit(lits));
        return Some(d + 1 + len);
    }
    if dst.len() - d < len + 3 {
        return None;
    }
    let n1 = len - 1;
    let mut p = d;
    if n1 < 60 {
        set(dst, p, (n1 * 4) as u8);
        p = p + 1;
        assert(dst@.subrange(0, p as int) =~= pre + seq![(n1 * 4) as u8]);
    } else if n1 < 256 {
        set(dst, p, 240);
        set(dst, p + 1, n1 as u8);
        p = p + 2;
        assert(dst@.subrange(0, p as int) =~= pre + seq![240u8, n1 as u8]);
    } else {
        set(dst, p, 244);
        set(dst, p + 1, (n1 % 256) as u8);
        set(dst, p + 2, (n1 / 256) as u8);
        p = p + 3;
        assert(dst@.subrange(0, p as int) =~= pre + seq![244u8, (n1 % 256) as u8, (n1 / 256) as u8]);
    }
    let ghost s1 = dst@;
    copy_lits(dst, p, input, a, len);
    proof {
        assert(dst@.subrange(0, p + len) =~= s1.subrange(0, p as int) + lits);
        assert(dst@.subrange(0, p + len) =~= pre + enc_lit(lits));
    }
    Some(p + len)
}

/// Writes a copy of `len` bytes from `off` back at `d`. `None` if it
/// may not fit.
#[inline(always)]
fn emit_copy(dst: &mut [u8], d: usize, off: usize, len: usize) -> (r: Option<usize>)
    requires
        d <= old(dst)@.len(),
        1 <= off <= 65535,
        4 <= len <= 64,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(d2) ==> d2 <= final(dst)@.len() && final(dst)@.subrange(0, d2 as int) == old(dst)@.subrange(
            0,
            d as int,
        ) + enc_copy(off as nat, len as nat),
{
    if dst.len() - d < 3 {
        return None;
    }
    let ghost pre = dst@.subrange(0, d as int);
    // Which of the two forms is not predictable, so there is no branch on
    // it: `c` is 1 for the short form, three bytes are written either
    // way, and the third is left behind when the form has two.
    let short = (len < 12) & (off < 2048);
    assert((off >> 8) & 7 <= 7 && off >> 8 == off / 256 && (off < 2048 ==> (off >> 8) & 7 == off / 256))
        by (bit_vector)
        requires
            off <= 65535,
    ;
    let l4 = (len - 4) & 7;
    assert(l4 <= 7 && (len < 12 ==> l4 == len - 4)) by (bit_vector)
        requires
            4 <= len <= 64,
            l4 == sub(len, 4) & 7,
    ;
    let tag = pick(short, 1 + l4 * 4 + ((off >> 8) & 7) * 32, 2 + (len - 1) * 4);
    let c = pick(short, 1, 0);
    set(dst, d, tag as u8);
    set(dst, d + 1, (off % 256) as u8);
    set(dst, d + 2, (off >> 8) as u8);
    let d2 = d + 3 - c;
    assert(dst@.subrange(0, d2 as int) =~= pre + enc_copy(off as nat, len as nat));
    Some(d2)
}

/// Writes one copy element for `input[ip..ip + len]`, which repeats what
/// is `off` back.
#[inline(always)]
fn emit_copy_at(
    dst: &mut [u8],
    d: usize,
    input: &[u8],
    ip: usize,
    off: usize,
    len: usize,
    Ghost(i0): Ghost<int>,
    Ghost(n): Ghost<nat>,
    Ghost(hi): Ghost<int>,
) -> (r: Option<usize>)
    requires
        d <= old(dst)@.len(),
        1 <= off <= 65535,
        off <= ip,
        4 <= len <= 64,
        ip + len <= hi <= input@.len(),
        forall|k: int| ip <= k < hi ==> #[trigger] input@[k] == input@[k - off],
        reach(old(dst)@.subrange(0, d as int), i0, input@.subrange(0, ip as int), n),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(d2) ==> d2 <= final(dst)@.len() && reach(
            final(dst)@.subrange(0, d2 as int),
            i0,
            input@.subrange(0, ip + len),
            n,
        ),
        r matches Some(d2) ==> d <= d2 && final(dst)@.subrange(0, d as int) == old(dst)@.subrange(0, d as int),
{
    let ghost p0 = dst@.subrange(0, d as int);
    let r = emit_copy(dst, d, off, len);
    proof {
        if r.is_some() {
            let d2 = r.unwrap();
            assert(dst@.subrange(0, d as int) =~= dst@.subrange(0, d2 as int).subrange(0, d as int));
        }
        let o = input@.subrange(0, ip as int);
        let t = input@.subrange(0, ip + len);
        assert forall|j: int| o.len() <= j < t.len() implies #[trigger] t[j] == t[j - off] by {
            assert(input@[j] == input@[j - off]);
        }
        lemma_lz_copy_is(o, t, off as int, len as nat);
        lemma_reach_copy(p0, i0, o, n, off as nat, len as nat);
    }
    r
}

/// Writes copy elements for the match `input[ip..ip + len]`, `off` back:
/// 64 bytes at a time, keeping at least 4 for the last.
fn emit_match(
    dst: &mut [u8],
    d: usize,
    input: &[u8],
    ip: usize,
    off: usize,
    len: usize,
    Ghost(i0): Ghost<int>,
    Ghost(n): Ghost<nat>,
) -> (r: Option<usize>)
    requires
        d <= old(dst)@.len(),
        1 <= off <= 65535,
        off <= ip,
        4 <= len <= 65536,
        ip + len <= input@.len(),
        forall|k: int| ip <= k < ip + len ==> #[trigger] input@[k] == input@[k - off],
        reach(old(dst)@.subrange(0, d as int), i0, input@.subrange(0, ip as int), n),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(d2) ==> d2 <= final(dst)@.len() && reach(
            final(dst)@.subrange(0, d2 as int),
            i0,
            input@.subrange(0, ip + len),
            n,
        ),
        r matches Some(d2) ==> d <= d2 && final(dst)@.subrange(0, d as int) == old(dst)@.subrange(0, d as int),
{
    if len <= 64 {
        return emit_copy_at(dst, d, input, ip, off, len, Ghost(i0), Ghost(n), Ghost((ip + len) as int));
    }
    let ilen = input.len();
    let d00 = d;
    let mut d = d;
    let mut at = ip;
    let mut rem = len;
    let ghost hi = ip + len;
    while rem >= 68
        invariant
            dst@.len() == old(dst)@.len(),
            d <= dst@.len(),
            1 <= off <= 65535,
            off <= ip <= at,
            at + rem == hi,
            hi == ip + len,
            hi <= input@.len(),
            4 <= rem,
            ilen == input@.len(),
            d00 <= d,
            dst@.subrange(0, d00 as int) == old(dst)@.subrange(0, d00 as int),
            forall|k: int| ip <= k < hi ==> #[trigger] input@[k] == input@[k - off],
            reach(dst@.subrange(0, d as int), i0, input@.subrange(0, at as int), n),
        decreases rem,
    {
        match emit_copy_at(dst, d, input, at, off, 64, Ghost(i0), Ghost(n), Ghost(hi)) {
            None => {
                return None;
            },
            Some(d2) => {
                proof {
                    assert(dst@.subrange(0, d00 as int) =~= dst@.subrange(0, d as int).subrange(0, d00 as int));
                }
                d = d2;
            },
        }
        at = at + 64;
        rem = rem - 64;
    }
    let ghost b1 = dst@;
    let d1 = d;
    if rem > 64 {
        match emit_copy_at(dst, d, input, at, off, 60, Ghost(i0), Ghost(n), Ghost(hi)) {
            None => {
                return None;
            },
            Some(d2) => {
                d = d2;
            },
        }
        at = at + 60;
        rem = rem - 60;
    }
    let ghost b2 = dst@;
    let r = emit_copy_at(dst, d, input, at, off, rem, Ghost(i0), Ghost(n), Ghost(hi));
    proof {
        assert(b2.subrange(0, d00 as int) =~= b2.subrange(0, d1 as int).subrange(0, d00 as int));
        assert(b1.subrange(0, d00 as int) =~= b1.subrange(0, d1 as int).subrange(0, d00 as int));
        if r.is_some() {
            assert(dst@.subrange(0, d00 as int) =~= dst@.subrange(0, d as int).subrange(0, d00 as int));
            assert(b2.subrange(0, d00 as int) =~= b2.subrange(0, d as int).subrange(0, d00 as int));
        }
    }
    r
}

/// Writes the literal `input[a..b]`, if it is not empty.
#[inline(always)]
fn emit_lit_at(
    dst: &mut [u8],
    d: usize,
    input: &[u8],
    a: usize,
    b: usize,
    Ghost(i0): Ghost<int>,
    Ghost(n): Ghost<nat>,
) -> (r: Option<usize>)
    requires
        d <= old(dst)@.len(),
        a <= b <= input@.len(),
        b - a <= 65536,
        reach(old(dst)@.subrange(0, d as int), i0, input@.subrange(0, a as int), n),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(d2) ==> d2 <= final(dst)@.len() && reach(
            final(dst)@.subrange(0, d2 as int),
            i0,
            input@.subrange(0, b as int),
            n,
        ),
        r matches Some(d2) ==> d <= d2 && final(dst)@.subrange(0, d as int) == old(dst)@.subrange(0, d as int),
{
    if a == b {
        return Some(d);
    }
    let ghost p0 = dst@.subrange(0, d as int);
    let r = emit_literal(dst, d, input, a, b - a);
    proof {
        let lits = input@.subrange(a as int, b as int);
        assert(input@.subrange(0, a as int) + lits =~= input@.subrange(0, b as int));
        lemma_reach_lit(p0, i0, input@.subrange(0, a as int), n, lits);
        if r.is_some() {
            let d2 = r.unwrap();
            assert(dst@.subrange(0, d as int) =~= dst@.subrange(0, d2 as int).subrange(0, d as int));
        }
    }
    r
}

// ---------------------------------------------------------------------------
// Finding matches
// ---------------------------------------------------------------------------

/// google/snappy's hash of four bytes, for a table of `n` entries where
/// `shift` leaves fewer than `n` values.
#[inline(always)]
fn hash4(x: u32, shift: u32, Ghost(n): Ghost<usize>) -> (h: usize)
    requires
        shift < 32,
        (0xffff_ffffu32 >> shift) < n,
    ensures
        h < n,
{
    let m = x.wrapping_mul(0x1e35a7bdu32);
    assert(m >> shift <= 0xffff_ffffu32 >> shift) by (bit_vector)
        requires
            shift < 32,
    ;
    (m >> shift) as usize
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

/// Byte `j` of the four that `lemma_next_word` is about.
proof fn lemma_next_byte(s: Seq<u8>, i: int, v: u64, v2: u64, t: u64, nx: u64, j: u64)
    requires
        0 <= i,
        i + 12 <= s.len(),
        v as nat == le_bytes(s, i, 8),
        v2 as nat == le_bytes(s, i + 4, 8),
        t < 8,
        j < 4,
        nx == (v >> ((8 * t) as u64)) | (((v2 >> 32) << 1) << ((63 - 8 * t) as u64)),
    ensures
        ((nx >> ((8 * j) as u64)) & 0xff) as nat == s[i + t + j],
{
    let sh = (8 * t) as u64;
    assert(sh & 7 == 0 && sh <= 56) by (bit_vector)
        requires
            sh == mul(8, t),
            t < 8,
    ;
    let p = (t + j) as u64;
    let sj = (8 * j) as u64;
    assert(sj == 0 || sj == 8 || sj == 16 || sj == 24);
    if p < 8 {
        lemma_word_byte(s, i, v, p);
        let sp = (8 * p) as u64;
        assert(sp == sh + sj);
        assert((nx >> sj) & 0xff == (v >> sp) & 0xff) by (bit_vector)
            requires
                nx == (v >> sh) | (((v2 >> 32) << 1) << sub(63, sh)),
                sh & 7 == 0,
                sh <= 56,
                sj == 0 || sj == 8 || sj == 16 || sj == 24,
                sp == add(sh, sj),
                sp < 64,
        ;
    } else {
        let p4 = (p - 4) as u64;
        lemma_word_byte(s, i + 4, v2, p4);
        let sp = (8 * p4) as u64;
        assert(sp + 32 == sh + sj);
        assert((nx >> sj) & 0xff == (v2 >> sp) & 0xff) by (bit_vector)
            requires
                nx == (v >> sh) | (((v2 >> 32) << 1) << sub(63, sh)),
                sh & 7 == 0,
                sh <= 56,
                sj == 0 || sj == 8 || sj == 16 || sj == 24,
                add(sp, 32) == add(sh, sj),
                add(sh, sj) >= 64,
                sp < 64,
        ;
    }
}

/// Four bytes at `i + t`, out of the eight at `i` and the eight at `i + 4`.
proof fn lemma_next_word(s: Seq<u8>, i: int, v: u64, v2: u64, t: u64, nx: u64)
    requires
        0 <= i,
        i + 12 <= s.len(),
        v as nat == le_bytes(s, i, 8),
        v2 as nat == le_bytes(s, i + 4, 8),
        t < 8,
        nx == (v >> ((8 * t) as u64)) | (((v2 >> 32) << 1) << ((63 - 8 * t) as u64)),
    ensures
        (nx & 0xffff_ffff) as nat == le_bytes(s, i + t, 4),
{
    let sh = (8 * t) as u64;
    assert(sh & 7 == 0 && sh <= 56) by (bit_vector)
        requires
            sh == mul(8, t),
            t < 8,
    ;
    let n0 = (nx >> 0) & 0xff;
    let n1 = (nx >> 8) & 0xff;
    let n2 = (nx >> 16) & 0xff;
    let n3 = (nx >> 24) & 0xff;
    lemma_next_byte(s, i, v, v2, t, nx, 0);
    lemma_next_byte(s, i, v, v2, t, nx, 1);
    lemma_next_byte(s, i, v, v2, t, nx, 2);
    lemma_next_byte(s, i, v, v2, t, nx, 3);
    reveal_with_fuel(le_bytes, 5);
    assert((nx & 0xffff_ffff) == add(add(add(n0, mul(0x100, n1)), mul(0x1_0000, n2)), mul(0x100_0000, n3)) && n0 <= 255
        && n1 <= 255 && n2 <= 255 && n3 <= 255) by (bit_vector)
        requires
            n0 == (nx >> 0) & 0xff,
            n1 == (nx >> 8) & 0xff,
            n2 == (nx >> 16) & 0xff,
            n3 == (nx >> 24) & 0xff,
    ;
}

/// `eq_len` where there are at least twelve bytes to compare, so the
/// first eight are compared with no test of how many there are; a match
/// usually ends among them. Also the four bytes after the match, when
/// they are inside `data`: they come out of what was already loaded, so
/// looking up the next position does not wait for another load.
#[inline(always)]
fn eq_len8(data: &[u8], a: usize, b: usize, max: usize) -> (r: (usize, u64))
    requires
        12 <= max,
        a + max <= data@.len(),
        b + max <= data@.len(),
    ensures
        r.0 <= max,
        forall|j: int| 0 <= j < r.0 ==> #[trigger] data@[a + j] == data@[b + j],
        b + r.0 + 4 <= data@.len() ==> (r.1 & 0xffff_ffff) as nat == le_bytes(data@, b + r.0, 4),
{
    let total = data.len();
    let u = load_u64_le(data, a);
    let v = load_u64_le(data, b);
    let v2 = load_u64_le(data, b + 4);
    let x = u ^ v;
    if x != 0 {
        let tz = x.trailing_zeros();
        let t = (tz / 8) as usize;
        proof {
            vstd::std_specs::bits::axiom_u64_trailing_zeros(x);
            assert forall|j: int| 0 <= j < t implies #[trigger] data@[a + j] == data@[b + j] by {
                let q = j as u64;
                let tz64 = tz as u64;
                lemma_word_byte(data@, a as int, u, q);
                lemma_word_byte(data@, b as int, v, q);
                assert(8 * q + 8 <= tz64);
                let sh = (8 * q) as u64;
                assert((u >> sh) & 0xff == (v >> sh) & 0xff) by (bit_vector)
                    requires
                        x == u ^ v,
                        x << sub(64, tz64) == 0,
                        tz64 <= 64,
                        sh < 64,
                        sh + 8 <= tz64,
                ;
            }
            assert(tz < 64) by {
                if tz >= 64 {
                    let tz64 = tz as u64;
                    assert(x == 0) by (bit_vector)
                        requires
                            x << sub(64, tz64) == 0,
                            tz64 == 64,
                    ;
                }
            }
        }
        let sh = (8 * t) as u64;
        let nx = (v >> sh) | (((v2 >> 32) << 1) << (63 - sh));
        proof {
            lemma_next_word(data@, b as int, v, v2, t as u64, nx);
        }
        return (t, nx);
    }
    let r = eq_len(data, a + 8, b + 8, max - 8);
    proof {
        assert(u == v) by (bit_vector)
            requires
                x == u ^ v,
                x == 0,
        ;
        assert forall|j: int| 0 <= j < 8 + r implies #[trigger] data@[a + j] == data@[b + j] by {
            if j < 8 {
                lemma_word_byte(data@, a as int, u, j as u64);
                lemma_word_byte(data@, b as int, v, j as u64);
            } else {
                assert(data@[a + 8 + (j - 8)] == data@[b + 8 + (j - 8)]);
            }
        }
    }
    let k = 8 + r;
    let nx = if total - (b + k) >= 4 {
        load32(data, b + k) as u64
    } else {
        0
    };
    assert(nx & 0xffff_ffff == nx) by (bit_vector)
        requires
            nx <= 0xffff_ffff,
    ;
    (k, nx)
}

/// The four bytes at `i` and the four at `i + 1`, out of the eight at `i`.
proof fn lemma_word_parts(s: Seq<u8>, i: int, w: u64)
    requires
        0 <= i,
        i + 8 <= s.len(),
        w as nat == le_bytes(s, i, 8),
    ensures
        (w & 0xffff_ffff) as nat == le_bytes(s, i, 4),
        ((w >> 8) & 0xffff_ffff) as nat == le_bytes(s, i + 1, 4),
{
    reveal_with_fuel(le_bytes, 9);
    let b0 = s[i] as u64;
    let b1 = s[i + 1] as u64;
    let b2 = s[i + 2] as u64;
    let b3 = s[i + 3] as u64;
    let b4 = s[i + 4] as u64;
    let hi = le_bytes(s, i + 5, 3) as u64;
    assert(w == b0 + 0x100 * b1 + 0x1_0000 * b2 + 0x100_0000 * b3 + 0x1_0000_0000 * b4 + 0x100_0000_0000 * hi);
    assert(hi <= 0xff_ffff);
    assert((w & 0xffff_ffff) == add(add(add(b0, mul(0x100, b1)), mul(0x1_0000, b2)), mul(0x100_0000, b3)) && ((w >> 8)
        & 0xffff_ffff) == add(add(add(b1, mul(0x100, b2)), mul(0x1_0000, b3)), mul(0x100_0000, b4))) by (bit_vector)
        requires
            b0 <= 255,
            b1 <= 255,
            b2 <= 255,
            b3 <= 255,
            b4 <= 255,
            hi <= 0xff_ffff,
            w == add(
                add(add(add(add(b0, mul(0x100, b1)), mul(0x1_0000, b2)), mul(0x100_0000, b3)), mul(0x1_0000_0000, b4)),
                mul(0x100_0000_0000, hi),
            ),
    ;
}

/// Compresses the fragment `input[fs..fe]`, writing its elements at `d`.
/// `None` if `dst` may be too small.
#[inline(never)]
fn compress_fragment<const N: usize>(
    input: &[u8],
    fs: usize,
    fe: usize,
    dst: &mut [u8],
    d0: usize,
    shift: u32,
    Ghost(i0): Ghost<int>,
    Ghost(n): Ghost<nat>,
) -> (r: Option<usize>)
    requires
        shift < 32,
        (0xffff_ffffu32 >> shift) < N,
        fs <= fe <= input@.len(),
        fe - fs <= FRAGMENT,
        d0 <= old(dst)@.len(),
        reach(old(dst)@.subrange(0, d0 as int), i0, input@.subrange(0, fs as int), n),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(d2) ==> d2 <= final(dst)@.len() && reach(
            final(dst)@.subrange(0, d2 as int),
            i0,
            input@.subrange(0, fe as int),
            n,
        ),
        r matches Some(d2) ==> d0 <= d2 && final(dst)@.subrange(0, d0 as int) == old(dst)@.subrange(0, d0 as int),
{
    let mut anchor = fs;
    let mut d = d0;
    if fe - fs >= 17 {
        // The last 16 bytes are always literals (15 in google/snappy), so
        // that twelve bytes can always be loaded after a match's first four.
        let ip_limit = fe - 16;
        // A fresh table for each fragment, as in google/snappy: every
        // entry is then a position before the one being looked at, and
        // only its four bytes need comparing.
        let mut table = [0u16;N];
        let frag = slice_subrange(input, fs, fe);
        let lim = ip_limit - fs;
        let flen = fe - fs;
        // The first position has nothing before it to match.
        let mut ip = fs + 1;
        let mut done = false;
        loop
            invariant_except_break
                !done,
                fs < ip <= ip_limit,
                anchor < ip,
                forall|h: int| 0 <= h < N ==> fs + (#[trigger] table@[h]) < ip,
            invariant
                shift < 32,
                (0xffff_ffffu32 >> shift) < N,
                dst@.len() == old(dst)@.len(),
                fs <= anchor <= fe,
                fe <= input@.len(),
                fe - fs <= FRAGMENT,
                fe - fs >= 17,
                ip_limit == fe - 16,
                lim == fe - fs - 16,
                flen == fe - fs,
                frag@ == input@.subrange(fs as int, fe as int),
                d0 <= d <= dst@.len(),
                dst@.subrange(0, d0 as int) == old(dst)@.subrange(0, d0 as int),
                reach(dst@.subrange(0, d as int), i0, input@.subrange(0, anchor as int), n),
            decreases fe - anchor,
        {
            // Look for four bytes seen before, stepping faster the longer
            // nothing is found. Positions are counted from the fragment's
            // start, which is what the table holds.
            let mut found = false;
            let mut skip: usize = 32;
            let mut q = ip - fs;
            let mut c: usize = 0;
            let ghost q0 = q;
            loop
                invariant_except_break
                    !found,
                    q <= lim,
                    forall|h: int| 0 <= h < N ==> (#[trigger] table@[h]) < q,
                invariant
                    shift < 32,
                    (0xffff_ffffu32 >> shift) < N,
                    frag@ == input@.subrange(fs as int, fe as int),
                    fs <= fe <= input@.len(),
                    0 < q0 <= q,
                    fe - fs <= FRAGMENT,
                    fe - fs >= 17,
                    lim == fe - fs - 16,
                    32 <= skip <= 32 + (q - q0),
                    forall|h: int| 0 <= h < N ==> (#[trigger] table@[h]) <= q,
                ensures
                    found ==> q <= lim && c < q && le_bytes(frag@, c as int, 4) == le_bytes(frag@, q as int, 4),
                decreases lim + 1 - q,
            {
                let x = load32(frag, q);
                let h = hash4(x, shift, Ghost(N));
                let e = table[h] as usize;
                table[h] = q as u16;
                if load32(frag, e) == x {
                    c = e;
                    found = true;
                    break ;
                }
                let step = skip >> 5;
                assert(skip >> 5 >= 1 && skip >> 5 <= skip) by (bit_vector)
                    requires
                        skip >= 32,
                ;
                skip = skip + step;
                q = q + step;
                if q > lim {
                    break ;
                }
            }
            if !found {
                break ;
            }
            // What was passed over is a literal, and it is not empty.
            let ghost g1 = dst@;
            let ghost a1 = anchor;
            match emit_lit_at(dst, d, input, anchor, fs + q, Ghost(i0), Ghost(n)) {
                None => {
                    return None;
                },
                Some(d2) => {
                    proof {
                        assert(dst@.subrange(0, d0 as int) =~= dst@.subrange(0, d as int).subrange(0, d0 as int));
                        assert(g1.subrange(0, d0 as int) =~= g1.subrange(0, d as int).subrange(0, d0 as int));
                    }
                    d = d2;
                },
            }
            anchor = fs + q;
            // One match after another, for as long as the position after
            // a match starts the next one.
            loop
                invariant_except_break
                    !done,
                    c < q <= lim,
                    le_bytes(frag@, c as int, 4) == le_bytes(frag@, q as int, 4),
                invariant
                    shift < 32,
                    (0xffff_ffffu32 >> shift) < N,
                    dst@.len() == old(dst)@.len(),
                    anchor == fs + q,
                    a1 < anchor,
                    q <= flen,
                    forall|h: int| 0 <= h < N ==> (#[trigger] table@[h]) <= q,
                    fs <= fe <= input@.len(),
                    fe - fs <= FRAGMENT,
                    fe - fs >= 17,
                    lim == fe - fs - 16,
                    flen == fe - fs,
                    frag@ == input@.subrange(fs as int, fe as int),
                    d0 <= d <= dst@.len(),
                    dst@.subrange(0, d0 as int) == old(dst)@.subrange(0, d0 as int),
                    reach(dst@.subrange(0, d as int), i0, input@.subrange(0, anchor as int), n),
                ensures
                    !done ==> q < lim,
                decreases flen - q,
            {
                let at = fs + q;
                let cand = fs + c;
                proof {
                    lemma_load_eq(frag@, c as int, q as int);
                    assert forall|t: int| 0 <= t < 4 implies #[trigger] input@[cand + t] == input@[at + t] by {
                        assert(frag@[c + t] == input@[fs + c + t]);
                        assert(frag@[q + t] == input@[fs + q + t]);
                    }
                }
                let (more, nx) = eq_len8(frag, c + 4, q + 4, flen - (q + 4));
                proof {
                    assert forall|j: int| 0 <= j < more implies #[trigger] input@[cand + 4 + j] == input@[at + 4 + j] by {
                        assert(frag@[c + 4 + j] == frag@[q + 4 + j]);
                        assert(frag@[c + 4 + j] == input@[fs + c + 4 + j]);
                        assert(frag@[q + 4 + j] == input@[fs + q + 4 + j]);
                    }
                }
                let len = 4 + more;
                let off = q - c;
                proof {
                    assert forall|k: int| at <= k < at + len implies #[trigger] input@[k] == input@[k - off] by {
                        let t = k - at;
                        if t < 4 {
                            assert(input@[cand + t] == input@[at + t]);
                        } else {
                            assert(input@[cand + 4 + (t - 4)] == input@[at + 4 + (t - 4)]);
                        }
                    }
                }
                let ghost g2 = dst@;
                match emit_match(dst, d, input, at, off, len, Ghost(i0), Ghost(n)) {
                    None => {
                        return None;
                    },
                    Some(d2) => {
                        proof {
                            assert(dst@.subrange(0, d0 as int) =~= dst@.subrange(0, d as int).subrange(0, d0 as int));
                            assert(g2.subrange(0, d0 as int) =~= g2.subrange(0, d as int).subrange(0, d0 as int));
                        }
                        d = d2;
                    },
                }
                q = q + len;
                anchor = fs + q;
                if q >= lim {
                    done = true;
                    break ;
                }
                // Remember the position before this one, then see whether
                // this one starts a match.
                // One load holds both positions' four bytes.
                let w = load_u64_le(frag, q - 1);
                proof {
                    lemma_word_parts(frag@, q - 1, w);
                }
                assert(w & 0xffff_ffff <= 0xffff_ffff && (w >> 8) & 0xffff_ffff <= 0xffff_ffff) by (bit_vector);
                let h2 = hash4((w & 0xffff_ffff) as u32, shift, Ghost(N));
                table[h2] = (q - 1) as u16;
                // This position's four bytes came with the match's length.
                assert(nx & 0xffff_ffff <= 0xffff_ffff) by (bit_vector);
                let x = (nx & 0xffff_ffff) as u32;
                let h = hash4(x, shift, Ghost(N));
                let e = table[h] as usize;
                table[h] = q as u16;
                if load32(frag, e) != x {
                    break ;
                }
                c = e;
            }
            if done {
                break ;
            }
            ip = fs + q + 1;
        }
    }
    let ghost g3 = dst@;
    let r = emit_lit_at(dst, d, input, anchor, fe, Ghost(i0), Ghost(n));
    proof {
        if r.is_some() {
            assert(dst@.subrange(0, d0 as int) =~= dst@.subrange(0, d as int).subrange(0, d0 as int));
            assert(g3.subrange(0, d0 as int) =~= g3.subrange(0, d as int).subrange(0, d0 as int));
        }
    }
    r
}

/// google/snappy's `MaxCompressedLength`: room that is always enough for
/// an input of `n` bytes.
pub fn max_compressed_length(n: usize) -> (r: usize)
    requires
        n <= 0xffff_ffff,
{
    32 + n + n / 6
}

/// Compresses `input` into `dst`. `Some(m)`: `dst[..m]` decompresses to
/// `input`. `None`: `dst` may be too small (`max_compressed_length` is
/// always enough), or `input` is 4 GiB or longer, which the format cannot
/// hold.
pub fn compress_into(input: &[u8], dst: &mut [u8]) -> (r: Option<usize>)
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(m) ==> m <= final(dst)@.len() && decompress(final(dst)@.subrange(0, m as int)) == Some(input@),
{
    let n = input.len();
    if n > 0xffff_ffff || dst.len() < 5 {
        return None;
    }
    // The preamble.
    let mut d: usize = 0;
    let mut v = n;
    let ghost goal = enc_varint(n as nat);
    while v >= 128
        invariant
            dst@.len() == old(dst)@.len(),
            dst@.len() >= 5,
            v <= n <= 0xffff_ffff,
            d <= 4,
            d == 0 ==> v < 0x1_0000_0000,
            d == 1 ==> v < 0x200_0000,
            d == 2 ==> v < 0x4_0000,
            d == 3 ==> v < 0x800,
            d == 4 ==> v < 0x10,
            dst@.subrange(0, d as int) + enc_varint(v as nat) == goal,
        decreases v,
    {
        let ghost before = dst@;
        set(dst, d, (v % 128 + 128) as u8);
        proof {
            assert(dst@.subrange(0, d + 1) + enc_varint((v / 128) as nat) =~= before.subrange(0, d as int) + enc_varint(
                v as nat,
            ));
        }
        d = d + 1;
        v = v / 128;
    }
    let ghost before = dst@;
    set(dst, d, v as u8);
    proof {
        assert(dst@.subrange(0, d + 1) =~= before.subrange(0, d as int) + enc_varint(v as nat));
    }
    d = d + 1;
    let i0 = d;
    let ghost pre = dst@.subrange(0, i0 as int);
    // The table is sized to the input, so that a short input does not pay
    // for clearing a long table.
    let mut fs: usize = 0;
    proof {
        assert(input@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while fs < n
        invariant
            dst@.len() == old(dst)@.len(),
            n == input@.len(),
            fs <= n,
            i0 <= d <= dst@.len(),
            pre == goal,
            pre.len() == i0,
            dst@.subrange(0, i0 as int) == pre,
            reach(dst@.subrange(0, d as int), i0 as int, input@.subrange(0, fs as int), n as nat),
        decreases n - fs,
    {
        let fe = if n - fs > FRAGMENT {
            fs + FRAGMENT
        } else {
            n
        };
        let ghost before = dst@;
        assert(0xffff_ffffu32 >> 22 < 1024 && 0xffff_ffffu32 >> 20 < 4096 && 0xffff_ffffu32 >> 18 < 16384) by (bit_vector);
        let r = if n <= 1024 {
            compress_fragment::<1024>(input, fs, fe, dst, d, 22, Ghost(i0 as int), Ghost(n as nat))
        } else if n <= 4096 {
            compress_fragment::<4096>(input, fs, fe, dst, d, 20, Ghost(i0 as int), Ghost(n as nat))
        } else {
            compress_fragment::<HASH_SIZE>(input, fs, fe, dst, d, 18, Ghost(i0 as int), Ghost(n as nat))
        };
        match r {
            None => {
                return None;
            },
            Some(d2) => {
                proof {
                    // The preamble is still there.
                    assert(dst@.subrange(0, i0 as int) =~= dst@.subrange(0, d as int).subrange(0, i0 as int));
                    assert(before.subrange(0, i0 as int) =~= before.subrange(0, d as int).subrange(0, i0 as int));
                }
                d = d2;
            },
        }
        fs = fe;
    }
    proof {
        let s = dst@.subrange(0, d as int);
        assert(input@.subrange(0, n as int) =~= input@);
        assert(s.subrange(0, s.len() as int) =~= s);
        assert(extends(s, s));
        assert(s.subrange(0, i0 as int) =~= goal);
        lemma_varint(s, 0, 0, n as nat);
    }
    Some(d)
}

} // verus!
