//! The block decoder, proven equal to `spec::seqs`. It writes straight
//! into the caller's buffer; the copies are vcore's (`lz::copy_match`,
//! `lz::copy_lits`), which work 16 bytes at a time where there is room.
use crate::spec::*;
use verilith_core::lz::{copy_lits, copy_match};
#[cfg(verus_only)]
use verilith_core::lz::{lemma_lz_copy_len, lemma_matched, matched, placed};
use verilith_core::prims::{get, load_u64_le};
use vstd::prelude::*;

verus! {

/// Past a run of 255s, `ext_len` is the rest plus 255 for each.
proof fn lemma_ext_len_run(s: Seq<u8>, i: int, k: int)
    requires
        0 <= i <= k <= s.len(),
        forall|j: int| i <= j < k ==> s[j] == 255,
    ensures
        ext_len(s, i) == match ext_len(s, k) {
            Some((n, j)) => Some((n + 255 * (k - i) as nat, j)),
            None => None,
        },
    decreases k - i,
{
    if i < k {
        lemma_ext_len_run(s, i + 1, k);
    }
}

/// An extended length is at most 255 for each byte it takes.
pub proof fn lemma_ext_len_max(s: Seq<u8>, i: int)
    ensures
        ext_len(s, i) matches Some((n, j)) ==> n <= 255 * (j - i) && i < j <= s.len(),
    decreases s.len() - i,
{
    if 0 <= i < s.len() && s[i] == 255 {
        lemma_ext_len_max(s, i + 1);
    }
}

/// A block grows its output by at most 255 bytes for each byte of it,
/// so a block of `n` bytes needs at most `255 * n` bytes of room.
pub proof fn lemma_seqs_max(s: Seq<u8>, i: int, out: Seq<u8>, strict: Option<nat>)
    requires
        0 <= i,
    ensures
        seqs(s, i, out, strict) matches Some(o) ==> o.len() <= out.len() + 255 * (s.len() - i),
    decreases s.len() - i,
{
    if 0 <= i < s.len() {
        let token = s[i];
        lemma_ext_len_max(s, i + 1);
        match read_len(s, i + 1, (token / 16) as nat) {
            None => {},
            Some((ll, j)) => {
                if j + ll <= s.len() {
                    let out1 = out + s.subrange(j, j + ll);
                    let k = j + ll;
                    if k != s.len() && k + 2 <= s.len() {
                        lemma_ext_len_max(s, k + 2);
                        let off = le16(s, k);
                        match read_len(s, k + 2, (token % 16) as nat) {
                            None => {},
                            Some((ml, m)) => {
                                lemma_lz_copy_len(out1, off as int, ml + 4);
                                lemma_seqs_max(s, m, lz_copy(out1, off as int, ml + 4), strict);
                            },
                        }
                    }
                }
            },
        }
    }
}

/// The result of `seqs` is at least as long as what it started from.
pub proof fn lemma_seqs_len(s: Seq<u8>, i: int, out: Seq<u8>, strict: Option<nat>)
    ensures
        seqs(s, i, out, strict) matches Some(o) ==> o.len() >= out.len(),
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
                                lemma_lz_copy_len(out1, off as int, ml + 4);
                                lemma_seqs_len(s, m, lz_copy(out1, off as int, ml + 4), strict);
                            },
                        }
                    }
                }
            },
        }
    }
}

/// The extension of a length field at `i`, added to `base`, if the total
/// is at most `limit`.
fn read_ext(src: &[u8], i: usize, base: usize, limit: usize) -> (r: (Option<(usize, usize)>, Ghost<nat>))
    requires
        i <= src@.len(),
        base <= 300,
    ensures
        // Its loop's turns: the bytes it reads.
        r.1@ <= src@.len() - i,
        r.0 matches Some((_t, j)) ==> r.1@ < j - i,
        match r.0 {
            Some((t, j)) => ext_len(src@, i as int) == Some(((t - base) as nat, j as int)) && base <= t <= limit && i < j
                <= src@.len(),
            None => match ext_len(src@, i as int) {
                Some((e, _j)) => base + e > limit,
                None => true,
            },
        },
{
    let n = src.len();
    let mut k = i;
    while k < n && get(src, k) == 255
        invariant
            i <= k <= n,
            n == src@.len(),
            forall|j: int| i <= j < k ==> src@[j] == 255,
        decreases n - k,
    {
        k = k + 1;
    }
    proof {
        lemma_ext_len_run(src@, i as int, k as int);
    }
    let ghost w = (k - i) as nat;
    if k >= n {
        return (None, Ghost(w));
    }
    let cnt = k - i;
    let b = get(src, k) as usize;
    if cnt > limit / 255 {
        return (None, Ghost(w));
    }
    let t = 255 * cnt;
    let rest = base + b;
    if rest > limit - t {
        return (None, Ghost(w));
    }
    (Some((t + rest, k + 1)), Ghost(w))
}

/// The low two bytes of an 8-byte load are the offset there.
proof fn lemma_low16(s: Seq<u8>, i: int, w: u64)
    requires
        0 <= i,
        i + 8 <= s.len(),
        w as nat == verilith_core::prims::le_bytes(s, i, 8),
    ensures
        (w & 0xffff) as nat == le16(s, i),
{
    reveal_with_fuel(verilith_core::prims::le_bytes, 9);
    let a = le16(s, i);
    let b = verilith_core::prims::le_bytes(s, i + 2, 6);
    assert(verilith_core::prims::le_bytes(s, i, 8) == a + 0x1_0000 * b);
    assert(a < 0x1_0000);
    assert(w & 0xffff == w % 0x1_0000) by (bit_vector);
}

/// The decoder's inner loop: sequences of the two commonest shapes, while
/// there is so much input (320 bytes) and room (600) left that nothing
/// about lengths needs checking: every sequence whose literal length and
/// match length each take at most one extra byte. It stops at the first
/// sequence that is anything else, or not valid, having decoded from
/// `(ip0, op0)` to the positions it gives;
/// `decode_block` takes one sequence from there and comes back.
///
/// Kept out of line and free of calls so that the positions stay in
/// registers.
#[inline(never)]
fn fast_loop(src: &[u8], out: &mut [u8], lo: usize, ip0: usize, op0: usize) -> (r: (usize, usize, Ghost<nat>))
    requires
        lo <= op0 <= old(out)@.len(),
        ip0 <= src@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        ip0 <= r.0 <= src@.len(),
        op0 <= r.1 <= final(out)@.len(),
        final(out)@.subrange(0, op0 as int) == old(out)@.subrange(0, op0 as int),
        seqs(src@, r.0 as int, final(out)@.subrange(lo as int, r.1 as int), None) == seqs(
            src@,
            ip0 as int,
            old(out)@.subrange(lo as int, op0 as int),
            None,
        ),
        // Work: every sequence takes at least three input bytes. The
        // constant is for one left unfinished.
        r.2@ <= 150 * (r.0 - ip0) + (r.1 - op0) + 320,
{
    let n = src.len();
    let len = out.len();
    let ghost goal = seqs(src@, ip0 as int, out@.subrange(lo as int, op0 as int), None);
    let mut ip = ip0;
    let mut op = op0;
    let ghost mut work: nat = 0;
    if n < 320 || len < 600 {
        return (ip, op, Ghost(work));
    }
    let ilim = n - 320;
    let olim = len - 600;
    loop
        invariant_except_break
            work <= 150 * (ip - ip0) + (op - op0),
        invariant
            n == src@.len(),
            len == out@.len(),
            len == old(out)@.len(),
            ilim == n - 320,
            olim == len - 600,
            lo <= op0 <= op <= len,
            ip0 <= ip <= n,
            seqs(src@, ip as int, out@.subrange(lo as int, op as int), None) == goal,
            out@.subrange(0, op0 as int) == old(out)@.subrange(0, op0 as int),
        ensures
            work <= 150 * (ip - ip0) + (op - op0) + 320,
        decreases n - ip,
    {
        if ip > ilim || op > olim {
            break ;
        }
        let ghost w0 = work;
        proof {
            work = work + 1;
        }
        let ghost cur = out@.subrange(lo as int, op as int);
        let ghost before = out@;
        let token = get(src, ip);
        let lnib = (token >> 4) as usize;
        let mnib = (token & 15) as usize;
        proof {
            assert(token >> 4 == token / 16) by (bit_vector);
            assert(token & 15 == token % 16) by (bit_vector);
            assert(token & 15 < 16) by (bit_vector);
        }
        let ll: usize;
        let j: usize;
        if lnib != 15 {
            ll = lnib;
            j = ip + 1;
            verilith_core::prims::copy16_in(out, op, src, j);
            proof {
                work = work + 16;
            }
        } else {
            let b = get(src, ip + 1);
            if b == 255 {
                break ;
            }
            ll = 15 + b as usize;
            j = ip + 2;
            verilith_core::lz::copy_lits_wild(out, op, src, j, ll);
            proof {
                work = (work + ll + 32) as nat;
            }
        }
        assert(work <= w0 + 1 + ll + 32 && ll <= 270 && j <= ip + 2);
        assert(read_len(src@, ip + 1, (token / 16) as nat) == Some((ll as nat, j as int)));
        let ghost out1 = cur + src@.subrange(j as int, j + ll);
        let op1 = op + ll;
        let k = j + ll;
        proof {
            assert(out@.subrange(lo as int, op1 as int) =~= out1);
            assert(out@.subrange(0, op0 as int) =~= before.subrange(0, op0 as int));
        }
        let w = load_u64_le(src, k);
        assert(w & 0xffff <= 0xffff) by (bit_vector);
        let off = (w & 0xffff) as usize;
        proof {
            lemma_low16(src@, k as int, w);
        }
        if off == 0 || off > op1 - lo {
            proof {
                assert(out@.subrange(lo as int, op as int) =~= cur);
            }
            break ;
        }
        let ml: usize;
        let m: usize;
        let ghost mid = out@;
        if mnib != 15 && off >= 8 {
            // At most 18 bytes from at least 8 back: three 8-byte copies.
            ml = mnib + 4;
            m = k + 2;
            verilith_core::lz::copy_match24(out, op1, off, ml);
            proof {
                work = work + 24;
            }
        } else {
            if mnib == 15 {
                let e = get(src, k + 2);
                if e == 255 {
                    proof {
                        assert(out@.subrange(lo as int, op as int) =~= cur);
                    }
                    break ;
                }
                ml = 19 + e as usize;
                m = k + 3;
            } else {
                ml = mnib + 4;
                m = k + 2;
            }
            if off >= 16 {
                verilith_core::lz::copy_match_wild(out, op1, off, ml);
            } else {
                copy_match(out, op1, off, ml);
            }
            proof {
                work = (work + ml + 32) as nat;
            }
        }
        assert(read_len(src@, k + 2, (token % 16) as nat) == Some(((ml - 4) as nat, m as int)));
        proof {
            lemma_matched(mid, out@, lo as int, op1 as int, off as int, ml as int);
            assert(((ml - 4) as nat + 4) as nat == ml as nat);
            assert(out@.subrange(0, op0 as int) =~= mid.subrange(0, op0 as int));
        }
        ip = m;
        op = op1 + ml;
    }
    (ip, op, Ghost(work))
}

/// Runs the inner loop if there is input and room enough for it to take
/// even one sequence.
#[inline(always)]
fn fast(src: &[u8], out: &mut [u8], lo: usize, start: usize, ip0: usize, op0: usize) -> (r: (usize, usize, Ghost<nat>))
    requires
        lo <= start <= op0 <= old(out)@.len(),
        ip0 <= src@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        ip0 <= r.0 <= src@.len(),
        op0 <= r.1 <= final(out)@.len(),
        final(out)@.subrange(0, start as int) == old(out)@.subrange(0, start as int),
        seqs(src@, r.0 as int, final(out)@.subrange(lo as int, r.1 as int), None) == seqs(
            src@,
            ip0 as int,
            old(out)@.subrange(lo as int, op0 as int),
            None,
        ),
        r.2@ <= 150 * (r.0 - ip0) + (r.1 - op0) + 320,
{
    if src.len() - ip0 >= 320 && out.len() - op0 >= 600 {
        let r = fast_loop(src, out, lo, ip0, op0);
        proof {
            assert(out@.subrange(0, start as int) =~= old(out)@.subrange(0, start as int)) by {
                assert forall|x: int| 0 <= x < start implies #[trigger] out@[x] == old(out)@[x] by {
                    assert(out@.subrange(0, op0 as int)[x] == old(out)@.subrange(0, op0 as int)[x]);
                }
            }
        }
        r
    } else {
        (ip0, op0, Ghost(0))
    }
}

/// Decodes the block `src` into `out` from `start`. Matches may reach
/// back to `lo`: `out[lo..start]` is the history (earlier blocks, or
/// nothing when `lo == start`).
///
/// `Some(n)`: the block is valid and decodes to `out[start..n]`.
/// `None`: the block is not valid, or what it decodes to does not fit in
/// `out`. Bytes of `out` from `start` on may be changed either way;
/// bytes before `start` are not.
#[verifier::rlimit(60)]
pub fn decode_block_counted(src: &[u8], out: &mut [u8], lo: usize, start: usize) -> (r: (Option<usize>, Ghost<nat>))
    requires
        lo <= start <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(0, start as int) == old(out)@.subrange(0, start as int),
        match r.0 {
            Some(n) => start <= n <= final(out)@.len() && block(src@, old(out)@.subrange(lo as int, start as int))
                == Some(final(out)@.subrange(lo as int, n as int)),
            None => match block(src@, old(out)@.subrange(lo as int, start as int)) {
                Some(o) => lo + o.len() > old(out)@.len(),
                None => true,
            },
        },
        // Work: linear in the block, and in its output (or, if it does not
        // decode, in the room given).
        r.1@ <= block_work(src@.len(), (old(out)@.len() - start) as nat),
        r.0 matches Some(n) ==> r.1@ <= block_work(src@.len(), (n - start) as nat),
{
    let ghost mut work: nat = 0;
    let n = src.len();
    let len = out.len();
    let ghost hist = out@.subrange(lo as int, start as int);
    let ghost goal = block(src@, hist);
    let mut ip: usize = 0;
    let mut op: usize = start;
    loop
        invariant
            n == src@.len(),
            len == out@.len(),
            len == old(out)@.len(),
            lo <= start <= op <= len,
            ip <= n,
            goal == block(src@, hist),
            hist == old(out)@.subrange(lo as int, start as int),
            seqs(src@, ip as int, out@.subrange(lo as int, op as int), None) == goal,
            out@.subrange(0, start as int) == old(out)@.subrange(0, start as int),
            work <= 150 * ip + (op - start),
        decreases n - ip,
    {
        let (ip2, op2, Ghost(wf)) = fast(src, out, lo, start, ip, op);
        proof {
            work = work + wf;
        }
        ip = ip2;
        op = op2;
        if ip >= n {
            return (None, Ghost(work));
        }
        let ghost cur = out@.subrange(lo as int, op as int);
        let ghost before = out@;
        let ghost w1 = work;
        proof {
            work = work + 1;
        }
        let token = get(src, ip);
        let lnib = (token >> 4) as usize;
        let mnib = (token & 15) as usize;
        proof {
            assert(token >> 4 == token / 16) by (bit_vector);
            assert(token & 15 == token % 16) by (bit_vector);
            assert(token & 15 < 16) by (bit_vector);
        }
        let ll: usize;
        let j: usize;
        if lnib != 15 && n - ip >= 19 && len - op >= 40 {
            // The common case: at most 14 literals, with room to copy
            // 16 bytes without looking at the length, and more input
            // after them.
            ll = lnib;
            j = ip + 1;
            verilith_core::prims::copy16_in(out, op, src, j);
            proof {
                work = work + 16;
            }
        } else if lnib == 15 && n - ip >= 320 && len - op >= 320 && get(src, ip + 1) != 255 {
            // The next most common: a literal length in one more byte
            // (at most 269), with room to copy it 32 bytes at a time
            // and more input after it.
            ll = 15 + get(src, ip + 1) as usize;
            j = ip + 2;
            copy_lits(out, op, src, j, ll);
            proof {
                work = (work + ll + 32) as nat;
            }
        } else {
            let mut l = lnib;
            let mut jj = ip + 1;
            if l == 15 {
                let (re, Ghost(we)) = read_ext(src, jj, 15, n);
                proof {
                    work = work + we;
                }
                match re {
                    None => {
                        proof {
                            lemma_ext_len_next(src@, jj as int);
                        }
                        return (None, Ghost(work));
                    },
                    Some((t, j2)) => {
                        l = t;
                        jj = j2;
                    },
                }
            }
            assert(read_len(src@, ip + 1, (token / 16) as nat) == Some((l as nat, jj as int)));
            if l > n - jj {
                return (None, Ghost(work));
            }
            if l > len - op {
                proof {
                    // What the block decodes to is at least this long.
                    let out1 = cur + src@.subrange(jj as int, jj + l);
                    if goal.is_some() {
                        let k = jj + l;
                        if k != n && k + 2 <= n {
                            let off = le16(src@, k);
                            match read_len(src@, k + 2, (token % 16) as nat) {
                                None => {},
                                Some((ml, m)) => {
                                    lemma_lz_copy_len(out1, off as int, ml + 4);
                                    lemma_seqs_len(src@, m, lz_copy(out1, off as int, ml + 4), None);
                                },
                            }
                        }
                    }
                }
                return (None, Ghost(work));
            }
            copy_lits(out, op, src, jj, l);
            proof {
                work = (work + l + 32) as nat;
            }
            if jj + l == n {
                proof {
                    assert(out@.subrange(lo as int, op + l) =~= cur + src@.subrange(jj as int, jj + l));
                    assert(out@.subrange(0, start as int) =~= before.subrange(0, start as int));
                }
                return (Some(op + l), Ghost(work));
            }
            if n - (jj + l) < 2 {
                return (None, Ghost(work));
            }
            ll = l;
            j = jj;
        }
        assert(read_len(src@, ip + 1, (token / 16) as nat) == Some((ll as nat, j as int)));
        let ghost out1 = cur + src@.subrange(j as int, j + ll);
        let op1 = op + ll;
        let k = j + ll;
        proof {
            assert(out@.subrange(lo as int, op1 as int) =~= out1);
            assert(out@.subrange(0, start as int) =~= before.subrange(0, start as int));
        }
        let off = get(src, k) as usize + 256 * (get(src, k + 1) as usize);
        let mut ml = mnib + 4;
        let mut m = k + 2;
        if mnib == 15 {
            let (re, Ghost(we)) = read_ext(src, m, 19, len);
            proof {
                work = work + we;
            }
            match re {
                None => {
                    proof {
                        lemma_ext_len_next(src@, m as int);
                        if goal.is_some() {
                            let (ml0, m0) = read_len(src@, k + 2, (token % 16) as nat).unwrap();
                            lemma_lz_copy_len(out1, off as int, ml0 + 4);
                            lemma_seqs_len(src@, m0, lz_copy(out1, off as int, ml0 + 4), None);
                        }
                    }
                    return (None, Ghost(work));
                },
                Some((t, m2)) => {
                    ml = t;
                    m = m2;
                },
            }
        }
        assert(read_len(src@, k + 2, (token % 16) as nat) == Some(((ml - 4) as nat, m as int)));
        if off == 0 || off > op1 - lo {
            return (None, Ghost(work));
        }
        let ghost mid = out@;
        if mnib != 15 && off >= 8 && len - op1 >= 24 {
            // At most 18 bytes from at least 8 back: three 8-byte copies.
            verilith_core::lz::copy_match24(out, op1, off, ml);
            proof {
                work = work + 24;
            }
        } else {
            if ml > len - op1 {
                proof {
                    lemma_lz_copy_len(out1, off as int, ml as nat);
                    lemma_seqs_len(src@, m as int, lz_copy(out1, off as int, ml as nat), None);
                }
                return (None, Ghost(work));
            }
            copy_match(out, op1, off, ml);
            proof {
                work = (work + ml + 32) as nat;
            }
        }
        proof {
            lemma_matched(mid, out@, lo as int, op1 as int, off as int, ml as int);
            assert(((ml - 4) as nat + 4) as nat == ml as nat);
            assert(out@.subrange(0, start as int) =~= mid.subrange(0, start as int));
        }
        ip = m;
        op = op1 + ml;
    }
}

/// The decoder's work bound: at most this many steps for a block of
/// `n` bytes that writes at most `m` bytes. A step is a turn of a loop or a
/// byte copied (counting what the wide copies write past the end).
pub open spec fn block_work(n: nat, m: nat) -> nat {
    151 * n + m + 400
}

/// `decode_block_counted` without the count.
///
/// Decodes the block `src` into `out` from `start`. Matches may reach
/// back to `lo`: `out[lo..start]` is the history (earlier blocks, or
/// nothing when `lo == start`).
///
/// `Some(n)`: the block is valid and decodes to `out[start..n]`.
/// `None`: the block is not valid, or what it decodes to does not fit in
/// `out`. Bytes of `out` from `start` on may be changed either way;
/// bytes before `start` are not.
#[inline(always)]
pub fn decode_block(src: &[u8], out: &mut [u8], lo: usize, start: usize) -> (r: Option<usize>)
    requires
        lo <= start <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(0, start as int) == old(out)@.subrange(0, start as int),
        match r {
            Some(n) => start <= n <= final(out)@.len() && block(src@, old(out)@.subrange(lo as int, start as int))
                == Some(final(out)@.subrange(lo as int, n as int)),
            None => match block(src@, old(out)@.subrange(lo as int, start as int)) {
                Some(o) => lo + o.len() > old(out)@.len(),
                None => true,
            },
        },
{
    decode_block_counted(src, out, lo, start).0
}

} // verus!

verus! {

/// Decodes the block `src` into `out`. `Some(n)`: the block is valid and
/// decodes to `out[..n]`. `None`: it is not valid, or does not fit.
pub fn decompress_into(src: &[u8], out: &mut [u8]) -> (r: Option<usize>)
    ensures
        final(out)@.len() == old(out)@.len(),
        match r {
            Some(n) => n <= final(out)@.len() && block(src@, Seq::empty()) == Some(final(out)@.subrange(0, n as int)),
            None => match block(src@, Seq::empty()) {
                Some(o) => o.len() > old(out)@.len(),
                None => true,
            },
        },
{
    proof {
        assert(out@.subrange(0, 0) =~= Seq::empty());
    }
    decode_block(src, out, 0, 0)
}

} // verus!
