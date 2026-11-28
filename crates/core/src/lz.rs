//! LZ77 over byte slices, for the byte-oriented formats (LZ4, Snappy)
//! whose decoders write straight into the caller's buffer: what copying a
//! match means (`lz_copy`), and proven ways to do it fast.
//!
//! - `copy_match` writes a match 16 or 8 bytes at a time where the buffer
//!   has room after the match, whatever the offset: offsets under 8 first
//!   double the distance with overlapping 8-byte moves. The chunks may
//!   write up to 15 bytes past the match's end (still inside the buffer);
//!   the proof is that the match's own bytes are right.
//! - `copy_lits` copies literals 16 bytes at a time when both buffers have
//!   room.
//! - `eq_len` counts matching bytes eight at a time.
//! - `load32` reads four bytes as a little-endian number.
use crate::prims::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// `out` with `n` more bytes, each a copy of the byte `off` before it: an
/// LZ77 match. The copies may overlap what they write (`off < n`).
pub open spec fn lz_copy(out: Seq<u8>, off: int, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        out
    } else {
        lz_copy(out.push(out[out.len() - off]), off, (n - 1) as nat)
    }
}

pub proof fn lemma_lz_copy_len(out: Seq<u8>, off: int, n: nat)
    ensures
        lz_copy(out, off, n).len() == out.len() + n,
    decreases n,
{
    if n > 0 {
        lemma_lz_copy_len(out.push(out[out.len() - off]), off, (n - 1) as nat);
    }
}

/// A sequence that starts with `o` and whose every later byte equals the
/// one `off` before it is `lz_copy(o, off, n)`.
pub proof fn lemma_lz_copy_is(o: Seq<u8>, r: Seq<u8>, off: int, n: nat)
    requires
        1 <= off <= o.len(),
        r.len() == o.len() + n,
        forall|j: int| 0 <= j < o.len() ==> #[trigger] r[j] == o[j],
        forall|j: int| o.len() <= j < r.len() ==> #[trigger] r[j] == r[j - off],
    ensures
        lz_copy(o, off, n) == r,
    decreases n,
{
    if n == 0 {
        assert(o =~= r);
    } else {
        let o1 = o.push(o[o.len() - off]);
        assert(r[o.len() as int] == r[o.len() - off]);
        assert forall|j: int| 0 <= j < o1.len() implies #[trigger] r[j] == o1[j] by {
            if j == o.len() {
                assert(r[j] == r[j - off]);
            }
        }
        lemma_lz_copy_is(o1, r, off, (n - 1) as nat);
    }
}

/// `b` is `a` with an `n`-byte match written at `op`: the same before
/// `op`, and from `op` to `op + n` each byte equals the one `off` before
/// it. Bytes from `op + n` on are not constrained.
pub open spec fn matched(a: Seq<u8>, b: Seq<u8>, op: int, off: int, n: int) -> bool {
    &&& b.len() == a.len()
    &&& forall|j: int| 0 <= j < op ==> #[trigger] b[j] == a[j]
    &&& forall|j: int| op <= j < op + n ==> #[trigger] b[j] == b[j - off]
}

/// `matched` is `lz_copy`, on any window `lo..` that holds the offset.
pub proof fn lemma_matched(a: Seq<u8>, b: Seq<u8>, lo: int, op: int, off: int, n: int)
    requires
        matched(a, b, op, off, n),
        0 <= lo,
        1 <= off <= op - lo,
        0 <= n,
        op + n <= a.len(),
    ensures
        b.subrange(lo, op + n) == lz_copy(a.subrange(lo, op), off, n as nat),
{
    let o = a.subrange(lo, op);
    let r = b.subrange(lo, op + n);
    assert forall|j: int| 0 <= j < o.len() implies #[trigger] r[j] == o[j] by {
        assert(b[lo + j] == a[lo + j]);
    }
    assert forall|j: int| o.len() <= j < r.len() implies #[trigger] r[j] == r[j - off] by {
        assert(b[lo + j] == b[lo + j - off]);
    }
    lemma_lz_copy_is(o, r, off, n as nat);
}

/// `b` is `a` with `s[ip..ip + n]` written at `op`. Bytes from `op + n`
/// on are not constrained.
pub open spec fn placed(a: Seq<u8>, b: Seq<u8>, op: int, s: Seq<u8>, ip: int, n: int) -> bool {
    &&& b.len() == a.len()
    &&& forall|j: int| 0 <= j < op ==> #[trigger] b[j] == a[j]
    &&& forall|j: int| op <= j < op + n ==> #[trigger] b[j] == s[j - op + ip]
}

/// Writes at `op` the `n` bytes of a match `off` back. May also change
/// bytes after `op + n`.
#[inline(always)]
pub fn copy_match(out: &mut [u8], op: usize, off: usize, n: usize)
    requires
        1 <= off <= op,
        op + n <= old(out)@.len(),
    ensures
        matched(old(out)@, final(out)@, op as int, off as int, n as int),
{
    let len = out.len();
    let end = op + n;
    let src = op - off;
    if len - end < 16 {
        // Too near the end of the buffer for whole chunks: byte by byte.
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                out@.len() == len,
                end == op + n,
                end <= len,
                src == op - off,
                1 <= off <= op,
                forall|j: int| 0 <= j < op ==> #[trigger] out@[j] == old(out)@[j],
                forall|j: int| op <= j < op + k ==> #[trigger] out@[j] == out@[j - off],
            decreases n - k,
        {
            let b = get(out, src + k);
            set(out, op + k, b);
            k = k + 1;
        }
        return ;
    }
    let mut w = op;
    if off < 8 {
        // Each move writes the pattern again after itself, which doubles
        // the distance between `src` and `w`.
        while w - src < 8 && w < end
            invariant
                out@.len() == len,
                end == op + n,
                len - end >= 16,
                src == op - off,
                1 <= off <= op,
                op <= w,
                w <= len,
                forall|j: int| 0 <= j < op ==> #[trigger] out@[j] == old(out)@[j],
                forall|j: int| op <= j < w ==> #[trigger] out@[j] == out@[j - off],
                forall|j: int| 0 <= j < off ==> #[trigger] out@[w - off + j] == out@[src + j],
            decreases 16 - (w - src),
        {
            let ghost cur = out@;
            let gap = w - src;
            move8(out, src, w);
            proof {
                let new = out@;
                assert forall|j: int| op <= j < w + gap implies #[trigger] new[j] == new[j - off] by {
                    if j >= w {
                        let t = j - w;
                        assert(new[j] == cur[src + t]);
                        if t >= off {
                            assert(new[j - off] == cur[src + t - off]);
                            assert(cur[src + t] == cur[src + t - off]);
                        } else {
                            assert(new[j - off] == cur[w - off + t]);
                        }
                    } else {
                        assert(cur[j] == cur[j - off]);
                    }
                }
                assert forall|j: int| 0 <= j < off implies #[trigger] new[w + gap - off + j] == new[src + j] by {
                    assert(new[w + gap - off + j] == cur[src + gap - off + j]);
                    assert(cur[w - off + j] == cur[src + j]);
                }
            }
            w = w + gap;
        }
        if w >= end {
            return ;
        }
    }
    let d = w - src;
    let ghost w0 = w as int;
    if d >= 16 {
        while w < end
            invariant
                out@.len() == len,
                end == op + n,
                len - end >= 16,
                src == op - off,
                1 <= off <= op,
                op <= w0 <= w,
                d == w0 - src,
                d >= 16,
                w <= end + 15,
                forall|j: int| 0 <= j < op ==> #[trigger] out@[j] == old(out)@[j],
                forall|j: int| op <= j < w ==> #[trigger] out@[j] == out@[j - off],
                forall|j: int| w0 <= j < w ==> #[trigger] out@[j] == out@[j - d],
                forall|j: int| 0 <= j < off ==> #[trigger] out@[w0 - off + j] == out@[src + j],
            decreases end + 16 - w,
        {
            let ghost cur = out@;
            copy16(out, w - d, w);
            proof {
                lemma_chunk(cur, out@, op as int, off as int, w0, w as int, d as int, 16);
            }
            w = w + 16;
        }
    } else {
        while w < end
            invariant
                out@.len() == len,
                end == op + n,
                len - end >= 16,
                src == op - off,
                1 <= off <= op,
                op <= w0 <= w,
                d == w0 - src,
                d >= 8,
                w <= end + 7,
                forall|j: int| 0 <= j < op ==> #[trigger] out@[j] == old(out)@[j],
                forall|j: int| op <= j < w ==> #[trigger] out@[j] == out@[j - off],
                forall|j: int| w0 <= j < w ==> #[trigger] out@[j] == out@[j - d],
                forall|j: int| 0 <= j < off ==> #[trigger] out@[w0 - off + j] == out@[src + j],
            decreases end + 8 - w,
        {
            let ghost cur = out@;
            copy8(out, w - d, w);
            proof {
                lemma_chunk(cur, out@, op as int, off as int, w0, w as int, d as int, 8);
            }
            w = w + 8;
        }
    }
}

/// Writes at `op` the `n` bytes of a match at least 16 back, 32 bytes at
/// a time: no length to look at but the one loop test, and not even that
/// for the first 32. Writes up to 32 bytes past the end, which the
/// caller has room for.
#[inline(always)]
pub fn copy_match_wild(out: &mut [u8], op: usize, off: usize, n: usize)
    requires
        16 <= off <= op,
        op + n + 32 <= old(out)@.len(),
    ensures
        matched(old(out)@, final(out)@, op as int, off as int, n as int),
{
    let len = out.len();
    let end = op + n;
    let src = op - off;
    let ghost c0 = out@;
    copy16(out, src, op);
    proof {
        lemma_chunk(c0, out@, op as int, off as int, op as int, op as int, off as int, 16);
    }
    let ghost c1 = out@;
    copy16(out, src + 16, op + 16);
    proof {
        lemma_chunk(c1, out@, op as int, off as int, op as int, op + 16, off as int, 16);
    }
    let mut w = op + 32;
    while w < end
        invariant
            out@.len() == len,
            len == old(out)@.len(),
            end == op + n,
            end + 32 <= len,
            src == op - off,
            16 <= off <= op,
            op + 32 <= w <= end + 32,
            forall|j: int| 0 <= j < op ==> #[trigger] out@[j] == old(out)@[j],
            forall|j: int| op <= j < w ==> #[trigger] out@[j] == out@[j - off],
        decreases end + 32 - w,
    {
        let ghost cur = out@;
        copy16(out, w - off, w);
        proof {
            lemma_chunk(cur, out@, op as int, off as int, op as int, w as int, off as int, 16);
        }
        let ghost cur2 = out@;
        copy16(out, w + 16 - off, w + 16);
        proof {
            lemma_chunk(cur2, out@, op as int, off as int, op as int, w + 16, off as int, 16);
        }
        w = w + 32;
    }
}

/// One chunk of `c` bytes copied from `d` back, at `w`, keeps the match
/// property: every byte from `op` on equals the one `off` before it. `d`
/// need not be `off`: after the doubling moves it is a multiple of it,
/// which is carried here as two facts, that from `w0` (where the chunks
/// started) each byte equals the one `d` before it, and that the `off`
/// bytes before `w0` are the first `off` bytes of the pattern.
pub proof fn lemma_chunk(cur: Seq<u8>, new: Seq<u8>, op: int, off: int, w0: int, w: int, d: int, c: int)
    requires
        1 <= off <= op,
        op <= w0 <= w,
        0 <= c <= d,
        d == w0 - (op - off),
        w + c <= cur.len(),
        new.len() == cur.len(),
        forall|k: int|
            0 <= k < new.len() ==> #[trigger] new[k] == if w <= k < w + c {
                cur[k - w + (w - d)]
            } else {
                cur[k]
            },
        forall|j: int| op <= j < w ==> #[trigger] cur[j] == cur[j - off],
        forall|j: int| w0 <= j < w ==> #[trigger] cur[j] == cur[j - d],
        forall|j: int| 0 <= j < off ==> #[trigger] cur[w0 - off + j] == cur[(op - off) + j],
    ensures
        forall|j: int| 0 <= j < w ==> #[trigger] new[j] == cur[j],
        forall|j: int| op <= j < w + c ==> #[trigger] new[j] == new[j - off],
        forall|j: int| w0 <= j < w + c ==> #[trigger] new[j] == new[j - d],
        forall|j: int| 0 <= j < off ==> #[trigger] new[w0 - off + j] == new[(op - off) + j],
{
    let src = op - off;
    assert forall|j: int| op <= j < w + c implies #[trigger] new[j] == new[j - off] by {
        if j >= w {
            assert(new[j] == cur[j - d]);
            if j - off >= w {
                assert(new[j - off] == cur[j - off - d]);
                assert(cur[j - d] == cur[j - d - off]);
            } else if j - off >= w0 {
                assert(new[j - off] == cur[j - off]);
                assert(cur[j - off] == cur[j - off - d]);
                assert(cur[j - d] == cur[j - d - off]);
            } else {
                let t = j - w0;
                assert(new[j - off] == cur[w0 - off + t]);
                assert(cur[w0 - off + t] == cur[src + t]);
            }
        } else {
            assert(cur[j] == cur[j - off]);
        }
    }
    assert forall|j: int| w0 <= j < w + c implies #[trigger] new[j] == new[j - d] by {
        if j < w {
            assert(cur[j] == cur[j - d]);
        }
    }
    assert forall|j: int| 0 <= j < off implies #[trigger] new[w0 - off + j] == new[(op - off) + j] by {
        assert(cur[w0 - off + j] == cur[(op - off) + j]);
    }
}

/// `copy_match` for a match of at most 24 bytes from at least 8 back,
/// with 24 bytes of room: three 8-byte copies and no tests. May change
/// the bytes from `op + n` to `op + 24`.
#[inline(always)]
pub fn copy_match24(out: &mut [u8], op: usize, off: usize, n: usize)
    requires
        8 <= off <= op,
        n <= 24,
        op + 24 <= old(out)@.len(),
    ensures
        matched(old(out)@, final(out)@, op as int, off as int, n as int),
{
    let len = out.len();
    let src = op - off;
    let ghost a = out@;
    copy8(out, src, op);
    let ghost b = out@;
    proof {
        lemma_chunk(a, b, op as int, off as int, op as int, op as int, off as int, 8);
    }
    copy8(out, src + 8, op + 8);
    let ghost c = out@;
    proof {
        lemma_chunk(b, c, op as int, off as int, op as int, op + 8, off as int, 8);
    }
    copy8(out, src + 16, op + 16);
    proof {
        lemma_chunk(c, out@, op as int, off as int, op as int, op + 16, off as int, 8);
    }
}

/// `copy_match` for a match of at most 16 bytes from at least 8 back,
/// with 16 bytes of room: two 8-byte copies and no tests. May change the
/// bytes from `op + n` to `op + 16`.
#[inline(always)]
pub fn copy_match16(out: &mut [u8], op: usize, off: usize, n: usize)
    requires
        8 <= off <= op,
        n <= 16,
        op + 16 <= old(out)@.len(),
    ensures
        matched(old(out)@, final(out)@, op as int, off as int, n as int),
{
    let len = out.len();
    let src = op - off;
    let ghost a = out@;
    copy8(out, src, op);
    let ghost b = out@;
    proof {
        lemma_chunk(a, b, op as int, off as int, op as int, op as int, off as int, 8);
    }
    copy8(out, src + 8, op + 8);
    proof {
        lemma_chunk(b, out@, op as int, off as int, op as int, op + 8, off as int, 8);
    }
}

/// The longest run `copy_lits` copies 32 bytes at a time; longer ones are
/// one call of the platform's copy. Chosen by hand, not derived: the
/// trade-off is mostly the cost of the call and of memcpy's branches,
/// which the instruction-level model in `bench/crossover` cannot see
/// (its README has the details).
pub const WILD_MAX: usize = 192;

/// Writes `src[ip..ip + n]` at `op`. May also change bytes after
/// `op + n`.
#[inline(always)]
pub fn copy_lits(out: &mut [u8], op: usize, src: &[u8], ip: usize, n: usize)
    requires
        ip + n <= src@.len(),
        op + n <= old(out)@.len(),
    ensures
        placed(old(out)@, final(out)@, op as int, src@, ip as int, n as int),
{
    let sl = src.len();
    let ol = out.len();
    if n <= 16 && sl - ip >= 16 && ol - op >= 16 {
        copy16_in(out, op, src, ip);
    } else if n <= WILD_MAX && sl - ip - n >= 32 && ol - op - n >= 32 {
        copy_lits_wild(out, op, src, ip, n);
    } else {
        copy_in(out, op, src, ip, n);
    }
}

/// Writes `src[ip..ip + n]` at `op`, 32 bytes at a time: no length to
/// look at but the one loop test, and not even that for the first 32.
/// Reads and writes up to 32 bytes past the end, which the caller has
/// room for.
#[inline(always)]
pub fn copy_lits_wild(out: &mut [u8], op: usize, src: &[u8], ip: usize, n: usize)
    requires
        ip + n + 32 <= src@.len(),
        op + n + 32 <= old(out)@.len(),
    ensures
        placed(old(out)@, final(out)@, op as int, src@, ip as int, n as int),
{
    let sl = src.len();
    let ol = out.len();
    copy16_in(out, op, src, ip);
    copy16_in(out, op + 16, src, ip + 16);
    let mut k: usize = 32;
    while k < n
        invariant
            ip + n + 32 <= sl,
            op + n + 32 <= ol,
            sl == src@.len(),
            ol == out@.len(),
            ol == old(out)@.len(),
            32 <= k <= n + 32,
            forall|j: int| 0 <= j < op ==> #[trigger] out@[j] == old(out)@[j],
            forall|j: int| op <= j < op + k ==> #[trigger] out@[j] == src@[j - op + ip],
        decreases n + 32 - k,
    {
        copy16_in(out, op + k, src, ip + k);
        copy16_in(out, op + k + 16, src, ip + k + 16);
        k = k + 32;
    }
}

/// Byte `j` of the little-endian number in `n` bytes at `i`.
pub proof fn lemma_le_digit(s: Seq<u8>, i: int, n: nat, j: nat)
    requires
        j < n,
        0 <= i,
        i + n <= s.len(),
    ensures
        (le_bytes(s, i, n) / pow2(8 * j)) % 256 == s[i + j],
    decreases j,
{
    let r = le_bytes(s, i + 1, (n - 1) as nat);
    let v = le_bytes(s, i, n);
    assert(v == s[i] as nat + 256 * r);
    if j == 0 {
        lemma2_to64();
        assert(pow2(0) == 1);
        assert(v / 1 == v);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v as int, 256, r as int, s[i] as int);
    } else {
        lemma_le_digit(s, i + 1, (n - 1) as nat, (j - 1) as nat);
        lemma_pow2_adds(8, (8 * (j - 1)) as nat);
        lemma2_to64();
        assert(8 * j == 8 + 8 * (j - 1));
        lemma_pow2_pos((8 * (j - 1)) as nat);
        vstd::arithmetic::div_mod::lemma_div_denominator(v as int, 256, pow2((8 * (j - 1)) as nat) as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v as int, 256, r as int, s[i] as int);
        assert(i + 1 + (j - 1) == i + j);
    }
}

/// Byte `j` of a word loaded from `s` at `i` is `s[i + j]`.
pub proof fn lemma_word_byte(s: Seq<u8>, i: int, u: u64, j: u64)
    requires
        u as nat == le_word(s, i),
        j < 8,
        0 <= i,
        i + 8 <= s.len(),
    ensures
        ((u >> ((8 * j) as u64)) & 0xff) as nat == s[i + j],
{
    let sh = (8 * j) as u64;
    lemma_le_digit(s, i, 8, j as nat);
    vstd::bits::lemma_u64_shr_is_div(u, sh);
    crate::bits::lemma_and_mask(u >> sh, 8);
    crate::bits::lemma_mask(8);
    lemma2_to64();
}

/// How many bytes from `a` and from `b` agree, up to `max`, compared
/// eight at a time.
#[inline(always)]
pub fn eq_len(data: &[u8], a: usize, b: usize, max: usize) -> (k: usize)
    requires
        a + max <= data@.len(),
        b + max <= data@.len(),
    ensures
        k <= max,
        forall|j: int| 0 <= j < k ==> #[trigger] data@[a + j] == data@[b + j],
{
    let n = data.len();
    let mut k: usize = 0;
    while max - k >= 8
        invariant
            k <= max,
            a + max <= n,
            b + max <= n,
            n == data@.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] data@[a + j] == data@[b + j],
        decreases max - k,
    {
        let u = load_u64_le(data, a + k);
        let v = load_u64_le(data, b + k);
        let x = u ^ v;
        if x == 0 {
            proof {
                assert forall|j: int| 0 <= j < k + 8 implies #[trigger] data@[a + j] == data@[b + j] by {
                    if j >= k {
                        let q = (j - k) as u64;
                        lemma_word_byte(data@, (a + k) as int, u, q);
                        lemma_word_byte(data@, (b + k) as int, v, q);
                        assert(u == v) by (bit_vector)
                            requires
                                x == u ^ v,
                                x == 0,
                        ;
                    }
                }
            }
            k = k + 8;
        } else {
            let tz = x.trailing_zeros();
            let t = (tz / 8) as usize;
            proof {
                vstd::std_specs::bits::axiom_u64_trailing_zeros(x);
                assert forall|j: int| 0 <= j < k + t implies #[trigger] data@[a + j] == data@[b + j] by {
                    if j >= k {
                        let q = (j - k) as u64;
                        let tz64 = tz as u64;
                        lemma_word_byte(data@, (a + k) as int, u, q);
                        lemma_word_byte(data@, (b + k) as int, v, q);
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
                }
            }
            return k + t;
        }
    }
    while k < max && get(data, a + k) == get(data, b + k)
        invariant
            k <= max,
            a + max <= n,
            b + max <= n,
            n == data@.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] data@[a + j] == data@[b + j],
        decreases max - k,
    {
        k = k + 1;
    }
    k
}

/// The four bytes at `i` as a little-endian number.
#[inline(always)]
pub fn load32(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r as nat == le_bytes(b@, i as int, 4),
{
    // One copy that LLVM turns into a single 4-byte load (byte loads
    // get merged piecewise with the caller's other loads).
    let w = crate::prims::bytes4(b, i);
    let b0 = w[0] as u32;
    let b1 = w[1] as u32;
    let b2 = w[2] as u32;
    let b3 = w[3] as u32;
    proof {
        assert(w@[0] == b@[i as int] && w@[1] == b@[i + 1] && w@[2] == b@[i + 2] && w@[3] == b@[i + 3]);
        reveal_with_fuel(le_bytes, 5);
        assert((b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)) == b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) by (bit_vector)
            requires
                b0 < 256,
                b1 < 256,
                b2 < 256,
                b3 < 256,
        ;
    }
    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
}

} // verus!
