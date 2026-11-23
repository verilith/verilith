//! Stage 1 of the two-pass parser: the structural index.
//!
//! `structural_index` lists, in order, the positions of the bytes that stage
//! 2 needs to look at: brackets, commas and colons outside strings, both
//! quotes of every string, the first byte of every number or literal, and
//! the backslash that starts each escape. It works on 64-byte blocks with
//! bit masks, the way simdjson does.
//!
//! The spec functions below define each of those notions one byte at a time,
//! over the whole input. The executable code is proven to compute exactly
//! them. Positions past the end of the input read as spaces (`byte`), so the
//! last, partial block needs no special case in the spec.
#[allow(unused_imports)]
use crate::lanes::*;
#[allow(unused_imports)]
use crate::simd::*;
#[allow(unused_imports)]
use crate::spec::*;
#[allow(unused_imports)]
use verilith_simd::cpu::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Spec
// ---------------------------------------------------------------------------

/// Byte `i` of the input, or a space past its end.
pub open spec fn byte(s: Seq<u8>, i: int) -> u8 {
    if 0 <= i < s.len() {
        s[i]
    } else {
        0x20
    }
}

/// Byte `i` follows an odd-length run of backslashes that starts at or
/// after `st`. (This ignores strings: outside a string a backslash is an
/// error anyway.)
pub open spec fn esc(s: Seq<u8>, st: int, i: int) -> bool
    decreases i - st,
{
    if i <= st {
        false
    } else {
        byte(s, i - 1) == 0x5C && !esc(s, st, i - 1)
    }
}

/// An unescaped quote: it opens or closes a string.
pub open spec fn uq(s: Seq<u8>, st: int, i: int) -> bool {
    byte(s, i) == 0x22 && !esc(s, st, i)
}

/// An odd number of unescaped quotes in `[st, i]`: true from an opening
/// quote up to the byte before its closing quote.
pub open spec fn instr(s: Seq<u8>, st: int, i: int) -> bool
    decreases i - st + 1,
{
    if i < st {
        false
    } else {
        instr(s, st, i - 1) != uq(s, st, i)
    }
}

/// Part of a string, quotes included.
pub open spec fn strs(s: Seq<u8>, st: int, i: int) -> bool {
    instr(s, st, i) || uq(s, st, i)
}

/// Between the quotes of a string.
pub open spec fn inside(s: Seq<u8>, st: int, i: int) -> bool {
    instr(s, st, i) && !uq(s, st, i)
}

/// Outside strings, neither whitespace nor an operator: part of a number,
/// a literal, or garbage.
pub open spec fn scalar(s: Seq<u8>, st: int, i: int) -> bool {
    !(is_ws(byte(s, i)) || is_op(byte(s, i)) || strs(s, st, i))
}

pub open spec fn scalar_start(s: Seq<u8>, st: int, i: int) -> bool {
    scalar(s, st, i) && !(i > st && scalar(s, st, i - 1))
}

/// A backslash inside a string that is not itself escaped.
pub open spec fn escape_start(s: Seq<u8>, st: int, i: int) -> bool {
    byte(s, i) == 0x5C && inside(s, st, i) && !esc(s, st, i)
}

/// What stage 2 needs to see of well-formed JSON.
pub open spec fn sbase(s: Seq<u8>, st: int, i: int) -> bool {
    (is_op(byte(s, i)) && !strs(s, st, i)) || uq(s, st, i) || scalar_start(s, st, i)
        || escape_start(s, st, i)
}

/// The bytes the index lists: those of `sbase`, and the control
/// characters inside strings, which stage 2 then rejects where it meets
/// them. So stage 2 needs no other check of stage 1's.
pub open spec fn structural(s: Seq<u8>, st: int, i: int) -> bool {
    sbase(s, st, i) || bad(s, st, i)
}

/// A control character inside a string, which RFC 8259 forbids.
pub open spec fn bad(s: Seq<u8>, st: int, i: int) -> bool {
    byte(s, i) < 0x20 && inside(s, st, i)
}

/// The structural positions in `[a, b)`, in order.
pub open spec fn positions(s: Seq<u8>, st: int, a: int, b: int) -> Seq<int>
    decreases b - a,
{
    if b <= a {
        Seq::empty()
    } else {
        let p = positions(s, st, a, b - 1);
        if structural(s, st, b - 1) {
            p.push(b - 1)
        } else {
            p
        }
    }
}

/// The structural positions in `[w0, b)` as offsets from `w0`: what a
/// window of the index that starts at `w0` holds.
pub open spec fn rpos(s: Seq<u8>, st: int, w0: int, b: int) -> Seq<u32>
    decreases b - w0,
{
    if b <= w0 {
        Seq::empty()
    } else {
        let p = rpos(s, st, w0, b - 1);
        if structural(s, st, b - 1) {
            p.push((b - 1 - w0) as u32)
        } else {
            p
        }
    }
}

/// A window's offsets are its positions less `w0`.
pub proof fn lemma_rpos(s: Seq<u8>, st: int, w0: int, b: int)
    requires
        w0 <= b <= w0 + u32::MAX,
    ensures
        rpos(s, st, w0, b).len() == positions(s, st, w0, b).len(),
        forall|i: int|
            0 <= i < rpos(s, st, w0, b).len() ==> {
                &&& #[trigger] rpos(s, st, w0, b)[i] as int + w0 == positions(s, st, w0, b)[i]
                &&& w0 <= positions(s, st, w0, b)[i] < b
            },
    decreases b - w0,
{
    if b > w0 {
        lemma_rpos(s, st, w0, b - 1);
    }
}

/// The positions of `[a, c)` are those of `[a, b)` then those of `[b, c)`.
pub proof fn lemma_positions_split(s: Seq<u8>, st: int, a: int, b: int, c: int)
    requires
        a <= b <= c,
    ensures
        positions(s, st, a, c) == positions(s, st, a, b) + positions(s, st, b, c),
    decreases c - b,
{
    if c > b {
        lemma_positions_split(s, st, a, b, c - 1);
        let x = positions(s, st, a, b);
        let y = positions(s, st, b, c - 1);
        assert((x + y).push(c - 1) =~= x + y.push(c - 1));
    } else {
        assert(positions(s, st, a, b) + positions(s, st, b, c) =~= positions(s, st, a, b));
    }
}

/// No control character inside a string in `[st, b)`.
pub open spec fn clean(s: Seq<u8>, st: int, b: int) -> bool {
    forall|i: int| st <= i < b ==> !#[trigger] bad(s, st, i)
}

// ---------------------------------------------------------------------------
// Bit lemmas
// ---------------------------------------------------------------------------

#[verifier::bit_vector]
pub proof fn lemma_bit_ops(a: u64, b: u64, k: u64)
    requires
        k < 64,
    ensures
        ((a & b) >> k) & 1u64 == 1u64 <==> ((a >> k) & 1u64 == 1u64 && (b >> k) & 1u64 == 1u64),
        ((a | b) >> k) & 1u64 == 1u64 <==> ((a >> k) & 1u64 == 1u64 || (b >> k) & 1u64 == 1u64),
        ((a ^ b) >> k) & 1u64 == 1u64 <==> ((a >> k) & 1u64 == 1u64) != ((b >> k) & 1u64 == 1u64),
        ((!a) >> k) & 1u64 == 1u64 <==> !((a >> k) & 1u64 == 1u64),
{
}

#[verifier::bit_vector]
pub proof fn lemma_bit_shl1(a: u64, c: u64, k: u64)
    requires
        k < 64,
        c <= 1,
    ensures
        k > 0 ==> ((((a << 1u64) | c) >> k) & 1u64 == 1u64 <==> (a >> sub(k, 1u64)) & 1u64 == 1u64),
        k == 0 ==> ((((a << 1u64) | c) >> k) & 1u64 == 1u64 <==> c == 1u64),
        (a >> 63u64) <= 1,
        ((a >> 63u64) == 1u64) == ((a >> 63u64) & 1u64 == 1u64),
{
}

#[verifier::bit_vector]
pub proof fn lemma_bit_single(e: u64, k: u64, j: u64)
    requires
        k < 63,
        j < 64,
    ensures
        ((e | (1u64 << add(k, 1u64))) >> j) & 1u64 == 1u64 <==> ((e >> j) & 1u64 == 1u64 || j
            == add(k, 1u64)),
{
}

#[verifier::bit_vector]
pub proof fn lemma_bit_consts(k: u64)
    requires
        k < 64,
    ensures
        (0u64 >> k) & 1u64 == 0u64,
        (0xFFFF_FFFF_FFFF_FFFFu64 >> k) & 1u64 == 1u64,
        (1u64 >> k) & 1u64 == 1u64 <==> k == 0,
{
}

/// Prefix XOR by shifting: bit `k` of the result is the XOR of bits
/// `0..=k` of `x`.
pub open spec fn spec_prefix_xor(x: u64) -> u64 {
    let x1 = x ^ (x << 1u64);
    let x2 = x1 ^ (x1 << 2u64);
    let x3 = x2 ^ (x2 << 4u64);
    let x4 = x3 ^ (x3 << 8u64);
    let x5 = x4 ^ (x4 << 16u64);
    x5 ^ (x5 << 32u64)
}

#[verifier::bit_vector]
proof fn lemma_prefix_xor_bv(x: u64, r: u64)
    requires
        r == ({
            let x1 = x ^ (x << 1u64);
            let x2 = x1 ^ (x1 << 2u64);
            let x3 = x2 ^ (x2 << 4u64);
            let x4 = x3 ^ (x3 << 8u64);
            let x5 = x4 ^ (x4 << 16u64);
            x5 ^ (x5 << 32u64)
        }),
    ensures
        r ^ (r << 1u64) == x,
{
}

#[inline(always)]
pub fn prefix_xor(x: u64) -> (r: u64)
    ensures
        r ^ (r << 1u64) == x,
{
    let x1 = x ^ (x << 1u64);
    let x2 = x1 ^ (x1 << 2u64);
    let x3 = x2 ^ (x2 << 4u64);
    let x4 = x3 ^ (x3 << 8u64);
    let x5 = x4 ^ (x4 << 16u64);
    let r = x5 ^ (x5 << 32u64);
    proof {
        lemma_prefix_xor_bv(x, r);
    }
    r
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// One block
// ---------------------------------------------------------------------------

/// The byte classes of the block at `base`, as `classify64` reports them.
pub open spec fn block_classes(m: Masks, s: Seq<u8>, base: int) -> bool {
    forall|k: u64|
        k < 64 ==> {
            let c = #[trigger] byte(s, base + k);
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
            &&& bit64(m.ctrl, k) == (c < 0x20)
        }
}

/// The same without the control characters, which the NEON loop finds
/// another way.
pub open spec fn classes4(m: Masks, s: Seq<u8>, base: int) -> bool {
    forall|k: u64|
        k < 64 ==> {
            let c = #[trigger] byte(s, base + k);
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
        }
}

/// The branch-free escape scan (as in simdjson): it satisfies the
/// fixpoint `e == ((b & !e) << 1) | c`, which says bit by bit that a byte
/// is escaped exactly when it follows a backslash that is not itself
/// escaped.
#[verifier::bit_vector]
proof fn lemma_escape_fixpoint(b: u64, c: u64)
    requires
        c <= 1,
    ensures
        ({
            let pot = b & !c;
            let mo = (pot << 1u64) | 0xAAAA_AAAA_AAAA_AAAAu64;
            let et = mo.wrapping_sub(pot) ^ 0xAAAA_AAAA_AAAA_AAAAu64;
            let e = et ^ (b | c);
            &&& e == ((b & !e) << 1u64) | c
            &&& (et & b) >> 63u64 == (b & !e) >> 63u64
        }),
{
}

#[verifier::bit_vector]
proof fn lemma_fixpoint_bit(b: u64, e: u64, c: u64, k: u64)
    requires
        c <= 1,
        k < 64,
        e == ((b & !e) << 1u64) | c,
    ensures
        k == 0 ==> (((e >> k) & 1u64 == 1u64) == (c == 1u64)),
        k > 0 ==> (((e >> k) & 1u64 == 1u64) == ((b >> sub(k, 1u64)) & 1u64 == 1u64 && !((e
            >> sub(k, 1u64)) & 1u64 == 1u64))),
        ((b & !e) >> 63u64) <= 1u64,
        (((b & !e) >> 63u64) == 1u64) == ((b >> 63u64) & 1u64 == 1u64 && !((e >> 63u64) & 1u64
            == 1u64)),
{
}

/// Escape mask of the block at `base`: bit `k` is `esc(base + k)`. Also
/// returns `esc(base + 64)`, the carry into the next block.
#[inline(always)]
fn escapes(b: u64, carry: u64, Ghost(s): Ghost<Seq<u8>>, Ghost(st): Ghost<int>, Ghost(base): Ghost<
    int,
>) -> (r: (u64, u64))
    requires
        st <= base,
        carry <= 1,
        (carry == 1) == esc(s, st, base),
        forall|k: u64| k < 64 ==> #[trigger] bit64(b, k) == (byte(s, base + k) == 0x5C),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(r.0, k) == esc(s, st, base + k),
        r.1 <= 1,
        (r.1 == 1) == esc(s, st, base + 64),
{
    // Most blocks have no backslash; skipping the arithmetic then also
    // keeps it off the chain of dependences from one block to the next.
    if b == 0 && carry == 0 {
        proof {
            assert(0u64 == ((0u64 & !0u64) << 1u64) | 0u64) by (bit_vector);
            assert forall|k: u64| k < 64 implies #[trigger] bit64(0u64, k) == esc(s, st, base + k) by {
                lemma_escape_bits(s, st, base, 0, 0, 0, k);
            }
            assert(bit64(b, 63) == (byte(s, base + 63) == 0x5C));
            assert(!bit64(0u64, 63)) by (bit_vector);
        }
        return (0, 0);
    }
    const ODD: u64 = 0xAAAA_AAAA_AAAA_AAAA;
    let pot = b & !carry;
    let mo = (pot << 1u64) | ODD;
    let et = mo.wrapping_sub(pot) ^ ODD;
    let e = et ^ (b | carry);
    let out = (et & b) >> 63u64;
    proof {
        lemma_escape_fixpoint(b, carry);
        lemma_fixpoint_bit(b, e, carry, 0);
        lemma_escape_bits(s, st, base, b, e, carry, 63);
        assert forall|k: u64| k < 64 implies #[trigger] bit64(e, k) == esc(s, st, base + k) by {
            lemma_escape_bits(s, st, base, b, e, carry, k);
        }
        assert(esc(s, st, base + 64) == (byte(s, base + 63) == 0x5C && !esc(s, st, base + 63)));
        assert(bit64(b, 63) == (byte(s, base + 63) == 0x5C));
        assert(bit64(e, 63) == esc(s, st, base + 63));
    }
    (e, out)
}

/// From the fixpoint, bit `k` of `e` is `esc(base + k)`, by induction on `k`.
proof fn lemma_escape_bits(s: Seq<u8>, st: int, base: int, b: u64, e: u64, c: u64, k: u64)
    requires
        st <= base,
        c <= 1,
        k < 64,
        (c == 1) == esc(s, st, base),
        forall|j: u64| j < 64 ==> #[trigger] bit64(b, j) == (byte(s, base + j) == 0x5C),
        e == ((b & !e) << 1u64) | c,
    ensures
        bit64(e, k) == esc(s, st, base + k),
    decreases k,
{
    lemma_fixpoint_bit(b, e, c, k);
    if k > 0 {
        lemma_escape_bits(s, st, base, b, e, c, (k - 1) as u64);
        assert(bit64(b, (k - 1) as u64) == (byte(s, base + (k - 1)) == 0x5C));
    }
}

#[verifier::bit_vector]
proof fn lemma_clear_lowest(m: u64, t: u64, j: u64)
    requires
        t < 64,
        j < 64,
        (m >> t) & 1u64 == 1u64,
        m << sub(64u64, t) == 0u64,
    ensures
        (((m & m.wrapping_sub(1u64)) >> j) & 1u64 == 1u64) == ((m >> j) & 1u64 == 1u64 && j != t),
{
}

#[verifier::bit_vector]
proof fn lemma_carry_xor(p: u64, u: u64, c: u64)
    requires
        p ^ (p << 1u64) == u,
        c == 0u64 || c == 0xFFFF_FFFF_FFFF_FFFFu64,
    ensures
        (p ^ c) ^ (((p ^ c) << 1u64) | (c & 1u64)) == u,
        (c & 1u64) <= 1,
        (c & 1u64 == 1u64) == (c == 0xFFFF_FFFF_FFFF_FFFFu64),
{
}

#[verifier::bit_vector]
proof fn lemma_spread(r: u64)
    ensures
        (r >> 63u64) <= 1,
        0u64.wrapping_sub(r >> 63u64) == 0u64 || 0u64.wrapping_sub(r >> 63u64)
            == 0xFFFF_FFFF_FFFF_FFFFu64,
        (0u64.wrapping_sub(r >> 63u64) == 0xFFFF_FFFF_FFFF_FFFFu64) == ((r >> 63u64) & 1u64
            == 1u64),
{
}

/// From `r ^ (r << 1 | c) == u`: bit `k` of `r` is the parity of `c` and
/// bits `0..=k` of `u`, which is `instr` when `u` holds the unescaped quotes.
proof fn lemma_instr_bits(s: Seq<u8>, st: int, base: int, r: u64, u: u64, c: u64, k: u64)
    requires
        st <= base,
        k < 64,
        c <= 1,
        r ^ ((r << 1u64) | c) == u,
        (c == 1) == instr(s, st, base - 1),
        forall|j: u64| j < 64 ==> #[trigger] bit64(u, j) == uq(s, st, base + j),
    ensures
        bit64(r, k) == instr(s, st, base + k),
    decreases k,
{
    lemma_bit_ops(r, (r << 1u64) | c, k);
    lemma_bit_shl1(r, c, k);
    assert(bit64(u, k) == uq(s, st, base + k));
    if k > 0 {
        lemma_instr_bits(s, st, base, r, u, c, (k - 1) as u64);
    }
}

/// Per-bit meaning of the block's derived masks.
proof fn lemma_block_bits(
    s: Seq<u8>,
    st: int,
    base: int,
    m: Masks,
    e: u64,
    u: u64,
    r: u64,
    strs_m: u64,
    inside_m: u64,
    scalar_m: u64,
    prev: u64,
    starts_m: u64,
    escs_m: u64,
    st_m: u64,
    bad_m: u64,
    k: u64,
)
    requires
        st <= base,
        k < 64,
        prev <= 1,
        (prev == 1) == (base > st && scalar(s, st, base - 1)),
        classes4(m, s, base),
        forall|j: u64| j < 64 ==> #[trigger] bit64(e, j) == esc(s, st, base + j),
        forall|j: u64| j < 64 ==> #[trigger] bit64(r, j) == instr(s, st, base + j),
        u == m.quote & !e,
        strs_m == r | u,
        inside_m == r & !u,
        scalar_m == !(m.ws | m.op | strs_m),
        starts_m == scalar_m & !((scalar_m << 1u64) | prev),
        escs_m == m.backslash & inside_m & !e,
        st_m == (m.op & !strs_m) | u | starts_m | escs_m,
        bad_m == m.ctrl & inside_m,
    ensures
        bit64(u, k) == uq(s, st, base + k),
        bit64(scalar_m, k) == scalar(s, st, base + k),
        bit64(st_m, k) == sbase(s, st, base + k),
        bit64(bad_m, k) == (bit64(m.ctrl, k) && inside(s, st, base + k)),
    decreases k,
{
    let c = byte(s, base + k);
    assert(bit64(m.quote, k) == (c == 0x22));
    assert(bit64(m.backslash, k) == (c == 0x5C));
    assert(bit64(m.ws, k) == is_ws(c));
    assert(bit64(m.op, k) == is_op(c));
    assert(bit64(e, k) == esc(s, st, base + k));
    assert(bit64(r, k) == instr(s, st, base + k));
    lemma_bit_ops(m.quote, !e, k);
    lemma_bit_ops(e, e, k);
    lemma_bit_ops(r, u, k);
    lemma_bit_ops(r, !u, k);
    lemma_bit_ops(u, u, k);
    lemma_bit_ops(m.ws, m.op, k);
    lemma_bit_ops(m.ws | m.op, strs_m, k);
    lemma_bit_ops(m.ws | m.op | strs_m, 0, k);
    lemma_bit_ops(scalar_m, !((scalar_m << 1u64) | prev), k);
    lemma_bit_ops((scalar_m << 1u64) | prev, 0, k);
    lemma_bit_shl1(scalar_m, prev, k);
    lemma_bit_ops(m.backslash, inside_m, k);
    lemma_bit_ops(m.backslash & inside_m, !e, k);
    lemma_bit_ops(m.op, !strs_m, k);
    lemma_bit_ops(strs_m, strs_m, k);
    lemma_bit_ops(m.op & !strs_m, u, k);
    lemma_bit_ops((m.op & !strs_m) | u, starts_m, k);
    lemma_bit_ops((m.op & !strs_m) | u | starts_m, escs_m, k);
    lemma_bit_ops(m.ctrl, inside_m, k);
    assert(bit64(u, k) == uq(s, st, base + k));
    assert(bit64(scalar_m, k) == scalar(s, st, base + k));
    if k > 0 {
        lemma_block_bits(
            s,
            st,
            base,
            m,
            e,
            u,
            r,
            strs_m,
            inside_m,
            scalar_m,
            prev,
            starts_m,
            escs_m,
            st_m,
            bad_m,
            (k - 1) as u64,
        );
        assert(bit64(scalar_m, (k - 1) as u64) == scalar(s, st, base + k - 1));
    }
}

proof fn lemma_positions_block(s: Seq<u8>, st: int, w0: int, base: int, m: u64, j: int)
    requires
        w0 <= base,
        0 <= j <= 64,
        base - w0 + 64 <= u32::MAX,
        forall|k: u64| k < 64 ==> #[trigger] bit64(m, k) == structural(s, st, base + k),
    ensures
        rpos(s, st, w0, base + j) == rpos(s, st, w0, base) + bits_upto(m, base - w0, j),
    decreases j,
{
    if j > 0 {
        lemma_positions_block(s, st, w0, base, m, j - 1);
        assert(bit64(m, (j - 1) as u64) == structural(s, st, base + j - 1));
        let a = rpos(s, st, w0, base);
        let b = bits_upto(m, base - w0, j - 1);
        assert((a + b).push((base - w0 + j - 1) as u32) =~= a + b.push((base - w0 + j - 1) as u32));
        assert((base + j - 1 - w0) as u32 == (base - w0 + j - 1) as u32);
    } else {
        assert(rpos(s, st, w0, base) + bits_upto(m, base - w0, 0) =~= rpos(s, st, w0, base));
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// The whole input
// ---------------------------------------------------------------------------

proof fn lemma_mask_zero(m: u64)
    ensures
        (m == 0) == (forall|k: u64| k < 64 ==> !#[trigger] bit64(m, k)),
{
    if m == 0 {
        assert forall|k: u64| k < 64 implies !#[trigger] bit64(m, k) by {
            lemma_bit_consts(k);
        }
    } else {
        vstd::std_specs::bits::axiom_u64_trailing_zeros(m);
        let t = vstd::std_specs::bits::u64_trailing_zeros(m) as u64;
        assert(bit64(m, t));
    }
}

#[verifier::bit_vector]
proof fn lemma_or_zero(a: u64, b: u64)
    ensures
        ((a | b) == 0u64) == (a == 0u64 && b == 0u64),
{
}

/// Past the end of the input every byte reads as a space, which changes
/// nothing.
proof fn lemma_past_end(s: Seq<u8>, st: int, i: int)
    requires
        st <= i,
        s.len() <= i,
        st <= s.len(),
    ensures
        !structural(s, st, i),
        !bad(s, st, i),
        !scalar(s, st, i),
        instr(s, st, i) == instr(s, st, s.len() - 1),
    decreases i,
{
    assert(byte(s, i) == 0x20);
    if i > s.len() {
        lemma_past_end(s, st, i - 1);
    }
}

proof fn lemma_positions_past_end(s: Seq<u8>, st: int, w0: int, b: int)
    requires
        st <= w0 <= s.len() <= b,
    ensures
        rpos(s, st, w0, b) == rpos(s, st, w0, s.len() as int),
        clean(s, st, b) == clean(s, st, s.len() as int),
    decreases b,
{
    if b > s.len() {
        lemma_positions_past_end(s, st, w0, b - 1);
        lemma_past_end(s, st, b - 1);
        if clean(s, st, b - 1) {
            assert forall|i: int| st <= i < b implies !#[trigger] bad(s, st, i) by {
                if i == b - 1 {
                } else {
                    assert(!bad(s, st, i));
                }
            }
        }
    }
}

/// Stage 1's state between blocks.
#[derive(Clone, Copy)]
pub struct Stage1 {
    /// Positions written so far, in the current window.
    pub w: usize,
    /// Whether the next block starts escaped.
    pub carry_esc: u64,
    /// All ones when the next block starts inside a string.
    pub in_str: u64,
    /// Whether the byte before the next block is part of a scalar.
    pub prev: u64,
    /// Nonzero once a control character inside a string was seen.
    pub err: u64,
    /// The structural bits of the last block, not yet written, which
    /// starts at `pbase` bytes into the window.
    pub pend: u64,
    pub pbase: u32,
}

/// The state after the blocks before `base`, in the window that starts
/// at `w0` and has room for the positions of the bytes up to `lim`.
pub open spec fn stage1_inv(g: Seq<u8>, gst: int, w0: int, lim: int, base: int, idx: Seq<u32>, t: Stage1) -> bool {
    &&& 0 <= gst <= w0 <= base
    &&& lim <= g.len()
    &&& lim - w0 + 128 <= u32::MAX
    &&& idx.len() >= lim - w0 + 64
    &&& w0 + t.pbase <= base
    &&& w0 + t.pbase <= lim
    &&& t.w <= t.pbase
    &&& t.w + bits_upto(t.pend, t.pbase as int, 64).len() <= base - w0
    &&& idx.subrange(0, t.w as int) + bits_upto(t.pend, t.pbase as int, 64) == rpos(g, gst, w0, base)
    &&& t.carry_esc <= 1
    &&& (t.carry_esc == 1) == esc(g, gst, base)
    &&& (t.in_str == 0 || t.in_str == 0xFFFF_FFFF_FFFF_FFFFu64)
    &&& (t.in_str == 0xFFFF_FFFF_FFFF_FFFFu64) == instr(g, gst, base - 1)
    &&& t.prev <= 1
    &&& (t.prev == 1) == (base > gst && scalar(g, gst, base - 1))
    &&& (t.err == 0) == clean(g, gst, base)
}

/// The part of stage 1's state that the bit logic carries, but for the
/// error word.
pub open spec fn core_inv(g: Seq<u8>, gst: int, base: int, t: Stage1) -> bool {
    &&& 0 <= gst <= base
    &&& t.carry_esc <= 1
    &&& (t.carry_esc == 1) == esc(g, gst, base)
    &&& (t.in_str == 0 || t.in_str == 0xFFFF_FFFF_FFFF_FFFFu64)
    &&& (t.in_str == 0xFFFF_FFFF_FFFF_FFFFu64) == instr(g, gst, base - 1)
    &&& t.prev <= 1
    &&& (t.prev == 1) == (base > gst && scalar(g, gst, base - 1))
}

/// The part of stage 1's state that the bit logic carries.
pub open spec fn logic_inv(g: Seq<u8>, gst: int, base: int, t: Stage1) -> bool {
    &&& core_inv(g, gst, base, t)
    &&& (t.err == 0) == clean(g, gst, base)
}

/// A mask of the control characters inside strings of a block is zero
/// exactly when there are none.
proof fn lemma_bad_mask(g: Seq<u8>, gst: int, base: int, m: u64)
    requires
        forall|k: u64| k < 64 ==> #[trigger] bit64(m, k) == bad(g, gst, base + k),
    ensures
        (m == 0) == (forall|i: int| base <= i < base + 64 ==> !#[trigger] bad(g, gst, i)),
{
    if m == 0 {
        assert forall|i: int| base <= i < base + 64 implies !#[trigger] bad(g, gst, i) by {
            let k = (i - base) as u64;
            lemma_bit_consts(k);
            assert(bit64(m, k) == bad(g, gst, base + k));
        }
    } else {
        vstd::std_specs::bits::axiom_u64_trailing_zeros(m);
        let k = vstd::std_specs::bits::u64_trailing_zeros(m) as u64;
        assert(bit64(m, k));
        assert(bad(g, gst, base + k));
    }
}

/// The error word after the bytes `[a, b)`.
proof fn lemma_err_range(g: Seq<u8>, gst: int, a: int, b: int, err0: u64, e: u64)
    requires
        gst <= a <= b,
        (err0 == 0) == clean(g, gst, a),
        (e == 0) == (forall|i: int| a <= i < b ==> !#[trigger] bad(g, gst, i)),
    ensures
        ((err0 | e) == 0) == clean(g, gst, b),
{
    lemma_or_zero(err0, e);
}

/// The bit logic of the block at `base`, from its classes `m`, escape
/// mask `e` (with carry out `c2`) and string mask `p`: the structural
/// bits, the bits of `m.ctrl` inside strings, and the state carried on.
/// Writes nothing and leaves the error word alone.
#[inline(always)]
fn block_core(
    m: Masks,
    e: u64,
    c2: u64,
    p: u64,
    base: usize,
    t: Stage1,
    Ghost(g): Ghost<Seq<u8>>,
    Ghost(gst): Ghost<int>,
) -> (o: (u64, u64, Stage1))
    requires
        core_inv(g, gst, base as int, t),
        base < g.len(),
        classes4(m, g, base as int),
        forall|k: u64| k < 64 ==> #[trigger] bit64(e, k) == esc(g, gst, base + k),
        c2 <= 1,
        (c2 == 1) == esc(g, gst, base + 64),
        p ^ (p << 1u64) == m.quote & !e,
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(o.0, k) == sbase(g, gst, base + k),
        forall|k: u64| k < 64 ==> #[trigger] bit64(o.1, k) == (bit64(m.ctrl, k) && inside(g, gst, base + k)),
        core_inv(g, gst, base + 64, o.2),
        o.2.err == t.err,
        o.2.w == t.w,
        o.2.pend == t.pend,
        o.2.pbase == t.pbase,
{
    let in_str = t.in_str;
    let prev = t.prev;
    let u = m.quote & !e;
    proof {
        assert forall|k: u64| k < 64 implies #[trigger] bit64(u, k) == uq(g, gst, base + k) by {
            lemma_bit_ops(m.quote, !e, k);
            lemma_bit_ops(e, e, k);
            assert(bit64(m.quote, k) == (byte(g, base + k) == 0x22));
            assert(bit64(e, k) == esc(g, gst, base + k));
        }
    }
    let r = p ^ in_str;
    proof {
        lemma_carry_xor(p, u, in_str);
        assert forall|k: u64| k < 64 implies #[trigger] bit64(r, k) == instr(g, gst, base + k) by {
            lemma_instr_bits(g, gst, base as int, r, u, in_str & 1u64, k);
        }
    }
    let strs_m = r | u;
    let inside_m = r & !u;
    let scalar_m = !(m.ws | m.op | strs_m);
    let starts_m = scalar_m & !((scalar_m << 1u64) | prev);
    let escs_m = m.backslash & inside_m & !e;
    let st_m = (m.op & !strs_m) | u | starts_m | escs_m;
    let bad_m = m.ctrl & inside_m;
    proof {
        assert forall|k: u64| k < 64 implies {
            &&& #[trigger] bit64(st_m, k) == sbase(g, gst, base + k)
            &&& bit64(bad_m, k) == (bit64(m.ctrl, k) && inside(g, gst, base + k))
            &&& bit64(scalar_m, k) == scalar(g, gst, base + k)
        } by {
            lemma_block_bits(
                g,
                gst,
                base as int,
                m,
                e,
                u,
                r,
                strs_m,
                inside_m,
                scalar_m,
                prev,
                starts_m,
                escs_m,
                st_m,
                bad_m,
                k,
            );
        }
    }
    proof {
        assert forall|k: u64| k < 64 implies #[trigger] bit64(bad_m, k) == (bit64(m.ctrl, k) && inside(
            g,
            gst,
            base + k,
        )) by {
            lemma_block_bits(g, gst, base as int, m, e, u, r, strs_m, inside_m, scalar_m, prev, starts_m, escs_m, st_m, bad_m, k);
        }
        lemma_spread(r);
        lemma_bit_shl1(scalar_m, 0, 63);
        lemma_bit_shl1(r, 0, 63);
        assert(bit64(r, 63) == instr(g, gst, base + 63));
        assert(bit64(st_m, 63) == sbase(g, gst, base + 63));
        assert(bit64(scalar_m, 63) == scalar(g, gst, base + 63));
    }
    (st_m, bad_m, Stage1 { w: t.w, carry_esc: c2, in_str: 0u64.wrapping_sub(r >> 63u64), prev: scalar_m >> 63u64, err: t.err, pend: t.pend, pbase: t.pbase })
}

/// `block_core`, with the control characters inside strings added to the
/// error word.
#[inline(always)]
fn block_logic(
    m: Masks,
    e: u64,
    c2: u64,
    p: u64,
    base: usize,
    t: Stage1,
    Ghost(g): Ghost<Seq<u8>>,
    Ghost(gst): Ghost<int>,
) -> (o: (u64, Stage1))
    requires
        logic_inv(g, gst, base as int, t),
        base < g.len(),
        block_classes(m, g, base as int),
        forall|k: u64| k < 64 ==> #[trigger] bit64(e, k) == esc(g, gst, base + k),
        c2 <= 1,
        (c2 == 1) == esc(g, gst, base + 64),
        p ^ (p << 1u64) == m.quote & !e,
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(o.0, k) == structural(g, gst, base + k),
        logic_inv(g, gst, base + 64, o.1),
        o.1.w == t.w,
        o.1.pend == t.pend,
        o.1.pbase == t.pbase,
{
    let (sb_m, bad_m, t2) = block_core(m, e, c2, p, base, t, Ghost(g), Ghost(gst));
    proof {
        assert forall|k: u64| k < 64 implies #[trigger] bit64(bad_m, k) == bad(g, gst, base + k) by {
            assert(bit64(m.ctrl, k) == (byte(g, base + k) < 0x20));
        }
        lemma_bad_mask(g, gst, base as int, bad_m);
        lemma_err_range(g, gst, base as int, base + 64, t2.err, bad_m);
    }
    let st_m = sb_m | bad_m;
    proof {
        assert forall|k: u64| k < 64 implies #[trigger] bit64(st_m, k) == structural(g, gst, base + k) by {
            lemma_bit_ops(sb_m, bad_m, k);
            assert(bit64(sb_m, k) == sbase(g, gst, base + k));
            assert(bit64(bad_m, k) == bad(g, gst, base + k));
        }
    }
    (st_m, Stage1 { w: t2.w, carry_esc: t2.carry_esc, in_str: t2.in_str, prev: t2.prev, err: t2.err | bad_m, pend: t2.pend, pbase: t2.pbase })
}

/// The block at `base`, held in four NEON vectors. Each class mask is
/// made where the bit logic first needs it (the backslashes for the
/// escapes, then the quotes for the strings, then the rest), so that the
/// vector work of one overlaps the scalar work of the one before.
///
/// The control characters come in one mask with the bytes from 0x80 up.
/// Returned with the structural bits and the state are that mask inside
/// strings, and that mask outside whitespace: where the latter is zero
/// the block is ASCII and the former is its errors.
#[inline(always)]
fn block_neon(
    v0: verilith_simd::neon::uint8x16_t,
    v1: verilith_simd::neon::uint8x16_t,
    v2: verilith_simd::neon::uint8x16_t,
    v3: verilith_simd::neon::uint8x16_t,
    base: usize,
    t: Stage1,
    Ghost(g): Ghost<Seq<u8>>,
    Ghost(gst): Ghost<int>,
) -> (o: (u64, Stage1, u64, u64))
    requires
        kernel_cpu(NEON),
        verilith_simd::neon::neon(),
        crate::neon::holds64(g, base as int, v0, v1, v2, v3),
        core_inv(g, gst, base as int, t),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(o.0, k) == sbase(g, gst, base + k),
        core_inv(g, gst, base + 64, o.1),
        o.1.err == t.err,
        low_masks(g, gst, base as int, o.2, o.3),
{
    let ghost b = base as int;
    let backslash = crate::neon::eq_mask64(v0, v1, v2, v3, 0x5C, Ghost(g), Ghost(b));
    proof {
        assert forall|k: u64| k < 64 implies #[trigger] bit64(backslash, k) == (byte(g, base + k) == 0x5C) by {
            assert(byte(g, base + k) == g[b + k]);
        }
    }
    let (e, c2) = escapes(backslash, t.carry_esc, Ghost(g), Ghost(gst), Ghost(b));
    let quote = crate::neon::eq_mask64(v0, v1, v2, v3, 0x22, Ghost(g), Ghost(b));
    let p = prefix_xor_clmul::<NEON>(quote & !e);
    let ws = crate::neon::ws_mask64(v0, v1, v2, v3, Ghost(g), Ghost(b));
    let (op, low) = crate::neon::op_low_mask64(v0, v1, v2, v3, Ghost(g), Ghost(b));
    let m = Masks { quote, backslash, ws, op, ctrl: low };
    proof {
        assert forall|k: u64| k < 64 implies {
            let c = #[trigger] byte(g, base + k);
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
        } by {
            assert(byte(g, base + k) == g[b + k]);
        }
    }
    let (st_m, ea, t2) = block_core(m, e, c2, p, base, t, Ghost(g), Ghost(gst));
    let ra = low & !ws;
    proof {
        assert forall|k: u64| k < 64 implies {
            &&& #[trigger] bit64(ea, k) == (crate::neon::lowb(g[b + k]) && inside(g, gst, b + k))
            &&& bit64(ra, k) == (crate::neon::lowb(g[b + k]) && !is_ws(g[b + k]))
        } by {
            assert(bit64(ea, k) == (bit64(m.ctrl, k) && inside(g, gst, base + k)));
            assert(bit64(low, k) == crate::neon::lowb(g[b + k]));
            assert(bit64(ws, k) == is_ws(g[b + k]));
            lemma_bit_ops(low, !ws, k);
            lemma_bit_ops(ws, ws, k);
        }
    }
    (st_m, t2, ea, ra)
}

/// What `block_neon` says of the control characters and high bytes of the
/// block at `b`.
pub open spec fn low_masks(g: Seq<u8>, gst: int, b: int, ea: u64, ra: u64) -> bool {
    forall|k: u64|
        k < 64 ==> {
            &&& #[trigger] bit64(ea, k) == (crate::neon::lowb(g[b + k]) && inside(g, gst, b + k))
            &&& bit64(ra, k) == (crate::neon::lowb(g[b + k]) && !is_ws(g[b + k]))
        }
}

/// With nothing low outside whitespace, the block is ASCII and `ea` is
/// its errors.
proof fn lemma_low_ascii(g: Seq<u8>, gst: int, b: int, ea: u64, ra: u64)
    requires
        0 <= b,
        b + 64 <= g.len(),
        low_masks(g, gst, b, ea, ra),
        ra == 0,
    ensures
        crate::utf8::ascii_span(g, b, b + 64),
        forall|k: u64| k < 64 ==> #[trigger] bit64(ea, k) == bad(g, gst, b + k),
{
    assert forall|k: u64| k < 64 implies g[b + k] < 0x80 && #[trigger] bit64(ea, k) == bad(g, gst, b + k) by {
        lemma_bit_consts(k);
        assert(bit64(ea, k) == (crate::neon::lowb(g[b + k]) && inside(g, gst, b + k)));
        assert(!bit64(ra, k));
        assert(byte(g, b + k) == g[b + k]);
    }
    assert forall|t: int| b <= t < b + 64 implies #[trigger] g[t] < 0x80 by {
        let k = (t - b) as u64;
        assert(bit64(ea, k) == bad(g, gst, b + k));
    }
}

/// The structural bits of a block: those of `sbase` and the control
/// characters inside strings.
proof fn lemma_struct_mask(g: Seq<u8>, gst: int, b: int, sm: u64, bm: u64)
    requires
        forall|k: u64| k < 64 ==> #[trigger] bit64(sm, k) == sbase(g, gst, b + k),
        forall|k: u64| k < 64 ==> #[trigger] bit64(bm, k) == bad(g, gst, b + k),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(sm | bm, k) == structural(g, gst, b + k),
{
    assert forall|k: u64| k < 64 implies #[trigger] bit64(sm | bm, k) == structural(g, gst, b + k) by {
        lemma_bit_ops(sm, bm, k);
        assert(bit64(sm, k) == sbase(g, gst, b + k));
        assert(bit64(bm, k) == bad(g, gst, b + k));
    }
}

/// Two blocks' error masks are zero exactly when the 128 bytes have no
/// control character inside a string.
proof fn lemma_bad_pair(g: Seq<u8>, gst: int, b: int, xa: u64, xb: u64)
    requires
        forall|k: u64| k < 64 ==> #[trigger] bit64(xa, k) == bad(g, gst, b + k),
        forall|k: u64| k < 64 ==> #[trigger] bit64(xb, k) == bad(g, gst, b + 64 + k),
    ensures
        ((xa | xb) == 0) == (forall|i: int| b <= i < b + 128 ==> !#[trigger] bad(g, gst, i)),
{
    lemma_bad_mask(g, gst, b, xa);
    assert forall|k: u64| k < 64 implies #[trigger] bit64(xb, k) == bad(g, gst, (b + 64) + k) by {
        assert(bit64(xb, k) == bad(g, gst, b + 64 + k));
    }
    lemma_bad_mask(g, gst, b + 64, xb);
    lemma_or_zero(xa, xb);
    if (xa | xb) == 0 {
        assert forall|i: int| b <= i < b + 128 implies !#[trigger] bad(g, gst, i) by {
            if i < b + 64 {
                assert(!bad(g, gst, i));
            } else {
                assert(!bad(g, gst, i));
            }
        }
    } else {
        if xa != 0 {
            let i = choose|i: int| b <= i < b + 64 && #[trigger] bad(g, gst, i);
            assert(bad(g, gst, i));
        } else {
            let i = choose|i: int| b + 64 <= i < b + 128 && #[trigger] bad(g, gst, i);
            assert(bad(g, gst, i));
        }
    }
}

/// The two blocks at `b` when one may hold bytes from 0x80 up, or follows
/// one that ends with them: finds those bytes, runs the UTF-8 check on
/// both blocks, and takes them out of the error masks. Out of line, as
/// its vector work would crowd the loop's registers. Returns the errors
/// of the two blocks and the UTF-8 check's new `ok` and `pa`.
#[cold]
#[inline(never)]
fn rare_pair(
    s: &[u8],
    st: usize,
    b: usize,
    uj: usize,
    ok: bool,
    pa: bool,
    ea: u64,
    eb: u64,
    Ghost(ra): Ghost<u64>,
    Ghost(rb): Ghost<u64>,
) -> (r: (u64, u64, bool, bool))
    requires
        verilith_simd::neon::neon(),
        crate::utf8::u8_state(s@, st as int, uj as int, ok),
        st <= b,
        b + 128 <= s@.len(),
        (uj == st + 3 && b == st) || (uj == b && st + 3 <= b),
        pa ==> crate::utf8::ascii_span(s@, uj - 3, b as int),
        low_masks(s@, st as int, b as int, ea, ra),
        low_masks(s@, st as int, b + 64, eb, rb),
    ensures
        crate::utf8::u8_state(s@, st as int, b + 128, r.2),
        r.3 ==> crate::utf8::ascii_span(s@, b + 125, b + 128),
        forall|k: u64| k < 64 ==> #[trigger] bit64(r.0, k) == bad(s@, st as int, b + k),
        forall|k: u64| k < 64 ==> #[trigger] bit64(r.1, k) == bad(s@, st as int, b + 64 + k),
{
    let _n = s.len();
    let ghost g = s@;
    let ghost gst = st as int;
    let va = crate::neon::load64(s, b);
    let na = crate::neon::high_mask64(va.0, va.1, va.2, va.3, Ghost(g), Ghost(b as int));
    let vb = crate::neon::load64(s, b + 64);
    let nb = crate::neon::high_mask64(vb.0, vb.1, vb.2, vb.3, Ghost(g), Ghost(b + 64));
    proof {
        lemma_high_zero(g, b as int, na);
        lemma_high_zero(g, b + 64, nb);
    }
    let ua = crate::utf8::utf8_block_neon(s, st, b, uj, ok, pa, na == 0);
    let ub = crate::utf8::utf8_block_neon(s, st, b + 64, b + 64, ua.0, ua.1, nb == 0);
    let xa = ea & !na;
    let xb = eb & !nb;
    proof {
        lemma_low_bad(g, gst, b as int, ea, ra, na, xa);
        lemma_low_bad(g, gst, b + 64, eb, rb, nb, xb);
        assert forall|k: u64| k < 64 implies #[trigger] bit64(xb, k) == bad(g, gst, b + 64 + k) by {
            assert(bit64(xb, k) == bad(g, gst, (b + 64) + k));
        }
    }
    (xa, xb, ub.0, ub.1)
}

/// No high byte in the mask, none in the block.
proof fn lemma_high_zero(g: Seq<u8>, b: int, na: u64)
    requires
        forall|k: u64| k < 64 ==> #[trigger] bit64(na, k) == (g[b + k] >= 0x80),
    ensures
        na == 0 ==> crate::utf8::ascii_span(g, b, b + 64),
{
    if na == 0 {
        assert forall|t: int| b <= t < b + 64 implies #[trigger] g[t] < 0x80 by {
            let k = (t - b) as u64;
            lemma_bit_consts(k);
            assert(bit64(na, k) == (g[b + k] >= 0x80));
        }
    }
}

/// The low bytes inside strings, less the high ones, are the errors.
proof fn lemma_low_bad(g: Seq<u8>, gst: int, b: int, ea: u64, ra: u64, na: u64, xa: u64)
    requires
        0 <= b,
        b + 64 <= g.len(),
        low_masks(g, gst, b, ea, ra),
        forall|k: u64| k < 64 ==> #[trigger] bit64(na, k) == (g[b + k] >= 0x80),
        xa == ea & !na,
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(xa, k) == bad(g, gst, b + k),
{
    assert forall|k: u64| k < 64 implies #[trigger] bit64(xa, k) == bad(g, gst, b + k) by {
        assert(bit64(ea, k) == (crate::neon::lowb(g[b + k]) && inside(g, gst, b + k)));
        assert(bit64(na, k) == (g[b + k] >= 0x80));
        lemma_bit_ops(ea, !na, k);
        lemma_bit_ops(na, na, k);
        assert(byte(g, b + k) == g[b + k]);
    }
}

/// Processes the block at `base`, whose classes are `m`.
#[inline(always)]
fn stage1_block<const K: u8>(
    m: Masks,
    base: usize,
    w0: usize,
    idx: &mut Vec<u32>,
    t: Stage1,
    Ghost(g): Ghost<Seq<u8>>,
    Ghost(gst): Ghost<int>,
    Ghost(lim): Ghost<int>,
) -> (r: Stage1)
    requires
        kernel_cpu(K),
        stage1_inv(g, gst, w0 as int, lim, base as int, old(idx)@, t),
        base < lim,
        block_classes(m, g, base as int),
    ensures
        final(idx)@.len() == old(idx)@.len(),
        stage1_inv(g, gst, w0 as int, lim, base + 64, final(idx)@, r),
{
    let _n = idx.len();
    let (e, c2) = escapes(m.backslash, t.carry_esc, Ghost(g), Ghost(gst), Ghost(base as int));
    let p = prefix_xor_clmul::<K>(m.quote & !e);
    let w = t.w;
    let pend = t.pend;
    let pbase = t.pbase;
    let (st_m, t2) = block_logic(m, e, c2, p, base, t, Ghost(g), Ghost(gst));
    // Write the previous block's positions rather than this one's, so
    // the writes' branches wait on nothing computed in this block.
    let ghost ib = idx@;
    let w2 = append_bits::<K>(idx, w, pend, pbase);
    proof {
        lemma_positions_block(g, gst, w0 as int, base as int, st_m, 64);
        lemma_bits_len(st_m, base - w0, 64);
        assert(idx@.subrange(0, w2 as int) =~= idx@.subrange(0, w as int) + idx@.subrange(
            w as int,
            w2 as int,
        ));
        assert(idx@.subrange(0, w as int) == ib.subrange(0, w as int));
    }
    Stage1 { w: w2, carry_esc: t2.carry_esc, in_str: t2.in_str, prev: t2.prev, err: t2.err, pend: st_m, pbase: (base - w0) as u32 }
}

/// The classes of the last, partial block at `base`, padded with spaces.
#[inline(always)]
fn tail_classes<const K: u8>(s: &[u8], base: usize) -> (m: Masks)
    requires
        kernel_cpu(K),
        base < s@.len() < base + 64,
        K == NEON ==> verilith_simd::neon::neon(),
    ensures
        block_classes(m, s@, base as int),
{
    let mut tail = [0x20u8; 64];
    let mut j = base;
    while j < s.len()
        invariant
            base <= j <= s@.len(),
            s@.len() < base + 64,
            tail@.len() == 64,
            forall|k: int| 0 <= k < 64 ==> #[trigger] tail@[k] == byte(
                s@,
                if k < j - base { base + k } else { s@.len() as int },
            ),
        decreases s@.len() - j,
    {
        tail[j - base] = s[j];
        j = j + 1;
    }
    proof {
        assert forall|k: int| 0 <= k < 64 implies #[trigger] tail@[k] == byte(s@, base + k) by {
            if k >= j - base {
                assert(byte(s@, s@.len() as int) == 0x20);
            }
        }
    }
    let m = classify64::<K>(tail.as_slice(), 0);
    proof {
        assert forall|k: u64| k < 64 implies {
            let c = #[trigger] byte(s@, base + k);
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
            &&& bit64(m.ctrl, k) == (c < 0x20)
        } by {
            assert(tail@[0 + k] == byte(s@, base + k));
        }
    }
    m
}

/// The classes of the full block at `base`.
#[inline(always)]
fn full_classes<const K: u8>(s: &[u8], base: usize) -> (m: Masks)
    requires
        kernel_cpu(K),
        base + 64 <= s@.len(),
        K == NEON ==> verilith_simd::neon::neon(),
    ensures
        block_classes(m, s@, base as int),
{
    let m = classify64::<K>(s, base);
    proof {
        assert forall|k: u64| k < 64 implies {
            let c = #[trigger] byte(s@, base + k);
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
            &&& bit64(m.ctrl, k) == (c < 0x20)
        } by {
            assert(s@[base + k] == byte(s@, base + k));
        }
    }
    m
}

/// Stage 1's main loop with NEON, over the window that starts at `w0`,
/// for as long as 128 bytes of it are left before `lim`. Returns the
/// state, where it stopped, and the UTF-8 check's state.
#[inline(always)]
fn stage1_neon(
    s: &[u8],
    st: usize,
    idx: &mut Vec<u32>,
    w0: usize,
    lim: usize,
    t0: Stage1,
    uj0: usize,
    uok0: bool,
    pa0: bool,
) -> (r: (Stage1, usize, usize, bool, bool))
    requires
        kernel_cpu(NEON),
        verilith_simd::neon::neon(),
        stage1_inv(s@, st as int, w0 as int, lim as int, w0 as int, old(idx)@, t0),
        t0.w == 0 && t0.pend == 0 && t0.pbase == 0,
        crate::utf8::u8_state(s@, st as int, uj0 as int, uok0),
        s@.len() - st >= 3 ==> (uj0 == st + 3 && w0 == st) || (uj0 == w0 && st + 3 <= w0),
        pa0 && s@.len() - st >= 3 ==> crate::utf8::ascii_span(s@, uj0 - 3, w0 as int),
    ensures
        final(idx)@.len() == old(idx)@.len(),
        w0 <= r.1 <= lim,
        lim - r.1 < 128,
        (lim - w0) % 128 == 0 ==> r.1 == lim,
        stage1_inv(s@, st as int, w0 as int, lim as int, r.1 as int, final(idx)@, r.0),
        crate::utf8::u8_state(s@, st as int, r.2 as int, r.3),
        s@.len() - st >= 3 ==> (r.2 == st + 3 && r.1 == st) || (r.2 == r.1 && st + 3 <= r.1),
        r.4 && s@.len() - st >= 3 ==> crate::utf8::ascii_span(s@, r.2 - 3, r.1 as int),
{
    let ghost g = s@;
    let ghost gst = st as int;
    let ghost len0 = idx@.len();
    let n = s.len();
    let mut t = t0;
    let mut base = w0;
    let mut uj = uj0;
    let mut uok = uok0;
    // Two blocks at a time. Each is loaded once, for its classes and
    // for the ASCII test of the UTF-8 check alike, and the positions
    // of both are written one whole turn later, so that the writes'
    // branches wait on nothing computed in this turn.
    let mut w: usize = 0;
    let mut qa: u64 = 0;
    let mut qb: u64 = 0;
    let mut qbase: usize = w0;
    let mut pa = pa0;
    let mut err: u64 = t0.err;
    proof {
        crate::simd::lemma_zero_upto(0, 64);
        crate::simd::lemma_zero_upto(64, 64);
        assert(idx@.subrange(0, 0) + bits_upto(0, 0, 64) + bits_upto(0, 64, 64) =~= rpos(
            g,
            gst,
            w0 as int,
            w0 as int,
        ));
    }
    while lim - base >= 128
        invariant
            kernel_cpu(NEON),
            verilith_simd::neon::neon(),
            g == s@,
            n == s@.len(),
            gst == st as int,
            st <= w0 <= base <= lim <= n,
            lim - w0 + 128 <= u32::MAX,
            (lim - w0) % 128 == 0 ==> (lim - base) % 128 == 0,
            idx@.len() == len0,
            len0 >= lim - w0 + 64,
            core_inv(g, gst, base as int, t),
            (err == 0) == clean(g, gst, base as int),
            w0 <= qbase,
            qbase + 128 <= base || (qa == 0 && qb == 0 && qbase == base),
            w <= qbase - w0,
            idx@.subrange(0, w as int) + bits_upto(qa, qbase - w0, 64) + bits_upto(qb, qbase - w0 + 64, 64)
                == rpos(g, gst, w0 as int, base as int),
            crate::utf8::u8_state(g, gst, uj as int, uok),
            n - st >= 3 ==> (uj == st + 3 && base == st) || (uj == base && st + 3 <= base),
            pa && n - st >= 3 ==> crate::utf8::ascii_span(g, uj - 3, base as int),
        decreases lim - base,
    {
        let va = crate::neon::load64(s, base);
        let (sa, t1, ea, ra) = block_neon(va.0, va.1, va.2, va.3, base, t, Ghost(g), Ghost(gst));
        let vb = crate::neon::load64(s, base + 64);
        let (sb, t2, eb, rb) = block_neon(vb.0, vb.1, vb.2, vb.3, base + 64, t1, Ghost(g), Ghost(gst));
        let ghost i0 = idx@;
        let ghost la = bits_upto(qa, qbase - w0, 64);
        let ghost lb = bits_upto(qb, qbase - w0 + 64, 64);
        proof {
            lemma_bits_len(qa, qbase - w0, 64);
            lemma_bits_len(qb, qbase - w0 + 64, 64);
            crate::simd::lemma_zero_upto(qbase - w0, 64);
            crate::simd::lemma_zero_upto(qbase - w0 + 64, 64);
        }
        let w1 = append_bits::<NEON>(idx, w, qa, (qbase - w0) as u32);
        let ghost i1 = idx@;
        let w2 = append_bits::<NEON>(idx, w1, qb, (qbase - w0 + 64) as u32);
        proof {
            assert(i1.subrange(0, w1 as int) =~= i0.subrange(0, w as int) + la) by {
                assert(i1.subrange(0, w1 as int) =~= i1.subrange(0, w as int) + i1.subrange(w as int, w1 as int));
            }
            assert(idx@.subrange(0, w2 as int) =~= i0.subrange(0, w as int) + la + lb) by {
                assert(idx@.subrange(0, w2 as int) =~= idx@.subrange(0, w1 as int) + idx@.subrange(
                    w1 as int,
                    w2 as int,
                ));
            }
        }
        // The blocks are ASCII, as the bytes before them, far more often
        // than not: one test for both, and the rest is out of line.
        let (xa, xb, uok2, pa2) = if (ra | rb) == 0 && pa {
            proof {
                lemma_or_zero(ra, rb);
                lemma_low_ascii(g, gst, base as int, ea, ra);
                lemma_low_ascii(g, gst, base + 64, eb, rb);
                assert forall|k: u64| k < 64 implies #[trigger] bit64(eb, k) == bad(g, gst, base + 64 + k) by {
                    assert(bit64(eb, k) == bad(g, gst, (base + 64) + k));
                }
            }
            let ua = crate::utf8::utf8_block_neon(s, st, base, uj, uok, pa, true);
            let ub = crate::utf8::utf8_block_neon(s, st, base + 64, base + 64, ua.0, ua.1, true);
            (ea, eb, ub.0, ub.1)
        } else {
            rare_pair(s, st, base, uj, uok, pa, ea, eb, Ghost(ra), Ghost(rb))
        };
        proof {
            lemma_bad_pair(g, gst, base as int, xa, xb);
            lemma_err_range(g, gst, base as int, base + 128, err, xa | xb);
            lemma_struct_mask(g, gst, base as int, sa, xa);
            assert forall|k: u64| k < 64 implies #[trigger] bit64(xb, k) == bad(g, gst, (base + 64) + k) by {
                assert(bit64(xb, k) == bad(g, gst, base + 64 + k));
            }
            lemma_struct_mask(g, gst, base + 64, sb, xb);
            lemma_positions_block(g, gst, w0 as int, base as int, sa | xa, 64);
            lemma_positions_block(g, gst, w0 as int, base + 64, sb | xb, 64);
        }
        err = err | (xa | xb);
        w = w2;
        qa = sa | xa;
        qb = sb | xb;
        qbase = base;
        t = t2;
        uj = base + 128;
        uok = uok2;
        pa = pa2;
        base = base + 128;
        proof {
            lemma_bits_len(qa, qbase - w0, 64);
            lemma_bits_len(qb, qbase - w0 + 64, 64);
        }
    }
    // The first of the two pending blocks; the second goes on as the
    // one-block loop's pending block.
    let ghost i0 = idx@;
    proof {
        lemma_bits_len(qa, qbase - w0, 64);
        lemma_bits_len(qb, qbase - w0 + 64, 64);
        crate::simd::lemma_zero_upto(qbase - w0, 64);
        crate::simd::lemma_zero_upto(qbase - w0 + 64, 64);
    }
    let w1 = append_bits::<NEON>(idx, w, qa, (qbase - w0) as u32);
    let pb = if qbase < base { qbase + 64 - w0 } else { qbase - w0 };
    proof {
        assert(idx@.subrange(0, w1 as int) =~= i0.subrange(0, w as int) + bits_upto(qa, qbase - w0, 64)) by {
            assert(idx@.subrange(0, w1 as int) =~= idx@.subrange(0, w as int) + idx@.subrange(w as int, w1 as int));
        }
        if qbase == base {
            crate::simd::lemma_zero_upto(pb as int, 64);
        }
    }
    t = Stage1 { w: w1, carry_esc: t.carry_esc, in_str: t.in_str, prev: t.prev, err, pend: qb, pbase: pb as u32 };
    (t, base, uj, uok, pa)
}

/// The state of stage 1 at the start of a window at `w0`: nothing
/// written or pending yet.
pub open spec fn fresh(g: Seq<u8>, gst: int, w0: int, t: Stage1) -> bool {
    &&& logic_inv(g, gst, w0, t)
    &&& t.w == 0
    &&& t.pend == 0
    &&& t.pbase == 0
}

/// Where the UTF-8 check stands when kernel `K` starts a window at `w0`.
pub open spec fn u8_at(K: u8, g: Seq<u8>, gst: int, w0: int, uj: int, ok: bool, pa: bool) -> bool {
    &&& crate::utf8::u8_state(g, gst, uj, ok)
    &&& (K == AVX2 || K == AVX512) && g.len() - gst >= 3 ==> uj == w0 + 3
    &&& K == NEON && g.len() - gst >= 3 ==> (uj == gst + 3 && w0 == gst) || (uj == w0 && gst + 3 <= w0)
    &&& K == NEON && pa && g.len() - gst >= 3 ==> crate::utf8::ascii_span(g, uj - 3, w0)
}

/// What filling the window `[w0, lim)` returns.
pub open spec fn filled(K: u8, g: Seq<u8>, gst: int, w0: int, lim: int, idx: Seq<u32>, r: (usize, Stage1, usize, bool, bool)) -> bool {
    &&& r.0 <= idx.len()
    &&& idx.subrange(0, r.0 as int) == rpos(g, gst, w0, lim)
    &&& r.0 <= lim - w0
    &&& crate::utf8::u8_state(g, gst, r.2 as int, r.3)
    &&& lim < g.len() ==> fresh(g, gst, lim, r.1) && u8_at(K, g, gst, lim, r.2 as int, r.3, r.4)
    &&& lim == g.len() ==> {
        &&& (r.1.err == 0) == clean(g, gst, lim)
        &&& (r.1.in_str == 0 || r.1.in_str == 0xFFFF_FFFF_FFFF_FFFFu64)
        &&& (r.1.in_str != 0) == instr(g, gst, lim - 1)
    }
}

/// Lists the structural positions of `s[w0..lim]` as offsets from `w0`
/// at the start of `idx`, carrying stage 1's state `t` and the UTF-8
/// check's on to `lim`. Returns how many there are, the state at `lim`
/// and the UTF-8 check's. A window that ends before the input does is a
/// whole number of 128-byte steps and leaves 3 bytes after it, so that
/// each kernel's loops end exactly at `lim`.
#[inline(always)]
pub fn fill_k<const K: u8>(
    s: &[u8],
    st: usize,
    idx: &mut Vec<u32>,
    w0: usize,
    lim: usize,
    t0: Stage1,
    uj0: usize,
    uok0: bool,
    pa0: bool,
) -> (r: (usize, Stage1, usize, bool, bool))
    requires
        kernel_cpu(K),
        K == NEON ==> verilith_simd::neon::neon(),
        st <= w0 <= lim <= s@.len(),
        lim - w0 + 128 <= u32::MAX,
        lim < s@.len() ==> (lim - w0) % 128 == 0 && s@.len() - lim >= 3 && lim - w0 >= 128,
        fresh(s@, st as int, w0 as int, t0),
        u8_at(K, s@, st as int, w0 as int, uj0 as int, uok0, pa0),
    ensures
        filled(K, s@, st as int, w0 as int, lim as int, final(idx)@, r),
{
    proof {
        lemma_kernel_utf8(K);
    }
    // Room for every position plus the scratch writes of the last block.
    let need = lim - w0 + 64;
    if idx.len() < need {
        *idx = vec![0u32; need];
    }
    let ghost g = s@;
    let ghost gst = st as int;
    let ghost len0 = idx@.len();
    let ghost glim = lim as int;
    let mut t = t0;
    let mut base = w0;
    let mut uj = uj0;
    let mut uok = uok0;
    let mut pa = pa0;
    proof {
        crate::simd::lemma_zero_upto(0, 64);
        assert(idx@.subrange(0, 0) + bits_upto(0, 0, 64) =~= rpos(g, gst, w0 as int, w0 as int));
    }
    let n = s.len();
    if K == NEON {
        let r = stage1_neon(s, st, idx, w0, lim, t, uj, uok, pa);
        t = r.0;
        base = r.1;
        uj = r.2;
        uok = r.3;
        pa = r.4;
    }
    // Two blocks at a time, classifying both before either is indexed.
    while (K == AVX2 || K == AVX512) && lim - base >= 128 && n - base >= 131
        invariant
            kernel_cpu(K),
            utf8_cpu(K),
            K == NEON ==> verilith_simd::neon::neon(),
            g == s@,
            n == s@.len(),
            gst == st as int,
            glim == lim as int,
            w0 <= base <= lim,
            idx@.len() == len0,
            lim < n ==> (lim - base) % 128 == 0 && n - lim >= 3,
            stage1_inv(g, gst, w0 as int, glim, base as int, idx@, t),
            crate::utf8::u8_state(g, gst, uj as int, uok),
            (K == AVX2 || K == AVX512) && n - st >= 3 ==> uj == base + 3,
            K == NEON && lim < n ==> base == lim,
            K == NEON ==> u8_at(K, g, gst, base as int, uj as int, uok, pa),
        decreases lim - base,
    {
        let m1 = full_classes::<K>(s, base);
        let m2 = full_classes::<K>(s, base + 64);
        t = stage1_block::<K>(m1, base, w0, idx, t, Ghost(g), Ghost(gst), Ghost(glim));
        t = stage1_block::<K>(m2, base + 64, w0, idx, t, Ghost(g), Ghost(gst), Ghost(glim));
        // `uj` is `base + 3`; written so, the loads of the UTF-8 check
        // are seen to be those of the classification above.
        let u = crate::utf8::utf8_step::<K>(s, st, base + 3, uok);
        uj = u.0;
        uok = u.1;
        base = base + 128;
    }
    proof {
        if lim < n && (K == AVX2 || K == AVX512 || K == NEON) {
            if K != NEON {
                assert(lim - base < 128);
                assert((lim - base) % 128 == 0);
            }
            assert(base == lim);
        }
    }
    let ghost base1 = base;
    while lim - base >= 64
        invariant
            kernel_cpu(K),
            utf8_cpu(K),
            K == NEON ==> verilith_simd::neon::neon(),
            g == s@,
            n == s@.len(),
            gst == st as int,
            glim == lim as int,
            w0 <= base <= lim,
            idx@.len() == len0,
            lim < n ==> (lim - base) % 64 == 0,
            lim < n && (K == AVX2 || K == AVX512 || K == NEON) ==> base == base1 && base1 == lim,
            lim < n && (K == AVX2 || K == AVX512 || K == NEON) ==> u8_at(K, g, gst, glim, uj as int, uok, pa),
            crate::utf8::u8_state(g, gst, uj as int, uok),
            stage1_inv(g, gst, w0 as int, glim, base as int, idx@, t),
        decreases lim - base,
    {
        let m = full_classes::<K>(s, base);
        t = stage1_block::<K>(m, base, w0, idx, t, Ghost(g), Ghost(gst), Ghost(glim));
        base = base + 64;
    }
    let ghost mut end = base as int;
    if base < lim {
        proof {
            assert(lim == n);
        }
        let m = tail_classes::<K>(s, base);
        t = stage1_block::<K>(m, base, w0, idx, t, Ghost(g), Ghost(gst), Ghost(glim));
        proof {
            end = base + 64;
        }
    }
    proof {
        if lim == n {
            lemma_positions_past_end(g, gst, w0 as int, end);
            if end > s.len() {
                lemma_past_end(g, gst, end - 1);
            }
        } else {
            assert(end == lim);
        }
    }
    let ghost ib = idx@;
    let w = append_bits::<K>(idx, t.w, t.pend, t.pbase);
    proof {
        assert(idx@.subrange(0, w as int) =~= idx@.subrange(0, t.w as int) + idx@.subrange(
            t.w as int,
            w as int,
        ));
        assert(idx@.subrange(0, t.w as int) == ib.subrange(0, t.w as int));
        lemma_bits_len(t.pend, t.pbase as int, 64);
        crate::simd::lemma_zero_upto(0, 64);
    }
    let r = (w, Stage1 { w: 0, carry_esc: t.carry_esc, in_str: t.in_str, prev: t.prev, err: t.err, pend: 0, pbase: 0 }, uj, uok, pa);
    proof {
        assert(r.0 <= idx@.len());
        assert(idx@.subrange(0, r.0 as int) == rpos(g, gst, w0 as int, glim));
        lemma_rpos(g, gst, w0 as int, glim);
        lemma_positions_len(g, gst, w0 as int, glim);
        assert(idx@.subrange(0, r.0 as int).len() == r.0);
        assert(r.0 <= lim - w0);
        assert(crate::utf8::u8_state(g, gst, r.2 as int, r.3));
        if lim < n {
            assert(fresh(g, gst, glim, r.1));
            assert(u8_at(K, g, gst, glim, r.2 as int, r.3, r.4));
        }
    }
    r
}

/// Lists the structural positions of `s[st..]`, as offsets from `st`, at
/// the start of `idx` and returns how many there are: the whole input as
/// one window. Also returns whether the input passes stage 1's checks (no
/// control character inside a string, and every string closed) and
/// whether it is UTF-8.
#[inline(always)]
pub fn structural_index<const K: u8>(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (r: (usize, bool, bool))
    requires
        kernel_cpu(K),
        st <= s@.len(),
        s@.len() - st + 128 <= u32::MAX,
        K == NEON ==> verilith_simd::neon::neon(),
    ensures
        r.0 <= final(idx)@.len(),
        final(idx)@.subrange(0, r.0 as int) == rpos(s@, st as int, st as int, s@.len() as int),
        r.1 == (clean(s@, st as int, s@.len() as int) && !instr(s@, st as int, s@.len() - 1)),
        r.2 == utf8_from(s@, st as int),
{
    proof {
        lemma_kernel_utf8(K);
    }
    let (uj, uok) = crate::utf8::utf8_start(s, st);
    let t = Stage1 { w: 0, carry_esc: 0, in_str: 0, prev: 0, err: 0, pend: 0, pbase: 0 };
    proof {
        assert(clean(s@, st as int, st as int));
    }
    let r = fill_k::<K>(s, st, idx, st, s.len(), t, uj, uok, true);
    (r.0, r.1.err == 0 && r.1.in_str == 0, crate::utf8::utf8_finish::<K>(s, st, r.2, r.3))
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Kernels
// ---------------------------------------------------------------------------

/// What filling a window and, for the last one, finishing the UTF-8 check
/// returns.
pub open spec fn filled_fin(K: u8, g: Seq<u8>, gst: int, w0: int, lim: int, idx: Seq<u32>, r: (usize, Stage1, usize, bool, bool, bool)) -> bool {
    &&& filled(K, g, gst, w0, lim, idx, (r.0, r.1, r.2, r.3, r.4))
    &&& lim == g.len() ==> r.5 == utf8_from(g, gst)
}

pub open spec fn fill_pre(K: u8, g: Seq<u8>, st: int, w0: int, lim: int, t0: Stage1, uj0: int, uok0: bool, pa0: bool) -> bool {
    &&& st <= w0 <= lim <= g.len()
    &&& lim - w0 + 128 <= u32::MAX
    &&& lim < g.len() ==> (lim - w0) % 128 == 0 && g.len() - lim >= 3 && lim - w0 >= 128
    &&& fresh(g, st, w0, t0)
    &&& u8_at(K, g, st, w0, uj0, uok0, pa0)
}

/// `fill_k`, then the end of the UTF-8 check if this is the last window.
#[inline(always)]
fn fill_fin<const K: u8>(
    s: &[u8],
    st: usize,
    idx: &mut Vec<u32>,
    w0: usize,
    lim: usize,
    t0: Stage1,
    uj0: usize,
    uok0: bool,
    pa0: bool,
) -> (r: (usize, Stage1, usize, bool, bool, bool))
    requires
        kernel_cpu(K),
        K == NEON ==> verilith_simd::neon::neon(),
        fill_pre(K, s@, st as int, w0 as int, lim as int, t0, uj0 as int, uok0, pa0),
    ensures
        filled_fin(K, s@, st as int, w0 as int, lim as int, final(idx)@, r),
{
    proof {
        lemma_kernel_utf8(K);
    }
    let r = fill_k::<K>(s, st, idx, w0, lim, t0, uj0, uok0, pa0);
    let u = if lim == s.len() { crate::utf8::utf8_finish::<K>(s, st, r.2, r.3) } else { false };
    (r.0, r.1, r.2, r.3, r.4, u)
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn fill_avx512_body(
    s: &[u8],
    st: usize,
    idx: &mut Vec<u32>,
    w0: usize,
    lim: usize,
    t0: Stage1,
    uj0: usize,
    uok0: bool,
    pa0: bool,
) -> (r: (usize, Stage1, usize, bool, bool, bool))
    requires
        kernel_cpu(AVX512),
        fill_pre(AVX512, s@, st as int, w0 as int, lim as int, t0, uj0 as int, uok0, pa0),
    ensures
        filled_fin(AVX512, s@, st as int, w0 as int, lim as int, final(idx)@, r),
{
    fill_fin::<AVX512>(s, st, idx, w0, lim, t0, uj0, uok0, pa0)
}

/// Trusted: `fill_avx512_body` compiled with `avx512f,avx512bw,avx512vbmi2,pclmulqdq,popcnt,bmi1,bmi2` enabled, through
/// `tf::fill_avx512`; the contract is `fill_avx512_body`'s, which is verified.
/// The caller checks the CPU first.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn fill_avx512(
    s: &[u8],
    st: usize,
    idx: &mut Vec<u32>,
    w0: usize,
    lim: usize,
    t0: Stage1,
    uj0: usize,
    uok0: bool,
    pa0: bool,
) -> (r: (usize, Stage1, usize, bool, bool, bool))
    requires
        kernel_cpu(AVX512) && popcnt() && bmi2(),
        fill_pre(AVX512, s@, st as int, w0 as int, lim as int, t0, uj0 as int, uok0, pa0),
    ensures
        filled_fin(AVX512, s@, st as int, w0 as int, lim as int, final(idx)@, r),
{
    // SAFETY: only called after the matching CPU check returned true.
    unsafe { tf::fill_avx512(s, st, idx, w0, lim, t0, uj0, uok0, pa0) }
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn fill_avx2_body(
    s: &[u8],
    st: usize,
    idx: &mut Vec<u32>,
    w0: usize,
    lim: usize,
    t0: Stage1,
    uj0: usize,
    uok0: bool,
    pa0: bool,
) -> (r: (usize, Stage1, usize, bool, bool, bool))
    requires
        kernel_cpu(AVX2),
        fill_pre(AVX2, s@, st as int, w0 as int, lim as int, t0, uj0 as int, uok0, pa0),
    ensures
        filled_fin(AVX2, s@, st as int, w0 as int, lim as int, final(idx)@, r),
{
    fill_fin::<AVX2>(s, st, idx, w0, lim, t0, uj0, uok0, pa0)
}

/// Trusted: `fill_avx2_body` compiled with `avx2,pclmulqdq,popcnt,bmi1,bmi2` enabled, through
/// `tf::fill_avx2`; the contract is `fill_avx2_body`'s, which is verified.
/// The caller checks the CPU first.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn fill_avx2(
    s: &[u8],
    st: usize,
    idx: &mut Vec<u32>,
    w0: usize,
    lim: usize,
    t0: Stage1,
    uj0: usize,
    uok0: bool,
    pa0: bool,
) -> (r: (usize, Stage1, usize, bool, bool, bool))
    requires
        kernel_cpu(AVX2) && popcnt() && bmi2(),
        fill_pre(AVX2, s@, st as int, w0 as int, lim as int, t0, uj0 as int, uok0, pa0),
    ensures
        filled_fin(AVX2, s@, st as int, w0 as int, lim as int, final(idx)@, r),
{
    // SAFETY: only called after the matching CPU check returned true.
    unsafe { tf::fill_avx2(s, st, idx, w0, lim, t0, uj0, uok0, pa0) }
}

/// Whether this CPU has what the AVX-512 kernel and its trampoline need.
#[cfg(target_arch = "x86_64")]
#[inline]
fn cpu_has_avx512() -> (r: bool)
    ensures
        r ==> kernel_cpu(AVX512) && verilith_simd::cpu::popcnt() && verilith_simd::cpu::bmi2(),
{
    verilith_simd::cpu::has_avx512vbmi2() && verilith_simd::cpu::has_pclmul() && verilith_simd::cpu::has_popcnt() && verilith_simd::cpu::has_bmi2()
}

/// Whether this CPU has what the AVX2 kernel and its trampoline need.
#[cfg(target_arch = "x86_64")]
#[inline]
fn cpu_has_avx2() -> (r: bool)
    ensures
        r ==> kernel_cpu(AVX2) && verilith_simd::cpu::popcnt() && verilith_simd::cpu::bmi2(),
{
    verilith_simd::cpu::has_avx2() && verilith_simd::cpu::has_pclmul() && verilith_simd::cpu::has_popcnt() && verilith_simd::cpu::has_bmi2()
}

/// Whether kernel `k` is built for this target: the x86 kernels only on
/// x86-64.
#[cfg(target_arch = "x86_64")]
pub open spec fn arch_ok(k: u8) -> bool {
    true
}

#[cfg(not(target_arch = "x86_64"))]
pub open spec fn arch_ok(k: u8) -> bool {
    k != AVX2 && k != AVX512
}

/// What the CPU must have to run kernel `k` here.
pub open spec fn kind_ok(k: u8) -> bool {
    &&& k == SCALAR || k == NEON || k == AVX2 || k == AVX512
    &&& arch_ok(k)
    &&& kernel_cpu(k)
    &&& k == NEON ==> verilith_simd::neon::neon()
    &&& (k == AVX2 || k == AVX512) ==> popcnt() && bmi2()
}

/// The best kernel this CPU supports.
pub fn best_kind() -> (k: u8)
    ensures
        kind_ok(k),
{
    #[cfg(target_arch = "x86_64")]
    {
        if cpu_has_avx512() {
            return AVX512;
        }
        if cpu_has_avx2() {
            return AVX2;
        }
    }
    if verilith_simd::neon::has_neon() {
        return NEON;
    }
    SCALAR
}

/// `fill_fin` with the kernel `k`.
fn fill_kind(
    k: u8,
    s: &[u8],
    st: usize,
    idx: &mut Vec<u32>,
    w0: usize,
    lim: usize,
    t0: Stage1,
    uj0: usize,
    uok0: bool,
    pa0: bool,
) -> (r: (usize, Stage1, usize, bool, bool, bool))
    requires
        kind_ok(k),
        fill_pre(k, s@, st as int, w0 as int, lim as int, t0, uj0 as int, uok0, pa0),
    ensures
        filled_fin(k, s@, st as int, w0 as int, lim as int, final(idx)@, r),
{
    #[cfg(target_arch = "x86_64")]
    {
        if k == AVX512 {
            return fill_avx512(s, st, idx, w0, lim, t0, uj0, uok0, pa0);
        }
        if k == AVX2 {
            return fill_avx2(s, st, idx, w0, lim, t0, uj0, uok0, pa0);
        }
    }
    if k == NEON {
        return fill_fin::<NEON>(s, st, idx, w0, lim, t0, uj0, uok0, pa0);
    }
    fill_fin::<SCALAR>(s, st, idx, w0, lim, t0, uj0, uok0, pa0)
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// The windowed index
// ---------------------------------------------------------------------------

/// Number of structural positions in `[st, i)`. A reader of the index
/// keeps the number of the next unread entry equal to `cnt` of its spec
/// position.
pub open spec fn cnt(s: Seq<u8>, st: int, i: int) -> int {
    positions(s, st, st, i).len() as int
}

/// At most one structural position per byte.
pub proof fn lemma_positions_len(s: Seq<u8>, st: int, a: int, b: int)
    requires
        a <= b,
    ensures
        positions(s, st, a, b).len() <= b - a,
        forall|i: int| 0 <= i < positions(s, st, a, b).len() ==> a <= #[trigger] positions(s, st, a, b)[i] < b,
    decreases b - a,
{
    if b > a {
        lemma_positions_len(s, st, a, b - 1);
    }
}

/// The default window: 64 KiB of input, whose index entries take 256 KiB.
pub const WINDOW: usize = 65536;

/// The structural index of `s[st..]`, built one window at a time: `buf`
/// holds the positions of `[w0, wend)` as offsets from `w0`, which are
/// entries `kbase..kend` of the whole index. Reading past `kend` indexes
/// the next window, so the memory taken is fixed however long the input.
///
/// Stage 1 needs no checks of its own: the index lists the control
/// characters inside strings, for stage 2 to reject, and stage 2 finds an
/// unclosed string where the index runs out. UTF-8 is checked alongside,
/// window by window.
pub struct Win<'a> {
    pub s: &'a [u8],
    pub st: usize,
    pub buf: Vec<u32>,
    pub w0: usize,
    pub wend: usize,
    pub kbase: usize,
    pub kend: usize,
    /// Stage 1's state at `wend`.
    pub t: Stage1,
    /// The UTF-8 check's state.
    pub uj: usize,
    pub uok: bool,
    pub pa: bool,
    /// Whether the input is valid UTF-8, once `done`.
    pub utf8: bool,
    pub kind: u8,
    /// Bytes in a window, but for the last, which may take up to 256 more.
    pub win: usize,
    /// The last window has been indexed.
    pub done: bool,
}

impl<'a> Win<'a> {
    pub open spec fn g(&self) -> Seq<u8> {
        self.s@
    }

    /// The whole index.
    pub open spec fn all(&self) -> Seq<int> {
        positions(self.s@, self.st as int, self.st as int, self.s@.len() as int)
    }

    pub open spec fn inv(&self) -> bool {
        let g = self.s@;
        let st = self.st as int;
        &&& st <= self.w0 <= self.wend <= g.len()
        &&& kind_ok(self.kind)
        &&& 128 <= self.win <= 0x4000_0000
        &&& self.win % 128 == 0
        &&& self.wend - self.w0 + 128 <= u32::MAX
        &&& self.kbase <= self.kend
        &&& self.kend - self.kbase <= self.buf@.len()
        &&& self.buf@.subrange(0, self.kend - self.kbase) == rpos(g, st, self.w0 as int, self.wend as int)
        &&& self.kbase == cnt(g, st, self.w0 as int)
        &&& self.kend <= self.wend - st
        &&& self.kend == cnt(g, st, self.wend as int)
        &&& !self.done ==> fresh(g, st, self.wend as int, self.t) && u8_at(
            self.kind,
            g,
            st,
            self.wend as int,
            self.uj as int,
            self.uok,
            self.pa,
        )
        &&& self.done ==> {
            &&& self.wend == g.len()
            &&& self.utf8 == utf8_from(g, st)
        }
    }

    /// What every operation keeps: the input, where its index starts, and
    /// the window size.
    pub open spec fn same(&self, o: &Self) -> bool {
        &&& self.s == o.s
        &&& self.st == o.st
        &&& self.win == o.win
    }
}

/// The entries of the window are the whole index's entries `kbase..kend`.
pub proof fn lemma_win_entry(w: &Win, k: int)
    requires
        w.inv(),
        w.kbase <= k < w.kend,
    ensures
        k < w.all().len(),
        w.all()[k] == w.w0 + w.buf@[k - w.kbase] as int,
        w.all()[k] < w.wend,
        w.all()[k] + 0 == positions(w.s@, w.st as int, w.st as int, w.wend as int)[k],
{
    let g = w.s@;
    let st = w.st as int;
    lemma_rpos(g, st, w.w0 as int, w.wend as int);
    lemma_positions_split(g, st, st, w.w0 as int, w.wend as int);
    lemma_positions_split(g, st, st, w.wend as int, g.len() as int);
    let r = rpos(g, st, w.w0 as int, w.wend as int);
    assert(w.buf@.subrange(0, w.kend - w.kbase)[k - w.kbase] == w.buf@[k - w.kbase]);
    assert(r[k - w.kbase] == w.buf@[k - w.kbase]);
}

impl<'a> Win<'a> {
    /// An empty window at the start of `s[st..]`, which the first read
    /// fills, for windows of `win` bytes.
    pub fn new(s: &'a [u8], st: usize, win: usize, buf: Vec<u32>) -> (r: Win<'a>)
        requires
            st <= s@.len(),
            128 <= win <= 0x4000_0000,
            win % 128 == 0,
        ensures
            r.inv(),
            r.s == s,
            r.st == st,
            r.kbase == 0,
            r.kend == 0,
    {
        Self::with_kind(s, st, win, buf, best_kind())
    }

    /// `new` with the kernel `kind`, which the CPU must support.
    pub fn with_kind(s: &'a [u8], st: usize, win: usize, buf: Vec<u32>, kind: u8) -> (r: Win<'a>)
        requires
            st <= s@.len(),
            128 <= win <= 0x4000_0000,
            win % 128 == 0,
            kind_ok(kind),
        ensures
            r.inv(),
            r.s == s,
            r.st == st,
            r.kbase == 0,
            r.kend == 0,
    {
        let (uj, uok) = crate::utf8::utf8_start(s, st);
        let t = Stage1 { w: 0, carry_esc: 0, in_str: 0, prev: 0, err: 0, pend: 0, pbase: 0 };
        proof {
            assert(rpos(s@, st as int, st as int, st as int) =~= Seq::<u32>::empty());
            assert(buf@.subrange(0, 0) =~= Seq::<u32>::empty());
            assert(positions(s@, st as int, st as int, st as int) =~= Seq::<int>::empty());
            assert(clean(s@, st as int, st as int));
            assert(crate::utf8::ascii_span(s@, st as int, st as int));
        }
        Win { s, st, buf, w0: st, wend: st, kbase: 0, kend: 0, t, uj, uok, pa: true, utf8: false, kind, win, done: false }
    }

    /// Gives back the buffer, to be used again.
    pub fn into_buf(self) -> (r: Vec<u32>) {
        self.buf
    }

    /// Indexes the next window.
    fn advance(&mut self)
        requires
            old(self).inv(),
            !old(self).done,
        ensures
            final(self).inv(),
            final(self).same(old(self)),
            old(self).wend <= final(self).wend,
            old(self).kend <= final(self).kend,
            final(self).kbase == old(self).kend,
            final(self).done || final(self).wend >= old(self).wend + 128,
    {
        let ghost o = *self;
        let ghost g = self.s@;
        let ghost st = self.st as int;
        let n = self.s.len();
        let w0 = self.wend;
        let lim = if n - w0 > self.win + 256 { w0 + self.win } else { n };
        let r = fill_kind(self.kind, self.s, self.st, &mut self.buf, w0, lim, self.t, self.uj, self.uok, self.pa);
        proof {
            lemma_rpos(g, st, o.w0 as int, w0 as int);
            lemma_positions_split(g, st, st, o.w0 as int, w0 as int);
            lemma_rpos(g, st, w0 as int, lim as int);
            lemma_positions_split(g, st, st, w0 as int, lim as int);
            lemma_positions_len(g, st, st, lim as int);
        }
        self.kbase = self.kend;
        self.kend = self.kend + r.0;
        self.w0 = w0;
        self.wend = lim;
        self.t = r.1;
        self.uj = r.2;
        self.uok = r.3;
        self.pa = r.4;
        if lim == n {
            self.done = true;
            self.utf8 = r.5;
        }
    }

    /// Entry `k` of the index, indexing further windows as needed (or
    /// again from the start, for an entry behind the window). `None` past
    /// the end of the index.
    #[inline(always)]
    pub fn at(&mut self, k: usize) -> (r: Option<usize>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).same(old(self)),
            final(self).kbase <= k,
            old(self).kbase <= k < old(self).kend ==> *final(self) == *old(self) && r is Some,
            r matches Some(q) ==> k < final(self).all().len() && q == final(self).all()[k as int]
                && q < final(self).wend && k < final(self).kend,
            r is None ==> final(self).done && k >= final(self).all().len(),
    {
        if self.kbase <= k && k < self.kend {
            proof {
                lemma_win_entry(self, k as int);
            }
            Some(self.w0 + get32(self.buf.as_slice(), k - self.kbase) as usize)
        } else {
            self.refill(k)
        }
    }

    /// Back to the start of the input, with nothing indexed.
    fn rewind(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).same(old(self)),
            final(self).kbase == 0,
            final(self).kend == 0,
    {
        let (uj, uok) = crate::utf8::utf8_start(self.s, self.st);
        proof {
            let g = self.s@;
            let st = self.st as int;
            assert(rpos(g, st, st, st) =~= Seq::<u32>::empty());
            assert(self.buf@.subrange(0, 0) =~= Seq::<u32>::empty());
            assert(positions(g, st, st, st) =~= Seq::<int>::empty());
            assert(clean(g, st, st));
            assert(crate::utf8::ascii_span(g, st, st));
        }
        self.t = Stage1 { w: 0, carry_esc: 0, in_str: 0, prev: 0, err: 0, pend: 0, pbase: 0 };
        self.w0 = self.st;
        self.wend = self.st;
        self.kbase = 0;
        self.kend = 0;
        self.uj = uj;
        self.uok = uok;
        self.pa = true;
        self.done = false;
    }

    #[inline(never)]
    fn refill(&mut self, k: usize) -> (r: Option<usize>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).same(old(self)),
            final(self).kbase <= k,
            old(self).kbase <= k < old(self).kend ==> *final(self) == *old(self) && r is Some,
            r matches Some(q) ==> k < final(self).all().len() && q == final(self).all()[k as int]
                && q < final(self).wend && k < final(self).kend,
            r is None ==> final(self).done && k >= final(self).all().len(),
    {
        let ghost o0 = *self;
        if k < self.kbase {
            self.rewind();
        }
        let ghost o = *self;
        loop
            invariant
                self.inv(),
                o0 == *old(self),
                self.same(&o0),
                self.kbase <= k,
                o.wend <= self.wend,
                o.kend <= self.kend,
                o0.kbase <= k < o0.kend ==> *self == o0,
            decreases self.s@.len() - self.wend + (if self.done { 0int } else { 1int }),
        {
            if k < self.kend {
                proof {
                    lemma_win_entry(self, k as int);
                }
                return Some(self.w0 + get32(self.buf.as_slice(), k - self.kbase) as usize);
            }
            if self.done {
                proof {
                    let g = self.s@;
                    let st = self.st as int;
                    lemma_rpos(g, st, self.w0 as int, self.wend as int);
                    lemma_positions_split(g, st, st, self.w0 as int, self.wend as int);
                }
                return None;
            }
            self.advance();
        }
    }
}

/// The structural index of `s[st..]` as one window, for inputs short
/// enough: the positions as offsets from `st`, with whether the input
/// passes stage 1's checks and whether it is UTF-8.
pub fn index(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (r: (usize, bool, bool))
    requires
        st <= s@.len(),
        s@.len() - st + 128 <= u32::MAX,
    ensures
        r.0 <= final(idx)@.len(),
        final(idx)@.subrange(0, r.0 as int) == rpos(s@, st as int, st as int, s@.len() as int),
        r.1 == (clean(s@, st as int, s@.len() as int) && !instr(s@, st as int, s@.len() - 1)),
        r.2 == utf8_from(s@, st as int),
{
    let (uj, uok) = crate::utf8::utf8_start(s, st);
    let kind = best_kind();
    let t = Stage1 { w: 0, carry_esc: 0, in_str: 0, prev: 0, err: 0, pend: 0, pbase: 0 };
    proof {
        assert(clean(s@, st as int, st as int));
        assert(crate::utf8::ascii_span(s@, st as int, st as int));
    }
    let r = fill_kind(kind, s, st, idx, st, s.len(), t, uj, uok, true);
    (r.0, r.1.err == 0 && r.1.in_str == 0, r.5)
}

} // verus!

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;

    /// Every entry of the index read through windows of `win` bytes with
    /// kernel `kind`, and whether the input is UTF-8.
    fn windowed(d: &[u8], win: usize, kind: u8) -> (Vec<usize>, bool) {
        let mut w = Win::with_kind(d, 0, win, Vec::new(), kind);
        let mut v = Vec::new();
        while let Some(q) = w.at(v.len()) {
            v.push(q);
        }
        (v, w.utf8)
    }

    /// The kernels agree, through windows of any size, with one scalar
    /// pass over the whole input, on inputs with every block layout.
    #[test]
    fn kernels_agree() {
        let mut x: u64 = 0x9E3779B97F4A7C15;
        let alphabet = b"[]{},:\"\\ \t\n0123456789.eEtrufalsn\x01\xc3\xa9x";
        let mut kinds = vec![SCALAR];
        if cpu_has_avx2() {
            kinds.push(AVX2);
        }
        if cpu_has_avx512() {
            kinds.push(AVX512);
        }
        for len in (0..400).chain([700, 1500]) {
            for _ in 0..20 {
                let d: Vec<u8> = (0..len)
                    .map(|_| {
                        x ^= x << 13;
                        x ^= x >> 7;
                        x ^= x << 17;
                        alphabet[(x % alphabet.len() as u64) as usize]
                    })
                    .collect();
                let mut a = Vec::new();
                let ra = structural_index::<SCALAR>(&d, 0, &mut a);
                assert_eq!(ra.2, std::str::from_utf8(&d).is_ok());
                let want: Vec<usize> = a[..ra.0].iter().map(|&q| q as usize).collect();
                for &kind in &kinds {
                    for win in [128, 256, 384, WINDOW] {
                        let (got, u) = windowed(&d, win, kind);
                        assert_eq!(got, want, "kind {kind} window {win} len {len}");
                        assert_eq!(u, ra.2);
                    }
                }
            }
        }
    }

    /// Reading backwards goes back to the start of the input as needed.
    #[test]
    fn rewind() {
        let d: Vec<u8> = b"[1, \"ab\\\\c\", {\"k\": null}],".iter().copied().cycle().take(5000).collect();
        let (all, _) = windowed(&d, 128, SCALAR);
        let mut w = Win::with_kind(&d, 0, 128, Vec::new(), SCALAR);
        for k in (0..all.len()).rev().step_by(7) {
            assert_eq!(w.at(k), Some(all[k]));
        }
        assert_eq!(w.at(all.len()), None);
    }
}

/// Trampolines that compile a verified `*_body` function with the target
/// features its kernel needs. Each is one call; `#[target_feature]` only
/// changes code generation. Verus rejects the attribute on verified code
/// (verus-lang/verus#3362), so it lives outside `verus!`.
#[cfg(target_arch = "x86_64")]
mod tf {
    #[allow(unused_imports)]
    use super::*;

    type Fill = (usize, Stage1, usize, bool, bool, bool);

    #[target_feature(enable = "avx512f,avx512bw,avx512vbmi2,pclmulqdq,popcnt,bmi1,bmi2")]
    #[allow(clippy::too_many_arguments)]
    pub(super) unsafe fn fill_avx512(s: &[u8], st: usize, idx: &mut Vec<u32>, w0: usize, lim: usize, t0: Stage1, uj0: usize, uok0: bool, pa0: bool) -> Fill {
        fill_avx512_body(s, st, idx, w0, lim, t0, uj0, uok0, pa0)
    }

    #[target_feature(enable = "avx2,pclmulqdq,popcnt,bmi1,bmi2")]
    #[allow(clippy::too_many_arguments)]
    pub(super) unsafe fn fill_avx2(s: &[u8], st: usize, idx: &mut Vec<u32>, w0: usize, lim: usize, t0: Stage1, uj0: usize, uok0: bool, pa0: bool) -> Fill {
        fill_avx2_body(s, st, idx, w0, lim, t0, uj0, uok0, pa0)
    }
}
