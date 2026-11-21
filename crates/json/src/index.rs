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

pub open spec fn structural(s: Seq<u8>, st: int, i: int) -> bool {
    (is_op(byte(s, i)) && !strs(s, st, i)) || uq(s, st, i) || scalar_start(s, st, i)
        || escape_start(s, st, i)
}

/// A control character inside a string, which RFC 8259 forbids.
pub open spec fn bad(s: Seq<u8>, st: int, i: int) -> bool {
    byte(s, i) < 0x20 && inside(s, st, i)
}

/// The structural positions in `[a, b)`, in order.
pub open spec fn positions(s: Seq<u8>, st: int, a: int, b: int) -> Seq<u32>
    decreases b - a,
{
    if b <= a {
        Seq::empty()
    } else {
        let p = positions(s, st, a, b - 1);
        if structural(s, st, b - 1) {
            p.push((b - 1) as u32)
        } else {
            p
        }
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
        block_classes(m, s, base),
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
        bit64(st_m, k) == structural(s, st, base + k),
        bit64(bad_m, k) == bad(s, st, base + k),
    decreases k,
{
    let c = byte(s, base + k);
    assert(bit64(m.quote, k) == (c == 0x22));
    assert(bit64(m.backslash, k) == (c == 0x5C));
    assert(bit64(m.ws, k) == is_ws(c));
    assert(bit64(m.op, k) == is_op(c));
    assert(bit64(m.ctrl, k) == (c < 0x20));
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

proof fn lemma_positions_block(s: Seq<u8>, st: int, base: int, m: u64, j: int)
    requires
        st <= base,
        0 <= j <= 64,
        base + 64 <= u32::MAX,
        forall|k: u64| k < 64 ==> #[trigger] bit64(m, k) == structural(s, st, base + k),
    ensures
        positions(s, st, st, base + j) == positions(s, st, st, base) + bits_upto(m, base, j),
    decreases j,
{
    if j > 0 {
        lemma_positions_block(s, st, base, m, j - 1);
        assert(bit64(m, (j - 1) as u64) == structural(s, st, base + j - 1));
        let a = positions(s, st, st, base);
        let b = bits_upto(m, base, j - 1);
        assert((a + b).push((base + j - 1) as u32) =~= a + b.push((base + j - 1) as u32));
    } else {
        assert(positions(s, st, st, base) + bits_upto(m, base, 0) =~= positions(s, st, st, base));
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

proof fn lemma_positions_past_end(s: Seq<u8>, st: int, b: int)
    requires
        st <= s.len() <= b,
    ensures
        positions(s, st, st, b) == positions(s, st, st, s.len() as int),
        clean(s, st, b) == clean(s, st, s.len() as int),
    decreases b,
{
    if b > s.len() {
        lemma_positions_past_end(s, st, b - 1);
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
pub struct Stage1 {
    /// Positions written so far.
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
    /// starts at `pbase`.
    pub pend: u64,
    pub pbase: u32,
}

/// The state after the blocks before `base`.
pub open spec fn stage1_inv(g: Seq<u8>, gst: int, base: int, idx: Seq<u32>, t: Stage1) -> bool {
    &&& 0 <= gst <= base
    &&& g.len() + 64 <= u32::MAX
    &&& idx.len() >= g.len() - gst + 64
    &&& gst <= t.pbase <= base
    &&& t.pbase <= g.len()
    &&& t.w <= t.pbase - gst
    &&& t.w + bits_upto(t.pend, t.pbase as int, 64).len() <= base - gst
    &&& idx.subrange(0, t.w as int) + bits_upto(t.pend, t.pbase as int, 64) == positions(g, gst, gst, base)
    &&& t.carry_esc <= 1
    &&& (t.carry_esc == 1) == esc(g, gst, base)
    &&& (t.in_str == 0 || t.in_str == 0xFFFF_FFFF_FFFF_FFFFu64)
    &&& (t.in_str == 0xFFFF_FFFF_FFFF_FFFFu64) == instr(g, gst, base - 1)
    &&& t.prev <= 1
    &&& (t.prev == 1) == (base > gst && scalar(g, gst, base - 1))
    &&& (t.err == 0) == clean(g, gst, base)
}

/// The part of stage 1's state that the bit logic carries.
pub open spec fn logic_inv(g: Seq<u8>, gst: int, base: int, t: Stage1) -> bool {
    &&& 0 <= gst <= base
    &&& g.len() + 64 <= u32::MAX
    &&& t.carry_esc <= 1
    &&& (t.carry_esc == 1) == esc(g, gst, base)
    &&& (t.in_str == 0 || t.in_str == 0xFFFF_FFFF_FFFF_FFFFu64)
    &&& (t.in_str == 0xFFFF_FFFF_FFFF_FFFFu64) == instr(g, gst, base - 1)
    &&& t.prev <= 1
    &&& (t.prev == 1) == (base > gst && scalar(g, gst, base - 1))
    &&& (t.err == 0) == clean(g, gst, base)
}

/// The bit logic of the block at `base`, from its classes `m`, escape
/// mask `e` (with carry out `c2`) and string mask `p`: the structural
/// bits and the state carried on. Writes nothing.
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
    let in_str = t.in_str;
    let prev = t.prev;
    let mut err = t.err;
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
            &&& #[trigger] bit64(st_m, k) == structural(g, gst, base + k)
            &&& bit64(bad_m, k) == bad(g, gst, base + k)
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
    let ghost err0 = err;
    err = err | bad_m;
    proof {
        lemma_or_zero(err0, bad_m);
        if err == 0 {
            assert forall|i: int| gst <= i < base + 64 implies !#[trigger] bad(g, gst, i) by {
                if i >= base {
                    let k = (i - base) as u64;
                    lemma_bit_consts(k);
                    assert(!bit64(bad_m, k));
                    assert(bit64(st_m, k) == structural(g, gst, base + k));
                    assert(bit64(bad_m, k) == bad(g, gst, base + k));
                }
            }
        } else if err0 == 0 {
            vstd::std_specs::bits::axiom_u64_trailing_zeros(bad_m);
            let k = vstd::std_specs::bits::u64_trailing_zeros(bad_m) as u64;
            assert(bit64(bad_m, k));
            assert(bit64(st_m, k) == structural(g, gst, base + k));
            assert(bit64(bad_m, k) == bad(g, gst, base + k));
            assert(bad(g, gst, base + k));
        }
        lemma_spread(r);
        lemma_bit_shl1(scalar_m, 0, 63);
        lemma_bit_shl1(r, 0, 63);
        assert(bit64(r, 63) == instr(g, gst, base + 63));
        assert(bit64(st_m, 63) == structural(g, gst, base + 63));
        assert(bit64(scalar_m, 63) == scalar(g, gst, base + 63));
    }
    (st_m, Stage1 { w: t.w, carry_esc: c2, in_str: 0u64.wrapping_sub(r >> 63u64), prev: scalar_m >> 63u64, err, pend: t.pend, pbase: t.pbase })
}

/// The block at `base`, held in four NEON vectors. Each class mask is
/// made where the bit logic first needs it (the backslashes for the
/// escapes, then the quotes for the strings, then the rest), so that the
/// vector work of one overlaps the scalar work of the one before.
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
) -> (o: (u64, Stage1))
    requires
        kernel_cpu(NEON),
        verilith_simd::neon::neon(),
        crate::neon::holds64(g, base as int, v0, v1, v2, v3),
        logic_inv(g, gst, base as int, t),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(o.0, k) == structural(g, gst, base + k),
        logic_inv(g, gst, base + 64, o.1),
        o.1.w == t.w,
        o.1.pend == t.pend,
        o.1.pbase == t.pbase,
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
    let (op, ctrl) = crate::neon::op_ctrl_mask64(v0, v1, v2, v3, Ghost(g), Ghost(b));
    let m = Masks { quote, backslash, ws, op, ctrl };
    proof {
        assert forall|k: u64| k < 64 implies {
            let c = #[trigger] byte(g, base + k);
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
            &&& bit64(m.ctrl, k) == (c < 0x20)
        } by {
            assert(byte(g, base + k) == g[b + k]);
        }
    }
    block_logic(m, e, c2, p, base, t, Ghost(g), Ghost(gst))
}

/// Processes the block at `base`, whose classes are `m`.
#[inline(always)]
fn stage1_block<const K: u8>(
    m: Masks,
    base: usize,
    idx: &mut Vec<u32>,
    t: Stage1,
    Ghost(g): Ghost<Seq<u8>>,
    Ghost(gst): Ghost<int>,
) -> (r: Stage1)
    requires
        kernel_cpu(K),
        stage1_inv(g, gst, base as int, old(idx)@, t),
        base < g.len(),
        block_classes(m, g, base as int),
    ensures
        final(idx)@.len() == old(idx)@.len(),
        stage1_inv(g, gst, base + 64, final(idx)@, r),
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
        lemma_positions_block(g, gst, base as int, st_m, 64);
        lemma_bits_len(st_m, base as int, 64);
        assert(idx@.subrange(0, w2 as int) =~= idx@.subrange(0, w as int) + idx@.subrange(
            w as int,
            w2 as int,
        ));
        assert(idx@.subrange(0, w as int) == ib.subrange(0, w as int));
    }
    Stage1 { w: w2, carry_esc: t2.carry_esc, in_str: t2.in_str, prev: t2.prev, err: t2.err, pend: st_m, pbase: base as u32 }
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

/// Stage 1's main loop with NEON, from the start of the text for as long
/// as 128 bytes are left. Returns the state, where it stopped, and the
/// UTF-8 check's state.
#[inline(always)]
fn stage1_neon(s: &[u8], st: usize, idx: &mut Vec<u32>, uj0: usize, uok0: bool) -> (r: (Stage1, usize, usize, bool))
    requires
        kernel_cpu(NEON),
        verilith_simd::neon::neon(),
        st <= s@.len(),
        s@.len() + 64 <= u32::MAX,
        old(idx)@.len() >= s@.len() - st + 64,
        crate::utf8::u8_state(s@, st as int, uj0 as int, uok0),
        s@.len() - st >= 3 ==> uj0 == st + 3,
    ensures
        final(idx)@.len() == old(idx)@.len(),
        st <= r.1 <= s@.len(),
        stage1_inv(s@, st as int, r.1 as int, final(idx)@, r.0),
        crate::utf8::u8_state(s@, st as int, r.2 as int, r.3),
{
    let ghost g = s@;
    let ghost gst = st as int;
    let ghost len0 = idx@.len();
    let n = s.len();
    let mut t = Stage1 { w: 0, carry_esc: 0, in_str: 0, prev: 0, err: 0, pend: 0, pbase: st as u32 };
    let mut base = st;
    let mut uj = uj0;
    let mut uok = uok0;
    proof {
        crate::simd::lemma_zero_upto(st as int, 64);
    }
    // Two blocks at a time. Each is loaded once, for its classes and
    // for the ASCII test of the UTF-8 check alike, and the positions
    // of both are written one whole turn later, so that the writes'
    // branches wait on nothing computed in this turn.
    let mut w: usize = 0;
    let mut qa: u64 = 0;
    let mut qb: u64 = 0;
    let mut qbase: usize = st;
    let mut pa = true;
    proof {
        crate::simd::lemma_zero_upto(st + 64, 64);
        assert(idx@.subrange(0, 0) + bits_upto(0, st as int, 64) + bits_upto(0, st + 64, 64) =~= positions(
            g,
            gst,
            gst,
            gst,
        ));
    }
    while n - base >= 128
        invariant
            kernel_cpu(NEON),
            verilith_simd::neon::neon(),
            g == s@,
            n == s@.len(),
            gst == st as int,
            st <= base <= n,
            idx@.len() == len0,
            len0 >= g.len() - gst + 64,
            logic_inv(g, gst, base as int, t),
            st <= qbase,
            qbase + 128 <= base || (qa == 0 && qb == 0 && qbase == base),
            w <= qbase - gst,
            idx@.subrange(0, w as int) + bits_upto(qa, qbase as int, 64) + bits_upto(qb, qbase + 64, 64)
                == positions(g, gst, gst, base as int),
            crate::utf8::u8_state(g, gst, uj as int, uok),
            n - st >= 3 ==> (uj == st + 3 && base == st) || (uj == base && st + 3 <= base),
            pa && n - st >= 3 ==> crate::utf8::ascii_span(g, uj - 3, base as int),
        decreases n - base,
    {
        let va = crate::neon::load64(s, base);
        let ha = crate::neon::ascii4(va.0, va.1, va.2, va.3, Ghost(g), Ghost(base as int));
        let ua = crate::utf8::utf8_block_neon(s, st, base, uj, uok, pa, ha);
        let (sa, t1) = block_neon(va.0, va.1, va.2, va.3, base, t, Ghost(g), Ghost(gst));
        let vb = crate::neon::load64(s, base + 64);
        let hb = crate::neon::ascii4(vb.0, vb.1, vb.2, vb.3, Ghost(g), Ghost(base + 64));
        let ub = crate::utf8::utf8_block_neon(s, st, base + 64, base + 64, ua.0, ua.1, hb);
        let (sb, t2) = block_neon(vb.0, vb.1, vb.2, vb.3, base + 64, t1, Ghost(g), Ghost(gst));
        let ghost i0 = idx@;
        let ghost la = bits_upto(qa, qbase as int, 64);
        let ghost lb = bits_upto(qb, qbase + 64, 64);
        proof {
            lemma_bits_len(qa, qbase as int, 64);
            lemma_bits_len(qb, qbase + 64, 64);
            crate::simd::lemma_zero_upto(qbase as int, 64);
            crate::simd::lemma_zero_upto(qbase + 64, 64);
        }
        let w1 = append_bits::<NEON>(idx, w, qa, qbase as u32);
        let ghost i1 = idx@;
        let w2 = append_bits::<NEON>(idx, w1, qb, (qbase + 64) as u32);
        proof {
            lemma_positions_block(g, gst, base as int, sa, 64);
            lemma_positions_block(g, gst, base + 64, sb, 64);
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
        w = w2;
        qa = sa;
        qb = sb;
        qbase = base;
        t = t2;
        uj = base + 128;
        uok = ub.0;
        pa = ub.1;
        base = base + 128;
        proof {
            lemma_bits_len(sa, qbase as int, 64);
            lemma_bits_len(sb, qbase + 64, 64);
        }
    }
    // The first of the two pending blocks; the second goes on as the
    // one-block loop's pending block.
    let ghost i0 = idx@;
    proof {
        lemma_bits_len(qa, qbase as int, 64);
        lemma_bits_len(qb, qbase + 64, 64);
        crate::simd::lemma_zero_upto(qbase as int, 64);
        crate::simd::lemma_zero_upto(qbase + 64, 64);
    }
    let w1 = append_bits::<NEON>(idx, w, qa, qbase as u32);
    let pb = if qbase < base { qbase + 64 } else { qbase };
    proof {
        assert(idx@.subrange(0, w1 as int) =~= i0.subrange(0, w as int) + bits_upto(qa, qbase as int, 64)) by {
            assert(idx@.subrange(0, w1 as int) =~= idx@.subrange(0, w as int) + idx@.subrange(w as int, w1 as int));
        }
    }
    t = Stage1 { w: w1, carry_esc: t.carry_esc, in_str: t.in_str, prev: t.prev, err: t.err, pend: qb, pbase: pb as u32 };
    (t, base, uj, uok)
}

/// Lists the structural positions of `s[st..]` at the start of `idx` and
/// returns how many there are. Also returns whether the input passes stage
/// 1's checks: no control character inside a string, and every string
/// closed.
#[inline(always)]
pub fn structural_index<const K: u8>(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (r: (usize, bool, bool))
    requires
        kernel_cpu(K),
        st <= s@.len(),
        s@.len() + 64 <= u32::MAX,
        K == NEON ==> verilith_simd::neon::neon(),
    ensures
        r.0 <= final(idx)@.len(),
        final(idx)@.subrange(0, r.0 as int) == positions(s@, st as int, st as int, s@.len() as int),
        r.1 == (clean(s@, st as int, s@.len() as int) && !instr(s@, st as int, s@.len() - 1)),
        r.2 == utf8_from(s@, st as int),
{
    proof {
        lemma_kernel_utf8(K);
    }
    // Room for every position plus the scratch writes of the last block.
    let need = s.len() - st + 64;
    if idx.len() < need {
        *idx = vec![0u32; need];
    }
    let ghost g = s@;
    let ghost gst = st as int;
    let ghost len0 = idx@.len();
    let mut t = Stage1 { w: 0, carry_esc: 0, in_str: 0, prev: 0, err: 0, pend: 0, pbase: st as u32 };
    let mut base = st;
    // UTF-8 validation runs alongside, on the bytes just indexed.
    let (mut uj, mut uok) = crate::utf8::utf8_start(s, st);
    proof {
        crate::simd::lemma_zero_upto(st as int, 64);
        assert(idx@.subrange(0, 0) + bits_upto(0, st as int, 64) =~= positions(g, gst, gst, gst));
    }
    let n = s.len();
    if K == NEON {
        let r = stage1_neon(s, st, idx, uj, uok);
        t = r.0;
        base = r.1;
        uj = r.2;
        uok = r.3;
    }
    // Two blocks at a time, classifying both before either is indexed.
    while (K == AVX2 || K == AVX512) && n - base >= 131
        invariant
            kernel_cpu(K),
            utf8_cpu(K),
            K == NEON ==> verilith_simd::neon::neon(),
            g == s@,
            n == s@.len(),
            gst == st as int,
            st <= base <= n,
            idx@.len() == len0,
            stage1_inv(g, gst, base as int, idx@, t),
            crate::utf8::u8_state(g, gst, uj as int, uok),
            K != NEON && n - st >= 3 ==> uj == base + 3,
        decreases n - base,
    {
        let m1 = full_classes::<K>(s, base);
        let m2 = full_classes::<K>(s, base + 64);
        t = stage1_block::<K>(m1, base, idx, t, Ghost(g), Ghost(gst));
        t = stage1_block::<K>(m2, base + 64, idx, t, Ghost(g), Ghost(gst));
        // `uj` is `base + 3`; written so, the loads of the UTF-8 check
        // are seen to be those of the classification above.
        let u = crate::utf8::utf8_step::<K>(s, st, base + 3, uok);
        uj = u.0;
        uok = u.1;
        base = base + 128;
    }
    while n - base >= 64
        invariant
            kernel_cpu(K),
            utf8_cpu(K),
            K == NEON ==> verilith_simd::neon::neon(),
            g == s@,
            n == s@.len(),
            gst == st as int,
            st <= base <= n,
            idx@.len() == len0,
            stage1_inv(g, gst, base as int, idx@, t),
        decreases n - base,
    {
        let m = full_classes::<K>(s, base);
        t = stage1_block::<K>(m, base, idx, t, Ghost(g), Ghost(gst));
        base = base + 64;
    }
    let ghost mut end = base as int;
    if base < n {
        let m = tail_classes::<K>(s, base);
        t = stage1_block::<K>(m, base, idx, t, Ghost(g), Ghost(gst));
        proof {
            end = base + 64;
        }
    }
    proof {
        lemma_positions_past_end(g, gst, end);
        if end > s.len() {
            lemma_past_end(g, gst, end - 1);
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
    }
    (w, t.err == 0 && t.in_str == 0, crate::utf8::utf8_finish::<K>(s, st, uj, uok))
}


} // verus!

verus! {

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn index_avx512_body(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (r: (usize, bool, bool))
    requires
        kernel_cpu(AVX512),
        st <= s@.len(),
        s@.len() + 64 <= u32::MAX,
    ensures
        r.0 <= final(idx)@.len(),
        final(idx)@.subrange(0, r.0 as int) == positions(s@, st as int, st as int, s@.len() as int),
        r.1 == (clean(s@, st as int, s@.len() as int) && !instr(s@, st as int, s@.len() - 1)),
        r.2 == utf8_from(s@, st as int),
{
    structural_index::<AVX512>(s, st, idx)
}

/// Trusted: `index_avx512_body` compiled with `avx512f,avx512bw,avx512vbmi2,pclmulqdq,popcnt,bmi1,bmi2` enabled, through
/// `tf::index_avx512`; the contract is `index_avx512_body`'s, which is verified.
/// The caller checks the CPU first.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn index_avx512(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (r: (usize, bool, bool))
    requires
        kernel_cpu(AVX512) && popcnt() && bmi2(),
        st <= s@.len(),
        s@.len() + 64 <= u32::MAX,
    ensures
        r.0 <= final(idx)@.len(),
        final(idx)@.subrange(0, r.0 as int) == positions(s@, st as int, st as int, s@.len() as int),
        r.1 == (clean(s@, st as int, s@.len() as int) && !instr(s@, st as int, s@.len() - 1)),
        r.2 == utf8_from(s@, st as int),
{
    // SAFETY: only called after the matching CPU check returned true.
    unsafe { tf::index_avx512(s, st, idx) }
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn index_avx2_body(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (r: (usize, bool, bool))
    requires
        kernel_cpu(AVX2),
        st <= s@.len(),
        s@.len() + 64 <= u32::MAX,
    ensures
        r.0 <= final(idx)@.len(),
        final(idx)@.subrange(0, r.0 as int) == positions(s@, st as int, st as int, s@.len() as int),
        r.1 == (clean(s@, st as int, s@.len() as int) && !instr(s@, st as int, s@.len() - 1)),
        r.2 == utf8_from(s@, st as int),
{
    structural_index::<AVX2>(s, st, idx)
}

/// Trusted: `index_avx2_body` compiled with `avx2,pclmulqdq,popcnt,bmi1,bmi2` enabled, through
/// `tf::index_avx2`; the contract is `index_avx2_body`'s, which is verified.
/// The caller checks the CPU first.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn index_avx2(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (r: (usize, bool, bool))
    requires
        kernel_cpu(AVX2) && popcnt() && bmi2(),
        st <= s@.len(),
        s@.len() + 64 <= u32::MAX,
    ensures
        r.0 <= final(idx)@.len(),
        final(idx)@.subrange(0, r.0 as int) == positions(s@, st as int, st as int, s@.len() as int),
        r.1 == (clean(s@, st as int, s@.len() as int) && !instr(s@, st as int, s@.len() - 1)),
        r.2 == utf8_from(s@, st as int),
{
    // SAFETY: only called after the matching CPU check returned true.
    unsafe { tf::index_avx2(s, st, idx) }
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

/// `structural_index` with the best kernel this CPU supports.
pub fn index(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (r: (usize, bool, bool))
    requires
        st <= s@.len(),
        s@.len() + 64 <= u32::MAX,
    ensures
        r.0 <= final(idx)@.len(),
        final(idx)@.subrange(0, r.0 as int) == positions(s@, st as int, st as int, s@.len() as int),
        r.1 == (clean(s@, st as int, s@.len() as int) && !instr(s@, st as int, s@.len() - 1)),
        r.2 == utf8_from(s@, st as int),
{
    #[cfg(target_arch = "x86_64")]
    {
        if cpu_has_avx512() {
            return unsafe { index_avx512(s, st, idx) };
        }
        if cpu_has_avx2() {
            return unsafe { index_avx2(s, st, idx) };
        }
    }
    if verilith_simd::neon::has_neon() {
        return structural_index::<NEON>(s, st, idx);
    }
    structural_index::<SCALAR>(s, st, idx)
}

} // verus!

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;

    /// The three kernels agree on inputs with every block layout.
    #[test]
    fn kernels_agree() {
        let mut x: u64 = 0x9E3779B97F4A7C15;
        let alphabet = b"[]{},:\"\\ \t\n0123456789.eEtrufalsn\x01\xc3\xa9x";
        for len in 0..400 {
            for _ in 0..20 {
                let d: Vec<u8> = (0..len)
                    .map(|_| {
                        x ^= x << 13;
                        x ^= x >> 7;
                        x ^= x << 17;
                        alphabet[(x % alphabet.len() as u64) as usize]
                    })
                    .collect();
                let (mut a, mut b) = (Vec::new(), Vec::new());
                let ra = structural_index::<SCALAR>(&d, 0, &mut a);
                let rb = unsafe { index_avx2(&d, 0, &mut b) };
                assert_eq!((ra.1, ra.2), (rb.1, rb.2));
                assert_eq!(ra.2, std::str::from_utf8(&d).is_ok());
                assert_eq!(a[..ra.0], b[..rb.0]);
                if cpu_has_avx512() {
                    let mut c = Vec::new();
                    let rc = unsafe { index_avx512(&d, 0, &mut c) };
                    assert_eq!((ra.1, ra.2), (rc.1, rc.2));
                    assert_eq!(a[..ra.0], c[..rc.0]);
                }
            }
        }
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

    #[target_feature(enable = "avx512f,avx512bw,avx512vbmi2,pclmulqdq,popcnt,bmi1,bmi2")]
    pub(super) unsafe fn index_avx512(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (usize, bool, bool) {
        index_avx512_body(s, st, idx)
    }

    #[target_feature(enable = "avx2,pclmulqdq,popcnt,bmi1,bmi2")]
    pub(super) unsafe fn index_avx2(s: &[u8], st: usize, idx: &mut Vec<u32>) -> (usize, bool, bool) {
        index_avx2_body(s, st, idx)
    }
}
