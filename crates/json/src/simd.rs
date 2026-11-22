//! Byte classification and bit-mask helpers, built from the single
//! instructions modelled in `lanes.rs` and verified against per-byte
//! specs.
//!
//! The 16-byte functions use SSE2, which every x86_64 CPU has. The 64-byte
//! ones have AVX-512, AVX2 and scalar versions, chosen by a `const` kernel
//! parameter. Other targets use scalar loops with the same contracts.
#[allow(unused_imports)]
use crate::spec::*;
#[allow(unused_imports)]
use crate::lanes::*;
pub use verilith_core::prims::{get as get8, get32, store_at};
#[allow(unused_imports)]
use verilith_simd::cpu::*;
use vstd::prelude::*;

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::{__m128i, __m256i};


verus! {

/// A byte that can appear unescaped inside a string and does not end it.
pub open spec fn plain(c: u8) -> bool {
    c != 0x22 && c != 0x5C && c >= 0x20
}

pub open spec fn is_digit_byte(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// The first `n` lanes of `v`, read as decimal digit values, most
/// significant first.
pub open spec fn dlanes(v: Seq<u8>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { dlanes(v, n - 1) * 10 + v[n - 1] as int }
}

/// 5^-k modulo 2^64, for k = 0..=16.
pub const INV5: [u64; 17] = [
    0x0000000000000001, 0xcccccccccccccccd, 0x8f5c28f5c28f5c29, 0x1cac083126e978d5,
    0xd288ce703afb7e91, 0x5d4e8fb00bcbe61d, 0x790fb65668c26139, 0xe5032477ae8d46a5,
    0xc767074b22e90e21, 0x8e47ce423a2e9c6d, 0x4fa7f60d3ed61f49, 0x0fee64690c913975,
    0x3662e0e1cf503eb1, 0xa47a2cf9f6433fbd, 0x54186f653140a659, 0x7738164770402145,
    0xe4a4d1417cd9a041,
];

pub open spec fn p5i(k: nat) -> int
    decreases k,
{
    if k == 0 { 1 } else { 5 * p5i((k - 1) as nat) }
}

pub open spec fn inv5_ok_below(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        (INV5@[n - 1] as int * p5i((n - 1) as nat)) % 0x1_0000_0000_0000_0000 == 1 && inv5_ok_below((n - 1) as nat)
    }
}

proof fn lemma_inv5_below(n: nat, k: nat)
    requires
        inv5_ok_below(n),
        k < n,
    ensures
        (INV5@[k as int] as int * p5i(k)) % 0x1_0000_0000_0000_0000 == 1,
    decreases n,
{
    if k != n - 1 {
        lemma_inv5_below((n - 1) as nat, k);
    }
}

/// `INV5[k]` is the inverse of 5^k modulo 2^64: checked by evaluation.
pub proof fn lemma_inv5(k: nat)
    requires
        k <= 16,
    ensures
        (INV5@[k as int] as int * p5i(k)) % 0x1_0000_0000_0000_0000 == 1,
{
    assert(inv5_ok_below(17)) by (compute_only);
    lemma_inv5_below(17, k);
}

/// Lanes past `n` that are zero add trailing zeros.
pub proof fn lemma_dlanes_zeros(v: Seq<u8>, n: int, m: int)
    requires
        0 <= n <= m,
        forall|k: int| n <= k < m ==> v[k] == 0,
    ensures
        dlanes(v, m) == dlanes(v, n) * p10i((m - n) as nat),
    decreases m - n,
{
    if m > n {
        lemma_dlanes_zeros(v, n, m - 1);
        assert(p10i((m - n) as nat) == 10 * p10i((m - 1 - n) as nat));
        assert(dlanes(v, n) * p10i((m - 1 - n) as nat) * 10 == dlanes(v, n) * p10i((m - n) as nat)) by (nonlinear_arith)
            requires p10i((m - n) as nat) == 10 * p10i((m - 1 - n) as nat);
    }
}

/// Lanes that agree below `n` give the same value.
pub proof fn lemma_dlanes_same(v: Seq<u8>, u: Seq<u8>, n: int)
    requires
        forall|k: int| 0 <= k < n ==> v[k] == u[k],
    ensures
        dlanes(v, n) == dlanes(u, n),
    decreases n,
{
    if n > 0 {
        lemma_dlanes_same(v, u, n - 1);
    }
}

pub proof fn lemma_dlanes_bound(v: Seq<u8>, n: int)
    requires
        n >= 0,
        forall|k: int| 0 <= k < n ==> v[k] <= 9,
    ensures
        0 <= dlanes(v, n) < p10i(n as nat),
    decreases n,
{
    if n > 0 {
        lemma_dlanes_bound(v, n - 1);
        assert(p10i(n as nat) == 10 * p10i((n - 1) as nat));
    }
}


/// `{ } [ ] , :`
pub open spec fn is_op(c: u8) -> bool {
    c == 0x7B || c == 0x7D || c == 0x5B || c == 0x5D || c == 0x2C || c == 0x3A
}

/// The four bytes at `i` as a little-endian word.
#[verifier::external_body]
#[inline(always)]
pub fn load4(s: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= s@.len(),
    ensures
        r == s@[i as int] as u32 | (s@[i + 1] as u32) << 8u32 | (s@[i + 2] as u32) << 16u32
            | (s@[i + 3] as u32) << 24u32,
{
    u32::from_le(unsafe { (s.as_ptr().add(i) as *const u32).read_unaligned() })
}

/// Whether the four bytes at `i` are `b0 b1 b2 b3`, by one word compare.
#[inline(always)]
pub fn ex_has4(s: &[u8], i: usize, b0: u8, b1: u8, b2: u8, b3: u8) -> (r: bool)
    requires
        i <= s@.len(),
    ensures
        r == (i + 4 <= s@.len() && s@[i as int] == b0 && s@[i + 1] == b1 && s@[i + 2] == b2
            && s@[i + 3] == b3),
{
    if s.len() - i < 4 {
        return false;
    }
    let w = b0 as u32 | (b1 as u32) << 8u32 | (b2 as u32) << 16u32 | (b3 as u32) << 24u32;
    proof {
        lemma_word_eq(s@[i as int], s@[i + 1], s@[i + 2], s@[i + 3], b0, b1, b2, b3);
    }
    load4(s, i) == w
}

#[verifier::bit_vector]
proof fn lemma_word_eq(a0: u8, a1: u8, a2: u8, a3: u8, b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        (a0 as u32 | (a1 as u32) << 8u32 | (a2 as u32) << 16u32 | (a3 as u32) << 24u32 == b0 as u32
            | (b1 as u32) << 8u32 | (b2 as u32) << 16u32 | (b3 as u32) << 24u32) == (a0 == b0 && a1
            == b1 && a2 == b2 && a3 == b3),
{
}

/// Which instruction set the 64-byte primitives use.
/// What the kernel `k` needs of the CPU: its vector instructions and the
/// carry-less multiply.
pub open spec fn kernel_cpu(k: u8) -> bool {
    &&& k == AVX2 ==> verilith_simd::cpu::avx2() && verilith_simd::cpu::pclmul()
    &&& k == AVX512 ==> verilith_simd::cpu::avx512vbmi2() && verilith_simd::cpu::pclmul()
}

/// What the UTF-8 validator's kernel `k` needs of the CPU.
pub open spec fn utf8_cpu(k: u8) -> bool {
    &&& k == AVX2 ==> verilith_simd::cpu::avx2()
    &&& k == AVX512 ==> verilith_simd::cpu::avx512bw()
}

/// A CPU that runs kernel `k` runs the UTF-8 validator's.
pub proof fn lemma_kernel_utf8(k: u8)
    requires
        kernel_cpu(k),
    ensures
        utf8_cpu(k),
{
    broadcast use verilith_simd::cpu::axiom_avx512_implications;
}

pub const SCALAR: u8 = 0;
pub const AVX2: u8 = 1;
pub const AVX512: u8 = 2;
/// AArch64 NEON (`crate::neon`).
pub const NEON: u8 = 3;

/// Classes of the 64 bytes of a block, one bit per byte.
pub struct Masks {
    pub quote: u64,
    pub backslash: u64,
    pub ws: u64,
    pub op: u64,
    pub ctrl: u64,
}

pub open spec fn masks_of(m: Masks, s: Seq<u8>, i: int) -> bool {
    forall|k: u64|
        k < 64 ==> {
            let c = #[trigger] s[i + k];
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
            &&& bit64(m.ctrl, k) == (c < 0x20)
        }
}

// ---------------------------------------------------------------------------
// Bit lemmas
// ---------------------------------------------------------------------------

#[verifier::bit_vector]
proof fn lemma_or4(a: u64, b: u64, c: u64, d: u64, k: u64)
    requires
        k < 64,
    ensures
        (((a | b | c | d) >> k) & 1u64 == 1u64) == (((a >> k) & 1u64 == 1u64) || ((b >> k) & 1u64
            == 1u64) || ((c >> k) & 1u64 == 1u64) || ((d >> k) & 1u64 == 1u64)),
{
}

#[verifier::bit_vector]
proof fn lemma_or4_32(a: u32, b: u32, c: u32, d: u32, k: u32)
    requires
        k < 32,
    ensures
        (((a | b | c | d) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) || ((b >> k) & 1u32
            == 1u32) || ((c >> k) & 1u32 == 1u32) || ((d >> k) & 1u32 == 1u32)),
        (((a | b) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) || ((b >> k) & 1u32
            == 1u32)),
        ((!a >> k) & 1u32 == 1u32) == !((a >> k) & 1u32 == 1u32),
{
}

/// `c | 0x20` folds `[ ]` onto `{ }`.
#[verifier::bit_vector]
proof fn lemma_fold_brackets(c: u8)
    ensures
        (c | 0x20u8 == 0x7Bu8) == (c == 0x7Bu8 || c == 0x5Bu8),
        (c | 0x20u8 == 0x7Du8) == (c == 0x7Du8 || c == 0x5Du8),
{
}

/// The top bit of an OR is the OR of the top bits.
#[verifier::bit_vector]
proof fn lemma_top_or(a: u8, b: u8)
    ensures
        ((a | b) >= 0x80u8) == (a >= 0x80u8 || b >= 0x80u8),
{
}

/// Two 32-bit movemasks side by side.
#[verifier::bit_vector]
proof fn lemma_join(lo: u32, hi: u32, k: u64)
    requires
        k < 64,
    ensures
        k < 32 ==> ((((lo as u64) | ((hi as u64) << 32u64)) >> k) & 1u64 == 1u64) == (((lo >> (k
            as u32)) & 1u32) == 1u32),
        k >= 32 ==> ((((lo as u64) | ((hi as u64) << 32u64)) >> k) & 1u64 == 1u64) == (((hi >> ((
        k - 32) as u32)) & 1u32) == 1u32),
{
}

/// Setting bit `k` of a mask whose bits from `k` up are clear.
#[verifier::bit_vector]
proof fn lemma_set_bit(m: u64, k: u64, j: u64)
    requires
        k < 64,
        j < 64,
        m >> k == 0u64,
    ensures
        (((m | (1u64 << k)) >> j) & 1u64 == 1u64) == (((m >> j) & 1u64 == 1u64) || j == k),
        (m | (1u64 << k)) >> k == 1u64,
        k < 63 ==> (m | (1u64 << k)) >> add(k, 1u64) == 0u64,
        k < 63 ==> m >> add(k, 1u64) == 0u64,
        j >= k ==> (m >> j) & 1u64 == 0u64,
{
}

#[verifier::bit_vector]
proof fn lemma_zero_bits(k: u64)
    requires
        k < 64,
    ensures
        0u64 >> k == 0u64,
        (0u64 >> k) & 1u64 == 0u64,
        (0xFFFF_FFFF_FFFF_FFFFu64 >> k) & 1u64 == 1u64,
{
}

// ---------------------------------------------------------------------------
// 64-byte classification
// ---------------------------------------------------------------------------

/// The scalar kernel: one byte at a time.
#[inline(always)]
fn classify64_scalar(s: &[u8], i: usize) -> (m: Masks)
    requires
        i + 64 <= s@.len(),
    ensures
        masks_of(m, s@, i as int),
{
    let _n = s.len();
    let mut m = Masks { quote: 0, backslash: 0, ws: 0, op: 0, ctrl: 0 };
    let mut k: u64 = 0;
    proof {
        lemma_zero_bits(0);
    }
    while k < 64
        invariant
            k <= 64,
            i + 64 <= s@.len(),
            _n == s@.len(),
            k < 64 ==> m.quote >> k == 0 && m.backslash >> k == 0 && m.ws >> k == 0 && m.op >> k
                == 0 && m.ctrl >> k == 0,
            forall|j: u64|
                j < k ==> {
                    let c = #[trigger] s@[i + j];
                    &&& bit64(m.quote, j) == (c == 0x22)
                    &&& bit64(m.backslash, j) == (c == 0x5C)
                    &&& bit64(m.ws, j) == is_ws(c)
                    &&& bit64(m.op, j) == is_op(c)
                    &&& bit64(m.ctrl, j) == (c < 0x20)
                },
        decreases 64 - k,
    {
        let c = get8(s, i + k as usize);
        let b = 1u64 << k;
        let ghost m0 = m;
        if c == 0x22 {
            m.quote = m.quote | b;
        }
        if c == 0x5C {
            m.backslash = m.backslash | b;
        }
        if c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D {
            m.ws = m.ws | b;
        }
        if c == 0x7B || c == 0x7D || c == 0x5B || c == 0x5D || c == 0x2C || c == 0x3A {
            m.op = m.op | b;
        }
        if c < 0x20 {
            m.ctrl = m.ctrl | b;
        }
        proof {
            assert forall|j: u64| j < k + 1 implies {
                let c = #[trigger] s@[i + j];
                &&& bit64(m.quote, j) == (c == 0x22)
                &&& bit64(m.backslash, j) == (c == 0x5C)
                &&& bit64(m.ws, j) == is_ws(c)
                &&& bit64(m.op, j) == is_op(c)
                &&& bit64(m.ctrl, j) == (c < 0x20)
            } by {
                lemma_set_bit(m0.quote, k, j);
                lemma_set_bit(m0.backslash, k, j);
                lemma_set_bit(m0.ws, k, j);
                lemma_set_bit(m0.op, k, j);
                lemma_set_bit(m0.ctrl, k, j);
            }
            if k < 63 {
                lemma_set_bit(m0.quote, k, 0);
                lemma_set_bit(m0.backslash, k, 0);
                lemma_set_bit(m0.ws, k, 0);
                lemma_set_bit(m0.op, k, 0);
                lemma_set_bit(m0.ctrl, k, 0);
            }
        }
        k = k + 1;
    }
    m
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn classify64_avx512(s: &[u8], i: usize) -> (m: Masks)
    requires
        avx512bw(),
        i + 64 <= s@.len(),
    ensures
        masks_of(m, s@, i as int),
{
    // simdjson's lookup: a byte is whitespace when the table entry for its
    // low nibble is the byte itself, and an operator when the other
    // table's entry is the byte with bit 5 set (which maps '[' and ']' onto
    // '{' and '}'). The second test also accepts 0x0C and 0x1A, which the
    // control-byte mask removes.
    let v = load64(s, i);
    let sw = shuffle64(table64(&WS_TABLE), v);
    let so = shuffle64(table64(&OP_TABLE), v);
    let f = or64(v, splat64(0x20));
    let ws = eq_mask64(sw, v);
    let op1 = eq_mask64(so, f);
    let ctrl = le_mask64(v, splat64(0x1F));
    let m = Masks {
        quote: eq_mask64(v, splat64(0x22)),
        backslash: eq_mask64(v, splat64(0x5C)),
        ws,
        op: op1 & !ctrl,
        ctrl,
    };
    proof {
        assert forall|k: u64| k < 64 implies {
            let c = #[trigger] s@[i + k];
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
            &&& bit64(m.ctrl, k) == (c < 0x20)
        } by {
            let c = s@[i + k];
            let ki = k as int;
            assert(b64(v)[ki] == c);
            assert(b64(f)[ki] == c | 0x20);
            lemma_lane16(ki, c);
            let ix = ki / 16 * 16 + (c % 16) as int;
            assert(0 <= ix < 64);
            assert(ix % 16 == (c % 16) as int);
            assert(b64(sw)[ki] == if c >= 0x80 { 0u8 } else { WS_TABLE@[(c % 16) as int] });
            assert(b64(so)[ki] == if c >= 0x80 { 0u8 } else { OP_TABLE@[(c % 16) as int] });
            assert(bit64(ws, k) == (b64(sw)[ki] == b64(v)[ki]));
            assert(bit64(op1, k) == (b64(so)[ki] == b64(f)[ki]));
            lemma_tables(c);
            crate::index::lemma_bit_ops(op1, !ctrl, k);
            crate::index::lemma_bit_ops(ctrl, ctrl, k);
            assert(bit64(m.quote, k) == (c == 0x22));
            assert(bit64(m.backslash, k) == (c == 0x5C));
            assert(bit64(ctrl, k) == (c <= 0x1F));
            assert(bit64(m.ws, k) == is_ws(c));
            assert(bit64(m.op, k) == (bit64(op1, k) && !bit64(ctrl, k)));
            assert(bit64(m.op, k) == is_op(c));
        }
    }
    m
}

/// Whitespace lookup: entry `n` is the one whitespace byte whose low nibble
/// is `n`, or 0x80, which no byte below 0x80 equals.
pub const WS_TABLE: [u8; 16] = [
    0x20, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x09, 0x0A, 0x80, 0x80, 0x0D, 0x80, 0x80,
];

/// Operator lookup, compared against the byte with bit 5 set.
pub const OP_TABLE: [u8; 16] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x3A, 0x7B, 0x2C, 0x7D, 0, 0];

pub proof fn lemma_lane16(k: int, c: u8)
    requires
        0 <= k < 64,
    ensures
        (k / 16 * 16 + c % 16) % 16 == c % 16,
{
    assert((k / 16 * 16 + c % 16) % 16 == c % 16) by (nonlinear_arith)
        requires 0 <= k < 64, 0 <= c % 16 < 16;
}

/// The two lookups give exactly the classes, for every byte.
pub proof fn lemma_tables(c: u8)
    ensures
        ((if c >= 0x80 { 0u8 } else { WS_TABLE@[(c % 16) as int] }) == c) == is_ws(c),
        ((if c >= 0x80 { 0u8 } else { OP_TABLE@[(c % 16) as int] }) == (c | 0x20) && !(c <= 0x1F)) == is_op(c),
{
    assert(c | 0x20 == if c & 0x20 == 0 { (c + 0x20) as u8 } else { c }) by (bit_vector);
    assert(c & 0x20 == 0 <==> (c / 32) % 2 == 0) by (bit_vector);
}

/// One class over 64 bytes from two 32-byte halves of 0xFF/0 lanes.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn join32(lo: __m256i, hi: __m256i) -> (m: u64)
    requires
        avx2(),
        b32(lo).len() == 32,
        b32(hi).len() == 32,
    ensures
        forall|k: u64|
            k < 64 ==> #[trigger] bit64(m, k) == if k < 32 {
                b32(lo)[k as int] >= 0x80
            } else {
                b32(hi)[k - 32] >= 0x80
            },
{
    let a = movemask32(lo);
    let b = movemask32(hi);
    let m = opaque64((a as u64) | ((b as u64) << 32u64));
    proof {
        assert forall|k: u64| k < 64 implies #[trigger] bit64(m, k) == if k < 32 {
            b32(lo)[k as int] >= 0x80
        } else {
            b32(hi)[k - 32] >= 0x80
        } by {
            lemma_join(a, b, k);
            if k < 32 {
                assert(bit(a, k as u32) == (b32(lo)[k as int] >= 0x80));
            } else {
                assert(bit(b, (k - 32) as u32) == (b32(hi)[(k - 32) as int] >= 0x80));
            }
        }
    }
    m
}

/// The class vectors of 32 bytes: 0xFF where the byte is in the class,
/// else 0. As in the AVX-512 classifier, `r.3` also marks 0x0C and 0x1A,
/// which are control bytes (`r.4`).
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn classes32(s: &[u8], i: usize) -> (r: (__m256i, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        i + 32 <= s@.len(),
    ensures
        b32(r.0).len() == 32,
        b32(r.1).len() == 32,
        b32(r.2).len() == 32,
        b32(r.3).len() == 32,
        b32(r.4).len() == 32,
        forall|k: int|
            0 <= k < 32 ==> {
                let c = #[trigger] s@[i + k];
                &&& (b32(r.0)[k] >= 0x80) == (c == 0x22)
                &&& (b32(r.1)[k] >= 0x80) == (c == 0x5C)
                &&& (b32(r.2)[k] >= 0x80) == is_ws(c)
                &&& (b32(r.3)[k] >= 0x80 && !(c < 0x20)) == is_op(c)
                &&& (b32(r.4)[k] >= 0x80) == (c < 0x20)
            },
{
    let v = load32(s, i);
    let sw = shuffle32(table32(&WS_TABLE), v);
    let so = shuffle32(table32(&OP_TABLE), v);
    let f = or32(v, splat32(0x20));
    let q = eq32(v, splat32(0x22));
    let b = eq32(v, splat32(0x5C));
    let ws = eq32(sw, v);
    let op = eq32(so, f);
    // Unsigned v <= 0x1F.
    let k1f = splat32(0x1F);
    let ctrl = eq32(max32(v, k1f), k1f);
    proof {
        assert forall|k: int| 0 <= k < 32 implies {
            let c = #[trigger] s@[i + k];
            &&& (b32(q)[k] >= 0x80) == (c == 0x22)
            &&& (b32(b)[k] >= 0x80) == (c == 0x5C)
            &&& (b32(ws)[k] >= 0x80) == is_ws(c)
            &&& (b32(op)[k] >= 0x80 && !(c < 0x20)) == is_op(c)
            &&& (b32(ctrl)[k] >= 0x80) == (c < 0x20)
        } by {
            let c = s@[i + k];
            assert(b32(v)[k] == c);
            assert(b32(f)[k] == c | 0x20);
            lemma_lane16(k, c);
            let ix = k / 16 * 16 + (c % 16) as int;
            assert(0 <= ix < 32);
            assert(ix % 16 == (c % 16) as int);
            assert(b32(sw)[k] == if c >= 0x80 { 0u8 } else { WS_TABLE@[(c % 16) as int] });
            assert(b32(so)[k] == if c >= 0x80 { 0u8 } else { OP_TABLE@[(c % 16) as int] });
            lemma_tables(c);
        }
    }
    (q, b, ws, op, ctrl)
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn classify64_avx2(s: &[u8], i: usize) -> (m: Masks)
    requires
        avx2(),
        i + 64 <= s@.len(),
    ensures
        masks_of(m, s@, i as int),
{
    let _n = s.len();
    let lo = classes32(s, i);
    let hi = classes32(s, i + 32);
    let op1 = join32(lo.3, hi.3);
    let ctrl = join32(lo.4, hi.4);
    let m = Masks {
        quote: join32(lo.0, hi.0),
        backslash: join32(lo.1, hi.1),
        ws: join32(lo.2, hi.2),
        op: op1 & !ctrl,
        ctrl,
    };
    proof {
        assert forall|k: u64| k < 64 implies {
            let c = #[trigger] s@[i + k];
            &&& bit64(m.quote, k) == (c == 0x22)
            &&& bit64(m.backslash, k) == (c == 0x5C)
            &&& bit64(m.ws, k) == is_ws(c)
            &&& bit64(m.op, k) == is_op(c)
            &&& bit64(m.ctrl, k) == (c < 0x20)
        } by {
            let c = s@[i + k];
            crate::index::lemma_bit_ops(op1, !ctrl, k);
            crate::index::lemma_bit_ops(ctrl, ctrl, k);
            if k >= 32 {
                let kk = (k - 32) as int;
                assert(s@[(i + 32) + kk] == c);
                assert(bit64(op1, k) == (b32(hi.3)[kk] >= 0x80));
                assert(bit64(ctrl, k) == (b32(hi.4)[kk] >= 0x80));
            } else {
                assert(s@[i + (k as int)] == c);
                assert(bit64(op1, k) == (b32(lo.3)[k as int] >= 0x80));
                assert(bit64(ctrl, k) == (b32(lo.4)[k as int] >= 0x80));
            }
            assert(bit64(m.op, k) == (bit64(op1, k) && !bit64(ctrl, k)));
        }
    }
    m
}

/// Classifies `s[i..i + 64]` with kernel `K`.
#[inline(always)]
pub fn classify64<const K: u8>(s: &[u8], i: usize) -> (m: Masks)
    requires
        kernel_cpu(K),
        i + 64 <= s@.len(),
        K == NEON ==> verilith_simd::neon::neon(),
    ensures
        masks_of(m, s@, i as int),
{
    proof {
        broadcast use verilith_simd::cpu::axiom_avx512_implications;
    }
    if K == NEON {
        return crate::neon::classify64_neon(s, i);
    }
    #[cfg(target_arch = "x86_64")]
    {
        if K == AVX512 {
            return classify64_avx512(s, i);
        }
        if K == AVX2 {
            return classify64_avx2(s, i);
        }
    }
    classify64_scalar(s, i)
}

// ---------------------------------------------------------------------------
// Prefix XOR
// ---------------------------------------------------------------------------

#[verifier::bit_vector]
proof fn lemma_clmul_step(x: u64, a: u64, n: u64)
    requires
        1 <= n < 64,
        a ^ (a << 1u64) == x ^ ((x << sub(n, 1u64)) << 1u64),
    ensures
        (a ^ (x << n)) ^ ((a ^ (x << n)) << 1u64) == x ^ ((x << n) << 1u64),
{
}

#[verifier::bit_vector]
proof fn lemma_clmul_ends(x: u64)
    ensures
        0u64 ^ (x << 0u64) == x,
        x ^ (x << 1u64) == x ^ ((x << 0u64) << 1u64),
        x ^ ((x << 63u64) << 1u64) == x,
{
}

/// Multiplying by all ones is prefix XOR: after `n` terms,
/// `r ^ (r << 1)` is `x` with `x << n` mixed in, which vanishes at 64.
proof fn lemma_clmul_ones(x: u64, n: nat)
    requires
        1 <= n <= 64,
    ensures
        ({
            let r = clmul_upto(x, 0xFFFF_FFFF_FFFF_FFFFu64, n);
            r ^ (r << 1u64) == x ^ ((x << ((n - 1) as u64)) << 1u64)
        }),
    decreases n,
{
    lemma_zero_bits((n - 1) as u64);
    lemma_clmul_ends(x);
    if n > 1 {
        lemma_clmul_ones(x, (n - 1) as nat);
        lemma_clmul_step(x, clmul_upto(x, 0xFFFF_FFFF_FFFF_FFFFu64, (n - 1) as nat), (n - 1) as u64);
    } else {
        assert(clmul_upto(x, 0xFFFF_FFFF_FFFF_FFFFu64, 0) == 0);
    }
}

/// Prefix XOR: bit `k` of the result is the XOR of bits `0..=k` of `x`,
/// stated as the identity `r ^ (r << 1) == x`. With AVX2 or AVX-512 this is
/// one carry-less multiply by all ones.
#[inline(always)]
pub fn prefix_xor_clmul<const K: u8>(x: u64) -> (r: u64)
    requires
        kernel_cpu(K),
    ensures
        r ^ (r << 1u64) == x,
{
    #[cfg(target_arch = "x86_64")]
    {
        if K == AVX512 || K == AVX2 {
            let r = clmul_lo(x, 0xFFFF_FFFF_FFFF_FFFFu64);
            proof {
                lemma_clmul_ones(x, 64);
                lemma_clmul_ends(x);
            }
            return r;
        }
    }
    crate::index::prefix_xor(x)
}

// ---------------------------------------------------------------------------
// Writing out set bits
// ---------------------------------------------------------------------------

/// `bits_upto` with a base is the base-0 list shifted.
proof fn lemma_bits_base(m: u64, base: int, j: int)
    requires
        0 <= j <= 64,
        0 <= base,
        base + 64 <= u32::MAX,
    ensures
        bits_upto(m, base, j).len() == bits_upto(m, 0, j).len(),
        forall|t: int|
            0 <= t < bits_upto(m, base, j).len() ==> #[trigger] bits_upto(m, base, j)[t] == bits_upto(
                m,
                0,
                j,
            )[t] + base && bits_upto(m, 0, j)[t] < j,
    decreases j,
{
    if j > 0 {
        lemma_bits_base(m, base, j - 1);
        let a = bits_upto(m, base, j - 1);
        let b = bits_upto(m, 0, j - 1);
        if bit64(m, (j - 1) as u64) {
            let a2 = a.push((base + j - 1) as u32);
            let b2 = b.push((j - 1) as u32);
            assert forall|t: int| 0 <= t < a2.len() implies #[trigger] a2[t] == b2[t] + base && b2[t]
                < j by {
                if t < a.len() {
                    assert(a2[t] == a[t]);
                    assert(b2[t] == b[t]);
                }
            }
        }
    }
}

/// Clearing the lowest set bit `t` drops the first entry.
proof fn lemma_bits_lowest(m: u64, base: int, t: u64, j: int)
    requires
        0 <= j <= 64,
        t < 64,
        bit64(m, t),
        forall|q: u64| q < t ==> !#[trigger] bit64(m, q),
        m << sub(64u64, t) == 0u64,
    ensures
        j <= t ==> bits_upto(m, base, j) == Seq::<u32>::empty() && bits_upto(
            m & m.wrapping_sub(1),
            base,
            j,
        ) == Seq::<u32>::empty(),
        j > t ==> bits_upto(m, base, j) == seq![(base + t) as u32] + bits_upto(
            m & m.wrapping_sub(1),
            base,
            j,
        ),
    decreases j,
{
    let m2 = m & m.wrapping_sub(1);
    if j > 0 {
        lemma_bits_lowest(m, base, t, j - 1);
        let q = (j - 1) as u64;
        lemma_clear_lowest_bit(m, t, q);
        if j - 1 > t {
            let a = bits_upto(m2, base, j - 1);
            assert(bits_upto(m, base, j - 1) == seq![(base + t) as u32] + a);
            if bit64(m, q) {
                assert(seq![(base + t) as u32] + a.push((base + j - 1) as u32) =~= (seq![(base
                    + t) as u32] + a).push((base + j - 1) as u32));
            }
        } else if j - 1 == t {
            assert(bits_upto(m, base, j) =~= seq![(base + t) as u32] + bits_upto(m2, base, j));
        }
    }
}

#[verifier::bit_vector]
proof fn lemma_clear_lowest_bv(m: u64, t: u64, q: u64)
    requires
        t < 64,
        q < 64,
        (m >> t) & 1u64 == 1u64,
        m << sub(64u64, t) == 0u64,
    ensures
        q < t ==> ((m & m.wrapping_sub(1u64)) >> q) & 1u64 == 0u64,
        q == t ==> ((m & m.wrapping_sub(1u64)) >> q) & 1u64 == 0u64,
        q > t ==> (((m & m.wrapping_sub(1u64)) >> q) & 1u64 == 1u64) == ((m >> q) & 1u64 == 1u64),
{
}

proof fn lemma_clear_lowest_bit(m: u64, t: u64, q: u64)
    requires
        t < 64,
        q < 64,
        bit64(m, t),
        m << sub(64u64, t) == 0u64,
    ensures
        q <= t ==> !bit64(m & m.wrapping_sub(1), q),
        q > t ==> bit64(m & m.wrapping_sub(1), q) == bit64(m, q),
{
    lemma_clear_lowest_bv(m, t, q);
}

/// The lowest set bit of a nonzero mask.
proof fn lemma_lowest(m: u64)
    requires
        m != 0,
    ensures
        ({
            let t = m.trailing_zeros() as u64;
            &&& t < 64
            &&& bit64(m, t)
            &&& forall|q: u64| q < t ==> !#[trigger] bit64(m, q)
            &&& m << sub(64u64, t) == 0u64
        }),
{
    vstd::std_specs::bits::axiom_u64_trailing_zeros(m);
    let t = m.trailing_zeros() as u64;
    assert forall|q: u64| q < t implies !#[trigger] bit64(m, q) by {
        assert((m >> q) & 1u64 == 0u64);
    }
}

/// Writes one position: `base + tz(m)` at `v[w]` (scratch when `m` is 0),
/// then clears the lowest bit of `m`.
#[inline(always)]
fn put_lowest(
    v: &mut Vec<u32>,
    w: usize,
    m: u64,
    base: u32,
) -> (r: u64)
    requires
        w < old(v)@.len(),
        base as int + 64 <= u32::MAX,
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|j: int| 0 <= j < old(v)@.len() && j != w ==> #[trigger] final(v)@[j] == old(v)@[j],
        m == 0 ==> r == 0,
        m != 0 ==> r == m & m.wrapping_sub(1) && bits_upto(m, base as int, 64) == seq![final(v)@[w as int]] + bits_upto(r, base as int, 64),
{
    // Through the barrier, LLVM keeps these stores scalar; it otherwise
    // gathers eight of them into a vector with slow lane inserts.
    let x = opaque64((base as u64) + (m.trailing_zeros() as u64));
    store_at(v, w, x as u32);
    proof {
        if m != 0 {
            lemma_lowest(m);
            lemma_bits_lowest(m, base as int, m.trailing_zeros() as u64, 64);
        } else {
            assert(0u64 & 0u64.wrapping_sub(1u64) == 0u64) by (bit_vector);
        }
    }
    m & m.wrapping_sub(1)
}

/// The bits of `m` in reverse order, by swapping halves at each width.
/// rustc compiles this to one `rbit` on AArch64.
pub open spec fn rev64s(m: u64) -> u64 {
    let a = ((m >> 1) & 0x5555_5555_5555_5555u64) | ((m & 0x5555_5555_5555_5555u64) << 1);
    let b = ((a >> 2) & 0x3333_3333_3333_3333u64) | ((a & 0x3333_3333_3333_3333u64) << 2);
    let c = ((b >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4);
    let d = ((c >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c & 0x00FF_00FF_00FF_00FFu64) << 8);
    let e = ((d >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d & 0x0000_FFFF_0000_FFFFu64) << 16);
    (e >> 32) | (e << 32)
}

#[inline(always)]
fn rev64(m: u64) -> (r: u64)
    ensures
        r == rev64s(m),
{
    let a = ((m >> 1) & 0x5555_5555_5555_5555u64) | ((m & 0x5555_5555_5555_5555u64) << 1);
    let b = ((a >> 2) & 0x3333_3333_3333_3333u64) | ((a & 0x3333_3333_3333_3333u64) << 2);
    let c = ((b >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4);
    let d = ((c >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c & 0x00FF_00FF_00FF_00FFu64) << 8);
    let e = ((d >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d & 0x0000_FFFF_0000_FFFFu64) << 16);
    (e >> 32) | (e << 32)
}

/// `r` is `rev64s(m)`, with the intermediate values named for the
/// bit-vector lemmas below.
spec fn rev_chain(m: u64, a: u64, b: u64, c: u64, d: u64, e: u64, r: u64) -> bool {
    &&& a == ((m >> 1) & 0x5555_5555_5555_5555u64) | ((m & 0x5555_5555_5555_5555u64) << 1)
    &&& b == ((a >> 2) & 0x3333_3333_3333_3333u64) | ((a & 0x3333_3333_3333_3333u64) << 2)
    &&& c == ((b >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4)
    &&& d == ((c >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c & 0x00FF_00FF_00FF_00FFu64) << 8)
    &&& e == ((d >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d & 0x0000_FFFF_0000_FFFFu64) << 16)
    &&& r == (e >> 32) | (e << 32)
}

#[verifier::bit_vector]
proof fn bv_rev_bit(m: u64, a: u64, b: u64, c: u64, d: u64, e: u64, r: u64, q: u64)
    requires
        a == ((m >> 1) & 0x5555_5555_5555_5555u64) | ((m & 0x5555_5555_5555_5555u64) << 1),
        b == ((a >> 2) & 0x3333_3333_3333_3333u64) | ((a & 0x3333_3333_3333_3333u64) << 2),
        c == ((b >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4),
        d == ((c >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c & 0x00FF_00FF_00FF_00FFu64) << 8),
        e == ((d >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d & 0x0000_FFFF_0000_FFFFu64) << 16),
        r == (e >> 32) | (e << 32),
        q < 64,
    ensures
        (r >> q) & 1u64 == (m >> sub(63u64, q)) & 1u64,
{
}

/// Bit `q` of the reversal is bit `63 - q`.
proof fn lemma_rev_bit(m: u64, q: u64)
    requires
        q < 64,
    ensures
        bit64(rev64s(m), q) == bit64(m, sub(63u64, q)),
{
    let a = ((m >> 1) & 0x5555_5555_5555_5555u64) | ((m & 0x5555_5555_5555_5555u64) << 1);
    let b = ((a >> 2) & 0x3333_3333_3333_3333u64) | ((a & 0x3333_3333_3333_3333u64) << 2);
    let c = ((b >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4);
    let d = ((c >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c & 0x00FF_00FF_00FF_00FFu64) << 8);
    let e = ((d >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d & 0x0000_FFFF_0000_FFFFu64) << 16);
    bv_rev_bit(m, a, b, c, d, e, rev64s(m), q);
}

/// Clearing the top set bit of the reversal is clearing the lowest set
/// bit of the mask. `r` and `r2` are the reversals of `m` and of `m`
/// without its lowest bit `t`.
#[verifier::bit_vector]
proof fn bv_rev_clear(
    m: u64, a: u64, b: u64, c: u64, d: u64, e: u64, r: u64,
    m2: u64, a2: u64, b2: u64, c2: u64, d2: u64, e2: u64, r2: u64,
    t: u64,
)
    requires
        a == ((m >> 1) & 0x5555_5555_5555_5555u64) | ((m & 0x5555_5555_5555_5555u64) << 1),
        b == ((a >> 2) & 0x3333_3333_3333_3333u64) | ((a & 0x3333_3333_3333_3333u64) << 2),
        c == ((b >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4),
        d == ((c >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c & 0x00FF_00FF_00FF_00FFu64) << 8),
        e == ((d >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d & 0x0000_FFFF_0000_FFFFu64) << 16),
        r == (e >> 32) | (e << 32),
        m2 == m & m.wrapping_sub(1u64),
        a2 == ((m2 >> 1) & 0x5555_5555_5555_5555u64) | ((m2 & 0x5555_5555_5555_5555u64) << 1),
        b2 == ((a2 >> 2) & 0x3333_3333_3333_3333u64) | ((a2 & 0x3333_3333_3333_3333u64) << 2),
        c2 == ((b2 >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b2 & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4),
        d2 == ((c2 >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c2 & 0x00FF_00FF_00FF_00FFu64) << 8),
        e2 == ((d2 >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d2 & 0x0000_FFFF_0000_FFFFu64) << 16),
        r2 == (e2 >> 32) | (e2 << 32),
        t < 64,
        (m >> t) & 1u64 == 1u64,
        m << sub(64u64, t) == 0u64,
    ensures
        r & !(0x8000_0000_0000_0000u64 >> (t & 63u64)) == r2,
{
}

proof fn lemma_rev_clear(m: u64, t: u64)
    requires
        t < 64,
        bit64(m, t),
        m << sub(64u64, t) == 0u64,
    ensures
        rev64s(m) & !(0x8000_0000_0000_0000u64 >> (t & 63u64)) == rev64s(m & m.wrapping_sub(1)),
{
    let a = ((m >> 1) & 0x5555_5555_5555_5555u64) | ((m & 0x5555_5555_5555_5555u64) << 1);
    let b = ((a >> 2) & 0x3333_3333_3333_3333u64) | ((a & 0x3333_3333_3333_3333u64) << 2);
    let c = ((b >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4);
    let d = ((c >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c & 0x00FF_00FF_00FF_00FFu64) << 8);
    let e = ((d >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d & 0x0000_FFFF_0000_FFFFu64) << 16);
    let m2 = m & m.wrapping_sub(1);
    let a2 = ((m2 >> 1) & 0x5555_5555_5555_5555u64) | ((m2 & 0x5555_5555_5555_5555u64) << 1);
    let b2 = ((a2 >> 2) & 0x3333_3333_3333_3333u64) | ((a2 & 0x3333_3333_3333_3333u64) << 2);
    let c2 = ((b2 >> 4) & 0x0F0F_0F0F_0F0F_0F0Fu64) | ((b2 & 0x0F0F_0F0F_0F0F_0F0Fu64) << 4);
    let d2 = ((c2 >> 8) & 0x00FF_00FF_00FF_00FFu64) | ((c2 & 0x00FF_00FF_00FF_00FFu64) << 8);
    let e2 = ((d2 >> 16) & 0x0000_FFFF_0000_FFFFu64) | ((d2 & 0x0000_FFFF_0000_FFFFu64) << 16);
    bv_rev_clear(m, a, b, c, d, e, rev64s(m), m2, a2, b2, c2, d2, e2, rev64s(m2), t);
}

/// `put_lowest` on the reversed mask `r` of `m`: the lowest set bit of `m`
/// is the top set bit of `r`, found with a leading-zero count and cleared
/// with one shift and one and-not. On AArch64 that is one instruction
/// fewer per write than a trailing-zero count (`rbit` and `clz`).
#[inline(always)]
fn put_top(
    v: &mut Vec<u32>,
    w: usize,
    r: u64,
    base: u32,
    Ghost(m): Ghost<u64>,
) -> (o: (u64, Ghost<u64>))
    requires
        w < old(v)@.len(),
        base as int + 64 <= u32::MAX,
        r == rev64s(m),
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|j: int| 0 <= j < old(v)@.len() && j != w ==> #[trigger] final(v)@[j] == old(v)@[j],
        o.0 == rev64s(o.1@),
        m == 0 ==> o.1@ == 0,
        m != 0 ==> o.1@ == m & m.wrapping_sub(1) && bits_upto(m, base as int, 64) == seq![final(v)@[w as int]] + bits_upto(o.1@, base as int, 64),
{
    let lz = r.leading_zeros();
    proof {
        vstd::std_specs::bits::axiom_u64_leading_zeros(r);
    }
    store_at(v, w, base + lz);
    let sh = (lz as u64) & 63;
    proof {
        assert(sh < 64) by (bit_vector)
            requires
                sh == (lz as u64) & 63,
        ;
    }
    let r2 = r & !(0x8000_0000_0000_0000u64 >> sh);
    proof {
        if m != 0 {
            lemma_lowest(m);
            let t = m.trailing_zeros() as u64;
            lemma_rev_bit(m, sub(63u64, t));
            assert(sub(63u64, sub(63u64, t)) == t);
            assert(bit64(r, sub(63u64, t)));
            assert(r != 0) by {
                if r == 0 {
                    lemma_zero_bits(sub(63u64, t));
                }
            }
            let l = lz as u64;
            assert(l < 64);
            let x = r >> sub(63u64, l);
            assert(x & 1u64 == 1u64) by (bit_vector)
                requires
                    x & 1u64 != 0u64,
            ;
            lemma_rev_bit(m, sub(63u64, l));
            assert(sub(63u64, sub(63u64, l)) == l);
            assert(bit64(m, l));
            assert(l >= t);
            if l > t {
                let j = sub(63u64, t);
                assert(64 - l <= j < 64);
                assert((r >> j) & 1u64 == 0u64);
                assert(false);
            }
            assert(l == t);
            lemma_rev_clear(m, t);
            lemma_bits_lowest(m, base as int, t, 64);
        } else {
            assert(rev64s(0u64) == 0u64) by (compute);
            assert(0u64 & !(0x8000_0000_0000_0000u64 >> (64u64 & 63u64)) == 0u64) by (bit_vector);
        }
    }
    (r2, Ghost(if m == 0 { 0u64 } else { m & m.wrapping_sub(1) }))
}

/// One group of four writes of `append_bits`, from `p`, with `q` and
/// `mm` as in its loop.
// `w` and `m` appear only in the specification.
#[allow(unused_variables)]
#[inline(always)]
fn put4_bits(
    v: &mut Vec<u32>,
    w: usize,
    m: u64,
    base: u32,
    p: usize,
    mm: u64,
    _n: usize,
    Ghost(v0): Ghost<Seq<u32>>,
    Ghost(all): Ghost<Seq<u32>>,
    Ghost(q): Ghost<int>,
) -> (r: (usize, u64, Ghost<int>))
    requires
        old(v)@.len() == v0.len(),
        _n == v0.len(),
        w + 64 <= v0.len(),
        base as int + 64 <= u32::MAX,
        all == bits_upto(m, base as int, 64),
        all.len() <= 64,
        w <= p,
        (p - w) % 4 == 0,
        w <= q <= p,
        mm != 0 ==> p as int == q,
        mm == 0 ==> q == w + all.len(),
        q - w + bits_upto(mm, base as int, 64).len() == all.len(),
        old(v)@.subrange(0, w as int) == v0.subrange(0, w as int),
        old(v)@.subrange(w as int, q) == all.subrange(0, q - w),
        all.subrange(q - w, all.len() as int) == bits_upto(mm, base as int, 64),
        p + 4 <= w + 64,
    ensures
        final(v)@.len() == v0.len(),
        w <= r.0,
        (r.0 - w) % 4 == 0,
        w <= r.2@ <= r.0,
        r.1 != 0 ==> r.0 as int == r.2@,
        r.1 == 0 ==> r.2@ == w + all.len(),
        r.2@ - w + bits_upto(r.1, base as int, 64).len() == all.len(),
        final(v)@.subrange(0, w as int) == v0.subrange(0, w as int),
        final(v)@.subrange(w as int, r.2@) == all.subrange(0, r.2@ - w),
        all.subrange(r.2@ - w, all.len() as int) == bits_upto(r.1, base as int, 64),
        r.0 == p + 4,
        mm != 0 ==> bits_upto(r.1, base as int, 64).len() < bits_upto(mm, base as int, 64).len(),
{
    let mut p = p;
    let mut mm = mm;
    let ghost mut q = q;
    let ghost p0 = p;
    let ghost mm0 = mm;
    proof {
        if mm != 0 {
            lemma_lowest(mm);
            lemma_bits_lowest(mm, base as int, mm.trailing_zeros() as u64, 64);
        } else {
            lemma_zero_upto(base as int, 64);
        }
    }
    let mut t: usize = 0;
    while t < 4
        invariant
            v@.len() == v0.len(),
            _n == v0.len(),
            w + 64 <= v0.len(),
            base as int + 64 <= u32::MAX,
            all == bits_upto(m, base as int, 64),
            all.len() <= 64,
            p0 + 4 <= w + 64,
            t <= 4,
            p == p0 + t,
            w <= q <= p,
            mm != 0 ==> p as int == q,
            mm == 0 ==> q == w + all.len(),
            q - w + bits_upto(mm, base as int, 64).len() == all.len(),
            v@.subrange(0, w as int) == v0.subrange(0, w as int),
            v@.subrange(w as int, q) == all.subrange(0, q - w),
            all.subrange(q - w, all.len() as int) == bits_upto(mm, base as int, 64),
            t == 0 ==> mm == mm0,
            t > 0 && mm0 != 0 ==> bits_upto(mm, base as int, 64).len() < bits_upto(mm0, base as int, 64).len(),
        decreases 4 - t,
    {
        let ghost vb = v@;
        let ghost mb = mm;
        if mm != 0 {
            proof {
                lemma_lowest(mm);
                lemma_bits_lowest(mm, base as int, mm.trailing_zeros() as u64, 64);
            }
        } else {
            proof {
                lemma_zero_upto(base as int, 64);
            }
        }
        mm = put_lowest(v, p, mm, base);
        proof {
            assert(v@.subrange(0, w as int) =~= vb.subrange(0, w as int));
            if mb != 0 {
                assert(v@.subrange(w as int, p + 1) =~= all.subrange(0, p + 1 - w)) by {
                    assert(all.subrange(p - w, all.len() as int)[0] == v@[p as int]);
                    assert forall|j: int| w <= j < p + 1 implies v@[j] == all[j - w] by {
                        if j < p {
                            assert(vb.subrange(w as int, p as int)[j - w] == all.subrange(0, p - w)[j - w]);
                        }
                    }
                }
                assert(all.subrange(p + 1 - w, all.len() as int) =~= all.subrange(p - w, all.len() as int).subrange(1, all.len() - (p - w)));
                q = p + 1;
                if mm == 0 {
                    lemma_zero_upto(base as int, 64);
                }
            } else {
                assert(v@.subrange(w as int, q) =~= vb.subrange(w as int, q));
            }
        }
        p = p + 1;
        t = t + 1;
    }
    proof {
        if mm == 0 {
            lemma_zero_upto(base as int, 64);
        }
    }
    (p, mm, Ghost(q))
}

/// `put4_bits` for the reversed mask `rv` of `append_bits`'s NEON path:
/// `mm`, the bits still to write, is ghost here.
// `w` and `m` appear only in the specification.
#[allow(unused_variables)]
#[inline(always)]
fn put_rev(
    v: &mut Vec<u32>,
    w: usize,
    m: u64,
    base: u32,
    p: usize,
    rv: u64,
    Ghost(mm): Ghost<u64>,
    _n: usize,
    Ghost(v0): Ghost<Seq<u32>>,
    Ghost(all): Ghost<Seq<u32>>,
    Ghost(q): Ghost<int>,
    n: usize,
) -> (r: (usize, u64, Ghost<int>, Ghost<u64>))
    requires
        rv == rev64s(mm),
        old(v)@.len() == v0.len(),
        _n == v0.len(),
        w + 64 <= v0.len(),
        base as int + 64 <= u32::MAX,
        all == bits_upto(m, base as int, 64),
        all.len() <= 64,
        w <= p,
        w <= q <= p,
        mm != 0 ==> p as int == q,
        mm == 0 ==> q == w + all.len(),
        q - w + bits_upto(mm, base as int, 64).len() == all.len(),
        old(v)@.subrange(0, w as int) == v0.subrange(0, w as int),
        old(v)@.subrange(w as int, q) == all.subrange(0, q - w),
        all.subrange(q - w, all.len() as int) == bits_upto(mm, base as int, 64),
        1 <= n,
        p + n <= w + 64,
    ensures
        r.1 == rev64s(r.3@),
        final(v)@.len() == v0.len(),
        w <= r.0,
        w <= r.2@ <= r.0,
        r.3@ != 0 ==> r.0 as int == r.2@,
        r.3@ == 0 ==> r.2@ == w + all.len(),
        r.2@ - w + bits_upto(r.3@, base as int, 64).len() == all.len(),
        final(v)@.subrange(0, w as int) == v0.subrange(0, w as int),
        final(v)@.subrange(w as int, r.2@) == all.subrange(0, r.2@ - w),
        all.subrange(r.2@ - w, all.len() as int) == bits_upto(r.3@, base as int, 64),
        r.0 == p + n,
        mm != 0 ==> bits_upto(r.3@, base as int, 64).len() < bits_upto(mm, base as int, 64).len(),
{
    let mut p = p;
    let mut rv = rv;
    let ghost mut mm = mm;
    let ghost mut q = q;
    let ghost p0 = p;
    let ghost mm0 = mm;
    proof {
        if mm != 0 {
            lemma_lowest(mm);
            lemma_bits_lowest(mm, base as int, mm.trailing_zeros() as u64, 64);
        } else {
            lemma_zero_upto(base as int, 64);
        }
    }
    let mut t: usize = 0;
    while t < n
        invariant
            rv == rev64s(mm),
            v@.len() == v0.len(),
            _n == v0.len(),
            w + 64 <= v0.len(),
            base as int + 64 <= u32::MAX,
            all == bits_upto(m, base as int, 64),
            all.len() <= 64,
            p0 + n <= w + 64,
            t <= n,
            p == p0 + t,
            w <= q <= p,
            mm != 0 ==> p as int == q,
            mm == 0 ==> q == w + all.len(),
            q - w + bits_upto(mm, base as int, 64).len() == all.len(),
            v@.subrange(0, w as int) == v0.subrange(0, w as int),
            v@.subrange(w as int, q) == all.subrange(0, q - w),
            all.subrange(q - w, all.len() as int) == bits_upto(mm, base as int, 64),
            t == 0 ==> mm == mm0,
            t > 0 && mm0 != 0 ==> bits_upto(mm, base as int, 64).len() < bits_upto(mm0, base as int, 64).len(),
        decreases n - t,
    {
        let ghost vb = v@;
        let ghost mb = mm;
        proof {
            if mm != 0 {
                lemma_lowest(mm);
                lemma_bits_lowest(mm, base as int, mm.trailing_zeros() as u64, 64);
            } else {
                lemma_zero_upto(base as int, 64);
            }
        }
        let (rv1, Ghost(mm1)) = put_top(v, p, rv, base, Ghost(mm));
        rv = rv1;
        proof {
            mm = mm1;
        }
        proof {
            assert(v@.subrange(0, w as int) =~= vb.subrange(0, w as int));
            if mb != 0 {
                assert(v@.subrange(w as int, p + 1) =~= all.subrange(0, p + 1 - w)) by {
                    assert(all.subrange(p - w, all.len() as int)[0] == v@[p as int]);
                    assert forall|j: int| w <= j < p + 1 implies v@[j] == all[j - w] by {
                        if j < p {
                            assert(vb.subrange(w as int, p as int)[j - w] == all.subrange(0, p - w)[j - w]);
                        }
                    }
                }
                assert(all.subrange(p + 1 - w, all.len() as int) =~= all.subrange(p - w, all.len() as int).subrange(1, all.len() - (p - w)));
                q = p + 1;
                if mm == 0 {
                    lemma_zero_upto(base as int, 64);
                }
            } else {
                assert(v@.subrange(w as int, q) =~= vb.subrange(w as int, q));
            }
        }
        p = p + 1;
        t = t + 1;
    }
    proof {
        if mm == 0 {
            lemma_zero_upto(base as int, 64);
        }
    }
    (p, rv, Ghost(q), Ghost(mm))
}

/// Writes the positions `base + k` of the set bits of `m` to
/// `v[w..]`, in order, and returns the new end. It may write scratch
/// values up to `v[w + 64]`.
#[inline(always)]
pub fn append_bits<const K: u8>(v: &mut Vec<u32>, w: usize, m: u64, base: u32) -> (r: usize)
    requires
        kernel_cpu(K),
        w + 64 <= old(v)@.len(),
        base as int + 64 <= u32::MAX,
    ensures
        final(v)@.len() == old(v)@.len(),
        r == w + bits_upto(m, base as int, 64).len(),
        r <= w + 64,
        final(v)@.subrange(0, w as int) == old(v)@.subrange(0, w as int),
        final(v)@.subrange(w as int, r as int) == bits_upto(m, base as int, 64),
{
    #[cfg(target_arch = "x86_64")]
    {
        if K == AVX512 {
            return append_bits_avx512(v, w, m, base);
        }
    }
    let ghost v0 = v@;
    let ghost all = bits_upto(m, base as int, 64);
    let _n = v.len();
    let cnt = popcnt64(m) as usize;
    let mut mm = m;
    let mut p = w;
    // `q` is the end of the real entries; past it, up to `p`, is scratch.
    let ghost mut q = w as int;
    proof {
        lemma_bits_base(m, base as int, 64);
        lemma_bits_base(m, 0, 64);
        lemma_bits_len(m, base as int, 64);
        assert(v@.subrange(w as int, w as int) =~= all.subrange(0, 0));
        assert(all.subrange(0, all.len() as int) =~= all);
        if m == 0 {
            lemma_zero_upto(base as int, 64);
        }
    }
    proof {
        assert(cnt == all.len());
    }
    if verilith_simd::neon::has_neon() {
        // From the reversed mask: six, then two at a time while any are
        // left. Writes past the last bit are scratch.
        let mut rv = rev64(m);
        let ghost mut gm = m;
        if cnt > 0 {
            let (p1, rv1, Ghost(q1), Ghost(gm1)) = put_rev(v, w, m, base, p, rv, Ghost(gm), _n, Ghost(v0), Ghost(all), Ghost(q), 6);
            p = p1;
            rv = rv1;
            proof {
                q = q1;
                gm = gm1;
            }
            while p - w < cnt
                invariant
                    rv == rev64s(gm),
                    cnt == all.len(),
                    v@.len() == v0.len(),
                    _n == v0.len(),
                    w + 64 <= v0.len(),
                    base as int + 64 <= u32::MAX,
                    all == bits_upto(m, base as int, 64),
                    all.len() <= 64,
                    w <= p,
                    (p - w) % 2 == 0,
                    w <= q <= p,
                    gm != 0 ==> p as int == q,
                    gm == 0 ==> q == w + all.len(),
                    q - w + bits_upto(gm, base as int, 64).len() == all.len(),
                    v@.subrange(0, w as int) == v0.subrange(0, w as int),
                    v@.subrange(w as int, q) == all.subrange(0, q - w),
                    all.subrange(q - w, all.len() as int) == bits_upto(gm, base as int, 64),
                decreases bits_upto(gm, base as int, 64).len(),
            {
                let (p1, rv1, Ghost(q1), Ghost(gm1)) = put_rev(v, w, m, base, p, rv, Ghost(gm), _n, Ghost(v0), Ghost(all), Ghost(q), 2);
                p = p1;
                rv = rv1;
                proof {
                    q = q1;
                    gm = gm1;
                }
            }
        }
        proof {
            lemma_zero_upto(base as int, 64);
            assert(q == w + cnt);
        }
        return w + cnt;
    }
    // Eight at a time, without testing for the last bit; writes past it
    // are scratch. Each group is decided by the count, known early,
    // rather than by the mask the writes update. Fewer, coarser branches
    // mispredict less often than one per four writes.
    if cnt > 0 {
        let (p1, mm1, Ghost(q1)) = put4_bits(v, w, m, base, p, mm, _n, Ghost(v0), Ghost(all), Ghost(q));
        p = p1;
        mm = mm1;
        proof {
            q = q1;
        }
        let (p1, mm1, Ghost(q1)) = put4_bits(v, w, m, base, p, mm, _n, Ghost(v0), Ghost(all), Ghost(q));
        p = p1;
        mm = mm1;
        proof {
            q = q1;
        }
        if cnt > 8 {
            let (p1, mm1, Ghost(q1)) = put4_bits(v, w, m, base, p, mm, _n, Ghost(v0), Ghost(all), Ghost(q));
            p = p1;
            mm = mm1;
            proof {
                q = q1;
            }
            let (p1, mm1, Ghost(q1)) = put4_bits(v, w, m, base, p, mm, _n, Ghost(v0), Ghost(all), Ghost(q));
            p = p1;
            mm = mm1;
            proof {
                q = q1;
            }
            while p - w < cnt
                invariant
                    cnt == all.len(),
                    v@.len() == v0.len(),
                    _n == v0.len(),
                    w + 64 <= v0.len(),
                    base as int + 64 <= u32::MAX,
                    all == bits_upto(m, base as int, 64),
                    all.len() <= 64,
                    w <= p,
                    (p - w) % 4 == 0,
                    w <= q <= p,
                    mm != 0 ==> p as int == q,
                    mm == 0 ==> q == w + all.len(),
                    q - w + bits_upto(mm, base as int, 64).len() == all.len(),
                    v@.subrange(0, w as int) == v0.subrange(0, w as int),
                    v@.subrange(w as int, q) == all.subrange(0, q - w),
                    all.subrange(q - w, all.len() as int) == bits_upto(mm, base as int, 64),
                decreases bits_upto(mm, base as int, 64).len(),
            {
                let (p1, mm1, Ghost(q1)) = put4_bits(v, w, m, base, p, mm, _n, Ghost(v0), Ghost(all), Ghost(q));
                p = p1;
                mm = mm1;
                proof {
                    q = q1;
                }
            }
        }
    }
    proof {
        lemma_zero_upto(base as int, 64);
        assert(cnt == all.len());
    }
    w + cnt
}

/// At most one position per bit.
pub proof fn lemma_bits_len(m: u64, base: int, j: int)
    requires
        0 <= j,
    ensures
        bits_upto(m, base, j).len() <= j,
    decreases j,
{
    if j > 0 {
        lemma_bits_len(m, base, j - 1);
    }
}

pub proof fn lemma_zero_upto(base: int, j: int)
    requires
        0 <= j <= 64,
    ensures
        bits_upto(0, base, j) == Seq::<u32>::empty(),
    decreases j,
{
    if j > 0 {
        lemma_zero_upto(base, j - 1);
        lemma_zero_bits((j - 1) as u64);
    }
}

/// Widens 16 lane indices to dwords, adds `base`, and stores them at
/// `v[at..at + 16]`.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn put16(v: &mut Vec<u32>, at: usize, e: __m128i, base: u32)
    requires
        avx512bw(),
        at + 16 <= old(v)@.len(),
        b16(e).len() == 16,
        forall|l: int| 0 <= l < 16 ==> #[trigger] b16(e)[l] < 64,
        base as int + 64 <= u32::MAX,
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|j: int|
            0 <= j < old(v)@.len() ==> #[trigger] final(v)@[j] == if at <= j < at + 16 {
                (b16(e)[j - at] + base) as u32
            } else {
                old(v)@[j]
            },
{
    let q = add_d16(widen16(e), base);
    store_d16(v, at, q);
}

/// `append_bits` with VBMI2: compress the lane indices of the set bits,
/// then widen, offset and store them 16 at a time.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn append_bits_avx512(v: &mut Vec<u32>, w: usize, m: u64, base: u32) -> (r: usize)
    requires
        avx512vbmi2(),
        w + 64 <= old(v)@.len(),
        base as int + 64 <= u32::MAX,
    ensures
        final(v)@.len() == old(v)@.len(),
        r == w + bits_upto(m, base as int, 64).len(),
        r <= w + 64,
        final(v)@.subrange(0, w as int) == old(v)@.subrange(0, w as int),
        final(v)@.subrange(w as int, r as int) == bits_upto(m, base as int, 64),
{
    proof {
        broadcast use verilith_simd::cpu::axiom_avx512_implications;
    }
    let ghost v0 = v@;
    let ghost all = bits_upto(m, base as int, 64);
    let ghost sb = bits_upto(m, 0, 64);
    let _n = v.len();
    let cnt = popcnt64(m) as usize;
    let ids = iota64();
    let packed = compress64(m, ids);
    proof {
        lemma_bits_base(m, base as int, 64);
        lemma_bits_base(m, 0, 64);
        lemma_bits_len(m, 0, 64);
        assert forall|j: int| 0 <= j < 64 implies #[trigger] b64(packed)[j] < 64 && (j < cnt ==> b64(packed)[j] == sb[j] as u8) by {
            if j < cnt {
                assert(b64(packed)[j] == b64(ids)[sb[j] as int]);
            }
        }
    }
    let e0 = extract128(packed, 0);
    let e1 = extract128(packed, 1);
    let e2 = extract128(packed, 2);
    let e3 = extract128(packed, 3);
    proof {
        assert forall|l: int| 0 <= l < 16 implies #[trigger] b16(e0)[l] < 64 && b16(e1)[l] < 64 && b16(e2)[l] < 64 && b16(e3)[l] < 64 by {
            assert(b16(e0)[l] == b64(packed)[l]);
            assert(b16(e1)[l] == b64(packed)[16 + l]);
            assert(b16(e2)[l] == b64(packed)[32 + l]);
            assert(b16(e3)[l] == b64(packed)[48 + l]);
        }
    }
    put16(v, w, e0, base);
    if cnt > 16 {
        put16(v, w + 16, e1, base);
        if cnt > 32 {
            put16(v, w + 32, e2, base);
            put16(v, w + 48, e3, base);
        }
    }
    proof {
        assert forall|j: int| 0 <= j < cnt implies #[trigger] v@[w + j] == all[j] by {
            assert(all[j] == sb[j] + base);
            let n = j / 16;
            let l = j % 16;
            if n == 0 {
                assert(b16(e0)[l] == b64(packed)[j]);
            } else if n == 1 {
                assert(b16(e1)[l] == b64(packed)[j]);
            } else if n == 2 {
                assert(b16(e2)[l] == b64(packed)[j]);
            } else {
                assert(b16(e3)[l] == b64(packed)[j]);
            }
        }
        assert(v@.subrange(0, w as int) =~= v0.subrange(0, w as int));
        assert(v@.subrange(w as int, (w + cnt) as int) =~= all) by {
            assert forall|j: int| 0 <= j < cnt implies v@.subrange(w as int, (w + cnt) as int)[j] == all[j] by {
                assert(v@[w + j] == all[j]);
            }
        }
    }
    w + cnt
}

// ---------------------------------------------------------------------------
// 16-byte classification (SSE2)
// ---------------------------------------------------------------------------

#[verifier::bit_vector]
proof fn lemma_low16(a: u32, k: u32)
    requires
        k < 16,
    ensures
        (((!a) & 0xFFFFu32) >> k) & 1u32 == 1u32 <==> !((a >> k) & 1u32 == 1u32),
        (!a) & 0xFFFFu32 < 0x10000u32,
{
}

#[verifier::bit_vector]
proof fn lemma_digit_test(c: u8)
    ensures
        ((if c.wrapping_sub(0x30u8) <= 9u8 { c.wrapping_sub(0x30u8) } else { 9u8 }) == c.wrapping_sub(
            0x30u8,
        )) == (0x30u8 <= c && c <= 0x39u8),
{
}

/// Bit `k` is set exactly when `s[i + k]` is not plain string content.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn classify_special(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !plain(s@[i + k])),
{
    let v = load16(s, i);
    let q = eq16(v, splat16(0x22));
    let b = eq16(v, splat16(0x5C));
    // Unsigned v <= 0x1F.
    let k1f = splat16(0x1F);
    let c = eq16(max16(v, k1f), k1f);
    let qb = or16(q, b);
    let all = or16(qb, c);
    let m = movemask16(all);
    proof {
        assert forall|k: u32| k < 16 implies (#[trigger] bit(m, k) <==> !plain(s@[i + k])) by {
            let j = k as int;
            assert(b16(v)[j] == s@[i + k]);
            lemma_top_or(b16(q)[j], b16(b)[j]);
            lemma_top_or(b16(qb)[j], b16(c)[j]);
        }
    }
    m
}

/// Bit `k` is set exactly when `s[i + k]` is not JSON whitespace.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn classify_non_ws(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !is_ws(s@[i + k])),
{
    let v = load16(s, i);
    let sp = eq16(v, splat16(0x20));
    let nl = eq16(v, splat16(0x0A));
    let cr = eq16(v, splat16(0x0D));
    let tb = eq16(v, splat16(0x09));
    let a = or16(sp, nl);
    let b = or16(cr, tb);
    let ws = or16(a, b);
    let w = movemask16(ws);
    let m = (!w) & 0xFFFF;
    proof {
        assert forall|k: u32| k < 16 implies (#[trigger] bit(m, k) <==> !is_ws(s@[i + k])) by {
            let j = k as int;
            assert(b16(v)[j] == s@[i + k]);
            lemma_top_or(b16(sp)[j], b16(nl)[j]);
            lemma_top_or(b16(cr)[j], b16(tb)[j]);
            lemma_top_or(b16(a)[j], b16(b)[j]);
            lemma_low16(w, k);
            assert(bit(w, k) == (b16(ws)[j] >= 0x80));
        }
        lemma_low16(w, 0);
    }
    m
}

/// Bit `k` is set exactly when `s[i + k]` is not an ASCII digit.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn classify_non_digit(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !is_digit_byte(s@[i + k])),
{
    let v = load16(s, i);
    // Unsigned (v - '0') <= 9.
    let d = sub16(v, splat16(0x30));
    let isd = eq16(min16(d, splat16(9)), d);
    let w = movemask16(isd);
    let m = (!w) & 0xFFFF;
    proof {
        assert forall|k: u32| k < 16 implies (#[trigger] bit(m, k) <==> !is_digit_byte(s@[i + k])) by {
            let j = k as int;
            assert(b16(v)[j] == s@[i + k]);
            lemma_digit_test(s@[i + k]);
            lemma_low16(w, k);
            assert(bit(w, k) == (b16(isd)[j] >= 0x80));
        }
        lemma_low16(w, 0);
    }
    m
}

#[verifier::bit_vector]
proof fn bv_split64(x: u64)
    ensures
        x == (x >> 32u64) * 0x1_0000_0000 + (x & 0xFFFF_FFFF),
        (x & 0xFFFF_FFFF) <= 0xFFFF_FFFF,
{
}

proof fn lemma_p10_2p5(k: nat)
    ensures
        p10i(k) == p5i(k) * vstd::arithmetic::power2::pow2(k) as int,
        p5i(k) > 0,
    decreases k,
{
    if k > 0 {
        lemma_p10_2p5((k - 1) as nat);
        vstd::arithmetic::power2::lemma_pow2_unfold(k);
        assert(p5i(k) * vstd::arithmetic::power2::pow2(k) == 5 * p5i((k - 1) as nat) * (2 * vstd::arithmetic::power2::pow2((k - 1) as nat))) ;
        assert(5 * p5i((k - 1) as nat) * (2 * vstd::arithmetic::power2::pow2((k - 1) as nat)) == 10 * (p5i((k - 1) as nat) * vstd::arithmetic::power2::pow2((k - 1) as nat))) by (nonlinear_arith);
    } else {
        vstd::arithmetic::power2::lemma2_to64();
    }
}

/// The value of the eight digit lanes `v[i..i + 8]`, grouped as
/// `pmaddwd` combines them.
pub open spec fn g8v(v: Seq<u8>, i: int) -> int {
    ((v[i] as int * 10 + v[i + 1] as int) * 100 + v[i + 2] as int * 10 + v[i + 3] as int) * 10000
        + (v[i + 4] as int * 10 + v[i + 5] as int) * 100 + v[i + 6] as int * 10 + v[i + 7] as int
}

pub open spec fn g4v(v: Seq<u8>, i: int) -> int {
    (v[i] as int * 10 + v[i + 1] as int) * 100 + v[i + 2] as int * 10 + v[i + 3] as int
}

#[cfg(target_arch = "x86_64")]
#[verifier::spinoff_prover]
#[inline(always)]
fn pairs16(e: __m128i) -> (r: __m128i)
    requires
        b16(e).len() == 16,
        forall|k: int| 0 <= k < 16 ==> b16(e)[k] <= 9,
    ensures
        forall|j: int| 0 <= j < 8 ==> w16(r)[j] as int == b16(e)[2 * j] as int * 10 + b16(e)[2 * j + 1] as int,
{
    let w2 = pair16(10, 1);
    let wl = widen_lo16(e);
    let wh = widen_hi16(e);
    let lo = madd16(wl, w2);
    let hi = madd16(wh, w2);
    let ghost ev = b16(e);
    proof {
        assert forall|j: int| 0 <= j < 4 implies w32(lo)[j] as int == ev[2 * j] as int * 10 + ev[2 * j + 1] as int by {
            assert(w16(wl)[2 * j] as int == ev[2 * j] as int);
            assert(w16(wl)[2 * j + 1] as int == ev[2 * j + 1] as int);
            assert(w16(w2)[2 * j] == 10i16);
            assert(w16(w2)[2 * j + 1] == 1i16);
        }
        assert forall|j: int| 0 <= j < 4 implies w32(hi)[j] as int == ev[8 + 2 * j] as int * 10 + ev[8 + 2 * j + 1] as int by {
            assert(w16(wh)[2 * j] as int == ev[2 * j + 8] as int);
            assert(w16(wh)[2 * j + 1] as int == ev[2 * j + 1 + 8] as int);
            assert(w16(w2)[2 * j] == 10i16);
            assert(w16(w2)[2 * j + 1] == 1i16);
        }
    }
    let p2 = packs16(lo, hi);
    proof {
        assert forall|j: int| 0 <= j < 8 implies w16(p2)[j] as int == ev[2 * j] as int * 10 + ev[2 * j + 1] as int by {
            if j < 4 {
                assert(w32(lo)[j] as int == ev[2 * j] as int * 10 + ev[2 * j + 1] as int);
            } else {
                assert(w32(hi)[j - 4] as int == ev[8 + 2 * (j - 4)] as int * 10 + ev[8 + 2 * (j - 4) + 1] as int);
            }
        }
    }
    p2
}

#[cfg(target_arch = "x86_64")]
#[verifier::spinoff_prover]
#[inline(always)]
fn quads16(e: __m128i) -> (r: __m128i)
    requires
        b16(e).len() == 16,
        forall|k: int| 0 <= k < 16 ==> b16(e)[k] <= 9,
    ensures
        forall|j: int| 0 <= j < 4 ==> w16(r)[j] as int == g4v(b16(e), 4 * j),
{
    let ghost ev = b16(e);
    let p2 = pairs16(e);
    let w4 = pair16(100, 1);
    let g4 = madd16(p2, w4);
    proof {
        assert forall|j: int| 0 <= j < 4 implies w32(g4)[j] as int == g4v(ev, 4 * j) by {
            assert(w16(p2)[2 * j] as int == ev[2 * (2 * j)] as int * 10 + ev[2 * (2 * j) + 1] as int);
            assert(w16(p2)[2 * j + 1] as int == ev[2 * (2 * j + 1)] as int * 10 + ev[2 * (2 * j + 1) + 1] as int);
            assert(w16(w4)[2 * j] == 100i16);
            assert(w16(w4)[2 * j + 1] == 1i16);
        }
    }
    let p4 = packs16(g4, g4);
    proof {
        assert forall|j: int| 0 <= j < 4 implies w16(p4)[j] as int == g4v(ev, 4 * j) by {
            assert(w32(g4)[j] as int == g4v(ev, 4 * j));
        }
    }
    p4
}

/// The two eight-digit halves of 16 digit lanes, as the low and high
/// dwords of a u64.
#[cfg(target_arch = "x86_64")]
#[verifier::spinoff_prover]
#[inline(always)]
fn halves16(e: __m128i) -> (x: u64)
    requires
        b16(e).len() == 16,
        forall|k: int| 0 <= k < 16 ==> b16(e)[k] <= 9,
    ensures
        x as int == g8v(b16(e), 0) + g8v(b16(e), 8) * 0x1_0000_0000,
{
    let ghost ev = b16(e);
    let p4 = quads16(e);
    let w8 = pair16(10000, 1);
    let g8 = madd16(p4, w8);
    proof {
        assert(w16(w8)[0] == 10000i16 && w16(w8)[1] == 1i16 && w16(w8)[2] == 10000i16 && w16(w8)[3] == 1i16);
        assert(w16(p4)[0] as int == g4v(ev, 0));
        assert(w16(p4)[1] as int == g4v(ev, 4));
        assert(w16(p4)[2] as int == g4v(ev, 8));
        assert(w16(p4)[3] as int == g4v(ev, 12));
        assert(g8v(ev, 0) == g4v(ev, 0) * 10000 + g4v(ev, 4));
        assert(g8v(ev, 8) == g4v(ev, 8) * 10000 + g4v(ev, 12));
        assert(w32(g8)[0] == (w16(p4)[0] * w16(w8)[0] + w16(p4)[1] * w16(w8)[1]) as i32);
        assert(w32(g8)[1] == (w16(p4)[2] * w16(w8)[2] + w16(p4)[3] * w16(w8)[3]) as i32);
        assert(w32(g8)[0] as int == g8v(ev, 0));
        assert(w32(g8)[1] as int == g8v(ev, 8));
    }
    low64(g8)
}

pub proof fn lemma_dlanes16(v: Seq<u8>)
    ensures
        dlanes(v, 16) == g8v(v, 0) * 100_000_000 + g8v(v, 8),
{
    reveal_with_fuel(dlanes, 17);
}

/// `v = D * 10^k`, with `D < 10^16`: shifting out `2^k` and multiplying by
/// the inverse of `5^k` gives `D`.
#[verifier::spinoff_prover]
proof fn lemma_unscale(v: u64, dd: int, k: nat)
    requires
        k <= 16,
        0 <= dd < 10_000_000_000_000_000,
        v as int == dd * p10i(k),
    ensures
        (v >> k as u64).wrapping_mul(INV5@[k as int]) as int == dd,
{
    lemma_p10_2p5(k);
    vstd::bits::lemma_u64_shr_is_div(v, k as u64);
    lemma_inv5(k);
    let p5 = p5i(k);
    let t2 = vstd::arithmetic::power2::pow2(k) as int;
    vstd::arithmetic::power2::lemma_pow2_pos(k);
    assert(v as int == t2 * (dd * p5)) by (nonlinear_arith)
        requires v as int == dd * p10i(k), p10i(k) == p5 * t2;
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(dd * p5, t2);
    let h = v >> k as u64;
    assert(h as int == dd * p5);
    let m = 0x1_0000_0000_0000_0000int;
    let i5 = INV5@[k as int] as int;
    assert(h.wrapping_mul(INV5@[k as int]) as int == (h as int * i5) % m);
    assert(h as int * i5 == dd * (i5 * p5)) by (nonlinear_arith)
        requires h as int == dd * p5;
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(dd, i5 * p5, m);
    vstd::arithmetic::div_mod::lemma_small_mod(dd as nat, m as nat);
}

#[verifier::bit_vector]
proof fn bv_and_mask(x: u8, m: u8)
    requires
        m == 0xFF || m == 0,
    ensures
        x & m == (if m == 0xFF { x } else { 0 }),
{
}

/// The value of the first `n` lanes of `d`, which hold digit values (0 to
/// 9), most significant first. The lanes are masked to the first `n` and
/// combined pairwise with `pmaddwd` (to 2, 4 and then 8 digits), giving
/// the 16-digit value of the digits followed by `16 - n` zeros; dividing
/// out `10^(16 - n)` is exact, so it is a shift by `16 - n` and a multiply
/// by the inverse of `5^(16 - n)` modulo 2^64.
#[cfg(target_arch = "x86_64")]
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
#[inline(always)]
pub fn digits_value16(d: __m128i, n: usize) -> (r: u64)
    requires
        n <= 16,
        b16(d).len() == 16,
        forall|k: int| 0 <= k < n ==> b16(d)[k] <= 9,
    ensures
        r as int == dlanes(b16(d), n as int),
{
    let mk = mask_first16(n);
    let e = and16(d, mk);
    let ghost ev = b16(e);
    proof {
        assert forall|k: int| 0 <= k < 16 implies ev[k] == (if k < n { b16(d)[k] } else { 0u8 }) by {
            bv_and_mask(b16(d)[k], b16(mk)[k]);
        }
    }
    let x = halves16(e);
    proof {
        bv_split64(x);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x as int, 0x1_0000_0000, g8v(ev, 8), g8v(ev, 0));
    }
    let v = (x & 0xFFFF_FFFF) * 100_000_000 + (x >> 32u64);
    let k = 16 - n;
    proof {
        lemma_dlanes16(ev);
        lemma_dlanes_zeros(ev, n as int, 16);
        lemma_dlanes_same(ev, b16(d), n as int);
        lemma_dlanes_bound(b16(d), n as int);
        lemma_p10_mono(n as nat, 16);
        assert(p10i(16) == 10_000_000_000_000_000) by (compute_only);
        lemma_unscale(v, dlanes(b16(d), n as int), k as nat);
    }
    (v >> k as u64).wrapping_mul(INV5[k])
}

proof fn lemma_p10_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        p10i(a) <= p10i(b),
        p10i(a) >= 1,
    decreases b,
{
    if a < b {
        lemma_p10_mono(a, (b - 1) as nat);
    } else if a > 0 {
        lemma_p10_mono((a - 1) as nat, (a - 1) as nat);
    }
}

/// Lanes holding the digit values of `s[i..i + n]` read as `dval`.
pub proof fn lemma_dlanes_dval(v: Seq<u8>, s: Seq<u8>, i: int, n: int)
    requires
        n >= 0,
        forall|k: int| 0 <= k < n ==> v[k] as int == s[i + k] - 0x30,
    ensures
        dlanes(v, n) == dval(s, i, i + n),
    decreases n,
{
    if n > 0 {
        lemma_dlanes_dval(v, s, i, n - 1);
    }
}

/// `digit_run16`, also returning the value of the run's digits.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn digit_run_acc16(s: &[u8], i: usize) -> (r: (usize, u64))
    requires
        i + 16 <= s@.len(),
    ensures
        r.0 <= 16,
        forall|q: int| i <= q < i + r.0 ==> is_digit_byte(#[trigger] s@[q]),
        r.0 < 16 ==> !is_digit_byte(s@[i + r.0]),
        r.1 as int == dval(s@, i as int, i + r.0),
{
    let v = load16(s, i);
    let z = splat16(0x30);
    let d = sub16(v, z);
    let isd = eq16(min16(d, splat16(9)), d);
    let w = movemask16(isd);
    let m = (!w) & 0xFFFF;
    proof {
        assert forall|k: u32| k < 16 implies (#[trigger] bit(m, k) <==> !is_digit_byte(s@[i + k])) by {
            let j = k as int;
            assert(b16(v)[j] == s@[i + k]);
            lemma_digit_test(s@[i + k]);
            lemma_low16(w, k);
            assert(bit(w, k) == (b16(isd)[j] >= 0x80));
        }
        lemma_low16(w, 0);
    }
    let n = first_set16(m);
    proof {
        assert forall|q: int| i <= q < i + n implies is_digit_byte(#[trigger] s@[q]) by {
            assert(!bit(m, (q - i) as u32));
        }
        assert forall|k: int| 0 <= k < n implies b16(d)[k] as int == s@[i + k] - 0x30 && b16(d)[k] <= 9 by {
            assert(b16(v)[k] == s@[i + k]);
            assert(is_digit_byte(s@[i + k]));
        }
        lemma_dlanes_dval(b16(d), s@, i as int, n as int);
    }
    (n, digits_value16(d, n))
}

} // verus!

#[cfg(not(target_arch = "x86_64"))]
verus! {

/// Off x86-64: on AArch64, the verified NEON kernels in `crate::neon`
/// (each with this function's contract; NEON is part of the AArch64
/// baseline); elsewhere, scalar fallbacks, which are not verified.
#[verifier::external_body]
#[inline(always)]
pub fn copy_plain16(s: &[u8], i: usize, end: usize, out: &mut Vec<u8>) -> (r: usize)
    requires
        i + 16 <= s@.len(),
        i <= end,
        spare(*old(out)) >= 16,
    ensures
        r <= 16,
        i + r <= end,
        forall|q: int| i <= q < i + r ==> plain(#[trigger] s@[q]),
        (r < 16 && i + r < end) ==> !plain(s@[i + r]),
        final(out)@ == old(out)@ + s@.subrange(i as int, i + r),
        spare(*final(out)) == spare(*old(out)) - r,
{
    if cfg!(target_arch = "aarch64") {
        return crate::neon::copy_plain16_neon(s, i, end, out);
    }
    let lim = (end - i).min(16);
    let r = s[i..i + lim].iter().take_while(|&&c| c != 0x22 && c != 0x5C && c >= 0x20).count();
    out.extend_from_slice(&s[i..i + r]);
    r
}

#[verifier::external_body]
#[inline(always)]
pub fn classify_special(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !plain(s@[i + k])),
{
    if cfg!(target_arch = "aarch64") {
        return crate::neon::classify_special_neon(s, i);
    }
    (0..16).filter(|&k| { let c = s[i + k]; !(c != 0x22 && c != 0x5C && c >= 0x20) }).fold(0, |m, k| m | 1 << k)
}

#[verifier::external_body]
#[inline(always)]
pub fn classify_non_ws(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !is_ws(s@[i + k])),
{
    if cfg!(target_arch = "aarch64") {
        return crate::neon::classify_non_ws_neon(s, i);
    }
    (0..16).filter(|&k| !matches!(s[i + k], 0x20 | 0x0A | 0x0D | 0x09)).fold(0, |m, k| m | 1 << k)
}

#[verifier::external_body]
#[inline(always)]
pub fn classify_non_digit(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !is_digit_byte(s@[i + k])),
{
    if cfg!(target_arch = "aarch64") {
        return crate::neon::classify_non_digit_neon(s, i);
    }
    (0..16).filter(|&k| !s[i + k].is_ascii_digit()).fold(0, |m, k| m | 1 << k)
}

#[verifier::external_body]
#[inline(always)]
pub fn digit_run_acc16(s: &[u8], i: usize) -> (r: (usize, u64))
    requires
        i + 16 <= s@.len(),
    ensures
        r.0 <= 16,
        forall|q: int| i <= q < i + r.0 ==> is_digit_byte(#[trigger] s@[q]),
        r.0 < 16 ==> !is_digit_byte(s@[i + r.0]),
        r.1 as int == dval(s@, i as int, i + r.0),
{
    if cfg!(target_arch = "aarch64") {
        return crate::neon::digit_run_acc16_neon(s, i);
    }
    let n = s[i..i + 16].iter().take_while(|c| c.is_ascii_digit()).count();
    (n, s[i..i + n].iter().fold(0u64, |w, &c| w.wrapping_mul(10).wrapping_add((c - b'0') as u64)))
}

} // verus!

verus! {

#[verifier::bit_vector]
proof fn lemma_guard_bit(m: u32, k: u32)
    requires
        m < 0x10000,
    ensures
        k < 16 ==> (((m | 0x10000u32) >> k) & 1u32 == 1u32) == ((m >> k) & 1u32 == 1u32),
        ((m | 0x10000u32) >> 16u32) & 1u32 == 1u32,
        m | 0x10000u32 != 0,
{
}

/// The index of the lowest set bit of a 16-bit class mask, or 16 if none.
/// Every lower bit is clear.
#[inline(always)]
pub fn first_set16(m: u32) -> (r: usize)
    requires
        m < 0x10000,
    ensures
        r <= 16,
        forall|k: u32| k < r ==> !#[trigger] bit(m, k),
        r < 16 ==> bit(m, r as u32),
{
    let g = m | 0x10000u32;
    let tz = g.trailing_zeros();
    proof {
        vstd::std_specs::bits::axiom_u32_trailing_zeros(g);
        lemma_guard_bit(m, tz);
        assert forall|k: u32| k < tz implies !#[trigger] bit(m, k) by {
            lemma_guard_bit(m, k);
        }
        if tz > 16 {
            assert((g >> 16u32) & 1u32 == 0u32);
        }
    }
    tz as usize
}

/// Number of plain string bytes at `s[i..]`, up to 16. When fewer than 16,
/// the byte after them is not plain.
#[inline(always)]
pub fn plain_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> plain(#[trigger] s@[q]),
        r < 16 ==> !plain(s@[i + r]),
{
    if verilith_simd::neon::has_neon() {
        return crate::neon::plain_run16_neon(s, i);
    }
    let m = classify_special(s, i);
    let r = first_set16(m);
    proof {
        assert forall|q: int| i <= q < i + r implies plain(#[trigger] s@[q]) by {
            assert(!bit(m, (q - i) as u32));
        }
    }
    r
}

/// Appends the plain bytes at `s[i..]`, at most 16 and not past `end`, to
/// `out` (into reserved space), and returns how many: a 16-byte store,
/// whatever the count.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn copy_plain16(s: &[u8], i: usize, end: usize, out: &mut Vec<u8>) -> (r: usize)
    requires
        i + 16 <= s@.len(),
        i <= end,
        spare(*old(out)) >= 16,
    ensures
        r <= 16,
        i + r <= end,
        forall|q: int| i <= q < i + r ==> plain(#[trigger] s@[q]),
        (r < 16 && i + r < end) ==> !plain(s@[i + r]),
        final(out)@ == old(out)@ + s@.subrange(i as int, i + r),
        spare(*final(out)) == spare(*old(out)) - r,
{
    let v = load16(s, i);
    let p = plain_run16(s, i);
    let r = if p < end - i { p } else { end - i };
    append16_spare(out, v, r);
    assert(b16(v).subrange(0, r as int) =~= s@.subrange(i as int, i + r));
    r
}

/// Number of whitespace bytes at `s[i..]`, up to 16. When fewer than 16, the
/// byte after them is not whitespace.
#[inline(always)]
pub fn ws_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> is_ws(#[trigger] s@[q]),
        r < 16 ==> !is_ws(s@[i + r]),
{
    if verilith_simd::neon::has_neon() {
        return crate::neon::ws_run16_neon(s, i);
    }
    let m = classify_non_ws(s, i);
    let r = first_set16(m);
    proof {
        assert forall|q: int| i <= q < i + r implies is_ws(#[trigger] s@[q]) by {
            assert(!bit(m, (q - i) as u32));
        }
    }
    r
}

/// Number of ASCII digits at `s[i..]`, up to 16. When fewer than 16, the
/// byte after them is not a digit.
#[inline(always)]
pub fn digit_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> is_digit_byte(#[trigger] s@[q]),
        r < 16 ==> !is_digit_byte(s@[i + r]),
{
    if verilith_simd::neon::has_neon() {
        return crate::neon::digit_run16_neon(s, i);
    }
    let m = classify_non_digit(s, i);
    let r = first_set16(m);
    proof {
        assert forall|q: int| i <= q < i + r implies is_digit_byte(#[trigger] s@[q]) by {
            assert(!bit(m, (q - i) as u32));
        }
    }
    r
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    /// `is_x86_feature_detected!`, and false on other targets.
    macro_rules! detected {
        ($f:tt) => {{
            #[cfg(target_arch = "x86_64")]
            let r = std::is_x86_feature_detected!($f);
            #[cfg(not(target_arch = "x86_64"))]
            let r = false;
            r
        }};
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx512f,avx512bw,avx512vbmi2")]
    unsafe fn append512(v: &mut Vec<u32>, m: u64) -> usize {
        append_bits::<AVX512>(v, 3, m, 1000)
    }

    fn scalar(f: fn(u8) -> bool, s: &[u8], i: usize) -> u32 {
        (0..16).filter(|&k| f(s[i + k])).fold(0, |m, k| m | 1 << k)
    }

    #[test]
    fn vec_spare() {
        let mut v: Vec<u32> = Vec::new();
        reserve_spare(&mut v, 10);
        assert!(v.capacity() - v.len() >= 10);
        let p = v.as_ptr();
        for x in 0..10 {
            push_spare(&mut v, x);
        }
        assert_eq!(v, (0..10).collect::<Vec<u32>>());
        assert_eq!(v.as_ptr(), p);
        set_spare(&mut v, 3, 99);
        assert_eq!(v[3], 99);
        assert_eq!(v.len(), 10);
    }

    #[test]
    fn prefix_xor_and_bits() {
        let mut x: u64 = 0x2545F4914F6CDD1D;
        for _ in 0..200_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            for m in [x, x & (x >> 1), x & (x >> 3) & (x >> 5), 0, !0, 1 << (x % 64)] {
                for k in [SCALAR, AVX2, AVX512] {
                    let r = match k {
                        SCALAR => prefix_xor_clmul::<SCALAR>(m),
                        AVX2 => prefix_xor_clmul::<AVX2>(m),
                        _ => prefix_xor_clmul::<AVX512>(m),
                    };
                    let want = (0..64).fold((0u64, 0u64), |(acc, p), i| {
                        let p = p ^ (m >> i & 1);
                        (acc | p << i, p)
                    });
                    assert_eq!(r, want.0);
                }
                let want: Vec<u32> = (0..64).filter(|i| m >> i & 1 == 1).map(|i| 1000 + i).collect();
                let mut v = vec![7u32; 70];
                let n = append_bits::<SCALAR>(&mut v, 3, m, 1000);
                assert_eq!(v[3..n], want[..]);
                assert_eq!(v[..3], [7, 7, 7]);
                #[cfg(target_arch = "x86_64")]
                if detected!("avx512vbmi2") {
                    let mut v = vec![7u32; 70];
                    let n = unsafe { append512(&mut v, m) };
                    assert_eq!(v[3..n], want[..]);
                    assert_eq!(v[..3], [7, 7, 7]);
                }
            }
        }
    }

    #[test]
    fn classify64_agrees() {
        let kernels: &[u8] = if detected!("avx512bw") {
            &[SCALAR, AVX2, AVX512]
        } else {
            &[SCALAR, AVX2]
        };
        let mut buf = vec![0u8; 128];
        for fill in [0u8, 0x20, b'a', b'"', 0xFF] {
            for lane in 0..64 {
                for c in 0..=255u8 {
                    buf.iter_mut().for_each(|b| *b = fill);
                    buf[3 + lane] = c;
                    let want = classify64::<SCALAR>(&buf, 3);
                    let scalar_bit = |f: fn(u8) -> bool| (0..64).filter(|&k| f(buf[3 + k])).fold(0u64, |m, k| m | 1 << k);
                    assert_eq!(want.quote, scalar_bit(|c| c == b'"'));
                    assert_eq!(want.backslash, scalar_bit(|c| c == b'\\'));
                    assert_eq!(want.ws, scalar_bit(|c| matches!(c, b' ' | b'\t' | b'\n' | b'\r')));
                    assert_eq!(want.op, scalar_bit(|c| matches!(c, b'{' | b'}' | b'[' | b']' | b',' | b':')));
                    assert_eq!(want.ctrl, scalar_bit(|c| c < 0x20));
                    for &k in kernels {
                        let got = match k {
                            AVX2 => classify64::<AVX2>(&buf, 3),
                            AVX512 => classify64::<AVX512>(&buf, 3),
                            _ => continue,
                        };
                        assert_eq!(
                            (got.quote, got.backslash, got.ws, got.op, got.ctrl),
                            (want.quote, want.backslash, want.ws, want.op, want.ctrl)
                        );
                    }
                }
            }
        }
    }

    /// Every byte value in every lane, against varied neighbours, and at
    /// every alignment.
    #[test]
    fn classifiers_agree() {
        let not_plain = |c: u8| !(c != 0x22 && c != 0x5C && c >= 0x20);
        let not_ws = |c: u8| !matches!(c, 0x20 | 0x0A | 0x0D | 0x09);
        let not_digit = |c: u8| !c.is_ascii_digit();
        let fills = [0u8, 0x20, b'a', b'5', b'"', 0xFF];
        let mut buf = vec![0u8; 40];
        for &fill in &fills {
            for off in 0..16 {
                for lane in 0..16 {
                    for c in 0..=255u8 {
                        buf.iter_mut().for_each(|b| *b = fill);
                        buf[off + lane] = c;
                        assert_eq!(classify_special(&buf, off), scalar(not_plain, &buf, off));
                        assert_eq!(classify_non_ws(&buf, off), scalar(not_ws, &buf, off));
                        assert_eq!(classify_non_digit(&buf, off), scalar(not_digit, &buf, off));
                    }
                }
            }
        }
        // Random windows.
        let mut x: u64 = 0x243F6A8885A308D3;
        let data: Vec<u8> = (0..1 << 16)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x as u8
            })
            .collect();
        for i in 0..data.len() - 16 {
            assert_eq!(classify_special(&data, i), scalar(not_plain, &data, i));
            assert_eq!(classify_non_ws(&data, i), scalar(not_ws, &data, i));
            assert_eq!(classify_non_digit(&data, i), scalar(not_digit, &data, i));
        }
    }
}
