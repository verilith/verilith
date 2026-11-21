//! NEON kernels for AArch64 (Apple Silicon and other ARM64 CPUs), built
//! from the trusted NEON specifications in `verilith_simd::neon` and verified
//! against the same contracts as the AVX2 kernels. Off AArch64 the vsimd
//! wrappers run an emulation, so these build, verify and test everywhere;
//! `index::index` selects them only where `has_neon()` holds.
use crate::lanes::*;
use crate::simd::*;
use crate::spec::*;
use verilith_simd::lanes::*;
use verilith_simd::neon::*;
use verilith_simd::neon_mask::*;
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use verilith_simd::neon::group_neon;

/// The table lookups with a nibble index (`tbl` on `c & 0x0F`) give the
/// classes for every byte, including those from 0x80 up, where `pshufb`
/// would have given 0.
proof fn lemma_tables_nibble(c: u8)
    ensures
        (WS_TABLE@[(c % 16) as int] == c) == is_ws(c),
        (OP_TABLE@[(c % 16) as int] == (c | 0x20) && !(c <= 0x1F)) == is_op(c),
{
    crate::simd::lemma_tables(c);
    if c >= 0x80 {
        assert((c | 0x20u8) >= 0x80u8) by (bit_vector)
            requires c >= 0x80u8;
        assert(c % 16 == 0 ==> c != 0x20);
        let n = (c % 16) as int;
        assert(0 <= n < 16);
        assert(WS_TABLE@[n] == c ==> n != 0 && c == 0x80);
    }
}

/// The five class vectors of `s[i..i + 16]`: 0xFF where the byte is in the
/// class, else 0. As with AVX2, `r.3` may also mark control bytes.
#[inline(always)]
fn classes16(s: &[u8], i: usize, wt: uint8x16_t, ot: uint8x16_t) -> (r: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        i + 16 <= s@.len(),
        n8(wt) == WS_TABLE@,
        n8(ot) == OP_TABLE@,
    ensures
        is_mask(n8(r.0)) && is_mask(n8(r.1)) && is_mask(n8(r.2)) && is_mask(n8(r.3)) && is_mask(n8(r.4)),
        forall|k: int|
            0 <= k < 16 ==> {
                let c = #[trigger] s@[i + k];
                &&& (n8(r.0)[k] == 0xFF) == (c == 0x22)
                &&& (n8(r.1)[k] == 0xFF) == (c == 0x5C)
                &&& (n8(r.2)[k] == 0xFF) == is_ws(c)
                &&& (n8(r.3)[k] == 0xFF && !(c < 0x20)) == is_op(c)
                &&& (n8(r.4)[k] == 0xFF) == (c < 0x20)
            },
{
    let v = vld1q_u8_at(s, i);
    let nib = vandq_u8(v, vdupq_n_u8(0x0F));
    let sw = vqtbl1q_u8(wt, nib);
    let so = vqtbl1q_u8(ot, nib);
    let f = vorrq_u8(v, vdupq_n_u8(0x20));
    let q = vceqq_u8(v, vdupq_n_u8(0x22));
    let b = vceqq_u8(v, vdupq_n_u8(0x5C));
    let ws = vceqq_u8(sw, v);
    let op = vceqq_u8(so, f);
    // Unsigned v <= 0x1F: saturating v - 0x1F is zero.
    let ctrl = vceqq_u8(vqsubq_u8(v, vdupq_n_u8(0x1F)), vdupq_n_u8(0));
    proof {
        assert forall|k: int| 0 <= k < 16 implies {
            let c = #[trigger] s@[i + k];
            &&& (n8(q)[k] == 0xFF) == (c == 0x22)
            &&& (n8(b)[k] == 0xFF) == (c == 0x5C)
            &&& (n8(ws)[k] == 0xFF) == is_ws(c)
            &&& (n8(op)[k] == 0xFF && !(c < 0x20)) == is_op(c)
            &&& (n8(ctrl)[k] == 0xFF) == (c < 0x20)
        } by {
            let c = s@[i + k];
            assert(n8(v)[k] == c);
            assert(c & 0x0Fu8 == c % 16 && c & 0x0Fu8 < 16) by (bit_vector);
            assert(n8(nib)[k] == c % 16);
            assert(n8(sw)[k] == WS_TABLE@[(c % 16) as int]);
            assert(n8(so)[k] == OP_TABLE@[(c % 16) as int]);
            assert(n8(f)[k] == c | 0x20);
            lemma_tables_nibble(c);
        }
    }
    (q, b, ws, op, ctrl)
}

/// `bit64` of a `movemask64` result, for the bytes `s[i..i + 64]`.
proof fn lemma_mask_bits(s: Seq<u8>, i: int, a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, d: Seq<u8>, m: u64, k: u64)
    requires
        a.len() == 16 && b.len() == 16 && c.len() == 16 && d.len() == 16,
        k < 64,
        forall|j: int| 0 <= j < 64 ==> ((m >> (j as u64)) & 1u64 == 1u64) == (#[trigger] byte4(a, b, c, d, j) == 0xFF),
    ensures
        bit64(m, k) == (byte4(a, b, c, d, k as int) == 0xFF),
{
    assert(((m >> ((k as int) as u64)) & 1u64 == 1u64) == (byte4(a, b, c, d, k as int) == 0xFF));
}

/// Classifies `s[i..i + 64]`: the NEON counterpart of `classify64_avx2`.
#[inline(always)]
pub fn classify64_neon(s: &[u8], i: usize) -> (m: Masks)
    requires
        neon(),
        i + 64 <= s@.len(),
    ensures
        masks_of(m, s@, i as int),
{
    let _n = s.len();
    let wt = vld1q_u8_at(WS_TABLE.as_slice(), 0);
    let ot = vld1q_u8_at(OP_TABLE.as_slice(), 0);
    proof {
        assert(n8(wt) =~= WS_TABLE@);
        assert(n8(ot) =~= OP_TABLE@);
    }
    let c0 = classes16(s, i, wt, ot);
    let c1 = classes16(s, i + 16, wt, ot);
    let c2 = classes16(s, i + 32, wt, ot);
    let c3 = classes16(s, i + 48, wt, ot);
    let quote = movemask64(c0.0, c1.0, c2.0, c3.0);
    let backslash = movemask64(c0.1, c1.1, c2.1, c3.1);
    let ws = movemask64(c0.2, c1.2, c2.2, c3.2);
    let op1 = movemask64(c0.3, c1.3, c2.3, c3.3);
    let ctrl = movemask64(c0.4, c1.4, c2.4, c3.4);
    let m = Masks { quote, backslash, ws, op: op1 & !ctrl, ctrl };
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
            lemma_mask_bits(s@, i as int, n8(c0.0), n8(c1.0), n8(c2.0), n8(c3.0), quote, k);
            lemma_mask_bits(s@, i as int, n8(c0.1), n8(c1.1), n8(c2.1), n8(c3.1), backslash, k);
            lemma_mask_bits(s@, i as int, n8(c0.2), n8(c1.2), n8(c2.2), n8(c3.2), ws, k);
            lemma_mask_bits(s@, i as int, n8(c0.3), n8(c1.3), n8(c2.3), n8(c3.3), op1, k);
            lemma_mask_bits(s@, i as int, n8(c0.4), n8(c1.4), n8(c2.4), n8(c3.4), ctrl, k);
            crate::index::lemma_bit_ops(op1, !ctrl, k);
            crate::index::lemma_bit_ops(ctrl, ctrl, k);
            let q = (k / 16) as int;
            let l = (k % 16) as int;
            assert(s@[(i + 16 * q) + l] == c);
        }
    }
    m
}

/// The four vectors hold `s[i..i + 64]`.
pub open spec fn holds64(s: Seq<u8>, i: int, v0: uint8x16_t, v1: uint8x16_t, v2: uint8x16_t, v3: uint8x16_t) -> bool {
    &&& 0 <= i
    &&& i + 64 <= s.len()
    &&& n8(v0) == s.subrange(i, i + 16)
    &&& n8(v1) == s.subrange(i + 16, i + 32)
    &&& n8(v2) == s.subrange(i + 32, i + 48)
    &&& n8(v3) == s.subrange(i + 48, i + 64)
}

/// Loads `s[i..i + 64]`.
#[inline(always)]
pub fn load64(s: &[u8], i: usize) -> (r: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        i + 64 <= s@.len(),
    ensures
        holds64(s@, i as int, r.0, r.1, r.2, r.3),
{
    let _n = s.len();
    (vld1q_u8_at(s, i), vld1q_u8_at(s, i + 16), vld1q_u8_at(s, i + 32), vld1q_u8_at(s, i + 48))
}

/// A fact about each lane of four class vectors, as bits of their mask.
proof fn lemma_mask4(
    s: Seq<u8>,
    i: int,
    v0: uint8x16_t,
    v1: uint8x16_t,
    v2: uint8x16_t,
    v3: uint8x16_t,
    c0: uint8x16_t,
    c1: uint8x16_t,
    c2: uint8x16_t,
    c3: uint8x16_t,
    m: u64,
    f: spec_fn(u8) -> bool,
)
    requires
        holds64(s, i, v0, v1, v2, v3),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] n8(c0)[k] == 0xFF) == f(n8(v0)[k]),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] n8(c1)[k] == 0xFF) == f(n8(v1)[k]),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] n8(c2)[k] == 0xFF) == f(n8(v2)[k]),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] n8(c3)[k] == 0xFF) == f(n8(v3)[k]),
        forall|j: int|
            0 <= j < 64 ==> ((m >> (j as u64)) & 1u64 == 1u64) == (#[trigger] byte4(n8(c0), n8(c1), n8(c2), n8(c3), j)
                == 0xFF),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(m, k) == f(s[i + k]),
{
    assert forall|k: u64| k < 64 implies #[trigger] bit64(m, k) == f(s[i + k]) by {
        lemma_mask_bits(s, i, n8(c0), n8(c1), n8(c2), n8(c3), m, k);
        let l = (k % 16) as int;
        if k < 16 {
            assert((n8(c0)[l] == 0xFF) == f(n8(v0)[l]));
            assert(n8(v0)[l] == s[i + k]);
        } else if k < 32 {
            assert((n8(c1)[l] == 0xFF) == f(n8(v1)[l]));
            assert(n8(v1)[l] == s[i + k]);
        } else if k < 48 {
            assert((n8(c2)[l] == 0xFF) == f(n8(v2)[l]));
            assert(n8(v2)[l] == s[i + k]);
        } else {
            assert((n8(c3)[l] == 0xFF) == f(n8(v3)[l]));
            assert(n8(v3)[l] == s[i + k]);
        }
    }
}

/// 0xFF where the byte is `c`.
#[inline(always)]
fn eq16(v: uint8x16_t, c: u8) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        is_mask(n8(r)),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] n8(r)[k] == 0xFF) == (n8(v)[k] == c),
{
    vceqq_u8(v, vdupq_n_u8(c))
}

/// 0xFF where the byte is whitespace.
#[inline(always)]
fn ws16(v: uint8x16_t, wt: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        n8(wt) == WS_TABLE@,
    ensures
        is_mask(n8(r)),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] n8(r)[k] == 0xFF) == is_ws(n8(v)[k]),
{
    let nib = vandq_u8(v, vdupq_n_u8(0x0F));
    let sw = vqtbl1q_u8(wt, nib);
    let r = vceqq_u8(sw, v);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] n8(r)[k] == 0xFF) == is_ws(n8(v)[k]) by {
            let c = n8(v)[k];
            assert(c & 0x0Fu8 == c % 16 && c & 0x0Fu8 < 16) by (bit_vector);
            assert(n8(nib)[k] == c % 16);
            assert(n8(sw)[k] == WS_TABLE@[(c % 16) as int]);
            lemma_tables_nibble(c);
        }
    }
    r
}

/// What the operator table says of a byte; it is right from 0x20 up.
pub open spec fn op_raw(c: u8) -> bool {
    OP_TABLE@[(c % 16) as int] == (c | 0x20)
}

/// 0xFF where the operator table matches.
#[inline(always)]
fn op16(v: uint8x16_t, ot: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        n8(ot) == OP_TABLE@,
    ensures
        is_mask(n8(r)),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] n8(r)[k] == 0xFF) == op_raw(n8(v)[k]),
{
    let nib = vandq_u8(v, vdupq_n_u8(0x0F));
    let so = vqtbl1q_u8(ot, nib);
    let f = vorrq_u8(v, vdupq_n_u8(0x20));
    let r = vceqq_u8(so, f);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] n8(r)[k] == 0xFF) == op_raw(n8(v)[k]) by {
            let c = n8(v)[k];
            assert(c & 0x0Fu8 == c % 16 && c & 0x0Fu8 < 16) by (bit_vector);
            assert(n8(nib)[k] == c % 16);
            assert(n8(so)[k] == OP_TABLE@[(c % 16) as int]);
            assert(n8(f)[k] == c | 0x20);
        }
    }
    r
}

/// 0xFF where the byte is a control character.
#[inline(always)]
fn ctrl16(v: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        is_mask(n8(r)),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] n8(r)[k] == 0xFF) == (n8(v)[k] < 0x20),
{
    vcleq_u8(v, vdupq_n_u8(0x1F))
}

/// The bytes of `s[i..i + 64]` equal to `c`, as a mask. The classes come
/// one mask at a time, so that stage 1 can use each as soon as it is
/// ready rather than after all five.
#[inline(always)]
pub fn eq_mask64(
    v0: uint8x16_t,
    v1: uint8x16_t,
    v2: uint8x16_t,
    v3: uint8x16_t,
    c: u8,
    Ghost(s): Ghost<Seq<u8>>,
    Ghost(i): Ghost<int>,
) -> (m: u64)
    requires
        neon(),
        holds64(s, i, v0, v1, v2, v3),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(m, k) == (s[i + k] == c),
{
    let c0 = eq16(v0, c);
    let c1 = eq16(v1, c);
    let c2 = eq16(v2, c);
    let c3 = eq16(v3, c);
    let m = movemask64(c0, c1, c2, c3);
    proof {
        lemma_mask4(s, i, v0, v1, v2, v3, c0, c1, c2, c3, m, |x: u8| x == c);
    }
    m
}

/// The whitespace of `s[i..i + 64]`, as a mask.
#[inline(always)]
pub fn ws_mask64(
    v0: uint8x16_t,
    v1: uint8x16_t,
    v2: uint8x16_t,
    v3: uint8x16_t,
    Ghost(s): Ghost<Seq<u8>>,
    Ghost(i): Ghost<int>,
) -> (m: u64)
    requires
        neon(),
        holds64(s, i, v0, v1, v2, v3),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(m, k) == is_ws(s[i + k]),
{
    let wt = vld1q_u8_at(WS_TABLE.as_slice(), 0);
    proof {
        assert(n8(wt) =~= WS_TABLE@);
    }
    let c0 = ws16(v0, wt);
    let c1 = ws16(v1, wt);
    let c2 = ws16(v2, wt);
    let c3 = ws16(v3, wt);
    let m = movemask64(c0, c1, c2, c3);
    proof {
        lemma_mask4(s, i, v0, v1, v2, v3, c0, c1, c2, c3, m, |x: u8| is_ws(x));
    }
    m
}

/// The operators and the control characters of `s[i..i + 64]`, as masks.
#[inline(always)]
pub fn op_ctrl_mask64(
    v0: uint8x16_t,
    v1: uint8x16_t,
    v2: uint8x16_t,
    v3: uint8x16_t,
    Ghost(s): Ghost<Seq<u8>>,
    Ghost(i): Ghost<int>,
) -> (r: (u64, u64))
    requires
        neon(),
        holds64(s, i, v0, v1, v2, v3),
    ensures
        forall|k: u64| k < 64 ==> #[trigger] bit64(r.0, k) == is_op(s[i + k]),
        forall|k: u64| k < 64 ==> #[trigger] bit64(r.1, k) == (s[i + k] < 0x20),
{
    let ot = vld1q_u8_at(OP_TABLE.as_slice(), 0);
    proof {
        assert(n8(ot) =~= OP_TABLE@);
    }
    let c0 = op16(v0, ot);
    let c1 = op16(v1, ot);
    let c2 = op16(v2, ot);
    let c3 = op16(v3, ot);
    let op1 = movemask64(c0, c1, c2, c3);
    let d0 = ctrl16(v0);
    let d1 = ctrl16(v1);
    let d2 = ctrl16(v2);
    let d3 = ctrl16(v3);
    let ctrl = movemask64(d0, d1, d2, d3);
    let op = op1 & !ctrl;
    proof {
        lemma_mask4(s, i, v0, v1, v2, v3, c0, c1, c2, c3, op1, |x: u8| op_raw(x));
        lemma_mask4(s, i, v0, v1, v2, v3, d0, d1, d2, d3, ctrl, |x: u8| x < 0x20);
        assert forall|k: u64| k < 64 implies #[trigger] bit64(op, k) == is_op(s[i + k]) by {
            assert(bit64(op1, k) == op_raw(s[i + k]));
            assert(bit64(ctrl, k) == (s[i + k] < 0x20));
            crate::index::lemma_bit_ops(op1, !ctrl, k);
            crate::index::lemma_bit_ops(ctrl, ctrl, k);
            lemma_tables_nibble(s[i + k]);
        }
    }
    (op, ctrl)
}

/// Whether `s[i..i + 64]`, already loaded, is all ASCII.
#[inline(always)]
pub fn ascii4(
    v0: uint8x16_t,
    v1: uint8x16_t,
    v2: uint8x16_t,
    v3: uint8x16_t,
    Ghost(s): Ghost<Seq<u8>>,
    Ghost(i): Ghost<int>,
) -> (r: bool)
    requires
        neon(),
        holds64(s, i, v0, v1, v2, v3),
    ensures
        r ==> crate::utf8::ascii_span(s, i, i + 64),
{
    let o = vorrq_u8(vorrq_u8(v0, v1), vorrq_u8(v2, v3));
    let r = vmaxvq_u8(o) < 0x80;
    proof {
        if r {
            assert forall|t: int| i <= t < i + 64 implies #[trigger] s[t] < 0x80 by {
                let l = (t - i) % 16;
                let (x0, x1, x2, x3) = (n8(v0)[l], n8(v1)[l], n8(v2)[l], n8(v3)[l]);
                assert(n8(o)[l] == ((x0 | x1) | (x2 | x3)));
                assert(n8(o)[l] < 0x80);
                assert(((x0 | x1) | (x2 | x3)) < 0x80u8 ==> x0 < 0x80u8 && x1 < 0x80u8 && x2 < 0x80u8 && x3 < 0x80u8)
                    by (bit_vector);
                if t < i + 16 {
                    assert(x0 == s[t]);
                } else if t < i + 32 {
                    assert(x1 == s[t]);
                } else if t < i + 48 {
                    assert(x2 == s[t]);
                } else {
                    assert(x3 == s[t]);
                }
            }
        }
    }
    r
}

/// Whether `s[j - 3 .. j + 64]` is all ASCII, in five loads.
#[inline(always)]
pub fn ascii64_neon(s: &[u8], j: usize) -> (r: bool)
    requires
        neon(),
        3 <= j,
        j + 64 <= s@.len(),
    ensures
        r ==> crate::utf8::ascii_span(s@, j - 3, j + 64),
{
    let _n = s.len();
    let a = vld1q_u8_at(s, j - 3);
    let b = vld1q_u8_at(s, j + 13);
    let c = vld1q_u8_at(s, j + 16);
    let d = vld1q_u8_at(s, j + 32);
    let e = vld1q_u8_at(s, j + 48);
    let o = vorrq_u8(vorrq_u8(vorrq_u8(a, b), vorrq_u8(c, d)), e);
    let r = vmaxvq_u8(o) < 0x80;
    proof {
        if r {
            assert forall|t: int| j - 3 <= t < j + 64 implies #[trigger] s@[t] < 0x80 by {
                let (v, l) = if t < j + 13 {
                    (a, t - (j - 3))
                } else if t < j + 16 {
                    (b, t - (j + 13))
                } else if t < j + 32 {
                    (c, t - (j + 16))
                } else if t < j + 48 {
                    (d, t - (j + 32))
                } else {
                    (e, t - (j + 48))
                };
                assert(0 <= l < 16);
                assert(n8(v)[l] == s@[t]);
                let (x0, x1, x2, x3, x4) = (n8(a)[l], n8(b)[l], n8(c)[l], n8(d)[l], n8(e)[l]);
                assert(n8(o)[l] == (((x0 | x1) | (x2 | x3)) | x4));
                assert(n8(o)[l] < 0x80);
                assert((((x0 | x1) | (x2 | x3)) | x4) < 0x80u8 ==> x0 < 0x80u8 && x1 < 0x80u8 && x2 < 0x80u8 && x3
                    < 0x80u8 && x4 < 0x80u8) by (bit_vector);
            }
        }
    }
    r
}

/// The error lanes for `[j, j + 16)`: lane `l` is zero exactly when
/// `loc` holds at `j + l`. The NEON counterpart of `utf8::err32`, with
/// `tbl` for `pshufb` and `uqsub` for `vpsubusb`.
#[inline(always)]
fn err16(s: &[u8], st: usize, j: usize, t1: uint8x16_t, t2: uint8x16_t, t3: uint8x16_t) -> (e: uint8x16_t)
    requires
        neon(),
        st + 3 <= j,
        j + 16 <= s@.len(),
        n8(t1) == crate::utf8::t1(),
        n8(t2) == crate::utf8::t2(),
        n8(t3) == crate::utf8::t3(),
    ensures
        forall|l: int| 0 <= l < 16 ==> (#[trigger] n8(e)[l] == 0) == verilith_core::utf8::loc(s@, st as int, j + l),
{
    let c = vld1q_u8_at(s, j);
    let p1 = vld1q_u8_at(s, j - 1);
    let p2 = vld1q_u8_at(s, j - 2);
    let p3 = vld1q_u8_at(s, j - 3);
    let h1 = vshrq_n_u8::<4>(p1);
    let l1 = vandq_u8(p1, vdupq_n_u8(0x0F));
    let hc = vshrq_n_u8::<4>(c);
    let a = vqtbl1q_u8(t1, h1);
    let b = vqtbl1q_u8(t2, l1);
    let d = vqtbl1q_u8(t3, hc);
    let m = vandq_u8(vorrq_u8(vqsubq_u8(p2, vdupq_n_u8(0x60)), vqsubq_u8(p3, vdupq_n_u8(0x70))), vdupq_n_u8(0x80));
    let e = veorq_u8(vandq_u8(vandq_u8(a, b), d), m);
    proof {
        reveal_with_fuel(verilith_simd::ops::pow2_spec, 5);
        assert(verilith_simd::ops::pow2_spec(4) == 16);
        assert forall|l: int| 0 <= l < 16 implies (#[trigger] n8(e)[l] == 0) == verilith_core::utf8::loc(
            s@,
            st as int,
            j + l,
        ) by {
            let k = j + l;
            let x3 = s@[k - 3];
            let x2 = s@[k - 2];
            let x1 = s@[k - 1];
            let x = s@[k];
            assert(n8(c)[l] == x);
            assert(n8(p1)[l] == x1);
            assert(n8(p2)[l] == x2);
            assert(n8(p3)[l] == x3);
            assert(x1 / 16 < 16 && x / 16 < 16);
            assert(x1 & 0x0Fu8 < 16 && x1 & 0x0Fu8 == x1 % 16) by (bit_vector);
            assert(n8(h1)[l] == x1 / 16);
            assert(n8(l1)[l] == x1 & 0x0F);
            assert(n8(hc)[l] == x / 16);
            let ea = crate::utf8::t1()[(x1 / 16) as int];
            let eb = crate::utf8::t2()[(x1 & 0x0F) as int];
            let ed = crate::utf8::t3()[(x / 16) as int];
            let em = (crate::utf8::subs(x2, 0x60) | crate::utf8::subs(x3, 0x70)) & 0x80;
            assert(n8(e)[l] == ((ea & eb) & ed) ^ em);
            crate::utf8::lemma_lane(s@, st as int, k, x3, x2, x1, x, n8(e)[l]);
        }
    }
    e
}

/// `loc` on `[j, j + 64)`, from four error vectors and one horizontal max.
#[inline(always)]
pub fn utf8_64_neon(s: &[u8], st: usize, j: usize) -> (r: bool)
    requires
        neon(),
        st + 3 <= j,
        j + 64 <= s@.len(),
    ensures
        r == verilith_core::utf8::all_loc(s@, st as int, j as int, j + 64),
{
    let _n = s.len();
    let t1 = vld1q_u8_at(crate::utf8::T1.as_slice(), 0);
    let t2 = vld1q_u8_at(crate::utf8::T2.as_slice(), 0);
    let t3 = vld1q_u8_at(crate::utf8::T3.as_slice(), 0);
    proof {
        assert(n8(t1) =~= crate::utf8::t1());
        assert(n8(t2) =~= crate::utf8::t2());
        assert(n8(t3) =~= crate::utf8::t3());
    }
    let e0 = err16(s, st, j, t1, t2, t3);
    let e1 = err16(s, st, j + 16, t1, t2, t3);
    let e2 = err16(s, st, j + 32, t1, t2, t3);
    let e3 = err16(s, st, j + 48, t1, t2, t3);
    let o = vorrq_u8(vorrq_u8(e0, e1), vorrq_u8(e2, e3));
    let mx = vmaxvq_u8(o);
    let r = mx == 0;
    proof {
        let g = s@;
        let si = st as int;
        let ji = j as int;
        assert forall|l: int| 0 <= l < 16 implies (#[trigger] n8(o)[l] == 0) == (verilith_core::utf8::loc(g, si, ji + l)
            && verilith_core::utf8::loc(g, si, ji + 16 + l) && verilith_core::utf8::loc(g, si, ji + 32 + l) && verilith_core::utf8::loc(
            g,
            si,
            ji + 48 + l,
        )) by {
            let (y0, y1, y2, y3) = (n8(e0)[l], n8(e1)[l], n8(e2)[l], n8(e3)[l]);
            assert(n8(o)[l] == ((y0 | y1) | (y2 | y3)));
            assert((((y0 | y1) | (y2 | y3)) == 0) == (y0 == 0 && y1 == 0 && y2 == 0 && y3 == 0)) by (bit_vector);
        }
        if r {
            assert forall|k: int| ji <= k < ji + 64 implies #[trigger] verilith_core::utf8::loc(g, si, k) by {
                let l = if k < ji + 16 {
                    k - ji
                } else if k < ji + 32 {
                    k - ji - 16
                } else if k < ji + 48 {
                    k - ji - 32
                } else {
                    k - ji - 48
                };
                assert(0 <= l < 16);
                assert(n8(o)[l] <= mx);
                assert(n8(o)[l] == 0);
            }
        } else {
            let l = choose|l: int| 0 <= l < 16 && #[trigger] n8(o)[l] == mx;
            assert(n8(o)[l] != 0);
            if !verilith_core::utf8::loc(g, si, ji + l) {
            } else if !verilith_core::utf8::loc(g, si, ji + 16 + l) {
            } else if !verilith_core::utf8::loc(g, si, ji + 32 + l) {
            } else {
                assert(!verilith_core::utf8::loc(g, si, ji + 48 + l));
            }
            assert(!verilith_core::utf8::all_loc(g, si, ji, ji + 64));
        }
    }
    r
}


proof fn lemma_p10_pos(k: nat)
    ensures
        p10i(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_p10_pos((k - 1) as nat);
    }
}

proof fn lemma_p10_le16(k: nat)
    requires
        k <= 16,
    ensures
        1 <= p10i(k) <= 10_000_000_000_000_000,
    decreases 16 - k,
{
    lemma_p10_pos(k);
    if k < 16 {
        lemma_p10_le16(k + 1);
        assert(p10i(k + 1) == 10 * p10i(k));
    } else {
        assert(p10i(16) == 10_000_000_000_000_000) by (compute_only);
    }
}

#[verifier::bit_vector]
proof fn lemma_not16(a: u32, k: u32)
    requires
        k < 16,
    ensures
        (((!a) & 0xFFFFu32) >> k) & 1u32 == 1u32 <==> !((a >> k) & 1u32 == 1u32),
        (!a) & 0xFFFFu32 < 0x10000u32,
{
}

/// `simd::classify_special` with NEON: bit `k` is set exactly when
/// 0xFF at each byte of `s[i..i + 16]` that is not plain string content.
#[inline(always)]
pub fn special_vec_neon(s: &[u8], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        is_mask(n8(r)),
        forall|k: int| 0 <= k < 16 ==> ((n8(r)[k] == 0xFF) == !plain(#[trigger] s@[i + k])),
{
    let v = vld1q_u8_at(s, i);
    let q = vceqq_u8(v, vdupq_n_u8(0x22));
    let b = vceqq_u8(v, vdupq_n_u8(0x5C));
    // Unsigned v <= 0x1F: saturating v - 0x1F is zero.
    let c = vceqq_u8(vqsubq_u8(v, vdupq_n_u8(0x1F)), vdupq_n_u8(0));
    let all = vorrq_u8(vorrq_u8(q, b), c);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (n8(all)[k] == 0xFF || n8(all)[k] == 0) && ((n8(all)[k] == 0xFF)
            == !plain(#[trigger] s@[i + k])) by {
            let x = s@[i + k];
            assert(n8(v)[k] == x);
            let (a1, a2, a3) = (n8(q)[k], n8(b)[k], n8(c)[k]);
            assert((a1 == 0 || a1 == 0xFF) && (a2 == 0 || a2 == 0xFF) && (a3 == 0 || a3 == 0xFF));
            assert(n8(all)[k] == ((a1 | a2) | a3));
            assert((a1 == 0 || a1 == 0xFFu8) && (a2 == 0 || a2 == 0xFFu8) && (a3 == 0 || a3 == 0xFFu8) ==> {
                let o = (a1 | a2) | a3;
                (o == 0 || o == 0xFFu8) && (o == 0xFFu8) == (a1 == 0xFFu8 || a2 == 0xFFu8 || a3 == 0xFFu8)
            }) by (bit_vector);
        }
        assert forall|k: int| 0 <= k < 16 implies #[trigger] n8(all)[k] == 0 || n8(all)[k] == 0xFF by {
            let (a1, a2, a3) = (n8(q)[k], n8(b)[k], n8(c)[k]);
            assert((a1 == 0 || a1 == 0xFF) && (a2 == 0 || a2 == 0xFF) && (a3 == 0 || a3 == 0xFF));
            assert(n8(all)[k] == ((a1 | a2) | a3));
            assert((a1 == 0 || a1 == 0xFFu8) && (a2 == 0 || a2 == 0xFFu8) && (a3 == 0 || a3 == 0xFFu8) ==> {
                let o = (a1 | a2) | a3;
                o == 0 || o == 0xFFu8
            }) by (bit_vector);
        }
        assert(is_mask(n8(all)));
    }
    all
}

/// `s[i + k]` is not plain string content.
#[inline(always)]
pub fn classify_special_neon(s: &[u8], i: usize) -> (m: u32)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !plain(s@[i + k])),
{
    let all = special_vec_neon(s, i);
    let m = verilith_simd::neon_mask::movemask16(all);
    proof {
        assert forall|k: u32| k < 16 implies (#[trigger] bit(m, k) <==> !plain(s@[i + k])) by {
            assert(plain(s@[i + k as int]) == plain(s@[i + k]));
        }
    }
    m
}

/// 0xFF at each whitespace byte of `s[i..i + 16]`.
#[inline(always)]
pub fn ws_vec_neon(s: &[u8], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        is_mask(n8(r)),
        forall|k: int| 0 <= k < 16 ==> ((n8(r)[k] == 0xFF) == is_ws(#[trigger] s@[i + k])),
{
    let v = vld1q_u8_at(s, i);
    let wt = vld1q_u8_at(WS_TABLE.as_slice(), 0);
    proof {
        assert(n8(wt) =~= WS_TABLE@);
    }
    let nib = vandq_u8(v, vdupq_n_u8(0x0F));
    let ws = vceqq_u8(vqtbl1q_u8(wt, nib), v);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (n8(ws)[k] == 0xFF || n8(ws)[k] == 0) && ((n8(ws)[k] == 0xFF)
            == is_ws(#[trigger] s@[i + k])) by {
            let c = s@[i + k];
            assert(n8(v)[k] == c);
            assert(c & 0x0Fu8 == c % 16 && c & 0x0Fu8 < 16) by (bit_vector);
            assert(n8(nib)[k] == c % 16);
            lemma_tables_nibble(c);
        }
        assert(is_mask(n8(ws)));
    }
    ws
}

/// `simd::classify_non_ws` with NEON.
#[inline(always)]
pub fn classify_non_ws_neon(s: &[u8], i: usize) -> (m: u32)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !is_ws(s@[i + k])),
{
    let ws = ws_vec_neon(s, i);
    let w = verilith_simd::neon_mask::movemask16(ws);
    let m = (!w) & 0xFFFF;
    proof {
        assert forall|k: u32| k < 16 implies (#[trigger] bit(m, k) <==> !is_ws(s@[i + k])) by {
            lemma_not16(w, k);
            assert(is_ws(s@[i + k as int]) == is_ws(s@[i + k]));
        }
        lemma_not16(w, 0);
    }
    m
}

/// 0xFF at each ASCII digit of `s[i..i + 16]`.
#[inline(always)]
pub fn digit_vec_neon(s: &[u8], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        is_mask(n8(r)),
        forall|k: int| 0 <= k < 16 ==> ((n8(r)[k] == 0xFF) == is_digit_byte(#[trigger] s@[i + k])),
{
    let v = vld1q_u8_at(s, i);
    // (v - '0') mod 256 <= 9: saturating (v - '0') - 9 is zero.
    let d = vaddq_u8(v, vdupq_n_u8(0xD0));
    let isd = vceqq_u8(vqsubq_u8(d, vdupq_n_u8(9)), vdupq_n_u8(0));
    proof {
        assert forall|k: int| 0 <= k < 16 implies (n8(isd)[k] == 0xFF || n8(isd)[k] == 0) && ((n8(isd)[k] == 0xFF)
            == is_digit_byte(#[trigger] s@[i + k])) by {
            let c = s@[i + k];
            assert(n8(v)[k] == c);
            let e = ((c + 0xD0u8 as int) % 256) as u8;
            assert(n8(d)[k] == e);
            assert(e == c.wrapping_add(0xD0u8)) by {
                assert(c.wrapping_add(0xD0u8) == ((c + 0xD0u8 as int) % 256) as u8);
            }
            assert({
                let e2 = c.wrapping_add(0xD0u8);
                (e2 <= 9u8) == (0x30u8 <= c && c <= 0x39u8)
            }) by (bit_vector);
        }
        assert(is_mask(n8(isd)));
    }
    isd
}

/// `simd::classify_non_digit` with NEON.
#[inline(always)]
pub fn classify_non_digit_neon(s: &[u8], i: usize) -> (m: u32)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> (#[trigger] bit(m, k) <==> !is_digit_byte(s@[i + k])),
{
    let isd = digit_vec_neon(s, i);
    let w = verilith_simd::neon_mask::movemask16(isd);
    let m = (!w) & 0xFFFF;
    proof {
        assert forall|k: u32| k < 16 implies (#[trigger] bit(m, k) <==> !is_digit_byte(s@[i + k])) by {
            lemma_not16(w, k);
            assert(is_digit_byte(s@[i + k as int]) == is_digit_byte(s@[i + k]));
        }
        lemma_not16(w, 0);
    }
    m
}

/// `tbl` indices that move the first `n` bytes of a vector to its end and
/// zero the rest: the 16 bytes at offset `n` (0xFF selects zero).
pub const SHUF_TAIL: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
];

/// Weights that combine digit lanes in pairs: to two, four and then eight
/// digits.
pub const W10: [u8; 16] = [10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1];

pub const W100: [u16; 8] = [100, 1, 100, 1, 100, 1, 100, 1];

pub const W10000: [u32; 4] = [10000, 1, 10000, 1];

/// Lanes that are zero and then `n` lanes of `v` read as `v`'s first `n`.
proof fn lemma_dlanes_lead(u: Seq<u8>, v: Seq<u8>, z: int, n: int)
    requires
        0 <= z,
        0 <= n,
        forall|k: int| 0 <= k < z ==> u[k] == 0,
        forall|k: int| 0 <= k < n ==> u[z + k] == v[k],
    ensures
        dlanes(u, z + n) == dlanes(v, n),
    decreases z + n,
{
    if n > 0 {
        lemma_dlanes_lead(u, v, z, n - 1);
        assert(u[z + (n - 1)] == v[n - 1]);
    } else if z > 0 {
        lemma_dlanes_lead(u, v, z - 1, 0);
        assert(u[z - 1] == 0);
    }
}

/// Adjacent digit lanes combined in pairs: eight 16-bit lanes, each
/// `10 * a + b`.
#[verifier::spinoff_prover]
#[inline(always)]
fn pairs16_neon(e: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        forall|k: int| 0 <= k < 16 ==> n8(e)[k] <= 9,
    ensures
        forall|j: int| 0 <= j < 8 ==> (#[trigger] u16s(n8(r))[j]) as int == n8(e)[2 * j] * 10 + n8(e)[2 * j + 1],
{
    let ghost ev = n8(e);
    let w1 = vld1q_u8_at(W10.as_slice(), 0);
    let t1 = vmulq_u8(e, w1);
    let r = vpaddlq_u8(t1);
    proof {
        assert forall|j: int| 0 <= j < 8 implies (#[trigger] u16s(n8(r))[j]) as int == ev[2 * j] * 10 + ev[2 * j + 1] by {
            assert(u16s(n8(r))[j] == paddl8(n8(t1))[j]);
            assert(n8(w1)[2 * j] == W10@[2 * j] && n8(w1)[2 * j + 1] == W10@[2 * j + 1]);
            assert(W10@[2 * j] == 10 && W10@[2 * j + 1] == 1);
            assert(ev[2 * j] <= 9 && ev[2 * j + 1] <= 9);
            assert(n8(t1)[2 * j] as int == (ev[2 * j] * 10) % 256);
            assert(n8(t1)[2 * j + 1] as int == (ev[2 * j + 1] * 1) % 256);
        }
    }
    r
}

/// Adjacent 16-bit lanes (each below 100) combined in pairs: four 32-bit
/// lanes, each `100 * a + b`.
#[verifier::spinoff_prover]
#[inline(always)]
fn quads16_neon(p: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        forall|j: int| 0 <= j < 8 ==> (#[trigger] u16s(n8(p))[j]) <= 99,
    ensures
        forall|j: int| 0 <= j < 4 ==> (#[trigger] u32s(n8(r))[j]) as int == u16s(n8(p))[2 * j] * 100 + u16s(n8(p))[2 * j + 1],
{
    let ghost a = u16s(n8(p));
    let w2 = vld1q_u16_at(W100.as_slice(), 0);
    let t2 = vmulq_u16(p, w2);
    let r = vpaddlq_u16(t2);
    proof {
        assert forall|j: int| 0 <= j < 4 implies (#[trigger] u32s(n8(r))[j]) as int == a[2 * j] * 100 + a[2 * j + 1] by {
            let b = u16s(n8(t2));
            assert(u32s(n8(r))[j] == paddl16(b)[j]);
            assert(u16s(n8(w2))[2 * j] == W100@[2 * j] && u16s(n8(w2))[2 * j + 1] == W100@[2 * j + 1]);
            assert(W100@[2 * j] == 100 && W100@[2 * j + 1] == 1);
            assert(a[2 * j] <= 99 && a[2 * j + 1] <= 99);
            assert(b[2 * j] as int == (a[2 * j] * 100) % 0x10000);
            assert(b[2 * j + 1] as int == (a[2 * j + 1] * 1) % 0x10000);
        }
    }
    r
}

/// Adjacent 32-bit lanes (each below 10000) combined in pairs: two 64-bit
/// lanes, each `10000 * a + b`.
#[verifier::spinoff_prover]
#[inline(always)]
fn halves16_neon(p: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        forall|j: int| 0 <= j < 4 ==> (#[trigger] u32s(n8(p))[j]) <= 9999,
    ensures
        forall|j: int| 0 <= j < 2 ==> (#[trigger] u64s(n8(r))[j]) as int == u32s(n8(p))[2 * j] * 10000 + u32s(n8(p))[2 * j + 1],
{
    let ghost a = u32s(n8(p));
    let w4 = vld1q_u32_at(W10000.as_slice(), 0);
    let t3 = vmulq_u32(p, w4);
    let r = vpaddlq_u32(t3);
    proof {
        assert forall|j: int| 0 <= j < 2 implies (#[trigger] u64s(n8(r))[j]) as int == a[2 * j] * 10000 + a[2 * j + 1] by {
            let b = u32s(n8(t3));
            assert(u64s(n8(r))[j] == paddl32(b)[j]);
            assert(u32s(n8(w4))[2 * j] == W10000@[2 * j] && u32s(n8(w4))[2 * j + 1] == W10000@[2 * j + 1]);
            assert(W10000@[2 * j] == 10000 && W10000@[2 * j + 1] == 1);
            assert(a[2 * j] <= 9999 && a[2 * j + 1] <= 9999);
            assert(b[2 * j] as int == (a[2 * j] * 10000) % 0x1_0000_0000);
            assert(b[2 * j + 1] as int == (a[2 * j + 1] * 1) % 0x1_0000_0000);
        }
    }
    r
}

/// The value of 16 lanes that hold digit values (0 to 9), most significant
/// first: three multiplies by place values, each followed by a widening
/// sum of adjacent lanes (to 2, 4 and 8 digits), then the two eight-digit
/// halves combined.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn digits_value16_neon(e: uint8x16_t) -> (r: u64)
    requires
        neon(),
        forall|k: int| 0 <= k < 16 ==> n8(e)[k] <= 9,
    ensures
        r as int == dlanes(n8(e), 16),
{
    let ghost ev = n8(e);
    let p2 = pairs16_neon(e);
    let ghost a2 = u16s(n8(p2));
    proof {
        assert forall|j: int| 0 <= j < 8 implies (#[trigger] a2[j]) <= 99 by {
            assert(ev[2 * j] <= 9 && ev[2 * j + 1] <= 9);
        }
    }
    let p4 = quads16_neon(p2);
    let ghost a4 = u32s(n8(p4));
    proof {
        assert forall|j: int| 0 <= j < 4 implies (#[trigger] a4[j]) as int == g4v(ev, 4 * j) && a4[j] <= 9999 by {
            assert(a2[2 * j] as int == ev[2 * (2 * j)] * 10 + ev[2 * (2 * j) + 1]);
            assert(a2[2 * j + 1] as int == ev[2 * (2 * j + 1)] * 10 + ev[2 * (2 * j + 1) + 1]);
            assert(ev[4 * j] <= 9 && ev[4 * j + 1] <= 9 && ev[4 * j + 2] <= 9 && ev[4 * j + 3] <= 9);
        }
    }
    let p8 = halves16_neon(p4);
    let ghost a8 = u64s(n8(p8));
    let hi = vgetq_lane_u64_0(p8);
    let lo = vgetq_lane_u64_1(p8);
    proof {
        assert(a4[0] as int == g4v(ev, 0) && a4[1] as int == g4v(ev, 4) && a4[2] as int == g4v(ev, 8) && a4[3] as int
            == g4v(ev, 12)) by {
            let (j0, j1, j2, j3) = (0int, 1int, 2int, 3int);
            assert(a4[j0] as int == g4v(ev, 4 * j0) && a4[j1] as int == g4v(ev, 4 * j1) && a4[j2] as int == g4v(ev, 4 * j2)
                && a4[j3] as int == g4v(ev, 4 * j3));
        }
        assert(a8[0] as int == a4[0] * 10000 + a4[1] && a8[1] as int == a4[2] * 10000 + a4[3]) by {
            let (j0, j1) = (0int, 1int);
            assert(a8[j0] as int == a4[2 * j0] * 10000 + a4[2 * j0 + 1]);
            assert(a8[j1] as int == a4[2 * j1] * 10000 + a4[2 * j1 + 1]);
        }
        assert(hi as int == g8v(ev, 0));
        assert(lo as int == g8v(ev, 8));
        assert(a4[0] <= 9999 && a4[1] <= 9999 && a4[2] <= 9999 && a4[3] <= 9999);
        lemma_dlanes16(ev);
    }
    hi * 100_000_000 + lo
}

/// `simd::digit_run_acc16` with NEON, with no branch on the run's length:
/// one classification gives the length `n`, a `tbl` moves the `n` digit
/// values to the end of the vector behind zeros, and `digits_value16_neon`
/// reads all 16 lanes.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn digit_run_acc16_neon(s: &[u8], i: usize) -> (r: (usize, u64))
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        r.0 <= 16,
        forall|q: int| i <= q < i + r.0 ==> is_digit_byte(#[trigger] s@[q]),
        r.0 < 16 ==> !is_digit_byte(s@[i + r.0]),
        r.1 as int == dval(s@, i as int, i + r.0),
{
    let v = vld1q_u8_at(s, i);
    // (v - '0') mod 256, at most 9 exactly on digits.
    let d = vaddq_u8(v, vdupq_n_u8(0xD0));
    let isd = vcleq_u8(d, vdupq_n_u8(9));
    proof {
        assert forall|k: int| 0 <= k < 16 implies (n8(isd)[k] == 0xFF || n8(isd)[k] == 0) && ((n8(isd)[k] == 0xFF)
            == is_digit_byte(#[trigger] s@[i + k])) && (is_digit_byte(s@[i + k]) ==> n8(d)[k] as int == s@[i + k]
            - 0x30) by {
            let c = s@[i + k];
            assert(n8(v)[k] == c);
            assert(n8(d)[k] as int == (c + 0xD0) % 256);
            assert(n8(isd)[k] == (if n8(d)[k] <= 9u8 { 0xFFu8 } else { 0u8 }));
            if c >= 0x30 {
                assert((c + 0xD0) % 256 == c - 0x30);
            } else {
                assert((c + 0xD0) % 256 == c + 0xD0);
            }
        }
        assert(is_mask(n8(isd)));
    }
    let n = lead_run16(isd, true);
    let sh = vld1q_u8_at(SHUF_TAIL.as_slice(), n);
    let e = vqtbl1q_u8(d, sh);
    let ghost ev = n8(e);
    let ghost z = 16 - n;
    proof {
        assert forall|q: int| i <= q < i + n implies is_digit_byte(#[trigger] s@[q]) by {
            let k = q - i;
            assert(is_digit_byte(s@[i + k]) == is_digit_byte(s@[q]));
            assert(n8(isd)[k] == 0xFF);
        }
        if n < 16 {
            assert(n8(isd)[n as int] != 0xFF);
            assert(!is_digit_byte(s@[i + n as int]));
        }
        assert forall|k: int| 0 <= k < 16 implies ev[k] == (if k < z { 0u8 } else { n8(d)[k - z] }) by {
            assert(n8(sh)[k] == SHUF_TAIL@[n + k]);
        }
        assert forall|k: int| 0 <= k < 16 implies ev[k] <= 9 by {
            if k >= z {
                assert(n8(isd)[k - z] == 0xFF);
                assert(is_digit_byte(s@[i + (k - z)]));
            }
        }
        assert forall|k: int| 0 <= k < n implies (#[trigger] ev[z + k]) as int == s@[i + k] - 0x30 by {
            assert(n8(isd)[k] == 0xFF);
            assert(is_digit_byte(s@[i + k]));
        }
    }
    let r = digits_value16_neon(e);
    proof {
        let dv = Seq::new(n as nat, |k: int| ev[z + k]);
        lemma_dlanes_lead(ev, dv, z, n as int);
        lemma_dlanes_dval(dv, s@, i as int, n as int);
    }
    (n, r)
}

/// `simd::copy_plain16` with NEON.
#[inline(always)]
pub fn copy_plain16_neon(s: &[u8], i: usize, end: usize, out: &mut Vec<u8>) -> (r: usize)
    requires
        neon(),
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
    let v = vld1q_u8_at(s, i);
    let p = plain_run16_neon(s, i);
    let r = if p < end - i { p } else { end - i };
    append16_spare_neon(out, v, r);
    assert(n8(v).subrange(0, r as int) =~= s@.subrange(i as int, i + r));
    r
}

/// The number of leading bytes of the mask `a` that are 0xFF (`ff`) or
/// 0x00 (`!ff`), from its nibble mask: `shrn`, `fmov` and a count, where
/// `movemask16` and `first_set16` take about a dozen instructions.
#[inline(always)]
pub fn lead_run16(a: uint8x16_t, ff: bool) -> (r: usize)
    requires
        neon(),
        is_mask(n8(a)),
    ensures
        r <= 16,
        forall|k: int| 0 <= k < r ==> ((n8(a)[k] == 0xFF) == ff),
        r < 16 ==> ((n8(a)[r as int] == 0xFF) != ff),
{
    let n = nibmask16(a);
    let z = if ff { !n } else { n };
    let tz = z.trailing_zeros();
    proof {
        vstd::std_specs::bits::axiom_u64_trailing_zeros(z);
        assert forall|k: int| 0 <= k < tz / 4 implies ((n8(a)[k] == 0xFF) == ff) by {
            let j = (4 * k) as u64;
            assert(j < tz);
            assert((z >> j) & 1 == 0);
            lemma_nibmask_bit(n, n8(a), j);
            assert(j / 4 == k);
            assert(j < 64 ==> ((((!n) >> j) & 1 == 0) == ((n >> j) & 1 == 1))) by (bit_vector);
        }
        if tz < 64 {
            let j = tz as u64;
            assert((z >> j) & 1 == 1);
            lemma_nibmask_bit(n, n8(a), j);
            assert(j < 64 ==> ((((!n) >> j) & 1 == 1) == ((n >> j) & 1 == 0))) by (bit_vector);
        }
    }
    (tz / 4) as usize
}

/// `simd::plain_run16` with NEON.
#[inline(always)]
pub fn plain_run16_neon(s: &[u8], i: usize) -> (r: usize)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> plain(#[trigger] s@[q]),
        r < 16 ==> !plain(s@[i + r]),
{
    let m = special_vec_neon(s, i);
    let r = lead_run16(m, false);
    proof {
        assert forall|q: int| i <= q < i + r implies plain(#[trigger] s@[q]) by {
            let k = q - i;
            assert(plain(s@[i + k]) == plain(s@[q]));
            assert(n8(m)[k] != 0xFF);
        }
    }
    r
}

/// `simd::ws_run16` with NEON.
#[inline(always)]
pub fn ws_run16_neon(s: &[u8], i: usize) -> (r: usize)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> is_ws(#[trigger] s@[q]),
        r < 16 ==> !is_ws(s@[i + r]),
{
    let m = ws_vec_neon(s, i);
    let r = lead_run16(m, true);
    proof {
        assert forall|q: int| i <= q < i + r implies is_ws(#[trigger] s@[q]) by {
            let k = q - i;
            assert(is_ws(s@[i + k]) == is_ws(s@[q]));
            assert(n8(m)[k] == 0xFF);
        }
    }
    r
}

/// `simd::digit_run16` with NEON.
#[inline(always)]
pub fn digit_run16_neon(s: &[u8], i: usize) -> (r: usize)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> is_digit_byte(#[trigger] s@[q]),
        r < 16 ==> !is_digit_byte(s@[i + r]),
{
    let m = digit_vec_neon(s, i);
    let r = lead_run16(m, true);
    proof {
        assert forall|q: int| i <= q < i + r implies is_digit_byte(#[trigger] s@[q]) by {
            let k = q - i;
            assert(is_digit_byte(s@[i + k]) == is_digit_byte(s@[q]));
            assert(n8(m)[k] == 0xFF);
        }
    }
    r
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use crate::index::structural_index;

    /// Every byte value in every lane, against varied neighbours.
    #[test]
    fn classify64_neon_agrees() {
        let mut buf = vec![0u8; 128];
        for fill in [0u8, 0x20, b'a', b'"', 0x80, 0xFF] {
            for lane in 0..64 {
                for c in 0..=255u8 {
                    buf.iter_mut().for_each(|b| *b = fill);
                    buf[3 + lane] = c;
                    let want = classify64::<SCALAR>(&buf, 3);
                    let got = classify64::<NEON>(&buf, 3);
                    assert_eq!(
                        (got.quote, got.backslash, got.ws, got.op, got.ctrl),
                        (want.quote, want.backslash, want.ws, want.op, want.ctrl),
                        "fill {fill:#x} lane {lane} byte {c:#x}"
                    );
                }
            }
        }
    }

    /// The stage-2 scanners against byte-by-byte definitions, for every
    /// byte value in every lane and digit runs of every length.
    #[test]
    fn stage2_scanners_agree() {
        let plain = |c: u8| c != 0x22 && c != 0x5C && c >= 0x20;
        let ws = |c: u8| matches!(c, 0x20 | 0x0A | 0x0D | 0x09);
        let mut buf = vec![0u8; 40];
        for fill in [b'0', b'5', b'a', 0x20, 0x80, 0xFF] {
            for lane in 0..16 {
                for c in 0..=255u8 {
                    buf.iter_mut().for_each(|b| *b = fill);
                    buf[3 + lane] = c;
                    let w = &buf[3..19];
                    let m = |f: &dyn Fn(u8) -> bool| (0..16).filter(|&k| f(w[k])).fold(0u32, |m, k| m | 1 << k);
                    assert_eq!(classify_special_neon(&buf, 3), m(&|c| !plain(c)));
                    assert_eq!(classify_non_ws_neon(&buf, 3), m(&|c| !ws(c)));
                    assert_eq!(classify_non_digit_neon(&buf, 3), m(&|c| !c.is_ascii_digit()));
                    let n = w.iter().take_while(|c| c.is_ascii_digit()).count();
                    let v = w[..n].iter().fold(0u64, |v, &c| v * 10 + (c - b'0') as u64);
                    assert_eq!(digit_run_acc16_neon(&buf, 3), (n, v));
                    for end in [3, 10, 19, 40] {
                        let mut out = Vec::with_capacity(64);
                        out.extend_from_slice(b"xy");
                        let r = copy_plain16_neon(&buf, 3, end, &mut out);
                        let want = buf[3..end.min(19)].iter().take_while(|&&c| plain(c)).count();
                        assert_eq!(r, want);
                        assert_eq!(&out[2..], &buf[3..3 + r]);
                    }
                }
            }
        }
    }

    fn texts() -> Vec<Vec<u8>> {
        let mut x: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let alphabet = b"[]{},:\"\\ \t\n0123456789.eEtrufalsnx\x01";
        let utf8 = ["\u{e9}", "\u{20ac}", "\u{1f600}", "\u{7ff}", "\u{ffff}"];
        let mut out = Vec::new();
        for len in 0..600 {
            for _ in 0..8 {
                let mut d = Vec::with_capacity(len + 4);
                while d.len() < len {
                    let r = next();
                    if r % 23 == 0 {
                        d.extend_from_slice(utf8[(r >> 8) as usize % utf8.len()].as_bytes());
                    } else if r % 97 == 0 {
                        // A stray continuation or lead byte.
                        d.push(0x80 | (r >> 16) as u8);
                    } else {
                        d.push(alphabet[(r >> 8) as usize % alphabet.len()]);
                    }
                }
                out.push(d);
            }
        }
        out
    }

    #[test]
    fn structural_index_neon_agrees() {
        for d in texts() {
            let (mut a, mut b) = (Vec::new(), Vec::new());
            let ra = structural_index::<SCALAR>(&d, 0, &mut a);
            let rb = structural_index::<NEON>(&d, 0, &mut b);
            assert_eq!((ra.1, ra.2), (rb.1, rb.2));
            assert_eq!(rb.2, std::str::from_utf8(&d).is_ok());
            assert_eq!(a[..ra.0], b[..rb.0]);
        }
    }

    #[test]
    fn utf8_neon_agrees() {
        for d in texts() {
            for st in [0, 1.min(d.len())] {
                let (uj, ok) = crate::utf8::utf8_start(&d, st);
                let got = crate::utf8::utf8_finish::<NEON>(&d, st, uj, ok);
                assert_eq!(got, std::str::from_utf8(&d[st..]).is_ok(), "len {} st {st}", d.len());
            }
        }
    }
}
