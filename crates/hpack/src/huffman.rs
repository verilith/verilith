//! The verified Huffman decoder (RFC 7541 §5.2).
//!
//! Decoding reads bits into a 64-bit window and, for each length `l` from
//! the shortest up, compares the next `l` bits with the range of codes of
//! that length. That works because the code is canonical: the codes of
//! length `l` are `FIRST[l]`, `FIRST[l] + 1`, ..., `FIRST[l] + CNT[l] - 1`,
//! given in symbol order by `SYMS[OFF[l]..]`. Those four arrays are not
//! trusted: `check` verifies at run time, against the RFC table
//! (`HUFF_CODE`, `HUFF_LEN`), that they describe it exactly, and the
//! decoder is proven correct given that they do (`layout_ok`).
use crate::bits::*;
use crate::htables::*;
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/// The canonical layout describes the RFC table.
pub open spec fn layout_ok() -> bool {
    &&& forall|l: int|
        1 <= l <= 30 ==> #[trigger] OFF@[l] + CNT@[l] <= 257 && FIRST@[l] + CNT@[l] <= 0x8000_0000
    &&& forall|l: int, i: int|
        1 <= l <= 30 && 0 <= i < CNT@[l] ==> {
            let s = #[trigger] SYMS@[OFF@[l] + i] as int;
            s < 257 && hlen(s) == l && hcode(s) == FIRST@[l] + i
        }
    &&& forall|s: int|
        0 <= s < 257 ==> {
            let l = #[trigger] hlen(s) as int;
            &&& 5 <= l <= 30
            &&& FIRST@[l] <= hcode(s) < FIRST@[l] + CNT@[l]
            &&& SYMS@[OFF@[l] + hcode(s) - FIRST@[l]] == s
        }
}

/// Checks `layout_ok` (once, when a decoder is made).
#[verifier::rlimit(30)]
pub fn check() -> (r: bool)
    ensures
        r ==> layout_ok(),
{
    let mut l: usize = 1;
    while l <= 30
        invariant
            1 <= l <= 31,
            forall|k: int| 1 <= k < l ==> #[trigger] OFF@[k] + CNT@[k] <= 257 && FIRST@[k] + CNT@[k] <= 0x8000_0000,
            forall|k: int, i: int|
                1 <= k < l && 0 <= i < CNT@[k] ==> {
                    let s = #[trigger] SYMS@[OFF@[k] + i] as int;
                    s < 257 && hlen(s) == k && hcode(s) == FIRST@[k] + i
                },
        decreases 31 - l,
    {
        let off = OFF[l];
        let cnt = CNT[l];
        let first = FIRST[l];
        if off > 257 || cnt > 257 - off || first > 0x8000_0000 || cnt > 0x8000_0000 - first {
            return false;
        }
        let mut i: u32 = 0;
        while i < cnt
            invariant
                1 <= l <= 30,
                off == OFF@[l as int],
                cnt == CNT@[l as int],
                first == FIRST@[l as int],
                off + cnt <= 257,
                first + cnt <= 0x8000_0000,
                i <= cnt,
                forall|j: int|
                    0 <= j < i ==> {
                        let s = #[trigger] SYMS@[off + j] as int;
                        s < 257 && hlen(s) == l && hcode(s) == first + j
                    },
            decreases cnt - i,
        {
            let s = SYMS[(off + i) as usize];
            if s >= 257 || HUFF_LEN[s as usize] as usize != l || HUFF_CODE[s as usize] != first + i {
                return false;
            }
            i = i + 1;
        }
        l = l + 1;
    }
    let mut s: usize = 0;
    while s < 257
        invariant
            s <= 257,
            forall|k: int| 1 <= k <= 30 ==> #[trigger] OFF@[k] + CNT@[k] <= 257 && FIRST@[k] + CNT@[k] <= 0x8000_0000,
            forall|t: int|
                0 <= t < s ==> {
                    let l = #[trigger] hlen(t) as int;
                    &&& 5 <= l <= 30
                    &&& FIRST@[l] <= hcode(t) < FIRST@[l] + CNT@[l]
                    &&& SYMS@[OFF@[l] + hcode(t) - FIRST@[l]] == t
                },
        decreases 257 - s,
    {
        let l = HUFF_LEN[s] as usize;
        if l < 5 || l > 30 {
            return false;
        }
        let c = HUFF_CODE[s];
        if c < FIRST[l] || c - FIRST[l] >= CNT[l] {
            return false;
        }
        if SYMS[(OFF[l] + (c - FIRST[l])) as usize] as usize != s {
            return false;
        }
        s = s + 1;
    }
    true
}

/// Under `layout_ok`, a code of length `l` with value `v` exists iff `v` is
/// in the range for `l`, and its symbol is the one at the matching place.
pub proof fn lemma_match(l: nat, v: nat)
    requires
        layout_ok(),
        1 <= l <= 30,
    ensures
        hmatch(l, v) <==> (FIRST@[l as int] <= v < FIRST@[l as int] + CNT@[l as int]),
        hmatch(l, v) ==> hsym(l, v) == SYMS@[OFF@[l as int] + v - FIRST@[l as int]] as int,
{
    let li = l as int;
    if FIRST@[li] <= v < FIRST@[li] + CNT@[li] {
        let i = v - FIRST@[li];
        let s = SYMS@[OFF@[li] + i] as int;
        assert(s < 257 && hlen(s) == l && hcode(s) == v);
        assert(hmatch(l, v));
    }
    if hmatch(l, v) {
        let s = hsym(l, v);
        assert(0 <= s < 257 && hlen(s) == l && hcode(s) == v);
        assert(FIRST@[li] <= hcode(s) < FIRST@[li] + CNT@[li]);
        assert(SYMS@[OFF@[li] + hcode(s) - FIRST@[li]] == s);
    }
}

/// The decoding window: `nb` bits of `b` from bit `8 * i - nb`.
pub open spec fn window(b: Seq<u8>, i: usize, acc: u64, nb: u64) -> bool {
    &&& i <= b.len()
    &&& nb <= 64
    &&& nb <= 8 * i
    &&& acc < pow2(nb as nat)
    &&& acc == code(b, 8 * i - nb, nb as nat)
}

/// Adds the 4 bytes at `b[i]` to a window of fewer than 33 bits.
#[inline(always)]
fn refill4(b: &[u8], i: usize, acc: u64, nb: u64, buf: u64) -> (r: (usize, u64, u64, u64))
    requires
        window(b@, i, acc, nb),
        aligned(acc, nb, buf),
        nb <= 32,
        i + 4 <= b@.len(),
    ensures
        window(b@, r.0, r.1, r.2),
        aligned(r.1, r.2, r.3),
        8 * r.0 - r.2 == 8 * i - nb,
        r.2 == nb + 32,
        r.0 == i + 4,
{
    let ghost bs = b@;
    let ghost p = 8 * i - nb;
    let _n = b.len();
    let x0 = verilith_core::prims::get(b, i) as u64;
    let x1 = verilith_core::prims::get(b, i + 1) as u64;
    let x2 = verilith_core::prims::get(b, i + 2) as u64;
    let x3 = verilith_core::prims::get(b, i + 3) as u64;
    let w = (x0 << 24u64) | (x1 << 16u64) | (x2 << 8u64) | x3;
    proof {
        lemma2_to64();
        lemma2_to64_rest();
        lemma_code_push(bs, p, nb as nat, i as int);
        lemma_code_push(bs, p, (nb + 8) as nat, i + 1);
        lemma_code_push(bs, p, (nb + 16) as nat, i + 2);
        lemma_code_push(bs, p, (nb + 24) as nat, i + 3);
        assert(w == x0 * 0x100_0000 + x1 * 0x1_0000 + x2 * 0x100 + x3 && w < 0x1_0000_0000) by (bit_vector)
            requires
                w == (x0 << 24u64) | (x1 << 16u64) | (x2 << 8u64) | x3,
                x0 < 256,
                x1 < 256,
                x2 < 256,
                x3 < 256,
        ;
        lemma_pow2_adds(nb as nat, 32);
        assert(acc * 0x1_0000_0000 + 0x1_0000_0000 <= pow2(nb as nat) * 0x1_0000_0000) by (nonlinear_arith)
            requires
                acc + 1 <= pow2(nb as nat),
        ;
        lemma_pow2_strictly_increases((nb + 32) as nat, 65);
        lemma_u64_shl_is_mul(acc, 32);
        assert((acc << 32u64) | w == (acc << 32u64) + w) by (bit_vector)
            requires
                w < 0x1_0000_0000,
        ;
        assert(code(bs, p, (nb + 32) as nat) == acc * 0x1_0000_0000 + w) by (nonlinear_arith)
            requires
                code(bs, p, (nb + 8) as nat) == code(bs, p, nb as nat) * 256 + x0,
                code(bs, p, (nb + 16) as nat) == code(bs, p, (nb + 8) as nat) * 256 + x1,
                code(bs, p, (nb + 24) as nat) == code(bs, p, (nb + 16) as nat) * 256 + x2,
                code(bs, p, (nb + 32) as nat) == code(bs, p, (nb + 24) as nat) * 256 + x3,
                code(bs, p, nb as nat) == acc,
                w == x0 * 0x100_0000 + x1 * 0x1_0000 + x2 * 0x100 + x3,
        ;
    }
    proof {
        lemma_bound_bv(acc, nb);
        assert(w >> 32u64 == 0) by (bit_vector)
            requires
                w < 0x1_0000_0000,
        ;
        lemma_al_push(acc, nb, buf, w, 32);
    }
    ((i + 4), (acc << 32u64) | w, nb + 32, buf | (w << ((32 - nb) as u64)))
}

/// Refills the window to more than 56 bits, or to the end of `b`.
fn refill(b: &[u8], i: usize, acc: u64, nb: u64, buf: u64) -> (r: (usize, u64, u64, u64))
    requires
        window(b@, i, acc, nb),
        aligned(acc, nb, buf),
    ensures
        window(b@, r.0, r.1, r.2),
        aligned(r.1, r.2, r.3),
        8 * r.0 - r.2 == 8 * i - nb,
        r.2 > 56 || r.0 == b@.len(),
{
    let ghost bs = b@;
    let n = b.len();
    let mut i = i;
    let mut acc = acc;
    let mut nb = nb;
    let mut buf = buf;
    let ghost p0 = 8 * i - nb;
    while nb <= 56 && i < n
        invariant
            n == b@.len(),
            bs == b@,
            window(bs, i, acc, nb),
            aligned(acc, nb, buf),
            8 * i - nb == p0,
        decreases n - i,
    {
        let ghost p = 8 * i - nb;
        let x = b[i];
        proof {
            lemma_bound_bv(acc, nb);
            assert((x as u64) >> 8u64 == 0) by (bit_vector);
            lemma_al_push(acc, nb, buf, x as u64, 8);
        }
        buf = buf | ((x as u64) << ((56 - nb) as u64));
        proof {
            lemma_code_push(bs, p, nb as nat, i as int);
            lemma_pow2_adds(nb as nat, 8);
            lemma2_to64();
            assert(acc * 256 + 256 <= pow2(nb as nat) * 256) by (nonlinear_arith)
                requires
                    acc + 1 <= pow2(nb as nat),
            ;
            if nb + 8 < 64 {
                lemma_pow2_strictly_increases((nb + 8) as nat, 64);
            }
            lemma2_to64_rest();
            lemma_u64_shl_is_mul(acc, 8);
            assert((acc << 8u64) | (x as u64) == (acc << 8u64) + (x as u64)) by (bit_vector)
                requires
                    x < 256,
            ;
        }
        acc = (acc << 8) | (x as u64);
        nb = nb + 8;
        i = i + 1;
    }
    (i, acc, nb, buf)
}

/// `buf` is the window `acc` of `nb` bits, moved to the top of 64 bits
/// (the decoder works on `buf`; `acc` is for the proofs).
pub open spec fn aligned(acc: u64, nb: u64, buf: u64) -> bool {
    if nb == 0 {
        buf == 0
    } else {
        nb <= 64 && buf == acc << ((64 - nb) as u64)
    }
}

proof fn lemma_bound_bv(acc: u64, nb: u64)
    requires
        nb <= 64,
        acc < pow2(nb as nat),
    ensures
        nb == 64 || acc >> nb == 0,
{
    if nb < 64 {
        lemma2_to64();
        lemma2_to64_rest();
        lemma_u64_shr_is_div(acc, nb);
        lemma_pow2_pos(nb as nat);
        vstd::arithmetic::div_mod::lemma_basic_div(acc as int, pow2(nb as nat) as int);
    }
}

/// Adding `k` bits `w` below the window.
proof fn lemma_al_push(acc: u64, nb: u64, buf: u64, w: u64, k: u64)
    requires
        aligned(acc, nb, buf),
        nb == 64 || acc >> nb == 0,
        k == 8 || k == 32,
        nb + k <= 64,
        w >> k == 0,
    ensures
        aligned((acc << k) | w, (nb + k) as u64, buf | (w << ((64 - nb - k) as u64))),
{
    let s = (64 - nb - k) as u64;
    if nb == 0 {
        assert(acc == 0) by (bit_vector)
            requires
                acc >> nb == 0,
                nb == 0,
        ;
        assert(0u64 | (w << s) == ((0u64 << k) | w) << s) by (bit_vector);
    } else {
        assert(buf | (w << s) == ((acc << k) | w) << s) by (bit_vector)
            requires
                buf == acc << ((64 - nb) as u64),
                acc >> nb == 0,
                1 <= nb,
                nb + k <= 64,
                k == 8 || k == 32,
                w >> k == 0,
                s == 64 - nb - k,
        ;
    }
}

/// The top `l` bits of the window.
proof fn lemma_al_top(acc: u64, nb: u64, buf: u64, l: u64)
    requires
        aligned(acc, nb, buf),
        nb == 64 || acc >> nb == 0,
        1 <= l <= nb,
    ensures
        buf >> ((64 - l) as u64) == acc >> ((nb - l) as u64),
{
    let a = (64 - nb) as u64;
    let c = (nb - l) as u64;
    lemma2_to64();
    lemma2_to64_rest();
    if nb < 64 {
        lemma_u64_shr_is_div(acc, nb);
        lemma_pow2_pos(nb as nat);
    }
    assert(acc < pow2(nb as nat)) by {
        if nb < 64 {
            assert(acc / (pow2(nb as nat) as u64) == 0);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(acc as int, pow2(nb as nat) as int);
        } else {
            assert(acc <= 0xFFFF_FFFF_FFFF_FFFF);
        }
    }
    lemma_pow2_adds(nb as nat, a as nat);
    assert(acc * pow2(a as nat) < pow2(64)) by (nonlinear_arith)
        requires
            acc < pow2(nb as nat),
            pow2(nb as nat) * pow2(a as nat) == pow2(64),
            pow2(a as nat) > 0,
    ;
    lemma_pow2_pos(a as nat);
    lemma_u64_shl_is_mul(acc, a);
    lemma_u64_shr_is_div(buf, (64 - l) as u64);
    lemma_u64_shr_is_div(acc, c);
    lemma_pow2_adds(a as nat, c as nat);
    lemma_pow2_pos(c as nat);
    // buf / 2^(a + c) == (acc * 2^a) / 2^a / 2^c == acc / 2^c.
    vstd::arithmetic::div_mod::lemma_div_denominator((acc * pow2(a as nat)) as int, pow2(a as nat) as int, pow2(c as nat) as int);
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(acc as int, pow2(a as nat) as int);
    assert(buf as int == acc * pow2(a as nat));
    assert((64 - l) as nat == a + c);
    let pa = pow2(a as nat) as int;
    let pc = pow2(c as nat) as int;
    assert(pow2((64 - l) as nat) as int == pa * pc);
    assert((buf as int) / (pa * pc) == ((buf as int) / pa) / pc);
    vstd::arithmetic::mul::lemma_mul_is_commutative(acc as int, pa);
    assert((buf as int) / pa == acc as int);
    assert((buf >> ((64 - l) as u64)) as int == (buf as int) / pow2((64 - l) as nat) as int);
    assert((acc >> c) as int == (acc as int) / pc);
}

/// Taking `l` bits off the top of the window.
proof fn lemma_al_take(acc: u64, nb: u64, buf: u64, l: u64)
    requires
        aligned(acc, nb, buf),
        nb == 64 || acc >> nb == 0,
        1 <= l <= nb,
        l < 64,
    ensures
        aligned((acc - ((acc >> ((nb - l) as u64)) << ((nb - l) as u64))) as u64, (nb - l) as u64, buf << l),
{
    let r = (nb - l) as u64;
    let a2 = (acc - ((acc >> r) << r)) as u64;
    assert((acc >> r) << r <= acc) by (bit_vector)
        requires
            r < 64,
    ;
    if r == 0 {
        assert(buf << l == 0) by (bit_vector)
            requires
                buf == acc << ((64 - nb) as u64),
                nb == 64 || acc >> nb == 0,
                l == nb,
                1 <= l,
                l < 64,
        ;
    } else {
        assert(buf << l == a2 << ((64 - r) as u64)) by (bit_vector)
            requires
                buf == acc << ((64 - nb) as u64),
                nb == 64 || acc >> nb == 0,
                r == nb - l,
                1 <= r,
                1 <= l,
                l < 64,
                nb <= 64,
                a2 == (acc - ((acc >> r) << r)) as u64,
                (acc >> r) << r <= acc,
        ;
    }
}

/// The window is `nb` (at most 7) one bits.
proof fn lemma_al_pad(acc: u64, nb: u64, buf: u64)
    requires
        aligned(acc, nb, buf),
        acc >> nb == 0,
        1 <= nb <= 7,
    ensures
        (acc + 1 == (1u64 << nb)) == (buf == (0xFFFF_FFFF_FFFF_FFFFu64 << ((64 - nb) as u64))),
{
    assert((acc + 1 == (1u64 << nb)) == (buf == (0xFFFF_FFFF_FFFF_FFFFu64 << ((64 - nb) as u64)))) by (bit_vector)
        requires
            buf == acc << ((64 - nb) as u64),
            acc >> nb == 0,
            1 <= nb,
            nb <= 7,
    ;
}

// ---------------------------------------------------------------------------
// The decoding table: for each 12-bit prefix, the one or two codes it
// starts with (built and proven once, `dtab`).
// ---------------------------------------------------------------------------

/// The `w` bits `x` do not start with a code of length `k`.
pub open spec fn nm(x: int, w: int, k: int) -> bool {
    !hmatch(k as nat, (x / (pow2((w - k) as nat) as int)) as nat)
}

/// The shortest code at the start of the `w` bits `x` has length `l` and
/// symbol `s`.
pub open spec fn fm(x: int, w: int, l: int, s: int) -> bool {
    &&& 1 <= l <= w
    &&& hmatch(l as nat, (x / (pow2((w - l) as nat) as int)) as nat)
    &&& hsym(l as nat, (x / (pow2((w - l) as nat) as int)) as nat) == s
    &&& forall|k: int| 1 <= k < l ==> #[trigger] nm(x, w, k)
}

/// An entry's fields: total length (bits 0 to 5, so the entry itself is
/// the count of a 64-bit shift by it), kind (6 and 7), first code's length
/// (8 to 11), symbols (16 to 23, 24 to 31).
pub open spec fn ek(e: u32) -> u32 {
    (e >> 6u32) & 3
}

pub open spec fn el1(e: u32) -> u32 {
    (e >> 8u32) & 15
}

pub open spec fn elt(e: u32) -> u32 {
    e & 63
}

pub open spec fn es1(e: u32) -> u32 {
    (e >> 16u32) & 255
}

pub open spec fn es2(e: u32) -> u32 {
    e >> 24u32
}

/// Entry `e` for the 12 bits `x`. Kind 1: one code (`el1` bits, symbol
/// `es1`); kind 2: two (`elt` bits in all, then `es2`); kind 0: no code of
/// at most 12 bits; kind 3: no claim.
pub open spec fn dentry(x: int, e: u32) -> bool {
    &&& ek(e) == 0 ==> forall|k: int| 1 <= k <= 12 ==> #[trigger] nm(x, 12, k)
    &&& (ek(e) == 1 || ek(e) == 2) ==> fm(x, 12, el1(e) as int, es1(e) as int)
    &&& ek(e) == 1 ==> elt(e) == el1(e)
    &&& ek(e) == 2 ==> {
        &&& el1(e) < elt(e) <= 12
        &&& fm(x % (pow2((12 - el1(e)) as nat) as int), 12 - el1(e), elt(e) - el1(e), es2(e) as int)
    }
}

pub open spec fn dtab_ok(t: Seq<u32>) -> bool {
    &&& t.len() == 4096
    &&& forall|x: int| 0 <= x < 4096 ==> dentry(x, #[trigger] t[x])
}

/// The shortest code at the start of the `w` bits `x`.
fn first(x: u64, w: u64) -> (r: Option<(u16, u64)>)
    requires
        layout_ok(),
        1 <= w <= 12,
        x < 4096,
    ensures
        match r {
            Some((s, l)) => fm(x as int, w as int, l as int, s as int) && s < 257 && 1 <= l <= w,
            None => forall|k: int| 1 <= k <= w ==> #[trigger] nm(x as int, w as int, k),
        },
{
    let mut l: u64 = 1;
    while l <= w
        invariant
            1 <= l <= w + 1,
            1 <= w <= 12,
            x < 4096,
            layout_ok(),
            forall|k: int| 1 <= k < l ==> #[trigger] nm(x as int, w as int, k),
        decreases w + 1 - l,
    {
        let v = x >> (w - l);
        proof {
            lemma_u64_shr_is_div(x, (w - l) as u64);
            lemma_match(l as nat, v as nat);
        }
        let li = l as usize;
        if v >= FIRST[li] as u64 && v - (FIRST[li] as u64) < CNT[li] as u64 {
            let s = SYMS[(OFF[li] + (v as u32 - FIRST[li])) as usize];
            return Some((s, l));
        }
        l = l + 1;
    }
    None
}

fn mk(k: u32, l1: u32, lt: u32, s1: u32, s2: u32) -> (e: u32)
    requires
        k < 4,
        l1 < 16,
        lt < 16,
        s1 < 256,
        s2 < 256,
    ensures
        ek(e) == k,
        el1(e) == l1,
        elt(e) == lt,
        es1(e) == s1,
        es2(e) == s2,
{
    let e = lt | (k << 6u32) | (l1 << 8u32) | (s1 << 16u32) | (s2 << 24u32);
    assert((e >> 6u32) & 3 == k && (e >> 8u32) & 15 == l1 && e & 63 == lt && (e >> 16u32) & 255 == s1 && e
        >> 24u32 == s2) by (bit_vector)
        requires
            e == lt | (k << 6u32) | (l1 << 8u32) | (s1 << 16u32) | (s2 << 24u32),
            k < 4,
            l1 < 16,
            lt < 16,
            s1 < 256,
            s2 < 256,
    ;
    e
}

/// The table entry for the 12 bits `x`.
fn dentry_for(x: u64) -> (e: u32)
    requires
        layout_ok(),
        x < 4096,
    ensures
        dentry(x as int, e),
{
    let e: u32 = match first(x, 12) {
            None => {
                let e = mk(0, 0, 0, 0, 0);
                e
            },
            Some((s1, l1)) => {
                if s1 >= 256 {
                    mk(3, 0, 0, 0, 0)
                } else if l1 == 12 {
                    mk(1, l1 as u32, l1 as u32, s1 as u32, 0)
                } else {
                    let w2 = 12 - l1;
                    proof {
                        lemma2_to64();
                        lemma_u64_shl_is_mul(1, w2);
                        lemma_pow2_pos(w2 as nat);
                    }
                    let y = x % (1u64 << w2);
                    match first(y, w2) {
                        Some((s2, l2)) => {
                            if s2 < 256 {
                                mk(2, l1 as u32, (l1 + l2) as u32, s1 as u32, s2 as u32)
                            } else {
                                mk(1, l1 as u32, l1 as u32, s1 as u32, 0)
                            }
                        },
                        None => mk(1, l1 as u32, l1 as u32, s1 as u32, 0),
                    }
                }
            },
        };
    e
}

/// Builds the decoding table.
pub fn build_dtab() -> (t: Vec<u32>)
    requires
        layout_ok(),
    ensures
        dtab_ok(t@),
{
    let mut t: Vec<u32> = Vec::with_capacity(4096);
    let mut x: u64 = 0;
    while x < 4096
        invariant
            x <= 4096,
            t@.len() == x,
            layout_ok(),
            forall|y: int| 0 <= y < x ==> dentry(y, #[trigger] t@[y]),
        decreases 4096 - x,
    {
        let e = dentry_for(x);
        t.push(e);
        x = x + 1;
    }
    t
}

/// The decoding table, built once, or `None` if the canonical layout check
/// fails (it does not: see tests/tables.rs). Trusted: that `OnceLock`
/// returns what the closure computed.
#[verifier::external_body]
pub fn dtab() -> (r: Option<&'static [u32]>)
    ensures
        r matches Some(t) ==> dtab_ok(t@) && layout_ok(),
{
    static T: std::sync::OnceLock<Option<Vec<u32>>> = std::sync::OnceLock::new();
    T.get_or_init(|| if check() { Some(build_dtab()) } else { None }).as_deref()
}

pub open spec fn nomatch(b: Seq<u8>, p: int, r: nat, l: nat) -> bool {
    l <= 30 && l <= r && !hmatch(l, code(b, p, l))
}

/// `hfind` skips lengths that do not match.
proof fn lemma_hfind_skip(b: Seq<u8>, p: int, r: nat, a: nat, l0: nat)
    requires
        a <= l0,
        forall|l: nat| a <= l < l0 ==> #[trigger] nomatch(b, p, r, l),
    ensures
        hfind(b, p, r, a) == hfind(b, p, r, l0),
    decreases l0 - a,
{
    if a < l0 {
        assert(nomatch(b, p, r, a));
        lemma_hfind_skip(b, p, r, (a + 1) as nat, l0);
    }
}

/// A table claim about the next `w` bits is a claim about `hfind`.
proof fn lemma_fm_hfind(b: Seq<u8>, p: int, r: nat, x: int, w: nat, l: int, s: int)
    requires
        fm(x, w as int, l, s),
        x == code(b, p, w),
        w <= r,
        w <= 30,
    ensures
        hfind(b, p, r, 1) == Some((s, l as nat)),
{
    assert forall|k: nat| 1 <= k < l implies #[trigger] nomatch(b, p, r, k) by {
        lemma_code_top(b, p, w, k);
        assert(nm(x, w as int, k as int));
    }
    lemma_hfind_skip(b, p, r, 1, l as nat);
    lemma_code_top(b, p, w, l as nat);
}

/// No code of at most 12 bits: `hfind` can start at 13.
proof fn lemma_nm_skip(b: Seq<u8>, p: int, r: nat, x: int)
    requires
        forall|k: int| 1 <= k <= 12 ==> #[trigger] nm(x, 12, k),
        x == code(b, p, 12),
        12 <= r,
    ensures
        hfind(b, p, r, 1) == hfind(b, p, r, 13),
{
    assert forall|k: nat| 1 <= k < 13 implies #[trigger] nomatch(b, p, r, k) by {
        lemma_code_top(b, p, 12, k);
        assert(nm(x, 12, k as int));
    }
    lemma_hfind_skip(b, p, r, 1, 13);
}

/// One decoded symbol.
proof fn lemma_hdec_step(b: Seq<u8>, p: int, s: int, l: nat)
    requires
        0 <= p,
        1 <= l,
        p + l <= 8 * b.len(),
        hfind(b, p, (8 * b.len() - p) as nat, 1) == Some((s, l)),
        s < 256,
    ensures
        hdec(b, p) == match hdec(b, p + l) {
            Some(t) => Some(seq![s as u8] + t),
            None => None::<Seq<u8>>,
        },
{
}

/// Drops the first `l` bits of the window.
#[inline(always)]
fn take(acc: u64, nb: u64, l: u64, Ghost(b): Ghost<Seq<u8>>, Ghost(i): Ghost<usize>) -> (r: (u64, u64))
    requires
        window(b, i, acc, nb),
        1 <= l <= nb,
    ensures
        window(b, i, r.0, r.1),
        r.1 == nb - l,
        r.0 == (acc - ((acc >> ((nb - l) as u64)) << ((nb - l) as u64))) as u64,
{
    let ghost p = 8 * i - nb;
    let rest = nb - l;
    let top = acc >> rest;
    proof {
        lemma2_to64();
        lemma_u64_shr_is_div(acc, rest);
        lemma_code_top(b, p, nb as nat, l as nat);
        lemma_pow2_pos(rest as nat);
        lemma_fundamental_div_mod(acc as int, pow2(rest as nat) as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(top as int, pow2(rest as nat) as int);
        lemma_u64_shl_is_mul(top, rest);
        lemma_code_bound(b, p + l, rest as nat);
    }
    (acc - (top << rest), rest)
}

/// Finds the shortest code matching the window, searching lengths from
/// `from` (shorter ones are known not to match): its symbol and length, or
/// `None` if no code of at most `min(30, nb)` bits does.
#[inline(always)]
fn find(acc: u64, nb: u64, buf: u64, from: u64, Ghost(b): Ghost<Seq<u8>>, Ghost(p): Ghost<int>, Ghost(r): Ghost<nat>) -> (res: Option<(u16, u64)>)
    requires
        layout_ok(),
        aligned(acc, nb, buf),
        1 <= nb <= 64,
        nb <= r,
        acc == code(b, p, nb as nat),
        acc < pow2(nb as nat),
        1 <= from <= (if nb < 30 { nb } else { 30 }) + 1,
        hfind(b, p, r, 1) == hfind(b, p, r, from as nat),
    ensures
        match res {
            Some((s, l)) => {
                &&& 1 <= l <= nb
                &&& l <= 30
                &&& s < 257
                &&& hfind(b, p, r, 1) == Some((s as int, l as nat))
            },
            None => hfind(b, p, r, 1) == hfind(b, p, r, (if nb < 30 { nb } else { 30 }) as nat + 1),
        },
{
    let lmax = if nb < 30 { nb } else { 30 };
    let mut l: u64 = from;
    while l <= lmax
        invariant
            1 <= l <= 31,
            lmax == if nb < 30 { nb } else { 30 },
            1 <= nb <= 64,
            nb <= r,
            acc == code(b, p, nb as nat),
            acc < pow2(nb as nat),
            hfind(b, p, r, 1) == hfind(b, p, r, l as nat),
            l <= lmax + 1,
            layout_ok(),
            aligned(acc, nb, buf),
        decreases lmax + 1 - l,
    {
        let v = buf >> (64 - l);
        proof {
            lemma_bound_bv(acc, nb);
            lemma_al_top(acc, nb, buf, l);
            lemma_u64_shr_is_div(acc, (nb - l) as u64);
            lemma_code_top(b, p, nb as nat, l as nat);
            lemma_match(l as nat, v as nat);
        }
        let li = l as usize;
        if v >= FIRST[li] as u64 && v - (FIRST[li] as u64) < CNT[li] as u64 {
            let s = SYMS[(OFF[li] + (v as u32 - FIRST[li])) as usize];
            return Some((s, l));
        }
        l = l + 1;
    }
    None
}

/// Under `layout_ok`, every code is at least 5 bits long.
proof fn lemma_min_len(l: nat, v: nat)
    requires
        layout_ok(),
        hmatch(l, v),
    ensures
        l >= 5,
{
    let s = choose|s: int| 0 <= s < 257 && hlen(s) == l && hcode(s) == v;
    assert(5 <= hlen(s));
}

/// The code `hfind` finds matches.
proof fn lemma_hfind_match(b: Seq<u8>, p: int, r: nat, from: nat)
    requires
        hfind(b, p, r, from) is Some,
    ensures
        hmatch(hfind(b, p, r, from)->Some_0.1, code(b, p, hfind(b, p, r, from)->Some_0.1)),
    decreases 31 - from,
{
    if from > 30 || from > r {
    } else if hmatch(from, code(b, p, from)) {
    } else {
        lemma_hfind_match(b, p, r, from + 1);
    }
}

/// The decoder's loop state: `done` decoded so far, held in
/// `o[..done.len()]` (what is after it is scratch), and the rest still to
/// decode from bit `8 * i - nb`. Every code is at least 5 bits, so `done`
/// is at most a fifth as long as the bits taken.
pub open spec fn bstate(bs: Seq<u8>, i: usize, acc: u64, nb: u64, o: Seq<u8>, done: Seq<u8>) -> bool {
    &&& window(bs, i, acc, nb)
    &&& done.len() <= o.len()
    &&& o.subrange(0, done.len() as int) == done
    &&& 5 * done.len() <= 8 * i - nb
    &&& hdec(bs, 0) == match hdec(bs, 8 * i - nb) {
        Some(t) => Some(done + t),
        None => None::<Seq<u8>>,
    }
}

/// Taking the code of symbol `s` and `l` bits at the start of the window.
proof fn lemma_consume(bs: Seq<u8>, i: usize, nb: u64, done: Seq<u8>, s: int, l: nat)
    requires
        layout_ok(),
        i <= bs.len(),
        nb <= 8 * i,
        1 <= l <= nb,
        hfind(bs, 8 * i - nb, (8 * bs.len() - (8 * i - nb)) as nat, 1) == Some((s, l)),
        s < 256,
        5 * done.len() <= 8 * i - nb,
        hdec(bs, 0) == match hdec(bs, 8 * i - nb) {
            Some(t) => Some(done + t),
            None => None::<Seq<u8>>,
        },
    ensures
        5 * (done.len() + 1) <= 8 * i - (nb - l),
        hdec(bs, 0) == match hdec(bs, 8 * i - (nb - l)) {
            Some(t) => Some(done.push(s as u8) + t),
            None => None::<Seq<u8>>,
        },
{
    let p = 8 * i - nb;
    let r = (8 * bs.len() - p) as nat;
    lemma_hdec_step(bs, p, s, l);
    lemma_hfind_match(bs, p, r, 1);
    lemma_min_len(l, code(bs, p, l));
    assert(p + l == 8 * i - (nb - l));
    let t1 = hdec(bs, p + l);
    if t1 is Some {
        assert(done + (seq![s as u8] + t1->Some_0) =~= done.push(s as u8) + t1->Some_0);
    }
}

/// Writing `s` just after `done` in `o`.
proof fn lemma_put(o: Seq<u8>, done: Seq<u8>, s: u8, o2: Seq<u8>)
    requires
        done.len() < o.len(),
        o.subrange(0, done.len() as int) == done,
        o2 == o.update(done.len() as int, s),
    ensures
        o2.subrange(0, done.len() as int + 1) == done.push(s),
{
    assert(o2.subrange(0, done.len() as int + 1) =~= done.push(s));
}

/// Writing anything past `done` keeps it.
proof fn lemma_put_after(o: Seq<u8>, done: Seq<u8>, k: int, s: u8, o2: Seq<u8>)
    requires
        done.len() <= k < o.len(),
        o.subrange(0, done.len() as int) == done,
        o2 == o.update(k, s),
    ensures
        o2.subrange(0, done.len() as int) == done,
{
    assert(o2.subrange(0, done.len() as int) =~= done);
}

/// Decodes the Huffman string `b` (RFC 7541 §5.2) into `out`, replacing
/// what it held. Returns false, with `out` holding something else, if `b`
/// is not a valid encoding.
///
/// `out` is first made long enough for any result (codes are at least 5
/// bits) plus two bytes, so a table entry's two symbols are both written
/// with no checks and the count of them taken; it is cut to the result at
/// the end.
#[verifier::rlimit(60)]
pub fn decode(b: &[u8], out: &mut Vec<u8>, t: &[u32]) -> (ok: bool)
    requires
        layout_ok(),
        dtab_ok(t@),
        8 * b@.len() + 2 < usize::MAX,
    ensures
        ok == hdec(b@, 0) is Some,
        ok ==> final(out)@ == hdec(b@, 0)->Some_0,
        final(out)@.len() <= 8 * b@.len() / 5 + 2,
{
    let ghost bs = b@;
    let n = b.len();
    let need = 8 * n / 5 + 2;
    if out.len() < need {
        out.resize(need, 0u8);
    }
    let mut i: usize = 0;
    let mut acc: u64 = 0;
    let mut nb: u64 = 0;
    let mut buf: u64 = 0;
    let mut w: usize = 0;
    let ghost mut done: Seq<u8> = Seq::empty();
    proof {
        lemma2_to64();
        assert(out@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    loop
        invariant
            bs == b@,
            n == b@.len(),
            8 * n + 2 < usize::MAX,
            need == 8 * n / 5 + 2,
            out@.len() >= need,
            bstate(bs, i, acc, nb, out@, done),
            aligned(acc, nb, buf),
            w == done.len(),
            layout_ok(),
            dtab_ok(t@),
        decreases 8 * n - (8 * i - nb),
    {
        // Refill only when the window may be shorter than a code.
        let (i2, acc2, nb2, buf2) = if nb < 30 && n - i >= 4 {
            refill4(b, i, acc, nb, buf)
        } else if nb < 30 {
            refill(b, i, acc, nb, buf)
        } else {
            (i, acc, nb, buf)
        };
        i = i2;
        acc = acc2;
        nb = nb2;
        buf = buf2;
        let ghost p = 8 * i - nb;
        let ghost r = (8 * n - p) as nat;
        if nb == 0 {
            out.truncate(w);
            proof {
                assert(done + Seq::<u8>::empty() =~= done);
            }
            return true;
        }
        let mut from: u64 = 1;
        if nb >= 12 {
            let x = buf >> 52;
            proof {
                lemma_bound_bv(acc, nb);
                lemma_al_top(acc, nb, buf, 12);
                lemma2_to64();
                lemma_u64_shr_is_div(acc, (nb - 12) as u64);
                lemma_code_top(bs, p, nb as nat, 12);
                lemma_code_bound(bs, p, 12);
            }
            let e = verilith_core::prims::get32(t, x as usize);
            let k = (e >> 6u32) & 3;
            proof {
                assert(dentry(x as int, e));
                assert((e >> 6u32) & 3 < 4 && (e >> 8u32) & 15 < 16 && e & 63 < 64 && (e >> 16u32) & 255 < 256 && e >> 24u32 < 256) by (bit_vector);
            }
            if k == 1 || k == 2 {
                let l1 = ((e >> 8u32) & 15) as u64;
                let lt = (e & 63) as u64;
                let s1 = ((e >> 16u32) & 255) as u8;
                let s2 = (e >> 24u32) as u8;
                let ghost o0 = out@;
                proof {
                    lemma_fm_hfind(bs, p, r, x as int, 12, l1 as int, s1 as int);
                    lemma_code_top(bs, p, 12, l1 as nat);
                    lemma_consume(bs, i, nb, done, s1 as int, l1 as nat);
                    assert(5 * (w + 2) <= 8 * n);
                    assert(w + 2 <= 8 * n / 5) by (nonlinear_arith)
                        requires
                            5 * (w + 2) <= 8 * n,
                    ;
                }
                verilith_core::prims::store_at(out, w, s1);
                let ghost o1 = out@;
                verilith_core::prims::store_at(out, w + 1, s2);
                proof {
                    let d1 = done.push(s1);
                    lemma_put(o0, done, s1, o1);
                    if k == 1 {
                        lemma_put_after(o1, d1, w + 1, s2, out@);
                        done = d1;
                    } else {
                        let w2 = (12 - l1) as nat;
                        let p2 = p + l1;
                        let l2 = (lt - l1) as nat;
                        lemma_fm_hfind(bs, p2, (r - l1) as nat, x as int % (pow2(w2) as int), w2, l2 as int, s2 as int);
                        assert(8 * i - (nb - l1) == p2);
                        assert((8 * bs.len() - p2) as nat == (r - l1) as nat);
                        lemma_consume(bs, i, (nb - l1) as u64, d1, s2 as int, l2);
                        lemma_put(o1, d1, s2, out@);
                        assert((nb - l1) - l2 == nb - lt);
                        done = d1.push(s2);
                    }
                }
                proof {
                    lemma_al_take(acc, nb, buf, lt);
                }
                let (a2, n2) = take(acc, nb, lt, Ghost(bs), Ghost(i));
                acc = a2;
                nb = n2;
                buf = buf << lt;
                w = w + k as usize;
                continue;
            }
            if k == 0 {
                proof {
                    lemma_nm_skip(bs, p, r, x as int);
                }
                from = 13;
            }
        }
        match find(acc, nb, buf, from, Ghost(bs), Ghost(p), Ghost(r)) {
            None => {
                proof {
                    let lmax: nat = (if nb < 30 { nb } else { 30 }) as nat;
                    assert(hfind(bs, p, r, lmax + 1) is None);
                }
                // No code within the window: valid only as padding (at
                // most 7 bits, all ones) at the end.
                if i == n && nb <= 7 {
                    proof {
                        lemma_pow2_8(nb as nat);
                        lemma_u64_shl_is_mul(1, nb);
                        lemma_bound_bv(acc, nb);
                        lemma_al_pad(acc, nb, buf);
                    }
                    if buf == (0xFFFF_FFFF_FFFF_FFFFu64 << (64 - nb)) {
                        out.truncate(w);
                        proof {
                            assert(done + Seq::<u8>::empty() =~= done);
                        }
                        return true;
                    }
                }
                out.truncate(0);
                return false;
            },
            Some((sym, l)) => {
                if sym == 256 {
                    out.truncate(0);
                    return false;
                }
                let ghost o0 = out@;
                proof {
                    lemma_consume(bs, i, nb, done, sym as int, l as nat);
                    assert(w + 1 <= 8 * n / 5) by (nonlinear_arith)
                        requires
                            5 * (w + 1) <= 8 * n,
                    ;
                }
                verilith_core::prims::store_at(out, w, sym as u8);
                proof {
                    lemma_put(o0, done, sym as u8, out@);
                    done = done.push(sym as u8);
                    lemma_bound_bv(acc, nb);
                    lemma_al_take(acc, nb, buf, l);
                }
                let (a2, n2) = take(acc, nb, l, Ghost(bs), Ghost(i));
                acc = a2;
                nb = n2;
                buf = buf << l;
                w = w + 1;
            },
        }
    }
}

} // verus!
