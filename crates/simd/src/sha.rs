//! What the SHA instructions compute (TRUSTED): the specification the
//! instruction kernels in verilith-sha2 (`shani`, `armv8`) are proven
//! against, and the wrappers in [`crate::sha_x86`] and [`crate::sha_neon`] state, transcribed from the vendors' pseudocode rather than from FIPS
//! 180-4, as functions on the 32- or 64-bit lanes of a vector, lane 0
//! first (bits 31:0 of an x86 register, element 0 of an Arm one).
//!
//! - x86-64 SHA extensions: `SHA256RNDS2`, `SHA256MSG1` and `SHA256MSG2`, as
//!   the Intel 64 and IA-32 Architectures Software Developer's Manual,
//!   volume 2, defines them (their "Operation" sections, with the helper
//!   functions of `SHA256RNDS2`).
//! - AArch64 FEAT_SHA256: `SHA256H`, `SHA256H2`, `SHA256SU0` and
//!   `SHA256SU1`, as the Arm Architecture Reference Manual for A-profile
//!   defines them (the shared pseudocode `SHA256hash`, `SHAchoose`,
//!   `SHAmajority`, `SHAhashSIGMA0` and `SHAhashSIGMA1`).
//! - AArch64 FEAT_SHA512: `SHA512H`, `SHA512H2`, `SHA512SU0` and
//!   `SHA512SU1`, from the same manual.
//! - The few other instructions the kernels use that verilith-simd does not
//!   specify: SSE4.1's `pblendw`, and on AArch64 `rev32`, `rev64` and
//!   64-bit `add`.
//!
//! Each is also checked against the CPU: verilith-sha2's `tests/isa.rs` runs every
//! instruction on random operands (natively on x86-64 with SHA-NI, on
//! AArch64 natively or under qemu) against [`crate::sha_ref`], verified
//! implementations of these functions. Operand order follows the
//! intrinsics (`core::arch`), which is the instruction's operand order
//! except where noted.
#![allow(missing_docs)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Words
// ---------------------------------------------------------------------------

/// `+` on 32-bit words in the pseudocode: modulo 2^32.
pub open spec fn add32(x: u32, y: u32) -> u32 {
    ((x as int + y as int) % 0x1_0000_0000) as u32
}

/// `+` on 64-bit words: modulo 2^64.
pub open spec fn add64(x: u64, y: u64) -> u64 {
    ((x as int + y as int) % 0x1_0000_0000_0000_0000) as u64
}

/// `x ROR n`, 0 < n < 32.
pub open spec fn ror32(x: u32, n: u32) -> u32 {
    (x >> n) | (x << ((32 - n) as u32))
}

/// `ROR(x, n)` on 64 bits, 0 < n < 64.
pub open spec fn ror64(x: u64, n: u64) -> u64 {
    (x >> n) | (x << ((64 - n) as u64))
}

// ---------------------------------------------------------------------------
// Intel SDM: SHA256RNDS2, SHA256MSG1, SHA256MSG2
// ---------------------------------------------------------------------------

/// Ch(E, F, G) = (E AND F) XOR ((NOT E) AND G).
pub open spec fn x_ch(e: u32, f: u32, g: u32) -> u32 {
    (e & f) ^ (!e & g)
}

/// Maj(A, B, C) = (A AND B) XOR (A AND C) XOR (B AND C).
pub open spec fn x_maj(a: u32, b: u32, c: u32) -> u32 {
    (a & b) ^ (a & c) ^ (b & c)
}

/// Σ0(A) = (A ROR 2) XOR (A ROR 13) XOR (A ROR 22).
pub open spec fn x_big_s0(a: u32) -> u32 {
    ror32(a, 2) ^ ror32(a, 13) ^ ror32(a, 22)
}

/// Σ1(E) = (E ROR 6) XOR (E ROR 11) XOR (E ROR 25).
pub open spec fn x_big_s1(e: u32) -> u32 {
    ror32(e, 6) ^ ror32(e, 11) ^ ror32(e, 25)
}

/// σ0(W) = (W ROR 7) XOR (W ROR 18) XOR (W SHR 3).
pub open spec fn x_small_s0(w: u32) -> u32 {
    ror32(w, 7) ^ ror32(w, 18) ^ (w >> 3u32)
}

/// σ1(W) = (W ROR 17) XOR (W ROR 19) XOR (W SHR 10).
pub open spec fn x_small_s1(w: u32) -> u32 {
    ror32(w, 17) ^ ror32(w, 19) ^ (w >> 10u32)
}

/// A..H of `SHA256RNDS2`'s loop.
pub struct Rnds2 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub d: u32,
    pub e: u32,
    pub f: u32,
    pub g: u32,
    pub h: u32,
}

/// One iteration of `SHA256RNDS2`'s `FOR i = 0 to 1` loop, with WK_i = `wk`:
///
/// ```text
/// A_(i+1) := Ch(E_i, F_i, G_i) + Σ1(E_i) + WK_i + H_i + Maj(A_i, B_i, C_i) + Σ0(A_i);
/// B_(i+1) := A_i;  C_(i+1) := B_i;  D_(i+1) := C_i;
/// E_(i+1) := Ch(E_i, F_i, G_i) + Σ1(E_i) + WK_i + H_i + D_i;
/// F_(i+1) := E_i;  G_(i+1) := F_i;  H_(i+1) := G_i;
/// ```
pub open spec fn rnds2_step(s: Rnds2, wk: u32) -> Rnds2 {
    let t = add32(add32(add32(x_ch(s.e, s.f, s.g), x_big_s1(s.e)), wk), s.h);
    Rnds2 {
        a: add32(add32(t, x_maj(s.a, s.b, s.c)), x_big_s0(s.a)),
        b: s.a,
        c: s.b,
        d: s.c,
        e: add32(t, s.d),
        f: s.e,
        g: s.f,
        h: s.g,
    }
}

/// `SHA256RNDS2 xmm1, xmm2, <XMM0>`, `_mm_sha256rnds2_epu32(src1, src2, k)`
/// with xmm1 = `src1`, xmm2 = `src2`, XMM0 = `k`:
///
/// ```text
/// A_0 := SRC2[127:96]; B_0 := SRC2[95:64]; C_0 := SRC1[127:96]; D_0 := SRC1[95:64];
/// E_0 := SRC2[63:32];  F_0 := SRC2[31:0];  G_0 := SRC1[63:32];  H_0 := SRC1[31:0];
/// WK_0 := XMM0[31:0]; WK_1 := XMM0[63:32];
/// FOR i = 0 to 1 ...
/// DEST[127:96] := A_2; DEST[95:64] := B_2; DEST[63:32] := E_2; DEST[31:0] := F_2;
/// ```
pub open spec fn sha256rnds2(src1: Seq<u32>, src2: Seq<u32>, k: Seq<u32>) -> Seq<u32> {
    let s0 = Rnds2 { a: src2[3], b: src2[2], c: src1[3], d: src1[2], e: src2[1], f: src2[0], g: src1[1], h: src1[0] };
    let s2 = rnds2_step(rnds2_step(s0, k[0]), k[1]);
    seq![s2.f, s2.e, s2.b, s2.a]
}

/// `SHA256MSG1 xmm1, xmm2`, `_mm_sha256msg1_epu32(src1, src2)`:
///
/// ```text
/// W4 := SRC2[31:0]; W3 := SRC1[127:96]; W2 := SRC1[95:64]; W1 := SRC1[63:32]; W0 := SRC1[31:0];
/// DEST[127:96] := W3 + σ0(W4); DEST[95:64] := W2 + σ0(W3);
/// DEST[63:32] := W1 + σ0(W2);  DEST[31:0] := W0 + σ0(W1);
/// ```
pub open spec fn sha256msg1(src1: Seq<u32>, src2: Seq<u32>) -> Seq<u32> {
    let (w0, w1, w2, w3, w4) = (src1[0], src1[1], src1[2], src1[3], src2[0]);
    seq![add32(w0, x_small_s0(w1)), add32(w1, x_small_s0(w2)), add32(w2, x_small_s0(w3)), add32(w3, x_small_s0(w4))]
}

/// `SHA256MSG2 xmm1, xmm2`, `_mm_sha256msg2_epu32(src1, src2)`:
///
/// ```text
/// W14 := SRC2[95:64]; W15 := SRC2[127:96];
/// W16 := SRC1[31:0] + σ1(W14);  W17 := SRC1[63:32] + σ1(W15);
/// W18 := SRC1[95:64] + σ1(W16); W19 := SRC1[127:96] + σ1(W17);
/// DEST[127:96] := W19; DEST[95:64] := W18; DEST[63:32] := W17; DEST[31:0] := W16;
/// ```
pub open spec fn sha256msg2(src1: Seq<u32>, src2: Seq<u32>) -> Seq<u32> {
    let (w14, w15) = (src2[2], src2[3]);
    let w16 = add32(src1[0], x_small_s1(w14));
    let w17 = add32(src1[1], x_small_s1(w15));
    let w18 = add32(src1[2], x_small_s1(w16));
    let w19 = add32(src1[3], x_small_s1(w17));
    seq![w16, w17, w18, w19]
}

/// `PBLENDW xmm1, xmm2, imm8`, `_mm_blend_epi16(a, b, IMM8)`, on bytes: word
/// i (bytes 2i and 2i + 1) is `b`'s if bit i of the immediate is set, else
/// `a`'s.
pub open spec fn blend16(a: Seq<u8>, b: Seq<u8>, imm: int) -> Seq<u8> {
    Seq::new(16, |i: int| if (imm / vstd::arithmetic::power2::pow2((i / 2) as nat) as int) % 2 == 1 { b[i] } else { a[i] })
}

// ---------------------------------------------------------------------------
// Arm ARM: SHA256H, SHA256H2, SHA256SU0, SHA256SU1
// ---------------------------------------------------------------------------

/// `SHAchoose(x, y, z) = ((y EOR z) AND x) EOR z`.
pub open spec fn a_choose(x: u32, y: u32, z: u32) -> u32 {
    ((y ^ z) & x) ^ z
}

/// `SHAmajority(x, y, z) = (x AND y) OR ((x OR y) AND z)`.
pub open spec fn a_majority(x: u32, y: u32, z: u32) -> u32 {
    (x & y) | ((x | y) & z)
}

/// `SHAhashSIGMA0(x) = ROR(x, 2) EOR ROR(x, 13) EOR ROR(x, 22)`.
pub open spec fn a_sigma0(x: u32) -> u32 {
    ror32(x, 2) ^ ror32(x, 13) ^ ror32(x, 22)
}

/// `SHAhashSIGMA1(x) = ROR(x, 6) EOR ROR(x, 11) EOR ROR(x, 25)`.
pub open spec fn a_sigma1(x: u32) -> u32 {
    ror32(x, 6) ^ ror32(x, 11) ^ ror32(x, 25)
}

/// One iteration (`e`) of `SHA256hash`'s loop over `(X, Y)`, with
/// `Elem[W, e, 32]` = `w`:
///
/// ```text
/// chs = SHAchoose(Y<31:0>, Y<63:32>, Y<95:64>);
/// maj = SHAmajority(X<31:0>, X<63:32>, X<95:64>);
/// t = Y<127:96> + SHAhashSIGMA1(Y<31:0>) + chs + Elem[W, e, 32];
/// X<127:96> = t + X<127:96>;
/// Y<127:96> = t + SHAhashSIGMA0(X<31:0>) + maj;
/// bits(256) yX = ROL(Y : X, 32);
/// Y = yX<255:128>; X = yX<127:0>;
/// ```
///
/// The rotation of `Y : X` left by 32 bits moves each word one lane up,
/// `Y<127:96>` into `X<31:0>` and `X<127:96>` into `Y<31:0>`.
pub open spec fn sha256hash_step(x: Seq<u32>, y: Seq<u32>, w: u32) -> (Seq<u32>, Seq<u32>) {
    let chs = a_choose(y[0], y[1], y[2]);
    let maj = a_majority(x[0], x[1], x[2]);
    let t = add32(add32(add32(y[3], a_sigma1(y[0])), chs), w);
    let x3 = add32(t, x[3]);
    let y3 = add32(add32(t, a_sigma0(x[0])), maj);
    (seq![y3, x[0], x[1], x[2]], seq![x3, y[0], y[1], y[2]])
}

/// `SHA256hash(X, Y, W, part1)` before its final choice: the four
/// iterations `e = 0 to 3`.
pub open spec fn sha256hash(x: Seq<u32>, y: Seq<u32>, w: Seq<u32>) -> (Seq<u32>, Seq<u32>) {
    let s1 = sha256hash_step(x, y, w[0]);
    let s2 = sha256hash_step(s1.0, s1.1, w[1]);
    let s3 = sha256hash_step(s2.0, s2.1, w[2]);
    sha256hash_step(s3.0, s3.1, w[3])
}

/// `SHA256H Qd, Qn, Vm.4S`, `vsha256hq_u32(hash_abcd, hash_efgh, wk)` with
/// Qd = `hash_abcd`, Qn = `hash_efgh`, Vm = `wk`:
/// `V[d] = SHA256hash(V[d], V[n], V[m], TRUE)`, which returns X.
pub open spec fn sha256h(hash_abcd: Seq<u32>, hash_efgh: Seq<u32>, wk: Seq<u32>) -> Seq<u32> {
    sha256hash(hash_abcd, hash_efgh, wk).0
}

/// `SHA256H2 Qd, Qn, Vm.4S`, `vsha256h2q_u32(hash_efgh, hash_abcd, wk)` with
/// Qd = `hash_efgh`, Qn = `hash_abcd`, Vm = `wk`:
/// `V[d] = SHA256hash(V[n], V[d], V[m], FALSE)`, which returns Y.
pub open spec fn sha256h2(hash_efgh: Seq<u32>, hash_abcd: Seq<u32>, wk: Seq<u32>) -> Seq<u32> {
    sha256hash(hash_abcd, hash_efgh, wk).1
}

/// `SHA256SU0 Vd.4S, Vn.4S`, `vsha256su0q_u32(w0_3, w4_7)` with Vd = `w0_3`,
/// Vn = `w4_7`:
///
/// ```text
/// T = operand2<31:0> : operand1<127:32>;
/// for e = 0 to 3
///     elt = Elem[T, e, 32];
///     elt = ROR(elt, 7) EOR ROR(elt, 18) EOR LSR(elt, 3);
///     Elem[result, e, 32] = elt + Elem[operand1, e, 32];
/// ```
pub open spec fn sha256su0(w0_3: Seq<u32>, w4_7: Seq<u32>) -> Seq<u32> {
    let t = seq![w0_3[1], w0_3[2], w0_3[3], w4_7[0]];
    Seq::new(4, |e: int| add32(ror32(t[e], 7) ^ ror32(t[e], 18) ^ (t[e] >> 3u32), w0_3[e]))
}

/// `LSR`/`ROR` of `SHA256SU1`: ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10).
pub open spec fn su1_sig(x: u32) -> u32 {
    ror32(x, 17) ^ ror32(x, 19) ^ (x >> 10u32)
}

/// `SHA256SU1 Vd.4S, Vn.4S, Vm.4S`, `vsha256su1q_u32(tw0_3, w8_11, w12_15)`
/// with Vd = `tw0_3`, Vn = `w8_11`, Vm = `w12_15`:
///
/// ```text
/// T0 = operand3<31:0> : operand2<127:32>;
/// T1 = operand3<127:64>;
/// for e = 0 to 1
///     elt = Elem[T1, e, 32];
///     elt = ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10);
///     elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
///     Elem[result, e, 32] = elt;
/// T1 = result<63:0>;
/// for e = 2 to 3
///     elt = Elem[T1, e-2, 32];
///     elt = ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10);
///     elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
///     Elem[result, e, 32] = elt;
/// ```
pub open spec fn sha256su1(tw0_3: Seq<u32>, w8_11: Seq<u32>, w12_15: Seq<u32>) -> Seq<u32> {
    let t0 = seq![w8_11[1], w8_11[2], w8_11[3], w12_15[0]];
    let r0 = add32(add32(su1_sig(w12_15[2]), tw0_3[0]), t0[0]);
    let r1 = add32(add32(su1_sig(w12_15[3]), tw0_3[1]), t0[1]);
    let r2 = add32(add32(su1_sig(r0), tw0_3[2]), t0[2]);
    let r3 = add32(add32(su1_sig(r1), tw0_3[3]), t0[3]);
    seq![r0, r1, r2, r3]
}

// ---------------------------------------------------------------------------
// Arm ARM: SHA512H, SHA512H2, SHA512SU0, SHA512SU1 (lanes: 0 is <63:0>)
// ---------------------------------------------------------------------------

/// `SHA512H Qd, Qn, Vm.2D`, `vsha512hq_u64(d, n, m)` (W = V[d], X = V[n],
/// Y = V[m]):
///
/// ```text
/// MSigma1 = ROR(Y<127:64>, 14) EOR ROR(Y<127:64>, 18) EOR ROR(Y<127:64>, 41);
/// Vtmp<127:64> = (Y<127:64> AND X<63:0>) EOR (NOT(Y<127:64>) AND X<127:64>);
/// Vtmp<127:64> = (Vtmp<127:64> + MSigma1 + W<127:64>);
/// tmp = Vtmp<127:64> + Y<63:0>;
/// MSigma1 = ROR(tmp, 14) EOR ROR(tmp, 18) EOR ROR(tmp, 41);
/// Vtmp<63:0> = (tmp AND Y<127:64>) EOR (NOT(tmp) AND X<63:0>);
/// Vtmp<63:0> = (Vtmp<63:0> + MSigma1 + W<63:0>);
/// V[d] = Vtmp;
/// ```
pub open spec fn sha512h(w: Seq<u64>, x: Seq<u64>, y: Seq<u64>) -> Seq<u64> {
    let ms1 = ror64(y[1], 14) ^ ror64(y[1], 18) ^ ror64(y[1], 41);
    let hi0 = (y[1] & x[0]) ^ (!y[1] & x[1]);
    let hi = add64(add64(hi0, ms1), w[1]);
    let tmp = add64(hi, y[0]);
    let ms1b = ror64(tmp, 14) ^ ror64(tmp, 18) ^ ror64(tmp, 41);
    let lo0 = (tmp & y[1]) ^ (!tmp & x[0]);
    let lo = add64(add64(lo0, ms1b), w[0]);
    seq![lo, hi]
}

/// `SHA512H2 Qd, Qn, Vm.2D`, `vsha512h2q_u64(d, n, m)` (W = V[d], X = V[n],
/// Y = V[m]):
///
/// ```text
/// NSigma0 = ROR(Y<63:0>, 28) EOR ROR(Y<63:0>, 34) EOR ROR(Y<63:0>, 39);
/// Vtmp<127:64> = (X<63:0> AND Y<127:64>) EOR (X<63:0> AND Y<63:0>) EOR (Y<127:64> AND Y<63:0>);
/// Vtmp<127:64> = (Vtmp<127:64> + NSigma0 + W<127:64>);
/// NSigma0 = ROR(Vtmp<127:64>, 28) EOR ROR(Vtmp<127:64>, 34) EOR ROR(Vtmp<127:64>, 39);
/// Vtmp<63:0> = (Vtmp<127:64> AND Y<63:0>) EOR (Vtmp<127:64> AND Y<127:64>) EOR (Y<127:64> AND Y<63:0>);
/// Vtmp<63:0> = (Vtmp<63:0> + NSigma0 + W<63:0>);
/// V[d] = Vtmp;
/// ```
pub open spec fn sha512h2(w: Seq<u64>, x: Seq<u64>, y: Seq<u64>) -> Seq<u64> {
    let ns0 = ror64(y[0], 28) ^ ror64(y[0], 34) ^ ror64(y[0], 39);
    let hi0 = (x[0] & y[1]) ^ (x[0] & y[0]) ^ (y[1] & y[0]);
    let hi = add64(add64(hi0, ns0), w[1]);
    let ns0b = ror64(hi, 28) ^ ror64(hi, 34) ^ ror64(hi, 39);
    let lo0 = (hi & y[0]) ^ (hi & y[1]) ^ (y[1] & y[0]);
    let lo = add64(add64(lo0, ns0b), w[0]);
    seq![lo, hi]
}

/// `SHA512SU0 Vd.2D, Vn.2D`, `vsha512su0q_u64(d, n)` (W = V[d], X = V[n]):
///
/// ```text
/// sig0 = ROR(W<127:64>, 1) EOR ROR(W<127:64>, 8) EOR LSR(W<127:64>, 7);
/// Vtmp<63:0> = W<63:0> + sig0;
/// sig0 = ROR(X<63:0>, 1) EOR ROR(X<63:0>, 8) EOR LSR(X<63:0>, 7);
/// Vtmp<127:64> = W<127:64> + sig0;
/// ```
pub open spec fn sha512su0(w: Seq<u64>, x: Seq<u64>) -> Seq<u64> {
    let s0 = ror64(w[1], 1) ^ ror64(w[1], 8) ^ (w[1] >> 7u64);
    let s1 = ror64(x[0], 1) ^ ror64(x[0], 8) ^ (x[0] >> 7u64);
    seq![add64(w[0], s0), add64(w[1], s1)]
}

/// `SHA512SU1 Vd.2D, Vn.2D, Vm.2D`, `vsha512su1q_u64(d, n, m)` (W = V[d],
/// X = V[n], Y = V[m]):
///
/// ```text
/// sig1 = ROR(X<127:64>, 19) EOR ROR(X<127:64>, 61) EOR LSR(X<127:64>, 6);
/// Vtmp<127:64> = W<127:64> + sig1 + Y<127:64>;
/// sig1 = ROR(X<63:0>, 19) EOR ROR(X<63:0>, 61) EOR LSR(X<63:0>, 6);
/// Vtmp<63:0> = W<63:0> + sig1 + Y<63:0>;
/// ```
pub open spec fn sha512su1(w: Seq<u64>, x: Seq<u64>, y: Seq<u64>) -> Seq<u64> {
    let s1 = ror64(x[1], 19) ^ ror64(x[1], 61) ^ (x[1] >> 6u64);
    let s0 = ror64(x[0], 19) ^ ror64(x[0], 61) ^ (x[0] >> 6u64);
    seq![add64(add64(w[0], s0), y[0]), add64(add64(w[1], s1), y[1])]
}

// ---------------------------------------------------------------------------
// Other AArch64 instructions
// ---------------------------------------------------------------------------

/// `REV32 Vd.16B, Vn.16B` (`vrev32q_u8`): the bytes of each 32-bit word
/// reversed.
pub open spec fn rev32(a: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |i: int| a[4 * (i / 4) + 3 - i % 4])
}

/// `REV64 Vd.16B, Vn.16B` (`vrev64q_u8`): the bytes of each 64-bit word
/// reversed.
pub open spec fn rev64(a: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |i: int| a[8 * (i / 8) + 7 - i % 8])
}

/// `ADD Vd.2D, Vn.2D, Vm.2D` (`vaddq_u64`).
pub open spec fn add64x2(a: Seq<u64>, b: Seq<u64>) -> Seq<u64> {
    seq![add64(a[0], b[0]), add64(a[1], b[1])]
}

} // verus!
