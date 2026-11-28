#!/usr/bin/env python3
"""Generates tests/difftest.rs: every intrinsic in src/x86.rs against the
verified reference (src/refs.rs) of its specification."""
import sys, zlib

def seed(s):
    """A fixed per-test seed, so regenerating gives the same file."""
    return (zlib.crc32(s.encode()) << 30) ^ zlib.crc32(s[::-1].encode())
N = "ITERS"
cases = []   # (test name, body lines)

def V(w): return "__m128i" if w == 128 else "__m256i"
def P(w): return "_mm_" if w == 128 else "_mm256_"
def FEAT(w, f128=None): return "avx2" if w == 256 else (f128 or "sse2")
VIEW = {"B": ("bytes", "u8"), "U16": ("u16s", "u16"), "U32": ("u32s", "u32"), "U64": ("u64s", "u64")}

def binop(w, intr, refcall, vin, vout, f128=None, same=False):
    """refcall uses {a} {b} as slices of the input view."""
    a_ = f"&{VIEW[vin][0]}{w}(a)"; b_ = f"&{VIEW[vin][0]}{w}(b)"
    body = f"""
    #[target_feature(enable = "{FEAT(w, f128)}")]
    fn go(a: {V(w)}, b: {V(w)}) -> {V(w)} {{ {intr}(a, b) }}
    let mut rng = Rng::new(0x{seed(intr+str(w)):x});
    for it in 0..{N} {{
        let a = rng.v{w}();
        let b = if it % 7 == 0 {{ a }} else if it % 11 == 0 {{ rng.near{w}(a) }} else {{ rng.v{w}() }};
        let got = {VIEW[vout][0]}{w}(unsafe {{ go(a, b) }});
        let want: Vec<{VIEW[vout][1]}> = {refcall.format(a=a_, b=b_)};
        if got != want {{ fail("{intr}", &bytes{w}(a), &bytes{w}(b), &format!("{{:?}} vs {{:?}}", got, want)); }}
    }}"""
    cases.append((f"{intr}", body))

def unop_imm(w, intr, imm, refcall, vin, vout, f128=None):
    a_ = f"&{VIEW[vin][0]}{w}(a)"
    body = f"""
    #[target_feature(enable = "{FEAT(w, f128)}")]
    fn go(a: {V(w)}) -> {V(w)} {{ {intr}::<{imm}>(a) }}
    let mut rng = Rng::new(0x{seed(intr+str(imm)):x});
    for _ in 0..{N}/16 {{
        let a = rng.v{w}();
        let got = {VIEW[vout][0]}{w}(unsafe {{ go(a) }});
        let want: Vec<{VIEW[vout][1]}> = {refcall.format(a=a_, imm=imm)};
        if got != want {{ fail("{intr}::<{imm}>", &bytes{w}(a), &[], &format!("{{:?}} vs {{:?}}", got, want)); }}
    }}"""
    cases.append((f"{intr}_{imm}", body))

def binop_imm(w, intr, imm, refcall, f128=None):
    body = f"""
    #[target_feature(enable = "{FEAT(w, f128)}")]
    fn go(a: {V(w)}, b: {V(w)}) -> {V(w)} {{ {intr}::<{imm}>(a, b) }}
    let mut rng = Rng::new(0x{seed(intr+str(imm)):x});
    for _ in 0..{N}/16 {{
        let a = rng.v{w}();
        let b = rng.v{w}();
        let got = bytes{w}(unsafe {{ go(a, b) }});
        let want: Vec<u8> = {refcall.format(a=f"&bytes{w}(a)", b=f"&bytes{w}(b)", imm=imm)};
        if got != want {{ fail("{intr}::<{imm}>", &bytes{w}(a), &bytes{w}(b), &format!("{{:?}} vs {{:?}}", got, want)); }}
    }}"""
    cases.append((f"{intr}_{imm}", body))

for w in (128, 256):
    p = P(w)
    for intr, ref, vin, vout, f in [
        ("add_epi8", "ref_add8", "B", "B", None), ("sub_epi8", "ref_sub8", "B", "B", None),
        ("adds_epu8", "ref_adds_u8", "B", "B", None), ("subs_epu8", "ref_subs_u8", "B", "B", None),
        ("subs_epu16", "ref_subs_u16", "U16", "U16", None),
        ("adds_epi8", "ref_adds_s8", "B", "B", None), ("subs_epi8", "ref_subs_s8", "B", "B", None),
        ("packs_epi16", "ref_packs16_lanes", "U16", "B", None),
        ("min_epu8", "ref_min_u8", "B", "B", None), ("max_epu8", "ref_max_u8", "B", "B", None),
        ("avg_epu8", "ref_avg_u8", "B", "B", None), ("cmpeq_epi8", "ref_cmpeq8", "B", "B", None),
        ("cmpgt_epi8", "ref_cmpgt_s8", "B", "B", None),
        ("add_epi16", "ref_add16", "U16", "U16", None), ("sub_epi16", "ref_sub16", "U16", "U16", None),
        ("mullo_epi16", "ref_mullo16", "U16", "U16", None), ("mulhi_epi16", "ref_mulhi_s16", "U16", "U16", None),
        ("mulhi_epu16", "ref_mulhi_u16", "U16", "U16", None),
        ("unpacklo_epi16", "ref_unpacklo16_lanes", "U16", "U16", None), ("unpackhi_epi16", "ref_unpackhi16_lanes", "U16", "U16", None),
        ("unpackhi_epi64", "ref_unpackhi64_lanes", "U64", "U64", None),
        ("cmpeq_epi16", "ref_cmpeq16", "U16", "U16", None), ("madd_epi16", "ref_madd16", "U16", "U32", None),
        ("add_epi32", "ref_add32", "U32", "U32", None), ("sub_epi32", "ref_sub32", "U32", "U32", None),
        ("cmpeq_epi32", "ref_cmpeq32", "U32", "U32", None), ("cmpgt_epi32", "ref_cmpgt_s32", "U32", "U32", None),
        ("add_epi64", "ref_add64", "U64", "U64", None), ("sad_epu8", "ref_sad8", "B", "U64", None),
        ("unpacklo_epi8", "ref_unpacklo8_lanes", "B", "B", None), ("unpackhi_epi8", "ref_unpackhi8_lanes", "B", "B", None),
        ("unpacklo_epi32", "ref_unpacklo32_lanes", "U32", "U32", None), ("unpackhi_epi32", "ref_unpackhi32_lanes", "U32", "U32", None),
        ("unpacklo_epi64", "ref_unpacklo64_lanes", "U64", "U64", None), ("packus_epi16", "ref_packus16_lanes", "U16", "B", None),
        ("shuffle_epi8", "ref_shuffle8_lanes", "B", "B", "ssse3"), ("maddubs_epi16", "ref_maddubs", "B", "U16", "ssse3"),
    ]:
        binop(w, p + intr, ref + "({a}, {b})", vin, vout, f)
    sfx = "si128" if w == 128 else "si256"
    for op, ref in [("and", "ref_and8"), ("or", "ref_or8"), ("xor", "ref_xor8"), ("andnot", "ref_andnot8")]:
        binop(w, f"{p}{op}_{sfx}", ref + "({a}, {b})", "B", "B")
    # blendv (3 operands)
    cases.append((f"{p}blendv_epi8", f"""
    #[target_feature(enable = "{FEAT(w, 'sse4.1')}")]
    fn go(a: {V(w)}, b: {V(w)}, m: {V(w)}) -> {V(w)} {{ {p}blendv_epi8(a, b, m) }}
    let mut rng = Rng::new(0x5151{w});
    for _ in 0..{N} {{
        let (a, b, m) = (rng.v{w}(), rng.v{w}(), rng.v{w}());
        let got = bytes{w}(unsafe {{ go(a, b, m) }});
        let want = ref_blendv8(&bytes{w}(a), &bytes{w}(b), &bytes{w}(m));
        if got != want {{ fail("{p}blendv_epi8", &bytes{w}(a), &bytes{w}(b), "mismatch"); }}
    }}"""))
    # movemask
    cases.append((f"{p}movemask_epi8", f"""
    #[target_feature(enable = "{FEAT(w)}")]
    fn go(a: {V(w)}) -> i32 {{ {p}movemask_epi8(a) }}
    let mut rng = Rng::new(0x7777{w});
    for _ in 0..{N} {{
        let a = rng.v{w}();
        let got = unsafe {{ go(a) }} as u32 as u64;
        let want = ref_movemask(&bytes{w}(a));
        if got != want {{ fail("{p}movemask_epi8", &bytes{w}(a), &[], &format!("{{got:x}} vs {{want:x}}")); }}
    }}"""))
    IMMS = list(range(0, 18)) + [31, 32, 33, 63, 64, 127, 128, 255]
    for intr, ref, vin, vout in [("srli_epi16", "ref_srli16", "U16", "U16"), ("slli_epi16", "ref_slli16", "U16", "U16"),
                                 ("srai_epi16", "ref_srai16", "U16", "U16"), ("srli_epi32", "ref_srli32", "U32", "U32"),
                                 ("srai_epi32", "ref_srai32", "U32", "U32"),
                                 ("slli_epi32", "ref_slli32", "U32", "U32"), ("srli_epi64", "ref_srli64", "U64", "U64"),
                                 ("slli_epi64", "ref_slli64", "U64", "U64")]:
        # Every count a 64-bit lane can shift by, and some past it.
        for imm in (IMMS if vin != "U64" else list(range(0, 66)) + [127, 128, 255]):
            unop_imm(w, p + intr, imm, ref + "({a}, {imm})", vin, vout)
    for imm in range(256):
        unop_imm(w, p + "shuffle_epi32", imm, "ref_shuffle32_lanes({a}, {imm})", "U32", "U32")
    bsl = "_mm_slli_si128" if w == 128 else "_mm256_bslli_epi128"
    bsr = "_mm_srli_si128" if w == 128 else "_mm256_bsrli_epi128"
    for imm in list(range(0, 18)) + [31, 32, 255]:
        unop_imm(w, bsl, imm, "ref_bslli_lanes({a}, {imm})", "B", "B")
        unop_imm(w, bsr, imm, "ref_bsrli_lanes({a}, {imm})", "B", "B")
    for imm in list(range(0, 34)) + [255]:
        binop_imm(w, p + "alignr_epi8", imm, "ref_alignr_lanes({a}, {b}, {imm})", "ssse3")

# 128-bit only: what the SSE backend of the NEON wrappers adds.
binop(128, "_mm_adds_epu16", "ref_adds_u16({a}, {b})", "U16", "U16")
binop(128, "_mm_max_epu16", "ref_max_u16({a}, {b})", "U16", "U16", "sse4.1")
binop(128, "_mm_mullo_epi32", "ref_mullo32({a}, {b})", "U32", "U32", "sse4.1")
cases.append(("_mm_abs_epi16", f"""
    #[target_feature(enable = "ssse3")]
    fn go(a: __m128i) -> __m128i {{ _mm_abs_epi16(a) }}
    let mut rng = Rng::new(0x{seed("_mm_abs_epi16"):x});
    for _ in 0..{N} {{
        let a = rng.v128();
        let got = u16s128(unsafe {{ go(a) }});
        let want = ref_abs16(&u16s128(a));
        if got != want {{ fail("_mm_abs_epi16", &bytes128(a), &[], &format!("{{:?}} vs {{:?}}", got, want)); }}
    }}"""))
for intr, ref, view, lim in [("_mm_sll_epi16", "ref_slli16", "u16s", 16), ("_mm_sra_epi16", "ref_srai16", "u16s", 16),
                             ("_mm_sll_epi32", "ref_slli32", "u32s", 32), ("_mm_sra_epi32", "ref_srai32", "u32s", 32)]:
    cases.append((intr, f"""
    #[target_feature(enable = "sse2")]
    fn go(a: __m128i, c: __m128i) -> __m128i {{ {intr}(a, c) }}
    let mut rng = Rng::new(0x{seed(intr):x});
    for it in 0..{N} {{
        let a = rng.v128();
        let n = (it % {lim}) as u32;
        let got = {view}128(unsafe {{ go(a, _mm_cvtsi32_si128(n as i32)) }});
        let want = {ref}(&{view}128(a), n);
        if got != want {{ fail("{intr}", &bytes128(a), &[], &format!("{{n}}: {{:?}} vs {{:?}}", got, want)); }}
    }}"""))

# constructors and moves, checked directly against the spec's meaning
cases.append(("constructors", f"""
    let mut rng = Rng::new(0xc0c0);
    #[target_feature(enable = "avx2")]
    fn s256(x8: i8, x16: i16, x32: i32, x64: i64) -> [__m256i; 4] {{
        [_mm256_set1_epi8(x8), _mm256_set1_epi16(x16), _mm256_set1_epi32(x32), _mm256_set1_epi64x(x64)]
    }}
    #[target_feature(enable = "sse2")]
    fn s128(x8: i8, x16: i16, x32: i32, x64: i64) -> [__m128i; 4] {{
        [_mm_set1_epi8(x8), _mm_set1_epi16(x16), _mm_set1_epi32(x32), _mm_set1_epi64x(x64)]
    }}
    for _ in 0..{N} {{
        let (x8, x16, x32, x64) = (rng.next() as i8, rng.next() as i16, rng.next() as i32, rng.next() as i64);
        let v = unsafe {{ s256(x8, x16, x32, x64) }};
        assert_eq!(bytes256(v[0]), vec![u8_of_i8(x8); 32]);
        assert_eq!(u16s256(v[1]), vec![u16_of_i16(x16); 16]);
        assert_eq!(u32s256(v[2]), vec![u32_of_i32(x32); 8]);
        assert_eq!(u64s256(v[3]), vec![u64_of_i64(x64); 4]);
        let v = unsafe {{ s128(x8, x16, x32, x64) }};
        assert_eq!(bytes128(v[0]), vec![u8_of_i8(x8); 16]);
        assert_eq!(u16s128(v[1]), vec![u16_of_i16(x16); 8]);
        assert_eq!(u32s128(v[2]), vec![u32_of_i32(x32); 4]);
        assert_eq!(u64s128(v[3]), vec![u64_of_i64(x64); 2]);
        assert_eq!(u32s128(_mm_cvtsi32_si128(x32)), vec![u32_of_i32(x32), 0, 0, 0]);
        assert_eq!(u64s128(_mm_cvtsi64_si128(x64)), vec![u64_of_i64(x64), 0]);
        let a = rng.v128();
        assert_eq!(u32_of_i32(_mm_cvtsi128_si32(a)), u32s128(a)[0]);
        assert_eq!(u64_of_i64(_mm_cvtsi128_si64(a)), u64s128(a)[0]);
    }}
    assert_eq!(bytes128(_mm_setzero_si128()), vec![0u8; 16]);
    #[target_feature(enable = "avx2")]
    fn z() -> __m256i {{ _mm256_setzero_si256() }}
    assert_eq!(bytes256(unsafe {{ z() }}), vec![0u8; 32]);
    let e: Vec<i8> = (0..32).map(|_| rng.next() as i8).collect();
    let v = _mm_setr_epi8(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9], e[10], e[11], e[12], e[13], e[14], e[15]);
    assert_eq!(bytes128(v), e[..16].iter().map(|&x| u8_of_i8(x)).collect::<Vec<_>>());
    #[target_feature(enable = "avx2")]
    fn r8(e: &[i8]) -> __m256i {{
        _mm256_setr_epi8(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9], e[10], e[11], e[12], e[13], e[14], e[15],
            e[16], e[17], e[18], e[19], e[20], e[21], e[22], e[23], e[24], e[25], e[26], e[27], e[28], e[29], e[30], e[31])
    }}
    assert_eq!(bytes256(unsafe {{ r8(&e) }}), e.iter().map(|&x| u8_of_i8(x)).collect::<Vec<_>>());
    let d: Vec<i32> = (0..8).map(|_| rng.next() as i32).collect();
    assert_eq!(u32s128(_mm_setr_epi32(d[0], d[1], d[2], d[3])), d[..4].iter().map(|&x| u32_of_i32(x)).collect::<Vec<_>>());
    #[target_feature(enable = "avx2")]
    fn r32(d: &[i32]) -> __m256i {{ _mm256_setr_epi32(d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7]) }}
    assert_eq!(u32s256(unsafe {{ r32(&d) }}), d.iter().map(|&x| u32_of_i32(x)).collect::<Vec<_>>());
"""))
cases.append(("lanes256", f"""
    let mut rng = Rng::new(0x2560);
    #[target_feature(enable = "avx2")]
    fn go(a: __m256i, _b: __m256i, lo: __m128i, hi: __m128i, idx: __m256i)
        -> (__m128i, __m128i, __m128i, __m256i, __m256i) {{
        (_mm256_castsi256_si128(a), _mm256_extracti128_si256::<0>(a), _mm256_extracti128_si256::<1>(a),
         _mm256_set_m128i(hi, lo), _mm256_permutevar8x32_epi32(a, idx))
    }}
    for _ in 0..{N} {{
        let (a, b, lo, hi, idx) = (rng.v256(), rng.v256(), rng.v128(), rng.v128(), rng.v256());
        let (c, e0, e1, s, p) = unsafe {{ go(a, b, lo, hi, idx) }};
        let ab = bytes256(a);
        assert_eq!(bytes128(c), ab[..16].to_vec());
        assert_eq!(bytes128(e0), ab[..16].to_vec());
        assert_eq!(bytes128(e1), ab[16..].to_vec());
        let mut cat = bytes128(lo); cat.extend(bytes128(hi));
        assert_eq!(bytes256(s), cat);
        assert_eq!(u32s256(p), ref_permvar32(&u32s256(a), &u32s256(idx)));
        let _ = b;
    }}
"""))
for imm in range(256):
    cases.append((f"_mm256_permute2x128_si256_{imm}", f"""
    #[target_feature(enable = "avx2")]
    fn go(a: __m256i, b: __m256i) -> __m256i {{ _mm256_permute2x128_si256::<{imm}>(a, b) }}
    let mut rng = Rng::new({imm + 1});
    for _ in 0..{N}/64 {{
        let (a, b) = (rng.v256(), rng.v256());
        let got = bytes256(unsafe {{ go(a, b) }});
        let (ab, bb) = (bytes256(a), bytes256(b));
        let half = |sel: u32| -> Vec<u8> {{
            if sel & 8 != 0 {{ vec![0; 16] }} else {{
                match sel & 3 {{ 0 => ab[..16].to_vec(), 1 => ab[16..].to_vec(), 2 => bb[..16].to_vec(), _ => bb[16..].to_vec() }}
            }}
        }};
        let mut want = half({imm} & 15); want.extend(half({imm} >> 4));
        assert_eq!(got, want, "_mm256_permute2x128_si256::<{imm}>");
    }}"""))

out = ["""//! Differential test of every trusted intrinsic specification.
//!
//! GENERATED by `tools/gen_difftest.py`.
//!
//! For each intrinsic in `src/x86.rs`, random and edge-biased inputs are run
//! through the CPU and through the verified reference implementation of the
//! intrinsic's specification (`verilith_simd::refs`); any difference fails the test.
//! `VSIMD_ITERS` sets the number of random inputs per intrinsic (default
//! 1,000,000; immediate-operand variants run a sixteenth of that each).
#![cfg(target_arch = "x86_64")]
#![allow(unused_unsafe, non_snake_case)]
use core::arch::x86_64::*;
use verilith_simd::refs::*;
use verilith_simd::refs_neon::{ref_abs16, ref_adds_u16, ref_max_u16, ref_mullo32};

fn iters() -> usize {
    std::env::var("VSIMD_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(1_000_000)
}

struct Rng(u64);
impl Rng {
    fn new(s: u64) -> Rng { Rng(s.wrapping_mul(0x9E3779B97F4A7C15) | 1) }
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0
    }
    /// A byte: uniform, or (one time in four) an edge value.
    fn byte(&mut self) -> u8 {
        let r = self.next();
        if r % 4 == 0 { [0u8, 1, 2, 0x7e, 0x7f, 0x80, 0x81, 0xfe, 0xff][(r >> 8) as usize % 9] } else { (r >> 16) as u8 }
    }
    fn bytes<const N: usize>(&mut self) -> [u8; N] {
        let mut b = [0u8; N];
        let mode = self.next() % 8;
        for x in b.iter_mut() { *x = if mode == 0 { (self.next() >> 20) as u8 } else { self.byte() }; }
        b
    }
    fn v128(&mut self) -> __m128i { unsafe { core::mem::transmute(self.bytes::<16>()) } }
    fn v256(&mut self) -> __m256i { unsafe { core::mem::transmute(self.bytes::<32>()) } }
    /// `a` with a few bytes changed (exercises equal / nearly-equal lanes).
    fn near128(&mut self, a: __m128i) -> __m128i {
        let mut b: [u8; 16] = unsafe { core::mem::transmute(a) };
        for _ in 0..(self.next() % 3) { let i = self.next() as usize % 16; b[i] = b[i].wrapping_add(self.next() as u8 % 3); }
        unsafe { core::mem::transmute(b) }
    }
    fn near256(&mut self, a: __m256i) -> __m256i {
        let mut b: [u8; 32] = unsafe { core::mem::transmute(a) };
        for _ in 0..(self.next() % 3) { let i = self.next() as usize % 32; b[i] = b[i].wrapping_add(self.next() as u8 % 3); }
        unsafe { core::mem::transmute(b) }
    }
}

// The views, as `verilith_simd::lanes` defines them: bytes in memory order, wider
// lanes little-endian.
fn bytes128(v: __m128i) -> Vec<u8> { let b: [u8; 16] = unsafe { core::mem::transmute(v) }; b.to_vec() }
fn bytes256(v: __m256i) -> Vec<u8> { let b: [u8; 32] = unsafe { core::mem::transmute(v) }; b.to_vec() }
fn u16s(b: &[u8]) -> Vec<u16> { b.chunks(2).map(|c| u16::from_le_bytes([c[0], c[1]])).collect() }
fn u32s(b: &[u8]) -> Vec<u32> { b.chunks(4).map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect() }
fn u64s(b: &[u8]) -> Vec<u64> { b.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect() }
fn u16s128(v: __m128i) -> Vec<u16> { u16s(&bytes128(v)) }
fn u32s128(v: __m128i) -> Vec<u32> { u32s(&bytes128(v)) }
fn u64s128(v: __m128i) -> Vec<u64> { u64s(&bytes128(v)) }
fn u16s256(v: __m256i) -> Vec<u16> { u16s(&bytes256(v)) }
fn u32s256(v: __m256i) -> Vec<u32> { u32s(&bytes256(v)) }
fn u64s256(v: __m256i) -> Vec<u64> { u64s(&bytes256(v)) }
// `ops::u8_of_i8` etc.: two's complement.
fn u8_of_i8(x: i8) -> u8 { x as u8 }
fn u16_of_i16(x: i16) -> u16 { x as u16 }
fn u32_of_i32(x: i32) -> u32 { x as u32 }
fn u64_of_i64(x: i64) -> u64 { x as u64 }

fn fail(what: &str, a: &[u8], b: &[u8], detail: &str) -> ! {
    panic!("{what} disagrees with its specification\\n  a = {a:02x?}\\n  b = {b:02x?}\\n  {detail}");
}

fn need_avx2() -> bool {
    if !std::is_x86_feature_detected!("avx2") { eprintln!("skipping: no AVX2"); return false; }
    true
}
"""]
for name, body in cases:
    nm = name.lstrip("_")
    out.append(f"#[test]\nfn {nm}() {{\n    if !need_avx2() {{ return; }}\n    #[target_feature(enable = \"avx2\")]\n    fn body(ITERS: usize) {{{body}\n    }}\n    unsafe {{ body(iters()) }}\n}}\n")
open(sys.argv[1], "w").write("\n".join(out))
print(len(cases), "tests")
