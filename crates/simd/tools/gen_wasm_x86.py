#!/usr/bin/env python3
"""Generates src/wasm_x86.rs: tools/wasm_x86_head.rs (helpers and lemmas)
followed by, for each function below, its contract copied from src/wasm.rs
and a body of SSE intrinsics proven against that contract.
    python3 tools/gen_wasm_x86.py src/wasm_x86.rs"""
import os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "..", "src", "wasm.rs")).read()
def contract(name):
    m = re.search(r'\n((?:///[^\n]*\n)*)#\[verifier::external_body\]\n#\[inline\(always\)\]\n(pub fn ' + name + r'\b[^\n]*\n(?:(?!\{\n).*\n)*?)\{\n', src)
    assert m, name
    return m.group(1), m.group(2)

def shufmask(ix):
    ka = [i if i < 16 else -128 for i in ix]
    kb = [i - 16 if i >= 16 else -128 for i in ix]
    return ka, kb

B = {}
def bin_(name, intr, view, op=None):
    B[name] = f"""    let r = u({intr}(m(a), m(b)));
    proof {{
        assert({view}(n8(r)) =~= {view}(n8(r)));
    }}
    r"""

for n, i, v in [("w_add16", "_mm_add_epi16", "u16s"), ("w_sub16", "_mm_sub_epi16", "u16s"),
                ("w_add32", "_mm_add_epi32", "u32s"), ("w_sub32", "_mm_sub_epi32", "u32s"),
                ("w_mul16", "_mm_mullo_epi16", "u16s"), ("w_mul32", "_mm_mullo_epi32", "u32s"),
                ("w_add_sat_u16", "_mm_adds_epu16", "u16s"), ("w_max_u16", "_mm_max_epu16", "u16s"),
                ("w_narrow_s16", "_mm_packs_epi16", "n8"), ("w_narrow_u16", "_mm_packus_epi16", "n8"),
                ("w_narrow_s32", "_mm_packs_epi32", "u16s"), ("w_xor", "_mm_xor_si128", "n8"),
                ("w_zip_lo16", "_mm_unpacklo_epi16", "u16s"), ("w_zip_hi16", "_mm_unpackhi_epi16", "u16s"),
                ("w_zip_lo32", "_mm_unpacklo_epi32", "u32s"), ("w_zip_hi32", "_mm_unpackhi_epi32", "u32s"),
                ("w_zip_lo64", "_mm_unpacklo_epi64", "u64s"), ("w_zip_hi64", "_mm_unpackhi_epi64", "u64s"),
                ("w_zip_lo8", "_mm_unpacklo_epi8", "n8"), ("w_zip_hi8", "_mm_unpackhi_epi8", "n8")]:
    B[n] = f"    u({i}(m(a), m(b)))"

B["w_abs16"] = "    u(_mm_abs_epi16(m(a)))"
B["w_splat8"] = """    let r = u(_mm_set1_epi8(crate::sse2::i8_of(x)));
    proof {
        assert(n8(r) =~= Seq::new(16, |i: int| x));
    }
    r"""
B["w_splat16"] = """    let r = u(_mm_set1_epi16(i16_of(x)));
    proof {
        assert(u16s(n8(r)) =~= Seq::new(8, |i: int| x));
    }
    r"""
B["w_splat32"] = """    let r = u(_mm_set1_epi32(i32_of(x)));
    proof {
        assert(u32s(n8(r)) =~= Seq::new(4, |i: int| x));
    }
    r"""
B["w_extend_lo8"] = """    let r = u(_mm_unpacklo_epi8(m(a), _mm_setzero_si128()));
    proof {
        lemma_zext(n8(a), n8(r), 0);
    }
    r"""
B["w_extend_hi8"] = """    let r = u(_mm_unpackhi_epi8(m(a), _mm_setzero_si128()));
    proof {
        lemma_zext(n8(a), n8(r), 8);
    }
    r"""
for lh, k in [("lo", "unpacklo"), ("hi", "unpackhi")]:
    off = "0" if lh == "lo" else "4"
    B[f"w_extmul_{lh}16"] = f"""    let z = _mm_setzero_si128();
    let x = _mm_{k}_epi16(m(a), z);
    let y = _mm_{k}_epi16(m(b), z);
    let r = u(_mm_madd_epi16(x, y));
    proof {{
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(n8(r))[i] == ((s16(u16s(n8(a))[{off} + i]) * s16(u16s(n8(b))[{off} + i])) % 0x1_0000_0000) as u32 by {{
            assert((2 * i) / 8 == 0 && (2 * i) % 8 == 2 * i && (2 * i + 1) / 8 == 0 && (2 * i + 1) % 8 == 2 * i + 1);
            assert((2 * i) % 2 == 0 && (2 * i + 1) % 2 == 1 && (2 * i) / 2 == i && (2 * i + 1) / 2 == i);
            assert(u16x8(z)[i] == 0u16) by {{
                assert(b128(z)[2 * i] == 0u8 && b128(z)[2 * i + 1] == 0u8);
                assert(((0u8 as u16) | ((0u8 as u16) << 8u16)) == 0u16) by (bit_vector);
            }}
            assert(u16x8(x)[2 * i] == u16s(n8(a))[{off} + i] && u16x8(x)[2 * i + 1] == 0);
            assert(u16x8(y)[2 * i] == u16s(n8(b))[{off} + i] && u16x8(y)[2 * i + 1] == 0);
            assert(s16(0u16) == 0);
            assert(s16(u16x8(x)[2 * i + 1]) * s16(u16x8(y)[2 * i + 1]) == 0);
            assert(u16x8(y)[2 * i] == u16s(n8(b))[{off} + i] && u16x8(y)[2 * i + 1] == 0);
        }}
        assert(u32s(n8(r)) =~= Seq::new(4, |i: int| ((s16(u16s(n8(a))[{off} + i]) * s16(u16s(n8(b))[{off} + i])) % 0x1_0000_0000) as u32));
    }}
    r"""
B["w_extadd16"] = """    let x = m(a);
    let lo = _mm_and_si128(x, _mm_setr_epi8(-1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0));
    let hi = _mm_srli_epi32::<16>(x);
    let r = u(_mm_add_epi32(lo, hi));
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] b128(lo)[j] == if j % 4 < 2 { n8(a)[j] } else { 0u8 } by {
            let c = n8(a)[j];
            assert(c & 255u8 == c) by (bit_vector);
            assert(c & 0u8 == 0u8) by (bit_vector);
        }
        lemma_extadd(n8(a), b128(lo), u32x4(hi));
        assert(u32s(n8(r)) =~= Seq::new(4, |i: int| (u16s(n8(a))[2 * i] + u16s(n8(a))[2 * i + 1]) as u32));
    }
    r"""
B["w_extract16_0"] = """    let v = _mm_cvtsi128_si32(m(a));
    let w = crate::sse2::u32_from(v);
    proof {
        lemma_u16s_of_u32s(n8(a));
        assert((w & 0xffff) as u16 == w as u16) by (bit_vector);
    }
    w as u16"""
B["w_extract32_0"] = """    let v = _mm_cvtsi128_si32(m(a));
    crate::sse2::u32_from(v)"""
B["w_extract64"] = """    let x = m(a);
    if L == 0 {
        let v = _mm_cvtsi128_si64(x);
        u64_from(v)
    } else {
        let h = _mm_unpackhi_epi64(x, x);
        let v = _mm_cvtsi128_si64(h);
        proof {
            assert(u64x2(h)[0] == u64x2(x)[1]);
        }
        u64_from(v)
    }"""
B["w_rot32_1"] = """    let x = m(a);
    let r = u(_mm_alignr_epi8::<4>(x, x));
    proof {
        lemma_rot_u32s(n8(a), n8(r), 1);
    }
    r"""
B["w_rot32_2"] = """    let x = m(a);
    let r = u(_mm_alignr_epi8::<8>(x, x));
    proof {
        lemma_rot_u32s(n8(a), n8(r), 2);
    }
    r"""
B["w_ext"] = """    u(_mm_alignr_epi8::<N>(m(b), m(a)))"""
B["w_dup16"] = """    let l = (2 * L) as i8;
    let h = (2 * L + 1) as i8;
    let k = _mm_setr_epi8(l, h, l, h, l, h, l, h, l, h, l, h, l, h, l, h);
    let r = u(_mm_shuffle_epi8(m(a), k));
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] u16s(n8(r))[i] == u16s(n8(a))[L as int] by {
            assert(b128(k)[2 * i] == 2 * L && b128(k)[2 * i + 1] == 2 * L + 1);
        }
        assert(u16s(n8(r)) =~= Seq::new(8, |i: int| u16s(n8(a))[L as int]));
    }
    r"""
for n, s, sh, v in [("w_shl16", "_mm_sll_epi16", 16, "u16s"), ("w_shr_s16", "_mm_sra_epi16", 16, "u16s"),
                     ("w_shl32", "_mm_sll_epi32", 32, "u32s"), ("w_shr_s32", "_mm_sra_epi32", 32, "u32s")]:
    B[n] = f"""    let c = _mm_cvtsi64_si128((n % {sh}) as i64);
    let r = u({s}(m(a), c));
    proof {{
        assert({v}(n8(r)) =~= {v}(n8(r)));
    }}
    r"""

def two(ix, a="a", b="b"):
    ka, kb = shufmask(ix)
    return f"""    let ka = _mm_setr_epi8({', '.join(map(str, ka))});
    let kb = _mm_setr_epi8({', '.join(map(str, kb))});
    let ghost ix = seq![{', '.join(f'{x}int' if j == 0 else str(x) for j, x in enumerate(ix))}];
    proof {{
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }}
    sh2({a}, {b}, ka, kb, Ghost(ix))"""
st3 = {
 "w_st3_ab0": [0, 16, 0, 1, 17, 0, 2, 18, 0, 3, 19, 0, 4, 20, 0, 5],
 "w_st3_ab1": [21, 0, 6, 22, 0, 7, 23, 0, 8, 24, 0, 9, 25, 0, 10, 26],
 "w_st3_ab2": [0, 11, 27, 0, 12, 28, 0, 13, 29, 0, 14, 30, 0, 15, 31, 0],
 "w_st3_c0": [0, 1, 16, 3, 4, 17, 6, 7, 18, 9, 10, 19, 12, 13, 20, 15],
 "w_st3_c1": [0, 21, 2, 3, 22, 5, 6, 23, 8, 9, 24, 11, 12, 25, 14, 15],
 "w_st3_c2": [26, 1, 2, 27, 4, 5, 28, 7, 8, 29, 10, 11, 30, 13, 14, 31],
}
for n, ix in st3.items():
    B[n] = two(ix)
B["w_even16"] = """    let r = {
""" + two([0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29]) + """
    };
    proof {
        lemma_pick16(n8(a), n8(b), n8(r), 0);
    }
    r"""
B["w_odd16"] = """    let r = {
""" + two([2, 3, 6, 7, 10, 11, 14, 15, 18, 19, 22, 23, 26, 27, 30, 31]) + """
    };
    proof {
        lemma_pick16(n8(a), n8(b), n8(r), 1);
    }
    r"""

ORDER = ["w_abs16", "w_add16", "w_sub16", "w_add32", "w_sub32", "w_mul16", "w_mul32",
    "w_add_sat_u16", "w_max_u16", "w_xor", "w_splat8", "w_splat16", "w_splat32", "w_dup16",
    "w_extend_lo8", "w_extend_hi8", "w_extmul_lo16", "w_extmul_hi16", "w_extadd16",
    "w_extract16_0", "w_extract32_0", "w_extract64", "w_narrow_s16", "w_narrow_u16",
    "w_narrow_s32", "w_zip_lo8", "w_zip_hi8", "w_zip_lo16", "w_zip_hi16", "w_zip_lo32",
    "w_zip_hi32", "w_zip_lo64", "w_zip_hi64", "w_even16", "w_odd16", "w_rot32_1", "w_rot32_2",
    "w_ext", "w_shl16", "w_shl32", "w_shr_s16", "w_shr_s32", "w_st3_ab0", "w_st3_ab1", "w_st3_ab2",
    "w_st3_c0", "w_st3_c1", "w_st3_c2"]
out = [open(os.path.join(here, "wasm_x86_head.rs")).read()]
for n in ORDER:
    doc, sig = contract(n)
    body = B[n]
    out.append(doc + "#[inline(always)]\n" + sig + "{\n    proof {\n        crate::neon::axiom_neon_x86();\n    }\n" + body + "\n}\n")
out.append("} // verus!\n")
open(sys.argv[1], "w").write("\n".join(out) + "\n")
