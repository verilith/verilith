#!/usr/bin/env python3
"""Generates src/refs.rs: tools/refs_head.rs (hand-written references and
helpers) followed by the elementwise references from the table below."""
import os, sys
# (name, spec fn, in elem type, out elem type, nargs, exec expr per i, extra proof)
EW = [
 ("add8", "u8", "u8", 2, "((a[i] as u16 + b[i] as u16) % 256) as u8"),
 ("sub8", "u8", "u8", 2, "((a[i] as u16 + 256 - b[i] as u16) % 256) as u8"),
 ("adds_u8", "u8", "u8", 2, "if a[i] as u16 + b[i] as u16 > 255 { 255u8 } else { a[i] + b[i] }"),
 ("subs_u8", "u8", "u8", 2, "if a[i] < b[i] { 0u8 } else { a[i] - b[i] }"),
 ("adds_s8", "u8", "u8", 2, "sat_s8e(s8e(a[i]) as i32 + s8e(b[i]) as i32)"),
 ("subs_s8", "u8", "u8", 2, "sat_s8e(s8e(a[i]) as i32 - s8e(b[i]) as i32)"),
 ("subs_u16", "u16", "u16", 2, "if a[i] < b[i] { 0u16 } else { a[i] - b[i] }"),
 ("min_u8", "u8", "u8", 2, "if a[i] < b[i] { a[i] } else { b[i] }"),
 ("max_u8", "u8", "u8", 2, "if a[i] > b[i] { a[i] } else { b[i] }"),
 ("avg_u8", "u8", "u8", 2, "((a[i] as u16 + b[i] as u16 + 1) / 2) as u8"),
 ("and8", "u8", "u8", 2, "a[i] & b[i]"),
 ("or8", "u8", "u8", 2, "a[i] | b[i]"),
 ("xor8", "u8", "u8", 2, "a[i] ^ b[i]"),
 ("andnot8", "u8", "u8", 2, "!a[i] & b[i]"),
 ("cmpeq8", "u8", "u8", 2, "if a[i] == b[i] { 0xffu8 } else { 0u8 }"),
 ("cmple_u8", "u8", "u8", 2, "if a[i] <= b[i] { 0xffu8 } else { 0u8 }"),
 ("testm8", "u8", "u8", 2, "if a[i] & b[i] != 0 { 0xffu8 } else { 0u8 }"),
 ("cmpgt_s8", "u8", "u8", 2, "if s8e(a[i]) > s8e(b[i]) { 0xffu8 } else { 0u8 }"),
 ("add16", "u16", "u16", 2, "((a[i] as u32 + b[i] as u32) % 0x10000) as u16"),
 ("sub16", "u16", "u16", 2, "((a[i] as u32 + 0x10000 - b[i] as u32) % 0x10000) as u16"),
 ("mullo16", "u16", "u16", 2, "mullo1(a[i], b[i])"),
 ("mulhi_s16", "u16", "u16", 2, "mulhi1(a[i], b[i])"),
 ("qdmulh_s16", "u16", "u16", 2, "qdmulh1(a[i], b[i])"),
 ("mulhi_u16", "u16", "u16", 2, "mulhiu1(a[i], b[i])"),
 ("cmpeq16", "u16", "u16", 2, "if a[i] == b[i] { 0xffffu16 } else { 0u16 }"),
 ("add32", "u32", "u32", 2, "((a[i] as u64 + b[i] as u64) % 0x1_0000_0000) as u32"),
 ("sub32", "u32", "u32", 2, "((a[i] as u64 + 0x1_0000_0000 - b[i] as u64) % 0x1_0000_0000) as u32"),
 ("add64", "u64", "u64", 2, "((a[i] as u128 + b[i] as u128) % 0x1_0000_0000_0000_0000) as u64"),
 ("cmpeq32", "u32", "u32", 2, "if a[i] == b[i] { 0xffff_ffffu32 } else { 0u32 }"),
 ("cmpgt_s32", "u32", "u32", 2, "if s32e(a[i]) > s32e(b[i]) { 0xffff_ffffu32 } else { 0u32 }"),
]
out = []
P = out.append
for name, ti, to, n, expr in EW:
    P(f"""pub fn ref_{name}(a: &[{ti}], b: &[{ti}]) -> (r: Vec<{to}>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == {name}(a@, b@),
{{
    let mut r: Vec<{to}> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] {name}(a@, b@)[j],
        decreases a.len() - i,
    {{
        let v = {expr};
        r.push(v);
        i = i + 1;
    }}
    assert(r@ =~= {name}(a@, b@));
    r
}}
""")
head = open(os.path.join(os.path.dirname(__file__), "refs_head.rs")).read()
open(sys.argv[1], "w").write(head + "\n".join(out) + "\n} // verus!\n")
