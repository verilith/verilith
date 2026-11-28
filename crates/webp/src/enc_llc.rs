//! Writing a prefix code's lengths (RFC 9649 §3.7.2.1.2, the "normal" code
//! length code), proven to read back under `spec::read_code`.
use crate::enc_bw::*;
use crate::enc_code::*;
#[cfg(verus_only)]
use crate::enc_lem::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// What is written
// ---------------------------------------------------------------------------
/// The place of code length symbol `s` in `cl_order`.
pub open spec fn clinv(s: int) -> int {
    seq![2int, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 8, 0, 1][s]
}

pub open spec fn clinv_ok(k: int) -> bool
    decreases 19 - k,
{
    if k >= 19 {
        true
    } else {
        cl_order()[k] < 19 && clinv(cl_order()[k] as int) == k && 0 <= clinv(k) < 19 && cl_order()[clinv(k)]
            == k && clinv_ok(k + 1)
    }
}

proof fn lemma_clinv_from(k: int)
    requires
        0 <= k,
        clinv_ok(k),
    ensures
        forall|j: int| k <= j < 19 ==> cl_order()[j] < 19 && #[trigger] clinv(cl_order()[j] as int) == j,
        forall|s: int| k <= s < 19 ==> 0 <= clinv(s) < 19 && #[trigger] cl_order()[clinv(s)] == s,
    decreases 19 - k,
{
    if k < 19 {
        lemma_clinv_from(k + 1);
    }
}

pub proof fn lemma_clinv()
    ensures
        forall|j: int| 0 <= j < 19 ==> cl_order()[j] < 19 && #[trigger] clinv(cl_order()[j] as int) == j,
        forall|s: int| 0 <= s < 19 ==> 0 <= clinv(s) < 19 && #[trigger] cl_order()[clinv(s)] == s,
{
    assert(clinv_ok(0)) by (compute_only);
    lemma_clinv_from(0);
}

/// The codes of the first `i` lengths, in the code length code `cl`.
pub open spec fn lens_syms(cl: Seq<u8>, lens: Seq<u8>, i: int) -> Seq<nat>
    decreases i,
{
    if i <= 0 {
        Seq::empty()
    } else {
        lens_syms(cl, lens, i - 1) + code_of(cl, lens[i - 1] as int)
    }
}

/// The first `k` lengths of the code length code, 3 bits each, in
/// `cl_order`.
pub open spec fn cl_fields(cl: Seq<u8>, k: int) -> Seq<nat>
    decreases k,
{
    if k <= 0 {
        Seq::empty()
    } else {
        cl_fields(cl, k - 1) + fld(cl[cl_order()[k - 1] as int] as nat, 3)
    }
}

/// A code written with a normal code length code `cl` of all 19 lengths,
/// and every length sent (no `max_symbol`, no repeat codes).
pub open spec fn normal_bits(cl: Seq<u8>, lens: Seq<u8>) -> Seq<nat> {
    fld(0, 1) + (fld(15, 4) + (cl_fields(cl, 19) + (fld(0, 1) + lens_syms(cl, lens, lens.len() as int))))
}

/// Lengths that can be written with `cl`.
pub open spec fn cl_fits(cl: Seq<u8>, lens: Seq<u8>) -> bool {
    &&& cl.len() == 19
    &&& forall|s: int| 0 <= s < 19 ==> #[trigger] cl[s] < 8
    &&& valid_code(cl)
    &&& lens_ok(cl)
    &&& forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] < 16 && 1 <= cl[lens[i] as int]
    &&& used(cl) == 1 ==> forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] as int == first_used(cl, 0)
    &&& valid_code(lens)
    &&& lens.len() >= 1
}

// ---------------------------------------------------------------------------
// Reading it back
// ---------------------------------------------------------------------------
proof fn lemma_cl_fields_len(cl: Seq<u8>, k: int)
    requires
        0 <= k,
    ensures
        cl_fields(cl, k).len() == 3 * k,
    decreases k,
{
    if k > 0 {
        lemma_cl_fields_len(cl, k - 1);
        lemma_bits_of(cl[cl_order()[k - 1] as int] as nat, 3);
    }
}

/// The fields read back.
proof fn lemma_cl_reads(b: Seq<u8>, u: Seq<nat>, cl: Seq<u8>, k: int, rest: Seq<nat>)
    requires
        0 <= k <= 19,
        cl.len() == 19,
        forall|s: int| 0 <= s < 19 ==> #[trigger] cl[s] < 8,
        ext(b, u + (cl_fields(cl, k) + rest)),
    ensures
        forall|j: int|
            0 <= j < k ==> #[trigger] bits(b, u.len() + 3 * j, 3) == cl[cl_order()[j] as int] as nat,
    decreases k,
{
    if k > 0 {
        let x = cl[cl_order()[k - 1] as int] as nat;
        lemma_clinv();
        lemma_pow2_small();
        assert(cl_fields(cl, k) == cl_fields(cl, k - 1) + fld(x, 3));
        assert(u + (cl_fields(cl, k) + rest) =~= u + (cl_fields(cl, k - 1) + (fld(x, 3) + rest)));
        lemma_cl_reads(b, u, cl, k - 1, fld(x, 3) + rest);
        assert(u + (cl_fields(cl, k - 1) + (fld(x, 3) + rest)) =~= (u + cl_fields(cl, k - 1)) + (fld(x, 3) + rest));
        lemma_rd(b, u + cl_fields(cl, k - 1), x, 3, rest);
        lemma_cl_fields_len(cl, k - 1);
    }
}

/// `cl_lens` after `i` fields.
proof fn lemma_cl_lens(b: Seq<u8>, p: int, cl: Seq<u8>, i: int)
    requires
        0 <= i <= 19,
        cl.len() == 19,
        forall|j: int| 0 <= j < 19 ==> #[trigger] bits(b, p + 3 * j, 3) == cl[cl_order()[j] as int] as nat,
    ensures
        cl_lens(b, p, i as nat) == Seq::new(19, |s: int| if clinv(s) < i { cl[s] } else { 0u8 }),
    decreases i,
{
    lemma_clinv();
    if i == 0 {
        assert(cl_lens(b, p, 0) =~= Seq::new(19, |s: int| if clinv(s) < i { cl[s] } else { 0u8 }));
    } else {
        lemma_cl_lens(b, p, cl, i - 1);
        let o = cl_order()[i - 1] as int;
        assert(bits(b, p + 3 * (i - 1), 3) == cl[o] as nat);
        assert(cl_lens(b, p, i as nat) =~= Seq::new(19, |s: int| if clinv(s) < i { cl[s] } else { 0u8 }));
    }
}

/// The lengths after the first `j` are read.
pub open spec fn part(lens: Seq<u8>, j: int) -> Seq<u8> {
    Seq::new(lens.len(), |i: int| if i < j { lens[i] } else { 0u8 })
}

#[verifier::spinoff_prover]
/// `read_lens` reads the codes of lengths `j..` back.
proof fn lemma_read_lens(b: Seq<u8>, u: Seq<nat>, cl: Seq<u8>, lens: Seq<u8>, j: int, prev: u8, rest: Seq<nat>)
    requires
        cl_fits(cl, lens),
        0 <= j <= lens.len(),
        ext(b, u + (lens_syms(cl, lens, lens.len() as int) + rest)),
    ensures
        read_lens(
            cl,
            b,
            (u.len() + lens_syms(cl, lens, j).len()) as int,
            lens.len(),
            (lens.len() - j) as nat,
            j as nat,
            prev,
            part(lens, j),
        ) == Some((lens, (u.len() + lens_syms(cl, lens, lens.len() as int).len()) as int)),
    decreases lens.len() - j,
{
    hide(read_symbol);
    hide(valid_code);
    hide(code_of);
    hide(lens_ok);
    hide(ext);
    let n = lens.len() as int;
    if j == n {
        assert(part(lens, j) =~= lens);
    } else {
        let c = lens[j] as int;
        let w = u + lens_syms(cl, lens, j);
        let tail = lens_syms_from(cl, lens, j + 1);
        lemma_syms_split(cl, lens, j);
        assert(lens_syms_from(cl, lens, j) == code_of(cl, c) + tail);
        assert(lens_syms(cl, lens, j + 1) == lens_syms(cl, lens, j) + code_of(cl, c));
        assert(u + (lens_syms(cl, lens, n) + rest) =~= w + (code_of(cl, c) + (tail + rest)));
        assert(1 <= cl[c]);
        lemma_sym(b, w, cl, c, tail + rest);
        assert(part(lens, j).update(j, c as u8) =~= part(lens, j + 1));
        lemma_read_lens(b, u, cl, lens, j + 1, if c != 0 { c as u8 } else { prev }, rest);
    }
}

/// The codes of lengths `j..`.
pub open spec fn lens_syms_from(cl: Seq<u8>, lens: Seq<u8>, j: int) -> Seq<nat>
    decreases lens.len() - j,
{
    if j >= lens.len() {
        Seq::empty()
    } else {
        code_of(cl, lens[j] as int) + lens_syms_from(cl, lens, j + 1)
    }
}

proof fn lemma_syms_split(cl: Seq<u8>, lens: Seq<u8>, j: int)
    requires
        0 <= j <= lens.len(),
    ensures
        lens_syms(cl, lens, lens.len() as int) == lens_syms(cl, lens, j) + lens_syms_from(cl, lens, j),
    decreases lens.len() - j,
{
    if j == lens.len() {
        assert(lens_syms(cl, lens, j) + lens_syms_from(cl, lens, j) =~= lens_syms(cl, lens, j));
    } else {
        lemma_syms_split(cl, lens, j + 1);
        assert(lens_syms(cl, lens, j) + lens_syms_from(cl, lens, j) =~= lens_syms(cl, lens, j + 1)
            + lens_syms_from(cl, lens, j + 1));
    }
}

#[verifier::spinoff_prover]
/// The theorem: a code written as `normal_bits` reads back as its lengths.
pub proof fn lemma_normal(b: Seq<u8>, w: Seq<nat>, cl: Seq<u8>, lens: Seq<u8>, rest: Seq<nat>)
    requires
        cl_fits(cl, lens),
        ext(b, w + (normal_bits(cl, lens) + rest)),
    ensures
        read_code(b, w.len() as int, lens.len()) == Some((lens, (w.len() + normal_bits(cl, lens).len()) as int)),
{
    hide(read_lens);
    hide(cl_lens);
    hide(valid_code);
    hide(lens_syms);
    hide(cl_fields);
    hide(fld);
    hide(ext);
    let p0 = w.len() as int;
    let syms = lens_syms(cl, lens, lens.len() as int);
    lemma_pow2_small();
    lemma_clinv();
    // The first bit: not simple.
    assert(w + (normal_bits(cl, lens) + rest) =~= w + (fld(0, 1) + ((fld(15, 4) + (cl_fields(cl, 19) + (fld(0, 1)
        + syms))) + rest)));
    lemma_rd(b, w, 0, 1, (fld(15, 4) + (cl_fields(cl, 19) + (fld(0, 1) + syms))) + rest);
    let w1 = w + fld(0, 1);
    assert(w + (fld(0, 1) + ((fld(15, 4) + (cl_fields(cl, 19) + (fld(0, 1) + syms))) + rest)) =~= w1 + (fld(15, 4) + ((
    cl_fields(cl, 19) + (fld(0, 1) + syms)) + rest)));
    lemma_rd(b, w1, 15, 4, (cl_fields(cl, 19) + (fld(0, 1) + syms)) + rest);
    let w2 = w1 + fld(15, 4);
    assert(w1 + (fld(15, 4) + ((cl_fields(cl, 19) + (fld(0, 1) + syms)) + rest)) =~= w2 + (cl_fields(cl, 19) + ((fld(0,
    1) + syms) + rest)));
    lemma_cl_reads(b, w2, cl, 19, (fld(0, 1) + syms) + rest);
    lemma_cl_lens(b, w2.len() as int, cl, 19);
    assert(cl_lens(b, w2.len() as int, 19) =~= cl);
    lemma_cl_fields_len(cl, 19);
    let w3 = w2 + cl_fields(cl, 19);
    assert(w2 + (cl_fields(cl, 19) + ((fld(0, 1) + syms) + rest)) =~= w3 + (fld(0, 1) + (syms + rest)));
    lemma_rd(b, w3, 0, 1, syms + rest);
    let w4 = w3 + fld(0, 1);
    assert(w3 + (fld(0, 1) + (syms + rest)) =~= w4 + (syms + rest));
    lemma_ext2(b, w4, syms, rest);
    assert(w4.len() == p0 + 1 + 4 + 57 + 1);
    assert(lens_syms(cl, lens, 0).len() == 0) by { reveal_with_fuel(lens_syms, 1); }
    assert(part(lens, 0) =~= zeros(lens.len()));
    lemma_read_lens(b, w4, cl, lens, 0, 8, rest);
    assert(normal_bits(cl, lens).len() == 1 + 4 + 57 + 1 + syms.len());
    assert(read_normal(b, p0 + 1, lens.len()) == Some((lens, (w4.len() + syms.len()) as int)));
}

} // verus!
// x
