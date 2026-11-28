//! Names in wire form: comparison ignoring case, the bailiwick test, and
//! the random case of 0x20 queries. Proven against `spec`.
use crate::spec::*;
use vstd::prelude::*;

verus! {

#[inline(always)]
pub fn lower_byte(c: u8) -> (r: u8)
    ensures
        r == lower(c),
{
    if 65 <= c && c <= 90 {
        c + 32
    } else {
        c
    }
}

pub proof fn lemma_lower_idem(c: u8)
    ensures
        lower(lower(c)) == lower(c),
{
}

pub proof fn lemma_eq_ci_refl(a: Seq<u8>)
    ensures
        eq_ci(a, a),
{
}

pub proof fn lemma_eq_ci_sym(a: Seq<u8>, b: Seq<u8>)
    requires
        eq_ci(a, b),
    ensures
        eq_ci(b, a),
{
}

pub proof fn lemma_eq_ci_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        eq_ci(a, b),
        eq_ci(b, c),
    ensures
        eq_ci(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies lower(#[trigger] a[i]) == lower(c[i]) by {
        assert(lower(a[i]) == lower(b[i]));
        assert(lower(b[i]) == lower(c[i]));
    }
}

/// `eq_ci(w[off..], z)`.
pub fn eq_ci_from(w: &[u8], off: usize, z: &[u8]) -> (r: bool)
    requires
        off <= w@.len(),
    ensures
        r == eq_ci(w@.subrange(off as int, w@.len() as int), z@),
{
    let n = w.len() - off;
    if n != z.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == w@.len() - off,
            n == z@.len(),
            off <= w@.len(),
            i <= n,
            forall|j: int| 0 <= j < i ==> lower(#[trigger] w@[off + j]) == lower(z@[j]),
        decreases n - i,
    {
        if lower_byte(w[off + i]) != lower_byte(z[i]) {
            proof {
                let s = w@.subrange(off as int, w@.len() as int);
                assert(s[i as int] == w@[off + i]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        let s = w@.subrange(off as int, w@.len() as int);
        assert forall|j: int| 0 <= j < s.len() implies lower(#[trigger] s[j]) == lower(z@[j]) by {
            assert(s[j] == w@[off + j]);
        }
    }
    true
}

/// `eq_ci(a, b)`.
pub fn eq_ci_exec(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == eq_ci(a@, b@),
{
    let r = eq_ci_from(a, 0, b);
    proof {
        assert(a@.subrange(0, a@.len() as int) =~= a@);
    }
    r
}

/// `is_sub(w, z)`: `z` is `w` or an ancestor of it, ignoring case.
pub fn is_sub_exec(w: &[u8], z: &[u8]) -> (r: bool)
    ensures
        r == is_sub(w@, z@),
{
    let mut off: usize = 0;
    while off < w.len()
        invariant
            sub_from(w@, 0, z@) == sub_from(w@, off as int, z@),
        decreases w@.len() - off,
    {
        if eq_ci_from(w, off, z) {
            return true;
        }
        let c = w[off] as usize;
        if c == 0 || c + 1 >= w.len() - off {
            return false;
        }
        off = off + 1 + c;
    }
    false
}

/// `w` with ASCII letters folded to lowercase: the cache's key for a name.
pub fn lowered(w: &[u8]) -> (r: Vec<u8>)
    ensures
        r@.len() == w@.len(),
        forall|i: int| 0 <= i < w@.len() ==> #[trigger] r@[i] == lower(w@[i]),
        eq_ci(r@, w@),
{
    let mut r: Vec<u8> = Vec::with_capacity(w.len());
    let mut i: usize = 0;
    while i < w.len()
        invariant
            i <= w@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] r@[j] == lower(w@[j]),
        decreases w@.len() - i,
    {
        r.push(lower_byte(w[i]));
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < r@.len() implies lower(#[trigger] r@[j]) == lower(w@[j]) by {
            lemma_lower_idem(w@[j]);
        }
    }
    r
}

/// `w` with the case of its letters set by `bits` (0x20 randomization): a
/// letter whose bit is 1 is uppercase. The result is the same name.
pub fn mix_case(w: &[u8], bits: u64) -> (r: Vec<u8>)
    ensures
        eq_ci(r@, w@),
{
    let mut r: Vec<u8> = Vec::with_capacity(w.len());
    let mut i: usize = 0;
    let mut b = bits;
    while i < w.len()
        invariant
            i <= w@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> lower(#[trigger] r@[j]) == lower(w@[j]),
        decreases w@.len() - i,
    {
        let c = w[i];
        let l = lower_byte(c);
        let out = if 97 <= l && l <= 122 {
            let up = b % 2 == 1;
            b = b / 2;
            if b == 0 {
                b = bits;
            }
            if up { l - 32 } else { l }
        } else {
            c
        };
        r.push(out);
        i = i + 1;
    }
    r
}

/// Changing the zone to one equal ignoring case does not change `sub_from`.
pub proof fn lemma_sub_from_ci(w: Seq<u8>, off: int, z: Seq<u8>, z2: Seq<u8>)
    requires
        eq_ci(z, z2),
    ensures
        sub_from(w, off, z) == sub_from(w, off, z2),
    decreases w.len() - off,
{
    if off >= 0 && off < w.len() {
        let s = w.subrange(off, w.len() as int);
        if eq_ci(s, z) {
            lemma_eq_ci_trans(s, z, z2);
        } else if eq_ci(s, z2) {
            lemma_eq_ci_sym(z, z2);
            lemma_eq_ci_trans(s, z2, z);
        }
        if !(w[off] == 0 || off + 1 + w[off] as int >= w.len()) {
            lemma_sub_from_ci(w, off + 1 + w[off] as int, z, z2);
        }
    }
}

pub proof fn lemma_is_sub_ci(w: Seq<u8>, z: Seq<u8>, z2: Seq<u8>)
    requires
        eq_ci(z, z2),
    ensures
        is_sub(w, z) == is_sub(w, z2),
{
    lemma_sub_from_ci(w, 0, z, z2);
}

/// A name equal to `z` ignoring case is at or below `z`.
pub proof fn lemma_is_sub_self(w: Seq<u8>, z: Seq<u8>)
    requires
        eq_ci(w, z),
        w.len() > 0,
    ensures
        is_sub(w, z),
{
    assert(w.subrange(0, w.len() as int) =~= w);
}

} // verus!
