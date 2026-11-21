//! Verified presentation-format conversion: printing computes exactly
//! `spec_text::pres_name`, parsing computes exactly
//! `spec_text::parse_text_name`, and parsing a printed name gives the name
//! back (`theorem_text_roundtrip`), so no two names print the same.
use alloc::vec::Vec;
use crate::parse::append;
use crate::rdata::plain_name_end;
#[allow(unused_imports)]
use crate::lemmas::*;
#[allow(unused_imports)]
use crate::spec::*;
#[allow(unused_imports)]
use crate::spec_rdata::*;
#[allow(unused_imports)]
use crate::spec_text::*;
use vstd::prelude::*;

verus! {

proof fn lemma_digits(c: u8)
    ensures
        ((48 + c / 100) as u8 - 48) * 100 + ((48 + (c % 100) / 10) as u8 - 48) * 10 + ((48 + c
            % 10) as u8 - 48) == c as int,
        is_digit((48 + c / 100) as u8),
        is_digit((48 + (c % 100) / 10) as u8),
        is_digit((48 + c % 10) as u8),
{
    assert(c / 100 <= 2) by (nonlinear_arith)
        requires
            c < 256,
    ;
    assert((c / 100) * 100 + ((c % 100) / 10) * 10 + c % 10 == c) by (nonlinear_arith);
}

/// Reading the text of `l[j..]` back gives `l[j..]`, when what follows it is
/// the end or a `.`.
proof fn lemma_text_label(l: Seq<u8>, j: int, p: Seq<u8>, t: Seq<u8>)
    requires
        0 <= j <= l.len(),
        t.len() == 0 || t[0] == 46,
    ensures
        text_label(p + esc_from(l, j) + t, p.len() as int) == Some(
            (l.subrange(j, l.len() as int), (p.len() + esc_from(l, j).len()) as int),
        ),
    decreases l.len() - j,
{
    let s = p + esc_from(l, j) + t;
    let i = p.len() as int;
    if j == l.len() {
        assert(esc_from(l, j) =~= Seq::<u8>::empty());
        assert(s =~= p + t);
        assert(l.subrange(j, l.len() as int) =~= Seq::<u8>::empty());
    } else {
        let c = l[j];
        let e = esc_byte(c);
        assert(esc_from(l, j) == e + esc_from(l, j + 1));
        let p2 = p + e;
        assert(s =~= p2 + esc_from(l, j + 1) + t);
        lemma_text_label(l, j + 1, p2, t);
        assert(seq![c] + l.subrange(j + 1, l.len() as int) =~= l.subrange(j, l.len() as int));
        if c < 0x20 || c > 0x7e {
            lemma_digits(c);
            assert(s[i] == 92 && s[i + 1] == e[1] && s[i + 2] == e[2] && s[i + 3] == e[3]);
        } else if is_special(c) {
            assert(s[i] == 92 && s[i + 1] == c);
        } else {
            assert(s[i] == c);
        }
    }
}

/// Reading labels `n[k..]` back from their text gives them.
proof fn lemma_text_labels(n: SpecName, k: int, p: Seq<u8>)
    requires
        0 <= k < n.len(),
        forall|i: int| 0 <= i < n.len() ==> valid_label(#[trigger] n[i]),
    ensures
        text_labels(p + esc_from(n[k], 0) + pres_from(n, k + 1), p.len() as int) == Some(
            n.subrange(k, n.len() as int),
        ),
    decreases n.len() - k,
{
    let r = pres_from(n, k + 1);
    let s = p + esc_from(n[k], 0) + r;
    let i = p.len() as int;
    assert(valid_label(n[k]));
    lemma_esc_len(n[k], 0);
    if k + 1 == n.len() {
        assert(r =~= Seq::<u8>::empty());
        lemma_text_label(n[k], 0, p, r);
        assert(n[k].subrange(0, n[k].len() as int) =~= n[k]);
        assert(n.subrange(k, n.len() as int) =~= seq![n[k]]);
    } else {
        let r2 = esc_from(n[k + 1], 0) + pres_from(n, k + 2);
        assert(r == seq![46u8] + r2);
        lemma_text_label(n[k], 0, p, r);
        assert(n[k].subrange(0, n[k].len() as int) =~= n[k]);
        let j = i + esc_from(n[k], 0).len();
        assert(valid_label(n[k + 1]));
        lemma_esc_len(n[k + 1], 0);
        let p2 = p + esc_from(n[k], 0) + seq![46u8];
        assert(s =~= p2 + esc_from(n[k + 1], 0) + pres_from(n, k + 2));
        lemma_text_labels(n, k + 1, p2);
        assert(s[j] == 46);
        assert(n.subrange(k, n.len() as int) =~= seq![n[k]] + n.subrange(k + 1, n.len() as int));
    }
}

/// The text of a non-empty label is non-empty.
proof fn lemma_esc_len(l: Seq<u8>, j: int)
    requires
        0 <= j <= l.len(),
    ensures
        esc_from(l, j).len() >= l.len() - j,
        j < l.len() ==> esc_from(l, j)[0] != 46,
    decreases l.len() - j,
{
    if j < l.len() {
        lemma_esc_len(l, j + 1);
    }
}

/// Printing a well-formed name and parsing the text gives the name back.
pub proof fn theorem_text_roundtrip(n: SpecName)
    requires
        valid_name(n),
    ensures
        parse_text_name(pres_name(n)) == Some(n),
{
    if n.len() == 0 {
        assert(pres_name(n) =~= Seq::<u8>::empty());
    } else {
        let s = pres_name(n);
        assert(s == Seq::<u8>::empty() + esc_from(n[0], 0) + pres_from(n, 1));
        lemma_text_labels(n, 0, Seq::empty());
        assert(n.subrange(0, n.len() as int) =~= n);
        assert(valid_label(n[0]));
        lemma_esc_len(n[0], 0);
        assert(s[0] != 46);
        assert(!(s =~= seq![46u8]));
    }
}

/// No two well-formed names have the same text.
pub proof fn theorem_text_injective(a: SpecName, b: SpecName)
    requires
        valid_name(a),
        valid_name(b),
        pres_name(a) == pres_name(b),
    ensures
        a == b,
{
    theorem_text_roundtrip(a);
    theorem_text_roundtrip(b);
}


fn push_escaped(out: &mut Vec<u8>, c: u8)
    ensures
        final(out)@ == old(out)@ + esc_byte(c),
{
    if c < 0x20 || c > 0x7e {
        out.push(92u8);
        out.push(48 + c / 100);
        out.push(48 + (c % 100) / 10);
        out.push(48 + c % 10);
    } else {
        if c == 34 || c == 46 || c == 59 || c == 92 || c == 40 || c == 41 || c == 64 || c == 36 {
            out.push(92u8);
        }
        out.push(c);
    }
    proof {
        assert(final(out)@ =~= old(out)@ + esc_byte(c));
    }
}

/// Appends the presentation form of the uncompressed wire-form name `w`
/// (which must be exactly one name) to `out`. Returns false, leaving `out`
/// unchanged, if `w` is not a well-formed name.
pub fn write_text(w: &[u8], out: &mut Vec<u8>) -> (ok: bool)
    ensures
        ok ==> (parse_plain_name(w@, 0, w@.len() as int) matches Some((n, e)) && e == w@.len()
            && final(out)@ == old(out)@ + pres_name(n)),
        !ok ==> final(out)@ == old(out)@ && !(parse_plain_name(w@, 0, w@.len() as int) matches Some(
            (n, e),
        ) && e == w@.len()),
{
    let (e, n) = match plain_name_end(w, 0, w.len()) {
        Some(x) => x,
        None => return false,
    };
    if e != w.len() {
        return false;
    }
    let ghost n = n@;
    let mut p: usize = 0;
    let ghost mut k: int = 0;
    proof {
        assert(w@.subrange(0, w@.len() as int) =~= w@);
        assert(n.subrange(0, n.len() as int) =~= n);
        assert(old(out)@ + pres_from(n, 0) =~= old(out)@ + pres_name(n));
    }
    loop
        invariant
            0 <= k <= n.len(),
            p <= w@.len(),
            (k == 0) == (p == 0),
            w@.subrange(p as int, w@.len() as int) == ser_name(n.subrange(k, n.len() as int)),
            out@ + pres_from(n, k) == old(out)@ + pres_name(n),
            valid_name(n),
            parse_plain_name(w@, 0, w@.len() as int) == Some((n, w@.len() as int)),
        decreases n.len() - k,
    {
        let ghost rest = n.subrange(k, n.len() as int);
        let ghost tail = w@.subrange(p as int, w@.len() as int);
        proof {
            assert(tail.len() >= 1);
        }
        let c = w[p];
        proof {
            assert(tail[0] == c);
            if k < n.len() {
                assert(rest[0] == n[k]);
                assert(valid_label(n[k]));
                assert(ser_labels(rest) == ser_label(rest[0]) + ser_labels(rest.drop_first()));
                assert(tail[0] == ser_label(rest[0])[0]);
            } else {
                assert(rest =~= Seq::<Seq<u8>>::empty());
            }
        }
        if c == 0 {
            proof {
                assert(pres_from(n, k) =~= Seq::<u8>::empty());
                assert(out@ =~= old(out)@ + pres_name(n));
            }
            return true;
        }
        let ghost l = n[k];
        proof {
            assert(rest[0] == l);
            assert(valid_label(l));
            assert(ser_labels(rest) == ser_label(l) + ser_labels(rest.drop_first()));
            assert(rest.drop_first() =~= n.subrange(k + 1, n.len() as int));
            assert(tail =~= ser_label(l) + ser_name(n.subrange(k + 1, n.len() as int)));
            assert(c == l.len());
        }
        let len = c as usize;
        proof {
            assert(p + 1 + len <= w@.len());
            assert(tail.subrange(1, 1 + len as int) =~= l);
            assert(w@.subrange(p + 1, p + 1 + len) =~= tail.subrange(1, 1 + len as int));
            assert(tail.subrange(1 + len as int, tail.len() as int) =~= ser_name(
                n.subrange(k + 1, n.len() as int),
            ));
            assert(w@.subrange((p + 1 + len) as int, w@.len() as int) =~= tail.subrange(
                1 + len as int,
                tail.len() as int,
            ));
        }
        if p > 0 {
            out.push(46u8);
        }
        let ghost before = out@;
        let mut j: usize = 0;
        proof {
            assert(out@ + esc_from(l, 0) =~= before + esc_from(l, 0));
        }
        while j < len
            invariant
                j <= len,
                p + 1 + len <= w@.len(),
                w@.len() == w.len(),
                len == l.len(),
                w@.subrange(p + 1, p + 1 + len) == l,
                out@ + esc_from(l, j as int) == before + esc_from(l, 0),
            decreases len - j,
        {
            let x = w[p + 1 + j];
            proof {
                assert(x == l[j as int]);
            }
            let ghost o0 = out@;
            push_escaped(out, x);
            proof {
                assert(esc_from(l, j as int) == esc_byte(x) + esc_from(l, j + 1));
                assert(out@ + esc_from(l, j + 1) =~= o0 + esc_from(l, j as int));
            }
            j = j + 1;
        }
        proof {
            assert(esc_from(l, len as int) =~= Seq::<u8>::empty());
            assert(pres_from(n, k) == (if k > 0 { seq![46u8] } else { Seq::<u8>::empty() })
                + esc_from(l, 0) + pres_from(n, k + 1));
            assert(out@ + pres_from(n, k + 1) =~= old(out)@ + pres_name(n));
            assert(w@.subrange((p + 1 + len) as int, w@.len() as int) =~= ser_name(
                n.subrange(k + 1, n.len() as int),
            ));
            k = k + 1;
        }
        p = p + 1 + len;
    }
}


pub open spec fn prepend_label(l: Seq<u8>, r: Option<(Seq<u8>, int)>) -> Option<(Seq<u8>, int)> {
    match r {
        Some((rest, e)) => Some((l + rest, e)),
        None => None,
    }
}

/// Reads one label's text at `s[i..]` into `l` (which starts empty).
fn read_text_label(s: &[u8], i: usize, l: &mut Vec<u8>) -> (r: Option<usize>)
    requires
        old(l)@.len() == 0,
        i <= s@.len(),
    ensures
        r matches Some(j) ==> text_label(s@, i as int) == Some((final(l)@, j as int)) && i <= j
            <= s@.len(),
        r is None ==> text_label(s@, i as int) is None,
{
    let mut q = i;
    proof {
        if let Some((rest, e)) = text_label(s@, i as int) {
            assert(l@ + rest =~= rest);
        }
    }
    while q < s.len() && s[q] != 46
        invariant
            i <= q <= s@.len(),
            s@.len() == s.len(),
            text_label(s@, i as int) == prepend_label(l@, text_label(s@, q as int)),
        decreases s@.len() - q,
    {
        let c = s[q];
        let ghost l0 = l@;
        if c == 92 {
            if s.len() - q > 3 && 48 <= s[q + 1] && s[q + 1] <= 57 && 48 <= s[q + 2] && s[q + 2] <= 57
                && 48 <= s[q + 3] && s[q + 3] <= 57 {
                let v = (s[q + 1] - 48) as u32 * 100 + (s[q + 2] - 48) as u32 * 10 + (s[q + 3]
                    - 48) as u32;
                if v > 255 {
                    return None;
                }
                l.push(v as u8);
                proof {
                    if let Some((rest, e)) = text_label(s@, q + 4) {
                        assert(l0 + (seq![v as u8] + rest) =~= l@ + rest);
                    }
                }
                q = q + 4;
            } else if q + 1 < s.len() {
                l.push(s[q + 1]);
                proof {
                    if let Some((rest, e)) = text_label(s@, q + 2) {
                        assert(l0 + (seq![s@[q + 1]] + rest) =~= l@ + rest);
                    }
                }
                q = q + 2;
            } else {
                return None;
            }
        } else {
            l.push(c);
            proof {
                if let Some((rest, e)) = text_label(s@, q + 1) {
                    assert(l0 + (seq![c] + rest) =~= l@ + rest);
                }
            }
            q = q + 1;
        }
    }
    proof {
        assert(l@ + Seq::<u8>::empty() =~= l@);
    }
    Some(q)
}

pub open spec fn prepend_name(acc: SpecName, r: Option<SpecName>) -> Option<SpecName> {
    match r {
        Some(rest) => Some(acc + rest),
        None => None,
    }
}

/// Parses a presentation-format name to uncompressed wire form.
pub fn parse_text(s: &[u8]) -> (r: Option<(Vec<u8>, Ghost<SpecName>)>)
    ensures
        r matches Some((v, n)) ==> parse_text_name(s@) == Some(n@) && v@ == ser_name(n@),
        r is None ==> parse_text_name(s@) is None,
{
    // A wire name is at most one byte longer than its text, plus the root.
    let mut out: Vec<u8> = Vec::with_capacity(if s.len() < 256 { s.len() + 2 } else { 258 });
    if s.len() == 0 || (s.len() == 1 && s[0] == 46) {
        out.push(0u8);
        proof {
            assert(out@ =~= ser_name(Seq::<Seq<u8>>::empty()));
            if s.len() == 1 {
                assert(s@ =~= seq![46u8]);
            }
        }
        return Some((out, Ghost(Seq::empty())));
    }
    proof {
        assert(!(s@ =~= seq![46u8])) by {
            if s@ =~= seq![46u8] {
                assert(s@.len() == 1 && s@[0] == 46);
            }
        }
    }
    let ghost mut acc: SpecName = Seq::empty();
    let mut i: usize = 0;
    proof {
        assert(ser_labels(acc) =~= Seq::<u8>::empty());
        if let Some(rest) = text_labels(s@, 0) {
            assert(acc + rest =~= rest);
        }
    }
    // One label buffer, reused.
    let mut l: Vec<u8> = Vec::with_capacity(64);
    loop
        invariant
            i < s@.len(),
            out@ == ser_labels(acc),
            text_labels(s@, 0) == prepend_name(acc, text_labels(s@, i as int)),
            !(s@.len() == 0 || s@ =~= seq![46u8]),
        decreases s@.len() - i,
    {
        l.clear();
        let j = match read_text_label(s, i, &mut l) {
            Some(j) => j,
            None => return None,
        };
        if l.len() == 0 || l.len() > 63 || j <= i {
            return None;
        }
        let ghost a0 = acc;
        out.push(l.len() as u8);
        append(&mut out, l.as_slice());
        proof {
            lemma_ser_labels_push(acc, l@);
            assert(out@ =~= ser_labels(acc) + ser_label(l@));
            acc = acc.push(l@);
        }
        if j >= s.len() || j + 1 == s.len() {
            out.push(0u8);
            proof {
                assert(a0 + seq![l@] =~= acc);
                assert(out@ =~= ser_name(acc));
            }
            if out.len() > 255 {
                return None;
            }
            return Some((out, Ghost(acc)));
        }
        proof {
            if let Some(rest) = text_labels(s@, j + 1) {
                assert(a0 + (seq![l@] + rest) =~= acc + rest);
            }
        }
        i = j + 1;
    }
}

} // verus!
