//! Verified code for internal entities: their replacement text, and which
//! may be referred to in attribute values and in content (`oka_seq`,
//! `okc_seq`). Each table is computed by applying its spec's step to the
//! previous level, at most `ENT_DEPTH` times, stopping early at a fixed
//! point; every application is linear in the size of the replacement
//! texts, so a document's entities cost at most `ENT_DEPTH` passes over
//! them.
use crate::content::*;
use crate::lex::*;
use crate::spec::*;
use crate::tape::*;
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

/// Appends the UTF-8 encoding of `c`.
#[inline(always)]
pub fn push_utf8(out: &mut Vec<u8>, c: u32)
    requires
        c <= 0x10FFFF,
    ensures
        final(out)@ == old(out)@ + utf8_encode(c),
{
    let ghost e = utf8_encode(c);
    if c < 0x80 {
        out.push(c as u8);
    } else if c < 0x800 {
        out.push((0xC0 + c / 64) as u8);
        out.push((0x80 + c % 64) as u8);
    } else if c < 0x10000 {
        out.push((0xE0 + c / 4096) as u8);
        out.push((0x80 + (c / 64) % 64) as u8);
        out.push((0x80 + c % 64) as u8);
    } else {
        out.push((0xF0 + c / 262144) as u8);
        out.push((0x80 + (c / 4096) % 64) as u8);
        out.push((0x80 + (c / 64) % 64) as u8);
        out.push((0x80 + c % 64) as u8);
    }
    assert(out@ =~= old(out)@ + e);
}

/// A character reference is at least four bytes (`&#N;`), and no
/// character takes more than four in UTF-8: the replacement text is never
/// longer than the literal.
pub proof fn lemma_charref_len(s: Seq<u8>, a: int)
    ensures
        charref(s, a) matches Some((c, e)) ==> e >= a + 4 && utf8_encode(c as u32).len() <= 4,
{
}

/// `repl(s, a, b)`.
pub fn ex_repl(s: &[u8], a: usize, b: usize) -> (r: Vec<u8>)
    requires
        a <= b <= s@.len() <= isize::MAX,
    ensures
        r@ == repl(s@, a as int, b as int),
        r@.len() <= b - a,
{
    let mut out: Vec<u8> = Vec::new();
    let mut i = a;
    proof {
        assert(out@ + repl(s@, a as int, b as int) =~= repl(s@, a as int, b as int));
    }
    while i < b
        invariant
            a <= i <= b <= s@.len() <= isize::MAX,
            out@ + repl(s@, i as int, b as int) == repl(s@, a as int, b as int),
            out@.len() <= i - a,
        decreases b - i,
    {
        let c = get(s, i);
        if c == 0x26 && ex_byte_is(s, i + 1, 0x23) {
            match ex_charref(s, i) {
                Some((v, e)) => {
                    if e > b {
                        proof {
                            assert(out@ + Seq::<u8>::empty() =~= out@);
                        }
                        return out;
                    }
                    proof {
                        lemma_charref_len(s@, i as int);
                        assert(repl(s@, i as int, b as int) == utf8_encode(v) + repl(s@, e as int, b as int));
                        assert(out@ + (utf8_encode(v) + repl(s@, e as int, b as int)) =~= (out@ + utf8_encode(v))
                            + repl(s@, e as int, b as int));
                    }
                    push_utf8(&mut out, v);
                    i = e;
                },
                None => {
                    proof {
                        assert(out@ + Seq::<u8>::empty() =~= out@);
                    }
                    return out;
                },
            }
        } else if c == 0x0D {
            let k = if i + 1 < b && get(s, i + 1) == 0x0A { i + 2 } else { i + 1 };
            proof {
                assert(repl(s@, i as int, b as int) == seq![0x0Au8] + repl(s@, k as int, b as int));
                assert(out@ + (seq![0x0Au8] + repl(s@, k as int, b as int)) =~= out@.push(0x0Au8) + repl(
                    s@,
                    k as int,
                    b as int,
                ));
            }
            out.push(0x0A);
            i = k;
        } else {
            proof {
                assert(repl(s@, i as int, b as int) == seq![c] + repl(s@, i + 1, b as int));
                assert(out@ + (seq![c] + repl(s@, i + 1, b as int)) =~= out@.push(c) + repl(s@, i + 1, b as int));
            }
            out.push(c);
            i = i + 1;
        }
    }
    proof {
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    out
}

/// `att_text(r, 0, env)`.
pub fn ex_att_text(r: &[u8], env: &XEnv) -> (ok: bool)
    requires
        r@.len() <= isize::MAX,
        env_wf(env),
    ensures
        ok == att_text(r@, 0, env_view(env)),
{
    proof {
        lemma_lim_all(env);
    }
    let n = r.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == r@.len() <= isize::MAX,
            env_wf(env),
            lim_view(env, env.ents@.len() as int) == env_view(env),
            att_text(r@, i as int, env_view(env)) == att_text(r@, 0, env_view(env)),
        decreases n - i,
    {
        let c = get(r, i);
        if c == 0x3C {
            return false;
        }
        if c == 0x26 {
            match ex_att_ref(r, i, Some(env), env.ents.len()) {
                None => {
                    return false;
                },
                Some(e) => {
                    i = e;
                },
            }
        } else {
            i = i + 1;
        }
    }
    true
}

/// Whether two flag vectors are the same.
fn flags_eq(a: &Vec<bool>, b: &Vec<bool>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut k: usize = 0;
    while k < a.len()
        invariant
            k <= a@.len() == b@.len(),
            forall|q: int| 0 <= q < k ==> a@[q] == b@[q],
        decreases a@.len() - k,
    {
        if a[k] != b[k] {
            return false;
        }
        k = k + 1;
    }
    assert(a@ =~= b@);
    true
}

/// Once a level equals the one before, every later level does too.
proof fn lemma_oka_fix(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, d: nat, m: nat)
    requires
        oka_seq(s, ents, wfc, d + 1) == oka_seq(s, ents, wfc, d),
    ensures
        oka_seq(s, ents, wfc, d + m) == oka_seq(s, ents, wfc, d),
    decreases m,
{
    if m > 0 {
        lemma_oka_fix(s, ents, wfc, d, (m - 1) as nat);
        let p = oka_seq(s, ents, wfc, d);
        assert(oka_seq(s, ents, wfc, d + m) =~= Seq::new(ents.len(), |k: int| ent_oka(s, ents, wfc, p, k)));
        assert(oka_seq(s, ents, wfc, d + 1) =~= Seq::new(ents.len(), |k: int| ent_oka(s, ents, wfc, p, k)));
    }
}

proof fn lemma_okc_fix(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, d: nat, m: nat)
    requires
        okc_seq(s, ents, wfc, oka, d + 1) == okc_seq(s, ents, wfc, oka, d),
    ensures
        okc_seq(s, ents, wfc, oka, d + m) == okc_seq(s, ents, wfc, oka, d),
    decreases m,
{
    if m > 0 {
        lemma_okc_fix(s, ents, wfc, oka, d, (m - 1) as nat);
        let p = okc_seq(s, ents, wfc, oka, d);
        assert(okc_seq(s, ents, wfc, oka, d + m) =~= Seq::new(ents.len(), |k: int| ent_okc(s, ents, wfc, oka, p, k)));
        assert(okc_seq(s, ents, wfc, oka, d + 1) =~= Seq::new(ents.len(), |k: int| ent_okc(s, ents, wfc, oka, p, k)));
    }
}

/// The replacement texts of the internal entities are in `rts`.
pub open spec fn rts_ok(doc: Seq<u8>, ents: Seq<XEnt>, rts: Seq<Vec<u8>>) -> bool {
    &&& rts.len() == ents.len()
    &&& forall|k: int|
        #![trigger rts[k]]
        0 <= k < ents.len() ==> rts[k]@.len() <= doc.len() && (ents[k].kind == 0 ==> rts[k]@ == repl(
            doc,
            ents[k].va as int,
            ents[k].vb as int,
        ))
}

/// The replacement text of each internal entity (and an empty one for
/// the others).
pub fn ex_rts(doc: &[u8], ents: &[XEnt]) -> (r: Vec<Vec<u8>>)
    requires
        doc@.len() <= isize::MAX,
        ents_wf(doc@, ents@),
    ensures
        rts_ok(doc@, ents@, r@),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < ents.len()
        invariant
            k <= ents@.len(),
            doc@.len() <= isize::MAX,
            ents_wf(doc@, ents@),
            out@.len() == k,
            forall|q: int|
                #![trigger out@[q]]
                0 <= q < k ==> out@[q]@.len() <= doc@.len() && (ents@[q].kind == 0 ==> out@[q]@ == repl(
                    doc@,
                    ents@[q].va as int,
                    ents@[q].vb as int,
                )),
        decreases ents@.len() - k,
    {
        let e = ents[k];
        proof {
            assert(e.va <= e.vb <= doc@.len());
        }
        if e.kind == 0 {
            out.push(ex_repl(doc, e.va as usize, e.vb as usize));
        } else {
            out.push(Vec::new());
        }
        k = k + 1;
    }
    out
}

/// `oka_seq(.., ENT_DEPTH)` and `okc_seq(.., ENT_DEPTH)`.
pub fn ex_ent_flags(doc: &[u8], ents: &[XEnt], wfc: bool, rts: &Vec<Vec<u8>>, idx: &crate::index::NameIndex) -> (r: (
    Vec<bool>,
    Vec<bool>,
))
    requires
        doc@.len() <= isize::MAX,
        ents_wf(doc@, ents@),
        rts_ok(doc@, ents@, rts@),
        crate::index::indexes(idx, doc@, ents@),
    ensures
        r.0@ == oka_seq(doc@, ents_view(doc@, ents@), wfc, ENT_DEPTH as nat),
        r.1@ == okc_seq(doc@, ents_view(doc@, ents@), wfc, r.0@, ENT_DEPTH as nat),
{
    let ghost es = ents_view(doc@, ents@);
    let n = ents.len();
    let none: Vec<bool> = Vec::new();
    // Attribute values.
    let mut prev: Vec<bool> = Vec::new();
    while prev.len() < n
        invariant
            prev@.len() <= n,
            forall|q: int| 0 <= q < prev@.len() ==> !prev@[q],
        decreases n - prev@.len(),
    {
        prev.push(false);
    }
    proof {
        assert(prev@ =~= oka_seq(doc@, es, wfc, 0));
    }
    let mut d: usize = 0;
    while d < ENT_DEPTH
        invariant
            d <= ENT_DEPTH,
            n == ents@.len(),
            es == ents_view(doc@, ents@),
            doc@.len() <= isize::MAX,
            ents_wf(doc@, ents@),
            rts_ok(doc@, ents@, rts@),
            none@ == Seq::<bool>::empty(),
            crate::index::indexes(idx, doc@, ents@),
            prev@ == oka_seq(doc@, es, wfc, d as nat),
        ensures
            prev@ == oka_seq(doc@, es, wfc, ENT_DEPTH as nat),
        decreases ENT_DEPTH - d,
    {
        let mut cur: Vec<bool> = Vec::new();
        {
            let env = XEnv { doc, ents, wfc, oka: prev.as_slice(), okc: none.as_slice(), idx };
            let mut k: usize = 0;
            while k < n
                invariant
                    k <= n,
                    n == ents@.len(),
                    es == ents_view(doc@, ents@),
                    doc@.len() <= isize::MAX,
                    env_wf(&env),
                    env.doc@ == doc@,
                    env.ents@ == ents@,
                    env_view(&env) == (Env { ents: es, wfc, oka: prev@, okc: Seq::empty() }),
                    rts_ok(doc@, ents@, rts@),
                    cur@.len() == k,
                    forall|q: int| 0 <= q < k ==> cur@[q] == ent_oka(doc@, es, wfc, prev@, q),
                decreases n - k,
            {
                let e = ents[k];
                proof {
                    assert(es[k as int] == ent_view(doc@, e));
                    assert(rts@[k as int]@.len() <= doc@.len());
                }
                let v = if e.kind == 0 {
                    ex_att_text(rts[k].as_slice(), &env)
                } else {
                    false
                };
                cur.push(v);
                k = k + 1;
            }
        }
        proof {
            assert(cur@ =~= oka_seq(doc@, es, wfc, (d + 1) as nat));
        }
        if flags_eq(&cur, &prev) {
            proof {
                lemma_oka_fix(doc@, es, wfc, d as nat, (ENT_DEPTH - d) as nat);
            }
            break;
        }
        prev = cur;
        d = d + 1;
    }
    let oka = prev;
    // Content.
    let mut prev: Vec<bool> = Vec::new();
    while prev.len() < n
        invariant
            prev@.len() <= n,
            forall|q: int| 0 <= q < prev@.len() ==> !prev@[q],
        decreases n - prev@.len(),
    {
        prev.push(false);
    }
    proof {
        assert(prev@ =~= okc_seq(doc@, es, wfc, oka@, 0));
    }
    let mut scratch = Tape::new();
    let mut d: usize = 0;
    while d < ENT_DEPTH
        invariant
            d <= ENT_DEPTH,
            n == ents@.len(),
            es == ents_view(doc@, ents@),
            doc@.len() <= isize::MAX,
            ents_wf(doc@, ents@),
            rts_ok(doc@, ents@, rts@),
            crate::index::indexes(idx, doc@, ents@),
            prev@ == okc_seq(doc@, es, wfc, oka@, d as nat),
        ensures
            prev@ == okc_seq(doc@, es, wfc, oka@, ENT_DEPTH as nat),
        decreases ENT_DEPTH - d,
    {
        let mut cur: Vec<bool> = Vec::new();
        {
            let env = XEnv { doc, ents, wfc, oka: oka.as_slice(), okc: prev.as_slice(), idx };
            let mut k: usize = 0;
            while k < n
                invariant
                    k <= n,
                    n == ents@.len(),
                    es == ents_view(doc@, ents@),
                    doc@.len() <= isize::MAX,
                    env_wf(&env),
                    env_view(&env) == (Env { ents: es, wfc, oka: oka@, okc: prev@ }),
                    rts_ok(doc@, ents@, rts@),
                    cur@.len() == k,
                    forall|q: int| 0 <= q < k ==> cur@[q] == ent_okc(doc@, es, wfc, oka@, prev@, q),
                decreases n - k,
            {
                let e = ents[k];
                proof {
                    assert(es[k as int] == ent_view(doc@, e));
                    assert(rts@[k as int]@.len() <= doc@.len());
                }
                let v = if e.kind == 0 {
                    ex_ent_content(rts[k].as_slice(), &mut scratch, &env)
                } else {
                    false
                };
                cur.push(v);
                k = k + 1;
            }
        }
        proof {
            assert(cur@ =~= okc_seq(doc@, es, wfc, oka@, (d + 1) as nat));
        }
        if flags_eq(&cur, &prev) {
            proof {
                lemma_okc_fix(doc@, es, wfc, oka@, d as nat, (ENT_DEPTH - d) as nat);
            }
            break;
        }
        prev = cur;
        d = d + 1;
    }
    (oka, prev)
}

} // verus!
