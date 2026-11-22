//! What the text of a document means, and the verified code that decodes
//! it: line-end normalization of character data (§2.11), and the
//! normalized value of an attribute (§3.3.3), entities expanded.
use crate::chars::*;
use crate::ent::*;
use crate::lex::*;
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// `s[a..b]` with each carriage return and line feed pair, and each
/// carriage return alone, replaced by a line feed (§2.11).
pub open spec fn eol(s: Seq<u8>, a: int, b: int) -> Seq<u8>
    decreases b - a,
{
    if !(0 <= a < b <= s.len()) {
        Seq::empty()
    } else if s[a] == 0x0D {
        if a + 1 < b && s[a + 1] == 0x0A {
            seq![0x0Au8] + eol(s, a + 2, b)
        } else {
            seq![0x0Au8] + eol(s, a + 1, b)
        }
    } else {
        seq![s[a]] + eol(s, a + 1, b)
    }
}

/// `p` before the result `o`, if there is one.
pub open spec fn pre(p: Seq<u8>, o: Option<Seq<u8>>) -> Option<Seq<u8>> {
    match o {
        Some(x) => Some(p + x),
        None => None,
    }
}

/// The normalized value (§3.3.3, for type CDATA) of the attribute value
/// `r[i..end]`, in the document `doc` with the entities of `env`:
/// a character reference stands for its character; an entity reference
/// for the normalized value of its replacement text, at most `d` deep;
/// each white space character for a space (a carriage return and line
/// feed pair, in the document itself, `eol`, being one line end); anything
/// else for itself. A reference to an entity that was not declared, which
/// a well-formed document has only where the declaration may be in an
/// unread external subset, is kept as written.
pub open spec fn att_norm(doc: Seq<u8>, r: Seq<u8>, i: int, end: int, eol: bool, env: Env, d: nat) -> Option<Seq<u8>>
    decreases d, end - i,
{
    if !(0 <= i < end <= r.len()) {
        Some(Seq::empty())
    } else if r[i] == 0x26 {
        if byte_is(r, i + 1, 0x23) {
            match charref(r, i) {
                Some((c, e)) => if i < e <= end {
                    pre(utf8_encode(c as u32), att_norm(doc, r, e, end, eol, env, d))
                } else {
                    None
                },
                None => None,
            }
        } else {
            let n = name_end(r, i + 1);
            if !(n > i + 1 && byte_is(r, n, 0x3B) && n + 1 <= end) {
                None
            } else {
                match predef(r, i + 1, n) {
                    Some(c) => pre(utf8_encode(c as u32), att_norm(doc, r, n + 1, end, eol, env, d)),
                    None => match find_ent(env.ents, r.subrange(i + 1, n)) {
                        None => pre(r.subrange(i, n + 1), att_norm(doc, r, n + 1, end, eol, env, d)),
                        Some(j) => match env.ents[j].kind {
                            EKind::Internal { start, end: ve } => if d == 0 {
                                None
                            } else {
                                let t = repl(doc, start, ve);
                                match att_norm(doc, t, 0, t.len() as int, false, env, (d - 1) as nat) {
                                    None => None,
                                    Some(x) => pre(x, att_norm(doc, r, n + 1, end, eol, env, d)),
                                }
                            },
                            _ => None,
                        },
                    },
                }
            }
        }
    } else if r[i] == 0x0D && eol {
        if i + 1 < end && r[i + 1] == 0x0A {
            pre(seq![0x20u8], att_norm(doc, r, i + 2, end, eol, env, d))
        } else {
            pre(seq![0x20u8], att_norm(doc, r, i + 1, end, eol, env, d))
        }
    } else if is_ws(r[i]) {
        pre(seq![0x20u8], att_norm(doc, r, i + 1, end, eol, env, d))
    } else {
        pre(seq![r[i]], att_norm(doc, r, i + 1, end, eol, env, d))
    }
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

/// Appends `eol(s, a, b)`.
pub fn ex_eol(s: &[u8], a: usize, b: usize, out: &mut Vec<u8>)
    requires
        a <= b <= s@.len(),
    ensures
        final(out)@ == old(out)@ + eol(s@, a as int, b as int),
{
    let mut i = a;
    proof {
        assert(old(out)@ + eol(s@, a as int, b as int) =~= out@ + eol(s@, a as int, b as int));
    }
    while i < b
        invariant
            a <= i <= b <= s@.len(),
            old(out)@ + eol(s@, a as int, b as int) == out@ + eol(s@, i as int, b as int),
        decreases b - i,
    {
        let c = get(s, i);
        if c == 0x0D {
            let k = if i + 1 < b && get(s, i + 1) == 0x0A { i + 2 } else { i + 1 };
            proof {
                assert(out@ + (seq![0x0Au8] + eol(s@, k as int, b as int)) =~= out@.push(0x0Au8) + eol(
                    s@,
                    k as int,
                    b as int,
                ));
            }
            out.push(0x0A);
            i = k;
        } else {
            proof {
                assert(out@ + (seq![c] + eol(s@, i + 1, b as int)) =~= out@.push(c) + eol(s@, i + 1, b as int));
            }
            out.push(c);
            i = i + 1;
        }
    }
    proof {
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
}

/// Appends `r[a..b]`.
fn ex_copy(r: &[u8], a: usize, b: usize, out: &mut Vec<u8>)
    requires
        a <= b <= r@.len(),
    ensures
        final(out)@ == old(out)@ + r@.subrange(a as int, b as int),
{
    let mut k = a;
    proof {
        assert(old(out)@ + r@.subrange(a as int, a as int) =~= out@);
    }
    while k < b
        invariant
            a <= k <= b <= r@.len(),
            out@ == old(out)@ + r@.subrange(a as int, k as int),
        decreases b - k,
    {
        out.push(get(r, k));
        proof {
            assert(r@.subrange(a as int, k + 1) =~= r@.subrange(a as int, k as int).push(r@[k as int]));
            assert(out@ =~= old(out)@ + r@.subrange(a as int, k + 1));
        }
        k = k + 1;
    }
}

/// `att_norm(doc, r, i, end, eol, env, d)` appended to `out`: 0 when it
/// is the value, 1 when there is none, 2 when `out` would pass `limit`
/// bytes (expansion stopped).
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub fn ex_att_norm(
    r: &[u8],
    i: usize,
    end: usize,
    eol: bool,
    env: &XEnv,
    rts: &Vec<Vec<u8>>,
    d: usize,
    out: &mut Vec<u8>,
    limit: usize,
) -> (res: u8)
    requires
        i <= end <= r@.len() <= isize::MAX,
        env_wf(env),
        env.doc@.len() <= isize::MAX,
        rts_ok(env.doc@, env.ents@, rts@),
    ensures
        res == 0 ==> pre(old(out)@, att_norm(env.doc@, r@, i as int, end as int, eol, env_view(env), d as nat)) == Some(
            final(out)@,
        ),
        res == 1 ==> att_norm(env.doc@, r@, i as int, end as int, eol, env_view(env), d as nat) is None,
    decreases d,
{
    let ghost doc = env.doc@;
    let ghost ev = env_view(env);
    let ghost whole = att_norm(doc, r@, i as int, end as int, eol, ev, d as nat);
    let mut j = i;
    proof {
        match att_norm(doc, r@, i as int, end as int, eol, ev, d as nat) {
            Some(v) => assert(old(out)@ + v =~= out@ + v),
            None => {},
        }
        lemma_lim_all(env);
    }
    while j < end
        invariant
            i <= j <= end <= r@.len() <= isize::MAX,
            env_wf(env),
            doc == env.doc@,
            ev == env_view(env),
            doc.len() <= isize::MAX,
            rts_ok(doc, env.ents@, rts@),
            lim_view(env, env.ents@.len() as int) == ev,
            whole == att_norm(doc, r@, i as int, end as int, eol, ev, d as nat),
            pre(old(out)@, whole) == pre(out@, att_norm(doc, r@, j as int, end as int, eol, ev, d as nat)),
        decreases end - j,
    {
        if out.len() > limit {
            return 2;
        }
        let c = get(r, j);
        if c == 0x26 {
            if ex_byte_is(r, j + 1, 0x23) {
                match ex_charref(r, j) {
                    Some((v, e)) => {
                        if e > end {
                            return 1;
                        }
                        proof {
                            let rest = att_norm(doc, r@, e as int, end as int, eol, ev, d as nat);
                            match rest {
                                Some(x) => assert(out@ + (utf8_encode(v) + x) =~= (out@ + utf8_encode(v)) + x),
                                None => {},
                            }
                        }
                        push_utf8(out, v);
                        j = e;
                    },
                    None => {
                        return 1;
                    },
                }
            } else {
                let n = ex_name_end(r, j + 1);
                if !(n > j + 1 && ex_byte_is(r, n, 0x3B) && n + 1 <= end) {
                    return 1;
                }
                match ex_predef(r, j + 1, n) {
                    Some(v) => {
                        proof {
                            let rest = att_norm(doc, r@, n + 1, end as int, eol, ev, d as nat);
                            match rest {
                                Some(x) => assert(out@ + (utf8_encode(v) + x) =~= (out@ + utf8_encode(v)) + x),
                                None => {},
                            }
                        }
                        push_utf8(out, v);
                        j = n + 1;
                    },
                    None => {
                        match ex_find_ent(env, env.ents.len(), r, j + 1, n) {
                            None => {
                                let ghost before = out@;
                                ex_copy(r, j, n + 1, out);
                                proof {
                                    let rest = att_norm(doc, r@, n + 1, end as int, eol, ev, d as nat);
                                    match rest {
                                        Some(x) => assert(before + (r@.subrange(j as int, n + 1) + x) =~= out@ + x),
                                        None => {},
                                    }
                                }
                                j = n + 1;
                            },
                            Some(q) => {
                                let e = env.ents[q];
                                proof {
                                    assert(ev.ents[q as int] == ent_view(doc, e));
                                }
                                if e.kind != 0 {
                                    return 1;
                                }
                                if d == 0 {
                                    return 1;
                                }
                                let t = rts[q].as_slice();
                                proof {
                                    assert(rts@[q as int]@.len() <= doc.len());
                                }
                                let ghost o = out@;
                                let ghost inner = att_norm(doc, t@, 0, t@.len() as int, false, ev, (d - 1) as nat);
                                let res = ex_att_norm(t, 0, t.len(), false, env, rts, d - 1, out, limit);
                                if res != 0 {
                                    return res;
                                }
                                proof {
                                    let x = inner->Some_0;
                                    assert(out@ == o + x);
                                    let rest = att_norm(doc, r@, n + 1, end as int, eol, ev, d as nat);
                                    match rest {
                                        Some(y) => assert(o + (x + y) =~= (o + x) + y),
                                        None => {},
                                    }
                                }
                                j = n + 1;
                            },
                        }
                    },
                }
            }
        } else if c == 0x0D && eol {
            let k = if j + 1 < end && get(r, j + 1) == 0x0A { j + 2 } else { j + 1 };
            proof {
                let rest = att_norm(doc, r@, k as int, end as int, eol, ev, d as nat);
                match rest {
                    Some(x) => assert(out@ + (seq![0x20u8] + x) =~= out@.push(0x20u8) + x),
                    None => {},
                }
            }
            out.push(0x20);
            j = k;
        } else if ex_is_ws(c) {
            proof {
                let rest = att_norm(doc, r@, j + 1, end as int, eol, ev, d as nat);
                match rest {
                    Some(x) => assert(out@ + (seq![0x20u8] + x) =~= out@.push(0x20u8) + x),
                    None => {},
                }
            }
            out.push(0x20);
            j = j + 1;
        } else {
            proof {
                let rest = att_norm(doc, r@, j + 1, end as int, eol, ev, d as nat);
                match rest {
                    Some(x) => assert(out@ + (seq![c] + x) =~= out@.push(c) + x),
                    None => {},
                }
            }
            out.push(c);
            j = j + 1;
        }
    }
    proof {
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    0
}

} // verus!
