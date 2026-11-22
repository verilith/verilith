//! What the text of a document means, and the verified code that decodes
//! it: line-end normalization of character data (§2.11), and the
//! normalized value of an attribute (§3.3.3), entities expanded.
use crate::chars::*;
use crate::ent::*;
use crate::lex::*;
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::utf8_encode;
use vstd::arithmetic::power::*;
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

/// `o`, and then `rest`: `None` if either is.
pub open spec fn then(o: Option<Seq<u8>>, rest: Option<Seq<u8>>) -> Option<Seq<u8>> {
    match o {
        Some(x) => pre(x, rest),
        None => None,
    }
}

proof fn lemma_then_assoc(a: Option<Seq<u8>>, b: Option<Seq<u8>>, c: Option<Seq<u8>>)
    ensures
        then(then(a, b), c) == then(a, then(b, c)),
{
    if let (Some(x), Some(y), Some(z)) = (a, b, c) {
        assert((x + y) + z =~= x + (y + z));
    }
}

proof fn lemma_pre_pre(p: Seq<u8>, q: Seq<u8>, o: Option<Seq<u8>>)
    ensures
        pre(p, pre(q, o)) == pre(p + q, o),
{
    if let Some(x) = o {
        assert(p + (q + x) =~= (p + q) + x);
    }
}

/// A frame of the decoder: the text (`usize::MAX` for the value itself,
/// otherwise the internal entity whose replacement text it is), the
/// position in it, its end, whether its line ends are normalized, and the
/// depth left.
pub type Frame = (usize, usize, usize, bool, usize);

pub open spec fn fbuf(r: Seq<u8>, rts: Seq<Vec<u8>>, src: usize) -> Seq<u8> {
    if src == usize::MAX {
        r
    } else {
        rts[src as int]@
    }
}

/// What the frames still have to produce, the top one first.
pub open spec fn frames_norm(doc: Seq<u8>, r: Seq<u8>, rts: Seq<Vec<u8>>, env: Env, fr: Seq<Frame>) -> Option<Seq<u8>>
    decreases fr.len(),
{
    if fr.len() == 0 {
        Some(Seq::empty())
    } else {
        let f = fr.last();
        then(
            att_norm(doc, fbuf(r, rts, f.0), f.1 as int, f.2 as int, f.3, env, f.4 as nat),
            frames_norm(doc, r, rts, env, fr.drop_last()),
        )
    }
}

/// The termination measure: each frame weighs what is left of it, one
/// more, in units of `b` to the power of its depth. A frame pushed for a
/// reference is one level shallower than the frame it is in, so it weighs
/// less than the reference it replaces.
pub open spec fn fweight(f: Frame, b: int) -> int {
    (f.2 - f.1 + 1) * pow(b, f.4 as nat)
}

pub open spec fn fmeas(fr: Seq<Frame>, b: int) -> int
    decreases fr.len(),
{
    if fr.len() == 0 {
        0
    } else {
        fmeas(fr.drop_last(), b) + fweight(fr.last(), b)
    }
}

pub open spec fn frames_ok(r: Seq<u8>, rts: Seq<Vec<u8>>, ents: Seq<XEnt>, fr: Seq<Frame>) -> bool {
    forall|k: int|
        #![trigger fr[k]]
        0 <= k < fr.len() ==> fr[k].1 <= fr[k].2 <= fbuf(r, rts, fr[k].0).len() && (fr[k].0 == usize::MAX || (fr[k].0
            < ents.len() && ents[fr[k].0 as int].kind == 0))
}

proof fn lemma_fmeas_nonneg(fr: Seq<Frame>, b: int)
    requires
        b > 0,
        forall|k: int| 0 <= k < fr.len() ==> (#[trigger] fr[k]).1 <= fr[k].2,
    ensures
        fmeas(fr, b) >= 0,
    decreases fr.len(),
{
    if fr.len() > 0 {
        let f = fr.last();
        assert(fr[fr.len() - 1] == f);
        lemma_fmeas_nonneg(fr.drop_last(), b);
        lemma_pow_positive(b, f.4 as nat);
        assert(fweight(f, b) >= 0) by (nonlinear_arith)
            requires
                f.2 - f.1 + 1 >= 1,
                pow(b, f.4 as nat) > 0,
                fweight(f, b) == (f.2 - f.1 + 1) * pow(b, f.4 as nat),
        ;
    }
}

/// The top frame moving forward lowers the measure by its unit at least.
proof fn lemma_fmeas_step(fr: Seq<Frame>, f: Frame, b: int)
    requires
        fr.len() > 0,
        b > 0,
        f.0 == fr.last().0 && f.4 == fr.last().4 && f.2 == fr.last().2,
        fr.last().1 < f.1,
    ensures
        fmeas(fr.update(fr.len() - 1, f), b) + pow(b, f.4 as nat) <= fmeas(fr, b),
{
    let g = fr.last();
    let fr2 = fr.update(fr.len() - 1, f);
    assert(fr2.drop_last() =~= fr.drop_last());
    assert(fr2.last() == f);
    lemma_pow_positive(b, f.4 as nat);
    let p = pow(b, f.4 as nat);
    assert((f.2 - f.1 + 1) * p + p <= (g.2 - g.1 + 1) * p) by (nonlinear_arith)
        requires
            p > 0,
            f.1 > g.1,
            f.2 == g.2,
    ;
}

/// Pushing a frame one level shallower, of fewer than `b - 1` bytes, adds
/// less than the unit of the frame below it.
proof fn lemma_fmeas_push(fr: Seq<Frame>, g: Frame, b: int, d: nat)
    requires
        b > 0,
        g.4 + 1 == d,
        g.1 <= g.2,
        g.2 - g.1 + 1 < b,
    ensures
        fmeas(fr.push(g), b) < fmeas(fr, b) + pow(b, d),
{
    assert(fr.push(g).drop_last() =~= fr);
    lemma_pow_positive(b, g.4 as nat);
    let p = pow(b, g.4 as nat);
    lemma_pow_adds(b, 1, g.4 as nat);
    lemma_pow1(b);
    assert(1 + g.4 as nat == d);
    assert(pow(b, d) == b * p);
    assert((g.2 - g.1 + 1) * p < b * p) by (nonlinear_arith)
        requires
            p > 0,
            g.2 - g.1 + 1 < b,
    ;
}

/// `att_norm(doc, r, i, end, eol, env, d)` appended to `out`: 0 when it
/// is the value, 1 when there is none, 2 when `out` would pass `limit`
/// bytes (expansion stopped). Entity references are expanded with an
/// explicit stack of frames, so the depth of nesting costs no call stack:
/// the frame being read is in locals, and `fr` holds those below it.
#[verifier::spinoff_prover]
#[verifier::rlimit(800)]
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
{
    let ghost doc = env.doc@;
    let ghost ev = env_view(env);
    let ghost whole = att_norm(doc, r@, i as int, end as int, eol, ev, d as nat);
    // Every text is shorter than `b - 1`.
    let ghost b: int = (if r@.len() > doc.len() { r@.len() + 2 } else { doc.len() + 2 }) as int;
    let mut fr: Vec<Frame> = Vec::new();
    let mut src: usize = usize::MAX;
    let mut buf: &[u8] = r;
    let mut j = i;
    let mut e_end = end;
    let mut e_eol = eol;
    let mut e_d = d;
    proof {
        lemma_lim_all(env);
        let full = fr@.push((src, j, e_end, e_eol, e_d));
        assert(full.drop_last() =~= Seq::<Frame>::empty());
        assert(frames_norm(doc, r@, rts@, ev, Seq::<Frame>::empty()) == Some(Seq::<u8>::empty()));
        assert(full.last() == (usize::MAX, i, end, eol, d));
        assert(fbuf(r@, rts@, usize::MAX) == r@);
        assert(frames_norm(doc, r@, rts@, ev, full) == then(whole, Some(Seq::empty())));
        match whole {
            Some(v) => {
                assert(v + Seq::<u8>::empty() =~= v);
                assert(old(out)@ + v =~= out@ + v);
            },
            None => {},
        }
        assert forall|k: int| 0 <= k < full.len() implies (#[trigger] full[k]).1 <= full[k].2 by {
            assert(full[k] == full.last());
        }
        lemma_fmeas_nonneg(full, b);
        assert(frames_ok(r@, rts@, env.ents@, full)) by {
            assert forall|k: int| 0 <= k < full.len() implies #[trigger] full[k] == full.last() by {}
        }
    }
    loop
        invariant
            i <= end <= r@.len() <= isize::MAX,
            env_wf(env),
            doc == env.doc@,
            ev == env_view(env),
            doc.len() <= isize::MAX,
            b == (if r@.len() > doc.len() { r@.len() + 2 } else { doc.len() + 2 }) as int,
            rts_ok(doc, env.ents@, rts@),
            lim_view(env, env.ents@.len() as int) == ev,
            whole == att_norm(doc, r@, i as int, end as int, eol, ev, d as nat),
            buf@ == fbuf(r@, rts@, src),
            frames_ok(r@, rts@, env.ents@, fr@.push((src, j, e_end, e_eol, e_d))),
            pre(old(out)@, whole) == pre(out@, frames_norm(doc, r@, rts@, ev, fr@.push((src, j, e_end, e_eol, e_d)))),
            fmeas(fr@.push((src, j, e_end, e_eol, e_d)), b) >= 0,
        decreases fmeas(fr@.push((src, j, e_end, e_eol, e_d)), b),
    {
        let ghost f: Frame = (src, j, e_end, e_eol, e_d);
        let ghost full = fr@.push(f);
        let ghost rest = frames_norm(doc, r@, rts@, ev, fr@);
        proof {
            assert(full.drop_last() =~= fr@);
            assert(full.last() == f);
            assert(full[full.len() - 1] == f);
            assert(j <= e_end <= buf@.len());
            if src != usize::MAX {
                assert(rts@[src as int]@.len() <= doc.len());
            }
            assert(buf@.len() + 2 <= b);
            assert(frames_norm(doc, r@, rts@, ev, full) == then(
                att_norm(doc, buf@, j as int, e_end as int, e_eol, ev, e_d as nat),
                rest,
            ));
            lemma_pow_positive(b, e_d as nat);
            assert forall|k: int| 0 <= k < fr@.len() implies #[trigger] fr@[k] == full[k] by {}
        }
        if j >= e_end {
            proof {
                assert(att_norm(doc, buf@, j as int, e_end as int, e_eol, ev, e_d as nat) == Some(Seq::<u8>::empty()));
                match rest {
                    Some(x) => assert(Seq::<u8>::empty() + x =~= x),
                    None => {},
                }
                assert(fweight(f, b) >= pow(b, e_d as nat)) by (nonlinear_arith)
                    requires
                        f.2 - f.1 + 1 >= 1,
                        pow(b, f.4 as nat) > 0,
                        fweight(f, b) == (f.2 - f.1 + 1) * pow(b, f.4 as nat),
                        f.4 == e_d,
                ;
            }
            let ghost fr0 = fr@;
            match fr.pop() {
                None => {
                    proof {
                        assert(fr0 =~= Seq::<Frame>::empty());
                        assert(out@ + Seq::<u8>::empty() =~= out@);
                    }
                    return 0;
                },
                Some(g) => {
                    proof {
                        assert(fr0 == fr@.push(g));
                        assert(fr0[fr0.len() - 1] == g);
                        assert(full[fr0.len() - 1] == g);
                        assert forall|k: int| 0 <= k < fr0.len() implies (#[trigger] fr0[k]).1 <= fr0[k].2 by {
                            assert(fr0[k] == full[k]);
                        }
                        lemma_fmeas_nonneg(fr0, b);
                        assert(frames_ok(r@, rts@, env.ents@, fr0)) by {
                            assert forall|k: int| 0 <= k < fr0.len() implies #[trigger] fr0[k] == full[k] by {}
                        }
                    }
                    src = g.0;
                    j = g.1;
                    e_end = g.2;
                    e_eol = g.3;
                    e_d = g.4;
                    buf = if src == usize::MAX {
                        r
                    } else {
                        rts[src].as_slice()
                    };
                    proof {
                        assert(fr@.push((src, j, e_end, e_eol, e_d)) == fr0);
                    }
                    continue;
                },
            }
        }
        if out.len() > limit {
            return 2;
        }
        let ghost here = att_norm(doc, buf@, j as int, e_end as int, e_eol, ev, e_d as nat);
        let c = get(buf, j);
        let ghost ob = out@;
        // The next position in this frame, and what it appended; or the
        // entity whose frame to push for a reference.
        let mut next: usize = j + 1;
        let mut push: Option<usize> = None;
        let ghost mut emitted: Seq<u8> = Seq::empty();
        if c == 0x26 {
            if ex_byte_is(buf, j + 1, 0x23) {
                match ex_charref(buf, j) {
                    Some((v, e)) => {
                        if e > e_end {
                            return 1;
                        }
                        push_utf8(out, v);
                        next = e;
                        proof {
                            emitted = utf8_encode(v);
                            assert(here == pre(emitted, att_norm(doc, buf@, next as int, e_end as int, e_eol, ev, e_d as nat)));
                        }
                    },
                    None => {
                        return 1;
                    },
                }
            } else {
                let n = ex_name_end(buf, j + 1);
                if !(n > j + 1 && ex_byte_is(buf, n, 0x3B) && n + 1 <= e_end) {
                    return 1;
                }
                match ex_predef(buf, j + 1, n) {
                    Some(v) => {
                        push_utf8(out, v);
                        next = n + 1;
                        proof {
                            emitted = utf8_encode(v);
                            assert(here == pre(emitted, att_norm(doc, buf@, next as int, e_end as int, e_eol, ev, e_d as nat)));
                        }
                    },
                    None => {
                        match ex_find_ent(env, env.ents.len(), buf, j + 1, n) {
                            None => {
                                ex_copy(buf, j, n + 1, out);
                                next = n + 1;
                                proof {
                                    emitted = buf@.subrange(j as int, n + 1);
                                    assert(here == pre(emitted, att_norm(doc, buf@, next as int, e_end as int, e_eol, ev, e_d as nat)));
                                }
                            },
                            Some(q) => {
                                let e = env.ents[q];
                                proof {
                                    assert(ev.ents[q as int] == ent_view(doc, e));
                                }
                                if e.kind != 0 {
                                    return 1;
                                }
                                if e_d == 0 {
                                    return 1;
                                }
                                proof {
                                    assert(rts@[q as int]@ == repl(doc, e.va as int, e.vb as int));
                                }
                                push = Some(q);
                                next = n + 1;
                                proof {
                                    assert(here == then(
                                        att_norm(doc, repl(doc, e.va as int, e.vb as int), 0, repl(doc, e.va as int, e.vb as int).len() as int, false, ev, (e_d - 1) as nat),
                                        att_norm(doc, buf@, next as int, e_end as int, e_eol, ev, e_d as nat),
                                    ));
                                }
                            },
                        }
                    },
                }
            }
        } else if c == 0x0D && e_eol {
            next = if j + 1 < e_end && get(buf, j + 1) == 0x0A { j + 2 } else { j + 1 };
            out.push(0x20);
            proof {
                emitted = seq![0x20u8];
                assert(here == pre(emitted, att_norm(doc, buf@, next as int, e_end as int, e_eol, ev, e_d as nat)));
            }
        } else if ex_is_ws(c) {
            out.push(0x20);
            proof {
                emitted = seq![0x20u8];
                assert(here == pre(emitted, att_norm(doc, buf@, next as int, e_end as int, e_eol, ev, e_d as nat)));
            }
        } else {
            out.push(c);
            proof {
                emitted = seq![c];
                assert(here == pre(emitted, att_norm(doc, buf@, next as int, e_end as int, e_eol, ev, e_d as nat)));
            }
        }
        proof {
            assert(out@ =~= ob + emitted);
        }
        let ghost f2: Frame = (src, next, e_end, e_eol, e_d);
        let ghost after = att_norm(doc, buf@, next as int, e_end as int, e_eol, ev, e_d as nat);
        proof {
            let full2 = fr@.push(f2);
            assert(full2 =~= full.update(full.len() - 1, f2));
            assert(full2.drop_last() =~= fr@);
            assert(full2.last() == f2);
            assert(frames_norm(doc, r@, rts@, ev, full2) == then(after, rest));
            lemma_fmeas_step(full, f2, b);
            assert(frames_ok(r@, rts@, env.ents@, full2)) by {
                assert forall|k: int| 0 <= k < full2.len() implies fr@.push(f2)[k].1 <= full2[k].2 <= fbuf(r@, rts@, #[trigger] full2[k].0).len() && (full2[k].0
                    == usize::MAX || (full2[k].0 < env.ents@.len() && env.ents@[full2[k].0 as int].kind == 0)) by {
                    if k < fr@.len() {
                        assert(full2[k] == full[k]);
                    }
                }
            }
        }
        match push {
            None => {
                j = next;
                proof {
                    let full2 = fr@.push(f2);
                    assert(here == pre(emitted, after));
                    lemma_then_assoc(Some(emitted), after, rest);
                    lemma_pre_pre(ob, emitted, then(after, rest));
                    assert forall|k: int| 0 <= k < full2.len() implies (#[trigger] full2[k]).1 <= full2[k].2 by {
                        if k < fr@.len() {
                            assert(full2[k] == full[k]);
                        }
                    }
                    lemma_fmeas_nonneg(full2, b);
                }
            },
            Some(q) => {
                let ghost fr1 = fr@.push(f2);
                fr.push((src, next, e_end, e_eol, e_d));
                let t = rts[q].as_slice();
                src = q;
                buf = t;
                j = 0;
                e_end = t.len();
                e_eol = false;
                e_d = e_d - 1;
                proof {
                    let g: Frame = (q, 0, t@.len() as usize, false, e_d);
                    let full3 = fr@.push(g);
                    assert(fr@ == fr1);
                    assert(full3.drop_last() =~= fr1);
                    assert(full3.last() == g);
                    assert(fbuf(r@, rts@, q) == t@);
                    assert(t@.len() <= doc.len());
                    let inner = att_norm(doc, t@, 0, t@.len() as int, false, ev, e_d as nat);
                    assert(frames_norm(doc, r@, rts@, ev, full3) == then(inner, then(after, rest)));
                    assert(here == then(inner, after));
                    lemma_then_assoc(inner, after, rest);
                    assert(emitted == Seq::<u8>::empty());
                    assert(out@ =~= ob);
                    lemma_fmeas_push(fr1, g, b, (e_d + 1) as nat);
                    assert(frames_ok(r@, rts@, env.ents@, full3)) by {
                        assert forall|k: int| 0 <= k < full3.len() implies full3[k].1 <= full3[k].2 <= fbuf(r@, rts@, #[trigger] full3[k].0).len() && (full3[k].0
                            == usize::MAX || (full3[k].0 < env.ents@.len() && env.ents@[full3[k].0 as int].kind == 0)) by {
                            if k < fr1.len() {
                                assert(full3[k] == fr1[k]);
                            }
                        }
                    }
                    assert forall|k: int| 0 <= k < full3.len() implies (#[trigger] full3[k]).1 <= full3[k].2 by {
                        if k < fr1.len() {
                            assert(full3[k] == fr1[k]);
                        }
                    }
                    lemma_fmeas_nonneg(full3, b);
                }
            },
        }
    }
}

} // verus!
