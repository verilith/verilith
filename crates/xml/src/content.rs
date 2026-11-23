//! Verified code for elements and whole documents: start tags and their
//! attributes, the content loop with its stack of open elements, the
//! prolog, and `document`. Each function is proven to return exactly what
//! the spec function of the same name returns.
use crate::chars::*;
use crate::lex::*;
use crate::spec::*;
use crate::tape::*;
use vstd::prelude::*;

verus! {

/// Every `Attr` token from `first` on has its span inside the input.
pub open spec fn attr_spans_ok(s: Seq<u8>, t: Seq<XTok>, first: int) -> bool {
    forall|m: int|
        #![trigger t[m]]
        first <= m < t.len() && t[m] is Attr ==> 0 <= t[m]->Attr_start <= t[m]->Attr_end <= s.len()
}

/// `attrs` from `i`: the end, and whether the tag was empty.
fn ex_attrs(s: &[u8], i: usize, tape: &mut Tape, env: &XEnv) -> (r: Option<(usize, bool)>)
    requires
        i <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() + 1 <= i,
        env_wf(env),
    ensures
        match attrs(s@, i as int, old(tape)@, env_view(env)) {
            Some((t, e, empty)) => r == Some((e as usize, empty)) && final(tape)@ == t && i < e <= s@.len() && t.len()
                + 1 <= e,
            None => r is None,
        },
        r is Some ==> old(tape)@.len() <= final(tape)@.len() && attr_spans_ok(s@, final(tape)@, old(tape)@.len() as int)
            && forall|k: int| 0 <= k < old(tape)@.len() ==> #[trigger] final(tape)@[k] == old(tape)@[k],
{
    let mut j0 = i;
    proof {
        assert(lit_empty_end() =~= seq![0x2Fu8, 0x3E]);
    }
    loop
        invariant
            i <= j0 <= s@.len() <= isize::MAX,
            s@.len() <= MAX_POS,
            tape@.len() + 1 <= j0,
            env_wf(env),
            lit_empty_end() == seq![0x2Fu8, 0x3E],
            old(tape)@.len() <= tape@.len(),
            attr_spans_ok(s@, tape@, old(tape)@.len() as int),
            forall|k: int| 0 <= k < old(tape)@.len() ==> #[trigger] tape@[k] == old(tape)@[k],
            attrs(s@, j0 as int, tape@, env_view(env)) == attrs(s@, i as int, old(tape)@, env_view(env)),
        decreases s@.len() - j0,
    {
        let j = ex_ws_end(s, j0);
        if ex_byte_is(s, j, 0x3E) {
            return Some((j + 1, false));
        }
        if ex_has2(s, j, 0x2F, 0x3E) {
            return Some((j + 2, true));
        }
        if j == j0 {
            tape.fail(j);
            return None;
        }
        let n = ex_name_end(s, j);
        if n == j {
            tape.fail(j);
            return None;
        }
        let v = match ex_eq_end(s, n) {
            None => {
                tape.fail(n);
                return None;
            },
            Some(v) => v,
        };
        if !(v < s.len() && (get(s, v) == 0x22 || get(s, v) == 0x27)) {
            tape.fail(v);
            return None;
        }
        proof {
            lemma_lim_all(env);
        }
        match ex_att_chars(s, v + 1, get(s, v), Some(env), env.ents.len()) {
            None => {
                tape.fail(v + 1);
                return None;
            },
            Some((q, plain)) => {
                tape.push(tok(Kind::Attr, j, n, 0));
                tape.push(tok(Kind::AttVal, v + 1, q, if plain { 1 } else { 0 }));
                j0 = q + 1;
            },
        }
    }
}

/// `attrs_distinct` of the tokens from `first` on, by comparing every
/// pair of names.
fn ex_attrs_distinct(s: &[u8], tape: &Tape, first: usize) -> (r: bool)
    requires
        first <= tape@.len() <= isize::MAX,
        tape@.len() <= MAX_POS,
        attr_spans_ok(s@, tape@, first as int),
    ensures
        r == attrs_distinct(s@, tape@, first as int),
{
    slice_len_bound(s);
    let n = tape.len();
    if n - first > 16 {
        return crate::uniq::ex_distinct_hashed(s, tape, first);
    }
    let mut k = first;
    while k < n
        invariant
            first <= k <= n,
            n == tape@.len(),
            attr_spans_ok(s@, tape@, first as int),
            s@.len() <= isize::MAX,
            forall|j: int, k2: int|
                first <= j < k2 < k && #[trigger] tape@[j] is Attr && #[trigger] tape@[k2] is Attr ==> s@.subrange(
                    tape@[j]->Attr_start,
                    tape@[j]->Attr_end,
                ) != s@.subrange(tape@[k2]->Attr_start, tape@[k2]->Attr_end),
        decreases n - k,
    {
        let tk = tape.toks[k];
        proof {
            assert(tape@[k as int] == tk@);
        }
        if is_attr(tk.kind) {
            let kl = tk.low_len();
            let mut j = first;
            while j < k
                invariant
                    first <= j <= k < n,
                    n == tape@.len(),
                    tape@[k as int] == tk@,
                    tk.kind == Kind::Attr,
                    kl == low_len(tk),
                    attr_spans_ok(s@, tape@, first as int),
                    s@.len() <= isize::MAX,
                    forall|j2: int|
                        first <= j2 < j && #[trigger] tape@[j2] is Attr ==> s@.subrange(
                            tape@[j2]->Attr_start,
                            tape@[j2]->Attr_end,
                        ) != s@.subrange(tk.sa(), tk.sb()),
                decreases k - j,
            {
                let tj = tape.toks[j];
                proof {
                    assert(tape@[j as int] == tj@);
                }
                if is_attr(tj.kind) {
                    proof {
                        assert(tape@[k as int] is Attr);
                        assert(tape@[j as int] is Attr);
                        assert(0 <= tape@[j as int]->Attr_start <= tape@[j as int]->Attr_end <= s@.len());
                        assert(0 <= tape@[k as int]->Attr_start <= tape@[k as int]->Attr_end <= s@.len());
                    }
                    // Names whose lengths differ in their low 32 bits differ:
                    // a cheap test before reading the 48-bit positions.
                    if tj.low_len() != kl {
                        proof {
                            if tj.sb() - tj.sa() == tk.sb() - tk.sa() {
                                lemma_low_len(tj, tk);
                            }
                            assert(s@.subrange(tj.sa(), tj.sb()).len() != s@.subrange(tk.sa(), tk.sb()).len());
                        }
                    } else if ex_bytes_eq(s, tj.a() as usize, tj.b() as usize, s, tk.a() as usize, tk.b() as usize) {
                        proof {
                            assert(tape@[j as int] is Attr && tape@[k as int] is Attr);
                        }
                        return false;
                    }
                }
                j = j + 1;
            }
            proof {
                assert forall|j2: int, k2: int|
                    first <= j2 < k2 < k + 1 && #[trigger] tape@[j2] is Attr && #[trigger] tape@[k2] is Attr implies s@.subrange(
                        tape@[j2]->Attr_start,
                        tape@[j2]->Attr_end,
                    ) != s@.subrange(tape@[k2]->Attr_start, tape@[k2]->Attr_end) by {
                    if k2 == k {
                    }
                }
            }
        } else {
            proof {
                assert(!(tape@[k as int] is Attr));
            }
        }
        k = k + 1;
    }
    true
}

/// `stag` at `i` (`s[i]` is `<`): the end, whether the tag was empty, and
/// the end of the element type's name.
fn ex_stag(s: &[u8], i: usize, tape: &mut Tape, env: &XEnv) -> (r: Option<(usize, bool, usize)>)
    requires
        i < s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
        env_wf(env),
    ensures
        match stag(s@, i as int, old(tape)@, env_view(env)) {
            Some((t, e, empty)) => r == Some((e as usize, empty, name_end(s@, i + 1) as usize)) && final(tape)@
                == t && i < e <= s@.len() && t.len() + 1 <= e,
            None => r is None,
        },
        r matches Some((_, _, n)) ==> i + 1 < n <= s@.len() && n == name_end(s@, i + 1),
        r is Some ==> old(tape)@.len() < final(tape)@.len() && final(tape)@[old(tape)@.len() as int] is STag
            && forall|k: int| 0 <= k < old(tape)@.len() ==> #[trigger] final(tape)@[k] == old(tape)@[k],
{
    let n = ex_name_end(s, i + 1);
    if n == i + 1 {
        return None;
    }
    let first = tape.len() + 1;
    tape.push(tok(Kind::STag, i + 1, n, 0));
    let ghost t1 = tape@;
    match ex_attrs(s, n, tape, env) {
        None => None,
        Some((e, empty)) => {
            proof {
                assert(tape@[first - 1] == t1[first - 1]);
            }
            if ex_attrs_distinct(s, tape, first) {
                Some((e, empty, n))
            } else {
                tape.fail(i);
                None
            }
        },
    }
}

pub open spec fn stack_view(st: Seq<(usize, usize, usize)>) -> Seq<Open> {
    st.map_values(|x: (usize, usize, usize)| (x.0 as int, x.1 as int, x.2 as int))
}

/// The open elements' names lie in the input and their start tags are
/// start tags in the tape.
pub open spec fn stack_ok(s: Seq<u8>, st: Seq<(usize, usize, usize)>, t: Seq<XTok>) -> bool {
    forall|q: int|
        #![trigger st[q]]
        0 <= q < st.len() ==> st[q].0 <= st[q].1 <= s.len() && (st[q].2 as int) < t.len() && t[st[q].2 as int] is STag
}

proof fn lemma_stack_grow(s: Seq<u8>, st: Seq<(usize, usize, usize)>, t: Seq<XTok>, t2: Seq<XTok>)
    requires
        stack_ok(s, st, t),
        t.len() <= t2.len(),
        forall|k: int| 0 <= k < t.len() ==> #[trigger] t2[k] == t[k],
    ensures
        stack_ok(s, st, t2),
{
    assert forall|q: int| 0 <= q < st.len() implies #[trigger] st[q].0 <= st[q].1 <= s.len() && (st[q].2 as int)
        < t2.len() && t2[st[q].2 as int] is STag by {
        assert(t2[st[q].2 as int] == t[st[q].2 as int]);
    }
}

/// One `item` at `j` with the open elements `stack`: the end.
#[verifier::spinoff_prover]
#[verifier::rlimit(120)]
pub fn ex_item(s: &[u8], j: usize, stack: &mut Vec<(usize, usize, usize)>, tape: &mut Tape, env: &XEnv) -> (r: Option<usize>)
    requires
        j < s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= j,
        env_wf(env),
        stack_ok(s@, old(stack)@, old(tape)@),
    ensures
        match item(s@, j as int, stack_view(old(stack)@), old(tape)@, env_view(env)) {
            Some((st, t, e)) => r matches Some(x) && x == e && stack_view(final(stack)@) == st && final(tape)@ == t
                && j < e <= s@.len() && t.len() <= e && stack_ok(s@, final(stack)@, final(tape)@),
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    let ghost sv = stack_view(stack@);
    let ghost t0 = tape@;
    proof {
        assert(sv.len() == stack@.len());
    }
    let c = get(s, j);
    if c == 0x3C {
        if ex_byte_is(s, j + 1, 0x2F) {
            if stack.len() == 0 {
                return None;
            }
            let top = stack[stack.len() - 1];
            proof {
                assert(sv.last() == (top.0 as int, top.1 as int, top.2 as int));
                assert(top.0 <= top.1 <= s@.len());
            }
            let m = ex_name_end(s, j + 2);
            if !ex_bytes_eq(s, j + 2, m, s, top.0 as usize, top.1 as usize) {
                return None;
            }
            let e = ex_ws_end(s, m);
            if !ex_byte_is(s, e, 0x3E) {
                return None;
            }
            tape.push(tok(Kind::ETag, 0, 0, 0));
            proof {
                assert(tape@[top.2 as int] == t0[top.2 as int]);
            }
            tape.close(top.2 as usize);
            let ghost st_old = stack@;
            stack.pop();
            proof {
                assert(stack@ =~= st_old.drop_last());
                assert(stack_view(stack@) =~= sv.drop_last());
                assert forall|q: int| 0 <= q < stack@.len() implies #[trigger] stack@[q].0 <= stack@[q].1 <= s@.len()
                    && (stack@[q].2 as int) < tape@.len() && tape@[stack@[q].2 as int] is STag by {
                    assert(stack@[q] == st_old[q]);
                    let k = st_old[q].2 as int;
                    assert(t0[k] is STag);
                    if k != top.2 as int {
                        assert(tape@[k] == t0[k]);
                    }
                }
            }
            Some(e + 1)
        } else if ex_has_lit(s, j, &L_COMMENT) {
            let r = ex_comment(s, j, tape);
            proof {
                if r is Some {
                    lemma_stack_grow(s@, stack@, t0, tape@);
                }
            }
            r
        } else if ex_has_lit(s, j, &L_CDATA) {
            match ex_cdata_end(s, j + 9) {
                None => None,
                Some((e, cr)) => {
                    tape.push(tok(Kind::CData, j + 9, e - 3, if cr { 1 } else { 0 }));
                    proof {
                        lemma_stack_grow(s@, stack@, t0, tape@);
                    }
                    Some(e)
                },
            }
        } else if ex_byte_is(s, j + 1, 0x3F) {
            let r = ex_pi(s, j, tape);
            proof {
                if r is Some {
                    lemma_stack_grow(s@, stack@, t0, tape@);
                }
            }
            r
        } else {
            let k0 = tape.len();
            match ex_stag(s, j, tape, env) {
                None => None,
                Some((e, empty, nm)) => {
                    proof {
                        lemma_stack_grow(s@, stack@, t0, tape@);
                    }
                    if empty {
                        let ghost t1 = tape@;
                        tape.push(tok(Kind::ETag, 0, 0, 0));
                        proof {
                            assert(tape@[k0 as int] == t1[k0 as int]);
                        }
                        tape.close(k0);
                        proof {
                            assert forall|q: int| 0 <= q < stack@.len() implies #[trigger] stack@[q].0 <= stack@[q].1
                                <= s@.len() && (stack@[q].2 as int) < tape@.len() && tape@[stack@[q].2 as int] is STag by {
                                let k = stack@[q].2 as int;
                                assert(t1[k] is STag);
                                if k != k0 as int {
                                    assert(tape@[k] == t1[k]);
                                }
                            }
                        }
                    } else {
                        let ghost st_old = stack@;
                        stack.push((j + 1, nm, k0));
                        proof {
                            assert(stack_view(stack@) =~= sv.push(((j + 1) as int, nm as int, k0 as int)));
                            assert forall|q: int| 0 <= q < stack@.len() implies #[trigger] stack@[q].0 <= stack@[q].1
                                <= s@.len() && (stack@[q].2 as int) < tape@.len() && tape@[stack@[q].2 as int] is STag by {
                                if q < st_old.len() {
                                    assert(stack@[q] == st_old[q]);
                                }
                            }
                        }
                    }
                    Some(e)
                },
            }
        }
    } else if c == 0x26 {
        match ex_content_ref(s, j, env) {
            None => None,
            Some((t, e)) => {
                tape.push(t);
                proof {
                    lemma_stack_grow(s@, stack@, t0, tape@);
                }
                Some(e)
            },
        }
    } else {
        match ex_text_end(s, j) {
            None => None,
            Some((e, cr)) => {
                tape.push(tok(Kind::Text, j, e, if cr { 1 } else { 0 }));
                proof {
                    lemma_stack_grow(s@, stack@, t0, tape@);
                }
                Some(e)
            },
        }
    }
}

/// `content` from `i` with the open elements `stack`: the position after
/// the end tag of the outermost.
fn ex_content(s: &[u8], i: usize, stack: &mut Vec<(usize, usize, usize)>, tape: &mut Tape, env: &XEnv) -> (r: Option<
    usize,
>)
    requires
        i <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
        env_wf(env),
        stack_ok(s@, old(stack)@, old(tape)@),
    ensures
        match content(s@, i as int, stack_view(old(stack)@), old(tape)@, env_view(env)) {
            Some((t, e)) => r matches Some(x) && x == e && final(tape)@ == t && i <= e <= s@.len() && t.len() <= e,
            None => r is None,
        },
{
    let n = s.len();
    let mut j = i;
    loop
        invariant
            i <= j <= n,
            n == s@.len() <= isize::MAX,
            s@.len() <= MAX_POS,
            tape@.len() <= j,
            env_wf(env),
            stack_ok(s@, stack@, tape@),
            content(s@, j as int, stack_view(stack@), tape@, env_view(env)) == content(
                s@,
                i as int,
                stack_view(old(stack)@),
                old(tape)@,
                env_view(env),
            ),
        decreases n - j,
    {
        if stack.len() == 0 {
            return Some(j);
        }
        if j >= n {
            return None;
        }
        match ex_item(s, j, stack, tape, env) {
            None => {
                tape.fail(j);
                return None;
            },
            Some(e) => {
                j = e;
            },
        }
    }
}

/// `ent_content(r, 0, [], [], env)`: the replacement text `r` as
/// content, into `tape`.
pub fn ex_ent_content(r: &[u8], tape: &mut Tape, env: &XEnv) -> (ok: bool)
    requires
        r@.len() <= isize::MAX,
        r@.len() <= MAX_POS,
        env_wf(env),
    ensures
        match ent_content(r@, 0, Seq::empty(), Seq::empty(), env_view(env)) {
            Some(t) => ok && final(tape)@ == t,
            None => !ok,
        },
{
    let n = r.len();
    let mut j: usize = 0;
    let mut stack: Vec<(usize, usize, usize)> = Vec::new();
    tape.clear();
    proof {
        assert(stack_view(stack@) =~= Seq::<Open>::empty());
    }
    loop
        invariant
            j <= n,
            n == r@.len() <= isize::MAX,
            r@.len() <= MAX_POS,
            tape@.len() <= j,
            env_wf(env),
            stack_ok(r@, stack@, tape@),
            ent_content(r@, j as int, stack_view(stack@), tape@, env_view(env)) == ent_content(
                r@,
                0,
                Seq::empty(),
                Seq::empty(),
                env_view(env),
            ),
        decreases n - j,
    {
        if j >= n {
            return stack.len() == 0;
        }
        match ex_item(r, j, &mut stack, tape, env) {
            None => {
                tape.fail(j);
                return false;
            },
            Some(e) => {
                j = e;
            },
        }
    }
}

/// `element` at `i`.
pub fn ex_element(s: &[u8], i: usize, tape: &mut Tape, env: &XEnv) -> (r: Option<usize>)
    requires
        i <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
        env_wf(env),
    ensures
        match element(s@, i as int, old(tape)@, env_view(env)) {
            Some((t, e)) => r matches Some(x) && x == e && final(tape)@ == t && i <= e <= s@.len() && t.len() <= e,
            None => r is None,
        },
{
    if !ex_byte_is(s, i, 0x3C) {
        return None;
    }
    let k0 = tape.len();
    match ex_stag(s, i, tape, env) {
        None => None,
        Some((e, empty, nm)) => {
            if empty {
                tape.push(tok(Kind::ETag, 0, 0, 0));
                tape.close(k0);
                Some(e)
            } else {
                let mut stack: Vec<(usize, usize, usize)> = Vec::new();
                stack.push((i + 1, nm, k0));
                proof {
                    assert(stack_view(stack@) =~= seq![((i + 1) as int, nm as int, k0 as int)]);
                }
                ex_content(s, e, &mut stack, tape, env)
            }
        },
    }
}

} // verus!
