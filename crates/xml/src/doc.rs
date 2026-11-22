//! Verified code for whole documents: the prolog, the check of attribute
//! defaults, and `document`.
use crate::chars::*;
use crate::content::*;
use crate::dtd::*;
use crate::lex::*;
use crate::spec::*;
use crate::tape::*;
use vstd::prelude::*;

verus! {

/// `defaults_ok`: every attribute default's references, against the
/// entities declared before it.
fn ex_defaults_ok(s: &[u8], tape: &Tape, env: &XEnv) -> (r: bool)
    requires
        s@.len() <= isize::MAX,
        env_wf(env),
    ensures
        r == defaults_ok(s@, tape@, env_view(env)),
{
    let n = tape.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == tape@.len(),
            s@.len() <= isize::MAX,
            env_wf(env),
            forall|m: int|
                0 <= m < k ==> match #[trigger] tape@[m] {
                    XTok::AttDefault { start, end, kind, nents } => kind < 3 || (0 <= start <= end < s@.len() && 0
                        <= nents <= env_view(env).ents.len() && att_chars(
                        s@,
                        start,
                        s@[end],
                        Some(
                            Env {
                                ents: env_view(env).ents.subrange(0, nents),
                                wfc: env.wfc,
                                oka: env.oka@,
                                okc: env.okc@,
                            },
                        ),
                    ) is Some),
                    _ => true,
                },
        decreases n - k,
    {
        let t = tape.toks[k];
        proof {
            assert(tape@[k as int] == t@);
        }
        if is_att_default(t.kind) && t.f >= 3 {
            let a = t.a as usize;
            let b = t.b as usize;
            let lim = t.c as usize;
            if !(a <= b && b < s.len() && lim <= env.ents.len()) {
                return false;
            }
            if ex_att_chars(s, a, get(s, b), Some(env), lim).is_none() {
                return false;
            }
        }
        k = k + 1;
    }
    true
}

/// `decl_head`: the position after the XML declaration, if any, and the
/// standalone declaration.
fn ex_decl_head(s: &[u8], tape: &mut Tape, enc: Enc) -> (r: Option<(usize, u8)>)
    requires
        s@.len() <= isize::MAX,
        old(tape)@.len() == 0,
    ensures
        match decl_head(s@, enc) {
            Some((t, p, sd)) => r matches Some((x, y)) && x == p && y == sd && final(tape)@ == t && p <= s@.len()
                && t.len() <= p,
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    let n = s.len();
    let p0: usize = if n >= 3 && get(s, 0) == 0xEF && get(s, 1) == 0xBB && get(s, 2) == 0xBF {
        proof {
            assert(s@.subrange(0, 3) =~= seq![0xEFu8, 0xBB, 0xBF]);
        }
        3
    } else {
        proof {
            if n >= 3 {
                assert(s@.subrange(0, 3)[0] == s@[0]);
                assert(s@.subrange(0, 3)[1] == s@[1]);
                assert(s@.subrange(0, 3)[2] == s@[2]);
            }
        }
        0
    };
    if ex_has_lit(s, p0, &L_XMLDECL) && p0 + 5 < n && ex_is_ws(get(s, p0 + 5)) {
        ex_xmldecl(s, p0, tape, enc)
    } else {
        Some((p0, 0u8))
    }
}

/// `doctype_opt` at `p`.
fn ex_doctype_opt(s: &[u8], p: usize, tape: &mut Tape, sd: u8) -> (r: Option<(usize, DtdOut)>)
    requires
        p <= s@.len() <= isize::MAX,
        old(tape)@.len() <= p,
    ensures
        match doctype_opt(s@, p as int, old(tape)@, sd as int) {
            Some((t, e, env)) => r matches Some((x, xe)) && x == e && final(tape)@ == t && out_view(s@, &xe) == env
                && out_wf(s@, &xe) && p <= e <= s@.len() && t.len() <= e,
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    if ex_has_lit(s, p, &L_DOCTYPE) {
        ex_doctype(s, p, tape, sd == 1)
    } else {
        let e = DtdOut::none(s);
        proof {
            assert(ents_view(s@, e.ents@) =~= Seq::<Ent>::empty());
            assert(e.oka@ =~= Seq::<bool>::empty());
            assert(e.okc@ =~= Seq::<bool>::empty());
            assert(out_view(s@, &e) == no_dtd());
        }
        Some((p, e))
    }
}

/// The prolog: the position of the root element, and what the document
/// type declaration leaves for the content.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn ex_prolog(s: &[u8], tape: &mut Tape, enc: Enc) -> (r: Option<(usize, DtdOut)>)
    requires
        s@.len() <= isize::MAX,
        old(tape)@.len() == 0,
    ensures
        match prolog(s@, enc) {
            Some((t, p, env)) => r matches Some((x, xe)) && x == p && final(tape)@ == t && out_view(s@, &xe) == env
                && out_wf(s@, &xe) && p <= s@.len() && t.len() <= p,
            None => r is None,
        },
{
    let (p1, sd) = match ex_decl_head(s, tape, enc) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let p2 = match ex_misc(s, p1, tape) {
        None => {
            return None;
        },
        Some(p) => p,
    };
    let (p3, dtd) = match ex_doctype_opt(s, p2, tape, sd) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let p4 = match ex_misc(s, p3, tape) {
        None => {
            return None;
        },
        Some(p) => p,
    };
    let ok = {
        let env = dtd.env(s);
        ex_defaults_ok(s, tape, &env)
    };
    if ok {
        Some((p4, dtd))
    } else {
        None
    }
}

/// `document`: whether `s` is a well-formed XML document, with its tape in
/// `tape` and what its DTD declares in the result.
pub fn ex_document(s: &[u8], tape: &mut Tape, enc: Enc) -> (r: Option<DtdOut>)
    ensures
        match document(s@, enc) {
            Some(t) => r is Some && final(tape)@ == t,
            None => r is None,
        },
        r matches Some(d) ==> final(tape)@.len() <= s@.len() && out_wf(s@, &d),
{
    slice_len_bound(s);
    if !ex_doc_chars(s) {
        return None;
    }
    tape.clear();
    // Documents run at about one token per ten to twenty bytes.
    tape.reserve(s.len() / 16);
    let (p, dtd) = match ex_prolog(s, tape, enc) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let e = {
        let env = dtd.env(s);
        match ex_element(s, p, tape, &env) {
            None => {
                tape.fail(p);
                return None;
            },
            Some(e) => e,
        }
    };
    match ex_misc(s, e, tape) {
        None => None,
        Some(f) => if f == s.len() {
            Some(dtd)
        } else {
            tape.fail(f);
            None
        },
    }
}

} // verus!
