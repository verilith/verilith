//! Why and where a document was rejected.
//!
//! The first half is specification: `document_fail` says which error a
//! text that is not a well-formed document gets, and at which byte. It
//! reads the text as `document` does, item by item, and the error is at
//! the first item that is not well-formed:
//!
//! - the first byte that is not part of a `Char` (`Encoding`);
//! - the XML declaration, if it is the one that fails;
//! - the comment or processing instruction that fails, in the prolog or
//!   after the root element;
//! - the declaration of the internal subset that fails, or else the
//!   document type declaration itself (also when an attribute default
//!   refers to an entity it may not);
//! - the item of content that fails: a start tag, an end tag that does not
//!   match, a reference, a comment, a CDATA section, a processing
//!   instruction or a run of text, at its first byte;
//! - the end of the input, when it ends inside the root element or the
//!   internal subset;
//! - whatever follows the root element that is not a comment, a processing
//!   instruction or white space.
//!
//! `lemma_document_fail` proves that it reports an error exactly when
//! `document` rejects the text. The second half computes it: `explain` is
//! proven to return `document_fail`'s error, and `line_col` its line and
//! column.
use crate::chars::*;
use crate::content::*;
use crate::doc::*;
use crate::dtd::*;
use crate::lex::*;
use crate::spec::*;
use crate::tape::*;
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

/// Why a text is not a well-formed document.
pub enum Why {
    /// A byte that is not part of a `Char` encoded in UTF-8.
    Encoding,
    /// The text breaks the grammar or a well-formedness constraint.
    Syntax,
    /// The text is longer than token positions hold (`MAX_POS`).
    TooLarge,
}

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// The first byte from `i` on that does not begin a `Char` in UTF-8 (see
/// `chars_from`), or the end.
pub open spec fn bad_char(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        i
    } else {
        match utf8_len(s, i) {
            None => i,
            Some(l) => if i + l <= s.len() && char_seq_ok(s, i, l) {
                bad_char(s, i + l)
            } else {
                i
            },
        }
    }
}

/// `misc`, with the start of the comment or processing instruction that
/// fails.
pub open spec fn misc_fail(s: Seq<u8>, i: int, tape: Seq<XTok>) -> Result<(Seq<XTok>, int), int>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if has_lit(s, j, lit_comment()) {
        match comment(s, j, tape) {
            None => Err(j),
            Some((t, e)) => if i < e <= s.len() {
                misc_fail(s, e, t)
            } else {
                Err(j)
            },
        }
    } else if has_lit(s, j, lit_pi()) {
        match pi(s, j, tape) {
            None => Err(j),
            Some((t, e)) => if i < e <= s.len() {
                misc_fail(s, e, t)
            } else {
                Err(j)
            },
        }
    } else {
        Ok((tape, j))
    }
}

/// `int_subset`, with the start of the declaration that fails (or the end
/// of the input, if it has no `]`).
pub open spec fn int_subset_fail(s: Seq<u8>, i: int, tape: Seq<XTok>, st: DtdSt) -> Result<
    (Seq<XTok>, DtdSt, int),
    int,
>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if !(0 <= j < s.len()) {
        Err(s.len() as int)
    } else if s[j] == 0x5D {
        Ok((tape, st, j))
    } else {
        match decl(s, j, tape, st) {
            None => Err(j),
            Some((t, st2, e)) => if i < e <= s.len() {
                int_subset_fail(s, e, t, st2)
            } else {
                Err(j)
            },
        }
    }
}

/// `doctype` at `i`: an error in the internal subset where
/// `int_subset_fail` puts it, any other at `i`.
pub open spec fn doctype_fail(s: Seq<u8>, i: int, tape: Seq<XTok>, sa: bool) -> Result<
    (Seq<XTok>, int, Env),
    int,
> {
    let j = ws_end(s, i + 9);
    let n = name_end(s, j);
    if j == i + 9 || n == j {
        Err(i)
    } else {
        let t1 = tape.push(XTok::Doctype { start: j, end: n });
        let k = ws_end(s, n);
        let er = if k > n && (has_lit(s, k, lit_system()) || has_lit(s, k, lit_public())) {
            match external_id(s, k, t1) {
                Some((t, e)) => Some((t, e, true)),
                None => None,
            }
        } else {
            Some((t1, n, false))
        };
        match er {
            None => Err(i),
            Some((t2, e, ext)) => {
                let m = ws_end(s, e);
                if byte_is(s, m, 0x5B) {
                    match int_subset_fail(s, m + 1, t2, dtd_init(sa)) {
                        Err(p) => Err(p),
                        Ok((t3, st, q)) => {
                            let r = ws_end(s, q + 1);
                            if byte_is(s, r, 0x3E) {
                                Ok((t3.push(XTok::DoctypeEnd), r + 1, env_of(s, st, ext)))
                            } else {
                                Err(i)
                            }
                        },
                    }
                } else if byte_is(s, m, 0x3E) {
                    Ok((t2.push(XTok::DoctypeEnd), m + 1, env_of(s, dtd_init(sa), ext)))
                } else {
                    Err(i)
                }
            },
        }
    }
}

pub open spec fn doctype_opt_fail(s: Seq<u8>, p: int, t: Seq<XTok>, sd: int) -> Result<
    (Seq<XTok>, int, Env),
    int,
> {
    if has_lit(s, p, lit_doctype()) {
        doctype_fail(s, p, t, sd == 1)
    } else {
        Ok((t, p, no_dtd()))
    }
}

/// `prolog`, with its error: the XML declaration at the start (after a
/// byte order mark), a comment or processing instruction, or the
/// document type declaration (`doctype_fail`; at its start when an
/// attribute default fails `defaults_ok`).
pub open spec fn prolog_fail(s: Seq<u8>, enc: Enc) -> Result<(Seq<XTok>, int, Env), int> {
    match decl_head(s, enc) {
        None => Err(bom_end(s)),
        Some((t0, p1, sd)) => match misc_fail(s, p1, t0) {
            Err(p) => Err(p),
            Ok((t1, p2)) => match doctype_opt_fail(s, p2, t1, sd) {
                Err(p) => Err(p),
                Ok((t2, p3, env)) => match misc_fail(s, p3, t2) {
                    Err(p) => Err(p),
                    Ok((t3, p4)) => if defaults_ok(s, t3, env) {
                        Ok((t3, p4, env))
                    } else {
                        Err(p2)
                    },
                },
            },
        },
    }
}

/// Where the attributes of a start tag from `i` on fail (see `attrs`):
/// the attribute with no white space before it or no name, its `=`, its
/// opening quote, or its value; or the end and whether it is an
/// empty-element tag. (`attrs` without the tape, which only collects.)
pub open spec fn attrs_pos(s: Seq<u8>, i: int, env: Env) -> Result<(int, bool), int>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if byte_is(s, j, 0x3E) {
        Ok((j + 1, false))
    } else if has_lit(s, j, lit_empty_end()) {
        Ok((j + 2, true))
    } else if j == i {
        Err(j)
    } else {
        let n = name_end(s, j);
        if n == j {
            Err(j)
        } else {
            match eq_end(s, n) {
                None => Err(n),
                Some(v) => if 0 <= v < s.len() && quote(s[v]) {
                    match att_chars(s, v + 1, s[v], Some(env)) {
                        None => Err(v + 1),
                        Some(q) => if i < q + 1 <= s.len() {
                            attrs_pos(s, q + 1, env)
                        } else {
                            Err(v + 1)
                        },
                    }
                } else {
                    Err(v)
                },
            }
        }
    }
}

/// Where the start tag at `i` fails: in its attributes (`attrs_pos`), or
/// at `i` (no name, or an attribute name twice).
pub open spec fn stag_at(s: Seq<u8>, i: int, env: Env) -> int {
    let n = name_end(s, i + 1);
    if n == i + 1 {
        i
    } else {
        match attrs_pos(s, n, env) {
            Err(p) => p,
            Ok(_) => i,
        }
    }
}

/// The item at `i` is a start tag (see `item`).
pub open spec fn is_stag_at(s: Seq<u8>, i: int) -> bool {
    s[i] == 0x3C && !byte_is(s, i + 1, 0x2F) && !has_lit(s, i, lit_comment()) && !has_lit(s, i, lit_cdata())
        && !byte_is(s, i + 1, 0x3F)
}

/// Where the item at `i` fails: inside it for a start tag (`stag_at`),
/// at its start for any other.
pub open spec fn item_at(s: Seq<u8>, i: int, env: Env) -> int {
    if is_stag_at(s, i) {
        stag_at(s, i, env)
    } else {
        i
    }
}

/// `content`, with where the item that fails fails (`item_at`), or the
/// end of the input if it ends inside an element.
pub open spec fn content_fail(s: Seq<u8>, i: int, stack: Seq<Open>, tape: Seq<XTok>, env: Env) -> Result<
    (Seq<XTok>, int),
    int,
>
    decreases s.len() - i,
{
    if stack.len() == 0 {
        Ok((tape, i))
    } else if !(0 <= i < s.len()) {
        Err(s.len() as int)
    } else {
        match item(s, i, stack, tape, env) {
            None => Err(item_at(s, i, env)),
            Some((st2, t2, e)) => if i < e <= s.len() {
                content_fail(s, e, st2, t2, env)
            } else {
                Err(i)
            },
        }
    }
}

/// `element`, with its error: in the root element's start tag
/// (`stag_at`), or `content_fail`'s.
pub open spec fn element_fail(s: Seq<u8>, i: int, tape: Seq<XTok>, env: Env) -> Result<(Seq<XTok>, int), int> {
    if !byte_is(s, i, 0x3C) {
        Err(i)
    } else {
        match stag(s, i, tape, env) {
            None => Err(stag_at(s, i, env)),
            Some((t, e, empty)) => if empty {
                Ok((close_at(t.push(XTok::ETag), tape.len() as int), e))
            } else {
                content_fail(s, e, seq![(i + 1, name_end(s, i + 1), tape.len() as int)], t, env)
            },
        }
    }
}

/// **The error a text gets** (see the top of this file): `Ok` with the
/// tape when it is a well-formed document.
pub open spec fn document_fail(s: Seq<u8>, enc: Enc) -> Result<Seq<XTok>, (int, Why)> {
    if !doc_chars(s) {
        Err((bad_char(s, 0), Why::Encoding))
    } else {
        match prolog_fail(s, enc) {
            Err(p) => Err((p, Why::Syntax)),
            Ok((t, p, env)) => match element_fail(s, p, t, env) {
                Err(q) => Err((q, Why::Syntax)),
                Ok((t2, e)) => match misc_fail(s, e, t2) {
                    Err(q) => Err((q, Why::Syntax)),
                    Ok((t3, f)) => if f == s.len() {
                        Ok(t3)
                    } else {
                        Err((f, Why::Syntax))
                    },
                },
            },
        }
    }
}

/// The number of line feeds in `s[..p]`.
pub open spec fn count_lf(s: Seq<u8>, p: int) -> int
    decreases p,
{
    if p <= 0 {
        0
    } else {
        count_lf(s, p - 1) + if s[p - 1] == 0x0A { 1int } else { 0 }
    }
}

/// The start of the line that `p` is on: just past the last line feed
/// before it, or 0.
pub open spec fn line_start(s: Seq<u8>, p: int) -> int
    decreases p,
{
    if p <= 0 {
        0
    } else if s[p - 1] == 0x0A {
        p
    } else {
        line_start(s, p - 1)
    }
}

// ---------------------------------------------------------------------------
// The errors agree with the grammar
// ---------------------------------------------------------------------------

/// `r` and `o` agree: both fail, or both succeed with the same value.
pub open spec fn agree<T, E>(r: Result<T, E>, o: Option<T>) -> bool {
    match (r, o) {
        (Ok(a), Some(b)) => a == b,
        (Err(_), None) => true,
        _ => false,
    }
}

pub proof fn lemma_bad_char(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        chars_from(s, i) ==> bad_char(s, i) == s.len(),
        !chars_from(s, i) ==> i <= bad_char(s, i) < s.len(),
    decreases s.len() - i,
{
    if i < s.len() {
        if let Some(l) = utf8_len(s, i) {
            if i + l <= s.len() && char_seq_ok(s, i, l) {
                lemma_bad_char(s, i + l);
            }
        }
    }
}

pub proof fn lemma_misc_fail(s: Seq<u8>, i: int, tape: Seq<XTok>)
    ensures
        agree(misc_fail(s, i, tape), misc(s, i, tape)),
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if has_lit(s, j, lit_comment()) {
        if let Some((t, e)) = comment(s, j, tape) {
            if i < e <= s.len() {
                lemma_misc_fail(s, e, t);
            }
        }
    } else if has_lit(s, j, lit_pi()) {
        if let Some((t, e)) = pi(s, j, tape) {
            if i < e <= s.len() {
                lemma_misc_fail(s, e, t);
            }
        }
    }
}

pub proof fn lemma_int_subset_fail(s: Seq<u8>, i: int, tape: Seq<XTok>, st: DtdSt)
    ensures
        agree(int_subset_fail(s, i, tape, st), int_subset(s, i, tape, st)),
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if 0 <= j < s.len() && s[j] != 0x5D {
        if let Some((t, st2, e)) = decl(s, j, tape, st) {
            if i < e <= s.len() {
                lemma_int_subset_fail(s, e, t, st2);
            }
        }
    }
}

pub proof fn lemma_doctype_fail(s: Seq<u8>, i: int, tape: Seq<XTok>, sa: bool)
    ensures
        agree(doctype_fail(s, i, tape, sa), doctype(s, i, tape, sa)),
{
    let j = ws_end(s, i + 9);
    let n = name_end(s, j);
    if !(j == i + 9 || n == j) {
        let t1 = tape.push(XTok::Doctype { start: j, end: n });
        let k = ws_end(s, n);
        let er = if k > n && (has_lit(s, k, lit_system()) || has_lit(s, k, lit_public())) {
            match external_id(s, k, t1) {
                Some((t, e)) => Some((t, e, true)),
                None => None,
            }
        } else {
            Some((t1, n, false))
        };
        if let Some((t2, e, ext)) = er {
            let m = ws_end(s, e);
            lemma_int_subset_fail(s, m + 1, t2, dtd_init(sa));
        }
    }
}

pub proof fn lemma_prolog_fail(s: Seq<u8>, enc: Enc)
    ensures
        agree(prolog_fail(s, enc), prolog(s, enc)),
{
    if let Some((t0, p1, sd)) = decl_head(s, enc) {
        lemma_misc_fail(s, p1, t0);
        if let Some((t1, p2)) = misc(s, p1, t0) {
            if has_lit(s, p2, lit_doctype()) {
                lemma_doctype_fail(s, p2, t1, sd == 1);
            }
            if let Some((t2, p3, env)) = doctype_opt(s, p2, t1, sd) {
                lemma_misc_fail(s, p3, t2);
            }
        }
    }
}

pub proof fn lemma_content_fail(s: Seq<u8>, i: int, stack: Seq<Open>, tape: Seq<XTok>, env: Env)
    ensures
        agree(content_fail(s, i, stack, tape, env), content(s, i, stack, tape, env)),
    decreases s.len() - i,
{
    if stack.len() > 0 && 0 <= i < s.len() {
        if let Some((st2, t2, e)) = item(s, i, stack, tape, env) {
            if i < e <= s.len() {
                lemma_content_fail(s, e, st2, t2, env);
            }
        }
    }
}

pub proof fn lemma_element_fail(s: Seq<u8>, i: int, tape: Seq<XTok>, env: Env)
    ensures
        agree(element_fail(s, i, tape, env), element(s, i, tape, env)),
{
    if byte_is(s, i, 0x3C) {
        if let Some((t, e, empty)) = stag(s, i, tape, env) {
            if !empty {
                lemma_content_fail(s, e, seq![(i + 1, name_end(s, i + 1), tape.len() as int)], t, env);
            }
        }
    }
}

/// **`document_fail` reports an error exactly when `document` rejects
/// the text**, and otherwise gives `document`'s tape.
pub proof fn lemma_document_fail(s: Seq<u8>, enc: Enc)
    ensures
        agree(document_fail(s, enc), document(s, enc)),
{
    if doc_chars(s) {
        lemma_prolog_fail(s, enc);
        if let Some((t, p, env)) = prolog(s, enc) {
            lemma_element_fail(s, p, t, env);
            if let Some((t2, e)) = element(s, p, t, env) {
                lemma_misc_fail(s, e, t2);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Computing it
// ---------------------------------------------------------------------------

fn ex_bad_char(s: &[u8]) -> (r: usize)
    ensures
        r as int == bad_char(s@, 0),
{
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            bad_char(s@, i as int) == bad_char(s@, 0),
        decreases n - i,
    {
        let b = get(s, i);
        if b < 0x80 {
            if b < 0x20 && b != 0x09 && b != 0x0A && b != 0x0D {
                return i;
            }
            i = i + 1;
        } else {
            match ex_cp_at_hi(s, i) {
                None => {
                    return i;
                },
                Some((c, l)) => {
                    proof {
                        lemma_cp_in_bounds(s@, i as int);
                    }
                    if l == 3 && c >= 0xFFFE {
                        proof {
                            assert(s@[i as int] == 0xEF && s@[i as int + 1] == 0xBF && s@[i as int + 2] >= 0xBE);
                        }
                        return i;
                    }
                    proof {
                        if l == 3 {
                            assert(!(s@[i as int] == 0xEF && s@[i as int + 1] == 0xBF && s@[i as int + 2] >= 0xBE));
                        }
                    }
                    i = i + l;
                },
            }
        }
    }
    i
}

fn ex_misc_fail(s: &[u8], i: usize, tape: &mut Tape) -> (r: Result<usize, usize>)
    requires
        i <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
    ensures
        match misc_fail(s@, i as int, old(tape)@) {
            Ok((t, e)) => r == Ok::<usize, usize>(e as usize) && final(tape)@ == t && i <= e <= s@.len() && t.len()
                <= e,
            Err(p) => r == Err::<usize, usize>(p as usize) && i <= p <= s@.len(),
        },
{
    let mut j = i;
    proof {
        lemma_lits();
    }
    loop
        invariant
            i <= j <= s@.len() <= isize::MAX,
            s@.len() <= MAX_POS,
            tape@.len() <= j,
            misc_fail(s@, j as int, tape@) == misc_fail(s@, i as int, old(tape)@),
            L_COMMENT@ == lit_comment(),
        decreases s@.len() - j,
    {
        let k = ex_ws_end(s, j);
        if ex_has_lit(s, k, &L_COMMENT) {
            match ex_comment(s, k, tape) {
                None => {
                    return Err(k);
                },
                Some(e) => {
                    j = e;
                },
            }
        } else if ex_has2(s, k, 0x3C, 0x3F) {
            proof {
                assert(lit_pi() =~= seq![0x3Cu8, 0x3F]);
            }
            match ex_pi(s, k, tape) {
                None => {
                    return Err(k);
                },
                Some(e) => {
                    j = e;
                },
            }
        } else {
            proof {
                assert(lit_pi() =~= seq![0x3Cu8, 0x3F]);
            }
            return Ok(k);
        }
    }
}

fn ex_int_subset_fail(s: &[u8], i: usize, tape: &mut Tape, d: &mut XDtd) -> (r: Result<usize, usize>)
    requires
        i <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
        dtd_wf(s@, old(d)),
        old(d).ents@.len() <= old(tape)@.len(),
    ensures
        match int_subset_fail(s@, i as int, old(tape)@, dtd_view(s@, old(d))) {
            Ok((t, st, e)) => r == Ok::<usize, usize>(e as usize) && final(tape)@ == t && dtd_view(s@, final(d))
                == st && i <= e < s@.len() && t.len() <= e,
            Err(p) => r == Err::<usize, usize>(p as usize) && i <= p <= s@.len(),
        },
        r is Ok ==> dtd_wf(s@, final(d)) && final(d).ents@.len() <= final(tape)@.len(),
{
    let mut j0 = i;
    loop
        invariant
            i <= j0 <= s@.len() <= isize::MAX,
            s@.len() <= MAX_POS,
            tape@.len() <= j0,
            dtd_wf(s@, d),
            d.ents@.len() <= tape@.len(),
            int_subset_fail(s@, j0 as int, tape@, dtd_view(s@, d)) == int_subset_fail(
                s@,
                i as int,
                old(tape)@,
                dtd_view(s@, old(d)),
            ),
        decreases s@.len() - j0,
    {
        let j = ex_ws_end(s, j0);
        if j >= s.len() {
            return Err(s.len());
        }
        if get(s, j) == 0x5D {
            return Ok(j);
        }
        match ex_decl(s, j, tape, d) {
            None => {
                return Err(j);
            },
            Some(e) => {
                j0 = e;
            },
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn ex_doctype_fail(s: &[u8], i: usize, tape: &mut Tape, sa: bool) -> (r: Result<(usize, DtdOut), usize>)
    requires
        i + 9 <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
    ensures
        match doctype_fail(s@, i as int, old(tape)@, sa) {
            Ok((t, e, env)) => r matches Ok((x, xe)) && x == e && final(tape)@ == t && out_view(s@, &xe) == env
                && out_wf(s@, &xe) && i < e <= s@.len() && t.len() <= e,
            Err(p) => r matches Err(x) && x == p && i <= p <= s@.len(),
        },
{
    let j = ex_ws_end(s, i + 9);
    let n = ex_name_end(s, j);
    if j == i + 9 || n == j {
        return Err(i);
    }
    tape.push(tok(Kind::Doctype, j, n, 0));
    let k = ex_ws_end(s, n);
    proof {
        lemma_lits();
    }
    let (e, ext) = if k > n && (ex_has_lit(s, k, &L_SYSTEM) || ex_has_lit(s, k, &L_PUBLIC)) {
        match ex_external_id(s, k, tape) {
            Some(e) => (e, true),
            None => {
                return Err(i);
            },
        }
    } else {
        (n, false)
    };
    let m = ex_ws_end(s, e);
    let mut d = XDtd { ents: Vec::new(), pe_seen: false, sa };
    proof {
        assert(ents_view(s@, d.ents@) =~= Seq::<Ent>::empty());
        assert(dtd_view(s@, &d) == dtd_init(sa));
    }
    if ex_byte_is(s, m, 0x5B) {
        match ex_int_subset_fail(s, m + 1, tape, &mut d) {
            Err(p) => Err(p),
            Ok(q) => {
                let r = ex_ws_end(s, q + 1);
                if ex_byte_is(s, r, 0x3E) {
                    tape.push(tok(Kind::DoctypeEnd, 0, 0, 0));
                    Ok((r + 1, ex_finish(s, d, ext)))
                } else {
                    Err(i)
                }
            },
        }
    } else if ex_byte_is(s, m, 0x3E) {
        tape.push(tok(Kind::DoctypeEnd, 0, 0, 0));
        proof {
            assert(dtd_wf(s@, &d));
        }
        Ok((m + 1, ex_finish(s, d, ext)))
    } else {
        Err(i)
    }
}

fn ex_doctype_opt_fail(s: &[u8], p: usize, tape: &mut Tape, sd: u8) -> (r: Result<(usize, DtdOut), usize>)
    requires
        p <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= p,
    ensures
        match doctype_opt_fail(s@, p as int, old(tape)@, sd as int) {
            Ok((t, e, env)) => r matches Ok((x, xe)) && x == e && final(tape)@ == t && out_view(s@, &xe) == env
                && out_wf(s@, &xe) && p <= e <= s@.len() && t.len() <= e,
            Err(q) => r matches Err(x) && x == q && q <= s@.len(),
        },
{
    proof {
        lemma_lits();
    }
    if ex_has_lit(s, p, &L_DOCTYPE) {
        ex_doctype_fail(s, p, tape, sd == 1)
    } else {
        let e = DtdOut::none(s);
        proof {
            assert(ents_view(s@, e.ents@) =~= Seq::<Ent>::empty());
            assert(e.oka@ =~= Seq::<bool>::empty());
            assert(e.okc@ =~= Seq::<bool>::empty());
            assert(out_view(s@, &e) == no_dtd());
        }
        Ok((p, e))
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn ex_prolog_fail(s: &[u8], tape: &mut Tape, enc: Enc) -> (r: Result<(usize, DtdOut), usize>)
    requires
        s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() == 0,
    ensures
        match prolog_fail(s@, enc) {
            Ok((t, p, env)) => r matches Ok((x, xe)) && x == p && final(tape)@ == t && out_view(s@, &xe) == env
                && out_wf(s@, &xe) && p <= s@.len() && t.len() <= p,
            Err(q) => r matches Err(x) && x == q && q <= s@.len(),
        },
{
    let (p1, sd) = match ex_decl_head(s, tape, enc) {
        None => {
            let b: usize = if s.len() >= 3 && get(s, 0) == 0xEF && get(s, 1) == 0xBB && get(s, 2) == 0xBF {
                proof {
                    assert(s@.subrange(0, 3) =~= seq![0xEFu8, 0xBB, 0xBF]);
                }
                3
            } else {
                proof {
                    if s.len() >= 3 {
                        assert(s@.subrange(0, 3)[0] == s@[0]);
                        assert(s@.subrange(0, 3)[1] == s@[1]);
                        assert(s@.subrange(0, 3)[2] == s@[2]);
                    }
                }
                0
            };
            return Err(b);
        },
        Some(x) => x,
    };
    let p2 = match ex_misc_fail(s, p1, tape) {
        Err(q) => {
            return Err(q);
        },
        Ok(p) => p,
    };
    let (p3, dtd) = match ex_doctype_opt_fail(s, p2, tape, sd) {
        Err(q) => {
            return Err(q);
        },
        Ok(x) => x,
    };
    let p4 = match ex_misc_fail(s, p3, tape) {
        Err(q) => {
            return Err(q);
        },
        Ok(p) => p,
    };
    let ok = {
        let env = dtd.env(s);
        ex_defaults_ok(s, tape, &env)
    };
    if ok {
        Ok((p4, dtd))
    } else {
        Err(p2)
    }
}

fn ex_attrs_pos(s: &[u8], i: usize, env: &XEnv) -> (r: Result<(usize, bool), usize>)
    requires
        i <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        env_wf(env),
    ensures
        match attrs_pos(s@, i as int, env_view(env)) {
            Ok((e, empty)) => r == Ok::<(usize, bool), usize>((e as usize, empty)),
            Err(p) => r == Err::<(usize, bool), usize>(p as usize) && i <= p <= s@.len(),
        },
{
    let mut j0 = i;
    proof {
        assert(lit_empty_end() =~= seq![0x2Fu8, 0x3E]);
    }
    loop
        invariant
            i <= j0 <= s@.len() <= isize::MAX,
            s@.len() <= MAX_POS,
            env_wf(env),
            lit_empty_end() == seq![0x2Fu8, 0x3E],
            attrs_pos(s@, j0 as int, env_view(env)) == attrs_pos(s@, i as int, env_view(env)),
        decreases s@.len() - j0,
    {
        let j = ex_ws_end(s, j0);
        if ex_byte_is(s, j, 0x3E) {
            return Ok((j + 1, false));
        }
        if ex_has2(s, j, 0x2F, 0x3E) {
            return Ok((j + 2, true));
        }
        if j == j0 {
            return Err(j);
        }
        let n = ex_name_end(s, j);
        if n == j {
            return Err(j);
        }
        let v = match ex_eq_end(s, n) {
            None => {
                return Err(n);
            },
            Some(v) => v,
        };
        if !(v < s.len() && (get(s, v) == 0x22 || get(s, v) == 0x27)) {
            return Err(v);
        }
        proof {
            lemma_lim_all(env);
        }
        match ex_att_chars(s, v + 1, get(s, v), Some(env), env.ents.len()) {
            None => {
                return Err(v + 1);
            },
            Some((q, _)) => {
                j0 = q + 1;
            },
        }
    }
}

fn ex_stag_at(s: &[u8], i: usize, env: &XEnv) -> (r: usize)
    requires
        i < s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        env_wf(env),
    ensures
        r as int == stag_at(s@, i as int, env_view(env)),
        i <= r <= s@.len(),
{
    let n = ex_name_end(s, i + 1);
    if n == i + 1 {
        return i;
    }
    match ex_attrs_pos(s, n, env) {
        Err(p) => p,
        Ok(_) => i,
    }
}

fn ex_item_at(s: &[u8], i: usize, env: &XEnv) -> (r: usize)
    requires
        i < s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        env_wf(env),
    ensures
        r as int == item_at(s@, i as int, env_view(env)),
        i <= r <= s@.len(),
{
    proof {
        lemma_lits();
        assert(lit_pi() =~= seq![0x3Cu8, 0x3F]);
    }
    if get(s, i) == 0x3C && !ex_byte_is(s, i + 1, 0x2F) && !ex_has_lit(s, i, &L_COMMENT) && !ex_has_lit(s, i, &L_CDATA)
        && !ex_byte_is(s, i + 1, 0x3F) {
        ex_stag_at(s, i, env)
    } else {
        i
    }
}

fn ex_content_fail(s: &[u8], i: usize, stack: &mut Vec<(usize, usize, usize)>, tape: &mut Tape, env: &XEnv) -> (r:
    Result<usize, usize>)
    requires
        i <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
        env_wf(env),
        stack_ok(s@, old(stack)@, old(tape)@),
    ensures
        match content_fail(s@, i as int, stack_view(old(stack)@), old(tape)@, env_view(env)) {
            Ok((t, e)) => r matches Ok(x) && x == e && final(tape)@ == t && i <= e <= s@.len() && t.len() <= e,
            Err(p) => r matches Err(x) && x == p && i <= p <= s@.len(),
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
            content_fail(s@, j as int, stack_view(stack@), tape@, env_view(env)) == content_fail(
                s@,
                i as int,
                stack_view(old(stack)@),
                old(tape)@,
                env_view(env),
            ),
        decreases n - j,
    {
        if stack.len() == 0 {
            return Ok(j);
        }
        if j >= n {
            return Err(n);
        }
        match ex_item(s, j, stack, tape, env) {
            None => {
                return Err(ex_item_at(s, j, env));
            },
            Some(e) => {
                j = e;
            },
        }
    }
}

fn ex_element_fail(s: &[u8], i: usize, tape: &mut Tape, env: &XEnv) -> (r: Result<usize, usize>)
    requires
        i <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
        env_wf(env),
    ensures
        match element_fail(s@, i as int, old(tape)@, env_view(env)) {
            Ok((t, e)) => r matches Ok(x) && x == e && final(tape)@ == t && i <= e <= s@.len() && t.len() <= e,
            Err(p) => r matches Err(x) && x == p && i <= p <= s@.len(),
        },
{
    if !ex_byte_is(s, i, 0x3C) {
        return Err(i);
    }
    let k0 = tape.len();
    match ex_stag(s, i, tape, env) {
        None => Err(ex_stag_at(s, i, env)),
        Some((e, empty, nm)) => {
            if empty {
                tape.push(tok(Kind::ETag, 0, 0, 0));
                tape.close(k0);
                Ok(e)
            } else {
                let mut stack: Vec<(usize, usize, usize)> = Vec::new();
                stack.push((i + 1, nm, k0));
                proof {
                    assert(stack_view(stack@) =~= seq![((i + 1) as int, nm as int, k0 as int)]);
                }
                ex_content_fail(s, e, &mut stack, tape, env)
            }
        },
    }
}

/// **The error the text `s` (in UTF-8, read from a document in `enc`)
/// gets** (`document_fail`), `TooLarge` past `MAX_POS` bytes; `Ok` when
/// it is a well-formed document.
pub fn explain(s: &[u8], enc: Enc) -> (r: Result<(), (usize, Why)>)
    ensures
        s@.len() > MAX_POS ==> r == Err::<(), (usize, Why)>((0, Why::TooLarge)),
        s@.len() <= MAX_POS ==> match document_fail(s@, enc) {
            Ok(_) => r is Ok,
            Err((p, w)) => r == Err::<(), (usize, Why)>((p as usize, w)) && p <= s@.len(),
        },
{
    slice_len_bound(s);
    if s.len() as u64 > MAX_POS {
        return Err((0, Why::TooLarge));
    }
    if !ex_doc_chars(s) {
        let p = ex_bad_char(s);
        proof {
            lemma_bad_char(s@, 0);
        }
        return Err((p, Why::Encoding));
    }
    let mut tape = Tape::new();
    let (p, dtd) = match ex_prolog_fail(s, &mut tape, enc) {
        Err(q) => {
            return Err((q, Why::Syntax));
        },
        Ok(x) => x,
    };
    let e = {
        let env = dtd.env(s);
        match ex_element_fail(s, p, &mut tape, &env) {
            Err(q) => {
                return Err((q, Why::Syntax));
            },
            Ok(e) => e,
        }
    };
    match ex_misc_fail(s, e, &mut tape) {
        Err(q) => Err((q, Why::Syntax)),
        Ok(f) => if f == s.len() {
            Ok(())
        } else {
            Err((f, Why::Syntax))
        },
    }
}

/// The 1-based line and column (in bytes) of offset `p`; lines end at
/// line feeds. (`p < usize::MAX` holds: a slice has at most `isize::MAX`
/// bytes.)
pub fn line_col(s: &[u8], p: usize) -> (r: (usize, usize))
    requires
        p <= s@.len(),
        p < usize::MAX,
    ensures
        r.0 as int == 1 + count_lf(s@, p as int),
        r.1 as int == 1 + p - line_start(s@, p as int),
{
    let mut n: usize = 0;
    let mut st: usize = 0;
    let mut k: usize = 0;
    while k < p
        invariant
            k <= p <= s@.len(),
            n as int == count_lf(s@, k as int),
            st as int == line_start(s@, k as int),
            n <= k,
            st <= k,
        decreases p - k,
    {
        if s[k] == 0x0A {
            n += 1;
            st = k + 1;
        }
        k += 1;
    }
    (n + 1, p - st + 1)
}

} // verus!
