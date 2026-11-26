//! The external parsed entities a document reaches, read with the
//! caller's loader (`parse_with`), and the check that no entity it reaches
//! refers to itself (§4.1, WFC: No Recursion).
//!
//! A reference in content to a declared entity names it (`find_ent`, the
//! first declaration binding, §4.2). An entity's replacement text is its
//! literal value's for an internal entity, and for an external parsed
//! entity the text the loader gives for its identifiers (`question`):
//! decoded by its byte order mark or text declaration, its text
//! declaration left out and its line ends normalized (`ext_rt`). That
//! text must be content (§4.3.2, `ent_content`); `bad` says it is not.
//! The entity `k` refers to `m` (`edge`) when a reference in its
//! replacement text, parsed as content, names `m`. The entities the
//! document reaches are those a path of such references leads to from a
//! reference in the document's content (`reachable`).
//!
//! `ex_read_external` walks them depth first, with a stack of its own (no
//! recursion, so a long chain of entities cannot exhaust the thread's
//! stack), and is proven to answer:
//!
//! * `Ok(reads)`: no entity the document reaches is `bad` or on a cycle
//!   of references (`on_cycle`), and `reads` holds, for exactly the
//!   entities it reaches, the text read and the tape of the replacement
//!   text (`read_ok`).
//! * `Err(Syntax)`: some entity the document reaches is `bad` or on a
//!   cycle.
//! * `Err(Limit)`: the loader read more than `MAX_EXT_ENTITIES` entities
//!   or `MAX_EXT_BYTES` bytes (by its own counts, which are trusted).
//!
//! The proof of `Ok` keeps a finishing number for each entity done: every
//! reference from a done entity is to a done entity finished before it,
//! so references only go down in that order and none can come back. An
//! `Err(Syntax)` for a cycle comes with one: the stack is a path, and a
//! reference to an entity on it closes it.
use crate::content::ex_ent_content;
#[cfg(verus_keep_ghost)]
use crate::decode::eol;
use crate::decode::ex_eol;
use crate::lex::*;
#[cfg(verus_keep_ghost)]
use crate::pe::load_model;
use crate::pe::{ex_ext_text, Loader};
#[cfg(verus_keep_ghost)]
use crate::pe_spec::ext_text;
use crate::pe_spec::LoadFn;
use crate::spec::*;
use crate::tape::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

/// At most this many external entities are read for a document (with the
/// external subset and parameter entities), and at most this many bytes
/// of them in all.
pub const MAX_EXT_ENTITIES: usize = 1 << 12;

pub const MAX_EXT_BYTES: usize = 1 << 28;

// ---------------------------------------------------------------------------
// The question for an external entity
// ---------------------------------------------------------------------------

/// The declaration of the general entity whose name is at `a..b`: the first
/// `EntityDecl` token there, from `i` on.
pub open spec fn decl_from(pt: Seq<Tok>, a: int, b: int, i: int) -> Option<int>
    decreases pt.len() - i,
{
    if i < 0 || i >= pt.len() {
        None
    } else if pt[i].kind is EntityDecl && pt[i].f == 0 && pt[i].sa() == a && pt[i].sb() == b {
        Some(i)
    } else {
        decl_from(pt, a, b, i + 1)
    }
}

/// The external identifiers that follow a declaration, from `i` on: the
/// system identifier's span and the public identifier's (empty if none),
/// or `None` for an unparsed entity (`NData`), or a span outside the text.
pub open spec fn ids_from(n: int, pt: Seq<Tok>, i: int, sys: (int, int), pb: (int, int)) -> Option<((int, int), (int, int))>
    decreases pt.len() - i,
{
    if i < 0 || i >= pt.len() {
        Some((sys, pb))
    } else if pt[i].kind is SysId {
        if 0 <= pt[i].sa() <= pt[i].sb() <= n {
            ids_from(n, pt, i + 1, (pt[i].sa(), pt[i].sb()), pb)
        } else {
            None
        }
    } else if pt[i].kind is PubId {
        if 0 <= pt[i].sa() <= pt[i].sb() <= n {
            ids_from(n, pt, i + 1, sys, (pt[i].sa(), pt[i].sb()))
        } else {
            None
        }
    } else if pt[i].kind is NData {
        None
    } else {
        Some((sys, pb))
    }
}

/// The trace of the DTD read whole: where each parameter entity's text
/// begins (its name, and its base URI) and ends (`None`).
pub type Trace = Seq<(usize, Option<Vec<u8>>, Vec<u8>)>;

/// The base URI of the innermost entity whose text holds position `pos`:
/// the trace's entries up to `pos` open (push) and close (pop) entities;
/// `open` holds the entries of those open, innermost last.
pub open spec fn base_from(tr: Trace, pos: int, i: int, open: Seq<int>) -> Seq<u8>
    decreases tr.len() - i,
{
    if i < 0 || i >= tr.len() || tr[i].0 > pos {
        if open.len() > 0 && 0 <= open.last() < tr.len() {
            tr[open.last()].2@
        } else {
            Seq::empty()
        }
    } else if tr[i].1 is Some {
        base_from(tr, pos, i + 1, open.push(i))
    } else {
        base_from(tr, pos, i + 1, if open.len() > 0 {
            open.drop_last()
        } else {
            open
        })
    }
}

/// What a document's entities are read from: the declarations' text and
/// tokens, the entities, their environment (`env_view`), the internal
/// entities' replacement texts, the trace, the loader's answers, and the
/// document's text, tokens and root element.
pub struct World {
    pub dtext: Seq<u8>,
    pub pt: Seq<Tok>,
    pub ents: Seq<XEnt>,
    pub env: Env,
    pub rts: Seq<Seq<u8>>,
    pub tr: Trace,
    pub lf: LoadFn,
    pub doc: Seq<u8>,
    pub dt: Seq<Tok>,
    pub root: int,
}

/// The question the loader is asked for entity `k`: (the base URI, the
/// system identifier, the public identifier), if it is an external parsed
/// entity.
pub open spec fn question_of(dtext: Seq<u8>, pt: Seq<Tok>, ents: Seq<XEnt>, tr: Trace, k: int) -> Option<
    (Seq<u8>, Seq<u8>, Seq<u8>),
> {
    let e = ents[k];
    if e.kind != 1 {
        None
    } else {
        match decl_from(pt, e.a as int, e.b as int, 0) {
            None => None,
            Some(i) => match ids_from(dtext.len() as int, pt, i + 1, (0, 0), (0, 0)) {
                None => None,
                Some((sy, pb)) => Some(
                    (base_from(tr, e.a as int, 0, Seq::empty()), dtext.subrange(sy.0, sy.1), dtext.subrange(pb.0, pb.1)),
                ),
            },
        }
    }
}

pub open spec fn question(w: World, k: int) -> Option<(Seq<u8>, Seq<u8>, Seq<u8>)> {
    question_of(w.dtext, w.pt, w.ents, w.tr, k)
}

/// The bytes the loader gives for entity `k`.
pub open spec fn answer(w: World, k: int) -> Option<Seq<u8>> {
    match question(w, k) {
        None => None,
        Some(q) => match (w.lf)(q.0, q.1, q.2) {
            Some((b, u)) => Some(b),
            None => None,
        },
    }
}

/// The replacement text of the external entity `k` read: decoded, after
/// its text declaration, line ends normalized.
#[verifier::opaque]
pub open spec fn ext_rt(w: World, k: int) -> Option<Seq<u8>> {
    match answer(w, k) {
        None => None,
        Some(b) => match ext_text(b) {
            None => None,
            Some((t, p)) => Some(eol(t, p, t.len() as int)),
        },
    }
}

/// The external entity `k` was read and is not well-formed: its bytes are
/// not text, or its text is not content (§4.3.2).
#[verifier::opaque]
pub open spec fn bad(w: World, k: int) -> bool {
    &&& answer(w, k) is Some
    &&& match ext_rt(w, k) {
        None => true,
        Some(r) => ent_content(r, 0, Seq::empty(), Seq::empty(), w.env) is None,
    }
}

/// The replacement text of entity `k`, if it is known: an internal
/// entity's, or an external parsed entity's that was read and is content.
#[verifier::opaque]
pub open spec fn rt(w: World, k: int) -> Option<Seq<u8>> {
    if w.ents[k].kind == 0 {
        Some(w.rts[k])
    } else if w.ents[k].kind == 1 && !bad(w, k) {
        ext_rt(w, k)
    } else {
        None
    }
}

/// The tape of entity `k`'s replacement text as content, if it is.
#[verifier::opaque]
pub open spec fn tape_of(w: World, k: int) -> Option<Seq<XTok>> {
    match rt(w, k) {
        Some(r) => ent_content(r, 0, Seq::empty(), Seq::empty(), w.env),
        None => None,
    }
}

/// Its tokens: none if it has no tape.
#[verifier::opaque]
pub open spec fn toks_of(w: World, k: int) -> Seq<XTok> {
    match tape_of(w, k) {
        Some(t) => t,
        None => Seq::empty(),
    }
}

/// The entity a token in the text `x` refers to, if it is an entity
/// reference to a declared entity.
pub open spec fn ref_of(w: World, x: Seq<u8>, tk: XTok) -> Option<int> {
    match tk {
        XTok::EntRef { start, end } => if 0 <= start <= end <= x.len() {
            find_ent(w.env.ents, x.subrange(start, end))
        } else {
            None
        },
        _ => None,
    }
}

/// The `j`th token of entity `k` refers to an entity.
#[verifier::opaque]
pub open spec fn ref_in(w: World, k: int, j: int) -> Option<int> {
    ref_of(
        w,
        match rt(w, k) {
            Some(r) => r,
            None => Seq::empty(),
        },
        toks_of(w, k)[j],
    )
}

/// The replacement text of `k` refers to `m`.
#[verifier::opaque]
pub open spec fn edge(w: World, k: int, m: int) -> bool {
    exists|j: int| 0 <= j < toks_of(w, k).len() && #[trigger] ref_in(w, k, j) == Some(m)
}

/// The document's content refers to `m`: a reference from the root
/// element on.
#[verifier::opaque]
pub open spec fn root_ref(w: World, m: int) -> bool {
    exists|j: int| w.root <= j < w.dt.len() && #[trigger] ref_of(w, w.doc, w.dt[j]@) == Some(m)
}

/// Each entity of `p` refers to the next.
#[verifier::opaque]
pub open spec fn path(w: World, p: Seq<int>) -> bool {
    &&& p.len() > 0
    &&& forall|i: int| 0 <= i < p.len() - 1 ==> edge(w, #[trigger] p[i], p[i + 1])
}

/// The document reaches `k`.
#[verifier::opaque]
pub open spec fn reachable(w: World, k: int) -> bool {
    exists|p: Seq<int>| #[trigger] path(w, p) && root_ref(w, p[0]) && p.last() == k
}

/// `k` refers to itself, directly or through others (§4.1, WFC: No
/// Recursion).
#[verifier::opaque]
pub open spec fn on_cycle(w: World, k: int) -> bool {
    exists|p: Seq<int>| #[trigger] path(w, p) && p.len() >= 2 && p[0] == k && p.last() == k
}

// ---------------------------------------------------------------------------
// Reading one entity
// ---------------------------------------------------------------------------

/// What was read for an entity: the text of an external one, and the tape
/// of its replacement text as content.
pub struct ERead {
    pub text: Option<Vec<u8>>,
    pub tape: Option<Tape>,
}

/// Why reading the external entities failed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RErr {
    /// An entity the document reaches is not well-formed, or refers to
    /// itself.
    Syntax,
    /// The loader read more than the limits allow.
    Limit,
}

/// `r` is what is read for entity `k`.
#[verifier::opaque]
pub open spec fn read_ok(w: World, k: int, r: ERead) -> bool {
    &&& match r.text {
        Some(t) => w.ents[k].kind == 1 && rt(w, k) == Some(t@),
        None => w.ents[k].kind != 1 || rt(w, k) is None,
    }
    &&& match r.tape {
        Some(t) => tape_of(w, k) == Some(t@),
        None => tape_of(w, k) is None,
    }
}

/// The world of these arguments.
pub open spec fn world(
    env: &XEnv,
    rts: &[Vec<u8>],
    pt: &[Tok],
    tr: &[(usize, Option<Vec<u8>>, Vec<u8>)],
    lf: LoadFn,
    doc: &[u8],
    dt: &[Tok],
    root: usize,
) -> World {
    World {
        dtext: env.doc@,
        pt: pt@,
        ents: env.ents@,
        env: env_view(env),
        rts: rts@.map_values(|v: Vec<u8>| v@),
        tr: tr@,
        lf,
        doc: doc@,
        dt: dt@,
        root: root as int,
    }
}

/// What the arguments must be: the environment the document was checked
/// with, and one replacement text per entity, each short enough for token
/// positions (the parser's, as `dtd::rts_ok` states).
pub open spec fn args_ok(env: &XEnv, rts: &[Vec<u8>]) -> bool {
    &&& env_wf(env)
    &&& rts@.len() == env.ents@.len()
    &&& forall|k: int| 0 <= k < rts@.len() ==> (#[trigger] rts@[k])@.len() <= MAX_POS
}

/// `decl_from`.
fn ex_decl_from(pt: &[Tok], a: usize, b: usize) -> (r: Option<usize>)
    ensures
        same(r, decl_from(pt@, a as int, b as int, 0)),
        r matches Some(i) ==> i < pt@.len(),
{
    let mut i: usize = 0;
    while i < pt.len()
        invariant
            i <= pt@.len(),
            decl_from(pt@, a as int, b as int, 0) == decl_from(pt@, a as int, b as int, i as int),
        decreases pt@.len() - i,
    {
        let t = pt[i];
        let is_decl = match t.kind {
            Kind::EntityDecl => true,
            _ => false,
        };
        if is_decl && t.f == 0 && t.a48() == a as u64 && t.b48() == b as u64 {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

/// `ids_from(n, pt, i, (0, 0), (0, 0))`.
fn ex_ids_from(n: usize, pt: &[Tok], i: usize) -> (r: Option<((usize, usize), (usize, usize))>)
    ensures
        match ids_from(n as int, pt@, i as int, (0, 0), (0, 0)) {
            Some((sy, pb)) => r matches Some((x, y)) && x.0 == sy.0 && x.1 == sy.1 && y.0 == pb.0 && y.1 == pb.1
                && sy.0 <= sy.1 <= n && pb.0 <= pb.1 <= n,
            None => r is None,
        },
{
    let mut sys: (usize, usize) = (0, 0);
    let mut pb: (usize, usize) = (0, 0);
    let mut j = i;
    while j < pt.len()
        invariant
            i <= j,
            sys.0 <= sys.1 <= n,
            pb.0 <= pb.1 <= n,
            ids_from(n as int, pt@, i as int, (0, 0), (0, 0)) == ids_from(
                n as int,
                pt@,
                j as int,
                (sys.0 as int, sys.1 as int),
                (pb.0 as int, pb.1 as int),
            ),
        decreases pt@.len() - j,
    {
        let t = pt[j];
        let a = t.a48();
        let b = t.b48();
        match t.kind {
            Kind::SysId => {
                if a <= b && b <= n as u64 {
                    sys = (a as usize, b as usize);
                } else {
                    return None;
                }
            },
            Kind::PubId => {
                if a <= b && b <= n as u64 {
                    pb = (a as usize, b as usize);
                } else {
                    return None;
                }
            },
            Kind::NData => {
                return None;
            },
            _ => {
                return Some((sys, pb));
            },
        }
        j = j + 1;
    }
    Some((sys, pb))
}

/// `base_from(tr, pos, 0, [])`, as an entry of the trace (`None`: empty).
fn ex_base(tr: &[(usize, Option<Vec<u8>>, Vec<u8>)], pos: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < tr@.len() && tr@[i as int].2@ == base_from(tr@, pos as int, 0, Seq::empty()),
            None => base_from(tr@, pos as int, 0, Seq::empty()) == Seq::<u8>::empty(),
        },
{
    let mut open: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(open@.map_values(|x: usize| x as int) =~= Seq::<int>::empty());
    }
    while i < tr.len() && tr[i].0 <= pos
        invariant
            i <= tr@.len(),
            forall|p: int| 0 <= p < open@.len() ==> #[trigger] open@[p] < tr@.len(),
            base_from(tr@, pos as int, 0, Seq::empty()) == base_from(
                tr@,
                pos as int,
                i as int,
                open@.map_values(|x: usize| x as int),
            ),
        decreases tr@.len() - i,
    {
        let ghost ov = open@.map_values(|x: usize| x as int);
        if tr[i].1.is_some() {
            open.push(i);
            proof {
                assert(open@.map_values(|x: usize| x as int) =~= ov.push(i as int));
            }
        } else if open.len() > 0 {
            open.pop();
            proof {
                assert(open@.map_values(|x: usize| x as int) =~= ov.drop_last());
            }
        }
        i = i + 1;
    }
    let ghost ov = open@.map_values(|x: usize| x as int);
    if open.len() > 0 {
        let l = open[open.len() - 1];
        proof {
            assert(ov.last() == l as int);
            assert(open@[open@.len() - 1] < tr@.len());
        }
        Some(l)
    } else {
        None
    }
}

/// The question for entity `k` (`question`).
fn ex_question<'a>(env: &'a XEnv, pt: &[Tok], tr: &'a [(usize, Option<Vec<u8>>, Vec<u8>)], k: usize) -> (r: Option<
    (&'a [u8], &'a [u8], &'a [u8]),
>)
    requires
        env_wf(env),
        k < env.ents@.len(),
    ensures
        match question_of(env.doc@, pt@, env.ents@, tr@, k as int) {
            Some((b, s, p)) => r matches Some((x, y, z)) && x@ == b && y@ == s && z@ == p,
            None => r is None,
        },
{
    let e = env.ents[k];
    if e.kind != 1 {
        return None;
    }
    let i = match ex_decl_from(pt, e.a, e.b) {
        Some(i) => i,
        None => {
            return None;
        },
    };
    let np = pt.len();
    proof {
        assert(i < np);
    }
    let ((sa, sb), (pa, pb)) = match ex_ids_from(env.doc.len(), pt, i + 1) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let base: &[u8] = match ex_base(tr, e.a) {
        Some(j) => tr[j].2.as_slice(),
        None => &[],
    };
    proof {
        assert(env.ents@[k as int] == e);
    }
    Some((base, vstd::slice::slice_subrange(env.doc, sa, sb), vstd::slice::slice_subrange(env.doc, pa, pb)))
}

} // verus!

verus! {

/// `eol` gives no more bytes than it reads.
pub proof fn lemma_eol_len(s: Seq<u8>, a: int, b: int)
    ensures
        eol(s, a, b).len() <= if a <= b {
            b - a
        } else {
            0
        },
    decreases b - a,
{
    if 0 <= a < b <= s.len() {
        if s[a] == 0x0D && a + 1 < b && s[a + 1] == 0x0A {
            lemma_eol_len(s, a + 2, b);
        } else {
            lemma_eol_len(s, a + 1, b);
        }
    }
}

/// The world is that of these arguments, with the loader's answers `lf`.
pub open spec fn fits(
    w: World,
    env: &XEnv,
    rts: &[Vec<u8>],
    pt: &[Tok],
    tr: &[(usize, Option<Vec<u8>>, Vec<u8>)],
    lf: LoadFn,
) -> bool {
    &&& w.dtext == env.doc@
    &&& w.pt == pt@
    &&& w.ents == env.ents@
    &&& w.env == env_view(env)
    &&& w.rts == rts@.map_values(|v: Vec<u8>| v@)
    &&& w.tr == tr@
    &&& w.lf == lf
}

/// Reads entity `k`: for an external parsed entity, asks the loader for
/// its text (`question`), and checks it (`bad`); parses its replacement
/// text as content.
fn ex_open(
    env: &XEnv,
    rts: &[Vec<u8>],
    pt: &[Tok],
    tr: &[(usize, Option<Vec<u8>>, Vec<u8>)],
    loader: &mut Loader,
    k: usize,
    Ghost(w): Ghost<World>,
) -> (r: Result<ERead, RErr>)
    requires
        args_ok(env, rts),
        fits(w, env, rts, pt, tr, load_model(old(loader))),
        k < env.ents@.len(),
    ensures
        load_model(final(loader)) == load_model(old(loader)),
        match r {
            Ok(e) => read_ok(w, k as int, e) && !bad(w, k as int),
            Err(RErr::Syntax) => bad(w, k as int),
            Err(RErr::Limit) => true,
        },
{
    let e = env.ents[k];
    proof {
        assert(env.ents@[k as int] == e);
        reveal(read_ok);
        reveal(bad);
        reveal(rt);
        reveal(tape_of);
        reveal(ext_rt);
    }
    if e.kind == 0 {
        let r = rts[k].as_slice();
        proof {
            assert(w.rts[k as int] == rts@[k as int]@);
            assert(rts@[k as int]@.len() <= MAX_POS);
        }
        slice_len_bound(r);
        let mut tape = Tape::new();
        let ok = ex_ent_content(r, &mut tape, env);
        return Ok(ERead { text: None, tape: if ok { Some(tape) } else { None } });
    }
    if e.kind != 1 {
        return Ok(ERead { text: None, tape: None });
    }
    let (base, sys, pubid) = match ex_question(env, pt, tr, k) {
        Some(q) => q,
        None => {
            return Ok(ERead { text: None, tape: None });
        },
    };
    if loader.count() >= MAX_EXT_ENTITIES {
        return Err(RErr::Limit);
    }
    let bytes = match loader.fetch(base, sys, pubid) {
        Some((b, _)) => b,
        None => {
            return Ok(ERead { text: None, tape: None });
        },
    };
    if loader.bytes() > MAX_EXT_BYTES {
        return Err(RErr::Limit);
    }
    let (t, q) = match ex_ext_text(bytes) {
        Some(x) => x,
        None => {
            return Err(RErr::Syntax);
        },
    };
    let mut r: Vec<u8> = Vec::new();
    ex_eol(t.as_slice(), q, t.len(), &mut r);
    proof {
        assert(r@ =~= eol(t@, q as int, t@.len() as int));
        lemma_eol_len(t@, q as int, t@.len() as int);
    }
    slice_len_bound(r.as_slice());
    let mut tape = Tape::new();
    if !ex_ent_content(r.as_slice(), &mut tape, env) {
        return Err(RErr::Syntax);
    }
    Ok(ERead { text: Some(r), tape: Some(tape) })
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Paths
// ---------------------------------------------------------------------------

proof fn lemma_path_push(w: World, p: Seq<int>, m: int)
    requires
        path(w, p),
        edge(w, p.last(), m),
    ensures
        path(w, p.push(m)),
{
    reveal(path);
    let q = p.push(m);
    assert forall|i: int| 0 <= i < q.len() - 1 implies edge(w, #[trigger] q[i], q[i + 1]) by {
        if i < p.len() - 1 {
            assert(q[i] == p[i] && q[i + 1] == p[i + 1]);
        } else {
            assert(q[i] == p.last() && q[i + 1] == m);
        }
    }
}

proof fn lemma_path_sub(w: World, p: Seq<int>, a: int, b: int)
    requires
        path(w, p),
        0 <= a < b <= p.len(),
    ensures
        path(w, p.subrange(a, b)),
{
    reveal(path);
    let q = p.subrange(a, b);
    assert forall|i: int| 0 <= i < q.len() - 1 implies edge(w, #[trigger] q[i], q[i + 1]) by {
        assert(q[i] == p[a + i] && q[i + 1] == p[a + i + 1]);
    }
}

/// Every entity on a path from a reference in the document is reachable.
proof fn lemma_path_reach(w: World, p: Seq<int>, i: int)
    requires
        path(w, p),
        root_ref(w, p[0]),
        0 <= i < p.len(),
    ensures
        reachable(w, p[i]),
{
    reveal(reachable);
    let q = p.subrange(0, i + 1);
    lemma_path_sub(w, p, 0, i + 1);
    assert(q[0] == p[0] && q.last() == p[i]);
    assert(path(w, q) && root_ref(w, q[0]) && q.last() == p[i]);
}

/// A reachable entity's successor is reachable.
proof fn lemma_reach_edge(w: World, k: int, m: int)
    requires
        reachable(w, k),
        edge(w, k, m),
    ensures
        reachable(w, m),
{
    reveal(reachable);
    let p = choose|p: Seq<int>| #[trigger] path(w, p) && root_ref(w, p[0]) && p.last() == k;
    assert(p.len() > 0) by {
        reveal(path);
    }
    lemma_path_push(w, p, m);
    assert(p.push(m)[0] == p[0]);
    assert(path(w, p.push(m)) && root_ref(w, p.push(m)[0]) && p.push(m).last() == m);
}

/// A path that ends where an entity on it is: a cycle.
proof fn lemma_cycle(w: World, p: Seq<int>, j: int, m: int)
    requires
        path(w, p),
        0 <= j < p.len(),
        p[j] == m,
        edge(w, p.last(), m),
    ensures
        on_cycle(w, m),
{
    lemma_path_sub(w, p, j, p.len() as int);
    let q = p.subrange(j, p.len() as int);
    assert(q.last() == p.last());
    lemma_path_push(w, q, m);
    let c = q.push(m);
    assert(c[0] == m && c.last() == m && c.len() >= 2);
    reveal(on_cycle);
    assert(path(w, c) && c.len() >= 2 && c[0] == m && c.last() == m);
}

// ---------------------------------------------------------------------------
// The walk's invariant
// ---------------------------------------------------------------------------

/// The entities on the stack.
pub open spec fn nodes(sk: Seq<(usize, usize)>) -> Seq<int> {
    sk.map_values(|f: (usize, usize)| f.0 as int)
}

/// What is left to read of the stack's entities: for termination.
pub open spec fn srem(w: World, sk: Seq<(usize, usize)>) -> int
    decreases sk.len(),
{
    if sk.len() == 0 {
        0
    } else {
        srem(w, sk.drop_last()) + (toks_of(w, sk.last().0 as int).len() - sk.last().1 + 1)
    }
}

proof fn lemma_srem_nonneg(w: World, sk: Seq<(usize, usize)>)
    requires
        forall|i: int| 0 <= i < sk.len() ==> (#[trigger] sk[i]).1 <= toks_of(w, sk[i].0 as int).len(),
    ensures
        srem(w, sk) >= 0,
    decreases sk.len(),
{
    if sk.len() > 0 {
        let d = sk.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).1 <= toks_of(w, d[i].0 as int).len() by {
            assert(d[i] == sk[i]);
        }
        lemma_srem_nonneg(w, d);
        assert(sk.last() == sk[sk.len() - 1]);
    }
}

/// A reference from the `i`th entity on the stack, read already: to a
/// black entity, or to the next one on the stack.
pub open spec fn ref_done(n: int, st: Seq<u8>, sk: Seq<(usize, usize)>, i: int, m: int) -> bool {
    (0 <= m < n && st[m] == 2) || (i + 1 < sk.len() && m == sk[i + 1].0)
}

/// The entities seen: what was read for each, which is right, and that
/// the document reaches it.
#[verifier::opaque]
pub open spec fn inv_rd(w: World, n: int, st: Seq<u8>, rd: Seq<Option<ERead>>) -> bool {
    &&& st.len() == n && rd.len() == n
    &&& forall|k: int| 0 <= k < n ==> #[trigger] st[k] <= 2
    &&& forall|k: int| 0 <= k < n ==> ((#[trigger] rd[k]) is Some) == (st[k] != 0)
    &&& forall|k: int| 0 <= k < n && (#[trigger] rd[k]) is Some ==> read_ok(w, k, rd[k]->0) && !bad(w, k)
    &&& forall|k: int| 0 <= k < n && #[trigger] st[k] != 0 ==> reachable(w, k)
}

/// The stack: the gray entities, each once, a path from the document.
#[verifier::opaque]
pub open spec fn inv_sk(w: World, n: int, st: Seq<u8>, sk: Seq<(usize, usize)>) -> bool {
    &&& forall|i: int|
        0 <= i < sk.len() ==> (#[trigger] sk[i]).0 < n && st[sk[i].0 as int] == 1 && sk[i].1 <= toks_of(
            w,
            sk[i].0 as int,
        ).len()
    &&& forall|i: int, j: int| 0 <= i < j < sk.len() ==> (#[trigger] sk[i]).0 != (#[trigger] sk[j]).0
    &&& forall|k: int| 0 <= k < n && #[trigger] st[k] == 1 ==> nodes(sk).contains(k)
    &&& sk.len() > 0 ==> path(w, nodes(sk)) && root_ref(w, sk[0].0 as int)
}

/// A gray entity's references read so far are to black ones, but for the
/// one being walked from it.
#[verifier::opaque]
pub open spec fn inv_ref(w: World, n: int, st: Seq<u8>, sk: Seq<(usize, usize)>) -> bool {
    forall|i: int, j: int|
        0 <= i < sk.len() && 0 <= j < sk[i].1 && (#[trigger] ref_in(w, sk[i].0 as int, j)) is Some ==> ref_done(
            n,
            st,
            sk,
            i,
            ref_in(w, sk[i].0 as int, j)->0,
        )
}

/// A black entity refers only to black ones, done before it.
#[verifier::opaque]
pub open spec fn inv_blk(w: World, n: int, st: Seq<u8>, fin: Seq<int>, cnt: int) -> bool {
    &&& forall|k: int| 0 <= k < n && #[trigger] st[k] == 2 ==> 0 <= fin[k] < cnt
    &&& forall|k: int, m: int|
        0 <= k < n && #[trigger] st[k] == 2 && #[trigger] edge(w, k, m) ==> 0 <= m < n && st[m] == 2 && fin[m] < fin[k]
}

/// The state of the walk: each entity is white (0, not seen), gray (1, on
/// the stack) or black (2, done); `fin` numbers the black ones in the
/// order they were done, below `cnt`.
pub open spec fn inv(
    w: World,
    n: int,
    st: Seq<u8>,
    rd: Seq<Option<ERead>>,
    sk: Seq<(usize, usize)>,
    fin: Seq<int>,
    cnt: int,
) -> bool {
    &&& 0 <= n <= usize::MAX
    &&& 0 <= cnt
    &&& fin.len() == n
    &&& inv_rd(w, n, st, rd)
    &&& inv_sk(w, n, st, sk)
    &&& inv_ref(w, n, st, sk)
    &&& inv_blk(w, n, st, fin, cnt)
}

/// The entities seen, as a set: for termination.
pub open spec fn seen(st: Seq<u8>) -> Set<int> {
    set_int_range(0, st.len() as int).filter(|k: int| st[k] != 0)
}

proof fn lemma_seen_finite(st: Seq<u8>)
    ensures
        seen(st).len() <= st.len(),
        forall|k: int| #[trigger] seen(st).contains(k) == (0 <= k < st.len() && st[k] != 0),
{
    let r = set_int_range(0, st.len() as int);
    lemma_int_range(0, st.len() as int);
    assert(seen(st).subset_of(r));
    lemma_len_subset(seen(st), r);
}

proof fn lemma_seen_add(st: Seq<u8>, k: int, v: u8)
    requires
        0 <= k < st.len(),
        st[k] == 0,
        v != 0,
    ensures
        seen(st.update(k, v)) == seen(st).insert(k),
        seen(st.update(k, v)).len() == seen(st).len() + 1,
{
    lemma_seen_finite(st);
    lemma_seen_finite(st.update(k, v));
    assert(seen(st.update(k, v)) =~= seen(st).insert(k));
    assert(!seen(st).contains(k));
}

proof fn lemma_seen_same(st: Seq<u8>, k: int, v: u8)
    requires
        0 <= k < st.len(),
        st[k] != 0,
        v != 0,
    ensures
        seen(st.update(k, v)) == seen(st),
{
    lemma_seen_finite(st);
    lemma_seen_finite(st.update(k, v));
    assert(seen(st.update(k, v)) =~= seen(st));
}

/// From references black at the end, every entity reached is black.
proof fn lemma_all_black(w: World, n: int, st: Seq<u8>, fin: Seq<int>, p: Seq<int>, i: int)
    requires
        st.len() == n,
        path(w, p),
        0 <= i < p.len(),
        root_ref(w, p[0]) ==> 0 <= p[0] < n && st[p[0]] == 2,
        root_ref(w, p[0]),
        forall|k: int, m: int|
            0 <= k < n && #[trigger] st[k] == 2 && #[trigger] edge(w, k, m) ==> 0 <= m < n && st[m] == 2 && fin[m] < fin[k],
    ensures
        0 <= p[i] < n && st[p[i]] == 2,
    decreases i,
{
    reveal(path);
    if i > 0 {
        lemma_all_black(w, n, st, fin, p, i - 1);
        assert(edge(w, p[i - 1], p[i]));
    }
}

/// Along a path of black entities, finishing numbers go down.
proof fn lemma_fin_down(w: World, n: int, st: Seq<u8>, fin: Seq<int>, p: Seq<int>, i: int)
    requires
        st.len() == n,
        path(w, p),
        1 <= i < p.len(),
        0 <= p[0] < n && st[p[0]] == 2,
        forall|k: int, m: int|
            0 <= k < n && #[trigger] st[k] == 2 && #[trigger] edge(w, k, m) ==> 0 <= m < n && st[m] == 2 && fin[m] < fin[k],
    ensures
        0 <= p[i] < n && st[p[i]] == 2,
        fin[p[i]] < fin[p[0]],
    decreases i,
{
    reveal(path);
    assert(edge(w, p[i - 1], p[i]));
    if i > 1 {
        lemma_fin_down(w, n, st, fin, p, i - 1);
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// The walk
// ---------------------------------------------------------------------------

/// A reference names an entity among the declared ones.
proof fn lemma_ref_range(w: World, n: int, x: Seq<u8>, tk: XTok)
    requires
        w.env.ents.len() == n,
    ensures
        ref_of(w, x, tk) matches Some(m) ==> 0 <= m < n,
{
    match tk {
        XTok::EntRef { start, end } => {
            if 0 <= start <= end <= x.len() {
                crate::index::lemma_find_first(w.env.ents, x.subrange(start, end));
            }
        },
        _ => {},
    }
}

/// `edge` from a reference read.
proof fn lemma_edge_of(w: World, k: int, j: int, m: int)
    requires
        0 <= j < toks_of(w, k).len(),
        ref_in(w, k, j) == Some(m),
    ensures
        edge(w, k, m),
{
    reveal(edge);
}

/// The entity the token `tk` in the text `x` refers to: `ref_of`.
fn ex_ref_of(env: &XEnv, x: &[u8], tk: Tok, Ghost(w): Ghost<World>) -> (r: Option<usize>)
    requires
        env_wf(env),
        w.env == env_view(env),
    ensures
        same(r, ref_of(w, x@, tk@)),
        r matches Some(m) ==> m < env.ents@.len(),
{
    match tk.kind {
        Kind::EntRef => {},
        _ => {
            return None;
        },
    }
    let a = tk.a48();
    let b = tk.b48();
    if !(a <= b && b <= x.len() as u64) {
        return None;
    }
    let n = env.ents.len();
    let r = ex_find_ent(env, n, x, a as usize, b as usize);
    proof {
        assert(lim_view(env, n as int).ents =~= env_view(env).ents);
    }
    r
}

/// The replacement text of `k` as read (`rt`, empty if unknown).
fn ex_text<'a>(env: &XEnv, rts: &'a [Vec<u8>], rd: &'a Vec<Option<ERead>>, k: usize, Ghost(w): Ghost<World>) -> (r: &'a [u8])
    requires
        args_ok(env, rts),
        w.ents == env.ents@,
        w.rts == rts@.map_values(|v: Vec<u8>| v@),
        k < env.ents@.len(),
        k < rd@.len(),
        rd@[k as int] is Some,
        read_ok(w, k as int, rd@[k as int]->0),
    ensures
        r@ == match rt(w, k as int) {
            Some(x) => x,
            None => Seq::empty(),
        },
{
    proof {
        reveal(read_ok);
        reveal(rt);
    }
    if env.ents[k].kind == 0 {
        proof {
            assert(w.rts[k as int] == rts@[k as int]@);
        }
        return rts[k].as_slice();
    }
    match &rd[k] {
        Some(e) => match &e.text {
            Some(t) => t.as_slice(),
            None => &[],
        },
        None => &[],
    }
}

/// How many tokens `k`'s replacement text has: `toks_of(w, k).len()`.
fn ex_ntoks(rd: &Vec<Option<ERead>>, k: usize, Ghost(w): Ghost<World>) -> (r: usize)
    requires
        k < rd@.len(),
        rd@[k as int] is Some,
        read_ok(w, k as int, rd@[k as int]->0),
    ensures
        r == toks_of(w, k as int).len(),
{
    proof {
        reveal(read_ok);
        reveal(toks_of);
    }
    match &rd[k] {
        Some(e) => match &e.tape {
            Some(t) => t.toks.len(),
            None => 0,
        },
        None => 0,
    }
}

/// `ref_in(w, k, j)`.
fn ex_ref_at(env: &XEnv, rts: &[Vec<u8>], rd: &Vec<Option<ERead>>, k: usize, j: usize, Ghost(w): Ghost<World>) -> (r: Option<
    usize,
>)
    requires
        args_ok(env, rts),
        w.ents == env.ents@,
        w.env == env_view(env),
        w.rts == rts@.map_values(|v: Vec<u8>| v@),
        k < env.ents@.len(),
        k < rd@.len(),
        rd@[k as int] is Some,
        read_ok(w, k as int, rd@[k as int]->0),
        j < toks_of(w, k as int).len(),
    ensures
        same(r, ref_in(w, k as int, j as int)),
        r matches Some(m) ==> m < env.ents@.len(),
{
    let x = ex_text(env, rts, rd, k, Ghost(w));
    proof {
        reveal(read_ok);
        reveal(toks_of);
        reveal(ref_in);
    }
    let tk = match &rd[k] {
        Some(e) => match &e.tape {
            Some(t) => t.toks[j],
            None => {
                return None;
            },
        },
        None => {
            return None;
        },
    };
    proof {
        let t = rd@[k as int]->0.tape->0;
        assert(t@ == t.toks@.map_values(|u: Tok| u@));
        assert(toks_of(w, k as int)[j as int] == tk@);
    }
    ex_ref_of(env, x, tk, Ghost(w))
}

/// Reads, with `loader`, each external parsed entity the document's
/// content refers to (from the root element on, in the document or in the
/// replacement text of an entity it refers to), and checks that each is
/// well-formed and that none refers to itself. On an error, the index of
/// the document's token whose reference led to it.
pub fn ex_read_external(
    env: &XEnv,
    rts: &[Vec<u8>],
    pt: &[Tok],
    tr: &[(usize, Option<Vec<u8>>, Vec<u8>)],
    loader: &mut Loader,
    doc: &[u8],
    dt: &[Tok],
    root: usize,
) -> (r: Result<Vec<Option<ERead>>, (RErr, usize)>)
    requires
        args_ok(env, rts),
    ensures
        load_model(final(loader)) == load_model(old(loader)),
        ({
        let w = world(env, rts, pt, tr, load_model(old(loader)), doc, dt, root);
        match r {
            Ok(rd) => {
                &&& rd@.len() == env.ents@.len()
                &&& forall|k: int| 0 <= k < rd@.len() ==> ((#[trigger] rd@[k]) is Some) == reachable(w, k)
                &&& forall|k: int| 0 <= k < rd@.len() && (#[trigger] rd@[k]) is Some ==> read_ok(w, k, rd@[k]->0)
                &&& forall|k: int| #[trigger] reachable(w, k) ==> 0 <= k < rd@.len() && !bad(w, k) && !on_cycle(w, k)
            },
            Err((RErr::Syntax, i)) => i < dt@.len() && exists|k: int| #[trigger] reachable(w, k) && (bad(w, k) || on_cycle(w, k)),
            Err((RErr::Limit, i)) => i < dt@.len(),
        }
        }),
{
    let ghost w = world(env, rts, pt, tr, load_model(loader), doc, dt, root);
    walk(env, rts, pt, tr, loader, doc, dt, root, Ghost(w))
}

/// `ex_read_external`, for the world `w`.
fn walk(
    env: &XEnv,
    rts: &[Vec<u8>],
    pt: &[Tok],
    tr: &[(usize, Option<Vec<u8>>, Vec<u8>)],
    loader: &mut Loader,
    doc: &[u8],
    dt: &[Tok],
    root: usize,
    Ghost(w): Ghost<World>,
) -> (r: Result<Vec<Option<ERead>>, (RErr, usize)>)
    requires
        args_ok(env, rts),
        fits(w, env, rts, pt, tr, load_model(old(loader))),
        w.doc == doc@,
        w.dt == dt@,
        w.root == root,
    ensures
        load_model(final(loader)) == load_model(old(loader)),
        match r {
            Ok(rd) => {
                &&& rd@.len() == env.ents@.len()
                &&& forall|k: int| 0 <= k < rd@.len() ==> ((#[trigger] rd@[k]) is Some) == reachable(w, k)
                &&& forall|k: int| 0 <= k < rd@.len() && (#[trigger] rd@[k]) is Some ==> read_ok(w, k, rd@[k]->0)
                &&& forall|k: int| #[trigger] reachable(w, k) ==> 0 <= k < rd@.len() && !bad(w, k) && !on_cycle(w, k)
            },
            Err((RErr::Syntax, i)) => i < dt@.len() && exists|k: int| #[trigger] reachable(w, k) && (bad(w, k) || on_cycle(w, k)),
            Err((RErr::Limit, i)) => i < dt@.len(),
        },
{
    let n = env.ents.len();
    let mut st: Vec<u8> = Vec::new();
    let mut rd: Vec<Option<ERead>> = Vec::new();
    while st.len() < n
        invariant
            st@.len() <= n,
            rd@.len() == st@.len(),
            forall|k: int| 0 <= k < st@.len() ==> #[trigger] st@[k] == 0,
            forall|k: int| 0 <= k < rd@.len() ==> (#[trigger] rd@[k]) is None,
        decreases n - st@.len(),
    {
        st.push(0);
        rd.push(None);
    }
    let ghost mut fin: Seq<int> = Seq::new(n as nat, |k: int| 0int);
    let ghost mut cnt: int = 0;
    let mut sk: Vec<(usize, usize)> = Vec::new();
    proof {
        assert(nodes(sk@) =~= Seq::<int>::empty());
        assert(w.env.ents.len() == n);
        reveal(inv_rd);
        reveal(inv_sk);
        reveal(inv_ref);
        reveal(inv_blk);
    }
    let mut i = root;
    while i < dt.len()
        invariant
            root <= i,
            n == env.ents@.len(),
            args_ok(env, rts),
            fits(w, env, rts, pt, tr, load_model(loader)),
            w.lf == load_model(old(loader)),
            w.doc == doc@,
            w.dt == dt@,
            w.root == root,
            w.env.ents.len() == n,
            inv(w, n as int, st@, rd@, sk@, fin, cnt),
            sk@.len() == 0,
            forall|j: int|
                root <= j < i && (#[trigger] ref_of(w, doc@, dt@[j]@)) is Some ==> st@[ref_of(w, doc@, dt@[j]@)->0] == 2,
        decreases dt@.len() - i,
    {
        let tk = dt[i];
        proof {
            assert(dt@[i as int] == tk);
            lemma_ref_range(w, n as int, doc@, tk@);
        }
        if let Some(m) = ex_ref_of(env, doc, tk, Ghost(w)) {
            proof {
                assert(sk@ =~= Seq::<(usize, usize)>::empty());
                lemma_no_gray(w, n as int, st@, rd@, fin, cnt);
            }
            if st[m] == 0 {
                proof {
                    lemma_root_start(w, i as int, m as int);
                }
                let e = match ex_open(env, rts, pt, tr, loader, m, Ghost(w)) {
                    Ok(e) => e,
                    Err(x) => {
                        return Err((x, i));
                    },
                };
                let ghost st0 = st@;
                let ghost rd0 = rd@;
                proof {
                    assert(sk@ =~= Seq::<(usize, usize)>::empty());
                }
                st.set(m, 1);
                rd.set(m, Some(e));
                sk.push((m, 0));
                proof {
                    assert(sk@ =~= seq![(m, 0usize)]);
                    lemma_open_root(w, n as int, st0, rd0, st@, rd@, sk@, fin, cnt, m as int);
                }
                // Depth first from m.
                while sk.len() > 0
                    invariant
                        n == env.ents@.len(),
                        args_ok(env, rts),
                        fits(w, env, rts, pt, tr, load_model(loader)),
                        w.lf == load_model(old(loader)),
                        w.doc == doc@,
                        w.dt == dt@,
                        w.root == root,
                        w.env.ents.len() == n,
                        inv(w, n as int, st@, rd@, sk@, fin, cnt),
                        m < n,
                        st@[m as int] != 0,
                        root <= i < dt@.len(),
                        forall|j: int|
                            root <= j < i && (#[trigger] ref_of(w, doc@, dt@[j]@)) is Some ==> st@[ref_of(w, doc@, dt@[j]@)->0]
                                == 2,
                    decreases n - seen(st@).len(), srem(w, sk@),
                {
                    let top = sk.len() - 1;
                    let (u, pos) = sk[top];
                    proof {
                        assert(sk@[top as int] == (u, pos));
                        assert(sk@.last() == (u, pos));
                        lemma_top(w, n as int, st@, rd@, sk@, fin, cnt);
                    }
                    let len = ex_ntoks(&rd, u, Ghost(w));
                    let ghost st0 = st@;
                    let ghost sk0 = sk@;
                    let ghost fin0 = fin;
                    let ghost cnt0 = cnt;
                    if pos >= len {
                        // Every reference of u is to a black entity: u is done.
                        sk.pop();
                        st.set(u, 2);
                        proof {
                            fin = fin.update(u as int, cnt);
                            cnt = cnt + 1;
                            lemma_pop(w, n as int, st0, rd@, sk0, fin0, cnt0, st@, sk@, fin, cnt);
                            lemma_seen_same(st0, u as int, 2);
                            lemma_srem_pop(w, sk0);
                            assert(sk@ == sk0.drop_last());
                            assert(seen(st@).len() == seen(st0).len());
                            assert(srem(w, sk@) < srem(w, sk0));
                        }
                    } else {
                        sk.set(top, (u, pos + 1));
                        proof {
                            assert(sk@ == sk0.update(sk0.len() - 1, (sk0.last().0, (sk0.last().1 + 1) as usize)));
                            lemma_srem_step(w, sk0, sk@);
                            assert(srem(w, sk@) < srem(w, sk0));
                        }
                        match ex_ref_at(env, rts, &rd, u, pos, Ghost(w)) {
                            None => {
                                proof {
                                    lemma_step(w, n as int, st@, rd@, sk0, sk@, fin, cnt);
                                    assert(st@ == st0);
                                }
                            },
                            Some(v) => {
                                proof {
                                    lemma_edge_of(w, u as int, pos as int, v as int);
                                }
                                if st[v] == 1 {
                                    // A reference back to the stack: a cycle.
                                    proof {
                                        lemma_back(w, n as int, st@, rd@, sk0, fin, cnt, v as int);
                                    }
                                    return Err((RErr::Syntax, i));
                                }
                                if st[v] == 0 {
                                    proof {
                                        assert(reachable(w, u as int));
                                        lemma_reach_edge(w, u as int, v as int);
                                    }
                                    let e = match ex_open(env, rts, pt, tr, loader, v, Ghost(w)) {
                                        Ok(e) => e,
                                        Err(x) => {
                                            return Err((x, i));
                                        },
                                    };
                                    let ghost st1 = st@;
                                    let ghost rd1 = rd@;
                                    let ghost sk1 = sk@;
                                    st.set(v, 1);
                                    rd.set(v, Some(e));
                                    sk.push((v, 0));
                                    proof {
                                        lemma_push(w, n as int, st1, rd1, sk0, sk1, fin, cnt, st@, rd@, sk@, v as int);
                                        lemma_seen_add(st1, v as int, 1);
                                        assert(st1 == st0);
                                        assert(seen(st@).len() == seen(st0).len() + 1);
                                    }
                                } else {
                                    proof {
                                        lemma_step(w, n as int, st@, rd@, sk0, sk@, fin, cnt);
                                        assert(st@ == st0);
                                    }
                                }
                            },
                        }
                    }
                    proof {
                        lemma_seen_finite(st@);
                        lemma_inv_srem(w, n as int, st@, rd@, sk@, fin, cnt);
                    }
                }
                proof {
                    assert(sk@ =~= Seq::<(usize, usize)>::empty());
                    lemma_no_gray(w, n as int, st@, rd@, fin, cnt);
                }
            }
        }
        proof {
            assert forall|j: int|
                root <= j < i + 1 && (#[trigger] ref_of(w, doc@, dt@[j]@)) is Some implies st@[ref_of(w, doc@, dt@[j]@)->0]
                == 2 by {
                if j == i {
                    assert(dt@[j] == tk);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(sk@ =~= Seq::<(usize, usize)>::empty());
        lemma_done(w, n as int, st@, rd@, fin, cnt);
    }
    Ok(rd)
}

} // verus!

verus! {


// ---------------------------------------------------------------------------
// The walk's steps keep its invariant
// ---------------------------------------------------------------------------

proof fn lemma_nodes_index(sk: Seq<(usize, usize)>, i: int)
    requires
        0 <= i < sk.len(),
    ensures
        nodes(sk)[i] == sk[i].0 as int,
        nodes(sk).len() == sk.len(),
{
}

/// The top of the stack.
proof fn lemma_top(
    w: World,
    n: int,
    st: Seq<u8>,
    rd: Seq<Option<ERead>>,
    sk: Seq<(usize, usize)>,
    fin: Seq<int>,
    cnt: int,
)
    requires
        inv(w, n, st, rd, sk, fin, cnt),
        sk.len() > 0,
    ensures
        sk.last().0 < n,
        st[sk.last().0 as int] == 1,
        sk.last().1 <= toks_of(w, sk.last().0 as int).len(),
        rd[sk.last().0 as int] is Some,
        read_ok(w, sk.last().0 as int, rd[sk.last().0 as int]->0),
        reachable(w, sk.last().0 as int),
        st.len() == n,
        rd.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] st[k] <= 2,
        srem(w, sk) >= 0,
        n - seen(st).len() >= 0,
{
    reveal(inv_sk);
    reveal(inv_rd);
    lemma_srem_nonneg(w, sk);
    lemma_seen_finite(st);
    let t = sk.len() - 1;
    assert(sk[t] == sk.last());
    assert(sk[t].0 < n);
    assert(st[sk[t].0 as int] == 1);
    assert(rd[sk[t].0 as int] is Some);
}

/// What is left to read is not negative.
proof fn lemma_inv_srem(
    w: World,
    n: int,
    st: Seq<u8>,
    rd: Seq<Option<ERead>>,
    sk: Seq<(usize, usize)>,
    fin: Seq<int>,
    cnt: int,
)
    requires
        inv(w, n, st, rd, sk, fin, cnt),
    ensures
        srem(w, sk) >= 0,
{
    reveal(inv_sk);
    lemma_srem_nonneg(w, sk);
}

/// With the stack empty, nothing is gray.
proof fn lemma_no_gray(w: World, n: int, st: Seq<u8>, rd: Seq<Option<ERead>>, fin: Seq<int>, cnt: int)
    requires
        inv(w, n, st, rd, Seq::empty(), fin, cnt),
    ensures
        st.len() == n,
        rd.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] st[k] <= 2 && st[k] != 1,
{
    reveal(inv_sk);
    reveal(inv_rd);
    assert(nodes(Seq::<(usize, usize)>::empty()) =~= Seq::<int>::empty());
    assert forall|k: int| 0 <= k < n implies #[trigger] st[k] <= 2 && st[k] != 1 by {
        if st[k] == 1 {
            assert(nodes(Seq::<(usize, usize)>::empty()).contains(k));
        }
    }
}

/// A reference in the document starts a path.
proof fn lemma_root_start(w: World, j: int, m: int)
    requires
        w.root <= j < w.dt.len(),
        ref_of(w, w.doc, w.dt[j]@) == Some(m),
    ensures
        root_ref(w, m),
        reachable(w, m),
        path(w, seq![m]),
{
    reveal(root_ref);
    reveal(path);
    reveal(reachable);
    let p = seq![m];
    assert(p[0] == m && p.last() == m);
    assert(path(w, p) && root_ref(w, p[0]) && p.last() == m);
}

/// The walk starts from `m`, referred to by the document.
proof fn lemma_open_root(
    w: World,
    n: int,
    st0: Seq<u8>,
    rd0: Seq<Option<ERead>>,
    st: Seq<u8>,
    rd: Seq<Option<ERead>>,
    sk: Seq<(usize, usize)>,
    fin: Seq<int>,
    cnt: int,
    m: int,
)
    requires
        inv(w, n, st0, rd0, Seq::empty(), fin, cnt),
        0 <= m < n,
        st0[m] == 0,
        st == st0.update(m, 1),
        rd.len() == rd0.len(),
        forall|k: int| 0 <= k < rd.len() && k != m ==> rd[k] == rd0[k],
        rd[m] is Some,
        read_ok(w, m, rd[m]->0),
        !bad(w, m),
        reachable(w, m),
        root_ref(w, m),
        path(w, seq![m]),
        sk == seq![(m as usize, 0usize)],
    ensures
        inv(w, n, st, rd, sk, fin, cnt),
{
    lemma_no_gray(w, n, st0, rd0, fin, cnt);
    assert(inv_rd(w, n, st, rd)) by {
        reveal(inv_rd);
        assert forall|k: int| 0 <= k < n implies #[trigger] st[k] <= 2 by {
            assert(st0[k] <= 2);
        }
        assert forall|k: int| 0 <= k < n implies ((#[trigger] rd[k]) is Some) == (st[k] != 0) by {
            if k != m {
                assert(rd[k] == rd0[k]);
            }
        }
        assert forall|k: int| 0 <= k < n && (#[trigger] rd[k]) is Some implies read_ok(w, k, rd[k]->0) && !bad(w, k) by {
            if k != m {
                assert(rd[k] == rd0[k]);
            }
        }
        assert forall|k: int| 0 <= k < n && #[trigger] st[k] != 0 implies reachable(w, k) by {
            if k != m {
                assert(st0[k] != 0);
            }
        }
    }
    assert(inv_sk(w, n, st, sk)) by {
        reveal(inv_sk);
        assert(nodes(sk) =~= seq![m]);
        assert(sk[0] == (m as usize, 0usize));
        assert(toks_of(w, m).len() >= 0);
        assert forall|k: int| 0 <= k < n && #[trigger] st[k] == 1 implies nodes(sk).contains(k) by {
            if k != m {
                assert(st0[k] == 1);
            } else {
                assert(nodes(sk)[0] == m);
            }
        }
    }
    assert(inv_ref(w, n, st, sk)) by {
        reveal(inv_ref);
    }
    assert(inv_blk(w, n, st, fin, cnt)) by {
        reveal(inv_blk);
        assert forall|k: int| 0 <= k < n && #[trigger] st[k] == 2 implies 0 <= fin[k] < cnt by {
            assert(st0[k] == 2);
        }
        assert forall|k: int, x: int| 0 <= k < n && #[trigger] st[k] == 2 && #[trigger] edge(w, k, x) implies 0 <= x < n
            && st[x] == 2 && fin[x] < fin[k] by {
            assert(st0[k] == 2);
        }
    }
}

/// `u`, on top, is done: black, numbered `cnt`.
proof fn lemma_pop(
    w: World,
    n: int,
    st0: Seq<u8>,
    rd: Seq<Option<ERead>>,
    sk0: Seq<(usize, usize)>,
    fin0: Seq<int>,
    cnt0: int,
    st: Seq<u8>,
    sk: Seq<(usize, usize)>,
    fin: Seq<int>,
    cnt: int,
)
    requires
        inv(w, n, st0, rd, sk0, fin0, cnt0),
        sk0.len() > 0,
        sk0.last().1 >= toks_of(w, sk0.last().0 as int).len(),
        st == st0.update(sk0.last().0 as int, 2),
        sk == sk0.drop_last(),
        fin == fin0.update(sk0.last().0 as int, cnt0),
        cnt == cnt0 + 1,
    ensures
        inv(w, n, st, rd, sk, fin, cnt),
{
    lemma_top(w, n, st0, rd, sk0, fin0, cnt0);
    let t = sk0.len() - 1;
    let u = sk0[t].0 as int;
    assert(sk0.last() == sk0[t]);
    lemma_pop_rd(w, n, st0, rd, u, st);
    lemma_pop_sk(w, n, st0, sk0, st, sk);
    lemma_pop_ref(w, n, st0, sk0, st, sk);
    lemma_pop_blk(w, n, st0, sk0, fin0, cnt0, st, fin, cnt);
}

proof fn lemma_pop_rd(w: World, n: int, st0: Seq<u8>, rd: Seq<Option<ERead>>, u: int, st: Seq<u8>)
    requires
        inv_rd(w, n, st0, rd),
        0 <= u < n,
        st0[u] == 1,
        st == st0.update(u, 2),
    ensures
        inv_rd(w, n, st, rd),
{
    reveal(inv_rd);
    assert forall|k: int| 0 <= k < n implies #[trigger] st[k] <= 2 by {
        if k != u {
            assert(st0[k] <= 2);
        }
    }
    assert forall|k: int| 0 <= k < n implies ((#[trigger] rd[k]) is Some) == (st[k] != 0) by {
        if k != u {
            assert(st[k] == st0[k]);
        }
    }
    assert forall|k: int| 0 <= k < n && #[trigger] st[k] != 0 implies reachable(w, k) by {
        assert(st0[k] != 0);
    }
}

proof fn lemma_pop_sk(w: World, n: int, st0: Seq<u8>, sk0: Seq<(usize, usize)>, st: Seq<u8>, sk: Seq<(usize, usize)>)
    requires
        inv_sk(w, n, st0, sk0),
        st0.len() == n,
        sk0.len() > 0,
        st == st0.update(sk0.last().0 as int, 2),
        sk == sk0.drop_last(),
    ensures
        inv_sk(w, n, st, sk),
{
    reveal(inv_sk);
    let t = sk0.len() - 1;
    let u = sk0[t].0 as int;
    assert(sk0.last() == sk0[t]);
    assert(nodes(sk) =~= nodes(sk0).subrange(0, t));
    assert forall|i: int|
        0 <= i < sk.len() implies (#[trigger] sk[i]).0 < n && st[sk[i].0 as int] == 1 && sk[i].1 <= toks_of(
        w,
        sk[i].0 as int,
    ).len() by {
        assert(sk[i] == sk0[i]);
        assert(sk0[i].0 != sk0[t].0);
    }
    assert forall|i: int, j: int| 0 <= i < j < sk.len() implies (#[trigger] sk[i]).0 != (#[trigger] sk[j]).0 by {
        assert(sk[i] == sk0[i] && sk[j] == sk0[j]);
    }
    assert forall|k: int| 0 <= k < n && #[trigger] st[k] == 1 implies nodes(sk).contains(k) by {
        assert(k != u);
        assert(st0[k] == 1);
        assert(nodes(sk0).contains(k));
        let x = choose|x: int| 0 <= x < nodes(sk0).len() && nodes(sk0)[x] == k;
        lemma_nodes_index(sk0, x);
        if x == t {
            assert(nodes(sk0)[t] == u);
        }
        assert(nodes(sk)[x] == k);
    }
    if sk.len() > 0 {
        lemma_path_sub(w, nodes(sk0), 0, t);
        assert(sk[0] == sk0[0]);
    }
}

proof fn lemma_pop_ref(w: World, n: int, st0: Seq<u8>, sk0: Seq<(usize, usize)>, st: Seq<u8>, sk: Seq<(usize, usize)>)
    requires
        inv_ref(w, n, st0, sk0),
        st0.len() == n,
        sk0.len() > 0,
        sk0.last().0 < n,
        st0[sk0.last().0 as int] == 1,
        st == st0.update(sk0.last().0 as int, 2),
        sk == sk0.drop_last(),
    ensures
        inv_ref(w, n, st, sk),
{
    reveal(inv_ref);
    let t = sk0.len() - 1;
    let u = sk0[t].0 as int;
    assert(sk0.last() == sk0[t]);
    assert forall|i: int, j: int|
        0 <= i < sk.len() && 0 <= j < sk[i].1 && (#[trigger] ref_in(w, sk[i].0 as int, j)) is Some implies ref_done(
        n,
        st,
        sk,
        i,
        ref_in(w, sk[i].0 as int, j)->0,
    ) by {
        assert(sk[i] == sk0[i]);
        let x = ref_in(w, sk[i].0 as int, j)->0;
        assert(ref_in(w, sk0[i].0 as int, j) is Some);
        assert(ref_done(n, st0, sk0, i, x));
        if 0 <= x < n && st0[x] == 2 {
        } else {
            assert(x == sk0[i + 1].0);
            if i + 1 < t {
                assert(sk[i + 1] == sk0[i + 1]);
            } else {
                assert(x == u);
            }
        }
    }
}

proof fn lemma_pop_blk(
    w: World,
    n: int,
    st0: Seq<u8>,
    sk0: Seq<(usize, usize)>,
    fin0: Seq<int>,
    cnt0: int,
    st: Seq<u8>,
    fin: Seq<int>,
    cnt: int,
)
    requires
        inv_blk(w, n, st0, fin0, cnt0),
        inv_ref(w, n, st0, sk0),
        0 <= cnt0,
        st0.len() == n,
        fin0.len() == n,
        sk0.len() > 0,
        sk0.last().0 < n,
        st0[sk0.last().0 as int] == 1,
        sk0.last().1 >= toks_of(w, sk0.last().0 as int).len(),
        st == st0.update(sk0.last().0 as int, 2),
        fin == fin0.update(sk0.last().0 as int, cnt0),
        cnt == cnt0 + 1,
    ensures
        inv_blk(w, n, st, fin, cnt),
{
    reveal(inv_blk);
    let t = sk0.len() - 1;
    let u = sk0[t].0 as int;
    assert(sk0.last() == sk0[t]);
    assert(fin[u] == cnt0);
    assert forall|k: int| 0 <= k < n && #[trigger] st[k] == 2 implies 0 <= fin[k] < cnt by {
        if k != u {
            assert(st0[k] == 2);
            assert(fin[k] == fin0[k]);
        }
    }
    assert forall|k: int, x: int| 0 <= k < n && #[trigger] st[k] == 2 && #[trigger] edge(w, k, x) implies 0 <= x < n && st[x]
        == 2 && fin[x] < fin[k] by {
        if k == u {
            reveal(edge);
            reveal(inv_ref);
            let j = choose|j: int| 0 <= j < toks_of(w, k).len() && #[trigger] ref_in(w, k, j) == Some(x);
            assert(ref_in(w, sk0[t].0 as int, j) == Some(x));
            assert(ref_done(n, st0, sk0, t, x));
            assert(st0[x] == 2);
            assert(x != u);
        } else {
            assert(st0[k] == 2);
            assert(st0[x] == 2);
            assert(x != u);
        }
    }
}

proof fn lemma_srem_pop(w: World, sk0: Seq<(usize, usize)>)
    requires
        sk0.len() > 0,
        sk0.last().1 <= toks_of(w, sk0.last().0 as int).len(),
    ensures
        srem(w, sk0.drop_last()) < srem(w, sk0),
{
}

proof fn lemma_srem_step(w: World, sk0: Seq<(usize, usize)>, sk: Seq<(usize, usize)>)
    requires
        sk0.len() > 0,
        sk == sk0.update(sk0.len() - 1, (sk0.last().0, (sk0.last().1 + 1) as usize)),
        sk0.last().1 + 1 <= usize::MAX,
    ensures
        srem(w, sk) == srem(w, sk0) - 1,
{
    assert(sk.drop_last() =~= sk0.drop_last());
    assert(sk.last() == (sk0.last().0, (sk0.last().1 + 1) as usize));
}

/// Reading a reference of `u` that is to no entity, or to a black one.
proof fn lemma_step(
    w: World,
    n: int,
    st: Seq<u8>,
    rd: Seq<Option<ERead>>,
    sk0: Seq<(usize, usize)>,
    sk: Seq<(usize, usize)>,
    fin: Seq<int>,
    cnt: int,
)
    requires
        inv(w, n, st, rd, sk0, fin, cnt),
        sk0.len() > 0,
        sk0.last().1 < toks_of(w, sk0.last().0 as int).len(),
        sk == sk0.update(sk0.len() - 1, (sk0.last().0, (sk0.last().1 + 1) as usize)),
        match ref_in(w, sk0.last().0 as int, sk0.last().1 as int) {
            Some(v) => 0 <= v < n && st[v] == 2,
            None => true,
        },
    ensures
        inv(w, n, st, rd, sk, fin, cnt),
{
    let t = sk0.len() - 1;
    assert(sk0.last() == sk0[t]);
    assert(nodes(sk) =~= nodes(sk0));
    assert(inv_sk(w, n, st, sk)) by {
        reveal(inv_sk);
        assert forall|i: int|
            0 <= i < sk.len() implies (#[trigger] sk[i]).0 < n && st[sk[i].0 as int] == 1 && sk[i].1 <= toks_of(
            w,
            sk[i].0 as int,
        ).len() by {
            if i != t {
                assert(sk[i] == sk0[i]);
            }
        }
        assert forall|i: int, j: int| 0 <= i < j < sk.len() implies (#[trigger] sk[i]).0 != (#[trigger] sk[j]).0 by {
            assert(sk[i].0 == sk0[i].0 && sk[j].0 == sk0[j].0);
        }
        if sk.len() > 0 {
            assert(sk[0].0 == sk0[0].0);
        }
    }
    assert(inv_ref(w, n, st, sk)) by {
        reveal(inv_ref);
        assert forall|i: int, j: int|
            0 <= i < sk.len() && 0 <= j < sk[i].1 && (#[trigger] ref_in(w, sk[i].0 as int, j)) is Some implies ref_done(
            n,
            st,
            sk,
            i,
            ref_in(w, sk[i].0 as int, j)->0,
        ) by {
            if i != t {
                assert(sk[i] == sk0[i]);
                assert(ref_in(w, sk0[i].0 as int, j) is Some);
                if i + 1 < sk.len() {
                    assert(sk[i + 1].0 == sk0[i + 1].0);
                }
            } else if j < sk0[t].1 {
                assert(ref_in(w, sk0[t].0 as int, j) is Some);
            }
        }
    }
}

/// A reference from the top of the stack back to an entity on it closes a
/// cycle, through entities the document reaches.
proof fn lemma_back(
    w: World,
    n: int,
    st: Seq<u8>,
    rd: Seq<Option<ERead>>,
    sk0: Seq<(usize, usize)>,
    fin: Seq<int>,
    cnt: int,
    v: int,
)
    requires
        inv(w, n, st, rd, sk0, fin, cnt),
        sk0.len() > 0,
        edge(w, sk0.last().0 as int, v),
        0 <= v < n,
        st[v] == 1,
    ensures
        exists|k: int| #[trigger] reachable(w, k) && (bad(w, k) || on_cycle(w, k)),
{
    reveal(inv_sk);
    reveal(inv_rd);
    let p = nodes(sk0);
    assert(p.contains(v));
    let j = choose|j: int| 0 <= j < p.len() && p[j] == v;
    assert(p.last() == sk0.last().0 as int) by {
        lemma_nodes_index(sk0, sk0.len() - 1);
    }
    lemma_cycle(w, p, j, v);
    assert(reachable(w, v));
}

/// Opening `v`, the target of the reference just read from `u`, on top:
/// gray, pushed.
proof fn lemma_push(
    w: World,
    n: int,
    st1: Seq<u8>,
    rd1: Seq<Option<ERead>>,
    sk0: Seq<(usize, usize)>,
    sk1: Seq<(usize, usize)>,
    fin: Seq<int>,
    cnt: int,
    st: Seq<u8>,
    rd: Seq<Option<ERead>>,
    sk: Seq<(usize, usize)>,
    v: int,
)
    requires
        inv(w, n, st1, rd1, sk0, fin, cnt),
        sk0.len() > 0,
        sk0.last().1 < toks_of(w, sk0.last().0 as int).len(),
        sk1 == sk0.update(sk0.len() - 1, (sk0.last().0, (sk0.last().1 + 1) as usize)),
        ref_in(w, sk0.last().0 as int, sk0.last().1 as int) == Some(v),
        0 <= v < n,
        st1[v] == 0,
        reachable(w, v),
        st == st1.update(v, 1),
        rd.len() == rd1.len(),
        forall|k: int| 0 <= k < rd.len() && k != v ==> rd[k] == rd1[k],
        rd[v] is Some,
        read_ok(w, v, rd[v]->0),
        !bad(w, v),
        sk == sk1.push((v as usize, 0usize)),
    ensures
        inv(w, n, st, rd, sk, fin, cnt),
{
    lemma_top(w, n, st1, rd1, sk0, fin, cnt);
    let t = sk0.len() - 1;
    assert(sk0.last() == sk0[t]);
    lemma_push_rd(w, n, st1, rd1, st, rd, v);
    lemma_push_sk(w, n, st1, sk0, sk1, st, sk, v);
    lemma_push_ref(w, n, st1, sk0, sk1, st, sk, v);
    assert(inv_blk(w, n, st, fin, cnt)) by {
        reveal(inv_blk);
        assert forall|k: int| 0 <= k < n && #[trigger] st[k] == 2 implies 0 <= fin[k] < cnt by {
            assert(st1[k] == 2);
        }
        assert forall|k: int, x: int| 0 <= k < n && #[trigger] st[k] == 2 && #[trigger] edge(w, k, x) implies 0 <= x < n
            && st[x] == 2 && fin[x] < fin[k] by {
            assert(st1[k] == 2);
            assert(st1[x] == 2);
        }
    }
}

proof fn lemma_push_rd(w: World, n: int, st1: Seq<u8>, rd1: Seq<Option<ERead>>, st: Seq<u8>, rd: Seq<Option<ERead>>, v: int)
    requires
        inv_rd(w, n, st1, rd1),
        0 <= v < n,
        st1[v] == 0,
        reachable(w, v),
        st == st1.update(v, 1),
        rd.len() == rd1.len(),
        forall|k: int| 0 <= k < rd.len() && k != v ==> rd[k] == rd1[k],
        rd[v] is Some,
        read_ok(w, v, rd[v]->0),
        !bad(w, v),
    ensures
        inv_rd(w, n, st, rd),
{
    reveal(inv_rd);
    assert forall|k: int| 0 <= k < n implies #[trigger] st[k] <= 2 by {
        if k != v {
            assert(st1[k] <= 2);
        }
    }
    assert forall|k: int| 0 <= k < n implies ((#[trigger] rd[k]) is Some) == (st[k] != 0) by {
        if k != v {
            assert(rd[k] == rd1[k]);
        }
    }
    assert forall|k: int| 0 <= k < n && (#[trigger] rd[k]) is Some implies read_ok(w, k, rd[k]->0) && !bad(w, k) by {
        if k != v {
            assert(rd[k] == rd1[k]);
        }
    }
    assert forall|k: int| 0 <= k < n && #[trigger] st[k] != 0 implies reachable(w, k) by {
        if k != v {
            assert(st1[k] != 0);
        }
    }
}

proof fn lemma_push_sk(
    w: World,
    n: int,
    st1: Seq<u8>,
    sk0: Seq<(usize, usize)>,
    sk1: Seq<(usize, usize)>,
    st: Seq<u8>,
    sk: Seq<(usize, usize)>,
    v: int,
)
    requires
        inv_sk(w, n, st1, sk0),
        st1.len() == n,
        0 <= n <= usize::MAX,
        sk0.len() > 0,
        sk0.last().1 < toks_of(w, sk0.last().0 as int).len(),
        sk1 == sk0.update(sk0.len() - 1, (sk0.last().0, (sk0.last().1 + 1) as usize)),
        ref_in(w, sk0.last().0 as int, sk0.last().1 as int) == Some(v),
        0 <= v < n,
        st1[v] == 0,
        st == st1.update(v, 1),
        sk == sk1.push((v as usize, 0usize)),
    ensures
        inv_sk(w, n, st, sk),
{
    reveal(inv_sk);
    let t = sk0.len() - 1;
    let u = sk0[t].0 as int;
    let pos = sk0[t].1 as int;
    assert(sk0.last() == sk0[t]);
    assert(nodes(sk1) =~= nodes(sk0));
    assert(nodes(sk) =~= nodes(sk0).push(v));
    lemma_edge_of(w, u, pos, v);
    assert(nodes(sk0).last() == u) by {
        lemma_nodes_index(sk0, t);
    }
    lemma_path_push(w, nodes(sk0), v);
    assert(sk[0].0 == sk0[0].0) by {
        if t == 0 {
            assert(sk[0] == sk1[0]);
        } else {
            assert(sk[0] == sk0[0]);
        }
    }
    assert forall|i: int|
        0 <= i < sk.len() implies (#[trigger] sk[i]).0 < n && st[sk[i].0 as int] == 1 && sk[i].1 <= toks_of(
        w,
        sk[i].0 as int,
    ).len() by {
        if i < t {
            assert(sk[i] == sk0[i]);
            assert(st1[sk0[i].0 as int] == 1);
        } else if i == t {
            assert(sk[i] == sk1[t]);
            assert(st1[u] == 1);
        } else {
            assert(sk[i] == (v as usize, 0usize));
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < sk.len() implies (#[trigger] sk[i]).0 != (#[trigger] sk[j]).0 by {
        if j < sk0.len() {
            assert(sk[i].0 == sk0[i].0 && sk[j].0 == sk0[j].0);
        } else {
            assert(sk[i].0 == sk0[i].0);
            assert(st1[sk0[i].0 as int] == 1);
        }
    }
    assert forall|k: int| 0 <= k < n && #[trigger] st[k] == 1 implies nodes(sk).contains(k) by {
        if k == v {
            assert(nodes(sk)[sk0.len() as int] == v);
        } else {
            assert(st1[k] == 1);
            assert(nodes(sk0).contains(k));
            let x = choose|x: int| 0 <= x < nodes(sk0).len() && nodes(sk0)[x] == k;
            assert(nodes(sk)[x] == k);
        }
    }
}

proof fn lemma_push_ref(
    w: World,
    n: int,
    st1: Seq<u8>,
    sk0: Seq<(usize, usize)>,
    sk1: Seq<(usize, usize)>,
    st: Seq<u8>,
    sk: Seq<(usize, usize)>,
    v: int,
)
    requires
        inv_ref(w, n, st1, sk0),
        st1.len() == n,
        0 <= n <= usize::MAX,
        sk0.len() > 0,
        sk1 == sk0.update(sk0.len() - 1, (sk0.last().0, (sk0.last().1 + 1) as usize)),
        ref_in(w, sk0.last().0 as int, sk0.last().1 as int) == Some(v),
        0 <= v < n,
        st1[v] == 0,
        st == st1.update(v, 1),
        sk == sk1.push((v as usize, 0usize)),
    ensures
        inv_ref(w, n, st, sk),
{
    reveal(inv_ref);
    let t = sk0.len() - 1;
    let pos = sk0[t].1 as int;
    assert(sk0.last() == sk0[t]);
    assert forall|i: int, j: int|
        0 <= i < sk.len() && 0 <= j < sk[i].1 && (#[trigger] ref_in(w, sk[i].0 as int, j)) is Some implies ref_done(
        n,
        st,
        sk,
        i,
        ref_in(w, sk[i].0 as int, j)->0,
    ) by {
        let x = ref_in(w, sk[i].0 as int, j)->0;
        if i < t {
            assert(sk[i] == sk0[i]);
            assert(ref_in(w, sk0[i].0 as int, j) is Some);
            assert(ref_done(n, st1, sk0, i, x));
            assert(sk[i + 1].0 == sk0[i + 1].0) by {
                if i + 1 == t {
                    assert(sk[i + 1] == sk1[t]);
                }
            }
            if 0 <= x < n && st1[x] == 2 {
                assert(x != v);
            }
        } else if i == t {
            assert(sk[i] == sk1[t]);
            assert(sk[i].0 == sk0[t].0);
            if j < pos {
                assert(ref_in(w, sk0[t].0 as int, j) is Some);
                assert(ref_done(n, st1, sk0, t, x));
                assert(st1[x] == 2);
                assert(x != v);
            } else {
                assert(j == pos);
                assert(x == v);
                assert(sk[t + 1] == (v as usize, 0usize));
            }
        } else {
            assert(sk[i] == (v as usize, 0usize));
        }
    }
}

/// At the end: every reference in the document is to a black entity, so
/// every entity it reaches is black, and none is on a cycle.
proof fn lemma_done(w: World, n: int, st: Seq<u8>, rd: Seq<Option<ERead>>, fin: Seq<int>, cnt: int)
    requires
        inv(w, n, st, rd, Seq::empty(), fin, cnt),
        w.env.ents.len() == n,
        forall|j: int|
            w.root <= j < w.dt.len() && (#[trigger] ref_of(w, w.doc, w.dt[j]@)) is Some ==> st[ref_of(w, w.doc, w.dt[j]@)->0]
                == 2,
    ensures
        rd.len() == n,
        forall|k: int| 0 <= k < n ==> ((#[trigger] rd[k]) is Some) == reachable(w, k),
        forall|k: int| 0 <= k < n && (#[trigger] rd[k]) is Some ==> read_ok(w, k, rd[k]->0),
        forall|k: int| #[trigger] reachable(w, k) ==> 0 <= k < n && !bad(w, k) && !on_cycle(w, k),
{
    reveal(inv_rd);
    reveal(inv_blk);
    assert forall|k: int| #[trigger] reachable(w, k) implies 0 <= k < n && st[k] == 2 by {
        reveal(reachable);
        reveal(root_ref);
        let p = choose|p: Seq<int>| #[trigger] path(w, p) && root_ref(w, p[0]) && p.last() == k;
        let j = choose|j: int| w.root <= j < w.dt.len() && #[trigger] ref_of(w, w.doc, w.dt[j]@) == Some(p[0]);
        lemma_ref_range(w, n, w.doc, w.dt[j]@);
        reveal(path);
        lemma_all_black(w, n, st, fin, p, p.len() - 1);
    }
    assert forall|k: int| #[trigger] reachable(w, k) implies 0 <= k < n && !bad(w, k) && !on_cycle(w, k) by {
        assert(st[k] == 2);
        assert(rd[k] is Some);
        if on_cycle(w, k) {
            reveal(on_cycle);
            let p = choose|p: Seq<int>| #[trigger] path(w, p) && p.len() >= 2 && p[0] == k && p.last() == k;
            lemma_fin_down(w, n, st, fin, p, p.len() - 1);
        }
    }
    assert forall|k: int| 0 <= k < n implies ((#[trigger] rd[k]) is Some) == reachable(w, k) by {
        if reachable(w, k) {
            assert(st[k] == 2);
        }
        if rd[k] is Some {
            assert(st[k] != 0);
        }
    }
}

} // verus!
