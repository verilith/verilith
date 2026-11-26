//! Attribute-list declarations, for reading (§3.3): which attribute
//! definitions apply, the defaults an element gets, and the collapsing of
//! white space in a value of a declared type other than CDATA (§3.3.3).
//!
//! * `decls` states which definitions are processed: those of the ATTLIST
//!   declarations in the DTD, in order, up to the end of the document type
//!   declaration and, unless the document is standalone, none after the
//!   first parameter entity reference that was not read (§5.1: "it must
//!   not process ... attribute-list declarations ... after an unread
//!   parameter entity reference").
//! * `binding` states which of them bind: "When more than one definition
//!   is provided for the same attribute of a given element type, the
//!   first declaration is binding and later declarations are ignored"
//!   (§3.3).
//! * `AttTable` is built from the tokens and proven to answer by that:
//!   `def_for` (the definition of one attribute of an element type),
//!   `next_default` and `ex_defaults` (the defaults an element gets: the
//!   binding definitions for its type with a default value, `#FIXED` or
//!   not, for the attributes its start tag does not give, in declaration
//!   order).
//! * `collapse` states §3.3.3's "discarding any leading and trailing
//!   space (#x20) characters, and by replacing sequences of space (#x20)
//!   characters by a single space (#x20) character", and `ex_collapse`
//!   computes it.
//!
//! Lookups go through `index::NameIndex`, the hashed index the entities
//! use, so a lookup takes time independent of how many definitions there
//! are: one index over the element types' names, and one per element type
//! over its attributes' names.
#[cfg(verus_keep_ghost)]
use crate::index::{indexes, lemma_find_first, spans};
#[cfg(verus_keep_ghost)]
use crate::lex::{ent_view, ents_view};
use crate::index::NameIndex;
use crate::lex::{ex_bytes_eq, XEnt};
use crate::spec::*;
use crate::tape::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §3.3.3: collapsing white space
// ---------------------------------------------------------------------------

/// `v[i..]` collapsed, after `sp` (a space was passed since the last
/// non-space byte) and `any` (a non-space byte was kept): spaces are
/// dropped, and one is put back before a non-space byte that follows
/// spaces, unless nothing was kept before it.
pub open spec fn coll(v: Seq<u8>, i: int, sp: bool, any: bool) -> Seq<u8>
    decreases v.len() - i,
{
    if i < 0 || i >= v.len() {
        Seq::empty()
    } else if v[i] == 0x20 {
        coll(v, i + 1, true, any)
    } else if sp && any {
        seq![0x20u8, v[i]] + coll(v, i + 1, false, true)
    } else {
        seq![v[i]] + coll(v, i + 1, false, true)
    }
}

/// §3.3.3: "If the attribute type is not CDATA, then the XML processor
/// MUST further process the normalized attribute value by discarding any
/// leading and trailing space (#x20) characters, and by replacing
/// sequences of space (#x20) characters by a single space (#x20)
/// character."
pub open spec fn collapse(v: Seq<u8>) -> Seq<u8> {
    coll(v, 0, false, false)
}

/// `collapse(v)`.
pub fn ex_collapse(v: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == collapse(v@),
{
    let mut out: Vec<u8> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    let mut sp = false;
    let mut any = false;
    while i < v.len()
        invariant
            i <= v@.len(),
            out@ + coll(v@, i as int, sp, any) == collapse(v@),
        decreases v@.len() - i,
    {
        let c = v[i];
        if c == 0x20 {
            sp = true;
        } else {
            proof {
                assert(out@ + coll(v@, i as int, sp, any) == collapse(v@));
            }
            if sp && any {
                proof {
                    assert(out@.push(0x20u8).push(c) + coll(v@, i + 1, false, true) =~= out@ + (seq![0x20u8, c] + coll(
                        v@,
                        i + 1,
                        false,
                        true,
                    )));
                }
                out.push(0x20);
            } else {
                proof {
                    assert(out@.push(c) + coll(v@, i + 1, false, true) =~= out@ + (seq![c] + coll(v@, i + 1, false, true)));
                }
            }
            out.push(c);
            sp = false;
            any = true;
        }
        i = i + 1;
    }
    proof {
        assert(out@ + coll(v@, i as int, sp, any) =~= out@);
    }
    out
}

/// What `coll` gives: no space first or last, and no two spaces in a row.
pub proof fn lemma_coll_shape(v: Seq<u8>, i: int, sp: bool, any: bool)
    requires
        0 <= i,
    ensures
        ({
            let r = coll(v, i, sp, any);
            &&& r.len() > 0 && r[0] == 0x20 ==> any
            &&& r.len() > 0 ==> r[r.len() - 1] != 0x20
            &&& forall|k: int| 0 <= k < r.len() - 1 && #[trigger] r[k] == 0x20 ==> r[k + 1] != 0x20
        }),
    decreases v.len() - i,
{
    if 0 <= i < v.len() {
        if v[i] == 0x20 {
            lemma_coll_shape(v, i + 1, true, any);
        } else {
            lemma_coll_shape(v, i + 1, false, true);
            let t = coll(v, i + 1, false, true);
            let r = coll(v, i, sp, any);
            let h = if sp && any {
                seq![0x20u8, v[i]]
            } else {
                seq![v[i]]
            };
            assert(r == h + t);
            assert forall|k: int| 0 <= k < r.len() - 1 && #[trigger] r[k] == 0x20 implies r[k + 1] != 0x20 by {
                if k + 1 >= h.len() {
                    if k >= h.len() {
                        assert(r[k] == t[k - h.len()]);
                        assert(r[k + 1] == t[k + 1 - h.len()]);
                    } else {
                        // r[k] is h's last byte, v[i], not a space.
                        assert(r[k] == v[i]);
                    }
                } else {
                    assert(r[k + 1] == v[i]);
                }
            }
            if t.len() > 0 {
                assert(r[r.len() - 1] == t[t.len() - 1]);
            } else {
                assert(r[r.len() - 1] == v[i]);
            }
        }
    }
}

/// §3.3.3's properties of a collapsed value: it does not begin or end
/// with a space, and holds no two spaces in a row.
pub proof fn lemma_collapse_shape(v: Seq<u8>)
    ensures
        ({
            let r = collapse(v);
            &&& r.len() > 0 ==> r[0] != 0x20 && r[r.len() - 1] != 0x20
            &&& forall|k: int| 0 <= k < r.len() - 1 && #[trigger] r[k] == 0x20 ==> r[k + 1] != 0x20
        }),
{
    lemma_coll_shape(v, 0, false, false);
}

/// What `coll` drops: only spaces; the other bytes are kept, in order.
pub open spec fn nonspace(v: Seq<u8>) -> Seq<u8> {
    v.filter(|c: u8| c != 0x20)
}

proof fn lemma_coll_nonspace(v: Seq<u8>, i: int, sp: bool, any: bool)
    requires
        0 <= i <= v.len(),
    ensures
        nonspace(coll(v, i, sp, any)) == nonspace(v.subrange(i, v.len() as int)),
    decreases v.len() - i,
{
    let f = |c: u8| c != 0x20;
    if i < v.len() {
        if v[i] == 0x20 {
            lemma_coll_nonspace(v, i + 1, true, any);
        } else {
            lemma_coll_nonspace(v, i + 1, false, true);
        }
        let rest = v.subrange(i + 1, v.len() as int);
        assert(v.subrange(i, v.len() as int) =~= seq![v[i]] + rest);
        Seq::filter_distributes_over_add(seq![v[i]], rest, f);
        reveal_with_fuel(Seq::filter, 2);
        if v[i] != 0x20 {
            let t = coll(v, i + 1, false, true);
            if sp && any {
                assert(seq![0x20u8, v[i]] =~= seq![0x20u8] + seq![v[i]]);
                Seq::filter_distributes_over_add(seq![0x20u8, v[i]], t, f);
                Seq::filter_distributes_over_add(seq![0x20u8], seq![v[i]], f);
            } else {
                Seq::filter_distributes_over_add(seq![v[i]], t, f);
            }
        }
    } else {
        assert(v.subrange(i, v.len() as int) =~= Seq::<u8>::empty());
    }
}

/// `collapse` keeps every byte that is not a space, in order.
pub proof fn lemma_collapse_nonspace(v: Seq<u8>)
    ensures
        nonspace(collapse(v)) == nonspace(v),
{
    lemma_coll_nonspace(v, 0, false, false);
    assert(v.subrange(0, v.len() as int) =~= v);
}

// ---------------------------------------------------------------------------
// §3.3: the definitions that are processed, and those that bind
// ---------------------------------------------------------------------------

/// An attribute definition that was processed: the spans (in the text of
/// the declarations) of the element type's name and the attribute's name,
/// the attribute's type (`att_type`: 1 CDATA, others above), its
/// default's kind (`XTok::AttDefault`: 1 `#REQUIRED`, 2 `#IMPLIED`,
/// 3 `#FIXED` value, 4 value) and, for kinds 3 and 4, the raw value's span.
#[derive(Clone, Copy, Debug)]
pub struct ADecl {
    pub ea: usize,
    pub eb: usize,
    pub na: usize,
    pub nb: usize,
    pub ty: u8,
    pub kind: u8,
    pub va: usize,
    pub vb: usize,
}

/// A token's span lies in a text of `n` bytes.
pub open spec fn in_text(t: Tok, n: int) -> bool {
    0 <= t.sa() <= t.sb() <= n
}

/// The definition of the `AttDef` token `d` with its default `v`, in the
/// ATTLIST declaration of the element type `el`, in a text of `n` bytes.
/// (On the parser's tapes `v` is always an `AttDefault` and the spans are
/// in the text; other tokens give nothing.)
pub open spec fn mk_decl(n: int, el: Tok, d: Tok, v: Tok) -> Option<ADecl> {
    if v.kind is AttDefault && in_text(el, n) && in_text(d, n) && (v.f < 3 || in_text(v, n)) {
        Some(
            ADecl {
                ea: el.sa() as usize,
                eb: el.sb() as usize,
                na: d.sa() as usize,
                nb: d.sb() as usize,
                ty: d.f,
                kind: v.f,
                va: if v.f < 3 {
                    0usize
                } else {
                    v.sa() as usize
                },
                vb: if v.f < 3 {
                    0usize
                } else {
                    v.sb() as usize
                },
            },
        )
    } else {
        None
    }
}

/// The definitions processed from token `i` on: `skip` once an unread
/// parameter entity reference was passed in a document that is not
/// standalone (`sa`), `el` the ATTLIST declaration being read.
pub open spec fn decls_from(n: int, t: Seq<Tok>, sa: bool, i: int, skip: bool, el: Option<Tok>) -> Seq<ADecl>
    decreases t.len() - i,
{
    if i < 0 || i >= t.len() {
        Seq::empty()
    } else if t[i].kind is DoctypeEnd {
        Seq::empty()
    } else if t[i].kind is PERef {
        decls_from(n, t, sa, i + 1, skip || !sa, el)
    } else if t[i].kind is AttlistDecl {
        decls_from(n, t, sa, i + 1, skip, Some(t[i]))
    } else if t[i].kind is AttDef && !skip && i + 1 < t.len() {
        let rest = decls_from(n, t, sa, i + 2, skip, el);
        match el {
            Some(e) => match mk_decl(n, e, t[i], t[i + 1]) {
                Some(d) => seq![d] + rest,
                None => rest,
            },
            None => rest,
        }
    } else {
        decls_from(n, t, sa, i + 1, skip, el)
    }
}

/// The attribute definitions processed, in order, from the tokens `t` of
/// the declarations (whose text is `n` bytes), in a document that is
/// standalone (`sa`) or not. The `PERef` tokens are the parameter entity
/// references that were not read: the parser expands the others.
pub open spec fn decls(n: int, t: Seq<Tok>, sa: bool) -> Seq<ADecl> {
    decls_from(n, t, sa, 0, false, None)
}

/// The element type a definition is for.
pub open spec fn en(s: Seq<u8>, d: ADecl) -> Seq<u8> {
    s.subrange(d.ea as int, d.eb as int)
}

/// The attribute a definition is of.
pub open spec fn an(s: Seq<u8>, d: ADecl) -> Seq<u8> {
    s.subrange(d.na as int, d.nb as int)
}

/// §3.3: definition `j` is the first for its attribute of its element type.
pub open spec fn binding(s: Seq<u8>, ds: Seq<ADecl>, j: int) -> bool {
    forall|k: int| 0 <= k < j ==> !(en(s, #[trigger] ds[k]) == en(s, ds[j]) && an(s, ds[k]) == an(s, ds[j]))
}

/// Every definition's spans are in the text.
pub open spec fn decls_in(s: Seq<u8>, ds: Seq<ADecl>) -> bool {
    bounded(ds, s.len() as int)
}

/// The definitions' spans are in a text of `n` bytes.
pub open spec fn bounded(ds: Seq<ADecl>, n: int) -> bool {
    forall|j: int|
        0 <= j < ds.len() ==> (#[trigger] ds[j]).ea <= ds[j].eb <= n && ds[j].na <= ds[j].nb <= n && ds[j].va <= ds[j].vb
            <= n
}

proof fn lemma_decls_in(n: int, t: Seq<Tok>, sa: bool, i: int, skip: bool, el: Option<Tok>)
    requires
        0 <= n <= usize::MAX,
    ensures
        bounded(decls_from(n, t, sa, i, skip, el), n),
    decreases t.len() - i,
{
    if 0 <= i < t.len() && !(t[i].kind is DoctypeEnd) {
        if t[i].kind is PERef {
            lemma_decls_in(n, t, sa, i + 1, skip || !sa, el);
        } else if t[i].kind is AttlistDecl {
            lemma_decls_in(n, t, sa, i + 1, skip, Some(t[i]));
        } else if t[i].kind is AttDef && !skip && i + 1 < t.len() {
            lemma_decls_in(n, t, sa, i + 2, skip, el);
            let rest = decls_from(n, t, sa, i + 2, skip, el);
            match el {
                Some(e) => match mk_decl(n, e, t[i], t[i + 1]) {
                    Some(d) => {
                        let all = seq![d] + rest;
                        assert(decls_from(n, t, sa, i, skip, el) == all);
                        assert(d.ea <= d.eb <= n && d.na <= d.nb <= n && d.va <= d.vb <= n);
                        assert forall|j: int| 0 <= j < all.len() implies #[trigger] all[j].ea <= all[j].eb <= n
                            && all[j].na <= all[j].nb <= n && all[j].va <= all[j].vb <= n by {
                            if j == 0 {
                                assert(all[0] == d);
                            } else {
                                assert(all[j] == rest[j - 1]);
                                assert(bounded(rest, n));
                                assert(rest[j - 1].ea <= rest[j - 1].eb <= n);
                            }
                        }
                    },
                    None => {},
                },
                None => {},
            }
        } else {
            lemma_decls_in(n, t, sa, i + 1, skip, el);
        }
    } else {
        assert(decls_from(n, t, sa, i, skip, el) =~= Seq::<ADecl>::empty());
    }
}

/// A token's span, if it lies in a text of `n` bytes.
fn span_of(t: Tok, n: usize) -> (r: Option<(usize, usize)>)
    ensures
        match r {
            Some((a, b)) => a == t.sa() && b == t.sb() && in_text(t, n as int),
            None => !in_text(t, n as int),
        },
{
    let a = t.a48();
    let b = t.b48();
    if a <= b && b <= n as u64 {
        Some((a as usize, b as usize))
    } else {
        None
    }
}

/// `mk_decl`.
fn ex_mk_decl(n: usize, el: Tok, d: Tok, v: Tok) -> (r: Option<ADecl>)
    ensures
        r == mk_decl(n as int, el, d, v),
{
    match v.kind {
        Kind::AttDefault => {},
        _ => {
            return None;
        },
    }
    let Some((ea, eb)) = span_of(el, n) else { return None };
    let Some((na, nb)) = span_of(d, n) else { return None };
    let (va, vb) = if v.f < 3 {
        (0usize, 0usize)
    } else {
        match span_of(v, n) {
            Some(x) => x,
            None => {
                return None;
            },
        }
    };
    Some(ADecl { ea, eb, na, nb, ty: d.f, kind: v.f, va, vb })
}

/// `decls(s.len(), t, sa)`.
pub fn ex_decls(s: &[u8], t: &[Tok], sa: bool) -> (r: Vec<ADecl>)
    ensures
        r@ == decls(s@.len() as int, t@, sa),
        decls_in(s@, r@),
{
    let n = s.len();
    let mut out: Vec<ADecl> = Vec::new();
    let mut i: usize = 0;
    let mut skip = false;
    let mut el: Option<Tok> = None;
    while i < t.len()
        invariant
            i <= t@.len(),
            n == s@.len(),
            out@ + decls_from(n as int, t@, sa, i as int, skip, el) == decls(n as int, t@, sa),
        decreases t@.len() - i,
    {
        let k = t[i];
        match k.kind {
            Kind::DoctypeEnd => {
                proof {
                    assert(out@ + decls_from(n as int, t@, sa, i as int, skip, el) =~= out@);
                }
                proof {
                    lemma_decls_in(n as int, t@, sa, 0, false, None);
                }
                return out;
            },
            Kind::PERef => {
                if !sa {
                    skip = true;
                }
                i = i + 1;
            },
            Kind::AttlistDecl => {
                el = Some(k);
                i = i + 1;
            },
            Kind::AttDef => {
                if !skip && i + 1 < t.len() {
                    let ghost rest = decls_from(n as int, t@, sa, i + 2, skip, el);
                    if let Some(e) = el {
                        if let Some(d) = ex_mk_decl(n, e, k, t[i + 1]) {
                            proof {
                                assert(out@.push(d) + rest =~= out@ + (seq![d] + rest));
                            }
                            out.push(d);
                        }
                    }
                    i = i + 2;
                } else {
                    i = i + 1;
                }
            },
            _ => {
                i = i + 1;
            },
        }
    }
    proof {
        assert(out@ + decls_from(n as int, t@, sa, i as int, skip, el) =~= out@);
        lemma_decls_in(n as int, t@, sa, 0, false, None);
    }
    out
}

// ---------------------------------------------------------------------------
// Finding a name with an index
// ---------------------------------------------------------------------------

/// The name a span of `s` stands for.
pub open spec fn sn(s: Seq<u8>, e: XEnt) -> Seq<u8> {
    s.subrange(e.a as int, e.b as int)
}

/// The spans are in `s`.
pub open spec fn spans_in(s: Seq<u8>, es: Seq<XEnt>) -> bool {
    forall|p: int| 0 <= p < es.len() ==> (#[trigger] es[p]).a <= es[p].b <= s.len()
}

/// The first of the names `es` that is `q[a..b]`.
fn find_first(x: &NameIndex, s: &[u8], es: &[XEnt], q: &[u8], a: usize, b: usize) -> (r: Option<usize>)
    requires
        indexes(x, s@, es@),
        a <= b <= q@.len(),
        spans_in(s@, es@),
    ensures
        match r {
            Some(j) => j < es@.len() && sn(s@, es@[j as int]) == q@.subrange(a as int, b as int) && forall|k: int|
                0 <= k < j ==> sn(s@, #[trigger] es@[k]) != q@.subrange(a as int, b as int),
            None => forall|k: int| 0 <= k < es@.len() ==> sn(s@, #[trigger] es@[k]) != q@.subrange(a as int, b as int),
        },
{
    let r = x.find(s, es, es.len(), q, a, b);
    proof {
        let ev = ents_view(s@, es@);
        let qn = q@.subrange(a as int, b as int);
        assert(ev.subrange(0, es@.len() as int) =~= ev);
        lemma_find_first(ev, qn);
        assert forall|k: int| 0 <= k < es@.len() implies #[trigger] ev[k].name == sn(s@, es@[k]) by {
            assert(ev[k] == ent_view(s@, es@[k]));
        }
        match r {
            Some(j) => {
                assert(ev[j as int].name == sn(s@, es@[j as int]));
                assert forall|k: int| 0 <= k < j implies sn(s@, #[trigger] es@[k]) != qn by {
                    assert(ev[k].name == sn(s@, es@[k]));
                }
            },
            None => {
                assert forall|k: int| 0 <= k < es@.len() implies sn(s@, #[trigger] es@[k]) != qn by {
                    assert(ev[k].name == sn(s@, es@[k]));
                }
            },
        }
    }
    r
}

/// A span as an index entry.
pub open spec fn ent_of(a: usize, b: usize) -> XEnt {
    XEnt { a, b, kind: 0, va: 0, vb: 0 }
}

// ---------------------------------------------------------------------------
// The table
// ---------------------------------------------------------------------------

/// The definitions processed (`decls`), grouped by element type, each
/// group indexed by attribute name.
pub struct AttTable {
    /// The definitions processed, in order.
    pub decls: Vec<ADecl>,
    /// Their element types' names, and an index of them.
    pub eix: Vec<XEnt>,
    pub eidx: NameIndex,
    /// Per definition: its group.
    pub grp: Vec<usize>,
    /// Per group: its definitions, in order.
    pub members: Vec<Vec<usize>>,
    /// Per group: its definitions' attribute names, and an index of them.
    pub names: Vec<Vec<XEnt>>,
    pub nidx: Vec<NameIndex>,
    /// Per group: where in `members` its binding definitions are, in order.
    pub bound: Vec<Vec<usize>>,
}

/// `v` is strictly increasing, and below `n`.
pub open spec fn incr(v: Seq<usize>, n: int) -> bool {
    &&& forall|p: int, q: int| 0 <= p < q < v.len() ==> v[p] < v[q]
    &&& forall|p: int| 0 <= p < v.len() ==> v[p] < n
}

/// The members of a group, as found by `members` and `grp`.
pub open spec fn group_ok(s: Seq<u8>, ds: Seq<ADecl>, grp: Seq<usize>, g: int, m: Seq<usize>, lim: int) -> bool {
    &&& m.len() > 0
    &&& incr(m, lim)
    &&& forall|p: int| 0 <= p < m.len() ==> grp[#[trigger] m[p] as int] == g
    &&& forall|j: int| 0 <= j < lim && grp[j] == g ==> #[trigger] m.contains(j as usize)
}

/// The first `lim` definitions are grouped by element type: `grp` gives
/// each its group, the same exactly for the same element type, and
/// `members` lists each group's.
pub open spec fn grouped(s: Seq<u8>, ds: Seq<ADecl>, grp: Seq<usize>, members: Seq<Vec<usize>>, lim: int) -> bool {
    &&& grp.len() >= lim
    &&& forall|k: int| 0 <= k < lim ==> #[trigger] grp[k] < members.len()
    &&& forall|k: int, l: int|
        0 <= k < lim && 0 <= l < lim ==> (#[trigger] grp[k] == #[trigger] grp[l]) == (en(s, ds[k]) == en(s, ds[l]))
    &&& forall|g: int| 0 <= g < members.len() ==> group_ok(s, ds, grp, g, #[trigger] members[g]@, lim)
}

/// No earlier name in `nm` is the same as the `p`th.
pub open spec fn first_name(s: Seq<u8>, nm: Seq<XEnt>, p: int) -> bool {
    forall|q: int| 0 <= q < p ==> sn(s, #[trigger] nm[q]) != sn(s, nm[p])
}

/// The names of a group's members.
pub open spec fn names_of(ds: Seq<ADecl>, m: Seq<usize>, nm: Seq<XEnt>) -> bool {
    &&& nm.len() == m.len()
    &&& forall|p: int| 0 <= p < m.len() ==> #[trigger] nm[p] == ent_of(ds[m[p] as int].na, ds[m[p] as int].nb)
}

/// One group's index of names, and which of its members bind.
pub open spec fn gtab_ok(s: Seq<u8>, ds: Seq<ADecl>, m: Seq<usize>, nm: Seq<XEnt>, x: &NameIndex, b: Seq<usize>) -> bool {
    &&& names_of(ds, m, nm)
    &&& spans_in(s, nm)
    &&& indexes(x, s, nm)
    &&& incr(b, m.len() as int)
    &&& forall|p: int| 0 <= p < m.len() ==> (#[trigger] b.contains(p as usize) == first_name(s, nm, p))
}

/// The table's invariant: what `build` makes and the lookups rely on.
pub open spec fn table_ok(s: Seq<u8>, t: &AttTable) -> bool {
    let ds = t.decls@;
    let n = ds.len() as int;
    let ng = t.members@.len() as int;
    &&& decls_in(s, ds)
    &&& n <= isize::MAX
    &&& t.eix@.len() == n && t.grp@.len() == n
    &&& forall|j: int| 0 <= j < n ==> #[trigger] t.eix@[j] == ent_of(ds[j].ea, ds[j].eb)
    &&& spans_in(s, t.eix@)
    &&& indexes(&t.eidx, s, t.eix@)
    &&& grouped(s, ds, t.grp@, t.members@, n)
    &&& t.names@.len() == ng && t.nidx@.len() == ng && t.bound@.len() == ng
    &&& forall|g: int|
        0 <= g < ng ==> gtab_ok(s, ds, t.members@[g]@, t.names@[g]@, &#[trigger] t.nidx@[g], t.bound@[g]@)
}

/// The table describes these definitions.
pub open spec fn table_of(s: Seq<u8>, t: &AttTable, ds: Seq<ADecl>) -> bool {
    table_ok(s, t) && t.decls@ == ds
}

proof fn lemma_incr_contains(v: Seq<usize>, n: int, p: int, x: usize)
    requires
        incr(v, n),
        0 <= p < v.len(),
        v.contains(x),
        x < v[p],
    ensures
        exists|q: int| 0 <= q < p && v[q] == x,
{
    let q = choose|q: int| 0 <= q < v.len() && v[q] == x;
    if q >= p {
        if q > p {
            assert(v[p] < v[q]);
        }
    }
}

/// Within a group, a member binds exactly when no earlier member has its
/// name: every earlier definition for its element type is an earlier
/// member.
proof fn lemma_binding_first(
    s: Seq<u8>,
    ds: Seq<ADecl>,
    grp: Seq<usize>,
    members: Seq<Vec<usize>>,
    n: int,
    g: int,
    nm: Seq<XEnt>,
    p: int,
)
    requires
        grouped(s, ds, grp, members, n),
        n == ds.len(),
        0 <= g < members.len(),
        names_of(ds, members[g]@, nm),
        0 <= p < members[g]@.len(),
    ensures
        binding(s, ds, members[g]@[p] as int) == first_name(s, nm, p),
{
    let m = members[g]@;
    assert(group_ok(s, ds, grp, g, m, n));
    let j = m[p] as int;
    assert(grp[j] == g);
    assert(nm[p] == ent_of(ds[j].na, ds[j].nb));
    if !binding(s, ds, j) {
        let k = choose|k: int| 0 <= k < j && en(s, #[trigger] ds[k]) == en(s, ds[j]) && an(s, ds[k]) == an(s, ds[j]);
        assert(grp[k] == grp[j]);
        assert(m.contains(k as usize));
        lemma_incr_contains(m, n, p, k as usize);
        let q = choose|q: int| 0 <= q < p && m[q] == k as usize;
        assert(nm[q] == ent_of(ds[k].na, ds[k].nb));
        assert(sn(s, nm[q]) == sn(s, nm[p]));
    }
    if !first_name(s, nm, p) {
        let q = choose|q: int| 0 <= q < p && sn(s, #[trigger] nm[q]) == sn(s, nm[p]);
        let k = m[q] as int;
        assert(m[q] < m[p]);
        assert(grp[k] == g);
        assert(grp[k] == grp[j]);
        assert(nm[q] == ent_of(ds[k].na, ds[k].nb));
        assert(en(s, ds[k]) == en(s, ds[j]) && an(s, ds[k]) == an(s, ds[j]));
    }
}

/// `grouped` for one more definition, put in the existing group `g`.
proof fn lemma_group_add(
    s: Seq<u8>,
    ds: Seq<ADecl>,
    og: Seq<usize>,
    om: Seq<Vec<usize>>,
    grp: Seq<usize>,
    members: Seq<Vec<usize>>,
    j: int,
    g: int,
    r: int,
)
    requires
        grouped(s, ds, og, om, j),
        og.len() == j,
        0 <= r < j,
        og[r] == g,
        en(s, ds[r]) == en(s, ds[j]),
        0 <= j < ds.len() <= isize::MAX,
        grp == og.push(g as usize),
        members.len() == om.len(),
        members[g]@ == om[g]@.push(j as usize),
        forall|g2: int| 0 <= g2 < om.len() && g2 != g ==> #[trigger] members[g2]@ == om[g2]@,
    ensures
        grouped(s, ds, grp, members, j + 1),
{
    assert(og[r] < om.len());
    assert forall|k: int| 0 <= k < j + 1 implies #[trigger] grp[k] < members.len() by {
        if k < j {
            assert(grp[k] == og[k]);
        }
    }
    assert forall|k: int, l: int|
        0 <= k < j + 1 && 0 <= l < j + 1 implies (#[trigger] grp[k] == #[trigger] grp[l]) == (en(s, ds[k]) == en(
        s,
        ds[l],
    )) by {
        if k < j {
            assert(grp[k] == og[k]);
            assert(og[k] == og[r] <==> en(s, ds[k]) == en(s, ds[r]));
        }
        if l < j {
            assert(grp[l] == og[l]);
            assert(og[l] == og[r] <==> en(s, ds[l]) == en(s, ds[r]));
        }
    }
    assert forall|g2: int| 0 <= g2 < members.len() implies group_ok(s, ds, grp, g2, #[trigger] members[g2]@, j + 1) by {
        let om2 = om[g2]@;
        assert(group_ok(s, ds, og, g2, om2, j));
        let m = members[g2]@;
        if g2 == g {
            assert(m == om2.push(j as usize));
            assert(grp[j] == g);
            assert forall|p: int, q: int| 0 <= p < q < m.len() implies m[p] < m[q] by {
                if q < om2.len() {
                    assert(m[p] == om2[p] && m[q] == om2[q]);
                } else {
                    assert(m[p] == om2[p]);
                    assert(m[q] == j);
                    assert(om2[p] < j);
                }
            }
            assert forall|p: int| 0 <= p < m.len() implies m[p] < j + 1 by {
                if p < om2.len() {
                    assert(m[p] == om2[p]);
                }
            }
            assert forall|p: int| 0 <= p < m.len() implies grp[#[trigger] m[p] as int] == g2 by {
                if p < om2.len() {
                    assert(m[p] == om2[p]);
                    assert(og[om2[p] as int] == g2);
                    assert(om2[p] < j);
                    assert(grp[om2[p] as int] == og[om2[p] as int]);
                } else {
                    assert(m[p] == j);
                }
            }
            assert forall|k: int| 0 <= k < j + 1 && grp[k] == g2 implies #[trigger] m.contains(k as usize) by {
                if k < j {
                    assert(grp[k] == og[k]);
                    assert(om2.contains(k as usize));
                    let q = choose|q: int| 0 <= q < om2.len() && om2[q] == k as usize;
                    assert(m[q] == om2[q]);
                } else {
                    assert(m[om2.len() as int] == j);
                }
            }
        } else {
            assert(m == om2);
            assert forall|p: int| 0 <= p < m.len() implies grp[#[trigger] m[p] as int] == g2 by {
                assert(og[m[p] as int] == g2);
            }
            assert forall|k: int| 0 <= k < j + 1 && grp[k] == g2 implies #[trigger] m.contains(k as usize) by {
                if k < j {
                    assert(grp[k] == og[k]);
                }
            }
        }
    }
}

/// `grouped` for one more definition, the first of its element type: a
/// new group `g`.
proof fn lemma_group_new(
    s: Seq<u8>,
    ds: Seq<ADecl>,
    og: Seq<usize>,
    om: Seq<Vec<usize>>,
    grp: Seq<usize>,
    members: Seq<Vec<usize>>,
    j: int,
)
    requires
        grouped(s, ds, og, om, j),
        og.len() == j,
        0 <= j < ds.len() <= isize::MAX,
        om.len() <= j,
        forall|k: int| 0 <= k < j ==> en(s, #[trigger] ds[k]) != en(s, ds[j]),
        grp == og.push(om.len() as usize),
        members.len() == om.len() + 1,
        members[om.len() as int]@ == seq![j as usize],
        forall|g2: int| 0 <= g2 < om.len() ==> #[trigger] members[g2]@ == om[g2]@,
    ensures
        grouped(s, ds, grp, members, j + 1),
{
    let g = om.len() as int;
    assert(grp[j] == g);
    assert forall|k: int| 0 <= k < j + 1 implies #[trigger] grp[k] < members.len() by {
        if k < j {
            assert(grp[k] == og[k]);
        }
    }
    assert forall|k: int, l: int|
        0 <= k < j + 1 && 0 <= l < j + 1 implies (#[trigger] grp[k] == #[trigger] grp[l]) == (en(s, ds[k]) == en(
        s,
        ds[l],
    )) by {
        if k < j {
            assert(grp[k] == og[k]);
            assert(og[k] < g);
            if l == j {
                assert(en(s, ds[k]) != en(s, ds[j]));
            }
        }
        if l < j {
            assert(grp[l] == og[l]);
            assert(og[l] < g);
            if k == j {
                assert(en(s, ds[l]) != en(s, ds[j]));
            }
        }
    }
    assert forall|g2: int| 0 <= g2 < members.len() implies group_ok(s, ds, grp, g2, #[trigger] members[g2]@, j + 1) by {
        let m = members[g2]@;
        if g2 < g {
            assert(m == om[g2]@);
            assert(group_ok(s, ds, og, g2, m, j));
            assert forall|p: int| 0 <= p < m.len() implies grp[#[trigger] m[p] as int] == g2 by {
                assert(og[m[p] as int] == g2);
            }
            assert forall|k: int| 0 <= k < j + 1 && grp[k] == g2 implies #[trigger] m.contains(k as usize) by {
                if k < j {
                    assert(grp[k] == og[k]);
                }
            }
        } else {
            assert(m == seq![j as usize]);
            assert(m[0] == j);
            assert(grp[j] == g2);
            assert forall|k: int| 0 <= k < j + 1 && grp[k] == g2 implies #[trigger] m.contains(k as usize) by {
                if k < j {
                    assert(grp[k] == og[k]);
                    assert(og[k] < g);
                }
            }
        }
    }
}

impl AttTable {
    /// The table of the definitions `decls(s.len(), t, sa)`.
    pub fn build(s: &[u8], t: &[Tok], sa: bool) -> (r: AttTable)
        requires
            t@.len() <= isize::MAX,
        ensures
            table_of(s@, &r, decls(s@.len() as int, t@, sa)),
    {
        let decls = ex_decls(s, t, sa);
        let n = decls.len();
        proof {
            lemma_decls_len(s@.len() as int, t@, sa, 0, false, None);
        }
        let ghost ds = decls@;
        let mut eix: Vec<XEnt> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n == ds.len(),
                ds == decls@,
                decls_in(s@, ds),
                eix@.len() == j,
                forall|k: int| 0 <= k < j ==> #[trigger] eix@[k] == ent_of(ds[k].ea, ds[k].eb),
            decreases n - j,
        {
            let d = decls[j];
            eix.push(XEnt { a: d.ea, b: d.eb, kind: 0, va: 0, vb: 0 });
            j = j + 1;
        }
        proof {
            assert forall|p: int| 0 <= p < eix@.len() implies (#[trigger] eix@[p]).a <= eix@[p].b <= s@.len() by {
                assert(eix@[p] == ent_of(ds[p].ea, ds[p].eb));
                assert(ds[p].ea <= ds[p].eb <= s@.len());
            }
        }
        let eidx = NameIndex::build(s, eix.as_slice());
        // Group the definitions by element type.
        let mut grp: Vec<usize> = Vec::new();
        let mut members: Vec<Vec<usize>> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n == ds.len() <= isize::MAX,
                ds == decls@,
                decls_in(s@, ds),
                eix@.len() == n,
                forall|k: int| 0 <= k < n ==> #[trigger] eix@[k] == ent_of(ds[k].ea, ds[k].eb),
                indexes(&eidx, s@, eix@),
                spans_in(s@, eix@),
                grp@.len() == j,
                members@.len() <= j,
                grouped(s@, ds, grp@, members@, j as int),
            decreases n - j,
        {
            let d = decls[j];
            let ghost q = en(s@, ds[j as int]);
            proof {
                assert(ds[j as int].ea <= ds[j as int].eb <= s@.len());
            }
            let r = find_first(&eidx, s, eix.as_slice(), s, d.ea, d.eb);
            proof {
                assert(eix@[j as int] == ent_of(ds[j as int].ea, ds[j as int].eb));
                assert(sn(s@, eix@[j as int]) == q);
            }
            let rj = r.unwrap();
            proof {
                assert(eix@[rj as int] == ent_of(ds[rj as int].ea, ds[rj as int].eb));
                assert(en(s@, ds[rj as int]) == q);
            }
            let ghost og = grp@;
            let ghost om = members@;
            if rj == j {
                // The first of its element type: a new group.
                let g = members.len();
                proof {
                    assert forall|k: int| 0 <= k < j implies en(s@, #[trigger] ds[k]) != q by {
                        assert(eix@[k] == ent_of(ds[k].ea, ds[k].eb));
                        assert(sn(s@, eix@[k]) != q);
                    }
                }
                let mut v: Vec<usize> = Vec::new();
                v.push(j);
                grp.push(g);
                members.push(v);
                proof {
                    assert(members@[g as int]@ == seq![j]);
                    lemma_group_new(s@, ds, og, om, grp@, members@, j as int);
                }
            } else {
                let g = grp[rj];
                proof {
                    assert(og[rj as int] < om.len());
                }
                let mut v: Vec<usize> = Vec::new();
                members.set_and_swap(g, &mut v);
                v.push(j);
                members.set_and_swap(g, &mut v);
                grp.push(g);
                proof {
                    lemma_group_add(s@, ds, og, om, grp@, members@, j as int, g as int, rj as int);
                }
            }
            j = j + 1;
        }
        // Index each group's names; mark the members that bind.
        let ng = members.len();
        let mut names: Vec<Vec<XEnt>> = Vec::new();
        let mut nidx: Vec<NameIndex> = Vec::new();
        let mut bound: Vec<Vec<usize>> = Vec::new();
        let mut g: usize = 0;
        while g < ng
            invariant
                g <= ng == members@.len(),
                n == ds.len() <= isize::MAX,
                ds == decls@,
                decls_in(s@, ds),
                grouped(s@, ds, grp@, members@, n as int),
                names@.len() == g && nidx@.len() == g && bound@.len() == g,
                forall|g2: int|
                    0 <= g2 < g ==> gtab_ok(s@, ds, members@[g2]@, names@[g2]@, &#[trigger] nidx@[g2], bound@[g2]@),
            decreases ng - g,
        {
            let m = &members[g];
            proof {
                assert(group_ok(s@, ds, grp@, g as int, m@, n as int));
            }
            let mut nm: Vec<XEnt> = Vec::new();
            let mut p: usize = 0;
            while p < m.len()
                invariant
                    p <= m@.len(),
                    m@ == members@[g as int]@,
                    incr(m@, n as int),
                    n == ds.len(),
                    ds == decls@,
                    decls_in(s@, ds),
                    nm@.len() == p,
                    forall|q: int| 0 <= q < p ==> #[trigger] nm@[q] == ent_of(ds[m@[q] as int].na, ds[m@[q] as int].nb),
                decreases m@.len() - p,
            {
                let d = decls[m[p]];
                nm.push(XEnt { a: d.na, b: d.nb, kind: 0, va: 0, vb: 0 });
                p = p + 1;
            }
            proof {
                assert forall|q: int| 0 <= q < nm@.len() implies (#[trigger] nm@[q]).a <= nm@[q].b <= s@.len() by {
                    assert(nm@[q] == ent_of(ds[m@[q] as int].na, ds[m@[q] as int].nb));
                    assert(m@[q] < n);
                    let jj = m@[q] as int;
                    assert(0 <= jj < ds.len());
                    assert(bounded(ds, s@.len() as int));
                    assert(ds[jj].na <= ds[jj].nb <= s@.len());
                }
                assert(m@.len() <= n) by {
                    lemma_incr_len(m@, n as int);
                }
            }
            let x = NameIndex::build(s, nm.as_slice());
            let mut b: Vec<usize> = Vec::new();
            let mut p: usize = 0;
            while p < m.len()
                invariant
                    p <= m@.len(),
                    names_of(ds, m@, nm@),
                    spans_in(s@, nm@),
                    indexes(&x, s@, nm@),
                    incr(b@, p as int),
                    forall|q: int| 0 <= q < p ==> (#[trigger] b@.contains(q as usize) == first_name(s@, nm@, q)),
                decreases m@.len() - p,
            {
                let e = nm[p];
                proof {
                    assert(nm@[p as int] == e);
                    assert(e.a <= e.b <= s@.len());
                }
                let f = find_first(&x, s, nm.as_slice(), s, e.a, e.b);
                let ghost ob = b@;
                let fp = f.unwrap();
                if fp == p {
                    b.push(p);
                    proof {
                        assert(first_name(s@, nm@, p as int)) by {
                            assert forall|q: int| 0 <= q < p implies sn(s@, #[trigger] nm@[q]) != sn(s@, nm@[p as int]) by {
                            }
                        }
                    }
                } else {
                    proof {
                        assert(fp < p);
                        assert(!first_name(s@, nm@, p as int)) by {
                            assert(sn(s@, nm@[fp as int]) == sn(s@, nm@[p as int]));
                        }
                    }
                }
                proof {
                    assert forall|q: int| 0 <= q < p + 1 implies (#[trigger] b@.contains(q as usize) == first_name(
                        s@,
                        nm@,
                        q,
                    )) by {
                        if q < p {
                            if fp == p {
                                assert(b@ == ob.push(p));
                                if ob.contains(q as usize) {
                                    let w = choose|w: int| 0 <= w < ob.len() && ob[w] == q as usize;
                                    assert(b@[w] == q as usize);
                                }
                                if b@.contains(q as usize) {
                                    let w = choose|w: int| 0 <= w < b@.len() && b@[w] == q as usize;
                                    if w < ob.len() {
                                        assert(ob[w] == q as usize);
                                    }
                                }
                            }
                        } else {
                            if fp == p {
                                assert(b@[ob.len() as int] == p);
                            } else {
                                assert(b@ == ob);
                                assert(!ob.contains(p as usize));
                            }
                        }
                    }
                }
                p = p + 1;
            }
            proof {
                assert(gtab_ok(s@, ds, m@, nm@, &x, b@));
            }
            names.push(nm);
            nidx.push(x);
            bound.push(b);
            proof {
                assert forall|g2: int|
                    0 <= g2 < g + 1 implies gtab_ok(s@, ds, members@[g2]@, names@[g2]@, &#[trigger] nidx@[g2], bound@[g2]@) by {
                }
            }
            g = g + 1;
        }
        let r = AttTable { decls, eix, eidx, grp, members, names, nidx, bound };
        r
    }

    /// The group of the element type `q[a..b]`, if a definition is for it.
    pub fn group_of(&self, s: &[u8], q: &[u8], a: usize, b: usize) -> (r: Option<usize>)
        requires
            table_ok(s@, self),
            a <= b <= q@.len(),
        ensures
            match r {
                Some(g) => g < self.members@.len() && forall|j: int|
                    0 <= j < self.decls@.len() ==> ((en(s@, #[trigger] self.decls@[j]) == q@.subrange(a as int, b as int))
                        == (self.grp@[j] == g)),
                None => forall|j: int|
                    0 <= j < self.decls@.len() ==> en(s@, #[trigger] self.decls@[j]) != q@.subrange(a as int, b as int),
            },
    {
        let ghost ds = self.decls@;
        let ghost qn = q@.subrange(a as int, b as int);
        match find_first(&self.eidx, s, self.eix.as_slice(), q, a, b) {
            Some(r) => {
                let g = self.grp[r];
                proof {
                    assert(self.eix@[r as int] == ent_of(ds[r as int].ea, ds[r as int].eb));
                    assert(en(s@, ds[r as int]) == qn);
                    assert forall|j: int| 0 <= j < ds.len() implies ((en(s@, #[trigger] ds[j]) == qn) == (self.grp@[j]
                        == g)) by {
                        assert(self.grp@[j] == self.grp@[r as int] <==> en(s@, ds[j]) == en(s@, ds[r as int]));
                    }
                }
                Some(g)
            },
            None => {
                proof {
                    assert forall|j: int| 0 <= j < ds.len() implies en(s@, #[trigger] ds[j]) != qn by {
                        assert(self.eix@[j] == ent_of(ds[j].ea, ds[j].eb));
                        assert(sn(s@, self.eix@[j]) != qn);
                    }
                }
                None
            },
        }
    }

    /// The binding definition of the attribute `y[c..d]` of the element
    /// type `q[a..b]`: the first definition for both (§3.3).
    pub fn def_for(&self, s: &[u8], q: &[u8], a: usize, b: usize, y: &[u8], c: usize, d: usize) -> (r: Option<usize>)
        requires
            table_ok(s@, self),
            a <= b <= q@.len(),
            c <= d <= y@.len(),
        ensures
            match r {
                Some(j) => j < self.decls@.len() && en(s@, self.decls@[j as int]) == q@.subrange(a as int, b as int)
                    && an(s@, self.decls@[j as int]) == y@.subrange(c as int, d as int) && forall|k: int|
                    0 <= k < j ==> !(en(s@, #[trigger] self.decls@[k]) == q@.subrange(a as int, b as int) && an(
                        s@,
                        self.decls@[k],
                    ) == y@.subrange(c as int, d as int)),
                None => forall|k: int|
                    0 <= k < self.decls@.len() ==> !(en(s@, #[trigger] self.decls@[k]) == q@.subrange(a as int, b as int)
                        && an(s@, self.decls@[k]) == y@.subrange(c as int, d as int)),
            },
    {
        let ghost ds = self.decls@;
        let ghost qe = q@.subrange(a as int, b as int);
        let ghost qn = y@.subrange(c as int, d as int);
        let n = self.decls.len();
        let g = match self.group_of(s, q, a, b) {
            Some(g) => g,
            None => {
                return None;
            },
        };
        let m = &self.members[g];
        proof {
            assert(gtab_ok(s@, ds, m@, self.names@[g as int]@, &self.nidx@[g as int], self.bound@[g as int]@));
            assert(group_ok(s@, ds, self.grp@, g as int, m@, n as int));
        }
        let nm = &self.names[g];
        match find_first(&self.nidx[g], s, nm.as_slice(), y, c, d) {
            Some(p) => {
                let j = m[p];
                proof {
                    assert(nm@[p as int] == ent_of(ds[j as int].na, ds[j as int].nb));
                    assert(self.grp@[j as int] == g);
                    assert forall|k: int| 0 <= k < j implies !(en(s@, #[trigger] ds[k]) == qe && an(s@, ds[k]) == qn) by {
                        if en(s@, ds[k]) == qe && an(s@, ds[k]) == qn {
                            assert(self.grp@[k] == g);
                            assert(m@.contains(k as usize));
                            lemma_incr_contains(m@, n as int, p as int, k as usize);
                            let w = choose|w: int| 0 <= w < p && m@[w] == k as usize;
                            assert(nm@[w] == ent_of(ds[k].na, ds[k].nb));
                            assert(sn(s@, nm@[w]) == qn);
                        }
                    }
                }
                Some(j)
            },
            None => {
                proof {
                    assert forall|k: int| 0 <= k < n implies !(en(s@, #[trigger] ds[k]) == qe && an(s@, ds[k]) == qn) by {
                        if en(s@, ds[k]) == qe && an(s@, ds[k]) == qn {
                            assert(self.grp@[k] == g);
                            assert(m@.contains(k as usize));
                            let w = choose|w: int| 0 <= w < m@.len() && m@[w] == k as usize;
                            assert(nm@[w] == ent_of(ds[k].na, ds[k].nb));
                            assert(sn(s@, nm@[w]) == qn);
                        }
                    }
                }
                None
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The defaults an element gets
// ---------------------------------------------------------------------------

/// The names of the attributes a start tag gives: its `Attr` tokens from
/// `i` on, each followed by its value, whose spans are in `buf`.
pub open spec fn tag_names(buf: Seq<u8>, t: Seq<Tok>, i: int) -> Seq<Seq<u8>>
    decreases t.len() - i,
{
    if 0 <= i && i + 1 < t.len() && t[i].kind is Attr {
        (if in_text(t[i], buf.len() as int) {
            seq![buf.subrange(t[i].sa(), t[i].sb())]
        } else {
            Seq::empty()
        }) + tag_names(buf, t, i + 2)
    } else {
        Seq::empty()
    }
}

/// §3.3.2: definition `j` gives a default to an element of type `qe`
/// whose start tag's attributes are `tag_names(buf, t, first)`: it binds,
/// it is for `qe`, it has a default value (`#FIXED` or not), and the start
/// tag does not give the attribute.
pub open spec fn is_default(s: Seq<u8>, ds: Seq<ADecl>, qe: Seq<u8>, buf: Seq<u8>, t: Seq<Tok>, first: int, j: int) -> bool {
    &&& 0 <= j < ds.len()
    &&& en(s, ds[j]) == qe
    &&& binding(s, ds, j)
    &&& ds[j].kind >= 3
    &&& !tag_names(buf, t, first).contains(an(s, ds[j]))
}

proof fn lemma_contains_cat(x: Seq<Seq<u8>>, y: Seq<Seq<u8>>, e: Seq<u8>)
    ensures
        (x + y).contains(e) == (x.contains(e) || y.contains(e)),
{
    if (x + y).contains(e) {
        let w = choose|w: int| 0 <= w < (x + y).len() && (x + y)[w] == e;
        if w < x.len() {
            assert(x[w] == e);
        } else {
            assert(y[w - x.len()] == e);
        }
    }
    if x.contains(e) {
        let w = choose|w: int| 0 <= w < x.len() && x[w] == e;
        assert((x + y)[w] == e);
    }
    if y.contains(e) {
        let w = choose|w: int| 0 <= w < y.len() && y[w] == e;
        assert((x + y)[w + x.len()] == e);
    }
}

/// Whether the start tag's attributes from `first` on give `s[a..b]`:
/// `tag_names(buf, t, first).contains(s[a..b])`.
pub fn ex_tag_has(buf: &[u8], t: &[Tok], first: usize, s: &[u8], a: usize, b: usize) -> (r: bool)
    requires
        a <= b <= s@.len(),
    ensures
        r == tag_names(buf@, t@, first as int).contains(s@.subrange(a as int, b as int)),
{
    let ghost x = s@.subrange(a as int, b as int);
    let mut i = first;
    while i < t.len() && i + 1 < t.len() && is_attr(t[i].kind)
        invariant
            first <= i,
            a <= b <= s@.len(),
            x == s@.subrange(a as int, b as int),
            tag_names(buf@, t@, first as int).contains(x) == tag_names(buf@, t@, i as int).contains(x),
        decreases t@.len() - i,
    {
        let k = t[i];
        proof {
            assert(t@[i as int] == k);
        }
        let ghost h = if in_text(k, buf@.len() as int) {
            seq![buf@.subrange(k.sa(), k.sb())]
        } else {
            Seq::<Seq<u8>>::empty()
        };
        proof {
            assert(tag_names(buf@, t@, i as int) == h + tag_names(buf@, t@, i + 2));
            lemma_contains_cat(h, tag_names(buf@, t@, i + 2), x);
        }
        if let Some((ka, kb)) = span_of(k, buf.len()) {
            if ex_bytes_eq(buf, ka, kb, s, a, b) {
                proof {
                    assert(h[0] == x);
                }
                return true;
            }
            proof {
                assert(!h.contains(x)) by {
                    if h.contains(x) {
                        let w = choose|w: int| 0 <= w < h.len() && h[w] == x;
                        assert(w == 0);
                    }
                }
            }
        }
        i = i + 2;
    }
    proof {
        assert(tag_names(buf@, t@, i as int) =~= Seq::<Seq<u8>>::empty());
    }
    false
}

impl AttTable {
    /// The defaults an element of type `buf[a..b]` gets, whose start
    /// tag's attributes are the `Attr` tokens of `t` from `first` on: the
    /// definitions `is_default`, in declaration order. Linear in the
    /// tag's attributes and the element type's definitions.
    pub fn ex_defaults(&self, s: &[u8], buf: &[u8], t: &[Tok], first: usize, a: usize, b: usize) -> (r: Vec<usize>)
        requires
            table_ok(s@, self),
            a <= b <= buf@.len(),
        ensures
            incr(r@, self.decls@.len() as int),
            forall|p: int|
                0 <= p < r@.len() ==> is_default(
                    s@,
                    self.decls@,
                    buf@.subrange(a as int, b as int),
                    buf@,
                    t@,
                    first as int,
                    #[trigger] r@[p] as int,
                ),
            forall|j: int|
                is_default(s@, self.decls@, buf@.subrange(a as int, b as int), buf@, t@, first as int, j) ==> #[trigger] r@.contains(
                    j as usize,
                ),
    {
        let ghost ds = self.decls@;
        let ghost qe = buf@.subrange(a as int, b as int);
        let ghost tn = tag_names(buf@, t@, first as int);
        let n = self.decls.len();
        let mut out: Vec<usize> = Vec::new();
        let g = match self.group_of(s, buf, a, b) {
            Some(g) => g,
            None => {
                proof {
                    assert forall|j: int| is_default(s@, ds, qe, buf@, t@, first as int, j) implies #[trigger] out@.contains(
                        j as usize,
                    ) by {
                        assert(en(s@, ds[j]) != qe);
                    }
                }
                return out;
            },
        };
        let m = &self.members[g];
        let nm = &self.names[g];
        let x = &self.nidx[g];
        let bd = &self.bound[g];
        proof {
            assert(gtab_ok(s@, ds, m@, nm@, x, bd@));
            assert(group_ok(s@, ds, self.grp@, g as int, m@, n as int));
        }
        // marks[p]: member p is the first of its name, and the tag gives it.
        let mut marks: Vec<bool> = Vec::new();
        while marks.len() < m.len()
            invariant
                marks@.len() <= m@.len(),
                forall|p: int| 0 <= p < marks@.len() ==> !(#[trigger] marks@[p]),
            decreases m@.len() - marks@.len(),
        {
            marks.push(false);
        }
        let ghost mut done: Seq<Seq<u8>> = Seq::empty();
        let mut i = first;
        while i < t.len() && i + 1 < t.len() && is_attr(t[i].kind)
            invariant
                first <= i,
                table_ok(s@, self),
                ds == self.decls@,
                marks@.len() == m@.len(),
                gtab_ok(s@, ds, m@, nm@, x, bd@),
                done + tag_names(buf@, t@, i as int) == tn,
                forall|p: int|
                    0 <= p < m@.len() ==> #[trigger] marks@[p] == (first_name(s@, nm@, p) && done.contains(sn(s@, nm@[p]))),
            decreases t@.len() - i,
        {
            let k = t[i];
            proof {
                assert(t@[i as int] == k);
            }
            let ghost h = if in_text(k, buf@.len() as int) {
                seq![buf@.subrange(k.sa(), k.sb())]
            } else {
                Seq::<Seq<u8>>::empty()
            };
            proof {
                assert(tag_names(buf@, t@, i as int) == h + tag_names(buf@, t@, i + 2));
                assert(done + h + tag_names(buf@, t@, i + 2) =~= done + tag_names(buf@, t@, i as int));
            }
            if let Some((ka, kb)) = span_of(k, buf.len()) {
                let ghost name = buf@.subrange(ka as int, kb as int);
                let ghost om = marks@;
                match find_first(x, s, nm.as_slice(), buf, ka, kb) {
                    Some(p0) => {
                        marks.set(p0, true);
                        proof {
                            assert forall|p: int|
                                0 <= p < m@.len() implies #[trigger] marks@[p] == (first_name(s@, nm@, p) && (done + h).contains(
                                sn(s@, nm@[p]),
                            )) by {
                                lemma_contains_cat(done, h, sn(s@, nm@[p]));
                                assert(h[0] == name);
                                assert(h.contains(sn(s@, nm@[p])) == (sn(s@, nm@[p]) == name)) by {
                                    if h.contains(sn(s@, nm@[p])) {
                                        let w = choose|w: int| 0 <= w < h.len() && h[w] == sn(s@, nm@[p]);
                                        assert(w == 0);
                                    }
                                }
                                if p == p0 {
                                    assert(first_name(s@, nm@, p));
                                } else {
                                    assert(marks@[p] == om[p]);
                                    if sn(s@, nm@[p]) == name && first_name(s@, nm@, p) {
                                        if p < p0 {
                                            assert(sn(s@, nm@[p]) != name);
                                        } else {
                                            assert(sn(s@, nm@[p0 as int]) != sn(s@, nm@[p]));
                                        }
                                    }
                                }
                            }
                        }
                    },
                    None => {
                        proof {
                            assert forall|p: int|
                                0 <= p < m@.len() implies #[trigger] marks@[p] == (first_name(s@, nm@, p) && (done + h).contains(
                                sn(s@, nm@[p]),
                            )) by {
                                lemma_contains_cat(done, h, sn(s@, nm@[p]));
                                assert(h[0] == name);
                                if h.contains(sn(s@, nm@[p])) {
                                    let w = choose|w: int| 0 <= w < h.len() && h[w] == sn(s@, nm@[p]);
                                    assert(w == 0);
                                }
                            }
                        }
                    },
                }
            } else {
                proof {
                    assert(h =~= Seq::<Seq<u8>>::empty());
                    assert(done + h =~= done);
                }
            }
            proof {
                done = done + h;
            }
            i = i + 2;
        }
        proof {
            assert(tag_names(buf@, t@, i as int) =~= Seq::<Seq<u8>>::empty());
            assert(done =~= tn);
        }
        // The members that bind and have a default value, unmarked.
        let mut k: usize = 0;
        while k < bd.len()
            invariant
                k <= bd@.len(),
                n == ds.len(),
                tn == tag_names(buf@, t@, first as int),
                qe == buf@.subrange(a as int, b as int),
                a <= b <= buf@.len(),
                table_ok(s@, self),
                ds == self.decls@,
                marks@.len() == m@.len(),
                gtab_ok(s@, ds, m@, nm@, x, bd@),
                group_ok(s@, ds, self.grp@, g as int, m@, n as int),
                grouped(s@, ds, self.grp@, self.members@, n as int),
                m@ == self.members@[g as int]@,
                (g as int) < self.members@.len(),
                forall|j: int| 0 <= j < ds.len() ==> ((en(s@, #[trigger] ds[j]) == qe) == (self.grp@[j] == g)),
                forall|p: int|
                    0 <= p < m@.len() ==> #[trigger] marks@[p] == (first_name(s@, nm@, p) && tn.contains(sn(s@, nm@[p]))),
                forall|q: int| 0 <= q < out@.len() ==> is_default(s@, ds, qe, buf@, t@, first as int, #[trigger] out@[q] as int),
                forall|q: int| 0 <= q < out@.len() && k < bd@.len() ==> #[trigger] out@[q] < m@[bd@[k as int] as int],
                incr(out@, n as int),
                forall|k2: int|
                    0 <= k2 < k && is_default(s@, ds, qe, buf@, t@, first as int, m@[#[trigger] bd@[k2] as int] as int)
                        ==> out@.contains(m@[bd@[k2] as int]),
            decreases bd@.len() - k,
        {
            let p = bd[k];
            let j = m[p];
            let ghost oo = out@;
            proof {
                assert(bd@[k as int] < m@.len());
                assert(j < n);
                assert(self.grp@[j as int] == g);
                assert(bd@.contains(p));
                assert(bd@.contains(p as int as usize));
                lemma_binding_first(s@, ds, self.grp@, self.members@, n as int, g as int, nm@, p as int);
                assert(names_of(ds, m@, nm@));
                assert(nm@[p as int] == ent_of(ds[j as int].na, ds[j as int].nb));
                assert(sn(s@, nm@[p as int]) == an(s@, ds[j as int]));
            }
            if self.decls[j].kind >= 3 && !marks[p] {
                out.push(j);
            }
            proof {
                let jj = j as int;
                assert(en(s@, ds[jj]) == qe);
                assert(first_name(s@, nm@, p as int));
                assert(binding(s@, ds, jj));
                assert(marks@[p as int] == tn.contains(an(s@, ds[jj])));
                assert(0 <= jj < ds.len());
                if ds[jj].kind >= 3 && !marks@[p as int] {
                    assert(!tn.contains(an(s@, ds[jj])));
                    assert(!tag_names(buf@, t@, first as int).contains(an(s@, ds[jj])));
                    assert(ds[jj].kind >= 3);
                    assert(binding(s@, ds, jj));
                    assert(en(s@, ds[jj]) == qe);
                    assert(qe == buf@.subrange(a as int, b as int));
                    assert(is_default(s@, ds, qe, buf@, t@, first as int, jj));
                }
                assert(is_default(s@, ds, qe, buf@, t@, first as int, jj) == (ds[jj].kind >= 3 && !marks@[p as int]));
                if k + 1 < bd@.len() {
                    assert(bd@[k as int] < bd@[k + 1]);
                    assert(m@[bd@[k as int] as int] < m@[bd@[k + 1] as int]);
                }
                assert forall|q: int| 0 <= q < out@.len() && k + 1 < bd@.len() implies #[trigger] out@[q] < m@[bd@[k + 1] as int] by {
                    if q < oo.len() {
                        assert(out@[q] == oo[q]);
                    }
                }
                assert forall|q1: int, q2: int| 0 <= q1 < q2 < out@.len() implies out@[q1] < out@[q2] by {
                    if q2 < oo.len() {
                        assert(out@[q1] == oo[q1] && out@[q2] == oo[q2]);
                    } else {
                        assert(out@[q1] == oo[q1]);
                    }
                }
                assert forall|q: int| 0 <= q < out@.len() implies is_default(s@, ds, qe, buf@, t@, first as int, #[trigger] out@[q] as int) by {
                    if q < oo.len() {
                        assert(out@[q] == oo[q]);
                    }
                }
                assert forall|k2: int|
                    0 <= k2 < k + 1 && is_default(s@, ds, qe, buf@, t@, first as int, m@[#[trigger] bd@[k2] as int] as int)
                        implies out@.contains(m@[bd@[k2] as int]) by {
                    if k2 < k {
                        let w = choose|w: int| 0 <= w < oo.len() && oo[w] == m@[bd@[k2] as int];
                        assert(out@[w] == oo[w]);
                    } else {
                        assert(out@[oo.len() as int] == j);
                    }
                }
            }
            k = k + 1;
        }
        proof {
            assert forall|j: int| is_default(s@, ds, qe, buf@, t@, first as int, j) implies #[trigger] out@.contains(
                j as usize,
            ) by {
                assert(self.grp@[j] == g);
                assert(m@.contains(j as usize));
                let p = choose|p: int| 0 <= p < m@.len() && m@[p] == j as usize;
                lemma_binding_first(s@, ds, self.grp@, self.members@, n as int, g as int, nm@, p);
                assert(bd@.contains(p as usize));
                let k2 = choose|k2: int| 0 <= k2 < bd@.len() && bd@[k2] == p as usize;
                assert(m@[bd@[k2] as int] == j);
            }
        }
        out
    }

    /// The next default from `k` on in the list of binding definitions of
    /// group `g`, the group of the element type `buf[a..b]`
    /// (`group_of`): the definition, and where to go on from. Without
    /// allocating; each candidate is checked against the start tag's
    /// attributes one by one.
    pub fn next_default(
        &self,
        s: &[u8],
        buf: &[u8],
        t: &[Tok],
        first: usize,
        a: usize,
        b: usize,
        g: usize,
        k: usize,
    ) -> (r: Option<(usize, usize)>)
        requires
            table_ok(s@, self),
            a <= b <= buf@.len(),
            g < self.members@.len(),
            forall|j: int|
                0 <= j < self.decls@.len() ==> ((en(s@, #[trigger] self.decls@[j]) == buf@.subrange(a as int, b as int))
                    == (self.grp@[j] == g)),
        ensures
            match r {
                Some((j, k2)) => k < k2 <= self.bound@[g as int]@.len() && j == self.members@[g as int]@[self.bound@[g as int]@[k2 - 1] as int] && is_default(
                    s@,
                    self.decls@,
                    buf@.subrange(a as int, b as int),
                    buf@,
                    t@,
                    first as int,
                    j as int,
                ) && forall|k3: int|
                    k <= k3 < k2 - 1 ==> !is_default(
                        s@,
                        self.decls@,
                        buf@.subrange(a as int, b as int),
                        buf@,
                        t@,
                        first as int,
                        self.members@[g as int]@[#[trigger] self.bound@[g as int]@[k3] as int] as int,
                    ),
                None => forall|k3: int|
                    k <= k3 < self.bound@[g as int]@.len() ==> !is_default(
                        s@,
                        self.decls@,
                        buf@.subrange(a as int, b as int),
                        buf@,
                        t@,
                        first as int,
                        self.members@[g as int]@[#[trigger] self.bound@[g as int]@[k3] as int] as int,
                    ),
            },
    {
        let ghost ds = self.decls@;
        let ghost qe = buf@.subrange(a as int, b as int);
        let n = self.decls.len();
        let m = &self.members[g];
        let nm = &self.names[g];
        let bd = &self.bound[g];
        proof {
            assert(gtab_ok(s@, ds, m@, nm@, &self.nidx@[g as int], bd@));
            assert(group_ok(s@, ds, self.grp@, g as int, m@, n as int));
        }
        let mut k2 = k;
        while k2 < bd.len()
            invariant
                k <= k2,
                n == ds.len(),
                qe == buf@.subrange(a as int, b as int),
                a <= b <= buf@.len(),
                table_ok(s@, self),
                ds == self.decls@,
                m@ == self.members@[g as int]@,
                nm@ == self.names@[g as int]@,
                bd@ == self.bound@[g as int]@,
                (g as int) < self.members@.len(),
                gtab_ok(s@, ds, m@, nm@, &self.nidx@[g as int], bd@),
                group_ok(s@, ds, self.grp@, g as int, m@, n as int),
                grouped(s@, ds, self.grp@, self.members@, n as int),
                forall|j: int| 0 <= j < ds.len() ==> ((en(s@, #[trigger] ds[j]) == qe) == (self.grp@[j] == g)),
                forall|k3: int|
                    k <= k3 < k2 ==> !is_default(s@, ds, qe, buf@, t@, first as int, m@[#[trigger] bd@[k3] as int] as int),
            decreases bd@.len() - k2,
        {
            let p = bd[k2];
            let j = m[p];
            let d = self.decls[j];
            proof {
                assert(bd@[k2 as int] < m@.len());
                assert(j < n);
                assert(self.grp@[j as int] == g);
                assert(bd@.contains(p));
                assert(bd@.contains(p as int as usize));
                lemma_binding_first(s@, ds, self.grp@, self.members@, n as int, g as int, nm@, p as int);
                assert(bounded(ds, s@.len() as int));
                assert(ds[j as int].na <= ds[j as int].nb <= s@.len());
            }
            if d.kind >= 3 && !ex_tag_has(buf, t, first, s, d.na, d.nb) {
                proof {
                    assert(en(s@, ds[j as int]) == qe);
                    assert(first_name(s@, nm@, p as int));
                    assert(binding(s@, ds, j as int));
                    assert(is_default(s@, ds, qe, buf@, t@, first as int, j as int));
                    assert forall|k3: int|
                        k <= k3 < k2 implies !is_default(
                            s@,
                            ds,
                            qe,
                            buf@,
                            t@,
                            first as int,
                            self.members@[g as int]@[#[trigger] self.bound@[g as int]@[k3] as int] as int,
                        ) by {
                        assert(bd@[k3] == self.bound@[g as int]@[k3]);
                    }
                }
                return Some((j, k2 + 1));
            }
            proof {
                assert(!is_default(s@, ds, qe, buf@, t@, first as int, m@[bd@[k2 as int] as int] as int));
            }
            k2 = k2 + 1;
        }
        proof {
            assert forall|k3: int|
                k <= k3 < self.bound@[g as int]@.len() implies !is_default(
                    s@,
                    ds,
                    qe,
                    buf@,
                    t@,
                    first as int,
                    self.members@[g as int]@[#[trigger] self.bound@[g as int]@[k3] as int] as int,
                ) by {
                assert(bd@[k3] == self.bound@[g as int]@[k3]);
            }
        }
        None
    }
}

proof fn lemma_incr_len(v: Seq<usize>, n: int)
    requires
        incr(v, n),
    ensures
        v.len() <= if n > 0 { n } else { 0 },
    decreases v.len(),
{
    if v.len() > 0 {
        let w = v.drop_last();
        assert forall|p: int, q: int| 0 <= p < q < w.len() implies w[p] < w[q] by {
            assert(w[p] == v[p] && w[q] == v[q]);
        }
        assert forall|p: int| 0 <= p < w.len() implies w[p] < v.last() by {
            assert(w[p] == v[p]);
            assert(v[p] < v[v.len() - 1]);
        }
        lemma_incr_len(w, v.last() as int);
    }
}

/// Each definition takes two tokens.
proof fn lemma_decls_len(n: int, t: Seq<Tok>, sa: bool, i: int, skip: bool, el: Option<Tok>)
    requires
        0 <= i,
    ensures
        decls_from(n, t, sa, i, skip, el).len() <= if i < t.len() {
            t.len() - i
        } else {
            0
        },
    decreases t.len() - i,
{
    if 0 <= i < t.len() && !(t[i].kind is DoctypeEnd) {
        if t[i].kind is PERef {
            lemma_decls_len(n, t, sa, i + 1, skip || !sa, el);
        } else if t[i].kind is AttlistDecl {
            lemma_decls_len(n, t, sa, i + 1, skip, Some(t[i]));
        } else if t[i].kind is AttDef && !skip && i + 1 < t.len() {
            lemma_decls_len(n, t, sa, i + 2, skip, el);
        } else {
            lemma_decls_len(n, t, sa, i + 1, skip, el);
        }
    }
}

} // verus!
