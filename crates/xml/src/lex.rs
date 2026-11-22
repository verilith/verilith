//! Verified code for the lexical layer of the grammar: white space,
//! literals, references, attribute and entity values, comments, processing
//! instructions, CDATA sections, character data and `Misc`. Each function
//! is proven to return exactly what the spec function of the same name
//! (without `ex_`) returns, never to panic, and to terminate.
use crate::chars::*;
use crate::scan::*;
use crate::spec::*;
use crate::tape::*;
pub use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The environment
// ---------------------------------------------------------------------------

/// A processed general entity declaration: the name's span, the kind (0
/// internal, 1 external, 2 unparsed) and an internal entity's literal
/// value's span.
#[derive(Clone, Copy, Debug)]
pub struct XEnt {
    pub a: u32,
    pub b: u32,
    pub kind: u8,
    pub va: u32,
    pub vb: u32,
}

pub open spec fn kind_view(e: XEnt) -> EKind {
    if e.kind == 0 {
        EKind::Internal { start: e.va as int, end: e.vb as int }
    } else if e.kind == 1 {
        EKind::External
    } else {
        EKind::Unparsed
    }
}

pub open spec fn ent_view(s: Seq<u8>, e: XEnt) -> Ent {
    Ent { name: s.subrange(e.a as int, e.b as int), kind: kind_view(e) }
}

pub open spec fn ents_view(s: Seq<u8>, es: Seq<XEnt>) -> Seq<Ent> {
    es.map_values(|e: XEnt| ent_view(s, e))
}

pub open spec fn ents_wf(s: Seq<u8>, es: Seq<XEnt>) -> bool {
    forall|k: int|
        #![trigger es[k]]
        0 <= k < es.len() ==> es[k].a <= es[k].b <= s.len() && es[k].kind <= 2 && es[k].va <= es[k].vb
            <= s.len()
}

/// The environment of the content: the document (where entity names
/// are), its processed general entities, and the flags of `Env`.
pub struct XEnv<'a> {
    pub doc: &'a [u8],
    pub ents: &'a [XEnt],
    pub wfc: bool,
    pub oka: &'a [bool],
    pub okc: &'a [bool],
    /// The entities by name.
    pub idx: &'a crate::index::NameIndex,
}

pub open spec fn env_view(e: &XEnv) -> Env {
    Env { ents: ents_view(e.doc@, e.ents@), wfc: e.wfc, oka: e.oka@, okc: e.okc@ }
}

pub open spec fn env_wf(e: &XEnv) -> bool {
    ents_wf(e.doc@, e.ents@) && crate::index::indexes(e.idx, e.doc@, e.ents@)
}

/// The environment of the first `lim` entities.
pub open spec fn lim_view(e: &XEnv, lim: int) -> Env {
    Env { ents: ents_view(e.doc@, e.ents@).subrange(0, lim), wfc: e.wfc, oka: e.oka@, okc: e.okc@ }
}

pub open spec fn oenv_view(e: Option<&XEnv>, lim: int) -> Option<Env> {
    match e {
        Some(e) => Some(lim_view(e, lim)),
        None => None,
    }
}

pub open spec fn oenv_wf(e: Option<&XEnv>, lim: int) -> bool {
    match e {
        Some(e) => env_wf(e) && 0 <= lim <= e.ents@.len(),
        None => true,
    }
}

/// The whole environment is its first `ents.len()` entities.
pub proof fn lemma_lim_all(e: &XEnv)
    ensures
        lim_view(e, e.ents@.len() as int) == env_view(e),
{
    assert(ents_view(e.doc@, e.ents@).subrange(0, e.ents@.len() as int) =~= ents_view(e.doc@, e.ents@));
}

/// The executable result `r` is the spec result `e`.
pub open spec fn same(r: Option<usize>, e: Option<int>) -> bool {
    match e {
        Some(e) => r matches Some(x) && x as int == e,
        None => r is None,
    }
}

// ---------------------------------------------------------------------------
// Bytes, white space and literals
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn ex_byte_is(s: &[u8], i: usize, c: u8) -> (r: bool)
    ensures
        r == byte_is(s@, i as int, c),
{
    i < s.len() && get(s, i) == c
}

/// `ws_end`.
#[inline(always)]
pub fn ex_ws_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r == ws_end(s@, i as int),
        i <= r <= s@.len(),
{
    let n = s.len();
    let mut j = i;
    while j < n && ex_is_ws(get(s, j))
        invariant
            i <= j <= n,
            n == s@.len(),
            ws_end(s@, j as int) == ws_end(s@, i as int),
        decreases n - j,
    {
        j = j + 1;
    }
    j
}

pub proof fn lemma_ws_end(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= ws_end(s, i) <= s.len(),
        ws_end(s, i) < s.len() ==> !is_ws(s[ws_end(s, i)]),
    decreases s.len() - i,
{
    if i < s.len() && is_ws(s[i]) {
        lemma_ws_end(s, i + 1);
    }
}

/// `has_lit` for a literal given as a slice.
pub fn ex_has_lit(s: &[u8], i: usize, lit: &[u8]) -> (r: bool)
    ensures
        r == has_lit(s@, i as int, lit@),
{
    let n = s.len();
    let l = lit.len();
    if i > n || l > n - i {
        return false;
    }
    let mut k: usize = 0;
    while k < l
        invariant
            i + l <= n,
            n == s@.len(),
            l == lit@.len(),
            k <= l,
            s@.subrange(i as int, i + k) =~= lit@.subrange(0, k as int),
        decreases l - k,
    {
        if get(s, i + k) != lit[k] {
            proof {
                assert(s@.subrange(i as int, i + l)[k as int] != lit@[k as int]);
            }
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(lit@.subrange(0, l as int) =~= lit@);
    }
    true
}

pub const L_XMLDECL: [u8; 5] = [0x3C, 0x3F, 0x78, 0x6D, 0x6C];
pub const L_VERSION: [u8; 7] = [0x76, 0x65, 0x72, 0x73, 0x69, 0x6F, 0x6E];
pub const L_ENCODING: [u8; 8] = [0x65, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67];
pub const L_STANDALONE: [u8; 10] = [0x73, 0x74, 0x61, 0x6E, 0x64, 0x61, 0x6C, 0x6F, 0x6E, 0x65];
pub const L_YES: [u8; 3] = [0x79, 0x65, 0x73];
pub const L_NO: [u8; 2] = [0x6E, 0x6F];
pub const L_COMMENT: [u8; 4] = [0x3C, 0x21, 0x2D, 0x2D];
pub const L_CDATA: [u8; 9] = [0x3C, 0x21, 0x5B, 0x43, 0x44, 0x41, 0x54, 0x41, 0x5B];
pub const L_DOCTYPE: [u8; 9] = [0x3C, 0x21, 0x44, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45];
pub const L_SYSTEM: [u8; 6] = [0x53, 0x59, 0x53, 0x54, 0x45, 0x4D];
pub const L_PUBLIC: [u8; 6] = [0x50, 0x55, 0x42, 0x4C, 0x49, 0x43];
pub const L_ELEMENT: [u8; 9] = [0x3C, 0x21, 0x45, 0x4C, 0x45, 0x4D, 0x45, 0x4E, 0x54];
pub const L_ATTLIST: [u8; 9] = [0x3C, 0x21, 0x41, 0x54, 0x54, 0x4C, 0x49, 0x53, 0x54];
pub const L_ENTITY: [u8; 8] = [0x3C, 0x21, 0x45, 0x4E, 0x54, 0x49, 0x54, 0x59];
pub const L_NOTATION: [u8; 10] = [0x3C, 0x21, 0x4E, 0x4F, 0x54, 0x41, 0x54, 0x49, 0x4F, 0x4E];
pub const L_NDATA: [u8; 5] = [0x4E, 0x44, 0x41, 0x54, 0x41];
pub const L_EMPTY: [u8; 5] = [0x45, 0x4D, 0x50, 0x54, 0x59];
pub const L_ANY: [u8; 3] = [0x41, 0x4E, 0x59];
pub const L_PCDATA: [u8; 7] = [0x23, 0x50, 0x43, 0x44, 0x41, 0x54, 0x41];
pub const L_REQUIRED: [u8; 9] = [0x23, 0x52, 0x45, 0x51, 0x55, 0x49, 0x52, 0x45, 0x44];
pub const L_IMPLIED: [u8; 8] = [0x23, 0x49, 0x4D, 0x50, 0x4C, 0x49, 0x45, 0x44];
pub const L_FIXED: [u8; 6] = [0x23, 0x46, 0x49, 0x58, 0x45, 0x44];
pub const L_CDATA_TY: [u8; 5] = [0x43, 0x44, 0x41, 0x54, 0x41];
pub const L_IDREFS: [u8; 6] = [0x49, 0x44, 0x52, 0x45, 0x46, 0x53];
pub const L_IDREF: [u8; 5] = [0x49, 0x44, 0x52, 0x45, 0x46];
pub const L_ID: [u8; 2] = [0x49, 0x44];
pub const L_ENTITIES: [u8; 8] = [0x45, 0x4E, 0x54, 0x49, 0x54, 0x49, 0x45, 0x53];
pub const L_ENTITY_TY: [u8; 6] = [0x45, 0x4E, 0x54, 0x49, 0x54, 0x59];
pub const L_NMTOKENS: [u8; 8] = [0x4E, 0x4D, 0x54, 0x4F, 0x4B, 0x45, 0x4E, 0x53];
pub const L_NMTOKEN: [u8; 7] = [0x4E, 0x4D, 0x54, 0x4F, 0x4B, 0x45, 0x4E];
pub const L_NOTATION_TY: [u8; 8] = [0x4E, 0x4F, 0x54, 0x41, 0x54, 0x49, 0x4F, 0x4E];

/// The literal constants are the spec's literals.
pub proof fn lemma_lits()
    ensures
        L_XMLDECL@ == lit_xmldecl(),
        L_VERSION@ == lit_version(),
        L_ENCODING@ == lit_encoding(),
        L_STANDALONE@ == lit_standalone(),
        L_YES@ == lit_yes(),
        L_NO@ == lit_no(),
        L_COMMENT@ == lit_comment(),
        L_CDATA@ == lit_cdata(),
        L_DOCTYPE@ == lit_doctype(),
        L_SYSTEM@ == lit_system(),
        L_PUBLIC@ == lit_public(),
        L_ELEMENT@ == lit_element(),
        L_ATTLIST@ == lit_attlist(),
        L_ENTITY@ == lit_entity(),
        L_NOTATION@ == lit_notation(),
        L_NDATA@ == lit_ndata(),
        L_EMPTY@ == lit_empty(),
        L_ANY@ == lit_any(),
        L_PCDATA@ == lit_pcdata(),
        L_REQUIRED@ == lit_required(),
        L_IMPLIED@ == lit_implied(),
        L_FIXED@ == lit_fixed(),
        L_CDATA_TY@ == lit_cdata_ty(),
        L_IDREFS@ == lit_idrefs(),
        L_IDREF@ == lit_idref(),
        L_ID@ == lit_id(),
        L_ENTITIES@ == lit_entities(),
        L_ENTITY_TY@ == lit_entity_ty(),
        L_NMTOKENS@ == lit_nmtokens(),
        L_NMTOKEN@ == lit_nmtoken(),
        L_NOTATION_TY@ == lit_notation_ty(),
{
    assert(L_XMLDECL@ =~= lit_xmldecl());
    assert(L_VERSION@ =~= lit_version());
    assert(L_ENCODING@ =~= lit_encoding());
    assert(L_STANDALONE@ =~= lit_standalone());
    assert(L_YES@ =~= lit_yes());
    assert(L_NO@ =~= lit_no());
    assert(L_COMMENT@ =~= lit_comment());
    assert(L_CDATA@ =~= lit_cdata());
    assert(L_DOCTYPE@ =~= lit_doctype());
    assert(L_SYSTEM@ =~= lit_system());
    assert(L_PUBLIC@ =~= lit_public());
    assert(L_ELEMENT@ =~= lit_element());
    assert(L_ATTLIST@ =~= lit_attlist());
    assert(L_ENTITY@ =~= lit_entity());
    assert(L_NOTATION@ =~= lit_notation());
    assert(L_NDATA@ =~= lit_ndata());
    assert(L_EMPTY@ =~= lit_empty());
    assert(L_ANY@ =~= lit_any());
    assert(L_PCDATA@ =~= lit_pcdata());
    assert(L_REQUIRED@ =~= lit_required());
    assert(L_IMPLIED@ =~= lit_implied());
    assert(L_FIXED@ =~= lit_fixed());
    assert(L_CDATA_TY@ =~= lit_cdata_ty());
    assert(L_IDREFS@ =~= lit_idrefs());
    assert(L_IDREF@ =~= lit_idref());
    assert(L_ID@ =~= lit_id());
    assert(L_ENTITIES@ =~= lit_entities());
    assert(L_ENTITY_TY@ =~= lit_entity_ty());
    assert(L_NMTOKENS@ =~= lit_nmtokens());
    assert(L_NMTOKEN@ =~= lit_nmtoken());
    assert(L_NOTATION_TY@ =~= lit_notation_ty());
}

/// `has_lit` for a two-byte literal.
#[inline(always)]
pub fn ex_has2(s: &[u8], i: usize, b0: u8, b1: u8) -> (r: bool)
    ensures
        r == has_lit(s@, i as int, seq![b0, b1]),
{
    let n = s.len();
    if i <= n && n - i >= 2 && get(s, i) == b0 && get(s, i + 1) == b1 {
        proof {
            assert(s@.subrange(i as int, i + 2) =~= seq![b0, b1]);
        }
        true
    } else {
        proof {
            if i <= n && n - i >= 2 {
                assert(s@.subrange(i as int, i + 2)[0] == s@[i as int]);
                assert(s@.subrange(i as int, i + 2)[1] == s@[i + 1]);
            }
        }
        false
    }
}

/// `eq_end`.
#[inline(always)]
pub fn ex_eq_end(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i <= s@.len(),
    ensures
        same(r, eq_end(s@, i as int)),
        r matches Some(e) ==> i < e <= s@.len(),
{
    let j = ex_ws_end(s, i);
    if j < s.len() && get(s, j) == 0x3D {
        Some(ex_ws_end(s, j + 1))
    } else {
        None
    }
}

/// Whether `x[a..b]` and `y[c..d]` hold the same bytes.
pub fn ex_bytes_eq(x: &[u8], a: usize, b: usize, y: &[u8], c: usize, d: usize) -> (r: bool)
    requires
        a <= b <= x@.len(),
        c <= d <= y@.len(),
    ensures
        r == (x@.subrange(a as int, b as int) == y@.subrange(c as int, d as int)),
{
    if b - a != d - c {
        proof {
            assert(x@.subrange(a as int, b as int).len() != y@.subrange(c as int, d as int).len());
        }
        return false;
    }
    let l = b - a;
    let mut k: usize = 0;
    while k < l
        invariant
            a + l == b <= x@.len(),
            c + l == d <= y@.len(),
            k <= l,
            x@.subrange(a as int, a + k) =~= y@.subrange(c as int, c + k),
        decreases l - k,
    {
        if get(x, a + k) != get(y, c + k) {
            proof {
                assert(x@.subrange(a as int, b as int)[k as int] != y@.subrange(c as int, d as int)[k as int]);
            }
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(x@.subrange(a as int, b as int) =~= y@.subrange(c as int, d as int));
    }
    true
}

// ---------------------------------------------------------------------------
// References
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn ex_is_hex(c: u8) -> (r: bool)
    ensures
        r == is_hex(c),
{
    (0x30 <= c && c <= 0x39) || (0x41 <= c && c <= 0x46) || (0x61 <= c && c <= 0x66)
}

#[inline(always)]
pub fn ex_is_char(c: u32) -> (r: bool)
    ensures
        r == is_char(c as int),
{
    c == 0x9 || c == 0xA || c == 0xD || (0x20 <= c && c <= 0xD7FF) || (0xE000 <= c && c <= 0xFFFD) || (0x10000
        <= c && c <= 0x10FFFF)
}

/// Above every character: where a reference's value is clamped.
pub const BIG: u32 = 0x110000;

pub open spec fn clamp(v: int) -> int {
    if v >= BIG as int {
        BIG as int
    } else {
        v
    }
}

pub proof fn lemma_hexv_nonneg(s: Seq<u8>, a: int, b: int)
    requires
        forall|k: int| a <= k < b ==> is_hex(#[trigger] s[k]),
    ensures
        hexv(s, a, b) >= 0,
    decreases b - a,
{
    if b > a {
        lemma_hexv_nonneg(s, a, b - 1);
        assert(is_hex(s[b - 1]));
    }
}

pub proof fn lemma_decv_nonneg(s: Seq<u8>, a: int, b: int)
    requires
        forall|k: int| a <= k < b ==> is_digit(#[trigger] s[k]),
    ensures
        decv(s, a, b) >= 0,
    decreases b - a,
{
    if b > a {
        lemma_decv_nonneg(s, a, b - 1);
    }
}

/// `charref` at `i`, where `s[i..i + 2]` is `&#`. The value is clamped
/// above every character while the digits are read, so it cannot
/// overflow.
pub fn ex_charref(s: &[u8], i: usize) -> (r: Option<(u32, usize)>)
    requires
        i + 2 <= s@.len(),
    ensures
        match charref(s@, i as int) {
            Some((c, e)) => r == Some((c as u32, e as usize)) && is_char(c) && i < e <= s@.len(),
            None => r is None,
        },
{
    let n = s.len();
    if i + 2 < n && get(s, i + 2) == 0x78 {
        let a = i + 3;
        let mut j = a;
        let mut v: u32 = 0;
        while j < n && ex_is_hex(get(s, j))
            invariant
                a <= j <= n,
                n == s@.len(),
                hex_end(s@, j as int) == hex_end(s@, a as int),
                forall|k: int| a <= k < j ==> is_hex(#[trigger] s@[k]),
                v as int == clamp(hexv(s@, a as int, j as int)),
            decreases n - j,
        {
            let c = get(s, j);
            let d: u32 = if c <= 0x39 {
                (c - 0x30) as u32
            } else if c <= 0x46 {
                (c - 0x41 + 10) as u32
            } else {
                (c - 0x61 + 10) as u32
            };
            proof {
                lemma_hexv_nonneg(s@, a as int, j as int);
                assert(hexv(s@, a as int, j + 1) == hexv(s@, a as int, j as int) * 16 + hex_val(c));
            }
            if v >= BIG {
                v = BIG;
            } else {
                let w = v * 16 + d;
                v = if w >= BIG { BIG } else { w };
            }
            j = j + 1;
        }
        if j > a && j < n && get(s, j) == 0x3B && ex_is_char(v) {
            proof {
                lemma_hexv_nonneg(s@, a as int, j as int);
            }
            Some((v, j + 1))
        } else {
            None
        }
    } else {
        let a = i + 2;
        let mut j = a;
        let mut v: u32 = 0;
        while j < n && 0x30 <= get(s, j) && get(s, j) <= 0x39
            invariant
                a <= j <= n,
                n == s@.len(),
                digits_end(s@, j as int) == digits_end(s@, a as int),
                forall|k: int| a <= k < j ==> is_digit(#[trigger] s@[k]),
                v as int == clamp(decv(s@, a as int, j as int)),
            decreases n - j,
        {
            let c = get(s, j);
            let d: u32 = (c - 0x30) as u32;
            proof {
                lemma_decv_nonneg(s@, a as int, j as int);
                assert(decv(s@, a as int, j + 1) == decv(s@, a as int, j as int) * 10 + (c - 0x30));
            }
            if v >= BIG {
                v = BIG;
            } else {
                let w = v * 10 + d;
                v = if w >= BIG { BIG } else { w };
            }
            j = j + 1;
        }
        if j > a && j < n && get(s, j) == 0x3B && ex_is_char(v) {
            proof {
                lemma_decv_nonneg(s@, a as int, j as int);
            }
            Some((v, j + 1))
        } else {
            None
        }
    }
}

/// `predef`.
pub fn ex_predef(s: &[u8], a: usize, b: usize) -> (r: Option<u32>)
    requires
        a <= b <= s@.len(),
    ensures
        r == match predef(s@, a as int, b as int) {
            Some(c) => Some(c as u32),
            None => None::<u32>,
        },
{
    let ghost n = s@.subrange(a as int, b as int);
    let l = b - a;
    proof {
        assert(n.len() == l);
        assert(forall|k: int| 0 <= k < l ==> #[trigger] n[k] == s@[a + k]);
        assert(n != seq![0x6Cu8, 0x74] ==> l != 2 || n[0] != 0x6C || n[1] != 0x74) by {
            if l == 2 && n[0] == 0x6C && n[1] == 0x74 {
                assert(n =~= seq![0x6Cu8, 0x74]);
            }
        }
        assert(n != seq![0x67u8, 0x74] ==> l != 2 || n[0] != 0x67 || n[1] != 0x74) by {
            if l == 2 && n[0] == 0x67 && n[1] == 0x74 {
                assert(n =~= seq![0x67u8, 0x74]);
            }
        }
        assert(n != seq![0x61u8, 0x6D, 0x70] ==> l != 3 || n[0] != 0x61 || n[1] != 0x6D || n[2] != 0x70) by {
            if l == 3 && n[0] == 0x61 && n[1] == 0x6D && n[2] == 0x70 {
                assert(n =~= seq![0x61u8, 0x6D, 0x70]);
            }
        }
        assert(n != seq![0x61u8, 0x70, 0x6F, 0x73] ==> l != 4 || n[0] != 0x61 || n[1] != 0x70 || n[2] != 0x6F
            || n[3] != 0x73) by {
            if l == 4 && n[0] == 0x61 && n[1] == 0x70 && n[2] == 0x6F && n[3] == 0x73 {
                assert(n =~= seq![0x61u8, 0x70, 0x6F, 0x73]);
            }
        }
        assert(n != seq![0x71u8, 0x75, 0x6F, 0x74] ==> l != 4 || n[0] != 0x71 || n[1] != 0x75 || n[2] != 0x6F
            || n[3] != 0x74) by {
            if l == 4 && n[0] == 0x71 && n[1] == 0x75 && n[2] == 0x6F && n[3] == 0x74 {
                assert(n =~= seq![0x71u8, 0x75, 0x6F, 0x74]);
            }
        }
    }
    if l == 2 {
        let c0 = get(s, a);
        let c1 = get(s, a + 1);
        if c1 == 0x74 {
            if c0 == 0x6C {
                return Some(0x3C);
            } else if c0 == 0x67 {
                return Some(0x3E);
            }
        }
        None
    } else if l == 3 {
        if get(s, a) == 0x61 && get(s, a + 1) == 0x6D && get(s, a + 2) == 0x70 {
            Some(0x26)
        } else {
            None
        }
    } else if l == 4 {
        let c0 = get(s, a);
        let c1 = get(s, a + 1);
        let c2 = get(s, a + 2);
        let c3 = get(s, a + 3);
        if c0 == 0x61 && c1 == 0x70 && c2 == 0x6F && c3 == 0x73 {
            Some(0x27)
        } else if c0 == 0x71 && c1 == 0x75 && c2 == 0x6F && c3 == 0x74 {
            Some(0x22)
        } else {
            None
        }
    } else {
        None
    }
}

/// `find_ent` of the prefix `ents[..j + 1]`, given that the prefix
/// `ents[..j]` has no match.
pub proof fn lemma_find_step(ents: Seq<Ent>, name: Seq<u8>, j: int)
    requires
        0 <= j < ents.len(),
        find_ent(ents.subrange(0, j), name) is None,
    ensures
        find_ent(ents.subrange(0, j + 1), name) == if ents[j].name == name {
            Some(j)
        } else {
            None::<int>
        },
{
    assert(ents.subrange(0, j + 1).drop_last() =~= ents.subrange(0, j));
}

pub proof fn lemma_find_range(ents: Seq<Ent>, name: Seq<u8>)
    ensures
        find_ent(ents, name) matches Some(j) ==> 0 <= j < ents.len() && ents[j].name == name,
    decreases ents.len(),
{
    if ents.len() > 0 {
        lemma_find_range(ents.drop_last(), name);
    }
}

/// `find_ent` of the entity whose name is `x[a..b]`, among the first
/// `lim` entities, through the index.
pub fn ex_find_ent(env: &XEnv, lim: usize, x: &[u8], a: usize, b: usize) -> (r: Option<usize>)
    requires
        a <= b <= x@.len(),
        env_wf(env),
        lim <= env.ents@.len(),
    ensures
        same(r, find_ent(lim_view(env, lim as int).ents, x@.subrange(a as int, b as int))),
        r matches Some(j) ==> j < lim,
{
    let r = env.idx.find(env.doc, env.ents, lim, x, a, b);
    proof {
        lemma_find_range(lim_view(env, lim as int).ents, x@.subrange(a as int, b as int));
    }
    r
}

/// A match in a prefix is the match in the whole.
pub proof fn lemma_find_prefix_some(ents: Seq<Ent>, name: Seq<u8>, j: int)
    requires
        0 <= j <= ents.len(),
        find_ent(ents.subrange(0, j), name) is Some,
    ensures
        find_ent(ents, name) == find_ent(ents.subrange(0, j), name),
    decreases ents.len() - j,
{
    if j < ents.len() {
        assert(ents.subrange(0, j + 1).drop_last() =~= ents.subrange(0, j));
        lemma_find_prefix_some(ents, name, j + 1);
    } else {
        assert(ents.subrange(0, j) =~= ents);
    }
}

/// The name after `&` at `i`, and whether `;` follows it.
#[inline(always)]
fn ex_ref_name(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 1 <= s@.len() < u32::MAX,
    ensures
        r == name_end(s@, i + 1),
        i + 1 <= r <= s@.len(),
{
    ex_name_end(s, i + 1)
}

/// `ref_syntax` at `i` (`s[i]` is `&`).
pub fn ex_ref_syntax(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i < s@.len() < u32::MAX,
    ensures
        same(r, ref_syntax(s@, i as int)),
        r matches Some(e) ==> i < e <= s@.len(),
{
    if ex_byte_is(s, i + 1, 0x23) {
        match ex_charref(s, i) {
            Some((_, e)) => Some(e),
            None => None,
        }
    } else {
        let n = ex_ref_name(s, i);
        if n > i + 1 && ex_byte_is(s, n, 0x3B) {
            Some(n + 1)
        } else {
            None
        }
    }
}

/// `att_ref` at `i` (`s[i]` is `&`), against the first `lim` entities.
pub fn ex_att_ref(s: &[u8], i: usize, env: Option<&XEnv>, lim: usize) -> (r: Option<usize>)
    requires
        i < s@.len() < u32::MAX,
        oenv_wf(env, lim as int),
    ensures
        same(r, att_ref(s@, i as int, oenv_view(env, lim as int))),
        r matches Some(e) ==> i < e <= s@.len(),
{
    if ex_byte_is(s, i + 1, 0x23) {
        match ex_charref(s, i) {
            Some((_, e)) => Some(e),
            None => None,
        }
    } else {
        let n = ex_ref_name(s, i);
        if !(n > i + 1 && ex_byte_is(s, n, 0x3B)) {
            None
        } else if ex_predef(s, i + 1, n).is_some() {
            Some(n + 1)
        } else {
            match env {
                None => Some(n + 1),
                Some(env) => match ex_find_ent(env, lim, s, i + 1, n) {
                    Some(j) => {
                        proof {
                            assert(lim_view(env, lim as int).ents[j as int] == ent_view(env.doc@, env.ents@[j as int]));
                        }
                        if env.ents[j].kind == 0 {
                            if j < env.oka.len() && env.oka[j] {
                                Some(n + 1)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    },
                    None => if env.wfc {
                        None
                    } else {
                        Some(n + 1)
                    },
                },
            }
        }
    }
}

/// `content_ref` at `i` (`s[i]` is `&`): the token and the end.
pub fn ex_content_ref(s: &[u8], i: usize, env: &XEnv) -> (r: Option<(Tok, usize)>)
    requires
        i < s@.len() < u32::MAX,
        env_wf(env),
    ensures
        match content_ref(s@, i as int, env_view(env)) {
            Some((x, e)) => r matches Some((t, e2)) && t@ == x && e2 == e && i < e <= s@.len(),
            None => r is None,
        },
{
    if ex_byte_is(s, i + 1, 0x23) {
        match ex_charref(s, i) {
            Some((c, e)) => Some((Tok { kind: Kind::CharRef, f: 0, a: i as u32, b: c, c: 0 }, e)),
            None => None,
        }
    } else {
        let n = ex_ref_name(s, i);
        if !(n > i + 1 && ex_byte_is(s, n, 0x3B)) {
            None
        } else {
            match ex_predef(s, i + 1, n) {
                Some(c) => Some((Tok { kind: Kind::CharRef, f: 0, a: i as u32, b: c, c: 0 }, n + 1)),
                None => {
                    proof {
                        lemma_lim_all(env);
                    }
                    match ex_find_ent(env, env.ents.len(), s, i + 1, n) {
                        Some(j) => {
                            proof {
                                assert(env_view(env).ents[j as int] == ent_view(env.doc@, env.ents@[j as int]));
                            }
                            let k = env.ents[j].kind;
                            if k == 2 {
                                None
                            } else if k == 1 {
                                Some((tok(Kind::EntRef, i + 1, n, 0), n + 1))
                            } else if j < env.okc.len() && env.okc[j] {
                                Some((tok(Kind::EntRef, i + 1, n, 0), n + 1))
                            } else {
                                None
                            }
                        },
                        None => if env.wfc {
                            None
                        } else {
                            Some((tok(Kind::EntRef, i + 1, n, 0), n + 1))
                        },
                    }
                },
            }
        }
    }
}


// ---------------------------------------------------------------------------
// Runs the scanners pass over
// ---------------------------------------------------------------------------

proof fn lemma_no_end3(s: Seq<u8>, j: int)
    requires
        0 <= j < s.len(),
        s[j] != 0x5D,
    ensures
        !has_lit(s, j, lit_cdata_end()),
{
    if has_lit(s, j, lit_cdata_end()) {
        assert(s.subrange(j, j + 3)[0] == s[j]);
    }
}

proof fn lemma_cr_step(s: Seq<u8>, i: int, j: int)
    requires
        i <= j < s.len(),
        s[j] != 0x0D,
    ensures
        has_cr(s, i, j + 1) == has_cr(s, i, j),
{
    if has_cr(s, i, j + 1) {
        let k = choose|k: int| i <= k < j + 1 && s[k] == 0x0D;
        assert(k < j);
    }
}

/// Character data passes over bytes that are not `text_stop`.
pub proof fn lemma_text_skip(s: Seq<u8>, i: int, j: int, k: int)
    requires
        0 <= i <= j,
        0 <= k,
        j + k <= s.len(),
        forall|q: int| j <= q < j + k ==> !text_stop(#[trigger] s[q]),
    ensures
        text_end(s, j) == text_end(s, j + k),
        has_cr(s, i, j + k) == has_cr(s, i, j),
    decreases k,
{
    if k > 0 {
        assert(!text_stop(s[j]));
        lemma_no_end3(s, j);
        lemma_cr_step(s, i, j);
        lemma_text_skip(s, i, j + 1, k - 1);
    }
}

/// A CDATA section passes over bytes that are not `cdata_stop`.
pub proof fn lemma_cdata_skip(s: Seq<u8>, i: int, j: int, k: int)
    requires
        0 <= i <= j,
        0 <= k,
        j + k <= s.len(),
        forall|q: int| j <= q < j + k ==> !cdata_stop(#[trigger] s[q]),
    ensures
        cdata_end(s, j) == cdata_end(s, j + k),
        has_cr(s, i, j + k) == has_cr(s, i, j),
    decreases k,
{
    if k > 0 {
        assert(!cdata_stop(s[j]));
        lemma_no_end3(s, j);
        lemma_cr_step(s, i, j);
        lemma_cdata_skip(s, i, j + 1, k - 1);
    }
}

/// A comment passes over bytes other than `-`.
pub proof fn lemma_comment_skip(s: Seq<u8>, j: int, k: int)
    requires
        0 <= j,
        0 <= k,
        j + k <= s.len(),
        forall|q: int| j <= q < j + k ==> #[trigger] s[q] != 0x2D,
    ensures
        comment_end(s, j) == comment_end(s, j + k),
    decreases k,
{
    if k > 0 {
        assert(s[j] != 0x2D);
        lemma_comment_skip(s, j + 1, k - 1);
    }
}

/// A processing instruction passes over bytes other than `?`.
pub proof fn lemma_pi_skip(s: Seq<u8>, j: int, k: int)
    requires
        0 <= j,
        0 <= k,
        j + k <= s.len(),
        forall|q: int| j <= q < j + k ==> #[trigger] s[q] != 0x3F,
    ensures
        pi_end(s, j) == pi_end(s, j + k),
    decreases k,
{
    if k > 0 {
        assert(s[j] != 0x3F);
        lemma_pi_skip(s, j + 1, k - 1);
    }
}

/// An attribute value passes over bytes that are not `att_stop`, and they
/// keep it plain.
pub proof fn lemma_att_skip(s: Seq<u8>, i: int, j: int, k: int, q: u8, env: Option<Env>)
    requires
        0 <= i <= j,
        0 <= k,
        j + k <= s.len(),
        forall|p: int| j <= p < j + k ==> !att_stop(#[trigger] s[p], q),
    ensures
        att_chars(s, j, q, env) == att_chars(s, j + k, q, env),
        att_plain(s, i, j + k) == att_plain(s, i, j),
    decreases k,
{
    if k > 0 {
        assert(!att_stop(s[j], q));
        lemma_att_skip(s, i, j + 1, k - 1, q, env);
        assert(att_plain(s, i, j + 1) == att_plain(s, i, j)) by {
            if att_plain(s, i, j) {
                assert forall|p: int| i <= p < j + 1 implies s[p] != 0x26 && s[p] != 0x09 && s[p] != 0x0A && s[p]
                    != 0x0D by {
                    if p < j {
                        assert(s[p] != 0x26 && s[p] != 0x09 && s[p] != 0x0A && s[p] != 0x0D);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Values and literals
// ---------------------------------------------------------------------------

/// `att_chars` from `i` to the closing quote `q`, with `att_plain` of
/// what it passed.
pub fn ex_att_chars(s: &[u8], i: usize, q: u8, env: Option<&XEnv>, lim: usize) -> (r: Option<(usize, bool)>)
    requires
        i <= s@.len() < u32::MAX,
        oenv_wf(env, lim as int),
    ensures
        match att_chars(s@, i as int, q, oenv_view(env, lim as int)) {
            Some(e) => r == Some((e as usize, att_plain(s@, i as int, e))) && i <= e < s@.len(),
            None => r is None,
        },
{
    let n = s.len();
    let mut j = i;
    let mut plain = true;
    loop
        invariant
            i <= j <= n,
            n == s@.len() < u32::MAX,
            oenv_wf(env, lim as int),
            att_chars(s@, j as int, q, oenv_view(env, lim as int)) == att_chars(s@, i as int, q, oenv_view(env, lim as int)),
            plain == att_plain(s@, i as int, j as int),
        decreases n - j,
    {
        if n - j >= 16 {
            let k = att_run16(s, j, q);
            proof {
                lemma_att_skip(s@, i as int, j as int, k as int, q, oenv_view(env, lim as int));
            }
            if k == 16 {
                j = j + 16;
                continue;
            }
            j = j + k;
        }
        if j >= n {
            return None;
        }
        let c = get(s, j);
        if c == q {
            return Some((j, plain));
        }
        if c == 0x3C {
            return None;
        }
        if c == 0x26 {
            match ex_att_ref(s, j, env, lim) {
                None => {
                    return None;
                },
                Some(e) => {
                    proof {
                        assert(!att_plain(s@, i as int, e as int));
                    }
                    plain = false;
                    j = e;
                },
            }
        } else {
            if c == 0x09 || c == 0x0A || c == 0x0D {
                plain = false;
            }
            j = j + 1;
        }
    }
}

/// `ent_value_end` from `i`.
pub fn ex_ent_value_end(s: &[u8], i: usize, q: u8) -> (r: Option<usize>)
    requires
        i <= s@.len() < u32::MAX,
    ensures
        same(r, ent_value_end(s@, i as int, q)),
        r matches Some(e) ==> i < e <= s@.len(),
{
    let n = s.len();
    let mut j = i;
    loop
        invariant
            i <= j <= n,
            n == s@.len() < u32::MAX,
            ent_value_end(s@, j as int, q) == ent_value_end(s@, i as int, q),
        decreases n - j,
    {
        if j >= n {
            return None;
        }
        let c = get(s, j);
        if c == q {
            return Some(j + 1);
        }
        if c == 0x25 {
            return None;
        }
        if c == 0x26 {
            match ex_ref_syntax(s, j) {
                None => {
                    return None;
                },
                Some(e) => {
                    j = e;
                },
            }
        } else {
            j = j + 1;
        }
    }
}

/// `lit_end` from `i`.
pub fn ex_lit_end(s: &[u8], i: usize, q: u8) -> (r: Option<usize>)
    requires
        i <= s@.len(),
    ensures
        same(r, lit_end(s@, i as int, q)),
        r matches Some(e) ==> i < e <= s@.len(),
{
    let n = s.len();
    let mut j = i;
    while j < n && get(s, j) != q
        invariant
            i <= j <= n,
            n == s@.len(),
            lit_end(s@, j as int, q) == lit_end(s@, i as int, q),
        decreases n - j,
    {
        j = j + 1;
    }
    if j < n {
        Some(j + 1)
    } else {
        None
    }
}

/// `pubid_end` from `i`.
pub fn ex_pubid_end(s: &[u8], i: usize, q: u8) -> (r: Option<usize>)
    requires
        i <= s@.len(),
    ensures
        same(r, pubid_end(s@, i as int, q)),
        r matches Some(e) ==> i < e <= s@.len(),
{
    let n = s.len();
    let mut j = i;
    while j < n && get(s, j) != q && ex_pubid_char(get(s, j))
        invariant
            i <= j <= n,
            n == s@.len(),
            pubid_end(s@, j as int, q) == pubid_end(s@, i as int, q),
        decreases n - j,
    {
        j = j + 1;
    }
    if j < n && get(s, j) == q {
        Some(j + 1)
    } else {
        None
    }
}

/// `sys_lit` at `i`.
pub fn ex_sys_lit(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i <= s@.len(),
    ensures
        same(r, sys_lit(s@, i as int)),
        r matches Some(e) ==> i + 1 < e <= s@.len(),
{
    if i < s.len() && (get(s, i) == 0x22 || get(s, i) == 0x27) {
        ex_lit_end(s, i + 1, get(s, i))
    } else {
        None
    }
}

/// `pubid_lit` at `i`.
pub fn ex_pubid_lit(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i <= s@.len(),
    ensures
        same(r, pubid_lit(s@, i as int)),
        r matches Some(e) ==> i + 1 < e <= s@.len(),
{
    if i < s.len() && (get(s, i) == 0x22 || get(s, i) == 0x27) {
        ex_pubid_end(s, i + 1, get(s, i))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Comments, processing instructions, CDATA sections, character data
// ---------------------------------------------------------------------------

/// `comment_end` from `i`.
pub fn ex_comment_end(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i <= s@.len(),
    ensures
        same(r, comment_end(s@, i as int)),
        r matches Some(e) ==> i + 3 <= e <= s@.len(),
{
    let n = s.len();
    let mut j = i;
    while j < n
        invariant
            i <= j <= n,
            n == s@.len(),
            comment_end(s@, j as int) == comment_end(s@, i as int),
        decreases n - j,
    {
        if n - j >= 16 {
            let k = byte_run16(s, j, 0x2D);
            proof {
                lemma_comment_skip(s@, j as int, k as int);
            }
            if k == 16 {
                j = j + 16;
                continue;
            }
            j = j + k;
        }
        if get(s, j) == 0x2D && ex_byte_is(s, j + 1, 0x2D) {
            if ex_byte_is(s, j + 2, 0x3E) {
                return Some(j + 3);
            } else {
                return None;
            }
        }
        j = j + 1;
    }
    None
}

/// `comment` at `i` (`s[i..]` starts with `<!--`).
pub fn ex_comment(s: &[u8], i: usize, tape: &mut Tape) -> (r: Option<usize>)
    requires
        i + 4 <= s@.len() < u32::MAX,
        old(tape)@.len() <= i,
    ensures
        match comment(s@, i as int, old(tape)@) {
            Some((t, e)) => r == Some(e as usize) && final(tape)@ == t && i < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> old(tape)@.len() <= final(tape)@.len(),
{
    match ex_comment_end(s, i + 4) {
        Some(e) => {
            tape.push(tok(Kind::Comment, i + 4, e - 3, 0));
            Some(e)
        },
        None => None,
    }
}

/// `pi_end` from `i`.
pub fn ex_pi_end(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i <= s@.len(),
    ensures
        same(r, pi_end(s@, i as int)),
        r matches Some(e) ==> i + 2 <= e <= s@.len(),
{
    let n = s.len();
    let mut j = i;
    while j < n
        invariant
            i <= j <= n,
            n == s@.len(),
            pi_end(s@, j as int) == pi_end(s@, i as int),
        decreases n - j,
    {
        if n - j >= 16 {
            let k = byte_run16(s, j, 0x3F);
            proof {
                lemma_pi_skip(s@, j as int, k as int);
            }
            if k == 16 {
                j = j + 16;
                continue;
            }
            j = j + k;
        }
        if get(s, j) == 0x3F && ex_byte_is(s, j + 1, 0x3E) {
            return Some(j + 2);
        }
        j = j + 1;
    }
    None
}

/// `xml_name`.
#[inline(always)]
fn ex_xml_name(s: &[u8], a: usize, b: usize) -> (r: bool)
    requires
        a <= b <= s@.len(),
    ensures
        r == xml_name(s@, a as int, b as int),
{
    b - a == 3 && (get(s, a) == 0x78 || get(s, a) == 0x58) && (get(s, a + 1) == 0x6D || get(s, a + 1) == 0x4D)
        && (get(s, a + 2) == 0x6C || get(s, a + 2) == 0x4C)
}

/// `pi` at `i` (`s[i..]` starts with `<?`).
pub fn ex_pi(s: &[u8], i: usize, tape: &mut Tape) -> (r: Option<usize>)
    requires
        i + 2 <= s@.len() < u32::MAX,
        old(tape)@.len() <= i,
    ensures
        match pi(s@, i as int, old(tape)@) {
            Some((t, e)) => r == Some(e as usize) && final(tape)@ == t && i < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> old(tape)@.len() <= final(tape)@.len(),
{
    let n = ex_name_end(s, i + 2);
    if n == i + 2 || ex_xml_name(s, i + 2, n) {
        return None;
    }
    if ex_has2(s, n, 0x3F, 0x3E) {
        tape.push(tok(Kind::PI, i + 2, n, 0));
        tape.push(tok(Kind::PIData, n, n, 0));
        proof {
            assert(lit_pi_end() =~= seq![0x3Fu8, 0x3E]);
        }
        Some(n + 2)
    } else if n < s.len() && ex_is_ws(get(s, n)) {
        proof {
            assert(lit_pi_end() =~= seq![0x3Fu8, 0x3E]);
        }
        let d = ex_ws_end(s, n);
        match ex_pi_end(s, d) {
            Some(e) => {
                tape.push(tok(Kind::PI, i + 2, n, 0));
                tape.push(tok(Kind::PIData, d, e - 2, 0));
                Some(e)
            },
            None => None,
        }
    } else {
        proof {
            assert(lit_pi_end() =~= seq![0x3Fu8, 0x3E]);
        }
        None
    }
}

/// `cdata_end` from `i`, and whether `s[i..e - 3]` holds a carriage
/// return.
pub fn ex_cdata_end(s: &[u8], i: usize) -> (r: Option<(usize, bool)>)
    requires
        i <= s@.len(),
    ensures
        match cdata_end(s@, i as int) {
            Some(e) => r == Some((e as usize, has_cr(s@, i as int, e - 3))) && i + 3 <= e <= s@.len(),
            None => r is None,
        },
{
    let n = s.len();
    let mut j = i;
    let mut cr = false;
    while j < n
        invariant
            i <= j <= n,
            n == s@.len(),
            cdata_end(s@, j as int) == cdata_end(s@, i as int),
            cr == has_cr(s@, i as int, j as int),
        decreases n - j,
    {
        if n - j >= 16 {
            let k = cdata_run16(s, j);
            proof {
                lemma_cdata_skip(s@, i as int, j as int, k as int);
            }
            if k == 16 {
                j = j + 16;
                continue;
            }
            j = j + k;
        }
        let c = get(s, j);
        if c == 0x5D && ex_byte_is(s, j + 1, 0x5D) && ex_byte_is(s, j + 2, 0x3E) {
            proof {
                assert(s@.subrange(j as int, j + 3) =~= lit_cdata_end());
            }
            return Some((j + 3, cr));
        }
        proof {
            if has_lit(s@, j as int, lit_cdata_end()) {
                assert(s@.subrange(j as int, j + 3)[0] == s@[j as int]);
                assert(s@.subrange(j as int, j + 3)[1] == s@[j + 1]);
                assert(s@.subrange(j as int, j + 3)[2] == s@[j + 2]);
            }
            if c == 0x0D {
                assert(has_cr(s@, i as int, j + 1));
            } else if has_cr(s@, i as int, j + 1) {
                let k = choose|k: int| i <= k < j + 1 && s@[k] == 0x0D;
                assert(k < j);
            }
        }
        if c == 0x0D {
            cr = true;
        }
        j = j + 1;
    }
    None
}

/// `text_end` from `i`, and whether `s[i..e]` holds a carriage return.
pub fn ex_text_end(s: &[u8], i: usize) -> (r: Option<(usize, bool)>)
    requires
        i < s@.len(),
        s@[i as int] != 0x3C && s@[i as int] != 0x26,
    ensures
        match text_end(s@, i as int) {
            Some(e) => r == Some((e as usize, has_cr(s@, i as int, e))) && i < e <= s@.len(),
            None => r is None,
        },
{
    let n = s.len();
    let mut j = i;
    let mut cr = false;
    while j < n
        invariant
            i <= j <= n,
            n == s@.len(),
            text_end(s@, j as int) == text_end(s@, i as int),
            cr == has_cr(s@, i as int, j as int),
            i < n,
            s@[i as int] != 0x3C && s@[i as int] != 0x26,
        decreases n - j,
    {
        if n - j >= 16 {
            let k = text_run16(s, j);
            proof {
                lemma_text_skip(s@, i as int, j as int, k as int);
            }
            if k == 16 {
                j = j + 16;
                continue;
            }
            j = j + k;
        }
        let c = get(s, j);
        if c == 0x3C || c == 0x26 {
            return Some((j, cr));
        }
        if c == 0x5D && ex_byte_is(s, j + 1, 0x5D) && ex_byte_is(s, j + 2, 0x3E) {
            proof {
                assert(s@.subrange(j as int, j + 3) =~= lit_cdata_end());
            }
            return None;
        }
        proof {
            if has_lit(s@, j as int, lit_cdata_end()) {
                assert(s@.subrange(j as int, j + 3)[0] == s@[j as int]);
                assert(s@.subrange(j as int, j + 3)[1] == s@[j + 1]);
                assert(s@.subrange(j as int, j + 3)[2] == s@[j + 2]);
            }
            if c == 0x0D {
                assert(has_cr(s@, i as int, j + 1));
            } else if has_cr(s@, i as int, j + 1) {
                let k = choose|k: int| i <= k < j + 1 && s@[k] == 0x0D;
                assert(k < j);
            }
        }
        if c == 0x0D {
            cr = true;
        }
        j = j + 1;
    }
    Some((j, cr))
}

/// `misc` from `i`.
pub fn ex_misc(s: &[u8], i: usize, tape: &mut Tape) -> (r: Option<usize>)
    requires
        i <= s@.len() < u32::MAX,
        old(tape)@.len() <= i,
    ensures
        match misc(s@, i as int, old(tape)@) {
            Some((t, e)) => r == Some(e as usize) && final(tape)@ == t && i <= e <= s@.len() && t.len() <= e,
            None => r is None,
        },
{
    let mut j = i;
    proof {
        lemma_lits();
    }
    loop
        invariant
            i <= j <= s@.len() < u32::MAX,
            tape@.len() <= j,
            misc(s@, j as int, tape@) == misc(s@, i as int, old(tape)@),
            L_COMMENT@ == lit_comment(),
        decreases s@.len() - j,
    {
        let k = ex_ws_end(s, j);
        if ex_has_lit(s, k, &L_COMMENT) {
            match ex_comment(s, k, tape) {
                None => {
                    tape.fail(k);
                    return None;
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
                    tape.fail(k);
                    return None;
                },
                Some(e) => {
                    j = e;
                },
            }
        } else {
            proof {
                assert(lit_pi() =~= seq![0x3Cu8, 0x3F]);
            }
            return Some(k);
        }
    }
}

} // verus!
