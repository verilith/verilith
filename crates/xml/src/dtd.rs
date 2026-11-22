//! Verified code for the XML declaration and the document type
//! declaration, internal subset included: each function is proven to
//! return exactly what the spec function of the same name returns.
use crate::chars::*;
use crate::ent::*;
use crate::lex::*;
use crate::spec::*;
use crate::tape::*;
#[cfg(verus_keep_ghost)]
use verilith_core::num::{digits_end, is_digit};
use vstd::prelude::*;

verus! {

/// The internal subset so far (see `DtdSt`): processed general entities,
/// the spans of the parameter entities' names, and two flags.
pub struct XDtd {
    pub ents: Vec<XEnt>,
    pub pes: Vec<(usize, usize)>,
    pub pe_seen: bool,
    pub sa: bool,
}

/// What the document type declaration leaves for the content: the
/// processed general entities, whether "Entity Declared" applies, which
/// entities may be referred to in attribute values and in content, and
/// each internal entity's replacement text.
pub struct DtdOut {
    pub ents: Vec<XEnt>,
    pub wfc: bool,
    pub oka: Vec<bool>,
    pub okc: Vec<bool>,
    pub rts: Vec<Vec<u8>>,
    pub idx: crate::index::NameIndex,
}

pub open spec fn out_view(s: Seq<u8>, d: &DtdOut) -> Env {
    Env { ents: ents_view(s, d.ents@), wfc: d.wfc, oka: d.oka@, okc: d.okc@ }
}

pub open spec fn out_wf(s: Seq<u8>, d: &DtdOut) -> bool {
    ents_wf(s, d.ents@) && rts_ok(s, d.ents@, d.rts@) && crate::index::indexes(&d.idx, s, d.ents@)
}

impl DtdOut {
    /// No document type declaration, in the document `s`.
    pub fn none(s: &[u8]) -> (r: DtdOut)
        ensures
            r.ents@.len() == 0,
            r.oka@.len() == 0,
            r.okc@.len() == 0,
            r.rts@.len() == 0,
            r.wfc,
            crate::index::indexes(&r.idx, s@, r.ents@),
    {
        let ents: Vec<XEnt> = Vec::new();
        let idx = crate::index::NameIndex::build(s, ents.as_slice());
        DtdOut { ents, wfc: true, oka: Vec::new(), okc: Vec::new(), rts: Vec::new(), idx }
    }

    /// The environment of the content of `doc`.
    pub fn env<'a>(&'a self, doc: &'a [u8]) -> (e: XEnv<'a>)
        requires
            out_wf(doc@, self),
        ensures
            env_view(&e) == out_view(doc@, self),
            env_wf(&e),
            e.doc@ == doc@,
            e.ents@ == self.ents@,
    {
        XEnv {
            doc,
            ents: self.ents.as_slice(),
            wfc: self.wfc,
            oka: self.oka.as_slice(),
            okc: self.okc.as_slice(),
            idx: &self.idx,
        }
    }
}

/// The environment after the internal subset (`env_of`).
fn ex_finish(s: &[u8], d: XDtd, ext: bool) -> (r: DtdOut)
    requires
        s@.len() <= isize::MAX,
        d.ents@.len() <= s@.len(),
        dtd_wf(s@, &d),
    ensures
        out_view(s@, &r) == env_of(s@, dtd_view(s@, &d), ext),
        out_wf(s@, &r),
{
    let wfc = (!ext && !d.pe_seen) || d.sa;
    let idx = crate::index::NameIndex::build(s, d.ents.as_slice());
    let rts = ex_rts(s, d.ents.as_slice());
    let (oka, okc) = ex_ent_flags(s, d.ents.as_slice(), wfc, &rts, &idx);
    DtdOut { ents: d.ents, wfc, oka, okc, rts, idx }
}

pub open spec fn pes_view(s: Seq<u8>, p: Seq<(usize, usize)>) -> Seq<Seq<u8>> {
    p.map_values(|x: (usize, usize)| s.subrange(x.0 as int, x.1 as int))
}

pub open spec fn dtd_view(s: Seq<u8>, d: &XDtd) -> DtdSt {
    DtdSt { ents: ents_view(s, d.ents@), pes: pes_view(s, d.pes@), pe_seen: d.pe_seen, sa: d.sa }
}

pub open spec fn dtd_wf(s: Seq<u8>, d: &XDtd) -> bool {
    &&& ents_wf(s, d.ents@)
    &&& forall|k: int| #![trigger d.pes@[k]] 0 <= k < d.pes@.len() ==> d.pes@[k].0 <= d.pes@[k].1 <= s.len()
}

// ---------------------------------------------------------------------------
// The XML declaration
// ---------------------------------------------------------------------------

/// `digits_end`.
fn ex_digits_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r == digits_end(s@, i as int),
        i <= r <= s@.len(),
{
    let n = s.len();
    let mut j = i;
    while j < n && 0x30 <= get(s, j) && get(s, j) <= 0x39
        invariant
            i <= j <= n,
            n == s@.len(),
            digits_end(s@, j as int) == digits_end(s@, i as int),
        decreases n - j,
    {
        j = j + 1;
    }
    j
}

/// `version_info` from `i`.
pub fn ex_version_info(s: &[u8], i: usize) -> (r: Option<(usize, usize, usize)>)
    requires
        i <= s@.len() <= isize::MAX,
    ensures
        match version_info(s@, i as int) {
            Some((e, a, b)) => r matches Some((x, y, z)) && x == e && y == a && z == b && i < a <= b < e <= s@.len(),
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    let j = ex_ws_end(s, i);
    if !(j > i && ex_has_lit(s, j, &L_VERSION)) {
        return None;
    }
    match ex_eq_end(s, j + 7) {
        None => None,
        Some(k) => {
            if k < s.len() && (get(s, k) == 0x22 || get(s, k) == 0x27) && ex_byte_is(s, k + 1, 0x31)
                && ex_byte_is(s, k + 2, 0x2E) {
                let d = ex_digits_end(s, k + 3);
                if d > k + 3 && ex_byte_is(s, d, get(s, k)) {
                    Some((d + 1, k + 1, d))
                } else {
                    None
                }
            } else {
                None
            }
        },
    }
}

#[inline(always)]
fn ex_enc_char(c: u8) -> (r: bool)
    ensures
        r == enc_char(c),
{
    (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A) || (0x30 <= c && c <= 0x39) || c == 0x2E || c == 0x5F
        || c == 0x2D
}

/// `ci_eq(s, a, b, lit)`.
pub fn ex_ci_eq(s: &[u8], a: usize, b: usize, lit: &[u8]) -> (r: bool)
    requires
        a <= b <= s@.len(),
    ensures
        r == ci_eq(s@, a as int, b as int, lit@),
{
    if b - a != lit.len() {
        return false;
    }
    let mut k: usize = 0;
    while k < lit.len()
        invariant
            k <= lit@.len(),
            b - a == lit@.len(),
            a <= b <= s@.len(),
            forall|q: int| 0 <= q < k ==> lower(#[trigger] s@[a + q]) == lower(lit@[q]),
        decreases lit@.len() - k,
    {
        let x = get(s, a + k);
        let y = lit[k];
        let lx = if 0x41 <= x && x <= 0x5A { x + 0x20 } else { x };
        let ly = if 0x41 <= y && y <= 0x5A { y + 0x20 } else { y };
        if lx != ly {
            return false;
        }
        k = k + 1;
    }
    true
}

pub const L_UTF8: [u8; 5] = [0x55, 0x54, 0x46, 0x2D, 0x38];
pub const L_UTF16: [u8; 6] = [0x55, 0x54, 0x46, 0x2D, 0x31, 0x36];
pub const L_LATIN1: [u8; 10] = [0x49, 0x53, 0x4F, 0x2D, 0x38, 0x38, 0x35, 0x39, 0x2D, 0x31];
pub const L_ASCII: [u8; 8] = [0x55, 0x53, 0x2D, 0x41, 0x53, 0x43, 0x49, 0x49];

pub proof fn lemma_enc_lits()
    ensures
        L_UTF8@ == lit_utf8(),
        L_UTF16@ == lit_utf16(),
        L_LATIN1@ == lit_latin1(),
        L_ASCII@ == lit_ascii(),
{
    assert(L_UTF8@ =~= lit_utf8());
    assert(L_UTF16@ =~= lit_utf16());
    assert(L_LATIN1@ =~= lit_latin1());
    assert(L_ASCII@ =~= lit_ascii());
}

/// `enc_name_ok`.
pub fn ex_enc_name_ok(s: &[u8], a: usize, b: usize, enc: Enc) -> (r: bool)
    requires
        a <= b <= s@.len(),
    ensures
        r == enc_name_ok(s@, a as int, b as int, enc),
{
    proof {
        lemma_enc_lits();
    }
    match enc {
        Enc::Utf8 => ex_ci_eq(s, a, b, &L_UTF8),
        Enc::Utf16 => ex_ci_eq(s, a, b, &L_UTF16),
        Enc::Latin1 => ex_ci_eq(s, a, b, &L_LATIN1),
        Enc::Ascii => ex_ci_eq(s, a, b, &L_ASCII),
    }
}

/// `enc_span` at `j`.
pub fn ex_enc_span(s: &[u8], j: usize) -> (r: Option<(usize, usize, usize)>)
    requires
        j + 8 <= s@.len() <= isize::MAX,
    ensures
        match enc_span(s@, j as int) {
            Some((e, a, b)) => r matches Some((x, y, z)) && x == e && y == a && z == b && j < a <= b < e <= s@.len(),
            None => r is None,
        },
{
    match ex_eq_end(s, j + 8) {
        None => None,
        Some(k) => {
            let n = s.len();
            if k < n && (get(s, k) == 0x22 || get(s, k) == 0x27) && k + 1 < n && ((0x41 <= get(s, k + 1) && get(
                s,
                k + 1,
            ) <= 0x5A) || (0x61 <= get(s, k + 1) && get(s, k + 1) <= 0x7A)) {
                let mut m = k + 2;
                while m < n && ex_enc_char(get(s, m))
                    invariant
                        k + 2 <= m <= n,
                        n == s@.len(),
                        enc_rest(s@, m as int) == enc_rest(s@, k + 2),
                    decreases n - m,
                {
                    m = m + 1;
                }
                if ex_byte_is(s, m, get(s, k)) {
                    Some((m + 1, k + 1, m))
                } else {
                    None
                }
            } else {
                None
            }
        },
    }
}

/// `encoding_decl` at `j`.
fn ex_encoding_decl(s: &[u8], j: usize, enc: Enc) -> (r: Option<(usize, usize, usize)>)
    requires
        j + 8 <= s@.len() <= isize::MAX,
    ensures
        match encoding_decl(s@, j as int, enc) {
            Some((e, a, b)) => r matches Some((x, y, z)) && x == e && y == a && z == b && j < a <= b < e <= s@.len(),
            None => r is None,
        },
{
    match ex_enc_span(s, j) {
        Some((e, a, b)) => if ex_enc_name_ok(s, a, b, enc) {
            Some((e, a, b))
        } else {
            None
        },
        None => None,
    }
}

/// `sd_decl` at `j`.
fn ex_sd_decl(s: &[u8], j: usize) -> (r: Option<(usize, u8)>)
    requires
        j + 10 <= s@.len() <= isize::MAX,
    ensures
        match sd_decl(s@, j as int) {
            Some((e, v)) => r matches Some((x, y)) && x == e && y == v && j < e <= s@.len(),
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    match ex_eq_end(s, j + 10) {
        None => None,
        Some(k) => {
            if k < s.len() && (get(s, k) == 0x22 || get(s, k) == 0x27) {
                let q = get(s, k);
                if ex_has_lit(s, k + 1, &L_YES) && ex_byte_is(s, k + 4, q) {
                    Some((k + 5, 1))
                } else if ex_has_lit(s, k + 1, &L_NO) && ex_byte_is(s, k + 3, q) {
                    Some((k + 4, 2))
                } else {
                    None
                }
            } else {
                None
            }
        },
    }
}

/// `xmldecl` at `i`, onto an empty tape: the end and the standalone
/// declaration.
pub fn ex_xmldecl(s: &[u8], i: usize, tape: &mut Tape, enc: Enc) -> (r: Option<(usize, u8)>)
    requires
        i + 5 <= s@.len() <= isize::MAX,
        old(tape)@.len() == 0,
    ensures
        match xmldecl(s@, i as int, enc) {
            Some((t, e, sd)) => r matches Some((x, y)) && x == e && y == sd && final(tape)@ == t && i < e
                <= s@.len() && t.len() <= e && 0 <= sd <= 2,
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    let (v, va, vb) = match ex_version_info(s, i + 5) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let j = ex_ws_end(s, v);
    let (e, ea, eb, has_enc) = if j > v && ex_has_lit(s, j, &L_ENCODING) {
        match ex_encoding_decl(s, j, enc) {
            None => {
                return None;
            },
            Some((e, a, b)) => (e, a, b, true),
        }
    } else {
        (v, 0, 0, false)
    };
    let k = ex_ws_end(s, e);
    let (d, sd) = if k > e && ex_has_lit(s, k, &L_STANDALONE) {
        match ex_sd_decl(s, k) {
            None => {
                return None;
            },
            Some(x) => x,
        }
    } else {
        (e, 0u8)
    };
    let m = ex_ws_end(s, d);
    if ex_has2(s, m, 0x3F, 0x3E) {
        proof {
            assert(lit_pi_end() =~= seq![0x3Fu8, 0x3E]);
        }
        tape.push(tok(Kind::XmlDecl, va, vb, sd));
        if has_enc {
            tape.push(tok(Kind::Encoding, ea, eb, 0));
        }
        proof {
            let t = seq![XTok::XmlDecl { start: va as int, end: vb as int, sd: sd as int }];
            assert(old(tape)@.push(t[0]) =~= t);
        }
        Some((m + 2, sd))
    } else {
        proof {
            assert(lit_pi_end() =~= seq![0x3Fu8, 0x3E]);
        }
        None
    }
}

// ---------------------------------------------------------------------------
// The document type declaration
// ---------------------------------------------------------------------------

/// `external_id` at `k`.
pub fn ex_external_id(s: &[u8], k: usize, tape: &mut Tape) -> (r: Option<usize>)
    requires
        k <= s@.len() <= isize::MAX,
        old(tape)@.len() <= k,
    ensures
        match external_id(s@, k as int, old(tape)@) {
            Some((t, e)) => r matches Some(x) && x == e && final(tape)@ == t && k < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> old(tape)@.len() <= final(tape)@.len(),
{
    proof {
        lemma_lits();
    }
    if ex_has_lit(s, k, &L_SYSTEM) {
        let j = ex_ws_end(s, k + 6);
        if j == k + 6 {
            return None;
        }
        match ex_sys_lit(s, j) {
            Some(e) => {
                tape.push(tok(Kind::SysId, j + 1, e - 1, 0));
                Some(e)
            },
            None => None,
        }
    } else if ex_has_lit(s, k, &L_PUBLIC) {
        let j = ex_ws_end(s, k + 6);
        if j == k + 6 {
            return None;
        }
        match ex_pubid_lit(s, j) {
            None => None,
            Some(e) => {
                let m = ex_ws_end(s, e);
                if m == e {
                    return None;
                }
                match ex_sys_lit(s, m) {
                    Some(f) => {
                        tape.push(tok(Kind::PubId, j + 1, e - 1, 0));
                        tape.push(tok(Kind::SysId, m + 1, f - 1, 0));
                        Some(f)
                    },
                    None => None,
                }
            },
        }
    } else {
        None
    }
}

#[inline(always)]
fn ex_quant_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r == quant_end(s@, i as int),
        i <= r <= s@.len(),
{
    if i < s.len() && (get(s, i) == 0x3F || get(s, i) == 0x2A || get(s, i) == 0x2B) {
        i + 1
    } else {
        i
    }
}

/// `cmodel(s, b, [], false)`: a children content model, with the stack of
/// its open groups in a vector.
fn ex_cmodel(s: &[u8], b: usize) -> (r: Option<usize>)
    requires
        b <= s@.len() <= isize::MAX,
    ensures
        same(r, cmodel(s@, b as int, Seq::empty(), false)),
        r matches Some(e) ==> b < e <= s@.len(),
{
    let n = s.len();
    let mut st: Vec<u8> = Vec::new();
    let mut i = b;
    let mut after = false;
    loop
        invariant
            b <= i <= n,
            n == s@.len() <= isize::MAX,
            cmodel(s@, i as int, st@, after) == cmodel(s@, b as int, Seq::empty(), false),
            i == b ==> st@.len() == 0 && !after,
        decreases n - i,
    {
        let j = ex_ws_end(s, i);
        if j >= n {
            return None;
        }
        let c = get(s, j);
        if !after {
            if c == 0x28 {
                st.push(0);
                i = j + 1;
            } else {
                let k = ex_name_end(s, j);
                if k == j {
                    return None;
                }
                let q = ex_quant_end(s, k);
                i = q;
                after = true;
            }
        } else if st.len() == 0 {
            return None;
        } else if c == 0x29 {
            let k = ex_quant_end(s, j + 1);
            if st.len() == 1 {
                return Some(k);
            }
            let ghost old_st = st@;
            st.pop();
            proof {
                assert(st@ =~= old_st.drop_last());
            }
            i = k;
        } else if (c == 0x7C || c == 0x2C) && (st[st.len() - 1] == 0 || st[st.len() - 1] == c) {
            let ghost old_st = st@;
            st.pop();
            st.push(c);
            proof {
                assert(st@ =~= old_st.drop_last().push(c));
            }
            i = j + 1;
            after = false;
        } else {
            return None;
        }
    }
}

/// `mixed` from `i`.
fn ex_mixed(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i <= s@.len() <= isize::MAX,
    ensures
        same(r, mixed(s@, i as int, false)),
        r matches Some(e) ==> i < e <= s@.len(),
{
    let mut j = i;
    let mut names = false;
    loop
        invariant
            i <= j <= s@.len() <= isize::MAX,
            mixed(s@, j as int, names) == mixed(s@, i as int, false),
        decreases s@.len() - j,
    {
        let k = ex_ws_end(s, j);
        if ex_byte_is(s, k, 0x29) {
            if ex_byte_is(s, k + 1, 0x2A) {
                return Some(k + 2);
            } else if names {
                return None;
            } else {
                return Some(k + 1);
            }
        } else if ex_byte_is(s, k, 0x7C) {
            let m = ex_ws_end(s, k + 1);
            let e = ex_name_end(s, m);
            if e == m {
                return None;
            }
            j = e;
            names = true;
        } else {
            return None;
        }
    }
}

/// `contentspec` at `b`.
fn ex_contentspec(s: &[u8], b: usize) -> (r: Option<usize>)
    requires
        b <= s@.len() <= isize::MAX,
    ensures
        same(r, contentspec(s@, b as int)),
        r matches Some(e) ==> b < e <= s@.len(),
{
    proof {
        lemma_lits();
    }
    if ex_has_lit(s, b, &L_EMPTY) {
        Some(b + 5)
    } else if ex_has_lit(s, b, &L_ANY) {
        Some(b + 3)
    } else if ex_byte_is(s, b, 0x28) {
        let k = ex_ws_end(s, b + 1);
        if ex_has_lit(s, k, &L_PCDATA) {
            ex_mixed(s, k + 7)
        } else {
            ex_cmodel(s, b)
        }
    } else {
        None
    }
}

/// `element_decl` at `j`.
fn ex_element_decl(s: &[u8], j: usize, tape: &mut Tape) -> (r: Option<usize>)
    requires
        j + 9 <= s@.len() <= isize::MAX,
        old(tape)@.len() <= j,
    ensures
        match element_decl(s@, j as int, old(tape)@) {
            Some((t, e)) => r matches Some(x) && x == e && final(tape)@ == t && j < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> old(tape)@.len() <= final(tape)@.len(),
{
    let a = ex_ws_end(s, j + 9);
    let n = ex_name_end(s, a);
    let b = ex_ws_end(s, n);
    if a == j + 9 || n == a || b == n {
        return None;
    }
    match ex_contentspec(s, b) {
        None => None,
        Some(c) => {
            let e = ex_ws_end(s, c);
            if ex_byte_is(s, e, 0x3E) {
                tape.push(tok(Kind::ElementDecl, a, n, 0));
                Some(e + 1)
            } else {
                None
            }
        },
    }
}

/// `alt_list` from `i`.
fn ex_alt_list(s: &[u8], i: usize, nm: bool) -> (r: Option<usize>)
    requires
        i <= s@.len() <= isize::MAX,
    ensures
        same(r, alt_list(s@, i as int, nm)),
        r matches Some(e) ==> i < e <= s@.len(),
{
    let mut j = i;
    loop
        invariant
            i <= j <= s@.len() <= isize::MAX,
            alt_list(s@, j as int, nm) == alt_list(s@, i as int, nm),
        decreases s@.len() - j,
    {
        let k = ex_ws_end(s, j);
        let n = if nm {
            ex_nmtoken_end(s, k)
        } else {
            ex_name_end(s, k)
        };
        if n == k {
            return None;
        }
        let m = ex_ws_end(s, n);
        if ex_byte_is(s, m, 0x29) {
            return Some(m + 1);
        } else if ex_byte_is(s, m, 0x7C) {
            j = m + 1;
        } else {
            return None;
        }
    }
}

/// `att_type` at `k`.
fn ex_att_type(s: &[u8], k: usize) -> (r: Option<(usize, u8)>)
    requires
        k <= s@.len() <= isize::MAX,
    ensures
        match att_type(s@, k as int) {
            Some((e, ty)) => r matches Some((x, y)) && x == e && y == ty && k < e <= s@.len(),
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    if ex_has_lit(s, k, &L_CDATA_TY) {
        Some((k + 5, 1))
    } else if ex_has_lit(s, k, &L_IDREFS) {
        Some((k + 6, 4))
    } else if ex_has_lit(s, k, &L_IDREF) {
        Some((k + 5, 3))
    } else if ex_has_lit(s, k, &L_ID) {
        Some((k + 2, 2))
    } else if ex_has_lit(s, k, &L_ENTITIES) {
        Some((k + 8, 6))
    } else if ex_has_lit(s, k, &L_ENTITY_TY) {
        Some((k + 6, 5))
    } else if ex_has_lit(s, k, &L_NMTOKENS) {
        Some((k + 8, 8))
    } else if ex_has_lit(s, k, &L_NMTOKEN) {
        Some((k + 7, 7))
    } else if ex_has_lit(s, k, &L_NOTATION_TY) {
        let j = ex_ws_end(s, k + 8);
        if j > k + 8 && ex_byte_is(s, j, 0x28) {
            match ex_alt_list(s, j + 1, false) {
                Some(e) => Some((e, 9)),
                None => None,
            }
        } else {
            None
        }
    } else if ex_byte_is(s, k, 0x28) {
        match ex_alt_list(s, k + 1, true) {
            Some(e) => Some((e, 10)),
            None => None,
        }
    } else {
        None
    }
}

/// `default_decl` at `m`.
fn ex_default_decl(s: &[u8], m: usize) -> (r: Option<(usize, u8, usize, usize)>)
    requires
        m <= s@.len() <= isize::MAX,
    ensures
        match default_decl(s@, m as int) {
            Some((e, kind, va, vb)) => r matches Some((x, y, z, w)) && x == e && y == kind && z == va && w == vb
                && m < e <= s@.len() && va <= vb < s@.len() && 1 <= kind <= 4,
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    if ex_has_lit(s, m, &L_REQUIRED) {
        Some((m + 9, 1, m, m))
    } else if ex_has_lit(s, m, &L_IMPLIED) {
        Some((m + 8, 2, m, m))
    } else {
        let fixed = ex_has_lit(s, m, &L_FIXED);
        let v = if fixed {
            ex_ws_end(s, m + 6)
        } else {
            m
        };
        if fixed && v == m + 6 {
            return None;
        }
        if v < s.len() && (get(s, v) == 0x22 || get(s, v) == 0x27) {
            match ex_att_chars(s, v + 1, get(s, v), None, 0) {
                Some((q, _)) => Some((q + 1, if fixed { 3 } else { 4 }, v + 1, q)),
                None => None,
            }
        } else {
            None
        }
    }
}

/// `att_defs` from `i`.
fn ex_att_defs(s: &[u8], i: usize, tape: &mut Tape, nents: usize) -> (r: Option<usize>)
    requires
        i <= s@.len() <= isize::MAX,
        old(tape)@.len() <= i,
        nents <= isize::MAX,
    ensures
        match att_defs(s@, i as int, old(tape)@, nents as int) {
            Some((t, e)) => r matches Some(x) && x == e && final(tape)@ == t && i < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> old(tape)@.len() <= final(tape)@.len(),
{
    let mut j0 = i;
    loop
        invariant
            i <= j0 <= s@.len() <= isize::MAX,
            tape@.len() <= j0,
            old(tape)@.len() <= tape@.len(),
            nents <= isize::MAX,
            att_defs(s@, j0 as int, tape@, nents as int) == att_defs(s@, i as int, old(tape)@, nents as int),
        decreases s@.len() - j0,
    {
        let j = ex_ws_end(s, j0);
        if ex_byte_is(s, j, 0x3E) {
            return Some(j + 1);
        }
        if j == j0 {
            return None;
        }
        let n = ex_name_end(s, j);
        let k = ex_ws_end(s, n);
        if n == j || k == n {
            return None;
        }
        let (e, ty) = match ex_att_type(s, k) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let m = ex_ws_end(s, e);
        if m == e {
            return None;
        }
        match ex_default_decl(s, m) {
            None => {
                return None;
            },
            Some((d, kind, va, vb)) => {
                tape.push(tok(Kind::AttDef, j, n, ty));
                tape.push(Tok { kind: Kind::AttDefault, f: kind, a: va, b: vb, c: nents });
                j0 = d;
            },
        }
    }
}

/// `attlist_decl` at `j`.
fn ex_attlist_decl(s: &[u8], j: usize, tape: &mut Tape, nents: usize) -> (r: Option<usize>)
    requires
        j + 9 <= s@.len() <= isize::MAX,
        old(tape)@.len() <= j,
        nents <= isize::MAX,
    ensures
        match attlist_decl(s@, j as int, old(tape)@, nents as int) {
            Some((t, e)) => r matches Some(x) && x == e && final(tape)@ == t && j < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> old(tape)@.len() <= final(tape)@.len(),
{
    let a = ex_ws_end(s, j + 9);
    let n = ex_name_end(s, a);
    if a == j + 9 || n == a {
        return None;
    }
    tape.push(tok(Kind::AttlistDecl, a, n, 0));
    ex_att_defs(s, n, tape, nents)
}

/// `ent_def` at `c`: the end and the entity's kind and value span.
fn ex_ent_def(s: &[u8], c: usize, tape: &mut Tape, ge: bool) -> (r: Option<(usize, u8, usize, usize)>)
    requires
        c <= s@.len() <= isize::MAX,
        old(tape)@.len() <= c,
    ensures
        match ent_def(s@, c as int, old(tape)@, ge) {
            Some((t, e, kind)) => r matches Some((x, k, va, vb)) && x == e && final(tape)@ == t && c < e <= s@.len()
                && t.len() <= e && k <= 2 && va <= vb <= s@.len() && kind == kind_view(
                XEnt { a: 0, b: 0, kind: k, va, vb },
            ),
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    if c < s.len() && (get(s, c) == 0x22 || get(s, c) == 0x27) {
        match ex_ent_value_end(s, c + 1, get(s, c)) {
            Some(e) => {
                tape.push(tok(Kind::EntityValue, c + 1, e - 1, 0));
                Some((e, 0, c + 1, e - 1))
            },
            None => None,
        }
    } else {
        match ex_external_id(s, c, tape) {
            None => None,
            Some(e) => {
                let k = ex_ws_end(s, e);
                if ge && k > e && ex_has_lit(s, k, &L_NDATA) {
                    let m = ex_ws_end(s, k + 5);
                    let n = ex_name_end(s, m);
                    if m == k + 5 || n == m {
                        None
                    } else {
                        tape.push(tok(Kind::NData, m, n, 0));
                        Some((n, 2, 0, 0))
                    }
                } else {
                    Some((e, 1, 0, 0))
                }
            },
        }
    }
}

/// `entity_decl` at `j`.
fn ex_entity_decl(s: &[u8], j: usize, tape: &mut Tape, d: &mut XDtd) -> (r: Option<usize>)
    requires
        j + 8 <= s@.len() <= isize::MAX,
        old(tape)@.len() <= j,
        dtd_wf(s@, old(d)),
        old(d).ents@.len() <= old(tape)@.len(),
    ensures
        match entity_decl(s@, j as int, old(tape)@, dtd_view(s@, old(d))) {
            Some((t, st, e)) => r matches Some(x) && x == e && final(tape)@ == t && dtd_view(s@, final(d)) == st
                && j < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> dtd_wf(s@, final(d)) && final(d).ents@.len() <= final(tape)@.len(),
{
    let a = ex_ws_end(s, j + 8);
    if a == j + 8 {
        return None;
    }
    if ex_byte_is(s, a, 0x25) {
        let b = ex_ws_end(s, a + 1);
        let n = ex_name_end(s, b);
        let c = ex_ws_end(s, n);
        if b == a + 1 || n == b || c == n {
            return None;
        }
        tape.push(tok(Kind::EntityDecl, b, n, 1));
        match ex_ent_def(s, c, tape, false) {
            None => None,
            Some((e, _, _, _)) => {
                let f = ex_ws_end(s, e);
                if ex_byte_is(s, f, 0x3E) {
                    let ghost old_p = d.pes@;
                    d.pes.push((b, n));
                    proof {
                        assert(pes_view(s@, d.pes@) =~= pes_view(s@, old_p).push(s@.subrange(b as int, n as int)));
                    }
                    Some(f + 1)
                } else {
                    None
                }
            },
        }
    } else {
        let n = ex_name_end(s, a);
        let c = ex_ws_end(s, n);
        if n == a || c == n {
            return None;
        }
        tape.push(tok(Kind::EntityDecl, a, n, 0));
        match ex_ent_def(s, c, tape, true) {
            None => None,
            Some((e, kind, va, vb)) => {
                let f = ex_ws_end(s, e);
                if ex_byte_is(s, f, 0x3E) {
                    if !d.pe_seen || d.sa {
                        let x = XEnt { a, b: n, kind, va, vb };
                        let ghost old_e = d.ents@;
                        d.ents.push(x);
                        proof {
                            assert(ents_view(s@, d.ents@) =~= ents_view(s@, old_e).push(ent_view(s@, x)));
                            assert(kind_view(x) == kind_view(XEnt { a: 0, b: 0, kind, va, vb }));
                        }
                    }
                    Some(f + 1)
                } else {
                    None
                }
            },
        }
    }
}

/// `notation_decl` at `j`.
fn ex_notation_decl(s: &[u8], j: usize, tape: &mut Tape) -> (r: Option<usize>)
    requires
        j + 10 <= s@.len() <= isize::MAX,
        old(tape)@.len() <= j,
    ensures
        match notation_decl(s@, j as int, old(tape)@) {
            Some((t, e)) => r matches Some(x) && x == e && final(tape)@ == t && j < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> old(tape)@.len() <= final(tape)@.len(),
{
    proof {
        lemma_lits();
    }
    let a = ex_ws_end(s, j + 10);
    let n = ex_name_end(s, a);
    let b = ex_ws_end(s, n);
    if a == j + 10 || n == a || b == n {
        return None;
    }
    tape.push(tok(Kind::NotationDecl, a, n, 0));
    let e = if ex_has_lit(s, b, &L_PUBLIC) {
        let p = ex_ws_end(s, b + 6);
        if p == b + 6 {
            return None;
        }
        match ex_pubid_lit(s, p) {
            None => {
                return None;
            },
            Some(e) => {
                tape.push(tok(Kind::PubId, p + 1, e - 1, 0));
                let k = ex_ws_end(s, e);
                if k > e && k < s.len() && (get(s, k) == 0x22 || get(s, k) == 0x27) {
                    match ex_sys_lit(s, k) {
                        Some(f) => {
                            tape.push(tok(Kind::SysId, k + 1, f - 1, 0));
                            f
                        },
                        None => {
                            return None;
                        },
                    }
                } else {
                    e
                }
            },
        }
    } else {
        match ex_external_id(s, b, tape) {
            None => {
                return None;
            },
            Some(e) => e,
        }
    };
    let f = ex_ws_end(s, e);
    if ex_byte_is(s, f, 0x3E) {
        Some(f + 1)
    } else {
        None
    }
}

/// Whether the parameter entity named `s[a..b]` was declared.
fn ex_pes_contains(s: &[u8], d: &XDtd, a: usize, b: usize) -> (r: bool)
    requires
        a <= b <= s@.len(),
        dtd_wf(s@, d),
    ensures
        r == dtd_view(s@, d).pes.contains(s@.subrange(a as int, b as int)),
{
    let ghost ps = dtd_view(s@, d).pes;
    let ghost name = s@.subrange(a as int, b as int);
    let m = d.pes.len();
    let mut k: usize = 0;
    while k < m
        invariant
            k <= m,
            m == d.pes@.len(),
            ps == dtd_view(s@, d).pes,
            ps.len() == m,
            a <= b <= s@.len(),
            dtd_wf(s@, d),
            name == s@.subrange(a as int, b as int),
            forall|q: int| 0 <= q < k ==> ps[q] != name,
        decreases m - k,
    {
        let (x, y) = d.pes[k];
        proof {
            assert(ps[k as int] == s@.subrange(x as int, y as int));
            assert(d.pes@[k as int].0 <= d.pes@[k as int].1 <= s@.len());
        }
        if ex_bytes_eq(s, x as usize, y as usize, s, a, b) {
            proof {
                assert(ps[k as int] == name);
            }
            return true;
        }
        k = k + 1;
    }
    false
}

/// `pe_ref` at `j`.
fn ex_pe_ref(s: &[u8], j: usize, tape: &mut Tape, d: &mut XDtd) -> (r: Option<usize>)
    requires
        j < s@.len() <= isize::MAX,
        old(tape)@.len() <= j,
        dtd_wf(s@, old(d)),
        old(d).ents@.len() <= old(tape)@.len(),
    ensures
        match pe_ref(s@, j as int, old(tape)@, dtd_view(s@, old(d))) {
            Some((t, st, e)) => r matches Some(x) && x == e && final(tape)@ == t && dtd_view(s@, final(d)) == st
                && j < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> dtd_wf(s@, final(d)) && final(d).ents@.len() <= final(tape)@.len(),
{
    let n = ex_name_end(s, j + 1);
    if n == j + 1 || !ex_byte_is(s, n, 0x3B) {
        return None;
    }
    if d.sa && !ex_pes_contains(s, d, j + 1, n) {
        return None;
    }
    tape.push(tok(Kind::PERef, j + 1, n, 0));
    d.pe_seen = true;
    Some(n + 1)
}

/// `decl` at `j`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn ex_decl(s: &[u8], j: usize, tape: &mut Tape, d: &mut XDtd) -> (r: Option<usize>)
    requires
        j < s@.len() <= isize::MAX,
        old(tape)@.len() <= j,
        dtd_wf(s@, old(d)),
        old(d).ents@.len() <= old(tape)@.len(),
    ensures
        match decl(s@, j as int, old(tape)@, dtd_view(s@, old(d))) {
            Some((t, st, e)) => r matches Some(x) && x == e && final(tape)@ == t && dtd_view(s@, final(d)) == st
                && j < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> dtd_wf(s@, final(d)) && final(d).ents@.len() <= final(tape)@.len(),
{
    proof {
        lemma_lits();
    }
    if get(s, j) == 0x25 {
        ex_pe_ref(s, j, tape, d)
    } else if ex_has_lit(s, j, &L_ELEMENT) {
        ex_element_decl(s, j, tape)
    } else if ex_has_lit(s, j, &L_ATTLIST) {
        ex_attlist_decl(s, j, tape, d.ents.len())
    } else if ex_has_lit(s, j, &L_ENTITY) {
        ex_entity_decl(s, j, tape, d)
    } else if ex_has_lit(s, j, &L_NOTATION) {
        ex_notation_decl(s, j, tape)
    } else if ex_has_lit(s, j, &L_COMMENT) {
        ex_comment(s, j, tape)
    } else if ex_has2(s, j, 0x3C, 0x3F) {
        proof {
            assert(lit_pi() =~= seq![0x3Cu8, 0x3F]);
        }
        ex_pi(s, j, tape)
    } else {
        proof {
            assert(lit_pi() =~= seq![0x3Cu8, 0x3F]);
        }
        None
    }
}

/// `int_subset` from `i`: the position of the closing `]`.
fn ex_int_subset(s: &[u8], i: usize, tape: &mut Tape, d: &mut XDtd) -> (r: Option<usize>)
    requires
        i <= s@.len() <= isize::MAX,
        old(tape)@.len() <= i,
        dtd_wf(s@, old(d)),
        old(d).ents@.len() <= old(tape)@.len(),
    ensures
        match int_subset(s@, i as int, old(tape)@, dtd_view(s@, old(d))) {
            Some((t, st, e)) => r matches Some(x) && x == e && final(tape)@ == t && dtd_view(s@, final(d)) == st
                && i <= e < s@.len() && t.len() <= e,
            None => r is None,
        },
        r is Some ==> dtd_wf(s@, final(d)) && final(d).ents@.len() <= final(tape)@.len(),
{
    let mut j0 = i;
    loop
        invariant
            i <= j0 <= s@.len() <= isize::MAX,
            tape@.len() <= j0,
            dtd_wf(s@, d),
            d.ents@.len() <= tape@.len(),
            int_subset(s@, j0 as int, tape@, dtd_view(s@, d)) == int_subset(
                s@,
                i as int,
                old(tape)@,
                dtd_view(s@, old(d)),
            ),
        decreases s@.len() - j0,
    {
        let j = ex_ws_end(s, j0);
        if j >= s.len() {
            return None;
        }
        if get(s, j) == 0x5D {
            return Some(j);
        }
        match ex_decl(s, j, tape, d) {
            None => {
                tape.fail(j);
                return None;
            },
            Some(e) => {
                j0 = e;
            },
        }
    }
}

/// `doctype` at `i`: the end, and the environment of the content.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn ex_doctype(s: &[u8], i: usize, tape: &mut Tape, sa: bool) -> (r: Option<(usize, DtdOut)>)
    requires
        i + 9 <= s@.len() <= isize::MAX,
        old(tape)@.len() <= i,
    ensures
        match doctype(s@, i as int, old(tape)@, sa) {
            Some((t, e, env)) => r matches Some((x, xe)) && x == e && final(tape)@ == t && out_view(s@, &xe) == env
                && out_wf(s@, &xe) && i < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
{
    let j = ex_ws_end(s, i + 9);
    let n = ex_name_end(s, j);
    if j == i + 9 || n == j {
        return None;
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
                return None;
            },
        }
    } else {
        (n, false)
    };
    let m = ex_ws_end(s, e);
    let mut d = XDtd { ents: Vec::new(), pes: Vec::new(), pe_seen: false, sa };
    proof {
        assert(ents_view(s@, d.ents@) =~= Seq::<Ent>::empty());
        assert(pes_view(s@, d.pes@) =~= Seq::<Seq<u8>>::empty());
        assert(dtd_view(s@, &d) == dtd_init(sa));
    }
    if ex_byte_is(s, m, 0x5B) {
        match ex_int_subset(s, m + 1, tape, &mut d) {
            None => None,
            Some(q) => {
                let r = ex_ws_end(s, q + 1);
                if ex_byte_is(s, r, 0x3E) {
                    tape.push(tok(Kind::DoctypeEnd, 0, 0, 0));
                    Some((r + 1, ex_finish(s, d, ext)))
                } else {
                    None
                }
            },
        }
    } else if ex_byte_is(s, m, 0x3E) {
        tape.push(tok(Kind::DoctypeEnd, 0, 0, 0));
        proof {
            assert(dtd_wf(s@, &d));
        }
        Some((m + 1, ex_finish(s, d, ext)))
    } else {
        None
    }
}

} // verus!
