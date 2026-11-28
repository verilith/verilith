//! The parser: each function here computes one function of
//! `parse_spec.rs`, and is proven to return exactly what it returns.
//!
//! The standard's loops are loops here; recursion happens only one nesting
//! level deeper (a simple block, a function or a rule's block), so the
//! stack is bounded by `MAX_DEPTH` levels.
use crate::lex::Token;
#[cfg(verus_keep_ghost)]
use crate::lex::views;
use crate::parse_spec::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The tree
// ---------------------------------------------------------------------------

/// A component value. Indices are positions in the token slice parsed.
pub enum ComponentValue {
    /// A preserved token.
    Token(usize),
    /// A simple block: `start` is its `{`, `[` or `(` token, `end` the
    /// index after its closing token (or the number of tokens).
    Block { start: usize, end: usize, value: Vec<ComponentValue> },
    /// A function: `start` is its function token.
    Function { start: usize, end: usize, value: Vec<ComponentValue> },
}

impl View for ComponentValue {
    type V = SCV;

    open spec fn view(&self) -> SCV
        decreases self,
    {
        match self {
            ComponentValue::Token(i) => SCV::Tok { i: *i as int },
            ComponentValue::Block { start, end, value } => SCV::Block {
                start: *start as int,
                end: *end as int,
                value: Seq::new(value@.len(), |k: int| if 0 <= k < value@.len() { value@[k]@ } else { SCV::Tok { i: 0 } }),
            },
            ComponentValue::Function { start, end, value } => SCV::Func {
                start: *start as int,
                end: *end as int,
                value: Seq::new(value@.len(), |k: int| if 0 <= k < value@.len() { value@[k]@ } else { SCV::Tok { i: 0 } }),
            },
        }
    }
}

pub open spec fn cvs(v: Seq<ComponentValue>) -> Seq<SCV> {
    Seq::new(v.len(), |k: int| v[k]@)
}

/// A declaration. `name` is the index of its name's ident token.
pub struct Declaration {
    pub name: usize,
    pub value: Vec<ComponentValue>,
    pub important: bool,
    pub start: usize,
    pub end: usize,
    pub value_start: usize,
    pub value_end: usize,
}

impl View for Declaration {
    type V = SDecl;

    open spec fn view(&self) -> SDecl {
        SDecl {
            name: self.name as int,
            value: cvs(self.value@),
            important: self.important,
            start: self.start as int,
            end: self.end as int,
            value_start: self.value_start as int,
            value_end: self.value_end as int,
        }
    }
}

pub open spec fn decls_v(v: Seq<Declaration>) -> Seq<SDecl> {
    Seq::new(v.len(), |k: int| v[k]@)
}

/// A rule, or a list of declarations among a block's contents.
pub enum Item {
    /// An at-rule (`at`, named by the at-keyword token `start`) or a
    /// qualified rule. A `Declarations` item among a qualified rule's
    /// `children` is a nested declarations rule.
    Rule {
        at: bool,
        start: usize,
        end: usize,
        prelude: Vec<ComponentValue>,
        block: bool,
        declarations: Vec<Declaration>,
        children: Vec<Item>,
    },
    /// A list of declarations.
    Declarations(Vec<Declaration>),
}

impl View for Item {
    type V = SItem;

    open spec fn view(&self) -> SItem
        decreases self,
    {
        match self {
            Item::Rule { at, start, end, prelude, block, declarations, children } => SItem::Rule {
                at: *at,
                start: *start as int,
                end: *end as int,
                prelude: cvs(prelude@),
                block: *block,
                decls: decls_v(declarations@),
                children: Seq::new(
                    children@.len(),
                    |k: int| if 0 <= k < children@.len() { children@[k]@ } else { SItem::Decls { decls: seq![] } },
                ),
            },
            Item::Declarations(v) => SItem::Decls { decls: decls_v(v@) },
        }
    }
}

pub open spec fn items_v(v: Seq<Item>) -> Seq<SItem> {
    Seq::new(v.len(), |k: int| v[k]@)
}

proof fn lemma_cv_view(c: ComponentValue)
    ensures
        c matches ComponentValue::Block { start, end, value } ==> c@ == (SCV::Block {
            start: start as int,
            end: end as int,
            value: cvs(value@),
        }),
        c matches ComponentValue::Function { start, end, value } ==> c@ == (SCV::Func {
            start: start as int,
            end: end as int,
            value: cvs(value@),
        }),
{
    match c {
        ComponentValue::Block { value, .. } => {
            if let SCV::Block { value: s, .. } = c@ {
                assert(s =~= cvs(value@));
            }
        },
        ComponentValue::Function { value, .. } => {
            if let SCV::Func { value: s, .. } = c@ {
                assert(s =~= cvs(value@));
            }
        },
        _ => {},
    }
}

proof fn lemma_item_view(r: Item)
    ensures
        r matches Item::Rule { at, start, end, prelude, block, declarations, children } ==> r@ == (SItem::Rule {
            at,
            start: start as int,
            end: end as int,
            prelude: cvs(prelude@),
            block,
            decls: decls_v(declarations@),
            children: items_v(children@),
        }),
{
    match r {
        Item::Rule { children, .. } => {
            if let SItem::Rule { children: s, .. } = r@ {
                assert(s =~= items_v(children@));
            }
        },
        _ => {},
    }
}

proof fn lemma_cvs_push(v: Seq<ComponentValue>, c: ComponentValue)
    ensures
        cvs(v.push(c)) == cvs(v).push(c@),
{
    assert(cvs(v.push(c)) =~= cvs(v).push(c@));
}

proof fn lemma_decls_push(v: Seq<Declaration>, c: Declaration)
    ensures
        decls_v(v.push(c)) == decls_v(v).push(c@),
{
    assert(decls_v(v.push(c)) =~= decls_v(v).push(c@));
}

proof fn lemma_items_push(v: Seq<Item>, c: Item)
    ensures
        items_v(v.push(c)) == items_v(v).push(c@),
{
    assert(items_v(v.push(c)) =~= items_v(v).push(c@));
}

proof fn lemma_empty()
    ensures
        cvs(Seq::<ComponentValue>::empty()) == Seq::<SCV>::empty(),
        decls_v(Seq::<Declaration>::empty()) == Seq::<SDecl>::empty(),
        items_v(Seq::<Item>::empty()) == Seq::<SItem>::empty(),
{
    assert(cvs(Seq::<ComponentValue>::empty()) =~= Seq::<SCV>::empty());
    assert(decls_v(Seq::<Declaration>::empty()) =~= Seq::<SDecl>::empty());
    assert(items_v(Seq::<Item>::empty()) =~= Seq::<SItem>::empty());
}

/// Every value in `v` ends at or before `n`.
pub open spec fn ends_le(v: Seq<SCV>, n: int) -> bool {
    forall|m: int| 0 <= m < v.len() ==> #[trigger] cv_end(v[m]) <= n
}

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------

/// `a == b` (a derived `PartialEq` has no specification Verus can use).
pub fn kind_eq(a: Kind, b: Kind) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (Kind::Ident, Kind::Ident) => true,
        (Kind::Function, Kind::Function) => true,
        (Kind::AtKeyword, Kind::AtKeyword) => true,
        (Kind::String, Kind::String) => true,
        (Kind::BadString, Kind::BadString) => true,
        (Kind::Url, Kind::Url) => true,
        (Kind::BadUrl, Kind::BadUrl) => true,
        (Kind::Whitespace, Kind::Whitespace) => true,
        (Kind::Cdo, Kind::Cdo) => true,
        (Kind::Cdc, Kind::Cdc) => true,
        (Kind::Colon, Kind::Colon) => true,
        (Kind::Semicolon, Kind::Semicolon) => true,
        (Kind::Comma, Kind::Comma) => true,
        (Kind::LeftBracket, Kind::LeftBracket) => true,
        (Kind::RightBracket, Kind::RightBracket) => true,
        (Kind::LeftParen, Kind::LeftParen) => true,
        (Kind::RightParen, Kind::RightParen) => true,
        (Kind::LeftBrace, Kind::LeftBrace) => true,
        (Kind::RightBrace, Kind::RightBrace) => true,
        (Kind::Hash { id: x }, Kind::Hash { id: y }) => x == y,
        (Kind::Delim(x), Kind::Delim(y)) => x == y,
        (Kind::Number { integer: x }, Kind::Number { integer: y }) => x == y,
        (Kind::Percentage { integer: x }, Kind::Percentage { integer: y }) => x == y,
        (Kind::Dimension { integer: x }, Kind::Dimension { integer: y }) => x == y,
        _ => false,
    }
}

fn x_tk(ts: &[Token], i: usize, k: Kind) -> (r: bool)
    ensures
        r == tk(views(ts@), i as int, k),
{
    if i < ts.len() {
        let r = kind_eq(ts[i].kind, k);
        proof {
            assert(views(ts@)[i as int] == ts@[i as int]@);
        }
        r
    } else {
        false
    }
}

fn x_is_open(k: Kind) -> (r: bool)
    ensures
        r == is_open(k),
{
    match k {
        Kind::LeftBrace => true,
        Kind::LeftBracket => true,
        Kind::LeftParen => true,
        _ => false,
    }
}

fn x_closer(k: Kind) -> (r: Kind)
    ensures
        r == closer(k),
{
    match k {
        Kind::LeftBrace => Kind::RightBrace,
        Kind::LeftBracket => Kind::RightBracket,
        _ => Kind::RightParen,
    }
}

fn x_skip_ws(ts: &[Token], i: usize) -> (r: usize)
    requires
        i <= ts.len(),
    ensures
        r == skip_ws(views(ts@), i as int),
        i <= r <= ts.len(),
{
    let mut k = i;
    while x_tk(ts, k, Kind::Whitespace)
        invariant
            i <= k <= ts.len(),
            skip_ws(views(ts@), k as int) == skip_ws(views(ts@), i as int),
        decreases ts.len() - k,
    {
        k += 1;
    }
    k
}

fn x_is_ws_cv(ts: &[Token], c: &ComponentValue) -> (r: bool)
    ensures
        r == is_ws_cv(views(ts@), c@),
{
    match c {
        ComponentValue::Token(i) => x_tk(ts, *i, Kind::Whitespace),
        _ => false,
    }
}

fn x_cv_end(c: &ComponentValue, n: usize) -> (r: usize)
    requires
        cv_end(c@) <= n,
    ensures
        r == cv_end(c@),
{
    match c {
        ComponentValue::Token(i) => *i + 1,
        ComponentValue::Block { end, .. } => *end,
        ComponentValue::Function { end, .. } => *end,
    }
}

// ---------------------------------------------------------------------------
// §5.5.8 - §5.5.10 Component values, simple blocks and functions
// ---------------------------------------------------------------------------

fn x_cv(ts: &[Token], i: usize, d: usize) -> (r: Option<(ComponentValue, usize)>)
    requires
        i < ts.len(),
    ensures
        match r {
            None => cv(views(ts@), i as int, d as nat) is None,
            Some((c, j)) => cv(views(ts@), i as int, d as nat) == Some((c@, j as int)) && i < j <= ts.len()
                && cv_end(c@) == j,
        },
    decreases d, ts.len() - i, 0int,
{
    proof {
        assert(views(ts@)[i as int] == ts@[i as int]@);
    }
    let k = ts[i].kind;
    let is_fn = kind_eq(k, Kind::Function);
    if x_is_open(k) || is_fn {
        if d == 0 {
            return None;
        }
        let close = if is_fn {
            Kind::RightParen
        } else {
            x_closer(k)
        };
        match x_block_body(ts, i + 1, close, d - 1) {
            None => None,
            Some((v, j)) => {
                let c = if is_fn {
                    ComponentValue::Function { start: i, end: j, value: v }
                } else {
                    ComponentValue::Block { start: i, end: j, value: v }
                };
                proof {
                    lemma_cv_view(c);
                }
                Some((c, j))
            },
        }
    } else {
        Some((ComponentValue::Token(i), i + 1))
    }
}

fn x_block_body(ts: &[Token], i: usize, close: Kind, d: usize) -> (r: Option<(Vec<ComponentValue>, usize)>)
    requires
        i <= ts.len(),
    ensures
        match r {
            None => block_body(views(ts@), i as int, close, seq![], d as nat) is None,
            Some((v, j)) => block_body(views(ts@), i as int, close, seq![], d as nat) == Some((cvs(v@), j as int))
                && i <= j <= ts.len(),
        },
    decreases d, ts.len() - i, 1int,
{
    let mut acc: Vec<ComponentValue> = Vec::new();
    let mut k = i;
    proof {
        lemma_empty();
    }
    loop
        invariant
            i <= k <= ts.len(),
            block_body(views(ts@), k as int, close, cvs(acc@), d as nat) == block_body(
                views(ts@),
                i as int,
                close,
                seq![],
                d as nat,
            ),
        decreases ts.len() - k,
    {
        if k >= ts.len() {
            return Some((acc, k));
        }
        if x_tk(ts, k, close) {
            return Some((acc, k + 1));
        }
        match x_cv(ts, k, d) {
            None => return None,
            Some((c, j)) => {
                proof {
                    lemma_cvs_push(acc@, c);
                }
                acc.push(c);
                k = j;
            },
        }
    }
}

fn x_is_stop(ts: &[Token], k: usize, stop: Option<Kind>) -> (r: bool)
    requires
        k < ts.len(),
    ensures
        r == (stop == Some(views(ts@)[k as int].kind)),
{
    proof {
        assert(views(ts@)[k as int] == ts@[k as int]@);
    }
    match stop {
        Some(s) => kind_eq(s, ts[k].kind),
        None => false,
    }
}

fn x_cv_list(ts: &[Token], i: usize, stop: Option<Kind>, nested: bool, d: usize) -> (r: Option<(Vec<ComponentValue>, usize)>)
    requires
        i <= ts.len(),
    ensures
        match r {
            None => cv_list(views(ts@), i as int, stop, nested, seq![], d as nat) is None,
            Some((v, j)) => cv_list(views(ts@), i as int, stop, nested, seq![], d as nat) == Some((cvs(v@), j as int))
                && i <= j <= ts.len() && ends_le(cvs(v@), j as int),
        },
    decreases d, ts.len() - i, 1int,
{
    let mut acc: Vec<ComponentValue> = Vec::new();
    let mut k = i;
    proof {
        lemma_empty();
    }
    loop
        invariant
            i <= k <= ts.len(),
            cv_list(views(ts@), k as int, stop, nested, cvs(acc@), d as nat) == cv_list(
                views(ts@),
                i as int,
                stop,
                nested,
                seq![],
                d as nat,
            ),
            ends_le(cvs(acc@), k as int),
        decreases ts.len() - k,
    {
        if k >= ts.len() || x_is_stop(ts, k, stop) {
            return Some((acc, k));
        }
        if x_tk(ts, k, Kind::RightBrace) {
            if nested {
                return Some((acc, k));
            }
            let c = ComponentValue::Token(k);
            proof {
                lemma_cvs_push(acc@, c);
            }
            acc.push(c);
            k += 1;
        } else {
            match x_cv(ts, k, d) {
                None => return None,
                Some((c, j)) => {
                    proof {
                        lemma_cvs_push(acc@, c);
                    }
                    acc.push(c);
                    k = j;
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §5.5.6 Declarations
// ---------------------------------------------------------------------------

fn x_bad_decl_end(ts: &[Token], i: usize, nested: bool, d: usize) -> (r: Option<usize>)
    requires
        i <= ts.len(),
    ensures
        match r {
            None => bad_decl_end(views(ts@), i as int, nested, d as nat) is None,
            Some(e) => bad_decl_end(views(ts@), i as int, nested, d as nat) == Some(e as int) && i <= e <= ts.len()
                && (i < ts.len() && !tk(views(ts@), i as int, Kind::RightBrace) ==> e > i),
        },
    decreases d, ts.len() - i, 1int,
{
    let mut k = i;
    loop
        invariant
            i <= k <= ts.len(),
            bad_decl_end(views(ts@), k as int, nested, d as nat) == bad_decl_end(views(ts@), i as int, nested, d as nat),
        decreases ts.len() - k,
    {
        if k >= ts.len() {
            return Some(k);
        }
        if x_tk(ts, k, Kind::Semicolon) {
            return Some(k + 1);
        }
        if x_tk(ts, k, Kind::RightBrace) {
            if nested {
                return Some(k);
            }
            k += 1;
        } else {
            match x_cv(ts, k, d) {
                None => return None,
                Some((_, j)) => {
                    k = j;
                },
            }
        }
    }
}

fn x_last_non_ws(ts: &[Token], v: &Vec<ComponentValue>, k: usize) -> (r: Option<usize>)
    requires
        k <= v.len(),
    ensures
        match r {
            None => last_non_ws(views(ts@), cvs(v@), k as int) == -1,
            Some(a) => last_non_ws(views(ts@), cvs(v@), k as int) == a && a < k,
        },
{
    let mut m = k;
    while m > 0 && x_is_ws_cv(ts, &v[m - 1])
        invariant
            m <= k <= v.len(),
            last_non_ws(views(ts@), cvs(v@), m as int) == last_non_ws(views(ts@), cvs(v@), k as int),
        decreases m,
    {
        m -= 1;
    }
    if m == 0 {
        None
    } else {
        Some(m - 1)
    }
}

#[inline(always)]
fn x_lower(c: u32) -> (r: u32)
    ensures
        r == lower(c),
{
    if 0x41 <= c && c <= 0x5A {
        c + 0x20
    } else {
        c
    }
}

fn x_important_name(v: &Vec<u32>) -> (r: bool)
    ensures
        r == is_important_name(v@),
{
    v.len() == 9 && x_lower(v[0]) == 0x69 && x_lower(v[1]) == 0x6D && x_lower(v[2]) == 0x70 && x_lower(v[3]) == 0x6F
        && x_lower(v[4]) == 0x72 && x_lower(v[5]) == 0x74 && x_lower(v[6]) == 0x61 && x_lower(v[7]) == 0x6E
        && x_lower(v[8]) == 0x74
}

fn x_is_bang(ts: &[Token], c: &ComponentValue) -> (r: bool)
    ensures
        r == is_delim_tok(views(ts@), c@, 0x21),
{
    match c {
        ComponentValue::Token(i) => x_tk(ts, *i, Kind::Delim(0x21)),
        _ => false,
    }
}

fn x_is_important(ts: &[Token], c: &ComponentValue) -> (r: bool)
    ensures
        r == is_important_tok(views(ts@), c@),
{
    match c {
        ComponentValue::Token(i) => {
            if x_tk(ts, *i, Kind::Ident) {
                proof {
                    assert(views(ts@)[*i as int] == ts@[*i as int]@);
                }
                x_important_name(&ts[*i].value)
            } else {
                false
            }
        },
        _ => false,
    }
}

fn x_strip_important(ts: &[Token], v: Vec<ComponentValue>, Ghost(n): Ghost<int>) -> (r: (Vec<ComponentValue>, bool))
    requires
        ends_le(cvs(v@), n),
    ensures
        (cvs(r.0@), r.1) == strip_important(views(ts@), cvs(v@)),
        ends_le(cvs(r.0@), n),
{
    let ghost sv = cvs(v@);
    let a = x_last_non_ws(ts, &v, v.len());
    match a {
        None => (v, false),
        Some(a) => {
            let b = x_last_non_ws(ts, &v, a);
            match b {
                None => (v, false),
                Some(b) => {
                    if x_is_bang(ts, &v[b]) && x_is_important(ts, &v[a]) {
                        let mut w = v;
                        w.remove(a);
                        w.remove(b);
                        proof {
                            assert(cvs(w@) =~= sv.remove(a as int).remove(b as int));
                            assert forall|m: int| 0 <= m < cvs(w@).len() implies #[trigger] cv_end(cvs(w@)[m]) <= n by {
                                let s1 = sv.remove(a as int);
                                if m < b {
                                    assert(cvs(w@)[m] == sv[m]);
                                } else if m + 1 < a {
                                    assert(cvs(w@)[m] == s1[m + 1]);
                                    assert(s1[m + 1] == sv[m + 1]);
                                } else {
                                    assert(cvs(w@)[m] == s1[m + 1]);
                                    assert(s1[m + 1] == sv[m + 2]);
                                }
                            }
                        }
                        (w, true)
                    } else {
                        (v, false)
                    }
                },
            }
        },
    }
}

fn x_strip_ws(ts: &[Token], v: Vec<ComponentValue>, Ghost(n): Ghost<int>) -> (r: Vec<ComponentValue>)
    requires
        ends_le(cvs(v@), n),
    ensures
        cvs(r@) == strip_ws(views(ts@), cvs(v@)),
        ends_le(cvs(r@), n),
{
    let mut w = v;
    while w.len() > 0 && x_is_ws_cv(ts, &w[w.len() - 1])
        invariant
            strip_ws(views(ts@), cvs(w@)) == strip_ws(views(ts@), cvs(v@)),
            ends_le(cvs(w@), n),
        decreases w.len(),
    {
        let ghost w0 = w@;
        proof {
            assert(cvs(w0).drop_last() =~= cvs(w0.drop_last()));
        }
        w.pop();
        proof {
            assert forall|m: int| 0 <= m < cvs(w@).len() implies #[trigger] cv_end(cvs(w@)[m]) <= n by {
                assert(cvs(w@)[m] == cvs(w0)[m]);
            }
        }
    }
    w
}


fn x_counts(ts: &[Token], v: &Vec<ComponentValue>) -> (r: (usize, usize))
    ensures
        r.0 == brace_count(views(ts@), cvs(v@), v.len() as int),
        r.1 == non_ws_count(views(ts@), cvs(v@), v.len() as int),
{
    let mut braces: usize = 0;
    let mut others: usize = 0;
    let mut k: usize = 0;
    while k < v.len()
        invariant
            k <= v.len(),
            braces == brace_count(views(ts@), cvs(v@), k as int),
            others == non_ws_count(views(ts@), cvs(v@), k as int),
            braces <= k,
            others <= k,
        decreases v.len() - k,
    {
        match &v[k] {
            ComponentValue::Block { start, .. } => {
                if x_tk(ts, *start, Kind::LeftBrace) {
                    braces += 1;
                }
            },
            _ => {},
        }
        if !x_is_ws_cv(ts, &v[k]) {
            others += 1;
        }
        k += 1;
    }
    (braces, others)
}

fn x_is_custom(v: &Vec<u32>) -> (r: bool)
    ensures
        r == is_custom(v@),
{
    v.len() >= 2 && v[0] == 0x2D && v[1] == 0x2D
}

fn x_decl(ts: &[Token], i: usize, nested: bool, d: usize) -> (r: Option<(Option<Declaration>, usize)>)
    requires
        i <= ts.len(),
    ensures
        match r {
            None => decl(views(ts@), i as int, nested, d as nat) is None,
            Some((None, e)) => decl(views(ts@), i as int, nested, d as nat) == Some((None::<SDecl>, e as int)) && e <= ts.len(),
            Some((Some(dl), e)) => decl(views(ts@), i as int, nested, d as nat) == Some((Some(dl@), e as int)) && i < e
                <= ts.len(),
        },
    decreases d, ts.len() - i, 2int,
{
    if !x_tk(ts, i, Kind::Ident) {
        return match x_bad_decl_end(ts, i, nested, d) {
            None => None,
            Some(e) => Some((None, e)),
        };
    }
    let j = x_skip_ws(ts, i + 1);
    if !x_tk(ts, j, Kind::Colon) {
        return match x_bad_decl_end(ts, j, nested, d) {
            None => None,
            Some(e) => Some((None, e)),
        };
    }
    let k = x_skip_ws(ts, j + 1);
    match x_cv_list(ts, k, Some(Kind::Semicolon), nested, d) {
        None => None,
        Some((v, e)) => {
            let (v2, important) = x_strip_important(ts, v, Ghost(e as int));
            let v3 = x_strip_ws(ts, v2, Ghost(e as int));
            let (braces, others) = x_counts(ts, &v3);
            proof {
                assert(views(ts@)[i as int] == ts@[i as int]@);
            }
            if !x_is_custom(&ts[i].value) && braces > 0 && others >= 2 {
                Some((None, e))
            } else {
                let value_end = if v3.len() == 0 {
                    k
                } else {
                    proof {
                        assert(cvs(v3@)[v3.len() - 1] == cvs(v3@).last());
                    }
                    x_cv_end(&v3[v3.len() - 1], e)
                };
                let dl = Declaration { name: i, value: v3, important, start: i, end: e, value_start: k, value_end };
                Some((Some(dl), e))
            }
        },
    }
}

// ---------------------------------------------------------------------------
// §5.5.4 Blocks and §5.5.5 block contents
// ---------------------------------------------------------------------------

fn x_block(ts: &[Token], i: usize, d: usize) -> (r: Option<(Vec<Item>, usize)>)
    requires
        i < ts.len(),
    ensures
        match r {
            None => block(views(ts@), i as int, d as nat) is None,
            Some((v, j)) => block(views(ts@), i as int, d as nat) == Some((items_v(v@), j as int)) && i < j <= ts.len(),
        },
    decreases d, ts.len() - i, 1int,
{
    if d == 0 {
        return None;
    }
    match x_contents(ts, i + 1, d - 1) {
        None => None,
        Some((items, j)) => {
            if x_tk(ts, j, Kind::RightBrace) {
                Some((items, j + 1))
            } else {
                Some((items, j))
            }
        },
    }
}

fn x_flush(rules: &mut Vec<Item>, decls: Vec<Declaration>)
    ensures
        items_v(final(rules)@) == flush(items_v(old(rules)@), decls_v(decls@)),
{
    if decls.len() > 0 {
        let it = Item::Declarations(decls);
        proof {
            lemma_items_push(rules@, it);
        }
        rules.push(it);
    }
}

fn x_contents(ts: &[Token], i: usize, d: usize) -> (r: Option<(Vec<Item>, usize)>)
    requires
        i <= ts.len(),
    ensures
        match r {
            None => contents(views(ts@), i as int, seq![], seq![], d as nat) is None,
            Some((v, j)) => contents(views(ts@), i as int, seq![], seq![], d as nat) == Some((items_v(v@), j as int))
                && i <= j <= ts.len(),
        },
    decreases d, ts.len() - i, 3int,
{
    let mut rules: Vec<Item> = Vec::new();
    let mut decls: Vec<Declaration> = Vec::new();
    let mut k = i;
    proof {
        lemma_empty();
    }
    loop
        invariant
            i <= k <= ts.len(),
            contents(views(ts@), k as int, items_v(rules@), decls_v(decls@), d as nat) == contents(
                views(ts@),
                i as int,
                seq![],
                seq![],
                d as nat,
            ),
        decreases ts.len() - k,
    {
        if k >= ts.len() || x_tk(ts, k, Kind::RightBrace) {
            x_flush(&mut rules, decls);
            return Some((rules, k));
        }
        if x_tk(ts, k, Kind::Whitespace) || x_tk(ts, k, Kind::Semicolon) {
            k += 1;
        } else if x_tk(ts, k, Kind::AtKeyword) {
            match x_at_rule(ts, k, true, d) {
                None => return None,
                Some((r, e)) => {
                    x_flush(&mut rules, decls);
                    decls = Vec::new();
                    proof {
                        lemma_items_push(rules@, r);
                        lemma_empty();
                    }
                    rules.push(r);
                    k = e;
                },
            }
        } else {
            match x_decl(ts, k, true, d) {
                None => return None,
                Some((Some(dl), e)) => {
                    proof {
                        lemma_decls_push(decls@, dl);
                    }
                    decls.push(dl);
                    k = e;
                },
                Some((None, _)) => match x_q_rule(ts, k, Some(Kind::Semicolon), true, d) {
                    None => return None,
                    Some((None, e)) => {
                        k = e;
                    },
                    Some((Some(r), e)) => {
                        x_flush(&mut rules, decls);
                        decls = Vec::new();
                        proof {
                            lemma_items_push(rules@, r);
                            lemma_empty();
                        }
                        rules.push(r);
                        k = e;
                    },
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §5.5.2 At-rules and §5.5.3 qualified rules
// ---------------------------------------------------------------------------

fn x_at_rule(ts: &[Token], start: usize, nested: bool, d: usize) -> (r: Option<(Item, usize)>)
    requires
        start < ts.len(),
    ensures
        match r {
            None => at_rule(views(ts@), start + 1, start as int, seq![], nested, d as nat) is None,
            Some((it, e)) => at_rule(views(ts@), start + 1, start as int, seq![], nested, d as nat) == Some((it@, e as int))
                && start < e <= ts.len(),
        },
    decreases d, ts.len() - start, 2int,
{
    let mut pre: Vec<ComponentValue> = Vec::new();
    let mut k = start + 1;
    proof {
        lemma_empty();
    }
    loop
        invariant
            start < k <= ts.len(),
            at_rule(views(ts@), k as int, start as int, cvs(pre@), nested, d as nat) == at_rule(
                views(ts@),
                start + 1,
                start as int,
                seq![],
                nested,
                d as nat,
            ),
        decreases ts.len() - k,
    {
        if k >= ts.len() || x_tk(ts, k, Kind::Semicolon) || (nested && x_tk(ts, k, Kind::RightBrace)) {
            let e = if k < ts.len() && x_tk(ts, k, Kind::Semicolon) {
                k + 1
            } else {
                k
            };
            let it = Item::Rule {
                at: true,
                start,
                end: e,
                prelude: pre,
                block: false,
                declarations: Vec::new(),
                children: Vec::new(),
            };
            proof {
                lemma_item_view(it);
                lemma_empty();
            }
            return Some((it, e));
        }
        if x_tk(ts, k, Kind::RightBrace) {
            let c = ComponentValue::Token(k);
            proof {
                lemma_cvs_push(pre@, c);
            }
            pre.push(c);
            k += 1;
        } else if x_tk(ts, k, Kind::LeftBrace) {
            match x_block(ts, k, d) {
                None => return None,
                Some((items, e)) => {
                    let it = Item::Rule {
                        at: true,
                        start,
                        end: e,
                        prelude: pre,
                        block: true,
                        declarations: Vec::new(),
                        children: items,
                    };
                    proof {
                        lemma_item_view(it);
                        lemma_empty();
                    }
                    return Some((it, e));
                },
            }
        } else {
            match x_cv(ts, k, d) {
                None => return None,
                Some((c, j)) => {
                    proof {
                        lemma_cvs_push(pre@, c);
                    }
                    pre.push(c);
                    k = j;
                },
            }
        }
    }
}

fn x_first_non_ws(ts: &[Token], v: &Vec<ComponentValue>, k: usize) -> (r: usize)
    requires
        k <= v.len(),
    ensures
        r == first_non_ws(views(ts@), cvs(v@), k as int),
        k <= r <= v.len(),
{
    let mut m = k;
    while m < v.len() && x_is_ws_cv(ts, &v[m])
        invariant
            k <= m <= v.len(),
            first_non_ws(views(ts@), cvs(v@), m as int) == first_non_ws(views(ts@), cvs(v@), k as int),
        decreases v.len() - m,
    {
        m += 1;
    }
    m
}

fn x_custom_prelude(ts: &[Token], pre: &Vec<ComponentValue>) -> (r: bool)
    ensures
        r == custom_prelude(views(ts@), cvs(pre@)),
{
    let a = x_first_non_ws(ts, pre, 0);
    if a >= pre.len() {
        return false;
    }
    let b = x_first_non_ws(ts, pre, a + 1);
    if b >= pre.len() {
        return false;
    }
    match (&pre[a], &pre[b]) {
        (ComponentValue::Token(x), ComponentValue::Token(y)) => {
            if x_tk(ts, *x, Kind::Ident) {
                proof {
                    assert(views(ts@)[*x as int] == ts@[*x as int]@);
                }
                x_is_custom(&ts[*x].value) && x_tk(ts, *y, Kind::Colon)
            } else {
                false
            }
        },
        _ => false,
    }
}

fn x_split(items: Vec<Item>) -> (r: (Vec<Declaration>, Vec<Item>))
    ensures
        (decls_v(r.0@), items_v(r.1@)) == split_decls(items_v(items@)),
{
    let first_is_decls = items.len() > 0 && match &items[0] {
        Item::Declarations(_) => true,
        _ => false,
    };
    if first_is_decls {
        let mut rest = items;
        let first = rest.remove(0);
        proof {
            assert(items_v(rest@) =~= items_v(items@).drop_first());
        }
        match first {
            Item::Declarations(ds) => (ds, rest),
            _ => {
                proof {
                    assert(false);
                }
                (Vec::new(), rest)
            },
        }
    } else {
        proof {
            lemma_empty();
        }
        (Vec::new(), items)
    }
}

fn x_q_rule(ts: &[Token], start: usize, stop: Option<Kind>, nested: bool, d: usize) -> (r: Option<(Option<Item>, usize)>)
    requires
        start <= ts.len(),
    ensures
        match r {
            None => q_rule(views(ts@), start as int, start as int, seq![], stop, nested, d as nat) is None,
            Some((None, e)) => q_rule(views(ts@), start as int, start as int, seq![], stop, nested, d as nat) == Some(
                (None::<SItem>, e as int),
            ) && start <= e <= ts.len(),
            Some((Some(it), e)) => q_rule(views(ts@), start as int, start as int, seq![], stop, nested, d as nat) == Some(
                (Some(it@), e as int),
            ) && start <= e <= ts.len(),
        },
        // It consumes something unless it stops at once.
        match r {
            Some((_, e)) => start < ts.len() && stop != Some(views(ts@)[start as int].kind) && !(nested && tk(
                views(ts@),
                start as int,
                Kind::RightBrace,
            )) ==> e > start,
            None => true,
        },
    decreases d, ts.len() - start, 2int,
{
    let mut pre: Vec<ComponentValue> = Vec::new();
    let mut k = start;
    proof {
        lemma_empty();
    }
    loop
        invariant
            start <= k <= ts.len(),
            q_rule(views(ts@), k as int, start as int, cvs(pre@), stop, nested, d as nat) == q_rule(
                views(ts@),
                start as int,
                start as int,
                seq![],
                stop,
                nested,
                d as nat,
            ),
        decreases ts.len() - k,
    {
        if k >= ts.len() || x_is_stop(ts, k, stop) {
            return Some((None, k));
        }
        if x_tk(ts, k, Kind::RightBrace) {
            if nested {
                return Some((None, k));
            }
            let c = ComponentValue::Token(k);
            proof {
                lemma_cvs_push(pre@, c);
            }
            pre.push(c);
            k += 1;
        } else if x_tk(ts, k, Kind::LeftBrace) {
            if x_custom_prelude(ts, &pre) {
                if nested {
                    return match x_bad_decl_end(ts, k, true, d) {
                        None => None,
                        Some(e) => Some((None, e)),
                    };
                } else {
                    return match x_block(ts, k, d) {
                        None => None,
                        Some((_, e)) => Some((None, e)),
                    };
                }
            }
            match x_block(ts, k, d) {
                None => return None,
                Some((items, e)) => {
                    let (declarations, children) = x_split(items);
                    let it = Item::Rule { at: false, start, end: e, prelude: pre, block: true, declarations, children };
                    proof {
                        lemma_item_view(it);
                    }
                    return Some((Some(it), e));
                },
            }
        } else {
            match x_cv(ts, k, d) {
                None => return None,
                Some((c, j)) => {
                    proof {
                        lemma_cvs_push(pre@, c);
                    }
                    pre.push(c);
                    k = j;
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §5.5.1 Stylesheets and §5.4 entry points
// ---------------------------------------------------------------------------

/// §5.4.4 Parse a stylesheet's contents, from its tokens: the rules, or
/// `None` if it nests deeper than `MAX_DEPTH`. Proven equal to
/// `parse_spec::parse_stylesheet`.
pub fn parse_stylesheet(ts: &[Token]) -> (r: Option<Vec<Item>>)
    ensures
        match r {
            None => crate::parse_spec::parse_stylesheet(views(ts@)) is None,
            Some(v) => crate::parse_spec::parse_stylesheet(views(ts@)) == Some(items_v(v@)),
        },
{
    let d = MAX_DEPTH;
    let mut rules: Vec<Item> = Vec::new();
    let mut k: usize = 0;
    proof {
        lemma_empty();
    }
    loop
        invariant
            k <= ts.len(),
            d == MAX_DEPTH,
            sheet(views(ts@), k as int, items_v(rules@), d as nat) == sheet(views(ts@), 0, seq![], d as nat),
        decreases ts.len() - k,
    {
        if k >= ts.len() {
            return Some(rules);
        }
        if x_tk(ts, k, Kind::Whitespace) || x_tk(ts, k, Kind::Cdo) || x_tk(ts, k, Kind::Cdc) {
            k += 1;
        } else if x_tk(ts, k, Kind::AtKeyword) {
            match x_at_rule(ts, k, false, d) {
                None => return None,
                Some((r, e)) => {
                    proof {
                        lemma_items_push(rules@, r);
                    }
                    rules.push(r);
                    k = e;
                },
            }
        } else {
            match x_q_rule(ts, k, None, false, d) {
                None => return None,
                Some((None, e)) => {
                    k = e;
                },
                Some((Some(r), e)) => {
                    proof {
                        lemma_items_push(rules@, r);
                    }
                    rules.push(r);
                    k = e;
                },
            }
        }
    }
}

/// §5.4.5 Parse a block's contents, such as a `style` attribute's: the
/// rules and lists of declarations, or `None` if it nests deeper than
/// `MAX_DEPTH`.
pub fn parse_block_contents(ts: &[Token]) -> (r: Option<Vec<Item>>)
    ensures
        match r {
            None => crate::parse_spec::parse_block_contents(views(ts@)) is None,
            Some(v) => crate::parse_spec::parse_block_contents(views(ts@)) == Some(items_v(v@)),
        },
{
    match x_contents(ts, 0, MAX_DEPTH) {
        None => None,
        Some((v, _)) => Some(v),
    }
}

/// §5.4.9 Parse a list of component values, or `None` if they nest deeper
/// than `MAX_DEPTH`.
pub fn parse_component_values(ts: &[Token]) -> (r: Option<Vec<ComponentValue>>)
    ensures
        match r {
            None => crate::parse_spec::parse_component_values(views(ts@)) is None,
            Some(v) => crate::parse_spec::parse_component_values(views(ts@)) == Some(cvs(v@)),
        },
{
    match x_cv_list(ts, 0, None, false, MAX_DEPTH) {
        None => None,
        Some((v, _)) => Some(v),
    }
}

} // verus!

// Plain Rust conveniences for the tree types, outside the verified code (a
// derive on a recursive type is a cycle to Verus).
impl Clone for ComponentValue {
    fn clone(&self) -> Self {
        match self {
            ComponentValue::Token(i) => ComponentValue::Token(*i),
            ComponentValue::Block { start, end, value } => ComponentValue::Block { start: *start, end: *end, value: value.clone() },
            ComponentValue::Function { start, end, value } => {
                ComponentValue::Function { start: *start, end: *end, value: value.clone() }
            }
        }
    }
}

impl PartialEq for ComponentValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ComponentValue::Token(a), ComponentValue::Token(b)) => a == b,
            (
                ComponentValue::Block { start: a, end: b, value: c },
                ComponentValue::Block { start: x, end: y, value: z },
            )
            | (
                ComponentValue::Function { start: a, end: b, value: c },
                ComponentValue::Function { start: x, end: y, value: z },
            ) => a == x && b == y && c == z,
            _ => false,
        }
    }
}

impl Eq for ComponentValue {}

impl std::fmt::Debug for ComponentValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComponentValue::Token(i) => f.debug_tuple("Token").field(i).finish(),
            ComponentValue::Block { start, end, value } => {
                f.debug_struct("Block").field("start", start).field("end", end).field("value", value).finish()
            }
            ComponentValue::Function { start, end, value } => {
                f.debug_struct("Function").field("start", start).field("end", end).field("value", value).finish()
            }
        }
    }
}

impl Clone for Declaration {
    fn clone(&self) -> Self {
        Declaration {
            name: self.name,
            value: self.value.clone(),
            important: self.important,
            start: self.start,
            end: self.end,
            value_start: self.value_start,
            value_end: self.value_end,
        }
    }
}

impl PartialEq for Declaration {
    fn eq(&self, o: &Self) -> bool {
        self.name == o.name
            && self.value == o.value
            && self.important == o.important
            && self.start == o.start
            && self.end == o.end
            && self.value_start == o.value_start
            && self.value_end == o.value_end
    }
}

impl Eq for Declaration {}

impl std::fmt::Debug for Declaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Declaration")
            .field("name", &self.name)
            .field("value", &self.value)
            .field("important", &self.important)
            .field("start", &self.start)
            .field("end", &self.end)
            .field("value_start", &self.value_start)
            .field("value_end", &self.value_end)
            .finish()
    }
}

impl Clone for Item {
    fn clone(&self) -> Self {
        match self {
            Item::Rule { at, start, end, prelude, block, declarations, children } => Item::Rule {
                at: *at,
                start: *start,
                end: *end,
                prelude: prelude.clone(),
                block: *block,
                declarations: declarations.clone(),
                children: children.clone(),
            },
            Item::Declarations(v) => Item::Declarations(v.clone()),
        }
    }
}

impl PartialEq for Item {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Item::Rule { at: a1, start: s1, end: e1, prelude: p1, block: b1, declarations: d1, children: c1 },
                Item::Rule { at: a2, start: s2, end: e2, prelude: p2, block: b2, declarations: d2, children: c2 },
            ) => a1 == a2 && s1 == s2 && e1 == e2 && p1 == p2 && b1 == b2 && d1 == d2 && c1 == c2,
            (Item::Declarations(a), Item::Declarations(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Item {}

impl std::fmt::Debug for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Item::Rule { at, start, end, prelude, block, declarations, children } => f
                .debug_struct("Rule")
                .field("at", at)
                .field("start", start)
                .field("end", end)
                .field("prelude", prelude)
                .field("block", block)
                .field("declarations", declarations)
                .field("children", children)
                .finish(),
            Item::Declarations(v) => f.debug_tuple("Declarations").field(v).finish(),
        }
    }
}
