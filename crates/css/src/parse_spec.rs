//! The specification of parsing: CSS Syntax Module Level 3 (Candidate
//! Recommendation Draft, 1 October 2026), §5.4 (parser entry points) and
//! §5.5 (parser algorithms), as spec functions over the tokens that
//! `spec::tokens` produces.
//!
//! This file is trusted, like `spec.rs`. The standard's algorithms read a
//! token stream; here every function takes the tokens as `ts` and the
//! position of the next token as `i`, and returns the position after what it
//! consumed. Each "process input" loop of the standard is a function that
//! recurses on the position and carries what the loop has built so far
//! (`acc`, `pre`, `rules`, `decls`).
//!
//! Three things are added to the standard, each marked where it occurs:
//!
//! - A nesting budget `d`. Every simple block, function and `{}` block of a
//!   rule spends one level. Input that would nest deeper than `MAX_DEPTH`
//!   makes the whole parse return `None`. The standard has no limit; the
//!   code recurses once per level, and the limit is what bounds its stack.
//! - Guards of the form `if j <= i || j > ts.len()` before recursing at `j`,
//!   as in `spec.rs`: they make termination evident to Verus, and the proofs
//!   of `parse.rs` show they never fire.
//! - Pending declarations are flushed when a block's contents end (§5.5.5,
//!   EOF and `}`). The published text only says "Return rules." there,
//!   which would drop the declarations of `a { color: red }`; every
//!   implementation keeps them.
//!
//! "Valid in the current context" (§5.5.2, §5.5.3, §5.5.6) depends on the
//! grammar of what is being parsed, which is not part of this crate: every
//! rule and declaration counts as valid here. The `unicode-range` step of
//! §5.5.6 (re-tokenizing the value with unicode ranges allowed) is not done.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The deepest nesting a parse accepts.
pub const MAX_DEPTH: usize = 128;

/// A component value (§5.1).
pub enum SCV {
    /// A preserved token: the token at index `i`.
    Tok { i: int },
    /// A simple block. `ts[start]` is its `{`, `[` or `(`; `end` is the
    /// index after its closing token (or the end of the tokens).
    Block { start: int, end: int, value: Seq<SCV> },
    /// A function. `ts[start]` is its function token.
    Func { start: int, end: int, value: Seq<SCV> },
}

/// A declaration (§5.1). `ts[name]` is its name's ident token; `start..end`
/// are the tokens it was consumed from; `value_start..value_end` are the
/// tokens of its value after `!important` and trailing whitespace are
/// removed (for a custom property, the standard's "original text").
pub struct SDecl {
    pub name: int,
    pub value: Seq<SCV>,
    pub important: bool,
    pub start: int,
    pub end: int,
    pub value_start: int,
    pub value_end: int,
}

/// A rule, or a list of declarations among a block's contents (§5.1).
pub enum SItem {
    /// An at-rule (`at`, named by the at-keyword token `ts[start]`) or a
    /// qualified rule. `block` says whether it has a `{}` block. A
    /// qualified rule's leading declarations are `decls`; a `Decls` item
    /// among its `children` is a nested declarations rule. An at-rule's
    /// `children` are its block's contents as they are, and its `decls` are
    /// empty.
    Rule {
        at: bool,
        start: int,
        end: int,
        prelude: Seq<SCV>,
        block: bool,
        decls: Seq<SDecl>,
        children: Seq<SItem>,
    },
    /// A list of declarations.
    Decls { decls: Seq<SDecl> },
}

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------

pub open spec fn tk(ts: Seq<SToken>, i: int, k: Kind) -> bool {
    0 <= i < ts.len() && ts[i].kind == k
}

pub open spec fn at_eof(ts: Seq<SToken>, i: int) -> bool {
    !(0 <= i < ts.len())
}

pub open spec fn is_open(k: Kind) -> bool {
    k == Kind::LeftBrace || k == Kind::LeftBracket || k == Kind::LeftParen
}

/// The ending token of a simple block (§5.5.9) or function (§5.5.10).
pub open spec fn closer(k: Kind) -> Kind {
    if k == Kind::LeftBrace {
        Kind::RightBrace
    } else if k == Kind::LeftBracket {
        Kind::RightBracket
    } else {
        Kind::RightParen
    }
}

/// "Discard whitespace" (§5.3): the position after the whitespace at `i`.
pub open spec fn skip_ws(ts: Seq<SToken>, i: int) -> int
    decreases ts.len() - i,
{
    if tk(ts, i, Kind::Whitespace) {
        skip_ws(ts, i + 1)
    } else {
        i
    }
}

pub open spec fn cv_end(c: SCV) -> int {
    match c {
        SCV::Tok { i } => i + 1,
        SCV::Block { end, .. } => end,
        SCV::Func { end, .. } => end,
    }
}

pub open spec fn is_ws_cv(ts: Seq<SToken>, c: SCV) -> bool {
    match c {
        SCV::Tok { i } => tk(ts, i, Kind::Whitespace),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// §5.5.8 - §5.5.10 Component values, simple blocks and functions
// ---------------------------------------------------------------------------

/// §5.5.8 Consume a component value, at a token that is not EOF.
pub open spec fn cv(ts: Seq<SToken>, i: int, d: nat) -> Option<(SCV, int)>
    decreases d, ts.len() - i, 0int,
{
    if !(0 <= i < ts.len()) {
        None
    } else if is_open(ts[i].kind) || ts[i].kind == Kind::Function {
        // Nesting budget (not in the standard).
        if d == 0 {
            None
        } else {
            let close = if ts[i].kind == Kind::Function { Kind::RightParen } else { closer(ts[i].kind) };
            match block_body(ts, i + 1, close, seq![], (d - 1) as nat) {
                None => None,
                Some((v, j)) => if ts[i].kind == Kind::Function {
                    Some((SCV::Func { start: i, end: j, value: v }, j))
                } else {
                    Some((SCV::Block { start: i, end: j, value: v }, j))
                },
            }
        }
    } else {
        Some((SCV::Tok { i }, i + 1))
    }
}

/// The loop of §5.5.9 Consume a simple block and §5.5.10 Consume a
/// function, after the opening token: component values until EOF or the
/// ending token `close`, which is discarded.
pub open spec fn block_body(ts: Seq<SToken>, i: int, close: Kind, acc: Seq<SCV>, d: nat) -> Option<(Seq<SCV>, int)>
    decreases d, ts.len() - i, 1int,
{
    if at_eof(ts, i) {
        Some((acc, i))
    } else if ts[i].kind == close {
        Some((acc, i + 1))
    } else {
        match cv(ts, i, d) {
            None => None,
            Some((c, j)) => if j <= i || j > ts.len() {
                None
            } else {
                block_body(ts, j, close, acc.push(c), d)
            },
        }
    }
}

/// §5.5.7 Consume a list of component values, with an optional stop token.
pub open spec fn cv_list(ts: Seq<SToken>, i: int, stop: Option<Kind>, nested: bool, acc: Seq<SCV>, d: nat) -> Option<(Seq<SCV>, int)>
    decreases d, ts.len() - i, 1int,
{
    if at_eof(ts, i) || stop == Some(ts[i].kind) {
        Some((acc, i))
    } else if ts[i].kind == Kind::RightBrace {
        if nested {
            Some((acc, i))
        } else {
            // A parse error; the token is kept.
            cv_list(ts, i + 1, stop, nested, acc.push(SCV::Tok { i }), d)
        }
    } else {
        match cv(ts, i, d) {
            None => None,
            Some((c, j)) => if j <= i || j > ts.len() {
                None
            } else {
                cv_list(ts, j, stop, nested, acc.push(c), d)
            },
        }
    }
}

// ---------------------------------------------------------------------------
// §5.5.6 Consume a declaration
// ---------------------------------------------------------------------------

/// Consume the remnants of a bad declaration (part of §5.5.6): the position
/// after them.
pub open spec fn bad_decl_end(ts: Seq<SToken>, i: int, nested: bool, d: nat) -> Option<int>
    decreases d, ts.len() - i, 1int,
{
    if at_eof(ts, i) {
        Some(i)
    } else if ts[i].kind == Kind::Semicolon {
        Some(i + 1)
    } else if ts[i].kind == Kind::RightBrace {
        if nested {
            Some(i)
        } else {
            bad_decl_end(ts, i + 1, nested, d)
        }
    } else {
        match cv(ts, i, d) {
            None => None,
            Some((c, j)) => if j <= i || j > ts.len() {
                None
            } else {
                bad_decl_end(ts, j, nested, d)
            },
        }
    }
}

/// The index of the last non-whitespace value in `v[..k]`, or -1.
pub open spec fn last_non_ws(ts: Seq<SToken>, v: Seq<SCV>, k: int) -> int
    decreases k,
{
    if k <= 0 || k > v.len() {
        -1
    } else if !is_ws_cv(ts, v[k - 1]) {
        k - 1
    } else {
        last_non_ws(ts, v, k - 1)
    }
}

pub open spec fn is_delim_tok(ts: Seq<SToken>, c: SCV, ch: u32) -> bool {
    match c {
        SCV::Tok { i } => tk(ts, i, Kind::Delim(ch)),
        _ => false,
    }
}

/// An ASCII case-insensitive match for "important".
pub open spec fn is_important_name(v: Seq<u32>) -> bool {
    v.len() == 9 && lower(v[0]) == 0x69 && lower(v[1]) == 0x6D && lower(v[2]) == 0x70 && lower(v[3]) == 0x6F
        && lower(v[4]) == 0x72 && lower(v[5]) == 0x74 && lower(v[6]) == 0x61 && lower(v[7]) == 0x6E
        && lower(v[8]) == 0x74
}

pub open spec fn is_important_tok(ts: Seq<SToken>, c: SCV) -> bool {
    match c {
        SCV::Tok { i } => tk(ts, i, Kind::Ident) && is_important_name(ts[i].value),
        _ => false,
    }
}

/// Step 6: if the last two non-whitespace values are `!` and `important`,
/// the value without them and true.
pub open spec fn strip_important(ts: Seq<SToken>, v: Seq<SCV>) -> (Seq<SCV>, bool) {
    let a = last_non_ws(ts, v, v.len() as int);
    let b = last_non_ws(ts, v, a);
    if a >= 0 && b >= 0 && is_delim_tok(ts, v[b], 0x21) && is_important_tok(ts, v[a]) {
        (v.remove(a).remove(b), true)
    } else {
        (v, false)
    }
}

/// Step 7: the value without trailing whitespace.
pub open spec fn strip_ws(ts: Seq<SToken>, v: Seq<SCV>) -> Seq<SCV>
    decreases v.len(),
{
    if v.len() > 0 && is_ws_cv(ts, v.last()) {
        strip_ws(ts, v.drop_last())
    } else {
        v
    }
}

pub open spec fn is_brace_block(ts: Seq<SToken>, c: SCV) -> bool {
    match c {
        SCV::Block { start, .. } => tk(ts, start, Kind::LeftBrace),
        _ => false,
    }
}

/// How many of `v[..k]` are `{}` blocks.
pub open spec fn brace_count(ts: Seq<SToken>, v: Seq<SCV>, k: int) -> int
    decreases k,
{
    if k <= 0 || k > v.len() {
        0
    } else {
        brace_count(ts, v, k - 1) + if is_brace_block(ts, v[k - 1]) { 1int } else { 0 }
    }
}

/// How many of `v[..k]` are not whitespace.
pub open spec fn non_ws_count(ts: Seq<SToken>, v: Seq<SCV>, k: int) -> int
    decreases k,
{
    if k <= 0 || k > v.len() {
        0
    } else {
        non_ws_count(ts, v, k - 1) + if is_ws_cv(ts, v[k - 1]) { 0int } else { 1 }
    }
}

/// A custom property name string (CSS Typed OM §3): starts with two
/// dashes.
pub open spec fn is_custom(name: Seq<u32>) -> bool {
    name.len() >= 2 && name[0] == 0x2D && name[1] == 0x2D
}

/// §5.5.6 Consume a declaration. `Some((None, _))` is "return nothing".
pub open spec fn decl(ts: Seq<SToken>, i: int, nested: bool, d: nat) -> Option<(Option<SDecl>, int)>
    decreases d, ts.len() - i, 2int,
{
    // 1. The name.
    if !tk(ts, i, Kind::Ident) {
        match bad_decl_end(ts, i, nested, d) {
            None => None,
            Some(e) => Some((None, e)),
        }
    } else {
        // 2. 3. Whitespace and the colon.
        let j = skip_ws(ts, i + 1);
        if j <= i || j > ts.len() {
            None
        } else if !tk(ts, j, Kind::Colon) {
            match bad_decl_end(ts, j, nested, d) {
                None => None,
                Some(e) => Some((None, e)),
            }
        } else {
            // 4. 5. Whitespace, and the value up to a semicolon.
            let k = skip_ws(ts, j + 1);
            if k <= i || k > ts.len() {
                None
            } else {
                match cv_list(ts, k, Some(Kind::Semicolon), nested, seq![], d) {
                    None => None,
                    Some((v, e)) => {
                        // 6. 7. `!important` and trailing whitespace.
                        let (v2, important) = strip_important(ts, v);
                        let v3 = strip_ws(ts, v2);
                        // 8. A {} block is the whole value or not allowed,
                        // unless the property is custom.
                        if !is_custom(ts[i].value) && brace_count(ts, v3, v3.len() as int) > 0
                            && non_ws_count(ts, v3, v3.len() as int) >= 2 {
                            Some((None, e))
                        } else {
                            let value_end = if v3.len() == 0 { k } else { cv_end(v3.last()) };
                            Some((Some(SDecl { name: i, value: v3, important, start: i, end: e, value_start: k, value_end }), e))
                        }
                    },
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §5.5.4 Consume a block and §5.5.5 Consume a block's contents
// ---------------------------------------------------------------------------

/// §5.5.4 Consume a block, at a `{`: its contents and the position after
/// its `}` (or the end).
pub open spec fn block(ts: Seq<SToken>, i: int, d: nat) -> Option<(Seq<SItem>, int)>
    decreases d, ts.len() - i, 1int,
{
    // Nesting budget (not in the standard).
    if d == 0 || at_eof(ts, i) {
        None
    } else {
        match contents(ts, i + 1, seq![], seq![], (d - 1) as nat) {
            None => None,
            Some((items, j)) => Some((items, if tk(ts, j, Kind::RightBrace) { j + 1 } else { j })),
        }
    }
}

/// Appends the pending declarations to `rules`, if there are any.
pub open spec fn flush(rules: Seq<SItem>, decls: Seq<SDecl>) -> Seq<SItem> {
    if decls.len() > 0 {
        rules.push(SItem::Decls { decls })
    } else {
        rules
    }
}

/// §5.5.5 Consume a block's contents: the rules and lists of declarations,
/// and the position of the EOF or `}` that ended them.
pub open spec fn contents(ts: Seq<SToken>, i: int, rules: Seq<SItem>, decls: Seq<SDecl>, d: nat) -> Option<(Seq<SItem>, int)>
    decreases d, ts.len() - i, 3int,
{
    if at_eof(ts, i) || ts[i].kind == Kind::RightBrace {
        // The flush is not in the published text (see the top of the file).
        Some((flush(rules, decls), i))
    } else if ts[i].kind == Kind::Whitespace || ts[i].kind == Kind::Semicolon {
        contents(ts, i + 1, rules, decls, d)
    } else if ts[i].kind == Kind::AtKeyword {
        match at_rule(ts, i + 1, i, seq![], true, d) {
            None => None,
            Some((r, e)) => if e <= i || e > ts.len() {
                None
            } else {
                contents(ts, e, flush(rules, decls).push(r), seq![], d)
            },
        }
    } else {
        // Mark; try a declaration; else restore and consume a qualified rule.
        match decl(ts, i, true, d) {
            None => None,
            Some((Some(dl), e)) => if e <= i || e > ts.len() {
                None
            } else {
                contents(ts, e, rules, decls.push(dl), d)
            },
            Some((None, _)) => match q_rule(ts, i, i, seq![], Some(Kind::Semicolon), true, d) {
                None => None,
                Some((r, e)) => if e <= i || e > ts.len() {
                    None
                } else {
                    match r {
                        None => contents(ts, e, rules, decls, d),
                        Some(r) => contents(ts, e, flush(rules, decls).push(r), seq![], d),
                    }
                },
            },
        }
    }
}

// ---------------------------------------------------------------------------
// §5.5.2 Consume an at-rule and §5.5.3 Consume a qualified rule
// ---------------------------------------------------------------------------

pub open spec fn at_item(start: int, end: int, pre: Seq<SCV>, block: bool, children: Seq<SItem>) -> SItem {
    SItem::Rule { at: true, start, end, prelude: pre, block, decls: seq![], children }
}

/// §5.5.2 Consume an at-rule: the loop after the at-keyword `ts[start]`,
/// with the prelude so far.
pub open spec fn at_rule(ts: Seq<SToken>, i: int, start: int, pre: Seq<SCV>, nested: bool, d: nat) -> Option<(SItem, int)>
    decreases d, ts.len() - i, 2int,
{
    if at_eof(ts, i) {
        Some((at_item(start, i, pre, false, seq![]), i))
    } else if ts[i].kind == Kind::Semicolon {
        Some((at_item(start, i + 1, pre, false, seq![]), i + 1))
    } else if ts[i].kind == Kind::RightBrace {
        if nested {
            Some((at_item(start, i, pre, false, seq![]), i))
        } else {
            at_rule(ts, i + 1, start, pre.push(SCV::Tok { i }), nested, d)
        }
    } else if ts[i].kind == Kind::LeftBrace {
        match block(ts, i, d) {
            None => None,
            Some((items, e)) => Some((at_item(start, e, pre, true, items), e)),
        }
    } else {
        match cv(ts, i, d) {
            None => None,
            Some((c, j)) => if j <= i || j > ts.len() {
                None
            } else {
                at_rule(ts, j, start, pre.push(c), nested, d)
            },
        }
    }
}

/// The index of the first non-whitespace value in `v[k..]`, or `v.len()`.
pub open spec fn first_non_ws(ts: Seq<SToken>, v: Seq<SCV>, k: int) -> int
    decreases v.len() - k,
{
    if k < 0 || k >= v.len() {
        v.len() as int
    } else if !is_ws_cv(ts, v[k]) {
        k
    } else {
        first_non_ws(ts, v, k + 1)
    }
}

/// The prelude starts like a custom property: an ident starting with `--`,
/// then a colon (whitespace aside).
pub open spec fn custom_prelude(ts: Seq<SToken>, pre: Seq<SCV>) -> bool {
    let a = first_non_ws(ts, pre, 0);
    let b = first_non_ws(ts, pre, a + 1);
    0 <= a < pre.len() && 0 <= b < pre.len() && match (pre[a], pre[b]) {
        (SCV::Tok { i: x }, SCV::Tok { i: y }) => tk(ts, x, Kind::Ident) && is_custom(ts[x].value) && tk(ts, y, Kind::Colon),
        _ => false,
    }
}

/// Splits a qualified rule's block contents: a leading list of
/// declarations becomes its declarations.
pub open spec fn split_decls(items: Seq<SItem>) -> (Seq<SDecl>, Seq<SItem>) {
    if items.len() > 0 && items[0] is Decls {
        (items[0]->Decls_decls, items.drop_first())
    } else {
        (seq![], items)
    }
}

/// §5.5.3 Consume a qualified rule: the loop from `i`, for a rule starting
/// at `start`, with the prelude so far. `Some((None, _))` is "return
/// nothing".
pub open spec fn q_rule(
    ts: Seq<SToken>,
    i: int,
    start: int,
    pre: Seq<SCV>,
    stop: Option<Kind>,
    nested: bool,
    d: nat,
) -> Option<(Option<SItem>, int)>
    decreases d, ts.len() - i, 2int,
{
    if at_eof(ts, i) || stop == Some(ts[i].kind) {
        // A parse error.
        Some((None, i))
    } else if ts[i].kind == Kind::RightBrace {
        // A parse error.
        if nested {
            Some((None, i))
        } else {
            q_rule(ts, i + 1, start, pre.push(SCV::Tok { i }), stop, nested, d)
        }
    } else if ts[i].kind == Kind::LeftBrace {
        if custom_prelude(ts, pre) {
            if nested {
                match bad_decl_end(ts, i, true, d) {
                    None => None,
                    Some(e) => Some((None, e)),
                }
            } else {
                match block(ts, i, d) {
                    None => None,
                    Some((_, e)) => Some((None, e)),
                }
            }
        } else {
            match block(ts, i, d) {
                None => None,
                Some((items, e)) => {
                    let (decls, children) = split_decls(items);
                    Some((Some(SItem::Rule { at: false, start, end: e, prelude: pre, block: true, decls, children }), e))
                },
            }
        }
    } else {
        match cv(ts, i, d) {
            None => None,
            Some((c, j)) => if j <= i || j > ts.len() {
                None
            } else {
                q_rule(ts, j, start, pre.push(c), stop, nested, d)
            },
        }
    }
}

// ---------------------------------------------------------------------------
// §5.5.1 Consume a stylesheet's contents
// ---------------------------------------------------------------------------

pub open spec fn sheet(ts: Seq<SToken>, i: int, rules: Seq<SItem>, d: nat) -> Option<Seq<SItem>>
    decreases d, ts.len() - i, 3int,
{
    if at_eof(ts, i) {
        Some(rules)
    } else if ts[i].kind == Kind::Whitespace || ts[i].kind == Kind::Cdo || ts[i].kind == Kind::Cdc {
        sheet(ts, i + 1, rules, d)
    } else if ts[i].kind == Kind::AtKeyword {
        match at_rule(ts, i + 1, i, seq![], false, d) {
            None => None,
            Some((r, e)) => if e <= i || e > ts.len() {
                None
            } else {
                sheet(ts, e, rules.push(r), d)
            },
        }
    } else {
        match q_rule(ts, i, i, seq![], None, false, d) {
            None => None,
            Some((r, e)) => if e <= i || e > ts.len() {
                None
            } else {
                match r {
                    None => sheet(ts, e, rules, d),
                    Some(r) => sheet(ts, e, rules.push(r), d),
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// §5.4 Entry points
// ---------------------------------------------------------------------------

/// §5.4.4 Parse a stylesheet's contents: the rules, or `None` if it nests
/// deeper than `MAX_DEPTH`.
pub open spec fn parse_stylesheet(ts: Seq<SToken>) -> Option<Seq<SItem>> {
    sheet(ts, 0, seq![], MAX_DEPTH as nat)
}

/// §5.4.5 Parse a block's contents (a `style` attribute, for one).
pub open spec fn parse_block_contents(ts: Seq<SToken>) -> Option<Seq<SItem>> {
    match contents(ts, 0, seq![], seq![], MAX_DEPTH as nat) {
        None => None,
        Some((items, _)) => Some(items),
    }
}

/// §5.4.9 Parse a list of component values.
pub open spec fn parse_component_values(ts: Seq<SToken>) -> Option<Seq<SCV>> {
    match cv_list(ts, 0, None, false, seq![], MAX_DEPTH as nat) {
        None => None,
        Some((v, _)) => Some(v),
    }
}

} // verus!
