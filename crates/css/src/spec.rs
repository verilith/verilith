//! The specification: CSS Syntax Module Level 3 (Candidate Recommendation
//! Draft, 1 October 2026), §3.3 (preprocessing the input stream) and §4
//! (tokenization), as spec functions over the input's code points. "Consume
//! a token" is transcribed with its "unicode ranges allowed" flag false,
//! which is how stylesheets are tokenized; see the README.
//!
//! This file is trusted: the proofs show the code computes exactly what is
//! written here, so a misreading of the standard here would be proven too.
//! Each function names the section it transcribes. The standard's
//! algorithms consume code points from a stream; here every function takes
//! the stream as `s` and the position of the next input code point as `i`,
//! and returns the position after what it consumed. Past the end, `at`
//! returns -1, which plays the standard's EOF code point: no predicate
//! below holds of it.
//!
//! A few recursive functions carry a guard such as `if j <= i || j > s.len() { ... }`
//! before recursing at `j`. The guard is there so that termination is
//! evident to Verus. It never fires: the proofs of the code in `lex.rs`
//! show every consumer advances and stays within the input, so the guard
//! does not change what the function computes.
use vstd::prelude::*;

verus! {

/// What kind of token, with the flags the standard attaches to some kinds.
/// A token's value (an ident, function, at-keyword, hash, string or url
/// token's code points, a dimension's unit) is in `Token::value`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// `<ident-token>`.
    Ident,
    /// `<function-token>`: the name, followed by `(`.
    Function,
    /// `<at-keyword-token>`: `@` and a name.
    AtKeyword,
    /// `<hash-token>`. `id` is the standard's type flag "id" (the name
    /// would also start an ident sequence), else "unrestricted".
    Hash { id: bool },
    /// `<string-token>`.
    String,
    /// `<bad-string-token>`: a string cut by a newline.
    BadString,
    /// `<url-token>`, from an unquoted `url(...)`.
    Url,
    /// `<bad-url-token>`.
    BadUrl,
    /// `<delim-token>` with its code point.
    Delim(u32),
    /// `<number-token>`. `integer` is the type flag "integer", else
    /// "number". The number's text is `start..repr_end`.
    Number { integer: bool },
    /// `<percentage-token>`; the number's text is `start..repr_end`.
    Percentage { integer: bool },
    /// `<dimension-token>`; the number's text is `start..repr_end` and the
    /// unit is the value.
    Dimension { integer: bool },
    /// `<whitespace-token>`.
    Whitespace,
    /// `<CDO-token>`: `<!--`.
    Cdo,
    /// `<CDC-token>`: `-->`.
    Cdc,
    /// `<colon-token>`.
    Colon,
    /// `<semicolon-token>`.
    Semicolon,
    /// `<comma-token>`.
    Comma,
    /// `<[-token>`.
    LeftBracket,
    /// `<]-token>`.
    RightBracket,
    /// `<(-token>`.
    LeftParen,
    /// `<)-token>`.
    RightParen,
    /// `<{-token>`.
    LeftBrace,
    /// `<}-token>`.
    RightBrace,
}

/// A token as the specification produces it. `start..end` are the
/// positions, in the preprocessed code points, of the text the token was
/// consumed from (comments before it are not included). `repr_end` is
/// where a numeric token's number ends; for other kinds it equals `end`.
pub struct SToken {
    pub kind: Kind,
    pub start: int,
    pub end: int,
    pub value: Seq<u32>,
    pub repr_end: int,
}

// ---------------------------------------------------------------------------
// §3.3 Preprocessing the input stream
// ---------------------------------------------------------------------------

/// A code point as preprocessing maps it on its own: U+000D CARRIAGE RETURN
/// and U+000C FORM FEED become U+000A LINE FEED, and U+0000 NULL and
/// surrogates become U+FFFD REPLACEMENT CHARACTER.
pub open spec fn pre_cp(c: u32) -> u32 {
    if c == 0 || (0xD800 <= c && c <= 0xDFFF) {
        0xFFFD
    } else if c == 0x0C || c == 0x0D {
        0x0A
    } else {
        c
    }
}

/// The preprocessed stream from position `i`: as `pre_cp`, except that a
/// CR LF pair becomes one LF.
pub open spec fn preprocess_from(s: Seq<u32>, i: int) -> Seq<u32>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        seq![]
    } else if s[i] == 0x0D && i + 1 < s.len() && s[i + 1] == 0x0A {
        seq![0x0Au32] + preprocess_from(s, i + 2)
    } else {
        seq![pre_cp(s[i])] + preprocess_from(s, i + 1)
    }
}

pub open spec fn preprocess(s: Seq<u32>) -> Seq<u32> {
    preprocess_from(s, 0)
}

// ---------------------------------------------------------------------------
// §4.2 Definitions
// ---------------------------------------------------------------------------

/// The code point at `i`, or -1 (EOF) past either end.
pub open spec fn at(s: Seq<u32>, i: int) -> int {
    if 0 <= i < s.len() {
        s[i] as int
    } else {
        -1
    }
}

pub open spec fn is_digit(c: int) -> bool {
    0x30 <= c <= 0x39
}

pub open spec fn is_hex(c: int) -> bool {
    is_digit(c) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

pub open spec fn hex_val(c: int) -> int {
    if is_digit(c) {
        c - 0x30
    } else if 0x41 <= c <= 0x46 {
        c - 0x41 + 10
    } else {
        c - 0x61 + 10
    }
}

pub open spec fn is_letter(c: int) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// "non-ASCII ident code point", as the 2021 Candidate Recommendation
/// defined it and as browsers implement it: every code point from U+0080.
/// The current draft narrows it to the ranges of XML names; see the
/// README's "Where it departs from the standard".
pub open spec fn is_non_ascii(c: int) -> bool {
    c >= 0x80
}

pub open spec fn is_ident_start(c: int) -> bool {
    is_letter(c) || is_non_ascii(c) || c == 0x5F
}

pub open spec fn is_ident_cp(c: int) -> bool {
    is_ident_start(c) || is_digit(c) || c == 0x2D
}

pub open spec fn is_non_printable(c: int) -> bool {
    (0 <= c <= 0x08) || c == 0x0B || (0x0E <= c <= 0x1F) || c == 0x7F
}

/// "newline": after preprocessing, only U+000A LINE FEED.
pub open spec fn is_newline(c: int) -> bool {
    c == 0x0A
}

pub open spec fn is_ws(c: int) -> bool {
    is_newline(c) || c == 0x09 || c == 0x20
}

pub const MAX_CP: u32 = 0x10FFFF;

// ---------------------------------------------------------------------------
// §4.3.8 - §4.3.10 Checks
// ---------------------------------------------------------------------------

/// §4.3.8 Check if two code points are a valid escape.
pub open spec fn valid_escape(a: int, b: int) -> bool {
    a == 0x5C && !is_newline(b)
}

/// §4.3.9 Check if three code points would start an ident sequence.
pub open spec fn starts_ident(a: int, b: int, c: int) -> bool {
    if a == 0x2D {
        is_ident_start(b) || b == 0x2D || valid_escape(b, c)
    } else if is_ident_start(a) {
        true
    } else if a == 0x5C {
        valid_escape(a, b)
    } else {
        false
    }
}

/// §4.3.10 Check if three code points would start a number.
pub open spec fn starts_number(a: int, b: int, c: int) -> bool {
    if a == 0x2B || a == 0x2D {
        is_digit(b) || (b == 0x2E && is_digit(c))
    } else if a == 0x2E {
        is_digit(b)
    } else {
        is_digit(a)
    }
}

pub open spec fn escape_at(s: Seq<u32>, i: int) -> bool {
    valid_escape(at(s, i), at(s, i + 1))
}

pub open spec fn ident_at(s: Seq<u32>, i: int) -> bool {
    starts_ident(at(s, i), at(s, i + 1), at(s, i + 2))
}

pub open spec fn number_at(s: Seq<u32>, i: int) -> bool {
    starts_number(at(s, i), at(s, i + 1), at(s, i + 2))
}

// ---------------------------------------------------------------------------
// Runs
// ---------------------------------------------------------------------------

/// The end of the whitespace run starting at `i`.
pub open spec fn ws_end(s: Seq<u32>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_ws(at(s, i)) {
        ws_end(s, i + 1)
    } else {
        i
    }
}

/// The end of the digit run starting at `i`.
pub open spec fn digits_end(s: Seq<u32>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_digit(at(s, i)) {
        digits_end(s, i + 1)
    } else {
        i
    }
}

/// The end of the run of at most `k` hex digits starting at `i`.
pub open spec fn hex_end(s: Seq<u32>, i: int, k: int) -> int
    decreases k,
{
    if k > 0 && is_hex(at(s, i)) {
        hex_end(s, i + 1, k - 1)
    } else {
        i
    }
}

/// The hex digits `s[a..b]` read as a number.
pub open spec fn hex_value(s: Seq<u32>, a: int, b: int) -> int
    decreases b - a,
{
    if a < b {
        hex_value(s, a, b - 1) * 16 + hex_val(at(s, b - 1))
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// §4.3.2 Consume comments
// ---------------------------------------------------------------------------

/// The position after the `*/` that closes a comment whose body starts at
/// `i`, or the end of the input.
pub open spec fn comment_end(s: Seq<u32>, i: int) -> int
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        i
    } else if at(s, i) == 0x2A && at(s, i + 1) == 0x2F {
        i + 2
    } else {
        comment_end(s, i + 1)
    }
}

/// The position after every comment that starts at `i`, one after another.
pub open spec fn skip_comments(s: Seq<u32>, i: int) -> int
    decreases s.len() - i,
{
    if at(s, i) == 0x2F && at(s, i + 1) == 0x2A {
        let j = comment_end(s, i + 2);
        if j <= i || j > s.len() {
            i
        } else {
            skip_comments(s, j)
        }
    } else {
        i
    }
}

// ---------------------------------------------------------------------------
// §4.3.7 Consume an escaped code point
// ---------------------------------------------------------------------------

/// Called with `i` just after a U+005C REVERSE SOLIDUS that starts a valid
/// escape. Returns the code point and the position after the escape.
pub open spec fn escape(s: Seq<u32>, i: int) -> (u32, int) {
    let c = at(s, i);
    if is_hex(c) {
        let e = hex_end(s, i, 6);
        let v = hex_value(s, i, e);
        let j = if is_ws(at(s, e)) { e + 1 } else { e };
        let cp = if v == 0 || (0xD800 <= v <= 0xDFFF) || v > MAX_CP { 0xFFFDu32 } else { v as u32 };
        (cp, j)
    } else if c == -1 {
        // EOF: a parse error, and U+FFFD.
        (0xFFFDu32, i)
    } else {
        (c as u32, i + 1)
    }
}

// ---------------------------------------------------------------------------
// §4.3.12 Consume an ident sequence
// ---------------------------------------------------------------------------

/// The ident sequence starting at `i`, and the position after it.
pub open spec fn ident_seq(s: Seq<u32>, i: int) -> (Seq<u32>, int)
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        (seq![], i)
    } else if is_ident_cp(at(s, i)) {
        let r = ident_seq(s, i + 1);
        (seq![s[i]] + r.0, r.1)
    } else if escape_at(s, i) {
        let e = escape(s, i + 1);
        if e.1 <= i || e.1 > s.len() {
            (seq![], i)
        } else {
            let r = ident_seq(s, e.1);
            (seq![e.0] + r.0, r.1)
        }
    } else {
        (seq![], i)
    }
}

// ---------------------------------------------------------------------------
// §4.3.13 Consume a number
// ---------------------------------------------------------------------------

/// The end of the number starting at `i` and whether its type is
/// "integer". Its numeric value is left to the caller (see the README).
pub open spec fn number_end(s: Seq<u32>, i: int) -> (int, bool) {
    let j = if at(s, i) == 0x2B || at(s, i) == 0x2D { i + 1 } else { i };
    let k = digits_end(s, j);
    let (k2, int1) = if at(s, k) == 0x2E && is_digit(at(s, k + 1)) {
        (digits_end(s, k + 2), false)
    } else {
        (k, true)
    };
    let k3 = if at(s, k2) == 0x45 || at(s, k2) == 0x65 {
        if is_digit(at(s, k2 + 1)) {
            digits_end(s, k2 + 2)
        } else if (at(s, k2 + 1) == 0x2B || at(s, k2 + 1) == 0x2D) && is_digit(at(s, k2 + 2)) {
            digits_end(s, k2 + 3)
        } else {
            k2
        }
    } else {
        k2
    };
    (k3, int1 && k3 == k2)
}

// ---------------------------------------------------------------------------
// §4.3.5 Consume a string token
// ---------------------------------------------------------------------------

/// The string whose body starts at `i`, ended by the code point `q`:
/// its value, the position after it, and whether it is a bad string.
pub open spec fn string_body(s: Seq<u32>, i: int, q: int) -> (Seq<u32>, int, bool)
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        // EOF: a parse error; the string token is returned.
        (seq![], i, false)
    } else if at(s, i) == q {
        (seq![], i + 1, false)
    } else if is_newline(at(s, i)) {
        // A parse error: the newline is reconsumed, and the token is bad.
        (seq![], i, true)
    } else if at(s, i) == 0x5C {
        if i + 1 >= s.len() {
            // U+005C then EOF: nothing is appended.
            (seq![], i + 1, false)
        } else if is_newline(at(s, i + 1)) {
            string_body(s, i + 2, q)
        } else {
            let e = escape(s, i + 1);
            if e.1 <= i || e.1 > s.len() {
                (seq![], i, false)
            } else {
                let r = string_body(s, e.1, q);
                (seq![e.0] + r.0, r.1, r.2)
            }
        }
    } else {
        let r = string_body(s, i + 1, q);
        (seq![s[i]] + r.0, r.1, r.2)
    }
}

// ---------------------------------------------------------------------------
// §4.3.15 Consume the remnants of a bad url
// ---------------------------------------------------------------------------

pub open spec fn bad_url_end(s: Seq<u32>, i: int) -> int
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        i
    } else if at(s, i) == 0x29 {
        i + 1
    } else if escape_at(s, i) {
        let e = escape(s, i + 1);
        if e.1 <= i || e.1 > s.len() {
            i
        } else {
            bad_url_end(s, e.1)
        }
    } else {
        bad_url_end(s, i + 1)
    }
}

// ---------------------------------------------------------------------------
// §4.3.6 Consume a url token
// ---------------------------------------------------------------------------

/// The url whose body starts at `i` (after its leading whitespace): its
/// value, the position after it, and whether it is a bad url.
pub open spec fn url_body(s: Seq<u32>, i: int) -> (Seq<u32>, int, bool)
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        // EOF: a parse error; the url token is returned.
        (seq![], i, false)
    } else {
        let c = at(s, i);
        if c == 0x29 {
            (seq![], i + 1, false)
        } else if is_ws(c) {
            let j = ws_end(s, i);
            if at(s, j) == 0x29 {
                (seq![], j + 1, false)
            } else if at(s, j) == -1 {
                (seq![], j, false)
            } else {
                (seq![], bad_url_end(s, j), true)
            }
        } else if c == 0x22 || c == 0x27 || c == 0x28 || is_non_printable(c) {
            (seq![], bad_url_end(s, i + 1), true)
        } else if c == 0x5C {
            if escape_at(s, i) {
                let e = escape(s, i + 1);
                if e.1 <= i || e.1 > s.len() {
                    (seq![], i, false)
                } else {
                    let r = url_body(s, e.1);
                    (seq![e.0] + r.0, r.1, r.2)
                }
            } else {
                (seq![], bad_url_end(s, i + 1), true)
            }
        } else {
            let r = url_body(s, i + 1);
            (seq![s[i]] + r.0, r.1, r.2)
        }
    }
}

// ---------------------------------------------------------------------------
// §4.3.4 Consume an ident-like token
// ---------------------------------------------------------------------------

pub open spec fn lower(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u32
    } else {
        c
    }
}

/// The value is an ASCII case-insensitive match for "url".
pub open spec fn is_url(v: Seq<u32>) -> bool {
    v.len() == 3 && lower(v[0]) == 0x75 && lower(v[1]) == 0x72 && lower(v[2]) == 0x6C
}

/// "While the next two input code points are whitespace, consume the next
/// input code point."
pub open spec fn url_ws(s: Seq<u32>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_ws(at(s, i)) && is_ws(at(s, i + 1)) {
        url_ws(s, i + 1)
    } else {
        i
    }
}

pub open spec fn tok(kind: Kind, start: int, end: int, value: Seq<u32>) -> SToken {
    SToken { kind, start, end, value, repr_end: end }
}

pub open spec fn ident_like(s: Seq<u32>, i: int) -> SToken {
    let r = ident_seq(s, i);
    let j = r.1;
    if is_url(r.0) && at(s, j) == 0x28 {
        let k = url_ws(s, j + 1);
        let c0 = at(s, k);
        let c1 = at(s, k + 1);
        if c0 == 0x22 || c0 == 0x27 || (is_ws(c0) && (c1 == 0x22 || c1 == 0x27)) {
            tok(Kind::Function, i, k, r.0)
        } else {
            let u = url_body(s, ws_end(s, k));
            if u.2 {
                tok(Kind::BadUrl, i, u.1, seq![])
            } else {
                tok(Kind::Url, i, u.1, u.0)
            }
        }
    } else if at(s, j) == 0x28 {
        tok(Kind::Function, i, j + 1, r.0)
    } else {
        tok(Kind::Ident, i, j, r.0)
    }
}

// ---------------------------------------------------------------------------
// §4.3.3 Consume a numeric token
// ---------------------------------------------------------------------------

pub open spec fn numeric(s: Seq<u32>, i: int) -> SToken {
    let (e, integer) = number_end(s, i);
    if ident_at(s, e) {
        let u = ident_seq(s, e);
        SToken { kind: Kind::Dimension { integer }, start: i, end: u.1, value: u.0, repr_end: e }
    } else if at(s, e) == 0x25 {
        SToken { kind: Kind::Percentage { integer }, start: i, end: e + 1, value: seq![], repr_end: e }
    } else {
        SToken { kind: Kind::Number { integer }, start: i, end: e, value: seq![], repr_end: e }
    }
}

// ---------------------------------------------------------------------------
// §4.3.1 Consume a token
// ---------------------------------------------------------------------------

pub open spec fn delim(i: int, c: int) -> SToken {
    tok(Kind::Delim(c as u32), i, i + 1, seq![])
}

/// The token at `i`, called after comments are consumed and before EOF.
pub open spec fn next_token(s: Seq<u32>, i: int) -> SToken {
    let c = at(s, i);
    if is_ws(c) {
        tok(Kind::Whitespace, i, ws_end(s, i), seq![])
    } else if c == 0x22 || c == 0x27 {
        let r = string_body(s, i + 1, c);
        if r.2 {
            tok(Kind::BadString, i, r.1, seq![])
        } else {
            tok(Kind::String, i, r.1, r.0)
        }
    } else if c == 0x23 {
        if is_ident_cp(at(s, i + 1)) || escape_at(s, i + 1) {
            let r = ident_seq(s, i + 1);
            tok(Kind::Hash { id: ident_at(s, i + 1) }, i, r.1, r.0)
        } else {
            delim(i, c)
        }
    } else if c == 0x28 {
        tok(Kind::LeftParen, i, i + 1, seq![])
    } else if c == 0x29 {
        tok(Kind::RightParen, i, i + 1, seq![])
    } else if c == 0x2B {
        if number_at(s, i) {
            numeric(s, i)
        } else {
            delim(i, c)
        }
    } else if c == 0x2C {
        tok(Kind::Comma, i, i + 1, seq![])
    } else if c == 0x2D {
        if number_at(s, i) {
            numeric(s, i)
        } else if at(s, i + 1) == 0x2D && at(s, i + 2) == 0x3E {
            tok(Kind::Cdc, i, i + 3, seq![])
        } else if ident_at(s, i) {
            ident_like(s, i)
        } else {
            delim(i, c)
        }
    } else if c == 0x2E {
        if number_at(s, i) {
            numeric(s, i)
        } else {
            delim(i, c)
        }
    } else if c == 0x3A {
        tok(Kind::Colon, i, i + 1, seq![])
    } else if c == 0x3B {
        tok(Kind::Semicolon, i, i + 1, seq![])
    } else if c == 0x3C {
        if at(s, i + 1) == 0x21 && at(s, i + 2) == 0x2D && at(s, i + 3) == 0x2D {
            tok(Kind::Cdo, i, i + 4, seq![])
        } else {
            delim(i, c)
        }
    } else if c == 0x40 {
        if ident_at(s, i + 1) {
            let r = ident_seq(s, i + 1);
            tok(Kind::AtKeyword, i, r.1, r.0)
        } else {
            delim(i, c)
        }
    } else if c == 0x5B {
        tok(Kind::LeftBracket, i, i + 1, seq![])
    } else if c == 0x5C {
        if escape_at(s, i) {
            ident_like(s, i)
        } else {
            // A parse error.
            delim(i, c)
        }
    } else if c == 0x5D {
        tok(Kind::RightBracket, i, i + 1, seq![])
    } else if c == 0x7B {
        tok(Kind::LeftBrace, i, i + 1, seq![])
    } else if c == 0x7D {
        tok(Kind::RightBrace, i, i + 1, seq![])
    } else if is_digit(c) {
        numeric(s, i)
    } else if is_ident_start(c) {
        ident_like(s, i)
    } else {
        delim(i, c)
    }
}

/// §4 Tokenization: the tokens from position `i` to the end of the input,
/// without the final `<EOF-token>`.
pub open spec fn tokens_from(s: Seq<u32>, i: int) -> Seq<SToken>
    decreases s.len() - i,
{
    let j = skip_comments(s, i);
    if !(0 <= i <= j < s.len()) {
        seq![]
    } else {
        let t = next_token(s, j);
        if t.end <= i || t.end > s.len() {
            seq![]
        } else {
            seq![t] + tokens_from(s, t.end)
        }
    }
}

/// The tokens of a stylesheet's preprocessed code points.
pub open spec fn tokens(s: Seq<u32>) -> Seq<SToken> {
    tokens_from(s, 0)
}

} // verus!
