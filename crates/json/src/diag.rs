//! Why and where a parse failed.
//!
//! The first half is specification: `doc_fail` says what error a text that
//! is not JSON gets, and at which byte. It reads the text left to right
//! with the grammar of `spec.rs`, rule for rule, and the error is the first
//! place where no rule applies: the byte that cannot come next, or the end
//! of the input where more was needed. `lemma_doc_fail` proves that it
//! reports an error exactly when `document` rejects the text, and that it
//! otherwise ends where `document` does.
//!
//! The second half computes it: `explain` is proven to return `doc_fail`'s
//! error, and `line_col` its line and column. The parser itself does not
//! track positions; `explain` reruns the grammar on failure only.
use crate::parser::{ex_escape_end, ex_has_lit, ex_is_digit, ex_number_end, ex_skip_ws};
use crate::spec::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// What was wrong with the input (`ErrorKind` in the public API).
pub enum Why {
    /// The input ended inside a value.
    UnexpectedEnd,
    /// A string was not closed before the end of the input.
    UnterminatedString,
    /// A byte that cannot appear here.
    UnexpectedByte(u8),
    /// A raw control character inside a string.
    ControlCharacter(u8),
    /// A backslash escape that `string_char` rejects.
    InvalidEscape,
    /// A number that does not follow the grammar.
    InvalidNumber,
    /// Something other than `true`, `false` or `null` where one began.
    InvalidLiteral,
    /// Arrays and objects nested deeper than `MAX_DEPTH`.
    TooDeep,
    /// Bytes other than whitespace after the value.
    TrailingData,
    /// Ill-formed UTF-8.
    InvalidUtf8,
    /// Over `MAX_INPUT` bytes.
    TooLarge,
}

/// An error: its byte offset and its reason.
pub type Fail = (int, Why);

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// The error at a `char` of a string body that `string_char` rejects (not
/// the closing quote): a control character, a backslash at the end of the
/// input, or a bad escape, reported at its backslash.
pub open spec fn char_fail(s: Seq<u8>, i: int) -> Fail {
    if s[i] < 0x20 {
        (i, Why::ControlCharacter(s[i]))
    } else if i + 1 >= s.len() {
        (s.len() as int, Why::UnterminatedString)
    } else {
        (i, Why::InvalidEscape)
    }
}

/// `string_body` from `i`, with its error.
pub open spec fn str_fail(s: Seq<u8>, i: int) -> Result<int, Fail>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        Err((s.len() as int, Why::UnterminatedString))
    } else if s[i] == 0x22 {
        Ok(i + 1)
    } else {
        match string_char(s, i) {
            None => Err(char_fail(s, i)),
            Some((_, n)) => {
                if !(i < n <= s.len()) {
                    Err((i, Why::InvalidEscape))
                } else {
                    str_fail(s, n)
                }
            },
        }
    }
}

/// The error where the literal `lit` should start at `i`: the end of the
/// input if what is there is a prefix of it, otherwise the literal.
pub open spec fn lit_fail(s: Seq<u8>, i: int, lit: Seq<u8>) -> Fail {
    if s.len() - i < lit.len() && s.subrange(i, s.len() as int) == lit.subrange(0, s.len() - i) {
        (s.len() as int, Why::UnexpectedEnd)
    } else {
        (i, Why::InvalidLiteral)
    }
}

/// The error at `s[k2]`, which is neither a separator nor a closing bracket
/// after the value `s[v..k]`: the number itself if it runs straight into a
/// byte that could continue a number (`01`, `1.`, `1e5e`), otherwise that
/// byte.
pub open spec fn next_fail(s: Seq<u8>, v: int, k: int, k2: int) -> Fail {
    if k2 == k && 0 < k && is_digit(s[k - 1]) && num_cont(s[k2]) {
        (v, Why::InvalidNumber)
    } else {
        (k2, Why::UnexpectedByte(s[k2]))
    }
}

/// `value`, with its error.
pub open spec fn value_fail(s: Seq<u8>, i: int, depth: nat) -> Result<int, Fail>
    decreases depth, s.len() - i, 2nat,
{
    if !(0 <= i < s.len()) {
        Err((s.len() as int, Why::UnexpectedEnd))
    } else {
        let c = s[i];
        if c == 0x5B || c == 0x7B {
            if depth == 0 {
                Err((i, Why::TooDeep))
            } else if c == 0x5B {
                array_fail(s, i + 1, depth)
            } else {
                object_fail(s, i + 1, depth)
            }
        } else if c == 0x22 {
            str_fail(s, i + 1)
        } else if c == 0x74 {
            if has_lit(s, i, seq![0x74u8, 0x72, 0x75, 0x65]) {
                Ok(i + 4)
            } else {
                Err(lit_fail(s, i, seq![0x74u8, 0x72, 0x75, 0x65]))
            }
        } else if c == 0x66 {
            if has_lit(s, i, seq![0x66u8, 0x61, 0x6C, 0x73, 0x65]) {
                Ok(i + 5)
            } else {
                Err(lit_fail(s, i, seq![0x66u8, 0x61, 0x6C, 0x73, 0x65]))
            }
        } else if c == 0x6E {
            if has_lit(s, i, seq![0x6Eu8, 0x75, 0x6C, 0x6C]) {
                Ok(i + 4)
            } else {
                Err(lit_fail(s, i, seq![0x6Eu8, 0x75, 0x6C, 0x6C]))
            }
        } else if c == 0x2D || is_digit(c) {
            match number_end(s, i) {
                Some(e) => Ok(e),
                None => Err((i, Why::InvalidNumber)),
            }
        } else {
            Err((i, Why::UnexpectedByte(c)))
        }
    }
}

/// `array`, with its error.
pub open spec fn array_fail(s: Seq<u8>, i: int, depth: nat) -> Result<int, Fail>
    decreases depth, s.len() - i, 1nat,
{
    let j = skip_ws(s, i);
    if 0 <= j < s.len() && s[j] == 0x5D {
        Ok(j + 1)
    } else {
        elements_fail(s, i, depth)
    }
}

/// `elements`, with its error.
pub open spec fn elements_fail(s: Seq<u8>, i: int, depth: nat) -> Result<int, Fail>
    decreases depth, s.len() - i, 0nat,
{
    if depth == 0 {
        Err((i, Why::TooDeep))
    } else {
        let v = skip_ws(s, i);
        match value_fail(s, v, (depth - 1) as nat) {
            Err(f) => Err(f),
            Ok(k) => {
                let k2 = skip_ws(s, k);
                if !(0 <= k2 < s.len()) {
                    Err((s.len() as int, Why::UnexpectedEnd))
                } else if s[k2] == 0x5D {
                    Ok(k2 + 1)
                } else if s[k2] == 0x2C {
                    if !(i < k2 + 1 <= s.len()) {
                        Err((k2, Why::UnexpectedByte(0x2C)))
                    } else {
                        elements_fail(s, k2 + 1, depth)
                    }
                } else {
                    Err(next_fail(s, v, k, k2))
                }
            },
        }
    }
}

/// `object`, with its error.
pub open spec fn object_fail(s: Seq<u8>, i: int, depth: nat) -> Result<int, Fail>
    decreases depth, s.len() - i, 1nat,
{
    let j = skip_ws(s, i);
    if 0 <= j < s.len() && s[j] == 0x7D {
        Ok(j + 1)
    } else {
        members_fail(s, i, depth)
    }
}

/// `members`, with its error.
pub open spec fn members_fail(s: Seq<u8>, i: int, depth: nat) -> Result<int, Fail>
    decreases depth, s.len() - i, 0nat,
{
    if depth == 0 {
        Err((i, Why::TooDeep))
    } else {
        let j = skip_ws(s, i);
        if !(0 <= j < s.len()) {
            Err((s.len() as int, Why::UnexpectedEnd))
        } else if s[j] != 0x22 {
            Err((j, Why::UnexpectedByte(s[j])))
        } else {
            match str_fail(s, j + 1) {
                Err(f) => Err(f),
                Ok(k) => {
                    let c = skip_ws(s, k);
                    if !(0 <= c < s.len()) {
                        Err((s.len() as int, Why::UnexpectedEnd))
                    } else if s[c] != 0x3A {
                        Err((c, Why::UnexpectedByte(s[c])))
                    } else {
                        let v = skip_ws(s, c + 1);
                        match value_fail(s, v, (depth - 1) as nat) {
                            Err(f) => Err(f),
                            Ok(m) => {
                                let m2 = skip_ws(s, m);
                                if !(0 <= m2 < s.len()) {
                                    Err((s.len() as int, Why::UnexpectedEnd))
                                } else if s[m2] == 0x7D {
                                    Ok(m2 + 1)
                                } else if s[m2] == 0x2C {
                                    if !(i < m2 + 1 <= s.len()) {
                                        Err((m2, Why::UnexpectedByte(0x2C)))
                                    } else {
                                        members_fail(s, m2 + 1, depth)
                                    }
                                } else {
                                    Err(next_fail(s, v, m, m2))
                                }
                            },
                        }
                    }
                },
            }
        }
    }
}

/// The start of the first ill-formed UTF-8 sequence in `s[i..]`, read one
/// sequence at a time, if there is one.
pub open spec fn bad_utf8(s: Seq<u8>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        None
    } else {
        match utf8_len(s, i) {
            Some(l) => bad_utf8(s, i + l),
            None => Some(i),
        }
    }
}

/// The error `f`, unless ill-formed UTF-8 comes first or at the same byte.
pub open spec fn or_utf8(s: Seq<u8>, f: Fail) -> Fail {
    match bad_utf8(s, bom_end(s)) {
        Some(u) => if u <= f.0 { (u, Why::InvalidUtf8) } else { f },
        None => f,
    }
}

/// **The error a text gets.** `Ok(k)` when it is JSON (`k` is the end of
/// the value), and otherwise the first error, reading left to right:
///
/// - over `MAX_INPUT` bytes: `TooLarge` at 0;
/// - the first grammar error (see `value_fail`);
/// - with `require_end`, the first byte after the value that is not
///   whitespace (`TrailingData`, or `InvalidNumber` at a number that runs
///   into it);
/// - without it, a number that runs into a byte that could continue it
///   (`cut_number`): `InvalidNumber` at the number;
/// - ill-formed UTF-8 in the text: `InvalidUtf8` at the first ill-formed
///   sequence. It wins over a grammar error that does not come before it.
pub open spec fn doc_fail(s: Seq<u8>, require_end: bool) -> Result<int, Fail> {
    if s.len() > MAX_INPUT {
        Err((0, Why::TooLarge))
    } else {
        let b = bom_end(s);
        let v = skip_ws(s, b);
        match value_fail(s, v, MAX_DEPTH as nat) {
            Err(f) => Err(or_utf8(s, f)),
            Ok(k) => {
                let e = skip_ws(s, k);
                if require_end && e != s.len() {
                    Err(
                        or_utf8(
                            s,
                            if e == k && 0 < k && is_digit(s[k - 1]) && num_cont(s[e]) {
                                (v, Why::InvalidNumber)
                            } else {
                                (e, Why::TrailingData)
                            },
                        ),
                    )
                } else if cut_number(s, require_end, k) {
                    Err(or_utf8(s, (v, Why::InvalidNumber)))
                } else {
                    match bad_utf8(s.subrange(0, if require_end { s.len() as int } else { k }), b) {
                        Some(u) => Err((u, Why::InvalidUtf8)),
                        None => Ok(k),
                    }
                }
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

pub proof fn lemma_str_fail(s: Seq<u8>, i: int, esc: bool)
    ensures
        str_fail(s, i) is Ok == string_body(s, i, esc) is Some,
        string_body(s, i, esc) matches Some((n, _)) ==> str_fail(s, i) == Ok::<int, Fail>(n),
    decreases s.len() - i,
{
    if 0 <= i < s.len() && s[i] != 0x22 {
        if let Some((_, n)) = string_char(s, i) {
            if i < n <= s.len() {
                lemma_str_fail(s, n, esc || s[i] == 0x5C);
            }
        }
    }
}

pub proof fn lemma_value_fail(s: Seq<u8>, i: int, depth: nat, t: Seq<STok>)
    ensures
        value_fail(s, i, depth) is Ok == value(s, i, depth, t) is Some,
        value(s, i, depth, t) matches Some((_, n)) ==> value_fail(s, i, depth) == Ok::<int, Fail>(n),
    decreases depth, s.len() - i, 2nat,
{
    if 0 <= i < s.len() {
        let c = s[i];
        if (c == 0x5B || c == 0x7B) && depth > 0 {
            if c == 0x5B {
                lemma_array_fail(s, i + 1, depth, t.push(STok::ArrStart { end: 0 }));
            } else {
                lemma_object_fail(s, i + 1, depth, t.push(STok::ObjStart { end: 0 }));
            }
        } else if c == 0x22 {
            lemma_str_fail(s, i + 1, false);
        }
    }
}

pub proof fn lemma_array_fail(s: Seq<u8>, i: int, depth: nat, t: Seq<STok>)
    ensures
        array_fail(s, i, depth) is Ok == array(s, i, depth, t) is Some,
        array(s, i, depth, t) matches Some((_, n)) ==> array_fail(s, i, depth) == Ok::<int, Fail>(n),
    decreases depth, s.len() - i, 1nat,
{
    lemma_elements_fail(s, i, depth, t);
}

pub proof fn lemma_elements_fail(s: Seq<u8>, i: int, depth: nat, t: Seq<STok>)
    ensures
        elements_fail(s, i, depth) is Ok == elements(s, i, depth, t) is Some,
        elements(s, i, depth, t) matches Some((_, n)) ==> elements_fail(s, i, depth) == Ok::<int, Fail>(n),
    decreases depth, s.len() - i, 0nat,
{
    if depth > 0 {
        let v = skip_ws(s, i);
        lemma_value_fail(s, v, (depth - 1) as nat, t);
        if let Some((t2, k)) = value(s, v, (depth - 1) as nat, t) {
            let k2 = skip_ws(s, k);
            if 0 <= k2 < s.len() && s[k2] == 0x2C && i < k2 + 1 <= s.len() {
                lemma_elements_fail(s, k2 + 1, depth, t2);
            }
        }
    }
}

pub proof fn lemma_object_fail(s: Seq<u8>, i: int, depth: nat, t: Seq<STok>)
    ensures
        object_fail(s, i, depth) is Ok == object(s, i, depth, t) is Some,
        object(s, i, depth, t) matches Some((_, n)) ==> object_fail(s, i, depth) == Ok::<int, Fail>(n),
    decreases depth, s.len() - i, 1nat,
{
    lemma_members_fail(s, i, depth, t);
}

pub proof fn lemma_members_fail(s: Seq<u8>, i: int, depth: nat, t: Seq<STok>)
    ensures
        members_fail(s, i, depth) is Ok == members(s, i, depth, t) is Some,
        members(s, i, depth, t) matches Some((_, n)) ==> members_fail(s, i, depth) == Ok::<int, Fail>(n),
    decreases depth, s.len() - i, 0nat,
{
    if depth > 0 {
        let j = skip_ws(s, i);
        if 0 <= j < s.len() && s[j] == 0x22 {
            lemma_str_fail(s, j + 1, false);
            if let Some((k, esc)) = string(s, j) {
                let c = skip_ws(s, k);
                if 0 <= c < s.len() && s[c] == 0x3A {
                    let v = skip_ws(s, c + 1);
                    let t1 = t.push(STok::Key { start: j + 1, end: k - 1, escaped: esc });
                    lemma_value_fail(s, v, (depth - 1) as nat, t1);
                    if let Some((t2, m)) = value(s, v, (depth - 1) as nat, t1) {
                        let m2 = skip_ws(s, m);
                        if 0 <= m2 < s.len() && s[m2] == 0x2C && i < m2 + 1 <= s.len() {
                            lemma_members_fail(s, m2 + 1, depth, t2);
                        }
                    }
                }
            }
        }
    }
}

pub proof fn lemma_bad_utf8(s: Seq<u8>, i: int)
    ensures
        bad_utf8(s, i) is None == utf8_from(s, i),
        bad_utf8(s, i) matches Some(u) ==> i <= u < s.len(),
    decreases s.len() - i,
{
    if 0 <= i < s.len() {
        if let Some(l) = utf8_len(s, i) {
            lemma_bad_utf8(s, i + l);
        }
    }
}

/// **`doc_fail` reports an error exactly when `document` rejects the
/// text**, and otherwise ends where `document` does.
pub proof fn lemma_doc_fail(s: Seq<u8>, require_end: bool)
    ensures
        doc_fail(s, require_end) is Ok == document(s, require_end) is Some,
        document(s, require_end) matches Some((_, k)) ==> doc_fail(s, require_end) == Ok::<int, Fail>(k),
{
    if s.len() <= MAX_INPUT {
        let b = bom_end(s);
        let v = skip_ws(s, b);
        lemma_value_fail(s, v, MAX_DEPTH as nat, Seq::empty());
        if let Some((_, k)) = value(s, v, MAX_DEPTH as nat, Seq::empty()) {
            lemma_bad_utf8(s.subrange(0, if require_end { s.len() as int } else { k }), b);
        }
    }
}

// ---------------------------------------------------------------------------
// Computing it
// ---------------------------------------------------------------------------

/// `r` is `g`, with machine integers.
pub open spec fn same(r: Result<usize, (usize, Why)>, g: Result<int, Fail>) -> bool {
    match (r, g) {
        (Ok(a), Ok(b)) => a as int == b,
        (Err((p, w)), Err((q, x))) => p as int == q && w == x,
        _ => false,
    }
}

/// `r` is a position in `s[i..]`, or its end.
pub open spec fn bounded(r: Result<usize, (usize, Why)>, i: int, n: int) -> bool {
    &&& r matches Ok(k) ==> i < k <= n
    &&& r matches Err((p, _)) ==> p <= n
}

fn ex_char_fail(s: &[u8], i: usize) -> (r: (usize, Why))
    requires
        i < s@.len(),
    ensures
        (r.0 as int, r.1) == char_fail(s@, i as int),
        r.0 <= s@.len(),
{
    if s[i] < 0x20 {
        (i, Why::ControlCharacter(s[i]))
    } else if i + 1 >= s.len() {
        (s.len(), Why::UnterminatedString)
    } else {
        (i, Why::InvalidEscape)
    }
}

fn ex_str_fail(s: &[u8], i0: usize) -> (r: Result<usize, (usize, Why)>)
    requires
        i0 <= s@.len(),
    ensures
        same(r, str_fail(s@, i0 as int)),
        bounded(r, i0 as int, s@.len() as int),
{
    let mut i = i0;
    loop
        invariant
            i0 <= i <= s@.len(),
            str_fail(s@, i0 as int) == str_fail(s@, i as int),
        decreases s@.len() - i,
    {
        if i >= s.len() {
            return Err((s.len(), Why::UnterminatedString));
        }
        let c = s[i];
        if c == 0x22 {
            return Ok(i + 1);
        }
        if c < 0x20 {
            return Err((i, Why::ControlCharacter(c)));
        }
        if c != 0x5C {
            assert(string_char(s@, i as int) == Some((seq![c], i + 1)));
            i += 1;
        } else {
            match ex_escape_end(s, i) {
                Some(n) => {
                    i = n;
                },
                None => {
                    return Err(ex_char_fail(s, i));
                },
            }
        }
    }
}

fn ex_lit_fail(s: &[u8], i: usize, lit: &[u8]) -> (r: (usize, Why))
    requires
        i < s@.len(),
    ensures
        (r.0 as int, r.1) == lit_fail(s@, i as int, lit@),
        r.0 <= s@.len(),
{
    let n = s.len() - i;
    if n >= lit.len() {
        return (i, Why::InvalidLiteral);
    }
    let mut j = i;
    while j < s.len()
        invariant
            i <= j <= s@.len(),
            s@.len() - i < lit@.len(),
            forall|m: int| 0 <= m < j - i ==> s@[i + m] == lit@[m],
        decreases s@.len() - j,
    {
        if s[j] != lit[j - i] {
            proof {
                assert(s@.subrange(i as int, s@.len() as int)[j - i] != lit@.subrange(0, s@.len() - i)[j - i]);
            }
            return (i, Why::InvalidLiteral);
        }
        j += 1;
    }
    proof {
        assert(s@.subrange(i as int, s@.len() as int) =~= lit@.subrange(0, s@.len() - i));
    }
    (s.len(), Why::UnexpectedEnd)
}

fn ex_next_fail(s: &[u8], v: usize, k: usize, k2: usize) -> (r: (usize, Why))
    requires
        k2 < s@.len(),
        v <= k2,
    ensures
        (r.0 as int, r.1) == next_fail(s@, v as int, k as int, k2 as int),
        r.0 <= s@.len(),
{
    let c = s[k2];
    if k2 == k && 0 < k && ex_is_digit(s[k - 1]) && (ex_is_digit(c) || c == 0x2E || c == 0x45 || c == 0x65
        || c == 0x2B || c == 0x2D) {
        (v, Why::InvalidNumber)
    } else {
        (k2, Why::UnexpectedByte(c))
    }
}

fn ex_value_fail(s: &[u8], i: usize, depth: usize) -> (r: Result<usize, (usize, Why)>)
    requires
        i <= s@.len(),
    ensures
        same(r, value_fail(s@, i as int, depth as nat)),
        bounded(r, i as int, s@.len() as int),
    decreases depth, s@.len() - i, 2nat,
{
    // Only the brackets recurse; everything else is in `ex_scalar_fail`,
    // which keeps this function's stack frame small for deep nesting.
    if i < s.len() && (s[i] == 0x5B || s[i] == 0x7B) {
        if depth == 0 {
            Err((i, Why::TooDeep))
        } else if s[i] == 0x5B {
            ex_array_fail(s, i + 1, depth)
        } else {
            ex_object_fail(s, i + 1, depth)
        }
    } else {
        ex_scalar_fail(s, i, depth)
    }
}

#[inline(never)]
fn ex_scalar_fail(s: &[u8], i: usize, depth: usize) -> (r: Result<usize, (usize, Why)>)
    requires
        i <= s@.len(),
        i < s@.len() ==> s@[i as int] != 0x5B && s@[i as int] != 0x7B,
    ensures
        same(r, value_fail(s@, i as int, depth as nat)),
        bounded(r, i as int, s@.len() as int),
{
    if i >= s.len() {
        return Err((s.len(), Why::UnexpectedEnd));
    }
    let c = s[i];
    if c == 0x22 {
        ex_str_fail(s, i + 1)
    } else if c == 0x74 {
        let lit: &[u8] = &[0x74u8, 0x72, 0x75, 0x65];
        assert(lit@ == seq![0x74u8, 0x72, 0x75, 0x65]);
        if ex_has_lit(s, i, lit) {
            Ok(i + 4)
        } else {
            Err(ex_lit_fail(s, i, lit))
        }
    } else if c == 0x66 {
        let lit: &[u8] = &[0x66u8, 0x61, 0x6C, 0x73, 0x65];
        assert(lit@ == seq![0x66u8, 0x61, 0x6C, 0x73, 0x65]);
        if ex_has_lit(s, i, lit) {
            Ok(i + 5)
        } else {
            Err(ex_lit_fail(s, i, lit))
        }
    } else if c == 0x6E {
        let lit: &[u8] = &[0x6Eu8, 0x75, 0x6C, 0x6C];
        assert(lit@ == seq![0x6Eu8, 0x75, 0x6C, 0x6C]);
        if ex_has_lit(s, i, lit) {
            Ok(i + 4)
        } else {
            Err(ex_lit_fail(s, i, lit))
        }
    } else if c == 0x2D || ex_is_digit(c) {
        match ex_number_end(s, i) {
            Some(e) => Ok(e),
            None => Err((i, Why::InvalidNumber)),
        }
    } else {
        Err((i, Why::UnexpectedByte(c)))
    }
}

fn ex_array_fail(s: &[u8], i: usize, depth: usize) -> (r: Result<usize, (usize, Why)>)
    requires
        i <= s@.len(),
    ensures
        same(r, array_fail(s@, i as int, depth as nat)),
        bounded(r, i as int, s@.len() as int),
    decreases depth, s@.len() - i, 1nat,
{
    let j = ex_skip_ws(s, i);
    if j < s.len() && s[j] == 0x5D {
        Ok(j + 1)
    } else {
        ex_elements_fail(s, i, depth)
    }
}

fn ex_elements_fail(s: &[u8], i0: usize, depth: usize) -> (r: Result<usize, (usize, Why)>)
    requires
        i0 <= s@.len(),
    ensures
        same(r, elements_fail(s@, i0 as int, depth as nat)),
        bounded(r, i0 as int, s@.len() as int),
    decreases depth, s@.len() - i0, 0nat,
{
    if depth == 0 {
        return Err((i0, Why::TooDeep));
    }
    let mut i = i0;
    loop
        invariant
            i0 <= i <= s@.len(),
            depth > 0,
            elements_fail(s@, i0 as int, depth as nat) == elements_fail(s@, i as int, depth as nat),
        decreases s@.len() - i,
    {
        let v = ex_skip_ws(s, i);
        let k = match ex_value_fail(s, v, depth - 1) {
            Ok(k) => k,
            Err(f) => return Err(f),
        };
        let k2 = ex_skip_ws(s, k);
        if k2 >= s.len() {
            return Err((s.len(), Why::UnexpectedEnd));
        }
        if s[k2] == 0x5D {
            return Ok(k2 + 1);
        }
        if s[k2] != 0x2C {
            return Err(ex_next_fail(s, v, k, k2));
        }
        i = k2 + 1;
    }
}

fn ex_object_fail(s: &[u8], i: usize, depth: usize) -> (r: Result<usize, (usize, Why)>)
    requires
        i <= s@.len(),
    ensures
        same(r, object_fail(s@, i as int, depth as nat)),
        bounded(r, i as int, s@.len() as int),
    decreases depth, s@.len() - i, 1nat,
{
    let j = ex_skip_ws(s, i);
    if j < s.len() && s[j] == 0x7D {
        Ok(j + 1)
    } else {
        ex_members_fail(s, i, depth)
    }
}

fn ex_members_fail(s: &[u8], i0: usize, depth: usize) -> (r: Result<usize, (usize, Why)>)
    requires
        i0 <= s@.len(),
    ensures
        same(r, members_fail(s@, i0 as int, depth as nat)),
        bounded(r, i0 as int, s@.len() as int),
    decreases depth, s@.len() - i0, 0nat,
{
    if depth == 0 {
        return Err((i0, Why::TooDeep));
    }
    let mut i = i0;
    loop
        invariant
            i0 <= i <= s@.len(),
            depth > 0,
            members_fail(s@, i0 as int, depth as nat) == members_fail(s@, i as int, depth as nat),
        decreases s@.len() - i,
    {
        let j = ex_skip_ws(s, i);
        if j >= s.len() {
            return Err((s.len(), Why::UnexpectedEnd));
        }
        if s[j] != 0x22 {
            return Err((j, Why::UnexpectedByte(s[j])));
        }
        let k = match ex_str_fail(s, j + 1) {
            Ok(k) => k,
            Err(f) => return Err(f),
        };
        let c = ex_skip_ws(s, k);
        if c >= s.len() {
            return Err((s.len(), Why::UnexpectedEnd));
        }
        if s[c] != 0x3A {
            return Err((c, Why::UnexpectedByte(s[c])));
        }
        let v = ex_skip_ws(s, c + 1);
        let m = match ex_value_fail(s, v, depth - 1) {
            Ok(m) => m,
            Err(f) => return Err(f),
        };
        let m2 = ex_skip_ws(s, m);
        if m2 >= s.len() {
            return Err((s.len(), Why::UnexpectedEnd));
        }
        if s[m2] == 0x7D {
            return Ok(m2 + 1);
        }
        if s[m2] != 0x2C {
            return Err(ex_next_fail(s, v, m, m2));
        }
        i = m2 + 1;
    }
}

/// The length of the well-formed UTF-8 sequence at `i`, or 0.
fn ex_utf8_len(s: &[u8], i: usize) -> (r: usize)
    requires
        i < s.len(),
    ensures
        r == match utf8_len(s@, i as int) {
            Some(l) => l,
            None => 0,
        },
        r <= 4,
{
    let n = s.len();
    let b = s[i];
    if b <= 0x7F {
        1
    } else if 0xC2 <= b && b <= 0xDF {
        if n - i > 1 && 0x80 <= s[i + 1] && s[i + 1] <= 0xBF { 2 } else { 0 }
    } else if 0xE0 <= b && b <= 0xEF {
        let lo: u8 = if b == 0xE0 { 0xA0 } else { 0x80 };
        let hi: u8 = if b == 0xED { 0x9F } else { 0xBF };
        if n - i > 2 && lo <= s[i + 1] && s[i + 1] <= hi && 0x80 <= s[i + 2] && s[i + 2] <= 0xBF { 3 } else { 0 }
    } else if 0xF0 <= b && b <= 0xF4 {
        let lo: u8 = if b == 0xF0 { 0x90 } else { 0x80 };
        let hi: u8 = if b == 0xF4 { 0x8F } else { 0xBF };
        if n - i > 3 && lo <= s[i + 1] && s[i + 1] <= hi && 0x80 <= s[i + 2] && s[i + 2] <= 0xBF && 0x80 <= s[i
            + 3] && s[i + 3] <= 0xBF {
            4
        } else {
            0
        }
    } else {
        0
    }
}

fn ex_bad_utf8(s: &[u8], i0: usize) -> (r: Option<usize>)
    requires
        i0 <= s@.len(),
    ensures
        r matches Some(x) ==> bad_utf8(s@, i0 as int) == Some(x as int) && i0 <= x < s@.len(),
        r is None ==> bad_utf8(s@, i0 as int) is None,
{
    proof {
        lemma_bad_utf8(s@, i0 as int);
    }
    let mut i = i0;
    while i < s.len()
        invariant
            i0 <= i <= s@.len(),
            bad_utf8(s@, i0 as int) == bad_utf8(s@, i as int),
        decreases s@.len() - i,
    {
        let l = ex_utf8_len(s, i);
        if l == 0 {
            return Some(i);
        }
        i += l;
    }
    None
}

fn ex_or_utf8(s: &[u8], b: usize, f: (usize, Why)) -> (r: (usize, Why))
    requires
        b as int == bom_end(s@),
        f.0 <= s@.len(),
    ensures
        (r.0 as int, r.1) == or_utf8(s@, (f.0 as int, f.1)),
        r.0 <= s@.len(),
{
    let x = ex_bad_utf8(s, b);
    proof {
        lemma_bad_utf8(s@, b as int);
    }
    match x {
        Some(u) => {
            if u <= f.0 {
                (u, Why::InvalidUtf8)
            } else {
                f
            }
        },
        None => f,
    }
}

/// **The error `s` gets** (`doc_fail`), when `document` rejects it.
pub fn explain(s: &[u8], require_end: bool) -> (r: (usize, Why))
    requires
        document(s@, require_end) is None,
    ensures
        doc_fail(s@, require_end) == Err::<int, Fail>((r.0 as int, r.1)),
        r.0 <= s@.len(),
{
    proof {
        lemma_doc_fail(s@, require_end);
    }
    if s.len() > MAX_INPUT {
        return (0, Why::TooLarge);
    }
    let b: usize = if ex_has_lit(s, 0, &[0xEF, 0xBB, 0xBF]) { 3 } else { 0 };
    proof {
        assert([0xEFu8, 0xBB, 0xBF]@ == seq![0xEFu8, 0xBB, 0xBF]);
    }
    let v = ex_skip_ws(s, b);
    let k = match ex_value_fail(s, v, MAX_DEPTH) {
        Ok(k) => k,
        Err(f) => return ex_or_utf8(s, b, f),
    };
    let e = ex_skip_ws(s, k);
    if require_end && e != s.len() {
        let f = if e == k && 0 < k && ex_is_digit(s[k - 1]) && (ex_is_digit(s[e]) || s[e] == 0x2E || s[e] == 0x45
            || s[e] == 0x65 || s[e] == 0x2B || s[e] == 0x2D) {
            (v, Why::InvalidNumber)
        } else {
            (e, Why::TrailingData)
        };
        return ex_or_utf8(s, b, f);
    }
    if !require_end && 0 < k && k < s.len() && ex_is_digit(s[k - 1]) && (ex_is_digit(s[k]) || s[k] == 0x2E || s[k]
        == 0x45 || s[k] == 0x65 || s[k] == 0x2B || s[k] == 0x2D) {
        return ex_or_utf8(s, b, (v, Why::InvalidNumber));
    }
    let lim = if require_end { s.len() } else { k };
    let t = slice_subrange(s, 0, lim);
    assert(t@ == s@.subrange(0, lim as int));
    assert(b as int == bom_end(s@) && b <= v <= k <= lim);
    match ex_bad_utf8(t, b) {
        Some(u) => {
            assert(u < lim);
            assert(doc_fail(s@, require_end) == Err::<int, Fail>((u as int, Why::InvalidUtf8)));
            (u, Why::InvalidUtf8)
        },
        None => {
            // Unreachable: `document` rejects `s`.
            assert(doc_fail(s@, require_end) == Ok::<int, Fail>(k as int));
            (0, Why::TooLarge)
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
