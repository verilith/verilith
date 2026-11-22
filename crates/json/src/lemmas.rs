//! Facts about the specification itself.
//!
//! The main result here is that the `if !(i < n <= s.len()) { None }`
//! termination guards in `spec.rs` are never taken: every successful parse
//! step consumes at least one byte and stays within the input. So the spec
//! means exactly what the grammar comments say, and the guards exist only to
//! make termination syntactic.
#[allow(unused_imports)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub proof fn lemma_skip_ws_bounds(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= skip_ws(s, i) <= s.len(),
        skip_ws(s, i) < s.len() ==> !is_ws(s[skip_ws(s, i)]),
    decreases s.len() - i,
{
    if i < s.len() && is_ws(s[i]) {
        lemma_skip_ws_bounds(s, i + 1);
    }
}

pub proof fn lemma_string_char_advances(s: Seq<u8>, i: int)
    ensures
        string_char(s, i) matches Some((_, n)) ==> i < n <= s.len(),
{
}

pub proof fn lemma_string_body_advances(s: Seq<u8>, i: int, esc: bool)
    ensures
        string_body(s, i, esc) matches Some((n, _)) ==> i < n <= s.len(),
    decreases s.len() - i,
{
    if 0 <= i < s.len() && s[i] != 0x22 {
        match string_char(s, i) {
            Some((_, n)) => {
                if i < n <= s.len() {
                    lemma_string_body_advances(s, n, esc || s[i] == 0x5C);
                }
            },
            None => {},
        }
    }
}

/// The guard in `string_body` is never taken.
pub proof fn lemma_string_body_guard(s: Seq<u8>, i: int)
    ensures
        string_char(s, i) matches Some((_, n)) ==> i < n <= s.len(),
{
    lemma_string_char_advances(s, i);
}

pub proof fn lemma_number_end_advances(s: Seq<u8>, i: int)
    ensures
        number_end(s, i) matches Some(e) ==> i < e <= s.len(),
{
    let j = if 0 <= i < s.len() && s[i] == 0x2D { i + 1 } else { i };
    if 0 <= j < s.len() && is_digit(s[j]) {
        lemma_digits_end_bounds(s, j);
        let k = if s[j] == 0x30 { j + 1 } else { digits_end(s, j) };
        if 0 <= k < s.len() && s[k] == 0x2E {
            lemma_digits_end_bounds(s, k + 1);
        }
        let k2 = if 0 <= k < s.len() && s[k] == 0x2E { digits_end(s, k + 1) } else { k };
        let m = if k2 + 1 < s.len() && (s[k2 + 1] == 0x2B || s[k2 + 1] == 0x2D) {
            k2 + 2
        } else {
            k2 + 1
        };
        if 0 <= k2 < s.len() && m <= s.len() {
            lemma_digits_end_bounds(s, m);
        }
    }
}

pub proof fn lemma_digits_end_bounds(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= digits_end(s, i) <= s.len(),
        i < s.len() && is_digit(s[i]) ==> i < digits_end(s, i),
    decreases s.len() - i,
{
    if i < s.len() && is_digit(s[i]) {
        lemma_digits_end_bounds(s, i + 1);
    }
}

/// Every successful value parse consumes input and stays in bounds.
pub proof fn lemma_value_advances(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        value(s, i, depth, tape) matches Some((_, n)) ==> i < n <= s.len(),
    decreases depth, s.len() - i, 2nat,
{
    if 0 <= i < s.len() {
        let c = s[i];
        if c == 0x5B && depth > 0 {
            lemma_array_advances(s, i + 1, depth, tape.push(STok::ArrStart { end: 0 }));
        } else if c == 0x7B && depth > 0 {
            lemma_object_advances(s, i + 1, depth, tape.push(STok::ObjStart { end: 0 }));
        } else if c == 0x22 {
            lemma_string_body_advances(s, i + 1, false);
        } else {
            lemma_number_end_advances(s, i);
        }
    }
}

pub proof fn lemma_array_advances(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        array(s, i, depth, tape) matches Some((_, n)) ==> i < n <= s.len(),
    decreases depth, s.len() - i, 1nat,
{
    if 0 <= i <= s.len() {
        lemma_skip_ws_bounds(s, i);
    }
    lemma_elements_advances(s, i, depth, tape);
}

pub proof fn lemma_object_advances(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        object(s, i, depth, tape) matches Some((_, n)) ==> i < n <= s.len(),
    decreases depth, s.len() - i, 1nat,
{
    if 0 <= i <= s.len() {
        lemma_skip_ws_bounds(s, i);
    }
    lemma_members_advances(s, i, depth, tape);
}

pub proof fn lemma_elements_advances(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        elements(s, i, depth, tape) matches Some((_, n)) ==> i < n <= s.len(),
    decreases depth, s.len() - i, 0nat,
{
    if 0 <= i <= s.len() {
        lemma_skip_ws_bounds(s, i);
    }
    if depth > 0 {
        let j = skip_ws(s, i);
        lemma_value_advances(s, j, (depth - 1) as nat, tape);
        match value(s, j, (depth - 1) as nat, tape) {
            None => {},
            Some((t, k)) => {
                lemma_skip_ws_bounds(s, k);
                let k2 = skip_ws(s, k);
                if 0 <= k2 < s.len() && s[k2] == 0x2C && i < k2 + 1 <= s.len() {
                    lemma_elements_advances(s, k2 + 1, depth, t);
                }
            },
        }
    }
}

pub proof fn lemma_members_advances(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        members(s, i, depth, tape) matches Some((_, n)) ==> i < n <= s.len(),
    decreases depth, s.len() - i, 0nat,
{
    if 0 <= i <= s.len() {
        lemma_skip_ws_bounds(s, i);
        let j = skip_ws(s, i);
        if 0 <= j < s.len() && s[j] == 0x22 {
            lemma_string_body_advances(s, j + 1, false);
        }
    }
    if depth > 0 {
        match string(s, skip_ws(s, i)) {
            None => {},
            Some((k, esc)) => {
                lemma_skip_ws_bounds(s, k);
                let c = skip_ws(s, k);
                if 0 <= c < s.len() && s[c] == 0x3A {
                    lemma_skip_ws_bounds(s, c + 1);
                    let t1 = tape.push(STok::Key { start: skip_ws(s, i) + 1, end: k - 1, escaped: esc });
                    let vs = skip_ws(s, c + 1);
                    lemma_value_advances(s, vs, (depth - 1) as nat, t1);
                    match value(s, vs, (depth - 1) as nat, t1) {
                        None => {},
                        Some((t, m)) => {
                            lemma_skip_ws_bounds(s, m);
                            let m2 = skip_ws(s, m);
                            if 0 <= m2 < s.len() && s[m2] == 0x2C && i < m2 + 1 <= s.len() {
                                lemma_members_advances(s, m2 + 1, depth, t);
                            }
                        },
                    }
                }
            },
        }
    }
}

/// The guard in `elements` is never taken: when the separator after an
/// element is a ',', the next position is after `i` and within bounds.
pub proof fn lemma_elements_guard(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= i <= s.len(),
        depth > 0,
    ensures
        value(s, skip_ws(s, i), (depth - 1) as nat, tape) matches Some((_, k)) ==> {
            let k2 = skip_ws(s, k);
            k2 < s.len() ==> i < k2 + 1 <= s.len()
        },
{
    lemma_skip_ws_bounds(s, i);
    lemma_value_advances(s, skip_ws(s, i), (depth - 1) as nat, tape);
    if let Some((_, k)) = value(s, skip_ws(s, i), (depth - 1) as nat, tape) {
        lemma_skip_ws_bounds(s, k);
    }
}

/// The guard in `members` is never taken.
pub proof fn lemma_members_guard(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= i <= s.len(),
        depth > 0,
    ensures
        string(s, skip_ws(s, i)) matches Some((k, esc)) ==> {
            let c = skip_ws(s, k);
            let t1 = tape.push(STok::Key { start: skip_ws(s, i) + 1, end: k - 1, escaped: esc });
            (0 <= c < s.len() && s[c] == 0x3A) ==> (value(
                s,
                skip_ws(s, c + 1),
                (depth - 1) as nat,
                t1,
            ) matches Some((_, m)) ==> {
                let m2 = skip_ws(s, m);
                m2 < s.len() ==> i < m2 + 1 <= s.len()
            })
        },
{
    lemma_skip_ws_bounds(s, i);
    let j = skip_ws(s, i);
    if 0 <= j < s.len() && s[j] == 0x22 {
        lemma_string_body_advances(s, j + 1, false);
    }
    if let Some((k, esc)) = string(s, j) {
        lemma_skip_ws_bounds(s, k);
        let c = skip_ws(s, k);
        if 0 <= c < s.len() && s[c] == 0x3A {
            lemma_skip_ws_bounds(s, c + 1);
            let t1 = tape.push(STok::Key { start: skip_ws(s, i) + 1, end: k - 1, escaped: esc });
            lemma_value_advances(s, skip_ws(s, c + 1), (depth - 1) as nat, t1);
            if let Some((_, m)) = value(s, skip_ws(s, c + 1), (depth - 1) as nat, t1) {
                lemma_skip_ws_bounds(s, m);
            }
        }
    }
}

/// Parsing only appends to the tape.
pub open spec fn extends(t: Seq<STok>, t0: Seq<STok>) -> bool {
    t.len() >= t0.len() && t.subrange(0, t0.len() as int) == t0
}

proof fn lemma_extends_push(t: Seq<STok>, t0: Seq<STok>, x: STok)
    requires
        extends(t, t0.push(x)),
    ensures
        extends(t, t0),
        t[t0.len() as int] == x,
{
    assert(t.subrange(0, t0.len() as int) =~= t.subrange(0, (t0.len() + 1) as int).subrange(0, t0.len() as int));
    assert(t0.push(x).subrange(0, t0.len() as int) =~= t0);
    assert(t[t0.len() as int] == t.subrange(0, (t0.len() + 1) as int)[t0.len() as int]);
}

proof fn lemma_extends_trans(t: Seq<STok>, t1: Seq<STok>, t0: Seq<STok>)
    requires
        extends(t, t1),
        extends(t1, t0),
    ensures
        extends(t, t0),
{
    assert(t.subrange(0, t0.len() as int) =~= t.subrange(0, t1.len() as int).subrange(0, t0.len() as int));
}

/// Setting a link past the prefix keeps the prefix.
proof fn lemma_extends_close(t: Seq<STok>, t0: Seq<STok>)
    requires
        extends(t, t0),
        t.len() > t0.len(),
    ensures
        extends(close_at(t, t0.len() as int), t0),
{
    assert(close_at(t, t0.len() as int).subrange(0, t0.len() as int) =~= t.subrange(0, t0.len() as int));
}

proof fn lemma_extends_refl_push(t0: Seq<STok>, x: STok)
    ensures
        extends(t0.push(x), t0),
{
    assert(t0.push(x).subrange(0, t0.len() as int) =~= t0);
}

pub proof fn lemma_value_extends(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        value(s, i, depth, tape) matches Some((t, _)) ==> extends(t, tape),
    decreases depth, s.len() - i, 2nat,
{
    if 0 <= i < s.len() {
        let c = s[i];
        if c == 0x5B && depth > 0 {
            let x = STok::ArrStart { end: 0 };
            lemma_array_extends(s, i + 1, depth, tape.push(x));
            if let Some((t, _)) = array(s, i + 1, depth, tape.push(x)) {
                lemma_extends_push(t, tape, x);
                lemma_extends_close(t, tape);
            }
        } else if c == 0x7B && depth > 0 {
            let x = STok::ObjStart { end: 0 };
            lemma_object_extends(s, i + 1, depth, tape.push(x));
            if let Some((t, _)) = object(s, i + 1, depth, tape.push(x)) {
                lemma_extends_push(t, tape, x);
                lemma_extends_close(t, tape);
            }
        } else if let Some((t, _)) = value(s, i, depth, tape) {
            assert(t == tape.push(t.last()));
            lemma_extends_refl_push(tape, t.last());
        }
    }
}

pub proof fn lemma_array_extends(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        array(s, i, depth, tape) matches Some((t, _)) ==> extends(t, tape),
    decreases depth, s.len() - i, 1nat,
{
    lemma_extends_refl_push(tape, STok::ArrEnd);
    lemma_elements_extends(s, i, depth, tape);
}

pub proof fn lemma_object_extends(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        object(s, i, depth, tape) matches Some((t, _)) ==> extends(t, tape),
    decreases depth, s.len() - i, 1nat,
{
    lemma_extends_refl_push(tape, STok::ObjEnd);
    lemma_members_extends(s, i, depth, tape);
}

pub proof fn lemma_elements_extends(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        elements(s, i, depth, tape) matches Some((t, _)) ==> extends(t, tape),
    decreases depth, s.len() - i, 0nat,
{
    if depth > 0 {
        let j = skip_ws(s, i);
        lemma_value_extends(s, j, (depth - 1) as nat, tape);
        if let Some((t1, k)) = value(s, j, (depth - 1) as nat, tape) {
            let k2 = skip_ws(s, k);
            lemma_extends_refl_push(t1, STok::ArrEnd);
            lemma_extends_trans(t1.push(STok::ArrEnd), t1, tape);
            if 0 <= k2 < s.len() && s[k2] == 0x2C && i < k2 + 1 <= s.len() {
                lemma_elements_extends(s, k2 + 1, depth, t1);
                if let Some((t, _)) = elements(s, k2 + 1, depth, t1) {
                    lemma_extends_trans(t, t1, tape);
                }
            }
        }
    }
}

pub proof fn lemma_members_extends(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        members(s, i, depth, tape) matches Some((t, _)) ==> extends(t, tape),
    decreases depth, s.len() - i, 0nat,
{
    if depth > 0 {
        let j = skip_ws(s, i);
        if let Some((k, esc)) = string(s, j) {
            let c = skip_ws(s, k);
            let key = STok::Key { start: j + 1, end: k - 1, escaped: esc };
            let tk = tape.push(key);
            let vs = skip_ws(s, c + 1);
            lemma_value_extends(s, vs, (depth - 1) as nat, tk);
            lemma_extends_refl_push(tape, key);
            if let Some((t1, m)) = value(s, vs, (depth - 1) as nat, tk) {
                lemma_extends_trans(t1, tk, tape);
                let m2 = skip_ws(s, m);
                lemma_extends_refl_push(t1, STok::ObjEnd);
                lemma_extends_trans(t1.push(STok::ObjEnd), t1, tape);
                if 0 <= m2 < s.len() && s[m2] == 0x2C && i < m2 + 1 <= s.len() {
                    lemma_members_extends(s, m2 + 1, depth, t1);
                    if let Some((t, _)) = members(s, m2 + 1, depth, t1) {
                        lemma_extends_trans(t, t1, tape);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Token ranges lie within the input
// ---------------------------------------------------------------------------

/// A token's byte range, if it has one, lies within an input of `n` bytes.
pub open spec fn tok_in(n: int, t: STok) -> bool {
    match t {
        STok::Num { start, end } => 0 <= start <= end <= n,
        STok::Str { start, end, .. } => 0 <= start <= end <= n,
        STok::Key { start, end, .. } => 0 <= start <= end <= n,
        _ => true,
    }
}

/// Every token's byte range lies within an input of `n` bytes. The
/// parsers ensure this of every tape they return, which is what lets the
/// value reader (`value.rs`) slice the input without bounds checks.
/// `t` is not empty and does not end with a key, so every key in it is
/// followed by another token (its value).
pub open spec fn ends_value(t: Seq<STok>) -> bool {
    t.len() > 0 && !(t.last() is Key)
}

pub open spec fn in_bounds(n: int, t: Seq<STok>) -> bool {
    forall|k: int| 0 <= k < t.len() ==> tok_in(n, #[trigger] t[k])
}

/// Setting a link keeps a tape within the input and ending with a value.
proof fn lemma_in_bounds_close(n: int, t: Seq<STok>, k: int)
    requires
        in_bounds(n, t),
        ends_value(t),
        0 <= k < t.len(),
    ensures
        in_bounds(n, close_at(t, k)),
        ends_value(close_at(t, k)),
{
    let c = close_at(t, k);
    assert forall|m: int| 0 <= m < c.len() implies tok_in(n, #[trigger] c[m]) by {
        if m != k {
            assert(c[m] == t[m]);
        }
    }
    if k != t.len() - 1 {
        assert(c.last() == t.last());
    }
}

proof fn lemma_in_bounds_push(n: int, t: Seq<STok>, x: STok)
    requires
        in_bounds(n, t),
        tok_in(n, x),
    ensures
        in_bounds(n, t.push(x)),
{
    assert forall|k: int| 0 <= k < t.push(x).len() implies tok_in(n, #[trigger] t.push(x)[k]) by {
        if k < t.len() {
            assert(t.push(x)[k] == t[k]);
        }
    }
}

pub proof fn lemma_value_in_bounds(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        in_bounds(s.len() as int, tape),
    ensures
        value(s, i, depth, tape) matches Some((t, _)) ==> in_bounds(s.len() as int, t)
            && ends_value(t),
    decreases depth, s.len() - i, 2nat,
{
    let n = s.len() as int;
    if 0 <= i < s.len() {
        let c = s[i];
        if c == 0x5B && depth > 0 {
            let x = STok::ArrStart { end: 0 };
            lemma_in_bounds_push(n, tape, x);
            lemma_array_in_bounds(s, i + 1, depth, tape.push(x));
            lemma_array_extends(s, i + 1, depth, tape.push(x));
            if let Some((t, _)) = array(s, i + 1, depth, tape.push(x)) {
                lemma_in_bounds_close(n, t, tape.len() as int);
            }
        } else if c == 0x7B && depth > 0 {
            let x = STok::ObjStart { end: 0 };
            lemma_in_bounds_push(n, tape, x);
            lemma_object_in_bounds(s, i + 1, depth, tape.push(x));
            lemma_object_extends(s, i + 1, depth, tape.push(x));
            if let Some((t, _)) = object(s, i + 1, depth, tape.push(x)) {
                lemma_in_bounds_close(n, t, tape.len() as int);
            }
        } else if c == 0x22 {
            lemma_string_body_advances(s, i + 1, false);
            if let Some((e, esc)) = string(s, i) {
                lemma_in_bounds_push(n, tape, STok::Str { start: i + 1, end: e - 1, escaped: esc });
            }
        } else if c == 0x74 {
            lemma_in_bounds_push(n, tape, STok::True);
        } else if c == 0x66 {
            lemma_in_bounds_push(n, tape, STok::False);
        } else if c == 0x6E {
            lemma_in_bounds_push(n, tape, STok::Null);
        } else {
            lemma_number_end_advances(s, i);
            if let Some(e) = number_end(s, i) {
                lemma_in_bounds_push(n, tape, STok::Num { start: i, end: e });
            }
        }
    }
}

pub proof fn lemma_array_in_bounds(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        in_bounds(s.len() as int, tape),
    ensures
        array(s, i, depth, tape) matches Some((t, _)) ==> in_bounds(s.len() as int, t)
            && ends_value(t),
    decreases depth, s.len() - i, 1nat,
{
    lemma_in_bounds_push(s.len() as int, tape, STok::ArrEnd);
    lemma_elements_in_bounds(s, i, depth, tape);
}

pub proof fn lemma_object_in_bounds(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        in_bounds(s.len() as int, tape),
    ensures
        object(s, i, depth, tape) matches Some((t, _)) ==> in_bounds(s.len() as int, t)
            && ends_value(t),
    decreases depth, s.len() - i, 1nat,
{
    lemma_in_bounds_push(s.len() as int, tape, STok::ObjEnd);
    lemma_members_in_bounds(s, i, depth, tape);
}

pub proof fn lemma_elements_in_bounds(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        in_bounds(s.len() as int, tape),
    ensures
        elements(s, i, depth, tape) matches Some((t, _)) ==> in_bounds(s.len() as int, t)
            && ends_value(t),
    decreases depth, s.len() - i, 0nat,
{
    if depth > 0 {
        let j = skip_ws(s, i);
        lemma_value_in_bounds(s, j, (depth - 1) as nat, tape);
        if let Some((t1, k)) = value(s, j, (depth - 1) as nat, tape) {
            let k2 = skip_ws(s, k);
            lemma_in_bounds_push(s.len() as int, t1, STok::ArrEnd);
            if 0 <= k2 < s.len() && s[k2] == 0x2C && i < k2 + 1 <= s.len() {
                lemma_elements_in_bounds(s, k2 + 1, depth, t1);
            }
        }
    }
}

pub proof fn lemma_members_in_bounds(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        in_bounds(s.len() as int, tape),
    ensures
        members(s, i, depth, tape) matches Some((t, _)) ==> in_bounds(s.len() as int, t)
            && ends_value(t),
    decreases depth, s.len() - i, 0nat,
{
    if depth > 0 {
        let j = skip_ws(s, i);
        if let Some((k, esc)) = string(s, j) {
            lemma_string_body_advances(s, j + 1, false);
            let c = skip_ws(s, k);
            let key = STok::Key { start: j + 1, end: k - 1, escaped: esc };
            let tk = tape.push(key);
            lemma_in_bounds_push(s.len() as int, tape, key);
            let vs = skip_ws(s, c + 1);
            lemma_value_in_bounds(s, vs, (depth - 1) as nat, tk);
            if let Some((t1, m)) = value(s, vs, (depth - 1) as nat, tk) {
                let m2 = skip_ws(s, m);
                lemma_in_bounds_push(s.len() as int, t1, STok::ObjEnd);
                if 0 <= m2 < s.len() && s[m2] == 0x2C && i < m2 + 1 <= s.len() {
                    lemma_members_in_bounds(s, m2 + 1, depth, t1);
                }
            }
        }
    }
}

/// Every tape that `document` accepts lies within the input.
pub proof fn lemma_document_in_bounds(s: Seq<u8>, require_end: bool)
    ensures
        document(s, require_end) matches Some((t, _)) ==> in_bounds(s.len() as int, t)
            && ends_value(t),
{
    assert(in_bounds(s.len() as int, Seq::<STok>::empty()));
    lemma_value_in_bounds(s, skip_ws(s, bom_end(s)), MAX_DEPTH as nat, Seq::empty());
}

// ---------------------------------------------------------------------------
// Size: a tape has at most one token per input byte
// ---------------------------------------------------------------------------

/// What a token costs in the input: one byte, plus a string's raw body.
/// The bodies count because eager parsing decodes them into a side buffer
/// (`Tape::strs`), and a decoded body is never longer than its source.
pub open spec fn tok_weight(t: STok) -> int {
    match t {
        STok::Str { start, end, .. } => 1 + body_len(start, end),
        STok::Key { start, end, .. } => 1 + body_len(start, end),
        _ => 1,
    }
}

pub open spec fn body_len(start: int, end: int) -> int {
    if start <= end { end - start } else { 0 }
}

/// A `char` decodes to no more bytes than it spans.
pub proof fn lemma_string_char_len(s: Seq<u8>, i: int)
    ensures
        string_char(s, i) matches Some((b, n)) ==> b.len() <= n - i,
{
    if 0 <= i < s.len() && s[i] == 0x5C && i + 1 < s.len() && s[i + 1] == 0x75 {
        if let Some(u) = hex4(s, i + 2) {
            assert(utf8_encode(u).len() <= 4);
            if 0xD800 <= u <= 0xDBFF && i + 7 < s.len() {
                if let Some(lo) = hex4(s, i + 8) {
                    let cp = (0x10000 + (u - 0xD800) * 1024 + (lo - 0xDC00)) as u32;
                    assert(utf8_encode(cp).len() <= 4);
                }
            }
        }
    }
}

/// A string body decodes to no more bytes than it spans.
pub proof fn lemma_decode_len(s: Seq<u8>, i: int, end: int)
    requires
        i <= end,
    ensures
        decode(s, i, end).len() <= end - i,
    decreases end - i,
{
    if 0 <= i < end && end <= s.len() {
        lemma_string_char_len(s, i);
        if let Some((b, n)) = string_char(s, i) {
            if i < n <= end {
                lemma_decode_len(s, n, end);
            }
        }
    }
}

/// The total `tok_weight` of a tape.
pub open spec fn weight(t: Seq<STok>) -> int
    decreases t.len(),
{
    if t.len() == 0 {
        0
    } else {
        weight(t.drop_last()) + tok_weight(t.last())
    }
}

pub proof fn lemma_weight_push(t: Seq<STok>, x: STok)
    ensures
        weight(t.push(x)) == weight(t) + tok_weight(x),
{
    assert(t.push(x).drop_last() =~= t);
}

/// Replacing a token by one of the same weight keeps the weight.
pub proof fn lemma_weight_update(t: Seq<STok>, k: int, x: STok)
    requires
        0 <= k < t.len(),
        tok_weight(x) == tok_weight(t[k]),
    ensures
        weight(t.update(k, x)) == weight(t),
    decreases t.len(),
{
    let u = t.update(k, x);
    if k == t.len() - 1 {
        assert(u.drop_last() =~= t.drop_last());
    } else {
        assert(u.drop_last() =~= t.drop_last().update(k, x));
        lemma_weight_update(t.drop_last(), k, x);
    }
}

/// Setting a link keeps the weight.
pub proof fn lemma_weight_close(t: Seq<STok>, k: int)
    requires
        0 <= k < t.len(),
        t[k] is ArrStart || t[k] is ObjStart,
    ensures
        weight(close_at(t, k)) == weight(t),
        close_at(t, k).len() == t.len(),
{
    let x = match t[k] {
        STok::ObjStart { .. } => STok::ObjStart { end: t.len() - 1 },
        _ => STok::ArrStart { end: t.len() - 1 },
    };
    lemma_weight_update(t, k, x);
}

/// Every token weighs at least one, so the weight bounds the length.
pub proof fn lemma_weight_len(t: Seq<STok>)
    ensures
        t.len() <= weight(t),
    decreases t.len(),
{
    if t.len() > 0 {
        lemma_weight_len(t.drop_last());
    }
}

/// A value's tokens weigh no more than the bytes it spans.
pub proof fn lemma_value_size(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        value(s, i, depth, tape) matches Some((t, n)) ==> weight(t) - weight(tape) <= n - i
            && t.len() - tape.len() <= n - i,
    decreases depth, s.len() - i, 2nat,
{
    if 0 <= i < s.len() {
        let c = s[i];
        if c == 0x5B && depth > 0 {
            let x = STok::ArrStart { end: 0 };
            lemma_weight_push(tape, x);
            lemma_array_size(s, i + 1, depth, tape.push(x));
            lemma_array_extends(s, i + 1, depth, tape.push(x));
            if let Some((t, _)) = array(s, i + 1, depth, tape.push(x)) {
                lemma_extends_push(t, tape, x);
                lemma_weight_close(t, tape.len() as int);
            }
        } else if c == 0x7B && depth > 0 {
            let x = STok::ObjStart { end: 0 };
            lemma_weight_push(tape, x);
            lemma_object_size(s, i + 1, depth, tape.push(x));
            lemma_object_extends(s, i + 1, depth, tape.push(x));
            if let Some((t, _)) = object(s, i + 1, depth, tape.push(x)) {
                lemma_extends_push(t, tape, x);
                lemma_weight_close(t, tape.len() as int);
            }
        } else if c == 0x22 {
            lemma_string_body_advances(s, i + 1, false);
            if let Some((e, esc)) = string(s, i) {
                lemma_weight_push(tape, STok::Str { start: i + 1, end: e - 1, escaped: esc });
            }
        } else if c == 0x74 {
            lemma_weight_push(tape, STok::True);
        } else if c == 0x66 {
            lemma_weight_push(tape, STok::False);
        } else if c == 0x6E {
            lemma_weight_push(tape, STok::Null);
        } else {
            lemma_number_end_advances(s, i);
            if let Some(e) = number_end(s, i) {
                lemma_weight_push(tape, STok::Num { start: i, end: e });
            }
        }
    }
}

pub proof fn lemma_array_size(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= i <= s.len(),
    ensures
        array(s, i, depth, tape) matches Some((t, n)) ==> weight(t) - weight(tape) <= n - i
            && t.len() - tape.len() <= n - i,
    decreases depth, s.len() - i, 1nat,
{
    lemma_skip_ws_bounds(s, i);
    lemma_weight_push(tape, STok::ArrEnd);
    lemma_elements_size(s, i, depth, tape);
}

pub proof fn lemma_object_size(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= i <= s.len(),
    ensures
        object(s, i, depth, tape) matches Some((t, n)) ==> weight(t) - weight(tape) <= n - i
            && t.len() - tape.len() <= n - i,
    decreases depth, s.len() - i, 1nat,
{
    lemma_skip_ws_bounds(s, i);
    lemma_weight_push(tape, STok::ObjEnd);
    lemma_members_size(s, i, depth, tape);
}

pub proof fn lemma_elements_size(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= i <= s.len(),
    ensures
        elements(s, i, depth, tape) matches Some((t, n)) ==> weight(t) - weight(tape) <= n - i
            && t.len() - tape.len() <= n - i,
    decreases depth, s.len() - i, 0nat,
{
    lemma_skip_ws_bounds(s, i);
    if depth > 0 {
        let j = skip_ws(s, i);
        lemma_value_size(s, j, (depth - 1) as nat, tape);
        lemma_value_advances(s, j, (depth - 1) as nat, tape);
        if let Some((t1, k)) = value(s, j, (depth - 1) as nat, tape) {
            lemma_skip_ws_bounds(s, k);
            let k2 = skip_ws(s, k);
            lemma_weight_push(t1, STok::ArrEnd);
            if 0 <= k2 < s.len() && s[k2] == 0x2C && i < k2 + 1 <= s.len() {
                lemma_elements_size(s, k2 + 1, depth, t1);
            }
        }
    }
}

pub proof fn lemma_members_size(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= i <= s.len(),
    ensures
        members(s, i, depth, tape) matches Some((t, n)) ==> weight(t) - weight(tape) <= n - i
            && t.len() - tape.len() <= n - i,
    decreases depth, s.len() - i, 0nat,
{
    lemma_skip_ws_bounds(s, i);
    if depth > 0 {
        let j = skip_ws(s, i);
        if 0 <= j < s.len() && s[j] == 0x22 {
            lemma_string_body_advances(s, j + 1, false);
        }
        if let Some((k, esc)) = string(s, j) {
            lemma_skip_ws_bounds(s, k);
            let c = skip_ws(s, k);
            if 0 <= c < s.len() && s[c] == 0x3A {
                lemma_skip_ws_bounds(s, c + 1);
                let key = STok::Key { start: j + 1, end: k - 1, escaped: esc };
                let tk = tape.push(key);
                lemma_weight_push(tape, key);
                let vs = skip_ws(s, c + 1);
                lemma_value_size(s, vs, (depth - 1) as nat, tk);
                lemma_value_advances(s, vs, (depth - 1) as nat, tk);
                if let Some((t1, m)) = value(s, vs, (depth - 1) as nat, tk) {
                    lemma_skip_ws_bounds(s, m);
                    let m2 = skip_ws(s, m);
                    lemma_weight_push(t1, STok::ObjEnd);
                    if 0 <= m2 < s.len() && s[m2] == 0x2C && i < m2 + 1 <= s.len() {
                        lemma_members_size(s, m2 + 1, depth, t1);
                    }
                }
            }
        }
    }
}

/// The memory bound: a document's tape has at most one token per input
/// byte, and its tokens with the raw bodies of its strings weigh at most
/// the input's length.
pub proof fn lemma_document_size(s: Seq<u8>, require_end: bool)
    ensures
        document(s, require_end) matches Some((t, _)) ==> weight(t) <= s.len() && t.len() <= s.len(),
{
    lemma_document_in_bounds(s, require_end);
    let st = skip_ws(s, bom_end(s));
    lemma_skip_ws_bounds(s, bom_end(s));
    assert(weight(Seq::<STok>::empty()) == 0);
    lemma_value_size(s, st, MAX_DEPTH as nat, Seq::empty());
    lemma_value_advances(s, st, MAX_DEPTH as nat, Seq::empty());
    if let Some((t, _)) = document(s, require_end) {
        lemma_weight_len(t);
    }
}

// ---------------------------------------------------------------------------
// Container links
// ---------------------------------------------------------------------------

/// The start token at `k`, if it is one, links to a later token of `t`
/// that ends a container of its kind.
pub open spec fn linked(t: Seq<STok>, k: int) -> bool {
    match t[k] {
        STok::ArrStart { end } => k < end < t.len() && t[end] is ArrEnd,
        STok::ObjStart { end } => k < end < t.len() && t[end] is ObjEnd,
        _ => true,
    }
}

/// Every start token of `t` from index `a` on is linked.
pub open spec fn links_from(t: Seq<STok>, a: int) -> bool {
    forall|k: int| a <= k < t.len() ==> #[trigger] linked(t, k)
}

/// Links below `t1.len()` survive extending the tape.
proof fn lemma_links_extend(t: Seq<STok>, t1: Seq<STok>, a: int)
    requires
        extends(t, t1),
        links_from(t1, a),
        0 <= a,
    ensures
        forall|k: int| a <= k < t1.len() ==> #[trigger] linked(t, k),
{
    assert forall|k: int| a <= k < t1.len() implies #[trigger] linked(t, k) by {
        assert(linked(t1, k));
        assert(t[k] == t.subrange(0, t1.len() as int)[k]);
        match t1[k] {
            STok::ArrStart { end } => {
                assert(t[end] == t.subrange(0, t1.len() as int)[end]);
            },
            STok::ObjStart { end } => {
                assert(t[end] == t.subrange(0, t1.len() as int)[end]);
            },
            _ => {},
        }
    }
}

proof fn lemma_links_push(t: Seq<STok>, a: int, x: STok)
    requires
        links_from(t, a),
        !(x is ArrStart) && !(x is ObjStart),
        0 <= a <= t.len(),
    ensures
        links_from(t.push(x), a),
{
    lemma_extends_refl_push(t, x);
    lemma_links_extend(t.push(x), t, a);
    assert(linked(t.push(x), t.len() as int));
}

/// An array's tokens end with its `ArrEnd`, an object's with its `ObjEnd`,
/// and every container start among them is linked.
pub proof fn lemma_value_links(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        value(s, i, depth, tape) matches Some((t, _)) ==> links_from(t, tape.len() as int),
    decreases depth, s.len() - i, 2nat,
{
    lemma_value_extends(s, i, depth, tape);
    if 0 <= i < s.len() {
        let c = s[i];
        if (c == 0x5B || c == 0x7B) && depth > 0 {
            let x = if c == 0x5B { STok::ArrStart { end: 0 } } else { STok::ObjStart { end: 0 } };
            let tx = tape.push(x);
            let r = if c == 0x5B { array(s, i + 1, depth, tx) } else { object(s, i + 1, depth, tx) };
            if c == 0x5B {
                lemma_array_links(s, i + 1, depth, tx);
                lemma_array_extends(s, i + 1, depth, tx);
            } else {
                lemma_object_links(s, i + 1, depth, tx);
                lemma_object_extends(s, i + 1, depth, tx);
            }
            if let Some((t1, _)) = r {
                lemma_extends_push(t1, tape, x);
                let k = tape.len() as int;
                let t = close_at(t1, k);
                assert(k < t1.len() - 1);
                assert forall|m: int| k <= m < t.len() implies #[trigger] linked(t, m) by {
                    if m > k {
                        assert(linked(t1, m));
                        assert(t[m] == t1[m]);
                    }
                }
            }
        } else if let Some((t, _)) = value(s, i, depth, tape) {
            assert(t == tape.push(t.last()));
            assert(linked(t, tape.len() as int));
        }
    }
}

pub proof fn lemma_array_links(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        array(s, i, depth, tape) matches Some((t, _)) ==> links_from(t, tape.len() as int) && t.len()
            > tape.len() && t.last() is ArrEnd,
    decreases depth, s.len() - i, 1nat,
{
    assert(links_from(tape, tape.len() as int));
    lemma_links_push(tape, tape.len() as int, STok::ArrEnd);
    lemma_elements_links(s, i, depth, tape);
}

pub proof fn lemma_object_links(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        object(s, i, depth, tape) matches Some((t, _)) ==> links_from(t, tape.len() as int) && t.len()
            > tape.len() && t.last() is ObjEnd,
    decreases depth, s.len() - i, 1nat,
{
    assert(links_from(tape, tape.len() as int));
    lemma_links_push(tape, tape.len() as int, STok::ObjEnd);
    lemma_members_links(s, i, depth, tape);
}

pub proof fn lemma_elements_links(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        elements(s, i, depth, tape) matches Some((t, _)) ==> links_from(t, tape.len() as int) && t.len()
            > tape.len() && t.last() is ArrEnd,
    decreases depth, s.len() - i, 0nat,
{
    if depth > 0 {
        let j = skip_ws(s, i);
        lemma_value_links(s, j, (depth - 1) as nat, tape);
        lemma_value_extends(s, j, (depth - 1) as nat, tape);
        if let Some((t1, k)) = value(s, j, (depth - 1) as nat, tape) {
            let k2 = skip_ws(s, k);
            lemma_links_push(t1, tape.len() as int, STok::ArrEnd);
            if 0 <= k2 < s.len() && s[k2] == 0x2C && i < k2 + 1 <= s.len() {
                lemma_elements_links(s, k2 + 1, depth, t1);
                lemma_elements_extends(s, k2 + 1, depth, t1);
                if let Some((t, _)) = elements(s, k2 + 1, depth, t1) {
                    lemma_links_extend(t, t1, tape.len() as int);
                    assert forall|m: int| tape.len() <= m < t.len() implies #[trigger] linked(t, m) by {
                        if m >= t1.len() {
                            assert(linked(t, m));
                        }
                    }
                }
            }
        }
    }
}

pub proof fn lemma_members_links(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    ensures
        members(s, i, depth, tape) matches Some((t, _)) ==> links_from(t, tape.len() as int) && t.len()
            > tape.len() && t.last() is ObjEnd,
    decreases depth, s.len() - i, 0nat,
{
    if depth > 0 {
        let j = skip_ws(s, i);
        if let Some((k, esc)) = string(s, j) {
            let c = skip_ws(s, k);
            let key = STok::Key { start: j + 1, end: k - 1, escaped: esc };
            let tk = tape.push(key);
            let vs = skip_ws(s, c + 1);
            assert(links_from(tape, tape.len() as int));
            lemma_links_push(tape, tape.len() as int, key);
            lemma_value_links(s, vs, (depth - 1) as nat, tk);
            lemma_value_extends(s, vs, (depth - 1) as nat, tk);
            if let Some((t1, m)) = value(s, vs, (depth - 1) as nat, tk) {
                lemma_links_extend(t1, tk, tape.len() as int);
                assert(links_from(t1, tape.len() as int)) by {
                    assert forall|q: int| tape.len() <= q < t1.len() implies #[trigger] linked(t1, q) by {
                        if q >= tk.len() {
                            assert(linked(t1, q));
                        }
                    }
                }
                let m2 = skip_ws(s, m);
                lemma_links_push(t1, tape.len() as int, STok::ObjEnd);
                if 0 <= m2 < s.len() && s[m2] == 0x2C && i < m2 + 1 <= s.len() {
                    lemma_members_links(s, m2 + 1, depth, t1);
                    lemma_members_extends(s, m2 + 1, depth, t1);
                    if let Some((t, _)) = members(s, m2 + 1, depth, t1) {
                        lemma_links_extend(t, t1, tape.len() as int);
                        assert forall|q: int| tape.len() <= q < t.len() implies #[trigger] linked(t, q) by {
                            if q >= t1.len() {
                                assert(linked(t, q));
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Every container start in a document's tape links to its end.
pub proof fn lemma_document_links(s: Seq<u8>, require_end: bool)
    ensures
        document(s, require_end) matches Some((t, _)) ==> links_from(t, 0),
{
    lemma_value_links(s, skip_ws(s, bom_end(s)), MAX_DEPTH as nat, Seq::empty());
}

} // verus!
