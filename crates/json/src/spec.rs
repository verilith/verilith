//! Executable-free specification of JSON (RFC 8259) parsing.
//!
//! The grammar is written as recursive spec functions over the input bytes.
//! A successful parse produces a *tape*: the pre-order serialization of the
//! JSON tree (open/close markers for arrays and objects, one token per
//! scalar, a `Key` token before every object member's value). Strings and
//! numbers are zero-copy: their tokens hold byte ranges of the input, and
//! `decode` gives the bytes a string range stands for.
//!
//! Every function takes a position `i` and returns the tape extended with the
//! tokens it recognized plus the position just past the recognized text, or
//! `None` if the input does not match the grammar at `i`.
//!
//! Termination is structural: functions either consume input or lower the
//! nesting depth. A few spec functions contain a guard of the form
//! `if !(i < n <= s.len()) { None }` before recursing at the same depth. Those
//! guards make the termination argument purely syntactic; `lemma_*` functions
//! in `lemmas.rs` show they never change the result of a parse.
#[cfg(verus_keep_ghost)]
pub use verilith_core::num::{digits_end, is_digit};
#[cfg(verus_keep_ghost)]
pub use verilith_core::utf8::{byte_in, cont, utf8_encode, utf8_from, utf8_len};
use vstd::prelude::*;

verus! {

global size_of usize == 8;

/// Nesting limit, identical to cJSON's `CJSON_NESTING_LIMIT`.
pub const MAX_DEPTH: usize = 1000;

/// The largest input, 2^48 - 1 bytes (256 TiB): more than a 64-bit address
/// space can hold today, so in effect no limit. Token positions are 48 bits.
pub const MAX_INPUT: usize = 0xFFFF_FFFF_FFFF;

pub enum STok {
    Null,
    True,
    False,
    /// A number, as the byte range `[start, end)` of its lexeme in the input.
    Num { start: int, end: int },
    /// A string value: the raw bytes between the quotes are `[start, end)`,
    /// `escaped` says whether they contain a backslash. The value is
    /// `decode(s, start, end)`.
    Str { start: int, end: int, escaped: bool },
    /// An object member name, represented like `Str`.
    Key { start: int, end: int, escaped: bool },
    /// The start of an array. `end` is the index in the tape of its
    /// `ArrEnd`, so a reader can skip the whole array.
    ArrStart { end: int },
    ArrEnd,
    /// The start of an object, with the index of its `ObjEnd`.
    ObjStart { end: int },
    ObjEnd,
}

// ---------------------------------------------------------------------------
// Lexical helpers
// ---------------------------------------------------------------------------

/// ws = *( %x20 / %x09 / %x0A / %x0D )
pub open spec fn is_ws(c: u8) -> bool {
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D
}

pub open spec fn is_hex(c: u8) -> bool {
    (0x30 <= c <= 0x39) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

pub open spec fn hex_val(c: u8) -> u32 {
    if 0x30 <= c <= 0x39 {
        (c - 0x30) as u32
    } else if 0x41 <= c <= 0x46 {
        (c - 0x41 + 10) as u32
    } else {
        (c - 0x61 + 10) as u32
    }
}

/// Index of the first non-whitespace byte at or after `i`.
pub open spec fn skip_ws(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_ws(s[i]) {
        skip_ws(s, i + 1)
    } else {
        i
    }
}

/// True when `s[i..]` starts with `lit`.
pub open spec fn has_lit(s: Seq<u8>, i: int, lit: Seq<u8>) -> bool {
    0 <= i && i + lit.len() <= s.len() && s.subrange(i, i + lit.len()) == lit
}

// ---------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------

/// number = [ minus ] int [ frac ] [ exp ]
/// int    = zero / ( digit1-9 *DIGIT )
/// frac   = decimal-point 1*DIGIT
/// exp    = e [ minus / plus ] 1*DIGIT
///
/// Returns the end of the number lexeme starting at `i`.
pub open spec fn number_end(s: Seq<u8>, i: int) -> Option<int> {
    let j = if 0 <= i < s.len() && s[i] == 0x2D { i + 1 } else { i };
    if !(0 <= j < s.len() && is_digit(s[j])) {
        None
    } else {
        let k = if s[j] == 0x30 { j + 1 } else { digits_end(s, j) };
        let frac = if 0 <= k < s.len() && s[k] == 0x2E {
            let d = digits_end(s, k + 1);
            if d == k + 1 { None } else { Some(d) }
        } else {
            Some(k)
        };
        match frac {
            None => None,
            Some(k2) => {
                if 0 <= k2 < s.len() && (s[k2] == 0x65 || s[k2] == 0x45) {
                    let m = if k2 + 1 < s.len() && (s[k2 + 1] == 0x2B || s[k2 + 1] == 0x2D) {
                        k2 + 2
                    } else {
                        k2 + 1
                    };
                    let d = digits_end(s, m);
                    if d == m { None } else { Some(d) }
                } else {
                    Some(k2)
                }
            },
        }
    }
}

/// `10^k`.
pub open spec fn p10i(k: nat) -> int
    decreases k,
{
    if k == 0 { 1 } else { 10 * p10i((k - 1) as nat) }
}

/// The value of the decimal digits `s[a..b]`.
pub open spec fn dval(s: Seq<u8>, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a { 0 } else { dval(s, a, b - 1) * 10 + (s[b - 1] as int - 0x30) }
}

/// The end of the integer part starting at `j`.
pub open spec fn int_end(s: Seq<u8>, j: int) -> int {
    if s[j] == 0x30 { j + 1 } else { digits_end(s, j) }
}

/// The significand of the integer and fraction parts starting at `j`, the
/// power of ten from the fraction, and their end.
pub open spec fn sig_value(s: Seq<u8>, j: int) -> (int, int, int) {
    let k = int_end(s, j);
    if 0 <= k < s.len() && s[k] == 0x2E {
        let d = digits_end(s, k + 1);
        (dval(s, j, k) * p10i((d - k - 1) as nat) + dval(s, k + 1, d), -(d - k - 1), d)
    } else {
        (dval(s, j, k), 0, k)
    }
}

/// The start of an exponent's digits after the `e` at `k2`.
pub open spec fn exp_digits(s: Seq<u8>, k2: int) -> int {
    if k2 + 1 < s.len() && (s[k2 + 1] == 0x2B || s[k2 + 1] == 0x2D) { k2 + 2 } else { k2 + 1 }
}

/// The value of the number lexeme at `i` (see `number_end`), as a sign, a
/// significand and a power of ten: `(neg, w, q)` stands for
/// `(-1)^neg * w * 10^q`. The significand is every digit of the integer
/// and fraction parts, read as one integer; the power is the exponent less
/// the number of fraction digits.
pub open spec fn number_value(s: Seq<u8>, i: int) -> (bool, int, int) {
    let neg = 0 <= i < s.len() && s[i] == 0x2D;
    let j = if neg { i + 1 } else { i };
    let (w, q0, k2) = sig_value(s, j);
    if 0 <= k2 < s.len() && (s[k2] == 0x65 || s[k2] == 0x45) {
        let m = exp_digits(s, k2);
        let ev = dval(s, m, digits_end(s, m));
        (neg, w, if s[k2 + 1] == 0x2D { q0 - ev } else { q0 + ev })
    } else {
        (neg, w, q0)
    }
}

// ---------------------------------------------------------------------------
// Strings
// ---------------------------------------------------------------------------

/// The four hex digits at `s[i..i+4]` as a code unit, if they are hex digits.
pub open spec fn hex4(s: Seq<u8>, i: int) -> Option<u32> {
    if 0 <= i && i + 4 <= s.len() && is_hex(s[i]) && is_hex(s[i + 1]) && is_hex(s[i + 2])
        && is_hex(s[i + 3]) {
        Some(
            (((hex_val(s[i]) * 16 + hex_val(s[i + 1])) * 16 + hex_val(s[i + 2])) * 16 + hex_val(
                s[i + 3],
            )) as u32,
        )
    } else {
        None
    }
}

/// Decoded byte for a single-character escape `\c`.
pub open spec fn simple_escape(c: u8) -> Option<u8> {
    if c == 0x22 {
        Some(0x22u8)
    } else if c == 0x5C {
        Some(0x5Cu8)
    } else if c == 0x2F {
        Some(0x2Fu8)
    } else if c == 0x62 {
        Some(0x08u8)
    } else if c == 0x66 {
        Some(0x0Cu8)
    } else if c == 0x6E {
        Some(0x0Au8)
    } else if c == 0x72 {
        Some(0x0Du8)
    } else if c == 0x74 {
        Some(0x09u8)
    } else {
        None
    }
}

/// One `char` of a string body starting at `i`:
///   char = unescaped / escape ( %x22 / %x5C / %x2F / %x62 / %x66 /
///          %x6E / %x72 / %x74 / %x75 4HEXDIG )
/// Returns the decoded bytes and the position after the char.
///
/// `\uXXXX` escapes are decoded to UTF-8. A high surrogate must be followed
/// by `\u` and a low surrogate, and a lone low surrogate is rejected (as in
/// cJSON). Unescaped bytes are passed through unchanged; control characters
/// (< 0x20) are rejected.
pub open spec fn string_char(s: Seq<u8>, i: int) -> Option<(Seq<u8>, int)> {
    if !(0 <= i < s.len()) {
        None
    } else if s[i] == 0x22 || s[i] < 0x20 {
        None
    } else if s[i] != 0x5C {
        Some((seq![s[i]], i + 1))
    } else if !(i + 1 < s.len()) {
        None
    } else if s[i + 1] != 0x75 {
        match simple_escape(s[i + 1]) {
            Some(b) => Some((seq![b], i + 2)),
            None => None,
        }
    } else {
        match hex4(s, i + 2) {
            None => None,
            Some(u) => {
                if 0xDC00 <= u <= 0xDFFF {
                    None
                } else if 0xD800 <= u <= 0xDBFF {
                    if !(i + 7 < s.len() && s[i + 6] == 0x5C && s[i + 7] == 0x75) {
                        None
                    } else {
                        match hex4(s, i + 8) {
                            None => None,
                            Some(lo) => {
                                if 0xDC00 <= lo <= 0xDFFF {
                                    let cp = (0x10000 + (u - 0xD800) * 1024 + (lo - 0xDC00)) as u32;
                                    Some((utf8_encode(cp), i + 12))
                                } else {
                                    None
                                }
                            },
                        }
                    }
                } else {
                    Some((utf8_encode(u), i + 6))
                }
            },
        }
    }
}

/// Validates the rest of a string body from `i` up to and including the
/// closing quote. Returns the position after the closing quote and whether a
/// backslash was seen (`esc` is the flag so far).
pub open spec fn string_body(s: Seq<u8>, i: int, esc: bool) -> Option<(int, bool)>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        None
    } else if s[i] == 0x22 {
        Some((i + 1, esc))
    } else {
        match string_char(s, i) {
            None => None,
            Some((_, n)) => {
                if !(i < n <= s.len()) {
                    None
                } else {
                    string_body(s, n, esc || s[i] == 0x5C)
                }
            },
        }
    }
}

/// string = quotation-mark *char quotation-mark
///
/// Returns the position after the closing quote and whether the body
/// contains an escape.
pub open spec fn string(s: Seq<u8>, i: int) -> Option<(int, bool)> {
    if 0 <= i < s.len() && s[i] == 0x22 {
        string_body(s, i + 1, false)
    } else {
        None
    }
}

/// The bytes that the string body `s[i..end)` stands for: each `char` is
/// replaced by its decoding (see `string_char`).
pub open spec fn decode(s: Seq<u8>, i: int, end: int) -> Seq<u8>
    decreases end - i,
{
    if !(0 <= i < end && end <= s.len()) {
        Seq::empty()
    } else {
        match string_char(s, i) {
            None => Seq::empty(),
            Some((bytes, n)) => {
                if !(i < n <= end) {
                    Seq::empty()
                } else {
                    bytes + decode(s, n, end)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

/// `t` with the container start token at `k` linked to `t`'s last token,
/// which closes that container. While a container is being parsed its
/// start token is `ArrStart { end: 0 }` (or `ObjStart`), and the link is
/// set once its end token is on the tape.
pub open spec fn close_at(t: Seq<STok>, k: int) -> Seq<STok> {
    t.update(
        k,
        match t[k] {
            STok::ObjStart { .. } => STok::ObjStart { end: t.len() - 1 },
            _ => STok::ArrStart { end: t.len() - 1 },
        },
    )
}

/// value = false / null / true / object / array / number / string
///
/// `i` points at the first byte of the value (whitespace already skipped).
/// `depth` is the number of arrays/objects that may still be opened.
pub open spec fn value(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>) -> Option<(Seq<STok>, int)>
    decreases depth, s.len() - i, 2nat,
{
    if !(0 <= i < s.len()) {
        None
    } else {
        let c = s[i];
        if c == 0x5B {
            // '['
            if depth == 0 {
                None
            } else {
                match array(s, i + 1, depth, tape.push(STok::ArrStart { end: 0 })) {
                    Some((t, n)) => Some((close_at(t, tape.len() as int), n)),
                    None => None,
                }
            }
        } else if c == 0x7B {
            // '{'
            if depth == 0 {
                None
            } else {
                match object(s, i + 1, depth, tape.push(STok::ObjStart { end: 0 })) {
                    Some((t, n)) => Some((close_at(t, tape.len() as int), n)),
                    None => None,
                }
            }
        } else if c == 0x22 {
            match string(s, i) {
                Some((n, esc)) => Some((tape.push(STok::Str { start: i + 1, end: n - 1, escaped: esc }), n)),
                None => None,
            }
        } else if c == 0x74 {
            if has_lit(s, i, seq![0x74u8, 0x72, 0x75, 0x65]) {
                Some((tape.push(STok::True), i + 4))
            } else {
                None
            }
        } else if c == 0x66 {
            if has_lit(s, i, seq![0x66u8, 0x61, 0x6C, 0x73, 0x65]) {
                Some((tape.push(STok::False), i + 5))
            } else {
                None
            }
        } else if c == 0x6E {
            if has_lit(s, i, seq![0x6Eu8, 0x75, 0x6C, 0x6C]) {
                Some((tape.push(STok::Null), i + 4))
            } else {
                None
            }
        } else {
            match number_end(s, i) {
                Some(e) => Some((tape.push(STok::Num { start: i, end: e }), e)),
                None => None,
            }
        }
    }
}

/// array = begin-array [ value *( value-separator value ) ] end-array
///
/// `i` is just past the '['.
pub open spec fn array(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>) -> Option<(Seq<STok>, int)>
    decreases depth, s.len() - i, 1nat,
{
    let j = skip_ws(s, i);
    if 0 <= j < s.len() && s[j] == 0x5D {
        Some((tape.push(STok::ArrEnd), j + 1))
    } else {
        elements(s, i, depth, tape)
    }
}

/// `value *( value-separator value ) end-array`, starting at `i`, which is
/// just past a '[' or a ','.
pub open spec fn elements(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>) -> Option<
    (Seq<STok>, int),
>
    decreases depth, s.len() - i, 0nat,
{
    if depth == 0 {
        None
    } else {
        match value(s, skip_ws(s, i), (depth - 1) as nat, tape) {
            None => None,
            Some((t, k)) => {
                let k2 = skip_ws(s, k);
                if !(0 <= k2 < s.len()) {
                    None
                } else if s[k2] == 0x5D {
                    Some((t.push(STok::ArrEnd), k2 + 1))
                } else if s[k2] == 0x2C {
                    if !(i < k2 + 1 <= s.len()) {
                        None
                    } else {
                        elements(s, k2 + 1, depth, t)
                    }
                } else {
                    None
                }
            },
        }
    }
}

/// object = begin-object [ member *( value-separator member ) ] end-object
///
/// `i` is just past the '{'.
pub open spec fn object(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>) -> Option<(Seq<STok>, int)>
    decreases depth, s.len() - i, 1nat,
{
    let j = skip_ws(s, i);
    if 0 <= j < s.len() && s[j] == 0x7D {
        Some((tape.push(STok::ObjEnd), j + 1))
    } else {
        members(s, i, depth, tape)
    }
}

/// `member *( value-separator member ) end-object`, where
/// member = string name-separator value. `i` is just past a '{' or a ','.
pub open spec fn members(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>) -> Option<
    (Seq<STok>, int),
>
    decreases depth, s.len() - i, 0nat,
{
    if depth == 0 {
        None
    } else {
        let j = skip_ws(s, i);
        match string(s, j) {
            None => None,
            Some((k, esc)) => {
                let c = skip_ws(s, k);
                if !(0 <= c < s.len() && s[c] == 0x3A) {
                    None
                } else {
                    match value(
                        s,
                        skip_ws(s, c + 1),
                        (depth - 1) as nat,
                        tape.push(STok::Key { start: j + 1, end: k - 1, escaped: esc }),
                    ) {
                        None => None,
                        Some((t, m)) => {
                            let m2 = skip_ws(s, m);
                            if !(0 <= m2 < s.len()) {
                                None
                            } else if s[m2] == 0x7D {
                                Some((t.push(STok::ObjEnd), m2 + 1))
                            } else if s[m2] == 0x2C {
                                if !(i < m2 + 1 <= s.len()) {
                                    None
                                } else {
                                    members(s, m2 + 1, depth, t)
                                }
                            } else {
                                None
                            }
                        },
                    }
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// UTF-8 (Unicode Table 3-7, well-formed byte sequences): `utf8_from` and
// the sequences it accepts are specified in `verilith_core::utf8`.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Documents
// ---------------------------------------------------------------------------

/// Position of the first byte after an optional UTF-8 byte order mark.
pub open spec fn bom_end(s: Seq<u8>) -> int {
    if has_lit(s, 0, seq![0xEFu8, 0xBB, 0xBF]) { 3 } else { 0 }
}

/// JSON-text = ws value ws, preceded by an optional BOM, and well-formed
/// UTF-8.
///
/// Returns the tape and the end of the value. With `require_end`, only
/// whitespace may follow the value. Without it, any bytes may follow (this is
/// what cJSON_Parse does); the caller decides what to do with them.
///
/// Inputs over `MAX_INPUT` are rejected, so that positions fit in 48 bits.
/// A byte that could continue a number in a lenient reader (strtod).
pub open spec fn num_cont(c: u8) -> bool {
    is_digit(c) || c == 0x2E || c == 0x45 || c == 0x65 || c == 0x2B || c == 0x2D
}

/// Without `require_end`, a number value that is followed directly by a
/// byte that could continue it (`01`, `1.`, `2e`, `1-`) is rejected rather
/// than read as a shorter number followed by other data. A lenient reader
/// would read a different number there.
pub open spec fn cut_number(s: Seq<u8>, require_end: bool, k: int) -> bool {
    !require_end && 0 < k < s.len() && is_digit(s[k - 1]) && num_cont(s[k])
}

pub open spec fn document(s: Seq<u8>, require_end: bool) -> Option<(Seq<STok>, int)> {
    if s.len() > MAX_INPUT {
        None
    } else {
    match value(s, skip_ws(s, bom_end(s)), MAX_DEPTH as nat, Seq::empty()) {
        None => None,
        Some((t, k)) => {
            if require_end && skip_ws(s, k) != s.len() {
                None
            } else if cut_number(s, require_end, k) {
                None
            } else if !utf8_from(s.subrange(0, if require_end { s.len() as int } else { k }), bom_end(s)) {
                // RFC 8259 §8.1: the text must be UTF-8. Without
                // `require_end`, only the bytes up to the end of the value
                // are part of the text.
                None
            } else {
                Some((t, k))
            }
        },
    }
    }
}

} // verus!
