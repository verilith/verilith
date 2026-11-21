//! A model of HTTP/1.1 recipients, for the uniqueness theorems in
//! `unique.rs`.
//!
//! RFC 9112 fixes how a recipient interprets most of a message, but leaves
//! it choices: whether a bare LF ends a line, whether obsolete line
//! folding is unfolded, whether a list of identical Content-Length values
//! is accepted, whether Transfer-Encoding overrides Content-Length, and so
//! on. Each choice is a field of [`Recipient`]. Where the RFC does not say
//! what a message means at all (Transfer-Encoding in HTTP/1.0, transfer
//! codings with parameters), the reading is a free parameter, so the model
//! covers recipients that do anything there.
//!
//! Request smuggling usually needs a parser that breaks the RFC, so the
//! model also covers the deviations behind published smuggling bugs: a
//! bare CR ending a line, whitespace before the colon, folded lines read
//! as field lines of their own, values cut at NUL, `_` read as `-` in
//! names, the first or last of several Content-Length or
//! Transfer-Encoding lines winning, Content-Length parsed like `strtol`,
//! Content-Length winning over Transfer-Encoding, and Transfer-Encoding
//! ignored unless it ends in `chunked`. Each is a field of [`Recipient`]
//! too, and the theorems hold for every combination.
//!
//! The model is written independently of `spec.rs`, in a different style:
//! it splits the head into lines first, as the RFC's prose does, and only
//! then looks inside lines. It is deliberately lenient wherever leniency
//! cannot change what a message means: it does not check that names are
//! tokens, that targets are well formed, or that values hold only allowed
//! bytes. A real recipient is this model plus extra rejections, and
//! rejecting more cannot make two readings of one message disagree.
//!
//! Not covered: recipients that match field names case-sensitively, or
//! that recognize `chunked` only as the whole Transfer-Encoding value.
//! Those disagree with the RFC on ordinary, well-formed messages, so no
//! parser that accepts such messages can agree with them.
//!
//! This file is trusted: read it next to RFC 9112 §2-6.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// How a message body ends.
pub enum Framing {
    /// Exactly this many bytes (0 for no body).
    Length(nat),
    /// The chunked transfer coding.
    Chunked,
    /// At the close of the connection (responses only).
    Close,
}

/// What a recipient makes of a byte string.
pub enum Reading {
    /// A message whose head is `b[..head]`, with this framing.
    Accept { head: int, framing: Framing },
    Reject,
    /// No complete head yet.
    Incomplete,
}

/// A recipient: the choices RFC 9112 leaves open, and the deviations from
/// it seen in deployed parsers.
pub struct Recipient {
    // --- Choices RFC 9112 allows ---
    /// §2.2: "a recipient MAY recognize a single LF as a line terminator
    /// and ignore any preceding CR".
    pub bare_lf: bool,
    /// §2.2: "A recipient of [a bare CR] MUST consider that element to be
    /// invalid or replace each bare CR with SP".
    pub bare_cr_to_sp: bool,
    /// §2.2: a server "SHOULD ignore at least one empty line (CRLF)
    /// received prior to the request-line". At most this many are skipped.
    pub empty_lines: nat,
    /// §3, §4: recipients "MAY instead parse on whitespace-delimited word
    /// boundaries", treating SP, HTAB, VT, FF and bare CR as separators.
    pub ws_start_line: bool,
    /// §2.2: whitespace-preceded lines between the start line and the
    /// first field line are either rejected or ignored.
    pub ignore_ws_lines: bool,
    /// §5.2: obsolete line folding is either rejected or replaced by SP.
    pub unfold: bool,
    /// RFC 9110 §5.5: NUL in a field value is either rejected or replaced
    /// by SP.
    pub nul_to_sp: bool,
    /// §6.3 rule 5: a Content-Length list whose values are all the same
    /// may be accepted as that value.
    pub cl_list: bool,
    /// §6.1, §6.3 rule 3: with both Transfer-Encoding and Content-Length,
    /// a recipient may reject, or use Transfer-Encoding alone.
    pub te_overrides_cl: bool,
    /// §6.1: Transfer-Encoding in HTTP/1.0 means the framing is faulty.
    /// The RFC does not say how to read such a message, so any reading.
    pub http10_te: Option<Framing>,
    /// Transfer codings with parameters or quoted strings: not modelled,
    /// so any reading.
    pub te_params: Option<Framing>,
    // --- Deviations from RFC 9112 seen in deployed parsers ---
    /// A bare CR ends a line (llhttp, CVE-2023-30589).
    pub cr_ends_line: bool,
    /// Whitespace between a field name and the colon is dropped from the
    /// name (§5.1 requires rejection).
    pub ws_before_colon: bool,
    /// A line that starts with whitespace is a field line of its own.
    pub fold_as_line: bool,
    /// A field value ends at the first NUL (C strings).
    pub nul_ends_value: bool,
    /// `_` in a field name matches `-` (CGI-style names).
    pub underscore_dash: bool,
    /// Content-Length is one number, not a list.
    pub cl_whole_value: bool,
    /// Content-Length is read as its leading digits, after optional
    /// whitespace and `+`, ignoring the rest (`strtol`).
    pub cl_prefix: bool,
    /// Of several different Content-Length values: 0 reject (as the RFC
    /// requires), 1 the first wins, 2 the last wins.
    pub cl_pick: nat,
    /// With both Transfer-Encoding and Content-Length, Content-Length is
    /// used (the TE.CL smuggling shape).
    pub cl_wins: bool,
    /// Of several Transfer-Encoding lines: 0 all count (as the RFC
    /// requires), 1 only the first, 2 only the last.
    pub te_lines: nat,
    /// Transfer-Encoding that does not end in `chunked` is ignored, as if
    /// absent.
    pub te_ignored_unless_chunked: bool,
}

// ---------------------------------------------------------------------------
// Lines (§2.2)
// ---------------------------------------------------------------------------

/// The first `x` in `s` at or after `i`, or `s.len()`.
pub open spec fn find(s: Seq<u8>, i: int, x: u8) -> int
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        s.len() as int
    } else if s[i] == x {
        i
    } else {
        find(s, i + 1, x)
    }
}

pub open spec fn has_byte(s: Seq<u8>, x: u8) -> bool {
    exists|k: int| 0 <= k < s.len() && s[k] == x
}

pub open spec fn replace(s: Seq<u8>, x: u8, y: u8) -> Seq<u8> {
    s.map_values(|c: u8| if c == x { y } else { c })
}

/// Whether a line ends at `b[j]`.
pub open spec fn is_eol(b: Seq<u8>, j: int, c: Recipient) -> bool {
    b[j] == LF || (c.cr_ends_line && b[j] == CR && !(j + 1 < b.len() && b[j + 1] == LF))
}

/// The first line end at or after `i`, or `b.len()`.
pub open spec fn find_eol(b: Seq<u8>, i: int, c: Recipient) -> int
    decreases b.len() - i,
{
    if i < 0 || i >= b.len() {
        b.len() as int
    } else if is_eol(b, i, c) {
        i
    } else {
        find_eol(b, i + 1, c)
    }
}

/// The line at `i`: its content without the line terminator, and where the
/// next line starts.
pub open spec fn read_line(b: Seq<u8>, i: int, c: Recipient) -> Parsed<Seq<u8>> {
    let j = find_eol(b, i, c);
    if i < 0 || j >= b.len() {
        Parsed::Partial
    } else {
        let line = if b[j] == CR {
            Some(b.subrange(i, j))  // a bare CR ends the line

        } else if j > i && b[j - 1] == CR {
            Some(b.subrange(i, j - 1))
        } else if c.bare_lf {
            Some(b.subrange(i, j))
        } else {
            None
        };
        match line {
            None => Parsed::Invalid,
            Some(l) => if !has_byte(l, CR) {
                Parsed::Done(l, j + 1)
            } else if c.bare_cr_to_sp {
                Parsed::Done(replace(l, CR, SP), j + 1)
            } else {
                Parsed::Invalid
            },
        }
    }
}

/// The lines from `i` up to the first empty one, and where the head ends
/// (just past the empty line).
pub open spec fn read_lines(b: Seq<u8>, i: int, c: Recipient) -> Parsed<Seq<Seq<u8>>>
    decreases b.len() - i,
{
    match read_line(b, i, c) {
        Parsed::Done(l, n) => if l.len() == 0 {
            Parsed::Done(Seq::empty(), n)
        } else if n <= i {
            Parsed::Invalid  // unreachable: a line is never empty

        } else {
            match read_lines(b, n, c) {
                Parsed::Done(ls, e) => Parsed::Done(seq![l] + ls, e),
                other => other,
            }
        },
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

/// Skips up to `k` empty lines at `i`; the value is where the start line
/// begins.
pub open spec fn skip_empty(b: Seq<u8>, i: int, c: Recipient, k: nat) -> Parsed<()>
    decreases k,
{
    match read_line(b, i, c) {
        Parsed::Done(l, n) => if l.len() == 0 && k > 0 {
            skip_empty(b, n, c, (k - 1) as nat)
        } else {
            Parsed::Done((), i)
        },
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

// ---------------------------------------------------------------------------
// Start lines (§3, §4)
// ---------------------------------------------------------------------------

/// A separator in the start line.
pub open spec fn is_sep(c: Recipient, x: u8) -> bool {
    x == SP || (c.ws_start_line && (x == HTAB || x == 0x0B || x == 0x0C))
}

/// `s` without trailing separators.
pub open spec fn rtrim_sep(s: Seq<u8>, c: Recipient) -> Seq<u8>
    decreases s.len(),
{
    if s.len() > 0 && is_sep(c, s.last()) {
        rtrim_sep(s.drop_last(), c)
    } else {
        s
    }
}

/// The last separator in `s[..k]`, or -1.
pub open spec fn last_sep(s: Seq<u8>, k: int, c: Recipient) -> int
    decreases k,
{
    if k <= 0 || k > s.len() {
        -1
    } else if is_sep(c, s[k - 1]) {
        k - 1
    } else {
        last_sep(s, k - 1, c)
    }
}

/// `HTTP-version = "HTTP/" DIGIT "." DIGIT` with major version 1: the
/// minor version. Another major version is rejected (§2.6: a server
/// answers 505).
pub open spec fn version_word(w: Seq<u8>) -> Option<u8> {
    if w.len() == 8 && w.subrange(0, 7) == http1_prefix() && is_digit(w[7]) {
        Some((w[7] - 0x30) as u8)
    } else {
        None
    }
}

/// `request-line = method SP request-target SP HTTP-version`: the minor
/// version, the last word. Only the version affects framing, so the model
/// asks no more of the method and target than that something precedes the
/// version.
pub open spec fn request_version(l: Seq<u8>, c: Recipient) -> Option<u8> {
    let t = if c.ws_start_line {
        rtrim_sep(l, c)
    } else {
        l
    };
    let k = last_sep(t, t.len() as int, c);
    if k < 0 || rtrim_sep(t.subrange(0, k), c).len() == 0 {
        None
    } else {
        version_word(t.subrange(k + 1, t.len() as int))
    }
}

/// `status-line = HTTP-version SP status-code SP [ reason-phrase ]`: the
/// minor version and the status code. Recipients that omit the second SP
/// before an empty reason phrase are covered too.
pub open spec fn status_line(l: Seq<u8>, c: Recipient) -> Option<(u8, nat)> {
    if l.len() < 12 || !is_sep(c, l[8]) {
        None
    } else {
        match version_word(l.subrange(0, 8)) {
            None => None,
            Some(minor) => {
                let p = if c.ws_start_line {
                    skip_sep(l, 9, c)
                } else {
                    9
                };
                if p + 3 <= l.len() && is_digit(l[p]) && is_digit(l[p + 1]) && is_digit(l[p + 2])
                    && (p + 3 == l.len() || is_sep(c, l[p + 3])) {
                    Some((minor, decimal(l.subrange(p, p + 3))))
                } else {
                    None
                }
            },
        }
    }
}

pub open spec fn skip_sep(s: Seq<u8>, i: int, c: Recipient) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_sep(c, s[i]) {
        skip_sep(s, i + 1, c)
    } else {
        i
    }
}

// ---------------------------------------------------------------------------
// Field lines (§5)
// ---------------------------------------------------------------------------

/// A field: name and value.
pub struct Field {
    pub name: Seq<u8>,
    pub value: Seq<u8>,
}

pub open spec fn ltrim(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() > 0 && is_ows(s[0]) {
        ltrim(s.drop_first())
    } else {
        s
    }
}

pub open spec fn rtrim(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() > 0 && is_ows(s.last()) {
        rtrim(s.drop_last())
    } else {
        s
    }
}

/// `s` without leading and trailing OWS.
pub open spec fn trim(s: Seq<u8>) -> Seq<u8> {
    rtrim(ltrim(s))
}

/// The field lines `ls[i..]` after the start line, with lines that begin
/// with whitespace handled as §2.2 and §5.2 allow: before the first field
/// line they are ignored or rejected; after it they continue the previous
/// line (obsolete line folding) or are rejected. A deviating recipient
/// takes them as field lines of their own. `acc` holds the lines so far.
pub open spec fn unfold(ls: Seq<Seq<u8>>, i: int, c: Recipient, acc: Seq<Seq<u8>>) -> Option<
    Seq<Seq<u8>>,
>
    decreases ls.len() - i,
{
    if i < 0 || i >= ls.len() {
        Some(acc)
    } else if ls[i].len() > 0 && is_ows(ls[i][0]) {
        if c.fold_as_line {
            unfold(ls, i + 1, c, acc.push(ltrim(ls[i])))
        } else if acc.len() == 0 {
            if c.ignore_ws_lines {
                unfold(ls, i + 1, c, acc)
            } else {
                None
            }
        } else if c.unfold {
            unfold(ls, i + 1, c, acc.drop_last().push(acc.last() + seq![SP] + ls[i]))
        } else {
            None
        }
    } else {
        unfold(ls, i + 1, c, acc.push(ls[i]))
    }
}

/// `field-line = field-name ":" OWS field-value OWS`. §5.1: "No whitespace
/// is allowed between the field name and colon ... a server MUST reject".
pub open spec fn field(l: Seq<u8>, c: Recipient) -> Option<Field> {
    let k = find(l, 0, COLON);
    if k >= l.len() || k == 0 || (is_ows(l[k - 1]) && !c.ws_before_colon) {
        None
    } else {
        let name = rtrim(l.subrange(0, k));
        let raw = l.subrange(k + 1, l.len() as int);
        let v = trim(
            if c.nul_ends_value {
                raw.subrange(0, find(raw, 0, 0))
            } else {
                raw
            },
        );
        if name.len() == 0 {
            None
        } else if !has_byte(v, 0) {
            Some(Field { name, value: v })
        } else if c.nul_to_sp {
            Some(Field { name, value: replace(v, 0, SP) })
        } else {
            None
        }
    }
}

pub open spec fn fields(ls: Seq<Seq<u8>>, c: Recipient) -> Option<Seq<Field>>
    decreases ls.len(),
{
    if ls.len() == 0 {
        Some(Seq::empty())
    } else {
        match (fields(ls.drop_last(), c), field(ls.last(), c)) {
            (Some(fs), Some(f)) => Some(fs.push(f)),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Framing (§6)
// ---------------------------------------------------------------------------

/// The elements of the comma-separated list `v[i..]` (RFC 9110 §5.6.1),
/// trimmed, with empty elements dropped.
pub open spec fn elements(v: Seq<u8>, i: int) -> Seq<Seq<u8>>
    decreases v.len() - i,
{
    if i < 0 || i > v.len() {
        Seq::empty()
    } else {
        let k = find(v, i, COMMA);
        let e = trim(v.subrange(i, k));
        let rest = if k < i || k >= v.len() {
            Seq::empty()
        } else {
            elements(v, k + 1)
        };
        if e.len() == 0 {
            rest
        } else {
            seq![e] + rest
        }
    }
}

/// Whether `f` is named `lit` (given in lowercase).
pub open spec fn named(f: Field, lit: Seq<u8>, c: Recipient) -> bool {
    ci_eq(f.name, lit) || (c.underscore_dash && ci_eq_dash(f.name, lit))
}

/// The values of the fields named `lit`, in order.
pub open spec fn values(fs: Seq<Field>, lit: Seq<u8>, c: Recipient) -> Seq<Seq<u8>>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else if named(fs.last(), lit, c) {
        values(fs.drop_last(), lit, c).push(fs.last().value)
    } else {
        values(fs.drop_last(), lit, c)
    }
}

/// The elements of all the lists `vs`, in order.
pub open spec fn list_all(vs: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases vs.len(),
{
    if vs.len() == 0 {
        Seq::empty()
    } else {
        list_all(vs.drop_last()) + elements(vs.last(), 0)
    }
}

pub open spec fn te_values(fs: Seq<Field>, c: Recipient) -> Seq<Seq<u8>> {
    values(fs, name_transfer_encoding(), c)
}

pub open spec fn cl_values(fs: Seq<Field>, c: Recipient) -> Seq<Seq<u8>> {
    values(fs, name_content_length(), c)
}

/// The transfer codings, in order: from every Transfer-Encoding line, or
/// a deviating recipient's first or last.
pub open spec fn codings(fs: Seq<Field>, c: Recipient) -> Seq<Seq<u8>> {
    let vs = te_values(fs, c);
    list_all(
        if vs.len() == 0 {
            vs
        } else if c.te_lines == 1 {
            seq![vs[0]]
        } else if c.te_lines == 2 {
            seq![vs.last()]
        } else {
            vs
        },
    )
}

/// A Transfer-Encoding value with parameters or quoted strings.
pub open spec fn te_params(fs: Seq<Field>, c: Recipient) -> bool {
    exists|k: int|
        0 <= k < te_values(fs, c).len() && (has_byte(te_values(fs, c)[k], 0x3B) || has_byte(
            te_values(fs, c)[k],
            0x22,
        ))
}

pub open spec fn all_digits(s: Seq<u8>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_digit(#[trigger] s[i])
}

/// The number of leading digits of `s[i..]`.
pub open spec fn digits_end(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_digit(s[i]) {
        digits_end(s, i + 1)
    } else {
        i
    }
}

/// A Content-Length value: `1*DIGIT`, or for a deviating recipient its
/// leading digits.
pub open spec fn cl_number(x: Seq<u8>, c: Recipient) -> Option<nat> {
    if all_digits(x) {
        Some(decimal(x))
    } else if c.cl_prefix {
        let t = ltrim(x);
        let t2 = if t.len() > 0 && t[0] == 0x2B {
            t.drop_first()
        } else {
            t
        };
        let k = digits_end(t2, 0);
        if k == 0 {
            None
        } else {
            Some(decimal(t2.subrange(0, k)))
        }
    } else {
        None
    }
}

/// §6.3 rule 5 and RFC 9110 §8.6: every value valid, all equal, and more
/// than one only if the recipient accepts lists (or, deviating, picks one).
pub open spec fn content_length(fs: Seq<Field>, c: Recipient) -> Option<Framing> {
    let vs = cl_values(fs, c);
    let items = if c.cl_whole_value {
        vs
    } else {
        list_all(vs)
    };
    if items.len() == 0 {
        None
    } else if exists|i: int| 0 <= i < items.len() && cl_number(#[trigger] items[i], c) is None {
        None
    } else if forall|i: int| 0 <= i < items.len() ==> cl_number(#[trigger] items[i], c) == cl_number(items[0], c) {
        if items.len() > 1 && !c.cl_list && c.cl_pick == 0 {
            None
        } else {
            Some(Framing::Length(cl_number(items[0], c)->Some_0))
        }
    } else if c.cl_pick == 1 {
        Some(Framing::Length(cl_number(items[0], c)->Some_0))
    } else if c.cl_pick == 2 {
        Some(Framing::Length(cl_number(items.last(), c)->Some_0))
    } else {
        None
    }
}

/// §6.1 and §6.3 rules 3 and 4 for a message with Transfer-Encoding.
/// `otherwise` is the reading when `chunked` is not the final coding
/// (rejection for a request, reading until close for a response), and
/// `absent` the reading without Transfer-Encoding or Content-Length.
pub open spec fn te_framing(
    fs: Seq<Field>,
    minor: u8,
    c: Recipient,
    otherwise: Option<Framing>,
    absent: Option<Framing>,
) -> Option<Framing> {
    let has_cl = cl_values(fs, c).len() > 0;
    let cs = codings(fs, c);
    if minor == 0 {
        c.http10_te
    } else if has_cl && c.cl_wins {
        content_length(fs, c)
    } else if has_cl && !c.te_overrides_cl {
        None
    } else if te_params(fs, c) {
        c.te_params
    } else if cs.len() > 0 && ci_eq(cs.last(), coding_chunked()) {
        Some(Framing::Chunked)
    } else if c.te_ignored_unless_chunked {
        if has_cl {
            content_length(fs, c)
        } else {
            absent
        }
    } else {
        otherwise
    }
}

/// §6.3 for a request.
pub open spec fn request_framing_rfc(fs: Seq<Field>, minor: u8, c: Recipient) -> Option<Framing> {
    if te_values(fs, c).len() > 0 {
        te_framing(fs, minor, c, None, Some(Framing::Length(0)))
    } else if cl_values(fs, c).len() > 0 {
        content_length(fs, c)
    } else {
        Some(Framing::Length(0))
    }
}

/// §6.3 for a response to a request that was HEAD (`head`) or CONNECT
/// (`connect`).
pub open spec fn response_framing_rfc(
    fs: Seq<Field>,
    minor: u8,
    status: nat,
    head: bool,
    connect: bool,
    c: Recipient,
) -> Option<Framing> {
    if head || (100 <= status <= 199) || status == 204 || status == 304 || (connect && 200 <= status
        <= 299) {
        Some(Framing::Length(0))
    } else if te_values(fs, c).len() > 0 {
        te_framing(fs, minor, c, Some(Framing::Close), Some(Framing::Close))
    } else if cl_values(fs, c).len() > 0 {
        content_length(fs, c)
    } else {
        Some(Framing::Close)
    }
}

// ---------------------------------------------------------------------------
// Messages
// ---------------------------------------------------------------------------

/// The head at `s`: the start line, and the field lines unfolded and
/// split.
pub open spec fn head_at(b: Seq<u8>, s: int, c: Recipient) -> Parsed<(Seq<u8>, Seq<Field>)> {
    match read_lines(b, s, c) {
        Parsed::Done(ls, end) => if ls.len() == 0 {
            Parsed::Invalid
        } else {
            match unfold(ls, 1, c, Seq::empty()) {
                None => Parsed::Invalid,
                Some(us) => match fields(us, c) {
                    None => Parsed::Invalid,
                    Some(fs) => Parsed::Done((ls[0], fs), end),
                },
            }
        },
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

/// The head of `b`, after skipped empty lines.
pub open spec fn head(b: Seq<u8>, c: Recipient) -> Parsed<(Seq<u8>, Seq<Field>)> {
    match skip_empty(b, 0, c, c.empty_lines) {
        Parsed::Done(_, s) => head_at(b, s, c),
        Parsed::Partial => Parsed::Partial,
        Parsed::Invalid => Parsed::Invalid,
    }
}

pub open spec fn reading(end: int, f: Option<Framing>) -> Reading {
    match f {
        Some(framing) => Reading::Accept { head: end, framing },
        None => Reading::Reject,
    }
}

/// How recipient `c` reads `b` as a request.
pub open spec fn read_request(b: Seq<u8>, c: Recipient) -> Reading {
    match head(b, c) {
        Parsed::Done((start, fs), end) => match request_version(start, c) {
            None => Reading::Reject,
            Some(minor) => reading(end, request_framing_rfc(fs, minor, c)),
        },
        Parsed::Partial => Reading::Incomplete,
        Parsed::Invalid => Reading::Reject,
    }
}

/// How recipient `c` reads `b` as a response to a HEAD request (`head`),
/// a CONNECT request (`connect`), or another request.
pub open spec fn read_response(b: Seq<u8>, head_req: bool, connect: bool, c: Recipient) -> Reading {
    match head(b, c) {
        Parsed::Done((start, fs), end) => match status_line(start, c) {
            None => Reading::Reject,
            Some((minor, status)) => reading(
                end,
                response_framing_rfc(fs, minor, status, head_req, connect, c),
            ),
        },
        Parsed::Partial => Reading::Incomplete,
        Parsed::Invalid => Reading::Reject,
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// Chunked bodies (§7.1)
// ---------------------------------------------------------------------------

/// How a recipient reads a chunked body. Line endings follow `line`; the
/// rest are deviations from RFC 9112 seen in deployed parsers.
pub struct ChunkReader {
    pub line: Recipient,
    /// Whatever follows the chunk size on its line is ignored, not only
    /// well-formed chunk extensions.
    pub ext_any: bool,
    /// Whitespace before the chunk size is skipped.
    pub size_leading_ws: bool,
    /// A chunk-size line ends only at CR LF; a bare LF in it belongs to
    /// the extension (one side of the 2025 "funky chunks" attacks).
    pub size_line_crlf_only: bool,
    /// The two bytes after chunk data are skipped without checking that
    /// they are CR LF (h11, CVE-2025-43859).
    pub data_end_unchecked: bool,
}

/// What a recipient makes of a chunked body.
pub enum ChunkReading {
    /// The body ends at `end`, and decodes to `body`.
    Done { end: int, body: Seq<u8> },
    Reject,
    Incomplete,
}

/// `HEXDIG`, either case.
pub open spec fn hexdig(c: u8) -> bool {
    (0x30 <= c <= 0x39) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

pub open spec fn hexdig_value(c: u8) -> nat {
    if 0x30 <= c <= 0x39 {
        (c - 0x30) as nat
    } else if 0x41 <= c <= 0x46 {
        (c - 0x41 + 10) as nat
    } else {
        (c - 0x61 + 10) as nat
    }
}

/// The value of the hex digits `s`.
pub open spec fn hex_value(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        hex_value(s.drop_last()) * 16 + hexdig_value(s.last())
    }
}

/// The end of the hex digits at `s[i..]`.
pub open spec fn hex_end(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && hexdig(s[i]) {
        hex_end(s, i + 1)
    } else {
        i
    }
}

/// The first CR LF at or after `i` (the CR's index), or `b.len()`.
pub open spec fn find_crlf(b: Seq<u8>, i: int) -> int
    decreases b.len() - i,
{
    if i < 0 || i + 1 >= b.len() {
        b.len() as int
    } else if b[i] == CR && b[i + 1] == LF {
        i
    } else {
        find_crlf(b, i + 1)
    }
}

pub open spec fn read_size_line(b: Seq<u8>, i: int, c: ChunkReader) -> Parsed<Seq<u8>> {
    if c.size_line_crlf_only {
        let j = find_crlf(b, i);
        if i < 0 || j >= b.len() {
            Parsed::Partial
        } else {
            Parsed::Done(b.subrange(i, j), j + 2)
        }
    } else {
        read_line(b, i, c.line)
    }
}

/// `chunk-size [ chunk-ext ]`: the chunk size. Extensions are ignored, as
/// §7.1.1 requires of unrecognized ones; only their start is checked.
pub open spec fn chunk_size(l: Seq<u8>, c: ChunkReader) -> Option<nat> {
    let t = if c.size_leading_ws {
        ltrim(l)
    } else {
        l
    };
    let k = hex_end(t, 0);
    let rest = ltrim(t.subrange(k, t.len() as int));
    if k == 0 {
        None
    } else if rest.len() == 0 || c.ext_any || rest[0] == 0x3B {
        Some(hex_value(t.subrange(0, k)))
    } else {
        None
    }
}

/// The CRLF after chunk data at `d`: where the next chunk starts.
pub open spec fn data_end(b: Seq<u8>, d: int, c: ChunkReader) -> Parsed<()> {
    if c.data_end_unchecked {
        if d + 2 > b.len() {
            Parsed::Partial
        } else {
            Parsed::Done((), d + 2)
        }
    } else {
        match read_line(b, d, c.line) {
            Parsed::Done(l, m) => if l.len() == 0 {
                Parsed::Done((), m)
            } else {
                Parsed::Invalid
            },
            Parsed::Partial => Parsed::Partial,
            Parsed::Invalid => Parsed::Invalid,
        }
    }
}

/// `chunked-body = *chunk last-chunk trailer-section CRLF` at `i`.
pub open spec fn read_chunks(b: Seq<u8>, i: int, c: ChunkReader) -> ChunkReading
    decreases b.len() - i,
{
    match read_size_line(b, i, c) {
        Parsed::Partial => ChunkReading::Incomplete,
        Parsed::Invalid => ChunkReading::Reject,
        Parsed::Done(l, n) => match chunk_size(l, c) {
            None => ChunkReading::Reject,
            Some(size) => if size == 0 {
                // The trailer section: field lines up to an empty line.
                match read_lines(b, n, c.line) {
                    Parsed::Done(_, e) => ChunkReading::Done { end: e, body: Seq::empty() },
                    Parsed::Partial => ChunkReading::Incomplete,
                    Parsed::Invalid => ChunkReading::Reject,
                }
            } else if n + size > b.len() {
                ChunkReading::Incomplete
            } else {
                match data_end(b, n + size, c) {
                    Parsed::Done(_, m) => if m <= i {
                        ChunkReading::Reject  // unreachable

                    } else {
                        match read_chunks(b, m, c) {
                            ChunkReading::Done { end, body } => ChunkReading::Done {
                                end,
                                body: b.subrange(n, n + size) + body,
                            },
                            other => other,
                        }
                    },
                    Parsed::Partial => ChunkReading::Incomplete,
                    Parsed::Invalid => ChunkReading::Reject,
                }
            },
        },
    }
}

} // verus!
