//! The on-demand reader's protocol, against the tape.
//!
//! `ondemand.rs` proves each cursor operation against the grammar at the
//! cursor. This module proves the step from there to whole documents: what
//! `Reader` remembers between calls (a value, a key, or a separator is
//! next) together with the containers it is in is enough to finish reading
//! the document the way the grammar does, and so the way the tape does.
//!
//! The grammar in `spec.rs` is recursive: `value` calls `array`, which
//! calls `elements`, which calls `value`. A reader stops in the middle of
//! that recursion between two calls, so the place it stands is described
//! here as a continuation: what is left of the innermost container
//! (`rest`), then of each container around it, innermost first
//! (`unwind`), then the check that only whitespace follows the document.
//! `finish` puts the two together. The reader keeps, as ghost state, the
//! open containers (`Frame`) and the tape of everything before the cursor,
//! and its invariant is that `finish` from there is the document's tape.
//! The `lemma_*_step` lemmas say that each move the reader makes leaves
//! `finish` unchanged, and `lemma_finish_keeps` that what is already on the
//! tape stays there, so each token the reader reads is the tape's token at
//! the same index.
#[allow(unused_imports)]
use crate::index::*;
use crate::lemmas::*;
use crate::ondemand::*;
use crate::spec::*;
use crate::stage2::*;
#[allow(unused_imports)]
use crate::simd::*;
use vstd::prelude::*;

verus! {

/// What the reader expects next: a value.
pub const VALUE: u8 = 0;

/// What the reader expects next: a separator or closing bracket, after a
/// value.
pub const AFTER: u8 = 1;

/// What the reader expects next: the first element or key of the
/// container just opened, or its closing bracket.
pub const START: u8 = 2;

/// What the reader expects next: an object member's key.
pub const KEY: u8 = 3;

/// An open container: whether it is an object, the nesting depth the
/// grammar's `elements` or `members` runs at in it, and the index on the
/// tape of its start token.
pub struct Frame {
    pub obj: bool,
    pub depth: nat,
    pub start: int,
}

/// The token that closes an object or an array.
pub open spec fn end_tok(obj: bool) -> STok {
    if obj {
        STok::ObjEnd
    } else {
        STok::ArrEnd
    }
}

/// The byte that closes an object or an array.
pub open spec fn close_byte(obj: bool) -> u8 {
    if obj {
        0x7D
    } else {
        0x5D
    }
}

/// The rest of the container `f` after one of its values (or members)
/// ended at `k`, with tape `t`: its tape and where it ends.
pub open spec fn after(s: Seq<u8>, k: int, f: Frame, t: Seq<STok>) -> Option<(Seq<STok>, int)> {
    let k2 = skip_ws(s, k);
    if !(0 <= k2 < s.len()) {
        None
    } else if s[k2] == close_byte(f.obj) {
        Some((t.push(end_tok(f.obj)), k2 + 1))
    } else if s[k2] == 0x2C {
        if f.obj {
            members(s, k2 + 1, f.depth, t)
        } else {
            elements(s, k2 + 1, f.depth, t)
        }
    } else {
        None
    }
}

/// The rest of the innermost container `f`, read from `p` by a reader
/// that expects `w` next.
pub open spec fn rest(s: Seq<u8>, w: u8, p: int, f: Frame, t: Seq<STok>) -> Option<(Seq<STok>, int)> {
    if w == START {
        if f.obj {
            object(s, p, f.depth, t)
        } else {
            array(s, p, f.depth, t)
        }
    } else if w == KEY {
        if f.obj {
            members(s, p, f.depth, t)
        } else {
            None
        }
    } else if w == VALUE {
        match value(s, skip_ws(s, p), (f.depth - 1) as nat, t) {
            Some((t1, k)) => after(s, k, f, t1),
            None => None,
        }
    } else if w == AFTER {
        after(s, p, f, t)
    } else {
        None
    }
}

/// Given the tape and end `r` of the innermost container of `fs` (or, with
/// no container open, of the document's value), the rest of the
/// document's tape: each container is linked and the one around it read
/// on, and at the top only whitespace may follow.
pub open spec fn unwind(s: Seq<u8>, fs: Seq<Frame>, r: Option<(Seq<STok>, int)>) -> Option<Seq<STok>>
    decreases fs.len(),
{
    match r {
        None => None,
        Some((t, n)) => {
            if fs.len() == 0 {
                if skip_ws(s, n) == s.len() {
                    Some(t)
                } else {
                    None
                }
            } else {
                let up = fs.drop_last();
                let t1 = close_at(t, fs.last().start);
                unwind(
                    s,
                    up,
                    if up.len() == 0 {
                        Some((t1, n))
                    } else {
                        after(s, n, up.last(), t1)
                    },
                )
            }
        },
    }
}

/// The start tokens' indices of the containers `fs`.
pub open spec fn starts(fs: Seq<Frame>) -> Seq<int> {
    Seq::new(fs.len(), |a: int| fs[a].start)
}

pub proof fn lemma_starts(fs: Seq<Frame>, f: Frame)
    ensures
        starts(fs.push(f)) == starts(fs).push(f.start),
        fs.len() > 0 ==> starts(fs.drop_last()) == starts(fs).drop_last(),
        fs.len() > 0 ==> starts(fs).last() == fs.last().start,
        starts(fs).len() == fs.len(),
{
    assert(starts(fs.push(f)) =~= starts(fs).push(f.start));
    if fs.len() > 0 {
        assert(starts(fs.drop_last()) =~= starts(fs).drop_last());
    }
}

/// The depth a value is read at inside the containers `fs`.
pub open spec fn vdepth(fs: Seq<Frame>) -> nat {
    if fs.len() == 0 {
        MAX_DEPTH as nat
    } else {
        (fs.last().depth - 1) as nat
    }
}

/// The tape of the whole document, as a reader at `p` that expects `w`,
/// inside the containers `fs` and with tape `t` so far, would finish it
/// (a `JSON-text` with only whitespace after the value).
pub open spec fn finish(s: Seq<u8>, fs: Seq<Frame>, w: u8, p: int, t: Seq<STok>) -> Option<Seq<STok>> {
    if fs.len() == 0 {
        if w == VALUE {
            unwind(s, fs, value(s, skip_ws(s, p), MAX_DEPTH as nat, t))
        } else if w == AFTER {
            unwind(s, fs, Some((t, p)))
        } else {
            None
        }
    } else {
        unwind(s, fs, rest(s, w, p, fs.last(), t))
    }
}

/// The containers' start tokens are on the tape, in order, each of its
/// container's kind.
pub open spec fn frames_ok(fs: Seq<Frame>, t: Seq<STok>) -> bool {
    &&& forall|a: int, b: int| 0 <= a < b < fs.len() ==> #[trigger] fs[a].start < #[trigger] fs[b].start
    &&& forall|a: int| 0 <= a < fs.len() ==> 0 <= #[trigger] fs[a].start < t.len()
    &&& forall|a: int|
        0 <= a < fs.len() ==> if #[trigger] fs[a].obj {
            t[fs[a].start] is ObjStart
        } else {
            t[fs[a].start] is ArrStart
        }
}

// ---------------------------------------------------------------------------
// Reading the tape
// ---------------------------------------------------------------------------

/// The index on the tape `t` just after the value whose first token is at
/// `i`: past the end token a start token links to, or past a scalar.
pub open spec fn next_val(t: Seq<STok>, i: int) -> int {
    match t[i] {
        STok::ArrStart { end } => end + 1,
        STok::ObjStart { end } => end + 1,
        _ => i + 1,
    }
}

/// The index of the end token a start token links to.
pub open spec fn link(x: STok) -> int {
    match x {
        STok::ArrStart { end } => end,
        STok::ObjStart { end } => end,
        _ => 0,
    }
}

/// The bytes a key token stands for: its body, decoded if it has escapes.
pub open spec fn key_bytes(s: Seq<u8>, x: STok) -> Seq<u8> {
    match x {
        STok::Key { start, end, escaped } => if escaped {
            decode(s, start, end)
        } else {
            s.subrange(start, end)
        },
        _ => Seq::empty(),
    }
}

// ---------------------------------------------------------------------------
// Tapes only grow
// ---------------------------------------------------------------------------

pub proof fn lemma_ext_at(t: Seq<STok>, t0: Seq<STok>, m: int)
    requires
        extends(t, t0),
        0 <= m < t0.len(),
    ensures
        t[m] == t0[m],
{
    assert(t.subrange(0, t0.len() as int)[m] == t[m]);
}

pub proof fn lemma_ext_push(t: Seq<STok>, x: STok)
    ensures
        extends(t.push(x), t),
        t.push(x)[t.len() as int] == x,
{
    assert(t.push(x).subrange(0, t.len() as int) =~= t);
}

pub proof fn lemma_ext_trans(a: Seq<STok>, b: Seq<STok>, c: Seq<STok>)
    requires
        extends(a, b),
        extends(b, c),
    ensures
        extends(a, c),
{
    assert(a.subrange(0, c.len() as int) =~= a.subrange(0, b.len() as int).subrange(0, c.len() as int));
}

pub proof fn lemma_frames_extend(fs: Seq<Frame>, t: Seq<STok>, t1: Seq<STok>)
    requires
        frames_ok(fs, t),
        extends(t1, t),
    ensures
        frames_ok(fs, t1),
{
    assert forall|a: int| 0 <= a < fs.len() implies t1[#[trigger] fs[a].start] == t[fs[a].start] by {
        lemma_ext_at(t1, t, fs[a].start);
    }
    assert forall|a: int| 0 <= a < fs.len() implies if #[trigger] fs[a].obj {
        t1[fs[a].start] is ObjStart
    } else {
        t1[fs[a].start] is ArrStart
    } by {
        lemma_ext_at(t1, t, fs[a].start);
    }
}

pub proof fn lemma_after_extends(s: Seq<u8>, k: int, f: Frame, t: Seq<STok>)
    ensures
        after(s, k, f, t) matches Some((t2, _)) ==> extends(t2, t),
{
    let k2 = skip_ws(s, k);
    if 0 <= k2 < s.len() {
        if s[k2] == close_byte(f.obj) {
            lemma_ext_push(t, end_tok(f.obj));
        } else if s[k2] == 0x2C {
            if f.obj {
                lemma_members_extends(s, k2 + 1, f.depth, t);
            } else {
                lemma_elements_extends(s, k2 + 1, f.depth, t);
            }
        }
    }
}

pub proof fn lemma_rest_extends(s: Seq<u8>, w: u8, p: int, f: Frame, t: Seq<STok>)
    ensures
        rest(s, w, p, f, t) matches Some((t2, _)) ==> extends(t2, t),
{
    if w == START {
        if f.obj {
            lemma_object_extends(s, p, f.depth, t);
        } else {
            lemma_array_extends(s, p, f.depth, t);
        }
    } else if w == KEY {
        if f.obj {
            lemma_members_extends(s, p, f.depth, t);
        }
    } else if w == VALUE {
        lemma_value_extends(s, skip_ws(s, p), (f.depth - 1) as nat, t);
        if let Some((t1, k)) = value(s, skip_ws(s, p), (f.depth - 1) as nat, t) {
            lemma_after_extends(s, k, f, t1);
            if let Some((t2, _)) = after(s, k, f, t1) {
                lemma_ext_trans(t2, t1, t);
            }
        }
    } else if w == AFTER {
        lemma_after_extends(s, p, f, t);
    }
}

/// Closing the containers changes nothing on the tape after their start
/// tokens.
pub proof fn lemma_unwind_keeps(s: Seq<u8>, fs: Seq<Frame>, t: Seq<STok>, n: int, m: int)
    requires
        forall|a: int| 0 <= a < fs.len() ==> #[trigger] fs[a].start < m,
        0 <= m < t.len(),
    ensures
        unwind(s, fs, Some((t, n))) matches Some(t2) ==> m < t2.len() && t2[m] == t[m],
    decreases fs.len(),
{
    if fs.len() > 0 {
        let up = fs.drop_last();
        let t1 = close_at(t, fs.last().start);
        assert(fs[fs.len() - 1].start < m);
        assert(t1[m] == t[m]);
        assert forall|a: int| 0 <= a < up.len() implies #[trigger] up[a].start < m by {
            assert(up[a] == fs[a]);
        }
        assert(unwind(s, fs, Some((t, n))) == unwind(s, up, if up.len() == 0 {
            Some((t1, n))
        } else {
            after(s, n, up.last(), t1)
        }));
        if up.len() == 0 {
            lemma_unwind_keeps(s, up, t1, n, m);
        } else {
            lemma_after_extends(s, n, up.last(), t1);
            if let Some((t3, n3)) = after(s, n, up.last(), t1) {
                lemma_ext_at(t3, t1, m);
                lemma_unwind_keeps(s, up, t3, n3, m);
            } else {
                assert(unwind(s, up, None) is None);
            }
        }
    }
}

/// **What is on the tape stays.** The tape a reader finishes the document
/// with has, at each index after the open containers' start tokens, the
/// token the reader's tape has there.
pub proof fn lemma_finish_keeps(s: Seq<u8>, fs: Seq<Frame>, w: u8, p: int, t: Seq<STok>, m: int)
    requires
        finish(s, fs, w, p, t) is Some,
        forall|a: int| 0 <= a < fs.len() ==> #[trigger] fs[a].start < m,
        0 <= m < t.len(),
    ensures
        m < finish(s, fs, w, p, t).unwrap().len(),
        finish(s, fs, w, p, t).unwrap()[m] == t[m],
{
    if fs.len() == 0 {
        if w == VALUE {
            lemma_value_extends(s, skip_ws(s, p), MAX_DEPTH as nat, t);
            let (t1, k) = value(s, skip_ws(s, p), MAX_DEPTH as nat, t).unwrap();
            lemma_ext_at(t1, t, m);
        }
    } else {
        let f = fs.last();
        lemma_rest_extends(s, w, p, f, t);
        let (t2, n) = rest(s, w, p, f, t).unwrap();
        lemma_ext_at(t2, t, m);
        lemma_unwind_keeps(s, fs, t2, n, m);
    }
}

// ---------------------------------------------------------------------------
// The first token of a value
// ---------------------------------------------------------------------------

/// The token `value` puts at its first slot on the tape is decided by the
/// value's first byte.
pub proof fn lemma_value_head(s: Seq<u8>, j: int, d: nat, t: Seq<STok>)
    requires
        value(s, j, d, t) is Some,
    ensures
        ({
            let (t1, k) = value(s, j, d, t).unwrap();
            let x = t1[t.len() as int];
            &&& 0 <= j < k <= s.len()
            &&& extends(t1, t)
            &&& t.len() < t1.len()
            &&& (s[j] == 0x5B) == (x is ArrStart)
            &&& (s[j] == 0x7B) == (x is ObjStart)
            &&& (s[j] == 0x22) == (x is Str)
            &&& (s[j] == 0x74) == (x is True)
            &&& (s[j] == 0x66) == (x is False)
            &&& (s[j] == 0x6E) == (x is Null)
            &&& !(x is ArrEnd) && !(x is ObjEnd) && !(x is Key)
            &&& s[j] == 0x5B ==> d > 0 && (array(s, j + 1, d, t.push(STok::ArrStart { end: 0 })) matches Some((ta, n))
                && n == k && t1 == close_at(ta, t.len() as int) && x == STok::ArrStart { end: t1.len() - 1 })
            &&& s[j] == 0x7B ==> d > 0 && (object(s, j + 1, d, t.push(STok::ObjStart { end: 0 })) matches Some((ta, n))
                && n == k && t1 == close_at(ta, t.len() as int) && x == STok::ObjStart { end: t1.len() - 1 })
            &&& s[j] == 0x22 ==> (string(s, j) matches Some((n, esc)) && n == k && t1 == t.push(
                STok::Str { start: j + 1, end: n - 1, escaped: esc },
            ))
            &&& s[j] == 0x74 ==> t1 == t.push(STok::True) && k == j + 4 && has_lit(
                s,
                j,
                seq![0x74u8, 0x72, 0x75, 0x65],
            )
            &&& s[j] == 0x66 ==> t1 == t.push(STok::False) && k == j + 5 && has_lit(
                s,
                j,
                seq![0x66u8, 0x61, 0x6C, 0x73, 0x65],
            )
            &&& s[j] == 0x6E ==> t1 == t.push(STok::Null) && k == j + 4 && has_lit(
                s,
                j,
                seq![0x6Eu8, 0x75, 0x6C, 0x6C],
            )
            &&& x is Num ==> number_end(s, j) == Some(k) && t1 == t.push(STok::Num { start: j, end: k })
        }),
{
    lemma_value_advances(s, j, d, t);
    lemma_value_extends(s, j, d, t);
    let (t1, k) = value(s, j, d, t).unwrap();
    let c = s[j];
    if c == 0x5B {
        let x0 = STok::ArrStart { end: 0 };
        lemma_array_extends(s, j + 1, d, t.push(x0));
        let (ta, n) = array(s, j + 1, d, t.push(x0)).unwrap();
        lemma_ext_push(t, x0);
        lemma_ext_at(ta, t.push(x0), t.len() as int);
    } else if c == 0x7B {
        let x0 = STok::ObjStart { end: 0 };
        lemma_object_extends(s, j + 1, d, t.push(x0));
        let (ta, n) = object(s, j + 1, d, t.push(x0)).unwrap();
        lemma_ext_push(t, x0);
        lemma_ext_at(ta, t.push(x0), t.len() as int);
    } else {
        lemma_ext_push(t, t1.last());
        assert(t1 == t.push(t1.last()));
    }
}

// ---------------------------------------------------------------------------
// Each move of the reader leaves the finished tape as it was
// ---------------------------------------------------------------------------

/// Reading (or passing over) a value: the reader then expects what comes
/// after it, with the value's tokens on its tape.
pub proof fn lemma_value_step(s: Seq<u8>, fs: Seq<Frame>, p: int, t: Seq<STok>)
    requires
        finish(s, fs, VALUE, p, t) is Some,
        frames_ok(fs, t),
    ensures
        value(s, skip_ws(s, p), vdepth(fs), t) matches Some((t1, k)) && {
            &&& finish(s, fs, AFTER, k, t1) == finish(s, fs, VALUE, p, t)
            &&& frames_ok(fs, t1)
            &&& extends(t1, t)
            &&& t.len() < t1.len()
            &&& finish(s, fs, VALUE, p, t).unwrap()[t.len() as int] == t1[t.len() as int]
        },
{
    let j = skip_ws(s, p);
    if fs.len() > 0 {
        assert(rest(s, VALUE, p, fs.last(), t) is Some);
    }
    lemma_value_head(s, j, vdepth(fs), t);
    let (t1, k) = value(s, j, vdepth(fs), t).unwrap();
    lemma_frames_extend(fs, t, t1);
    assert forall|a: int| 0 <= a < fs.len() implies #[trigger] fs[a].start < t.len() by {}
    lemma_finish_keeps(s, fs, AFTER, k, t1, t.len() as int);
}

/// After a value, what follows depends only on where the next token is.
pub proof fn lemma_after_ws(s: Seq<u8>, fs: Seq<Frame>, p: int, q: int, t: Seq<STok>)
    requires
        skip_ws(s, p) == skip_ws(s, q),
    ensures
        finish(s, fs, AFTER, p, t) == finish(s, fs, AFTER, q, t),
{
}

/// A value the reader reads to its end ends on a token boundary.
pub proof fn lemma_after_bnd(s: Seq<u8>, st: int, fs: Seq<Frame>, k: int, t: Seq<STok>)
    requires
        finish(s, fs, AFTER, k, t) is Some,
        0 <= st <= k,
    ensures
        bnd(s, st, k),
{
    if !bnd(s, st, k) {
        lemma_not_bnd(s, st, k);
        assert(skip_ws(s, k) == k);
        if fs.len() > 0 {
            assert(after(s, k, fs.last(), t) is None);
        }
    }
}

/// `elements` after a `[` or a `,` is a value, then what comes after a
/// value in the array.
pub proof fn lemma_elements_unfold(s: Seq<u8>, i: int, f: Frame, t: Seq<STok>)
    requires
        !f.obj,
        0 <= i <= s.len(),
        elements(s, i, f.depth, t) is Some,
    ensures
        elements(s, i, f.depth, t) == rest(s, VALUE, i, f, t),
{
    let j = skip_ws(s, i);
    lemma_skip_ws_bounds(s, i);
    let d1 = (f.depth - 1) as nat;
    lemma_value_advances(s, j, d1, t);
    let (t1, k) = value(s, j, d1, t).unwrap();
    lemma_skip_ws_bounds(s, k);
}

/// Opening a container: the reader then expects its first element or key
/// (or its end), inside one more container.
pub proof fn lemma_open_step(s: Seq<u8>, fs: Seq<Frame>, p: int, t: Seq<STok>)
    requires
        finish(s, fs, VALUE, p, t) is Some,
        frames_ok(fs, t),
        0 <= skip_ws(s, p) < s.len(),
        s[skip_ws(s, p)] == 0x5B || s[skip_ws(s, p)] == 0x7B,
    ensures
        ({
            let j = skip_ws(s, p);
            let obj = s[j] == 0x7B;
            let f = Frame { obj, depth: vdepth(fs), start: t.len() as int };
            let x = if obj {
                STok::ObjStart { end: 0 }
            } else {
                STok::ArrStart { end: 0 }
            };
            &&& finish(s, fs.push(f), START, j + 1, t.push(x)) == finish(s, fs, VALUE, p, t)
            &&& frames_ok(fs.push(f), t.push(x))
        }),
{
    let j = skip_ws(s, p);
    let obj = s[j] == 0x7B;
    let f = Frame { obj, depth: vdepth(fs), start: t.len() as int };
    let x = if obj {
        STok::ObjStart { end: 0 }
    } else {
        STok::ArrStart { end: 0 }
    };
    lemma_value_step(s, fs, p, t);
    lemma_value_head(s, j, vdepth(fs), t);
    let fs2 = fs.push(f);
    assert(fs2.drop_last() =~= fs);
    assert(fs2.last() == f);
    let inner = if obj {
        object(s, j + 1, vdepth(fs), t.push(x))
    } else {
        array(s, j + 1, vdepth(fs), t.push(x))
    };
    assert(rest(s, START, j + 1, f, t.push(x)) == inner);
    let (ta, n) = inner.unwrap();
    assert(value(s, j, vdepth(fs), t) == Some((close_at(ta, t.len() as int), n)));
    if fs.len() > 0 {
        assert(rest(s, VALUE, p, fs.last(), t) == after(s, n, fs.last(), close_at(ta, t.len() as int)));
    }
    lemma_ext_push(t, x);
    let t2 = t.push(x);
    assert forall|a: int, b: int| 0 <= a < b < fs2.len() implies #[trigger] fs2[a].start < #[trigger] fs2[b].start by {
        if b < fs.len() {
            assert(fs2[a] == fs[a] && fs2[b] == fs[b]);
        } else {
            assert(fs2[a] == fs[a]);
        }
    }
    assert forall|a: int| 0 <= a < fs2.len() implies 0 <= #[trigger] fs2[a].start < t2.len() by {
        if a < fs.len() {
            assert(fs2[a] == fs[a]);
        }
    }
    assert forall|a: int| 0 <= a < fs2.len() implies if #[trigger] fs2[a].obj {
        t2[fs2[a].start] is ObjStart
    } else {
        t2[fs2[a].start] is ArrStart
    } by {
        if a < fs.len() {
            assert(fs2[a] == fs[a]);
            lemma_ext_at(t2, t, fs[a].start);
        }
    }
}

/// Leaving the innermost container, from anywhere in it: the reader then
/// expects what comes after it, with the container linked on the tape.
pub proof fn lemma_leave_step(s: Seq<u8>, fs: Seq<Frame>, w: u8, p: int, t: Seq<STok>)
    requires
        fs.len() > 0,
        finish(s, fs, w, p, t) is Some,
        frames_ok(fs, t),
    ensures
        rest(s, w, p, fs.last(), t) matches Some((t2, n)) && {
            let f = fs.last();
            let up = fs.drop_last();
            let t3 = close_at(t2, f.start);
            &&& finish(s, up, AFTER, n, t3) == finish(s, fs, w, p, t)
            &&& frames_ok(up, t3)
            &&& extends(t2, t)
            &&& t3.len() == t2.len()
            &&& t3[f.start] == if f.obj {
                STok::ObjStart { end: t3.len() - 1 }
            } else {
                STok::ArrStart { end: t3.len() - 1 }
            }
            &&& finish(s, fs, w, p, t).unwrap()[f.start] == t3[f.start]
        },
{
    let f = fs.last();
    let up = fs.drop_last();
    assert(rest(s, w, p, f, t) is Some);
    lemma_rest_extends(s, w, p, f, t);
    let (t2, n) = rest(s, w, p, f, t).unwrap();
    let t3 = close_at(t2, f.start);
    assert(f == fs[fs.len() - 1]);
    assert(0 <= f.start < t.len());
    lemma_ext_at(t2, t, f.start);
    if up.len() > 0 {
        assert(rest(s, AFTER, n, up.last(), t3) == after(s, n, up.last(), t3));
    }
    assert forall|a: int| 0 <= a < up.len() implies #[trigger] up[a].start < f.start by {
        assert(up[a] == fs[a]);
    }
    assert forall|a: int, b: int| 0 <= a < b < up.len() implies #[trigger] up[a].start < #[trigger] up[b].start by {
        assert(up[a] == fs[a] && up[b] == fs[b]);
    }
    assert forall|a: int| 0 <= a < up.len() implies 0 <= #[trigger] up[a].start < t3.len() by {
        assert(up[a] == fs[a]);
    }
    assert forall|a: int| 0 <= a < up.len() implies if #[trigger] up[a].obj {
        t3[up[a].start] is ObjStart
    } else {
        t3[up[a].start] is ArrStart
    } by {
        assert(up[a] == fs[a]);
        lemma_ext_at(t2, t, fs[a].start);
    }
    lemma_finish_keeps(s, up, AFTER, n, t3, f.start);
}

/// At a container's start, unless it is empty: the reader then expects a
/// value (in an array) or a key (in an object).
pub proof fn lemma_start_step(s: Seq<u8>, fs: Seq<Frame>, p: int, t: Seq<STok>)
    requires
        fs.len() > 0,
        0 <= p <= s.len(),
        finish(s, fs, START, p, t) is Some,
        !(0 <= skip_ws(s, p) < s.len() && s[skip_ws(s, p)] == close_byte(fs.last().obj)),
    ensures
        finish(s, fs, if fs.last().obj {
            KEY
        } else {
            VALUE
        }, p, t) == finish(s, fs, START, p, t),
{
    let f = fs.last();
    if !f.obj {
        assert(rest(s, START, p, f, t) == elements(s, p, f.depth, t));
        lemma_elements_unfold(s, p, f, t);
    }
}

/// At a `,` after a value: the reader then expects the next value (in an
/// array) or key (in an object).
pub proof fn lemma_comma_step(s: Seq<u8>, fs: Seq<Frame>, p: int, t: Seq<STok>)
    requires
        fs.len() > 0,
        finish(s, fs, AFTER, p, t) is Some,
        0 <= skip_ws(s, p) < s.len(),
        s[skip_ws(s, p)] == 0x2C,
    ensures
        finish(s, fs, if fs.last().obj {
            KEY
        } else {
            VALUE
        }, skip_ws(s, p) + 1, t) == finish(s, fs, AFTER, p, t),
{
    let f = fs.last();
    let j = skip_ws(s, p);
    if !f.obj {
        assert(rest(s, AFTER, p, f, t) == elements(s, j + 1, f.depth, t));
        lemma_elements_unfold(s, j + 1, f, t);
    }
}

/// At a key: the reader reads it and the colon after it, and then expects
/// the member's value, with the key on its tape.
pub proof fn lemma_key_step(s: Seq<u8>, fs: Seq<Frame>, p: int, t: Seq<STok>)
    requires
        fs.len() > 0,
        0 <= p <= s.len(),
        finish(s, fs, KEY, p, t) is Some,
        frames_ok(fs, t),
    ensures
        fs.last().obj,
        string(s, skip_ws(s, p)) matches Some((k, esc)) && {
            let j = skip_ws(s, p);
            let c = skip_ws(s, k);
            let x = STok::Key { start: j + 1, end: k - 1, escaped: esc };
            &&& j < k
            &&& 0 <= c < s.len() && s[c] == 0x3A
            &&& finish(s, fs, VALUE, c + 1, t.push(x)) == finish(s, fs, KEY, p, t)
            &&& frames_ok(fs, t.push(x))
            &&& finish(s, fs, KEY, p, t).unwrap()[t.len() as int] == x
        },
{
    let f = fs.last();
    assert(rest(s, KEY, p, f, t) is Some);
    assert(f.obj);
    let d = f.depth;
    let j = skip_ws(s, p);
    lemma_skip_ws_bounds(s, p);
    lemma_string_body_advances(s, j + 1, false);
    let (k, esc) = string(s, j).unwrap();
    lemma_skip_ws_bounds(s, k);
    let c = skip_ws(s, k);
    lemma_skip_ws_bounds(s, c + 1);
    let x = STok::Key { start: j + 1, end: k - 1, escaped: esc };
    let i = skip_ws(s, c + 1);
    lemma_value_advances(s, i, (d - 1) as nat, t.push(x));
    let (t1, m) = value(s, i, (d - 1) as nat, t.push(x)).unwrap();
    lemma_skip_ws_bounds(s, m);
    assert(rest(s, KEY, p, f, t) == rest(s, VALUE, c + 1, f, t.push(x)));
    lemma_ext_push(t, x);
    lemma_frames_extend(fs, t, t.push(x));
    assert forall|a: int| 0 <= a < fs.len() implies #[trigger] fs[a].start < t.len() by {}
    lemma_finish_keeps(s, fs, VALUE, c + 1, t.push(x), t.len() as int);
}

// ---------------------------------------------------------------------------
// Where the rest of a container ends, in the index
// ---------------------------------------------------------------------------

proof fn lemma_after_body(s: Seq<u8>, st: int, p: int, f: Frame, t: Seq<STok>)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        after(s, p, f, t) is Some,
    ensures
        body_ok(s, st, p, after(s, p, f, t).unwrap().1, close_byte(f.obj)),
{
    let j = skip_ws(s, p);
    let idx = full(s, st);
    lemma_skip(s, st, p);
    lemma_close(s, st, p);
    let d = f.depth;
    if s[j] == close_byte(f.obj) {
        if f.obj {
            assert(object(s, p, d, t) == after(s, p, f, t));
            lemma_sv_object(s, st, p, d, t);
        } else {
            assert(array(s, p, d, t) == after(s, p, f, t));
            lemma_sv_array(s, st, p, d, t);
        }
    } else {
        assert(s[j] == 0x2C);
        assert(is_op(s[j]));
        let n = after(s, p, f, t).unwrap().1;
        if f.obj {
            lemma_sv_members(s, st, j + 1, d, t);
        } else {
            lemma_sv_elements(s, st, j + 1, d, t);
        }
        lemma_step(s, st, j);
        assert(transparent(s, idx, cnt(s, st, p), cnt(s, st, j + 1)));
        lemma_trans(s, idx, cnt(s, st, p), cnt(s, st, j + 1), cnt(s, st, n - 1));
    }
}

/// **Leaving agrees with the grammar.** From any place in a container the
/// grammar reads to its end at `n`, the bracket walk at depth 1 ends at
/// the container's closing bracket.
pub proof fn lemma_rest_body(s: Seq<u8>, st: int, w: u8, p: int, f: Frame, t: Seq<STok>)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        rest(s, w, p, f, t) is Some,
    ensures
        body_ok(s, st, p, rest(s, w, p, f, t).unwrap().1, close_byte(f.obj)),
{
    let d = f.depth;
    if w == START {
        if f.obj {
            lemma_sv_object(s, st, p, d, t);
        } else {
            lemma_sv_array(s, st, p, d, t);
        }
    } else if w == KEY {
        lemma_sv_members(s, st, p, d, t);
    } else if w == VALUE {
        let idx = full(s, st);
        let d1 = (d - 1) as nat;
        let (t1, k) = value(s, skip_ws(s, p), d1, t).unwrap();
        if !bnd(s, st, k) {
            lemma_value_advances(s, skip_ws(s, p), d1, t);
            lemma_skip_ws_bounds(s, p);
            lemma_not_bnd(s, st, k);
            assert(skip_ws(s, k) == k);
            assert(after(s, k, f, t1) is None);
        }
        lemma_skip_value(s, st, p, d1, t);
        lemma_after_body(s, st, k, f, t1);
        let n = after(s, k, f, t1).unwrap().1;
        lemma_trans(s, idx, cnt(s, st, p), cnt(s, st, k), cnt(s, st, n - 1));
    } else {
        lemma_after_body(s, st, p, f, t);
    }
}

/// With `body_ok`, the walk from `p` at depth 1 stops right after the
/// closing bracket at `n - 1`.
pub proof fn lemma_body_close(s: Seq<u8>, st: int, p: int, n: int, close: u8)
    requires
        0 <= st <= p,
        close == 0x5D || close == 0x7D,
        body_ok(s, st, p, n, close),
    ensures
        close_k(s, full(s, st), cnt(s, st, p), 1) == Some(cnt(s, st, n - 1) + 1),
        full(s, st)[cnt(s, st, n - 1)] == n - 1,
        cnt(s, st, n - 1) < full(s, st).len(),
{
    let idx = full(s, st);
    lemma_at(s, st, n - 1);
    let kc = cnt(s, st, n - 1);
    assert(byte(s, n - 1) == close);
    assert(close_k(s, idx, cnt(s, st, p), 1) == close_k(s, idx, kc, 1));
}

/// The document a reader starts on.
pub proof fn lemma_start(s: Seq<u8>)
    requires
        document(s, true) is Some,
    ensures
        finish(s, Seq::empty(), VALUE, bom_end(s), Seq::empty()) == Some(document(s, true).unwrap().0),
        frames_ok(Seq::empty(), Seq::empty()),
        utf8_from(s, bom_end(s)),
        s.len() <= MAX_INPUT,
{
    assert(s.subrange(0, s.len() as int) =~= s);
}

} // verus!
