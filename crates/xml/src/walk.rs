//! The walk over a tape that the C ABIs (expat's and libxml2's) make their
//! callbacks from, verified: which token comes next, where its item ends,
//! and which end tag closes which element.
//!
//! `items(t, i, e, d, merge)` is the spec of the order of events: the
//! tokens of `t` from `i` to `e`, one item per token, left to right, where
//!
//! * a start tag is one item with the `Attr`/`AttVal` pairs after it, and
//!   opens an element;
//! * an end tag closes the innermost open element, and is skipped when no
//!   element is open (`d` elements are open at `i`, opened before `i`);
//! * a processing instruction is one item with its `PIData`;
//! * with `merge`, a run of character data tokens, each starting where the
//!   one before ended, is one item (libxml2 reports such a run in one
//!   call);
//! * every other token is an item of its own.
//!
//! `Cursor` walks a range of a tape and is proven to give exactly
//! `items`, one at a time, with any number of stops in between (a handler
//! may suspend the parser). The lemmas say what that order is: the items
//! are in the tape's order and never overlap, only stray end tags fall
//! between them (`lemma_items_ordered`), a start tag's item is the tag and
//! its attributes (`lemma_items_shape`), and every end is matched by the
//! innermost open start, so the handlers see a well-nested sequence of
//! start and end events (`lemma_items_balanced`).
//!
//! The ABIs keep, beside the cursor, what they report about each element
//! (its name as reported, its namespace bindings) on a stack: they push on
//! `Start` and pop on `End`, and the balance theorem is what makes the
//! two stacks agree.
use crate::tape::*;
use vstd::prelude::*;

verus! {

/// One item of the walk. Fields are token indices: `at` is the item's
/// first token and `next` the one after its last.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Item {
    /// A start tag at `at`, its attributes up to `next`: an element opens.
    Start { at: usize, next: usize },
    /// The end tag at `at` closes the innermost open element.
    End { at: usize },
    /// Any other item: tokens `at..next`.
    Leaf { at: usize, next: usize },
    /// The range is walked.
    Done,
}

/// Where a start tag's attributes end, from `k` (the token after the tag):
/// past each `Attr`, `AttVal` pair that lies before `e`.
pub open spec fn attrs_end(t: Seq<Tok>, k: int, e: int) -> int
    decreases e - k,
{
    if 0 <= k && k + 1 < e && e <= t.len() && t[k].kind == Kind::Attr && t[k + 1].kind == Kind::AttVal {
        attrs_end(t, k + 2, e)
    } else {
        k
    }
}

/// Where a run of character data ends, from its token `j`: past each
/// following `Text` token before `e` that starts where the one before it
/// ended.
pub open spec fn run_end(t: Seq<Tok>, j: int, e: int) -> int
    decreases e - j,
{
    if 0 <= j && j + 1 < e && e <= t.len() && t[j + 1].kind == Kind::Text && t[j + 1].sa() == t[j].sb() {
        run_end(t, j + 1, e)
    } else {
        j + 1
    }
}

/// The item that starts at token `i` (`i < e`), where it ends, and how
/// many elements are open after it; `None` for an end tag skipped because
/// no element is open.
pub open spec fn step(t: Seq<Tok>, i: int, e: int, d: int, merge: bool) -> (Option<Item>, int, int) {
    let k = t[i].kind;
    if k == Kind::STag {
        let n = attrs_end(t, i + 1, e);
        (Some(Item::Start { at: i as usize, next: n as usize }), n, d + 1)
    } else if k == Kind::ETag {
        if d > 0 {
            (Some(Item::End { at: i as usize }), i + 1, d - 1)
        } else {
            (None, i + 1, d)
        }
    } else if k == Kind::PI && i + 1 < e {
        (Some(Item::Leaf { at: i as usize, next: (i + 2) as usize }), i + 2, d)
    } else if k == Kind::Text && merge {
        let n = run_end(t, i, e);
        (Some(Item::Leaf { at: i as usize, next: n as usize }), n, d)
    } else {
        (Some(Item::Leaf { at: i as usize, next: (i + 1) as usize }), i + 1, d)
    }
}

/// The spec of the walk: the items of `t` from `i` to `e`, with `d`
/// elements open at `i`. (The guard on `n` is never taken:
/// `lemma_step_bounds`.)
pub open spec fn items(t: Seq<Tok>, i: int, e: int, d: int, merge: bool) -> Seq<Item>
    decreases e - i,
{
    if !(0 <= i < e && e <= t.len()) {
        seq![]
    } else {
        let (x, n, d2) = step(t, i, e, d, merge);
        if !(i < n <= e) {
            seq![]
        } else {
            match x {
                Some(x) => seq![x] + items(t, n, e, d2, merge),
                None => items(t, n, e, d2, merge),
            }
        }
    }
}

/// How many elements are open after the items `s`, from `d`.
pub open spec fn depth_after(s: Seq<Item>, d: int) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        d
    } else {
        let d2 = match s[0] {
            Item::Start { .. } => d + 1,
            Item::End { .. } => d - 1,
            _ => d,
        };
        depth_after(s.drop_first(), d2)
    }
}

/// The items `s` are well nested from `d` open elements: no end comes
/// when none is open.
pub open spec fn balanced(s: Seq<Item>, d: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        d >= 0
    } else {
        match s[0] {
            Item::Start { .. } => balanced(s.drop_first(), d + 1),
            Item::End { .. } => d > 0 && balanced(s.drop_first(), d - 1),
            Item::Leaf { .. } => balanced(s.drop_first(), d),
            Item::Done => false,
        }
    }
}

/// The first token of an item.
pub open spec fn at_of(x: Item) -> int {
    match x {
        Item::Start { at, .. } => at as int,
        Item::End { at } => at as int,
        Item::Leaf { at, .. } => at as int,
        Item::Done => 0,
    }
}

/// The token after an item's last.
pub open spec fn next_of(x: Item) -> int {
    match x {
        Item::Start { next, .. } => next as int,
        Item::End { at } => at + 1,
        Item::Leaf { next, .. } => next as int,
        Item::Done => 0,
    }
}

/// The tokens `a..b` are all end tags (skipped ones).
pub open spec fn all_etags(t: Seq<Tok>, a: int, b: int) -> bool {
    forall|j: int| a <= j < b ==> #[trigger] t[j].kind == Kind::ETag
}

/// The items `s` lie in `i..e` in order, without overlapping, each at
/// least one token long; what lies between them (and after the last) is
/// end tags only.
pub open spec fn ordered(t: Seq<Tok>, s: Seq<Item>, i: int, e: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        all_etags(t, i, e)
    } else {
        &&& i <= at_of(s[0]) < next_of(s[0]) <= e
        &&& all_etags(t, i, at_of(s[0]))
        &&& ordered(t, s.drop_first(), next_of(s[0]), e)
    }
}

/// What an item is made of.
pub open spec fn shape(t: Seq<Tok>, x: Item, merge: bool) -> bool {
    match x {
        Item::Start { at, next } => {
            &&& t[at as int].kind == Kind::STag
            &&& forall|j: int|
                at < j < next ==> #[trigger] t[j].kind == if (j - at) % 2 == 1 {
                    Kind::Attr
                } else {
                    Kind::AttVal
                }
            &&& (next - at) % 2 == 1
        },
        Item::End { at } => t[at as int].kind == Kind::ETag,
        Item::Leaf { at, next } => {
            &&& t[at as int].kind != Kind::STag
            &&& t[at as int].kind != Kind::ETag
            &&& {
                ||| next == at + 1
                ||| t[at as int].kind == Kind::PI && next == at + 2
                ||| t[at as int].kind == Kind::Text && merge && forall|j: int|
                    at < j < next ==> #[trigger] t[j].kind == Kind::Text && t[j].sa() == t[j - 1].sb()
            }
        },
        Item::Done => false,
    }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// `attrs_end` stays in the range and past whole pairs.
pub proof fn lemma_attrs_end(t: Seq<Tok>, k: int, e: int)
    requires
        0 <= k <= e <= t.len(),
    ensures
        k <= attrs_end(t, k, e) <= e,
        (attrs_end(t, k, e) - k) % 2 == 0,
    decreases e - k,
{
    if k + 1 < e && t[k].kind == Kind::Attr && t[k + 1].kind == Kind::AttVal {
        lemma_attrs_end(t, k + 2, e);
    }
}

/// `run_end` moves forward, over `Text` tokens that follow on.
pub proof fn lemma_run_end(t: Seq<Tok>, j: int, e: int)
    requires
        0 <= j < e <= t.len(),
    ensures
        j < run_end(t, j, e) <= e,
        forall|m: int|
            j < m < run_end(t, j, e) ==> #[trigger] t[m].kind == Kind::Text && t[m].sa() == t[m - 1].sb(),
    decreases e - j,
{
    if j + 1 < e && t[j + 1].kind == Kind::Text && t[j + 1].sa() == t[j].sb() {
        lemma_run_end(t, j + 1, e);
    }
}

/// A step moves forward and stays in the range.
pub proof fn lemma_step_bounds(t: Seq<Tok>, i: int, e: int, d: int, merge: bool)
    requires
        0 <= i < e <= t.len(),
    ensures
        i < step(t, i, e, d, merge).1 <= e,
{
    if t[i].kind == Kind::STag {
        lemma_attrs_end(t, i + 1, e);
    } else if t[i].kind == Kind::Text && merge {
        lemma_run_end(t, i, e);
    }
}

/// The items of an empty range.
pub proof fn lemma_items_empty(t: Seq<Tok>, i: int, e: int, d: int, merge: bool)
    requires
        i >= e,
    ensures
        items(t, i, e, d, merge) == Seq::<Item>::empty(),
{
}

/// `items` unfolded once.
pub proof fn lemma_items_unfold(t: Seq<Tok>, i: int, e: int, d: int, merge: bool)
    requires
        0 <= i < e <= t.len(),
    ensures
        ({
            let (x, n, d2) = step(t, i, e, d, merge);
            &&& i < n <= e
            &&& items(t, i, e, d, merge) == match x {
                Some(x) => seq![x] + items(t, n, e, d2, merge),
                None => items(t, n, e, d2, merge),
            }
        }),
{
    lemma_step_bounds(t, i, e, d, merge);
}

/// The walk's events are well nested, and it ends with as many elements
/// open as it started with, plus those it opened, less those it closed.
pub proof fn lemma_items_balanced(t: Seq<Tok>, i: int, e: int, d: int, merge: bool)
    requires
        d >= 0,
    ensures
        balanced(items(t, i, e, d, merge), d),
    decreases e - i,
{
    if 0 <= i < e && e <= t.len() {
        lemma_items_unfold(t, i, e, d, merge);
        let (x, n, d2) = step(t, i, e, d, merge);
        lemma_items_balanced(t, n, e, d2, merge);
        let s = items(t, i, e, d, merge);
        match x {
            Some(x) => {
                assert(s.drop_first() =~= items(t, n, e, d2, merge));
            },
            None => {},
        }
    }
}

/// The walk visits the tokens in order, each in one item at most; it
/// skips only end tags that close nothing.
pub proof fn lemma_items_ordered(t: Seq<Tok>, i: int, e: int, d: int, merge: bool)
    requires
        0 <= i <= e <= t.len(),
        e <= usize::MAX,
    ensures
        ordered(t, items(t, i, e, d, merge), i, e),
    decreases e - i,
{
    if i < e {
        lemma_items_unfold(t, i, e, d, merge);
        let (x, n, d2) = step(t, i, e, d, merge);
        lemma_items_ordered(t, n, e, d2, merge);
        let s = items(t, i, e, d, merge);
        match x {
            Some(x) => {
                assert(s.drop_first() =~= items(t, n, e, d2, merge));
                assert(at_of(x) == i && next_of(x) == n);
            },
            None => {
                // A skipped end tag.
                lemma_ordered_skip(t, items(t, n, e, d2, merge), i, n, e);
            },
        }
    }
}

proof fn lemma_ordered_skip(t: Seq<Tok>, s: Seq<Item>, i: int, n: int, e: int)
    requires
        n == i + 1,
        t[i].kind == Kind::ETag,
        ordered(t, s, n, e),
    ensures
        ordered(t, s, i, e),
{
    if s.len() == 0 {
        assert forall|j: int| i <= j < e implies #[trigger] t[j].kind == Kind::ETag by {
            if j > i {
                assert(all_etags(t, n, e));
            }
        }
    } else {
        assert forall|j: int| i <= j < at_of(s[0]) implies #[trigger] t[j].kind == Kind::ETag by {
            if j > i {
                assert(all_etags(t, n, at_of(s[0])));
            }
        }
    }
}

/// Each item is what `shape` says.
pub proof fn lemma_items_shape(t: Seq<Tok>, i: int, e: int, d: int, merge: bool)
    requires
        0 <= i <= e <= t.len(),
        e <= usize::MAX,
    ensures
        forall|m: int| 0 <= m < items(t, i, e, d, merge).len() ==> shape(t, #[trigger] items(t, i, e, d, merge)[m], merge),
    decreases e - i,
{
    if i < e {
        lemma_items_unfold(t, i, e, d, merge);
        let (x, n, d2) = step(t, i, e, d, merge);
        lemma_items_shape(t, n, e, d2, merge);
        let s = items(t, i, e, d, merge);
        let r = items(t, n, e, d2, merge);
        match x {
            Some(x) => {
                lemma_step_shape(t, i, e, d, merge);
                assert forall|m: int| 0 <= m < s.len() implies shape(t, #[trigger] s[m], merge) by {
                    if m > 0 {
                        assert(s[m] == r[m - 1]);
                    }
                }
            },
            None => {},
        }
    }
}

proof fn lemma_step_shape(t: Seq<Tok>, i: int, e: int, d: int, merge: bool)
    requires
        0 <= i < e <= t.len(),
        e <= usize::MAX,
        step(t, i, e, d, merge).0 is Some,
    ensures
        shape(t, step(t, i, e, d, merge).0->Some_0, merge),
{
    let k = t[i].kind;
    if k == Kind::STag {
        lemma_attrs_end(t, i + 1, e);
        let n = attrs_end(t, i + 1, e);
        assert forall|j: int| i < j < n implies #[trigger] t[j].kind == if (j - i) % 2 == 1 {
            Kind::Attr
        } else {
            Kind::AttVal
        } by {
            assert((j - (i + 1)) % 2 == 0 <==> (j - i) % 2 == 1);
            lemma_attr_pair(t, i + 1, e, j);
        }
    } else if k == Kind::Text && merge && !(k == Kind::PI && i + 1 < e) {
        lemma_run_end(t, i, e);
    }
}

/// A start tag's attributes alternate `Attr`, `AttVal`.
proof fn lemma_attr_pair(t: Seq<Tok>, k: int, e: int, j: int)
    requires
        0 <= k <= j < attrs_end(t, k, e),
        e <= t.len(),
    ensures
        t[j].kind == if (j - k) % 2 == 0 {
            Kind::Attr
        } else {
            Kind::AttVal
        },
    decreases e - k,
{
    if k + 1 < e && t[k].kind == Kind::Attr && t[k + 1].kind == Kind::AttVal {
        if j >= k + 2 {
            lemma_attr_pair(t, k + 2, e, j);
            assert((j - k) % 2 == (j - (k + 2)) % 2);
        }
    }
}

// ---------------------------------------------------------------------------
// The cursor
// ---------------------------------------------------------------------------

fn kind_is(k: Kind, w: Kind) -> (r: bool)
    ensures
        r == (k == w),
{
    k as u8 == w as u8
}

/// A walk over the tokens `start..end` of a tape, `items` one at a time.
/// What it has given so far is `hist`, and `hist` followed by what is left
/// (`items` from `pos`) is `items` of the whole range: the items come in
/// the spec's order, none left out or given twice.
pub struct Cursor<'a> {
    toks: &'a [Tok],
    i: usize,
    end: usize,
    depth: usize,
    merge: bool,
    start: Ghost<int>,
    d0: Ghost<int>,
    hist: Ghost<Seq<Item>>,
}

impl<'a> Cursor<'a> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.end <= self.toks@.len()
        &&& 0 <= self.start@ <= self.i <= self.end
        &&& 0 <= self.d0@
        &&& self.depth <= self.d0@ + (self.i - self.start@)
        &&& self.d0@ + self.end <= usize::MAX
        &&& self.hist@ + items(self.toks@, self.i as int, self.end as int, self.depth as int, self.merge)
            == items(self.toks@, self.start@, self.end as int, self.d0@, self.merge)
        &&& self.depth == depth_after(self.hist@, self.d0@)
    }

    /// The tape.
    pub closed spec fn tape(self) -> Seq<Tok> {
        self.toks@
    }

    /// Where the walk began.
    pub closed spec fn first(self) -> int {
        self.start@
    }

    /// Where it ends.
    pub closed spec fn last(self) -> int {
        self.end as int
    }

    /// How many elements were open where it began.
    pub closed spec fn open0(self) -> int {
        self.d0@
    }

    /// Whether runs of character data are merged.
    pub closed spec fn merges(self) -> bool {
        self.merge
    }

    /// The token it is at.
    pub closed spec fn at(self) -> int {
        self.i as int
    }

    /// How many elements are open.
    pub closed spec fn open(self) -> int {
        self.depth as int
    }

    /// The items given so far.
    pub closed spec fn given(self) -> Seq<Item> {
        self.hist@
    }

    /// What the cursor keeps true.
    pub open spec fn wf(self) -> bool {
        &&& self.given() + items(self.tape(), self.at(), self.last(), self.open(), self.merges()) == items(
            self.tape(),
            self.first(),
            self.last(),
            self.open0(),
            self.merges(),
        )
        &&& self.open() == depth_after(self.given(), self.open0())
        &&& 0 <= self.first() <= self.at() <= self.last() <= self.tape().len()
        &&& 0 <= self.open0()
    }

    /// A walk over `toks[start..end]` with `open` elements already open,
    /// one item per character data token unless `merge`. Out-of-range
    /// arguments are cut to the tape (`end` to its length, `start` to
    /// `end`, `open` to what cannot overflow); in range they are kept.
    pub fn new(toks: &'a [Tok], start: usize, end: usize, open: usize, merge: bool) -> (r: Cursor<'a>)
        ensures
            r.tape() == toks@,
            r.merges() == merge,
            end <= toks@.len() ==> r.last() == end,
            start <= end <= toks@.len() ==> r.first() == start,
            open as int + end as int <= usize::MAX && end <= toks@.len() ==> r.open0() == open,
            r.at() == r.first(),
            r.open() == r.open0(),
            r.given() == Seq::<Item>::empty(),
            r.wf(),
    {
        let e = if end <= toks.len() { end } else { toks.len() };
        let a = if start <= e { start } else { e };
        let d = if open <= usize::MAX - e { open } else { usize::MAX - e };
        let r = Cursor { toks, i: a, end: e, depth: d, merge, start: Ghost(a as int), d0: Ghost(d as int), hist: Ghost(Seq::empty()) };
        proof {
            assert(r.hist@ + items(toks@, a as int, e as int, d as int, merge) =~= items(toks@, a as int, e as int, d as int, merge));
        }
        r
    }

    /// The token it is at.
    pub fn pos(&self) -> (r: usize)
        ensures
            r == self.at(),
    {
        self.i
    }

    /// How many elements are open.
    pub fn depth(&self) -> (r: usize)
        ensures
            r == self.open(),
    {
        self.depth
    }

    /// The tape it walks.
    pub fn toks(&self) -> (r: &'a [Tok])
        ensures
            r@ == self.tape(),
    {
        self.toks
    }

    /// The next item: `Done` when the range is walked, and then always.
    /// Otherwise the item is the first of what is left, and the cursor has
    /// moved past it.
    pub fn next(&mut self) -> (r: Item)
        ensures
            final(self).wf(),
            final(self).tape() == old(self).tape(),
            final(self).first() == old(self).first(),
            final(self).last() == old(self).last(),
            final(self).open0() == old(self).open0(),
            final(self).merges() == old(self).merges(),
            r is Done ==> items(final(self).tape(), old(self).at(), final(self).last(), old(self).open(), final(self).merges()) == Seq::<
                Item,
            >::empty() && final(self).given() == old(self).given() && final(self).at() == final(self).last(),
            !(r is Done) ==> {
                &&& items(final(self).tape(), old(self).at(), final(self).last(), old(self).open(), final(self).merges()) == seq![r]
                    + items(final(self).tape(), final(self).at(), final(self).last(), final(self).open(), final(self).merges())
                &&& final(self).given() == old(self).given().push(r)
                &&& final(self).at() == next_of(r)
            },
    {
        proof {
            use_type_invariant(&*self);
        }
        let toks = self.toks;
        let e = self.end;
        let d = self.depth;
        let merge = self.merge;
        let ghost t = toks@;
        let ghost i0 = self.i as int;
        let mut i = self.i;
        // Past the end tags that close nothing.
        if d == 0 {
            while i < e && kind_is(toks[i].kind, Kind::ETag)
                invariant
                    i0 <= i <= e,
                    e <= t.len(),
                    t == toks@,
                    d == 0,
                    items(t, i0, e as int, d as int, merge) == items(t, i as int, e as int, d as int, merge),
                decreases e - i,
            {
                proof {
                    lemma_items_unfold(t, i as int, e as int, d as int, merge);
                }
                i = i + 1;
            }
        }
        if i >= e {
            proof {
                lemma_items_empty(t, i as int, e as int, d as int, merge);
            }
            *self = Cursor { toks, i, end: e, depth: d, merge, start: self.start, d0: self.d0, hist: self.hist };
            return Item::Done;
        }
        proof {
            lemma_items_unfold(t, i as int, e as int, d as int, merge);
        }
        let (r, ni, nd) = step_at(toks, i, e, d, merge);
        proof {
            lemma_depth_after_push(self.hist@, self.d0@, r);
            assert(self.hist@.push(r) + items(t, ni as int, e as int, nd as int, merge) =~= self.hist@ + (seq![r]
                + items(t, ni as int, e as int, nd as int, merge)));
        }
        *self = Cursor { toks, i: ni, end: e, depth: nd, merge, start: self.start, d0: self.d0, hist: Ghost(self.hist@.push(r)) };
        r
    }
}

/// `depth_after` of one more item.
pub proof fn lemma_depth_after_push(s: Seq<Item>, d: int, x: Item)
    ensures
        depth_after(s.push(x), d) == match x {
            Item::Start { .. } => depth_after(s, d) + 1,
            Item::End { .. } => depth_after(s, d) - 1,
            _ => depth_after(s, d),
        },
    decreases s.len(),
{
    let p = s.push(x);
    if s.len() == 0 {
        assert(p[0] == x);
        assert(p.drop_first() =~= Seq::<Item>::empty());
        let d2 = match x {
            Item::Start { .. } => d + 1,
            Item::End { .. } => d - 1,
            _ => d,
        };
        assert(depth_after(p.drop_first(), d2) == d2);
        assert(depth_after(p, d) == d2);
    } else {
        assert(p[0] == s[0]);
        let d2 = match s[0] {
            Item::Start { .. } => d + 1,
            Item::End { .. } => d - 1,
            _ => d,
        };
        lemma_depth_after_push(s.drop_first(), d2, x);
        assert(p.drop_first() =~= s.drop_first().push(x));
    }
}

/// `step` at `i`, for an item (not a skipped end tag).
fn step_at(toks: &[Tok], i: usize, e: usize, d: usize, merge: bool) -> (r: (Item, usize, usize))
    requires
    i < e <= toks@.len(),
    d < usize::MAX,
    d > 0 || toks@[i as int].kind != Kind::ETag,
    ensures
    step(toks@, i as int, e as int, d as int, merge) == (Some(r.0), r.1 as int, r.2 as int),
    !(r.0 is Done),
    next_of(r.0) == r.1,
{
    let ghost t = toks@;
    let k = toks[i].kind;
    if kind_is(k, Kind::STag) {
        let mut j = i + 1;
        while j < e - 1 && kind_is(toks[j].kind, Kind::Attr) && kind_is(toks[j + 1].kind, Kind::AttVal)
            invariant
                i + 1 <= j <= e,
                e <= t.len(),
                t == toks@,
                attrs_end(t, j as int, e as int) == attrs_end(t, i + 1, e as int),
            decreases e - j,
        {
            j = j + 2;
        }
        (Item::Start { at: i, next: j }, j, d + 1)
    } else if kind_is(k, Kind::ETag) {
        (Item::End { at: i }, i + 1, d - 1)
    } else if kind_is(k, Kind::PI) && i + 1 < e {
        (Item::Leaf { at: i, next: i + 2 }, i + 2, d)
    } else if kind_is(k, Kind::Text) && merge {
        let mut j = i;
        while j + 1 < e && kind_is(toks[j + 1].kind, Kind::Text) && toks[j + 1].a48() == toks[j].b48()
            invariant
                i <= j < e,
                e <= t.len(),
                t == toks@,
                run_end(t, j as int, e as int) == run_end(t, i as int, e as int),
            decreases e - j,
        {
            j = j + 1;
        }
        (Item::Leaf { at: i, next: j + 1 }, j + 1, d)
    } else {
        (Item::Leaf { at: i, next: i + 1 }, i + 1, d)
    }
}

} // verus!
