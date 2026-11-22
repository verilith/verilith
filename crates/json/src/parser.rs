//! Verified executable parser. Every function here is proven to return
//! exactly what the corresponding function in `spec.rs` returns, to never
//! panic (no out-of-bounds indexing, no arithmetic overflow), and to
//! terminate. Recursion is bounded by the nesting depth (`MAX_DEPTH`);
//! sequences of elements, members and string characters are parsed by loops.
//!
//! The parser does not allocate per value: strings and numbers are recorded
//! as byte ranges of the input in a flat tape of 12-byte tokens, and string
//! bodies, whitespace and digit runs are scanned 16 bytes at a time (see
//! `simd.rs`).
use crate::spec::*;
use crate::simd::*;
#[allow(unused_imports)]
use crate::lanes::*;
#[cfg(verus_keep_ghost)]
use verilith_core::num::lemma_digits_run;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Kind {
    Null,
    True,
    False,
    Num,
    Str,
    Key,
    ArrStart,
    ArrEnd,
    ObjStart,
    ObjEnd,
}

/// One tape entry.
///
/// * `Num`, `Str`, `Key`: `a..b` is the byte range of the number lexeme or of
///   the raw string body (between the quotes); `escaped` says whether the
///   body contains a backslash.
/// * `ArrStart`, `ObjStart`: `a` is the index of the matching end token, so
///   readers can skip a whole container in O(1). The link is part of the
///   spec (`STok::ArrStart { end }`, set by `close_at`).
#[derive(Clone, Copy, Debug)]
pub struct Tok {
    pub kind: Kind,
    pub escaped: bool,
    pub a: u32,
    pub b: u32,
    /// `NO`, or a tag saying the parser stored this token's value in
    /// `Tape::aux` (at the token's index): for `Num`, `x - 0x8000` is the
    /// power of ten `q` and the slot holds the significand (see `NumVal`);
    /// for an escaped `Str` or `Key`, the slot holds the range of the
    /// decoded string in `Tape::strs` (start in the low half). It fills
    /// padding, so the token stays 12 bytes. It lets readers skip
    /// rescanning the input, and is not part of the spec: the view below
    /// ignores it.
    pub x: u16,
}

/// `Tok::x` when there is no payload.
pub const NO: u16 = 0;

/// A number's significand and power of ten, accumulated while the number is
/// lexed: the value is `w * 10^q`, negated if `neg`. Only stored when the
/// number has at most 19 significant digits, so that `w` is exact. The
/// arithmetic is not specified; `number.rs` turns it into an `f64`.
#[derive(Clone, Copy, Debug)]
pub struct NumVal {
    pub w: u64,
    pub q: i32,
    pub neg: bool,
}

impl View for Tok {
    type V = STok;

    open spec fn view(&self) -> STok {
        match self.kind {
            Kind::Null => STok::Null,
            Kind::True => STok::True,
            Kind::False => STok::False,
            Kind::Num => STok::Num { start: self.a as int, end: self.b as int },
            Kind::Str => STok::Str { start: self.a as int, end: self.b as int, escaped: self.escaped },
            Kind::Key => STok::Key { start: self.a as int, end: self.b as int, escaped: self.escaped },
            Kind::ArrStart => STok::ArrStart { end: self.a as int },
            Kind::ArrEnd => STok::ArrEnd,
            Kind::ObjStart => STok::ObjStart { end: self.a as int },
            Kind::ObjEnd => STok::ObjEnd,
        }
    }
}

#[inline(always)]
pub fn tok(kind: Kind) -> (t: Tok)
    ensures
        t.kind == kind,
        t.x == NO,
        t.a == 0,
        t.b == 0,
        !t.escaped,
{
    Tok { kind, escaped: false, a: 0, b: 0, x: NO }
}

pub struct Tape {
    pub toks: Vec<Tok>,
    /// Values stored while parsing, indexed like `toks` (see `Tok::x`).
    /// Only the slots of tagged tokens are meaningful.
    pub aux: Vec<u64>,
    /// Escaped strings, decoded while parsing.
    pub strs: Vec<u8>,
    /// Furthest position at which a parse step failed. Used only to report
    /// an error position; it carries no proof obligations.
    pub err_pos: usize,
}

impl View for Tape {
    type V = Seq<STok>;

    open spec fn view(&self) -> Seq<STok> {
        self.toks@.map_values(|t: Tok| t@)
    }
}

impl Tape {
    pub fn with_capacity(n: usize) -> (r: Tape)
        ensures
            r@ == Seq::<STok>::empty(),
    {
        let r = Tape { toks: Vec::with_capacity(n), aux: Vec::new(), strs: Vec::new(), err_pos: 0 };
        assert(r@ =~= Seq::<STok>::empty());
        r
    }

    /// Empties the tape, keeping its allocations.
    pub fn clear(&mut self)
        ensures
            final(self)@ == Seq::<STok>::empty(),
            final(self).toks@.len() == 0,
            final(self).strs@.len() == 0,
    {
        self.toks.clear();
        self.strs.clear();
        self.err_pos = 0;
        assert(self@ =~= Seq::<STok>::empty());
    }

    #[inline(always)]
    pub fn len(&self) -> (n: usize)
        ensures
            n == self@.len(),
    {
        self.toks.len()
    }

    #[inline(always)]
    pub fn push(&mut self, t: Tok)
        ensures
            final(self)@ == old(self)@.push(t@),
            final(self).toks@ == old(self).toks@.push(t),
            final(self).aux == old(self).aux,
            final(self).strs == old(self).strs,
    {
        let ghost tv = t@;
        self.toks.push(t);
        assert(final(self)@ =~= old(self)@.push(tv));
    }

    /// Points the container start token at `idx` to the end token at `end`.
    #[inline(always)]
    pub fn link(&mut self, idx: usize, end: usize)
        requires
            idx < old(self)@.len(),
            old(self).toks@[idx as int].kind == Kind::ArrStart || old(self).toks@[idx as int].kind
                == Kind::ObjStart,
        ensures
            spare(final(self).toks) == spare(old(self).toks),
            final(self).toks@ == old(self).toks@.update(idx as int, Tok {
                kind: old(self).toks@[idx as int].kind,
                escaped: old(self).toks@[idx as int].escaped,
                a: end as u32,
                b: old(self).toks@[idx as int].b,
                x: old(self).toks@[idx as int].x,
            }),
            final(self).aux == old(self).aux,
            final(self).strs == old(self).strs,
    {
        let t = self.toks[idx];
        let ghost tv = t@;
        set_spare(&mut self.toks, idx, Tok { kind: t.kind, escaped: t.escaped, a: end as u32, b: t.b, x: t.x });
    }

    /// Records a failure at `pos`.
    #[inline(always)]
    pub fn fail(&mut self, pos: usize)
        ensures
            final(self)@ == old(self)@,
            final(self).toks == old(self).toks,
            final(self).aux == old(self).aux,
            final(self).strs == old(self).strs,
    {
        if pos > self.err_pos {
            self.err_pos = pos;
        }
    }
}

/// Receiver of the tokens the parser produces. `hist` is the sequence of
/// tokens pushed so far; the parser's postconditions are stated in terms of
/// it. `Tape` stores them; other implementations (such as the C ABI's tree
/// builder) consume them as they arrive.
pub trait Sink {
    spec fn hist(&self) -> Seq<STok>;

    /// What the sink keeps beside the tokens is right for the input `s`.
    /// For `EagerTape` this says every value it stored while parsing is
    /// the value of its token (`stored_ok`), and that the decoded strings
    /// fit in the input; for the other sinks it is `true`.
    spec fn inv(&self, s: Seq<u8>) -> bool;

    /// Between `scan_str` of an escaped string whose body is `s[a..b]`
    /// and the `push_str_fast` of its token: the decoded bytes are
    /// stored, ready to be tagged.
    spec fn ready(&self, s: Seq<u8>, a: int, b: int) -> bool;

    fn push(&mut self, t: Tok)
        requires
            t.x == NO,
        ensures
            final(self).hist() == old(self).hist().push(t@),
            forall|g: Seq<u8>| old(self).inv(g) ==> #[trigger] final(self).inv(g),
    ;

    /// How many more tokens `push_fast` takes.
    spec fn room(&self) -> int;

    /// `push` into room made by `reserve`.
    fn push_fast(&mut self, t: Tok)
        requires
            old(self).room() > 0,
            t.x == NO,
        ensures
            final(self).hist() == old(self).hist().push(t@),
            final(self).room() == old(self).room() - 1,
            forall|g: Seq<u8>| old(self).inv(g) ==> #[trigger] final(self).inv(g),
    ;

    /// `push_fast` of the number token `t` of the input `s`, with its value
    /// as lexed (`ok` says whether `n` is exact, and then it is the
    /// number's `number_value`).
    fn push_num_fast(&mut self, t: Tok, s: &[u8], n: NumVal, ok: bool)
        requires
            old(self).room() > 0,
            t.x == NO,
            t.kind == Kind::Num,
            old(self).inv(s@),
            ok ==> number_value(s@, t.a as int) == (n.neg, n.w as int, n.q as int),
        ensures
            final(self).hist() == old(self).hist().push(t@),
            final(self).room() == old(self).room() - 1,
            final(self).inv(s@),
    ;

    /// `push_fast` of a string or key token whose body is `s[t.a..t.b]`,
    /// right after its `scan_str`.
    fn push_str_fast(&mut self, t: Tok, s: &[u8])
        requires
            old(self).room() > 0,
            t.a <= t.b <= s@.len(),
            t.x == NO,
            t.kind == Kind::Str || t.kind == Kind::Key,
            t.escaped ==> old(self).ready(s@, t.a as int, t.b as int),
            !t.escaped ==> old(self).inv(s@),
        ensures
            final(self).hist() == old(self).hist().push(t@),
            final(self).room() == old(self).room() - 1,
            final(self).inv(s@),
    ;

    /// Stage 2's scan of the string whose opening quote is index entry `k`
    /// (`ex2_string`). An eager sink also decodes an escaped body here, in
    /// the same pass, for the `push_str_fast` that follows.
    fn scan_str(&mut self, s: &[u8], idx: &[u32], k: usize, Ghost(st): Ghost<int>) -> (r: Option<
        (usize, usize, bool),
    >)
        requires
            crate::stage2::indexed(s@, st, idx@),
            k < idx@.len(),
            (idx@[k as int] as int) < s@.len(),
            s@[idx@[k as int] as int] == 0x22,
            crate::stage2::out(s@, st, idx@[k as int] as int),
            old(self).room() > 0,
            old(self).inv(s@),
        ensures
            r matches Some((_, n, esc)) ==> if esc {
                final(self).ready(s@, idx@[k as int] + 1, n - 1)
            } else {
                final(self).inv(s@)
            },
            match string(s@, idx@[k as int] as int) {
                Some((n, esc)) => r == Some((crate::stage2::cnt(s@, st, n) as usize, n as usize, esc))
                    && crate::stage2::out(s@, st, n) && crate::stage2::bnd(s@, st, n) && n <= s@.len(),
                None => r is None,
            },
            r matches Some((k2, _, _)) ==> k2 > k,
            final(self).hist() == old(self).hist(),
            final(self).room() == old(self).room(),
    ;

    /// Whether `push_num_fast` uses the value: if not, the parser need not
    /// compute it.
    fn eager(&self) -> bool;

    /// Makes room for `n` more tokens.
    fn reserve(&mut self, n: usize)
        ensures
            final(self).hist() == old(self).hist(),
            final(self).room() >= n,
            forall|g: Seq<u8>| old(self).inv(g) ==> #[trigger] final(self).inv(g),
    ;

    /// Number of tokens pushed so far.
    fn count(&self) -> (n: usize)
        ensures
            n == self.hist().len(),
    ;

    /// Called after the container whose start token is at index `idx` has
    /// been closed by the most recent push: links the start token to it.
    fn close(&mut self, idx: usize)
        requires
            idx < old(self).hist().len(),
            old(self).hist()[idx as int] is ArrStart || old(self).hist()[idx as int] is ObjStart,
            old(self).hist().len() <= u32::MAX + 1,
        ensures
            final(self).hist() == close_at(old(self).hist(), idx as int),
            final(self).room() == old(self).room(),
            forall|g: Seq<u8>| old(self).inv(g) ==> #[trigger] final(self).inv(g),
    ;

    /// Records a failure at `pos` (diagnostic only).
    fn fail(&mut self, pos: usize)
        ensures
            final(self).hist() == old(self).hist(),
            final(self).room() == old(self).room(),
            forall|g: Seq<u8>| old(self).inv(g) ==> #[trigger] final(self).inv(g),
    ;
}

/// `aux[toks.len()] = v`, growing `aux` to the tokens' capacity if needed
/// (so it grows rarely, and never past that capacity). Every other slot
/// keeps its value.
#[inline(always)]
fn set_aux(aux: &mut Vec<u64>, toks: &Vec<Tok>, v: u64)
    requires
        spare(*toks) > 0,
    ensures
        final(aux)@.len() > toks@.len(),
        final(aux)@[toks@.len() as int] == v,
        forall|j: int| 0 <= j < old(aux)@.len() && j != toks@.len() ==> final(aux)@[j] == old(aux)@[j],
        final(aux)@.len() == old(aux)@.len() || final(aux)@.len() == toks@.len() + spare(*toks),
{
    let i = toks.len();
    if i >= aux.len() {
        grow_aux(aux, len_spare(toks));
    }
    verilith_core::prims::store_at(aux, i, v);
}

/// Lengthens `aux` to `n` slots.
#[cold]
fn grow_aux(aux: &mut Vec<u64>, n: usize)
    requires
        old(aux)@.len() < n,
    ensures
        final(aux)@.len() == n,
        forall|j: int| 0 <= j < old(aux)@.len() ==> final(aux)@[j] == old(aux)@[j],
{
    let ghost a = aux@;
    aux.resize(n, 0);
    assert forall|j: int| 0 <= j < a.len() implies aux@[j] == a[j] by {
        assert(aux@[j] == aux@.subrange(0, a.len() as int)[j]);
    }
}

// ---------------------------------------------------------------------------
// Values stored while parsing (`EagerTape`)
// ---------------------------------------------------------------------------

/// The start of a decoded string's range in `Tape::strs`, as `value.rs`
/// reads it from a slot (`r as u32`).
pub open spec fn lo32(r: u64) -> int {
    (r & 0xFFFF_FFFFu64) as int
}

/// The end of a decoded string's range (`r >> 32`).
pub open spec fn hi32(r: u64) -> int {
    (r >> 32u64) as int
}

/// The power of ten a number token's tag encodes (`x & 0x7FFF`, less
/// `0x4000`, as `value.rs` reads it).
pub open spec fn tag_q(x: u16) -> int {
    (x & 0x7FFFu16) as int - 0x4000
}

/// The sign a number token's tag encodes (its top bit).
pub open spec fn tag_neg(x: u16) -> bool {
    (x >> 15u16) != 0
}

/// Slot `k` of `tape.aux` holds the value of token `k` of the input `s`: for
/// a number, its significand, with the sign and power of ten in the tag, so
/// that the three are its `number_value`; for an escaped string or key, a
/// range of `tape.strs` holding its `decode`d body.
pub open spec fn slot_ok(tape: Tape, s: Seq<u8>, k: int) -> bool {
    let t = tape.toks@[k];
    &&& k < tape.aux@.len()
    &&& match t.kind {
        Kind::Num => number_value(s, t.a as int) == (tag_neg(t.x), tape.aux@[k] as int, tag_q(t.x)),
        Kind::Str | Kind::Key => t.escaped && {
            let r = tape.aux@[k];
            &&& lo32(r) <= hi32(r) <= tape.strs@.len()
            &&& tape.strs@.subrange(lo32(r), hi32(r)) == decode(s, t.a as int, t.b as int)
        },
        _ => false,
    }
}

/// Every token tagged as having a stored value (`Tok::x != NO`) has it in
/// its slot. This is what `value.rs` relies on when it reads a number or an
/// escaped string from `aux` and `strs` instead of from the input.
pub open spec fn stored_ok(tape: Tape, s: Seq<u8>) -> bool {
    forall|k: int| 0 <= k < tape.toks@.len() && (#[trigger] tape.toks@[k]).x != NO ==> slot_ok(tape, s, k)
}

/// The slot for the next token holds the range of the bytes just decoded
/// into `strs`, which are `decode(s, a, b)`.
pub open spec fn pending_ok(tape: Tape, s: Seq<u8>, a: int, b: int) -> bool {
    let i = tape.toks@.len() as int;
    let r = tape.aux@[i];
    &&& i < tape.aux@.len()
    &&& lo32(r) <= hi32(r) == tape.strs@.len()
    &&& tape.strs@.subrange(lo32(r), hi32(r)) == decode(s, a, b)
}

#[verifier::bit_vector]
proof fn lemma_tag_bits(v: u16, b: u16)
    requires
        1 <= v <= 0x7FFF,
        b <= 1,
    ensures
        (v | (b << 15u16)) & 0x7FFFu16 == v,
        ((v | (b << 15u16)) >> 15u16) == b,
        (v | (b << 15u16)) != 0,
{
}

#[verifier::bit_vector]
proof fn lemma_range_bits(a: u64, b: u64)
    requires
        a <= 0xFFFF_FFFF,
        b <= 0xFFFF_FFFF,
    ensures
        (a | (b << 32u64)) & 0xFFFF_FFFFu64 == a,
        (a | (b << 32u64)) >> 32u64 == b,
{
}

/// Pushing a token without a stored value keeps every slot right.
proof fn lemma_stored_push(t0: Tape, t1: Tape, s: Seq<u8>, x: Tok)
    requires
        stored_ok(t0, s),
        t1.toks@ == t0.toks@.push(x),
        t1.aux@ == t0.aux@,
        t1.strs@ == t0.strs@,
        x.x == NO,
    ensures
        stored_ok(t1, s),
{
    assert forall|k: int| 0 <= k < t1.toks@.len() && (#[trigger] t1.toks@[k]).x != NO implies slot_ok(t1, s, k) by {
        assert(t1.toks@[k] == t0.toks@[k]);
        assert(slot_ok(t0, s, k));
    }
}

impl Sink for Tape {
    open spec fn hist(&self) -> Seq<STok> {
        self@
    }

    open spec fn inv(&self, s: Seq<u8>) -> bool {
        true
    }

    open spec fn ready(&self, s: Seq<u8>, a: int, b: int) -> bool {
        true
    }

    #[inline(always)]
    fn push(&mut self, t: Tok) {
        Tape::push(self, t);
    }

    open spec fn room(&self) -> int {
        spare(self.toks)
    }

    #[inline(always)]
    fn push_fast(&mut self, t: Tok) {
        let ghost tv = t@;
        push_spare(&mut self.toks, t);
        assert(self@ =~= old(self)@.push(tv));
    }

    #[inline(always)]
    fn eager(&self) -> bool {
        false
    }

    #[inline(always)]
    fn push_num_fast(&mut self, t: Tok, _s: &[u8], _n: NumVal, _ok: bool) {
        self.push_fast(t);
    }

    #[inline(always)]
    fn push_str_fast(&mut self, t: Tok, _s: &[u8]) {
        self.push_fast(t);
    }

    #[inline(always)]
    fn scan_str(&mut self, s: &[u8], idx: &[u32], k: usize, Ghost(st): Ghost<int>) -> (r: Option<
        (usize, usize, bool),
    >) {
        crate::stage2::ex2_string(s, idx, k, Ghost(st))
    }

    #[inline(always)]
    fn reserve(&mut self, n: usize) {
        reserve_spare(&mut self.toks, n);
    }

    #[inline(always)]
    fn count(&self) -> (n: usize) {
        self.toks.len()
    }

    #[inline(always)]
    fn close(&mut self, idx: usize) {
        let t = self.toks[idx];
        if matches!(t.kind, Kind::ArrStart | Kind::ObjStart) {
            let end = self.toks.len() - 1;
            self.link(idx, end);
            assert(self@ =~= close_at(old(self)@, idx as int));
        }
    }

    #[inline(always)]
    fn fail(&mut self, pos: usize) {
        Tape::fail(self, pos);
    }
}

/// A `Tape` filled eagerly: numbers' values and escaped strings' decoded
/// bytes are stored as they are parsed (see `Tok::x`). A separate type, so
/// that the parse loop is compiled once for each mode and the lazy one
/// carries no checks for the eager work.
pub struct EagerTape {
    pub tape: Tape,
}

impl Sink for EagerTape {
    open spec fn hist(&self) -> Seq<STok> {
        self.tape@
    }

    open spec fn inv(&self, s: Seq<u8>) -> bool {
        &&& stored_ok(self.tape, s)
        &&& self.tape.strs@.len() <= crate::lemmas::weight(self.tape@)
    }

    open spec fn ready(&self, s: Seq<u8>, a: int, b: int) -> bool {
        &&& stored_ok(self.tape, s)
        &&& self.tape.strs@.len() <= crate::lemmas::weight(self.tape@) + (b - a)
        &&& self.tape.strs@.len() <= u32::MAX ==> pending_ok(self.tape, s, a, b)
    }

    #[inline(always)]
    fn push(&mut self, t: Tok) {
        let ghost t0 = self.tape;
        self.tape.push(t);
        proof {
            crate::lemmas::lemma_weight_push(t0@, t@);
            assert forall|g: Seq<u8>| old(self).inv(g) implies #[trigger] self.inv(g) by {
                lemma_stored_push(t0, self.tape, g, t);
            }
        }
    }

    open spec fn room(&self) -> int {
        spare(self.tape.toks)
    }

    #[inline(always)]
    fn push_fast(&mut self, t: Tok) {
        let ghost tv = t@;
        let ghost t0 = self.tape;
        push_spare(&mut self.tape.toks, t);
        assert(self.tape@ =~= old(self).tape@.push(tv));
        proof {
            crate::lemmas::lemma_weight_push(t0@, tv);
            assert forall|g: Seq<u8>| old(self).inv(g) implies #[trigger] self.inv(g) by {
                lemma_stored_push(t0, self.tape, g, t);
            }
        }
    }

    #[inline(always)]
    fn eager(&self) -> bool {
        true
    }

    #[inline(always)]
    fn push_num_fast(&mut self, t: Tok, s: &[u8], n: NumVal, ok: bool) {
        let ghost tv = t@;
        let ghost t0 = self.tape;
        let mut t = t;
        if ok && -0x3FFF <= n.q && n.q <= 0x3FFF {
            set_aux(&mut self.tape.aux, &self.tape.toks, n.w);
            let v = (n.q + 0x4000) as u16;
            let b = n.neg as u16;
            t.x = v | (b << 15u16);
            proof {
                lemma_tag_bits(v, b);
            }
        }
        assert(t@ == tv);
        let ghost t1 = self.tape;
        push_spare(&mut self.tape.toks, t);
        assert(self.tape@ =~= old(self).tape@.push(tv));
        proof {
            crate::lemmas::lemma_weight_push(t0@, tv);
            let i = t0.toks@.len() as int;
            assert forall|k: int| 0 <= k < self.tape.toks@.len() && (#[trigger] self.tape.toks@[k]).x
                != NO implies slot_ok(self.tape, s@, k) by {
                if k < i {
                    assert(self.tape.toks@[k] == t0.toks@[k]);
                    assert(slot_ok(t0, s@, k));
                    assert(self.tape.aux@[k] == t0.aux@[k]);
                } else {
                    assert(self.tape.toks@[k] == t);
                }
            }
        }
    }

    #[inline(always)]
    fn push_str_fast(&mut self, t: Tok, s: &[u8]) {
        let ghost tv = t@;
        let ghost t0 = self.tape;
        let mut t = t;
        // `scan_str` decoded the body and recorded its range.
        if t.escaped && self.tape.strs.len() <= 0xFFFF_FFFF {
            t.x = 1;
        }
        assert(t@ == tv);
        push_spare(&mut self.tape.toks, t);
        assert(self.tape@ =~= old(self).tape@.push(tv));
        proof {
            crate::lemmas::lemma_weight_push(t0@, tv);
            let i = t0.toks@.len() as int;
            assert forall|k: int| 0 <= k < self.tape.toks@.len() && (#[trigger] self.tape.toks@[k]).x
                != NO implies slot_ok(self.tape, s@, k) by {
                if k < i {
                    assert(self.tape.toks@[k] == t0.toks@[k]);
                    assert(slot_ok(t0, s@, k));
                } else {
                    assert(self.tape.toks@[k] == t);
                }
            }
        }
    }

    #[inline(always)]
    fn scan_str(&mut self, s: &[u8], idx: &[u32], k: usize, Ghost(st): Ghost<int>) -> (r: Option<
        (usize, usize, bool),
    >) {
        let ghost t0 = self.tape;
        let start = self.tape.strs.len();
        let r = crate::stage2::ex2_string_dec(s, idx, k, Ghost(st), &mut self.tape.strs);
        let ghost t1 = self.tape;
        if let Some((_, _, true)) = r {
            let end = self.tape.strs.len();
            if end <= 0xFFFF_FFFF {
                set_aux(&mut self.tape.aux, &self.tape.toks, (start as u64) | ((end as u64) << 32u64));
                proof {
                    lemma_range_bits(start as u64, end as u64);
                }
            }
        }
        proof {
            if let Some((_, n, esc)) = r {
                let a = idx@[k as int] + 1;
                let b = n - 1;
                if esc {
                    crate::lemmas::lemma_string_body_advances(s@, a, false);
                    crate::lemmas::lemma_decode_len(s@, a, b);
                    assert(self.tape.strs@ == t0.strs@ + decode(s@, a, b));
                    assert forall|j: int| 0 <= j < self.tape.toks@.len() && (#[trigger] self.tape.toks@[j]).x
                        != NO implies slot_ok(self.tape, s@, j) by {
                        assert(slot_ok(t0, s@, j));
                        assert(self.tape.aux@[j] == t0.aux@[j]);
                        let r0 = t0.aux@[j];
                        if t0.toks@[j].kind == Kind::Str || t0.toks@[j].kind == Kind::Key {
                            assert(self.tape.strs@.subrange(lo32(r0), hi32(r0)) =~= t0.strs@.subrange(lo32(r0), hi32(r0)));
                        }
                    }
                    if self.tape.strs@.len() <= u32::MAX {
                        let i = self.tape.toks@.len() as int;
                        assert(self.tape.strs@.subrange(start as int, self.tape.strs@.len() as int) =~= decode(s@, a, b));
                    }
                } else {
                    assert(self.tape.strs@ == t0.strs@);
                }
            }
        }
        r
    }

    #[inline(always)]
    fn reserve(&mut self, n: usize) {
        reserve_spare(&mut self.tape.toks, n);
    }

    #[inline(always)]
    fn count(&self) -> (n: usize) {
        self.tape.toks.len()
    }

    #[inline(always)]
    fn close(&mut self, idx: usize) {
        let t = self.tape.toks[idx];
        if matches!(t.kind, Kind::ArrStart | Kind::ObjStart) {
            let end = self.tape.toks.len() - 1;
            let ghost t0 = self.tape;
            self.tape.link(idx, end);
            assert(self.tape@ =~= close_at(old(self).tape@, idx as int));
            proof {
                crate::lemmas::lemma_weight_close(t0@, idx as int);
                assert forall|g: Seq<u8>| old(self).inv(g) implies #[trigger] self.inv(g) by {
                    assert forall|j: int| 0 <= j < self.tape.toks@.len() && (#[trigger] self.tape.toks@[j]).x
                        != NO implies slot_ok(self.tape, g, j) by {
                        assert(slot_ok(t0, g, j));
                    }
                }
            }
        }
    }

    #[inline(always)]
    fn fail(&mut self, pos: usize) {
        self.tape.fail(pos);
    }
}

// ---------------------------------------------------------------------------
// Lexical helpers
// ---------------------------------------------------------------------------

#[inline(always)]
fn ex_is_ws(c: u8) -> (r: bool)
    ensures
        r == is_ws(c),
{
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D
}

#[inline(always)]
pub fn ex_is_digit(c: u8) -> (r: bool)
    ensures
        r == is_digit(c),
{
    0x30 <= c && c <= 0x39
}

pub fn ex_skip_ws(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r as int == skip_ws(s@, i as int),
        i <= r <= s@.len(),
{
    let mut j = i;
    while j < s.len() && s[j] <= 0x20 && ex_is_ws(s[j])
        invariant
            i <= j <= s@.len(),
            skip_ws(s@, i as int) == skip_ws(s@, j as int),
        decreases s@.len() - j,
    {
        j = j + 1;
        let ghost j0 = j;
        // Indentation: skip whitespace runs 16 bytes at a time.
        while s.len() - j >= 16
            invariant
                i <= j <= s@.len(),
                j0 <= j,
                skip_ws(s@, i as int) == skip_ws(s@, j as int),
            decreases s@.len() - j,
        {
            let n = ws_run16(s, j);
            proof {
                lemma_ws_run(s@, j as int, j + n);
            }
            j = j + n;
            if n < 16 {
                break;
            }
        }
    }
    j
}

proof fn lemma_ws_run(s: Seq<u8>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
        forall|m: int| j <= m < k ==> is_ws(#[trigger] s[m]),
    ensures
        skip_ws(s, j) == skip_ws(s, k),
    decreases k - j,
{
    if j < k {
        lemma_ws_run(s, j + 1, k);
    }
}

#[inline(always)]
fn ex_digits_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r as int == digits_end(s@, i as int),
        i <= r <= s@.len(),
        (i < s@.len() && is_digit(s@[i as int])) ==> i < r,
{
    let mut j = i;
    // Sixteen bytes at a time while the run continues.
    while s.len() - j >= 16
        invariant
            i <= j <= s@.len(),
            digits_end(s@, i as int) == digits_end(s@, j as int),
        decreases s@.len() - j,
    {
        let p = digit_run16(s, j);
        proof {
            lemma_digits_run(s@, j as int, (j + p) as int);
        }
        j = j + p;
        if p < 16 {
            return j;
        }
    }
    while j < s.len() && ex_is_digit(s[j])
        invariant
            i <= j <= s@.len(),
            digits_end(s@, i as int) == digits_end(s@, j as int),
        decreases s@.len() - j,
    {
        j = j + 1;
    }
    j
}

#[inline(always)]
pub fn ex_has_lit(s: &[u8], i: usize, lit: &[u8]) -> (r: bool)
    requires
        i <= s@.len(),
    ensures
        r == has_lit(s@, i as int, lit@),
{
    if lit.len() > s.len() - i {
        return false;
    }
    let _n = s.len();
    let mut k = 0;
    while k < lit.len()
        invariant
            k <= lit@.len(),
            _n == s@.len(),
            i <= s@.len(),
            i + lit@.len() <= s@.len(),
            forall|m: int| 0 <= m < k ==> s@[i + m] == lit@[m],
        decreases lit@.len() - k,
    {
        if s[i + k] != lit[k] {
            assert(s@.subrange(i as int, i + lit@.len())[k as int] != lit@[k as int]);
            return false;
        }
        k = k + 1;
    }
    assert(s@.subrange(i as int, i + lit@.len()) =~= lit@);
    true
}

// ---------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn ex_number_end(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i <= s@.len(),
    ensures
        match number_end(s@, i as int) {
            Some(e) => r is Some && r.unwrap() as int == e && i < e <= s@.len(),
            None => r is None,
        },
{
    let j = if i < s.len() && s[i] == 0x2D { i + 1 } else { i };
    if !(j < s.len() && ex_is_digit(s[j])) {
        return None;
    }
    let k = if s[j] == 0x30 { j + 1 } else { ex_digits_end(s, j) };
    let k2 = if k < s.len() && s[k] == 0x2E {
        let d = ex_digits_end(s, k + 1);
        if d == k + 1 {
            return None;
        }
        d
    } else {
        k
    };
    if k2 < s.len() && (s[k2] == 0x65 || s[k2] == 0x45) {
        let m = if k2 + 1 < s.len() && (s[k2 + 1] == 0x2B || s[k2 + 1] == 0x2D) {
            k2 + 2
        } else {
            k2 + 1
        };
        let d = ex_digits_end(s, m);
        if d == m {
            return None;
        }
        Some(d)
    } else {
        Some(k2)
    }
}

pub proof fn lemma_p10_add(a: nat, b: nat)
    ensures
        p10i(a + b) == p10i(a) * p10i(b),
        p10i(a) >= 1,
    decreases a,
{
    if a > 0 {
        lemma_p10_add((a - 1) as nat, b);
        assert(p10i(a + b) == 10 * p10i((a - 1 + b) as nat));
        assert(10 * (p10i((a - 1) as nat) * p10i(b)) == (10 * p10i((a - 1) as nat)) * p10i(b)) by (nonlinear_arith);
    }
}

/// Splitting a digit run splits its value.
pub proof fn lemma_dval_split(s: Seq<u8>, a: int, b: int, c: int)
    requires
        a <= b <= c,
    ensures
        dval(s, a, c) == dval(s, a, b) * p10i((c - b) as nat) + dval(s, b, c),
    decreases c - b,
{
    if c > b {
        lemma_dval_split(s, a, b, c - 1);
        let x = dval(s, a, b);
        let y = dval(s, b, c - 1);
        let p = p10i((c - 1 - b) as nat);
        assert(p10i((c - b) as nat) == 10 * p);
        assert((x * p + y) * 10 == x * (10 * p) + y * 10) by (nonlinear_arith);
    }
}

/// The value of `n` digits is below `10^n`.
pub proof fn lemma_dval_bound(s: Seq<u8>, a: int, b: int)
    requires
        a <= b,
        0 <= a,
        b <= s.len(),
        forall|m: int| a <= m < b ==> is_digit(#[trigger] s[m]),
    ensures
        0 <= dval(s, a, b) < p10i((b - a) as nat),
    decreases b - a,
{
    if b > a {
        lemma_dval_bound(s, a, b - 1);
        assert(is_digit(s[b - 1]));
        assert(p10i((b - a) as nat) == 10 * p10i((b - 1 - a) as nat));
    }
}

spec fn pow10_ok_below(n: nat) -> bool
    decreases n,
{
    n == 0 || (POW10_U64@[n - 1] as int == p10i((n - 1) as nat) && pow10_ok_below((n - 1) as nat))
}

proof fn lemma_pow10_u64(n: nat, k: nat)
    requires
        n <= 17,
        k < n,
    ensures
        POW10_U64@[k as int] as int == p10i(k),
    decreases n,
{
    if n == 17 {
        assert(pow10_ok_below(17)) by (compute_only);
    }
    assert(pow10_ok_below(n)) by {
        lemma_pow10_ok_down(17, n);
    }
    lemma_pow10_ok_at(n, k);
}

proof fn lemma_pow10_ok_down(n: nat, m: nat)
    requires
        pow10_ok_below(n) || n == 17,
        m <= n,
        n <= 17,
    ensures
        pow10_ok_below(m),
    decreases n,
{
    if n == 17 {
        assert(pow10_ok_below(17)) by (compute_only);
    }
    if m < n {
        lemma_pow10_ok_down((n - 1) as nat, m);
    }
}

proof fn lemma_pow10_ok_at(n: nat, k: nat)
    requires
        pow10_ok_below(n),
        k < n,
    ensures
        POW10_U64@[k as int] as int == p10i(k),
    decreases n,
{
    if k < n - 1 {
        lemma_pow10_ok_at((n - 1) as nat, k);
    }
}

pub open spec fn two64() -> int {
    0x1_0000_0000_0000_0000
}

/// The accumulator step `w * p + v`, wrapping, keeps the value modulo 2^64.
pub proof fn lemma_acc_step(w: u64, x: int, p: u64, v: int)
    requires
        w as int == x % two64(),
        0 <= v < two64(),
    ensures
        w.wrapping_mul(p).wrapping_add(v as u64) as int == (x * p + v) % two64(),
{
    let m = two64();
    let t = w.wrapping_mul(p);
    assert(t as int == (w as int * p) % m);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(x, p as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x * p, v, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(t as int, v, m);
    vstd::arithmetic::div_mod::lemma_small_mod(v as nat, m as nat);
    vstd::arithmetic::div_mod::lemma_mod_twice(x * p, m);
}

#[verifier::spinoff_prover]
proof fn lemma_acc_digits(s: Seq<u8>, i: int, j: int, c: int, w0: int, w: u64, pw: u64, v: u64)
    requires
        i <= j <= c,
        w as int == (w0 * p10i((j - i) as nat) + dval(s, i, j)) % two64(),
        pw as int == p10i((c - j) as nat),
        v as int == dval(s, j, c),
    ensures
        w.wrapping_mul(pw).wrapping_add(v) as int == (w0 * p10i((c - i) as nat) + dval(s, i, c)) % two64(),
{
    let x = w0 * p10i((j - i) as nat) + dval(s, i, j);
    lemma_acc_step(w, x, pw, v as int);
    lemma_dval_split(s, i, j, c);
    lemma_p10_add((j - i) as nat, (c - j) as nat);
    assert(x * pw + v == w0 * p10i((c - i) as nat) + dval(s, i, c)) by (nonlinear_arith)
        requires
            x == w0 * p10i((j - i) as nat) + dval(s, i, j),
            p10i((c - i) as nat) == p10i((j - i) as nat) * pw,
            dval(s, i, c) == dval(s, i, j) * pw + v;
}

/// `10^k` for `k <= 16`.
const POW10_U64: [u64; 17] = [
    1, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000, 1_000_000_000,
    10_000_000_000, 100_000_000_000, 1_000_000_000_000, 10_000_000_000_000, 100_000_000_000_000,
    1_000_000_000_000_000, 10_000_000_000_000_000,
];

/// The end of the digit run at `i`, also accumulating its digits onto `w`
/// (modulo 2^64). Sixteen bytes at a time with SSE2: the run's length is
/// verified as in `ex_digits_end`, and its value comes from
/// `digits_value16` without a loop, so the run's end costs no branch
/// misprediction.
#[verifier::spinoff_prover]
#[inline(always)]
fn ex_digits_acc(s: &[u8], i: usize, w: u64) -> (r: (usize, u64))
    requires
        i <= s@.len(),
    ensures
        r.0 as int == digits_end(s@, i as int),
        i <= r.0 <= s@.len(),
        (i < s@.len() && is_digit(s@[i as int])) ==> i < r.0,
        r.1 as int == (w as int * p10i((r.0 - i) as nat) + dval(s@, i as int, r.0 as int)) % two64(),
{
    let ghost w0 = w as int;
    let mut j = i;
    let mut acc = w;
    proof {
        vstd::arithmetic::div_mod::lemma_small_mod(w0 as nat, two64() as nat);
        assert(w0 * p10i(0) == w0);
    }
    // Sixteen bytes at a time while the run continues.
    while s.len() - j >= 16
        invariant
            i <= j <= s@.len(),
            digits_end(s@, i as int) == digits_end(s@, j as int),
            forall|m: int| i <= m < j ==> is_digit(#[trigger] s@[m]),
            acc as int == (w0 * p10i((j - i) as nat) + dval(s@, i as int, j as int)) % two64(),
            w0 == w as int,
        decreases s@.len() - j,
    {
        let (p, v) = digit_run_acc16(s, j);
        proof {
            lemma_digits_run(s@, j as int, (j + p) as int);
            lemma_pow10_u64(17, p as nat);
            lemma_acc_digits(s@, i as int, j as int, (j + p) as int, w0, acc, POW10_U64[p as int], v);
        }
        acc = acc.wrapping_mul(POW10_U64[p]).wrapping_add(v);
        j = j + p;
        if p < 16 {
            proof {
                assert(digits_end(s@, j as int) == j as int) by {
                    assert(!is_digit_byte(s@[j as int]));
                }
            }
            return (j, acc);
        }
    }
    while j < s.len() && ex_is_digit(get8(s, j))
        invariant
            i <= j <= s@.len(),
            digits_end(s@, i as int) == digits_end(s@, j as int),
            forall|m: int| i <= m < j ==> is_digit(#[trigger] s@[m]),
            acc as int == (w0 * p10i((j - i) as nat) + dval(s@, i as int, j as int)) % two64(),
            w0 == w as int,
        decreases s@.len() - j,
    {
        let c = get8(s, j);
        proof {
            reveal_with_fuel(p10i, 2);
            reveal_with_fuel(dval, 2);
            lemma_acc_digits(s@, i as int, j as int, j + 1, w0, acc, 10, (c - 0x30) as u64);
        }
        acc = acc.wrapping_mul(10).wrapping_add((c - 0x30) as u64);
        j = j + 1;
    }
    (j, acc)
}

/// Every byte of a digit run is a digit.
pub proof fn lemma_digits_all(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= digits_end(s, i) <= s.len(),
        forall|m: int| i <= m < digits_end(s, i) ==> is_digit(#[trigger] s[m]),
    decreases s.len() - i,
{
    if i < s.len() && is_digit(s[i]) {
        lemma_digits_all(s, i + 1);
    }
}

/// Reducing modulo 2^64 before scaling and adding does not change the
/// result modulo 2^64.
proof fn lemma_mod_lin(a: int, b: int, c: int)
    ensures
        ((a % two64()) * b + c) % two64() == (a * b + c) % two64(),
{
    let m = two64();
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(a, b, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop((a % m) * b, c, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a * b, c, m);
}

/// The significand: `x` integer digits with value `a` (below `10^x`) then
/// `f` fraction digits with value `b` (below `10^f`), at most 19 in all,
/// fit in 64 bits.
proof fn lemma_sig_fits(a: int, x: nat, b: int, f: nat)
    requires
        0 <= a < p10i(x),
        0 <= b < p10i(f),
        x + f <= 19,
    ensures
        0 <= a * p10i(f) + b < two64(),
{
    lemma_p10_add(x, f);
    lemma_p10_add((x + f) as nat, (19 - x - f) as nat);
    lemma_p10_add((19 - x - f) as nat, 0);
    assert(p10i(19) == 10_000_000_000_000_000_000) by (compute_only);
    assert(a * p10i(f) + b < p10i(x) * p10i(f)) by (nonlinear_arith)
        requires a + 1 <= p10i(x), b < p10i(f), p10i(f) >= 1, a >= 0;
    assert(p10i(x + f) <= p10i(19)) by (nonlinear_arith)
        requires p10i(19) == p10i(x + f) * p10i((19 - x - f) as nat), p10i((19 - x - f) as nat) >= 1, p10i(x + f) >= 1;
    assert(a * p10i(f) >= 0) by (nonlinear_arith) requires a >= 0, p10i(f) >= 1;
}


/// `ex_digits_acc` from 0 for an integer part: one to three digits (as in
/// coordinates) take a short scalar loop, whose end is well predicted and
/// has much less latency than the 16-byte kernel; longer runs use the
/// kernel.
#[verifier::spinoff_prover]
#[inline(always)]
fn ex_int_acc(s: &[u8], i: usize) -> (r: (usize, u64))
    requires
        i < s@.len(),
    ensures
        r.0 as int == digits_end(s@, i as int),
        i <= r.0 <= s@.len(),
        is_digit(s@[i as int]) ==> i < r.0,
        r.1 as int == dval(s@, i as int, r.0 as int) % two64(),
{
    if s.len() - i >= 4 && ex_is_digit(get8(s, i + 3)) && ex_is_digit(get8(s, i + 2)) && ex_is_digit(get8(s, i + 1)) {
        let r = ex_digits_acc(s, i, 0);
        assert(0 * p10i((r.0 - i) as nat) == 0);
        return r;
    }
    let mut j = i;
    let mut acc = 0u64;
    proof {
        vstd::arithmetic::div_mod::lemma_small_mod(0nat, two64() as nat);
        reveal_with_fuel(dval, 1);
    }
    while j < s.len() && ex_is_digit(get8(s, j))
        invariant
            i <= j <= s@.len(),
            digits_end(s@, i as int) == digits_end(s@, j as int),
            forall|m: int| i <= m < j ==> is_digit(#[trigger] s@[m]),
            acc as int == (0 * p10i((j - i) as nat) + dval(s@, i as int, j as int)) % two64(),
        decreases s@.len() - j,
    {
        let c = get8(s, j);
        proof {
            reveal_with_fuel(p10i, 2);
            reveal_with_fuel(dval, 2);
            lemma_acc_digits(s@, i as int, j as int, j + 1, 0, acc, 10, (c - 0x30) as u64);
        }
        acc = acc.wrapping_mul(10).wrapping_add((c - 0x30) as u64);
        j = j + 1;
    }
    assert(0 * p10i((j - i) as nat) == 0);
    (j, acc)
}

/// The integer and fraction parts at `j`, which starts with a digit:
/// their end (`None` if a `.` has no digits after it), the significand
/// modulo 2^64, the power of ten from the fraction, and whether the
/// significand is exact (at most 19 digits, not counting a leading `0`).
#[verifier::spinoff_prover]
#[inline(always)]
fn ex_sig(s: &[u8], j: usize) -> (r: Option<(usize, u64, i64, bool)>)
    requires
        j < s@.len(),
        is_digit(s@[j as int]),
    ensures
        ({
            let k = int_end(s@, j as int);
            if 0 <= k < s@.len() && s@[k] == 0x2E && digits_end(s@, k + 1) == k + 1 {
                r is None
            } else {
                r is Some && r.unwrap().0 as int == sig_value(s@, j as int).2
            }
        }),
        r matches Some((k2, _, q, _)) ==> j < k2 <= s@.len() && -100 <= q <= 0,
        r matches Some((_, w, q, ok)) ==> (ok ==> w as int == sig_value(s@, j as int).0 && q as int == sig_value(s@, j as int).1),
{
    let zero = s[j] == 0x30;
    let (k, w0) = if zero { (j + 1, 0) } else { ex_int_acc(s, j) };
    // The integer part's digit count, not counting a leading `0`.
    let ghost nint: nat = if zero { 0 } else { (k - j) as nat };
    proof {
        lemma_digits_all(s@, j as int);
        if zero {
            reveal_with_fuel(dval, 2);
            assert(dval(s@, j as int, k as int) == 0);
        } else {
            assert(0 * p10i((k - j) as nat) == 0);
            lemma_dval_bound(s@, j as int, k as int);
        }
        assert(0 <= dval(s@, j as int, k as int) < p10i(nint));
        assert(w0 as int == dval(s@, j as int, k as int) % two64());
    }
    let n: usize = if zero { 0 } else { k - j };
    if k < s.len() && s[k] == 0x2E {
        let (d, w1) = ex_digits_acc(s, k + 1, w0);
        if d == k + 1 {
            return None;
        }
        let f = d - (k + 1);
        let ok = f <= 19 && n <= 19 && n + f <= 19;
        proof {
            let a = dval(s@, j as int, k as int);
            let b = dval(s@, k + 1, d as int);
            lemma_mod_lin(a, p10i(f as nat), b);
            lemma_digits_all(s@, k + 1);
            lemma_dval_bound(s@, k + 1, d as int);
            if ok {
                lemma_sig_fits(a, nint, b, f as nat);
                vstd::arithmetic::div_mod::lemma_small_mod((a * p10i(f as nat) + b) as nat, two64() as nat);
            }
        }
        // Past 19 digits the value is not exact anyway.
        Some((d, w1, if f <= 100 { -(f as i64) } else { 0 }, ok))
    } else {
        let ok = n <= 19;
        proof {
            if ok {
                lemma_sig_fits(dval(s@, j as int, k as int), nint, 0, 0);
                vstd::arithmetic::div_mod::lemma_small_mod(dval(s@, j as int, k as int) as nat, two64() as nat);
            }
        }
        Some((k, w0, 0, ok))
    }
}

/// The value of the exponent digits `s[m..d]`, exact if below 100000.
/// Exponents are short; past 100000 the number is 0 or infinite.
#[verifier::spinoff_prover]
#[inline(always)]
fn ex_exp_value(s: &[u8], m: usize, d: usize) -> (ev: i64)
    requires
        m <= d <= s@.len(),
        forall|t: int| m <= t < d ==> is_digit(#[trigger] s@[t]),
    ensures
        0 <= ev < 1_000_010,
        ev < 100_000 ==> ev as int == dval(s@, m as int, d as int),
{
    let mut ev: i64 = 0;
    let mut x = m;
    while x < d && ev < 100_000
        invariant
            m <= x <= d <= s@.len(),
            forall|t: int| m <= t < d ==> is_digit(#[trigger] s@[t]),
            0 <= ev < 1_000_010,
            ev as int == dval(s@, m as int, x as int),
        decreases d - x,
    {
        let c = s[x];
        proof {
            assert(is_digit(s@[x as int]));
            reveal_with_fuel(dval, 2);
        }
        ev = ev * 10 + (c - 0x30) as i64;
        x = x + 1;
    }
    ev
}

/// `ex_number_scan` for values in objects (citm_catalog.json's ids), with a
/// shorter path for the common shapes: a sign, an integer part not starting
/// with `0` and shorter than 16 digits, read by one 16-byte kernel step,
/// then an end or a fraction. Anything else (and short inputs) goes to
/// `ex_number_scan`. On x86 array elements keep `ex_number_scan`, whose
/// scalar path for short integer parts has less latency (canada.json's
/// coordinates); on AArch64, where the 16-byte kernel is branchless, every
/// value comes here (see `ex2_value` in `src/stage2.rs`).
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ex_number_scan_k(s: &[u8], i: usize) -> (r: Option<(usize, NumVal, bool)>)
    requires
        i <= s@.len(),
    ensures
        match number_end(s@, i as int) {
            Some(e) => r is Some && r.unwrap().0 as int == e && i < e <= s@.len(),
            None => r is None,
        },
        (r is Some && r.unwrap().2) ==> number_value(s@, i as int)
            == (r.unwrap().1.neg, r.unwrap().1.w as int, r.unwrap().1.q as int),
{
    if s.len() - i >= 17 {
        let neg = get8(s, i) == 0x2D;
        let j = if neg { i + 1 } else { i };
        let c = get8(s, j);
        if c != 0x30 && ex_is_digit(c) {
            let (n, v) = crate::simd::digit_run_acc16(s, j);
            if n < 16 {
                let k = j + n;
                let d = get8(s, k);
                let ghost g = s@;
                proof {
                    lemma_digits_run(g, j as int, k as int);
                    assert(digits_end(g, k as int) == k as int);
                    assert(int_end(g, j as int) == k as int);
                    lemma_dval_bound(g, j as int, k as int);
                }
                if d != 0x2E && (d | 0x20) != 0x65 {
                    proof {
                        assert((d | 0x20) != 0x65 ==> d != 0x65 && d != 0x45) by (bit_vector);
                    }
                    return Some((k, NumVal { w: v, q: 0, neg }, true));
                }
                if d == 0x2E {
                    let (dd, w1) = ex_digits_acc(s, k + 1, v);
                    if dd == k + 1 {
                        return None;
                    }
                    let f = dd - (k + 1);
                    if dd >= s.len() || (get8(s, dd) | 0x20) != 0x65 {
                        let ok = f <= 19 && n + f <= 19;
                        proof {
                            if dd < s.len() {
                                let e = s@[dd as int];
                                assert((e | 0x20) != 0x65 ==> e != 0x65 && e != 0x45) by (bit_vector);
                            }
                            let a = dval(g, j as int, k as int);
                            let b = dval(g, k + 1, dd as int);
                            lemma_digits_all(g, k + 1);
                            lemma_dval_bound(g, k + 1, dd as int);
                            if ok {
                                lemma_sig_fits(a, n as nat, b, f as nat);
                                vstd::arithmetic::div_mod::lemma_small_mod((a * p10i(f as nat) + b) as nat, two64() as nat);
                            }
                        }
                        return Some((dd, NumVal { w: w1, q: if f <= 100 { -(f as i32) } else { 0 }, neg }, ok));
                    }
                }
            }
        }
    }
    ex_number_scan(s, i)
}

/// `ex_number_end`, also accumulating the number's value (see `NumVal`).
/// Returns the end, the value, and whether the value is exact: at most 19
/// digits (not counting a leading `0`) and an exponent below 100000, in
/// which case it is the number's `number_value`.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ex_number_scan(s: &[u8], i: usize) -> (r: Option<(usize, NumVal, bool)>)
    requires
        i <= s@.len(),
    ensures
        match number_end(s@, i as int) {
            Some(e) => r is Some && r.unwrap().0 as int == e && i < e <= s@.len(),
            None => r is None,
        },
        (r is Some && r.unwrap().2) ==> number_value(s@, i as int)
            == (r.unwrap().1.neg, r.unwrap().1.w as int, r.unwrap().1.q as int),
{
    let neg = i < s.len() && s[i] == 0x2D;
    let j = if neg { i + 1 } else { i };
    if !(j < s.len() && ex_is_digit(s[j])) {
        return None;
    }
    let (k2, w, q, ok) = match ex_sig(s, j) {
        Some(t) => t,
        None => return None,
    };
    if k2 < s.len() && (s[k2] == 0x65 || s[k2] == 0x45) {
        let eneg = k2 + 1 < s.len() && s[k2 + 1] == 0x2D;
        let m = if k2 + 1 < s.len() && (s[k2 + 1] == 0x2B || s[k2 + 1] == 0x2D) {
            k2 + 2
        } else {
            k2 + 1
        };
        let d = ex_digits_end(s, m);
        if d == m {
            return None;
        }
        proof {
            lemma_digits_all(s@, m as int);
        }
        let ev = ex_exp_value(s, m, d);
        let q = if eneg { q - ev } else { q + ev };
        Some((d, NumVal { w, q: q as i32, neg }, ok && ev < 100_000))
    } else {
        Some((k2, NumVal { w, q: q as i32, neg }, ok))
    }
}

// ---------------------------------------------------------------------------
// Strings
// ---------------------------------------------------------------------------

#[verifier::bit_vector]
proof fn lemma_or4(a: u32, b: u32, c: u32, d: u32)
    requires
        a <= 0xFF, b <= 0xFF, c <= 0xFF, d <= 0xFF,
    ensures
        ((a | b | c | d) < 16) == (a < 16 && b < 16 && c < 16 && d < 16),
{
}

/// The value of the four hex digits at `i`, if they are hex digits.
#[inline(always)]
fn ex_hex4(s: &[u8], i: usize) -> (r: Option<u32>)
    ensures
        r == hex4(s@, i as int),
        r matches Some(u) ==> u < 0x10000,
{
    if i > s.len() || 4 > s.len() - i {
        return None;
    }
    let (ok, u) = ex_hex4_raw(s, i);
    if !ok {
        return None;
    }
    Some(u)
}

/// `ex_hex4` on four bytes that are in range, without branching:
/// whether they are hex digits, and if so their value.
/// Hex digit values, and 255 for bytes that are not hex digits.
pub const HEX: [u8; 256] = [
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 255, 255, 255, 255, 255, 255,
    255, 10, 11, 12, 13, 14, 15, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 10, 11, 12, 13, 14, 15, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
];

pub open spec fn hex_tab_ok(c: u8) -> bool {
    if is_hex(c) {
        HEX@[c as int] as u32 == hex_val(c)
    } else {
        HEX@[c as int] == 0xFF
    }
}

pub open spec fn hex_tab_ok_below(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        hex_tab_ok((n - 1) as u8) && hex_tab_ok_below((n - 1) as nat)
    }
}

proof fn lemma_hex_tab_below(n: nat, c: u8)
    requires
        hex_tab_ok_below(n),
        (c as nat) < n,
    ensures
        hex_tab_ok(c),
    decreases n,
{
    if c as nat != n - 1 {
        lemma_hex_tab_below((n - 1) as nat, c);
    }
}

/// `HEX` is right: checked for all 256 entries by evaluation.
proof fn lemma_hex_tab(c: u8)
    ensures
        hex_tab_ok(c),
        HEX@[c as int] < 16 <==> is_hex(c),
{
    assert(hex_tab_ok_below(256)) by (compute_only);
    lemma_hex_tab_below(256, c);
}

#[verifier::bit_vector]
proof fn lemma_pack4(a: u32, b: u32, c: u32, d: u32)
    requires
        a < 16, b < 16, c < 16, d < 16,
    ensures
        (a << 12u32) | (b << 8u32) | (c << 4u32) | d == ((a * 16 + b) * 16 + c) * 16 + d,
        ((a * 16 + b) * 16 + c) * 16 + d < 0x10000,
{
}

/// Four hex digits by table lookup: `r.0` says all four are hex digits,
/// and then `r.1` is their value.
#[inline(always)]
pub fn ex_hex4_raw(s: &[u8], i: usize) -> (r: (bool, u32))
    requires
        i + 4 <= s@.len(),
    ensures
        r.0 == hex4(s@, i as int) is Some,
        r.0 ==> hex4(s@, i as int) == Some(r.1) && r.1 < 0x10000,
{
    let _n = s.len();
    let h0 = HEX[get8(s, i) as usize] as u32;
    let h1 = HEX[get8(s, i + 1) as usize] as u32;
    let h2 = HEX[get8(s, i + 2) as usize] as u32;
    let h3 = HEX[get8(s, i + 3) as usize] as u32;
    proof {
        lemma_hex_tab(s@[i as int]);
        lemma_hex_tab(s@[i + 1]);
        lemma_hex_tab(s@[i + 2]);
        lemma_hex_tab(s@[i + 3]);
        lemma_or4(h0, h1, h2, h3);
    }
    if (h0 | h1 | h2 | h3) >= 16 {
        return (false, 0);
    }
    proof {
        lemma_pack4(h0, h1, h2, h3);
    }
    (true, (h0 << 12u32) | (h1 << 8u32) | (h2 << 4u32) | h3)
}

/// A code unit whose first hex digit is not `d` is not a surrogate.
pub proof fn lemma_not_surrogate(s: Seq<u8>, i: int)
    requires
        hex4(s, i) is Some,
        s[i] | 0x20 != 0x64,
    ensures
        ({
            let u = hex4(s, i).unwrap();
            u < 0xD800 || u > 0xDFFF
        }),
{
    let b = s[i];
    assert(is_hex(b) && b | 0x20 != 0x64 ==> (if 0x30 <= b <= 0x39 { (b - 0x30) as u32 } else if 0x41
        <= b <= 0x46 { (b - 0x41 + 10) as u32 } else { (b - 0x61 + 10) as u32 }) != 13) by (bit_vector);
    let h0 = hex_val(s[i]) as int;
    let h1 = hex_val(s[i + 1]) as int;
    let h2 = hex_val(s[i + 2]) as int;
    let h3 = hex_val(s[i + 3]) as int;
    assert(h0 != 13 && 0 <= h0 <= 15 && 0 <= h1 <= 15 && 0 <= h2 <= 15 && 0 <= h3 <= 15);
    assert(h0 != 13 && 0 <= h0 <= 15 && 0 <= h1 <= 15 && 0 <= h2 <= 15 && 0 <= h3 <= 15 ==> {
        let u = ((h0 * 16 + h1) * 16 + h2) * 16 + h3;
        u < 0xD800 || u > 0xDFFF
    }) by (nonlinear_arith);
}

/// `ex_push_utf8` for a code point below 0x10000 into reserved space.
#[inline(always)]
fn ex_push_utf8_spare(out: &mut Vec<u8>, cp: u32)
    requires
        cp <= 0x10FFFF,
        spare(*old(out)) >= 4,
    ensures
        final(out)@ == old(out)@ + utf8_encode(cp),
        spare(*final(out)) == spare(*old(out)) - utf8_encode(cp).len(),
{
    // One four-byte store, keeping as many bytes as the encoding has.
    let (x, n) = if cp < 0x80 {
        (cp, 1)
    } else if cp < 0x800 {
        ((0xC0 + cp / 64) | ((0x80 + cp % 64) << 8u32), 2)
    } else if cp < 0x10000 {
        ((0xE0 + cp / 4096) | ((0x80 + (cp / 64) % 64) << 8u32) | ((0x80 + cp % 64) << 16u32), 3)
    } else {
        (
            (0xF0 + cp / 262144) | ((0x80 + (cp / 4096) % 64) << 8u32) | ((0x80 + (cp / 64) % 64) << 16u32) | ((0x80
                + cp % 64) << 24u32),
            4,
        )
    };
    proof {
        if cp < 0x80 {
            bv_le4(cp, 0, 0, 0);
        } else if cp < 0x800 {
            bv_le4((0xC0 + cp / 64) as u32, (0x80 + cp % 64) as u32, 0, 0);
        } else if cp < 0x10000 {
            bv_le4((0xE0 + cp / 4096) as u32, (0x80 + (cp / 64) % 64) as u32, (0x80 + cp % 64) as u32, 0);
        } else {
            bv_le4((0xF0 + cp / 262144) as u32, (0x80 + (cp / 4096) % 64) as u32, (0x80 + (cp / 64) % 64) as u32, (0x80 + cp % 64) as u32);
        }
    }
    let ghost o = out@;
    append4_spare(out, x, n);
    assert(le4(x).subrange(0, n as int) =~= utf8_encode(cp));
}

/// `ex_push_utf8_spare` for a code point below 0x10000.
#[inline(always)]
pub fn ex_push_bmp_spare(out: &mut Vec<u8>, cp: u32)
    requires
        cp < 0x10000,
        spare(*old(out)) >= 4,
    ensures
        final(out)@ == old(out)@ + utf8_encode(cp),
        spare(*final(out)) == spare(*old(out)) - utf8_encode(cp).len(),
{
    let (x, n) = if cp >= 0x800 {
        ((0xE0 + cp / 4096) | ((0x80 + (cp / 64) % 64) << 8u32) | ((0x80 + cp % 64) << 16u32), 3)
    } else if cp >= 0x80 {
        ((0xC0 + cp / 64) | ((0x80 + cp % 64) << 8u32), 2)
    } else {
        (cp, 1)
    };
    proof {
        if cp < 0x80 {
            bv_le4(cp, 0, 0, 0);
        } else if cp < 0x800 {
            bv_le4((0xC0 + cp / 64) as u32, (0x80 + cp % 64) as u32, 0, 0);
        } else {
            bv_le4((0xE0 + cp / 4096) as u32, (0x80 + (cp / 64) % 64) as u32, (0x80 + cp % 64) as u32, 0);
        }
    }
    append4_spare(out, x, n);
    assert(le4(x).subrange(0, n as int) =~= utf8_encode(cp));
}

#[verifier::bit_vector]
proof fn bv_le4(b0: u32, b1: u32, b2: u32, b3: u32)
    requires
        b0 < 256,
        b1 < 256,
        b2 < 256,
        b3 < 256,
    ensures
        ((b0 | (b1 << 8u32) | (b2 << 16u32) | (b3 << 24u32)) as u8) == b0 as u8,
        (((b0 | (b1 << 8u32) | (b2 << 16u32) | (b3 << 24u32)) >> 8u32) as u8) == b1 as u8,
        (((b0 | (b1 << 8u32) | (b2 << 16u32) | (b3 << 24u32)) >> 16u32) as u8) == b2 as u8,
        (((b0 | (b1 << 8u32) | (b2 << 16u32) | (b3 << 24u32)) >> 24u32) as u8) == b3 as u8,
        b0 | (b1 << 8u32) == b0 | (b1 << 8u32) | (0u32 << 16u32) | (0u32 << 24u32),
        b0 | (b1 << 8u32) | (b2 << 16u32) == b0 | (b1 << 8u32) | (b2 << 16u32) | (0u32 << 24u32),
        b0 == b0 | (0u32 << 8u32) | (0u32 << 16u32) | (0u32 << 24u32),
{
}

/// What each simple escape `\c` stands for, and 0 for every other byte
/// (no simple escape stands for 0). A lookup instead of a chain of
/// compares, which LLVM turned into a jump table that mispredicted on
/// strings mixing `\n` and `\u` escapes.
pub const ESC: [u8; 256] = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x22, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2F,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5C, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x0C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0A, 0x00,
    0x00, 0x00, 0x0D, 0x00, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];

pub open spec fn esc_tab_ok(c: u8) -> bool {
    match simple_escape(c) {
        Some(b) => ESC@[c as int] == b && b != 0,
        None => ESC@[c as int] == 0,
    }
}

pub open spec fn esc_tab_ok_below(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        esc_tab_ok((n - 1) as u8) && esc_tab_ok_below((n - 1) as nat)
    }
}

proof fn lemma_esc_tab_below(n: nat, c: u8)
    requires
        esc_tab_ok_below(n),
        (c as nat) < n,
    ensures
        esc_tab_ok(c),
    decreases n,
{
    if c as nat != n - 1 {
        lemma_esc_tab_below((n - 1) as nat, c);
    }
}

#[inline(always)]
fn ex_simple_escape(c: u8) -> (r: Option<u8>)
    ensures
        r == simple_escape(c),
{
    proof {
        // `ESC` is right: checked for all 256 entries by evaluation.
        assert(esc_tab_ok_below(256)) by (compute_only);
        lemma_esc_tab_below(256, c);
    }
    let b = ESC[c as usize];
    if b == 0 {
        None
    } else {
        Some(b)
    }
}

/// `ex_string_char` for an escape, writing into reserved space: the
/// output is never longer than the escape.
#[inline(never)]
pub fn ex_escape_spare(s: &[u8], i: usize, out: &mut Vec<u8>) -> (r: Option<usize>)
    requires
        i < s@.len(),
        spare(*old(out)) >= 4,
    ensures
        match string_char(s@, i as int) {
            Some((b, n)) => r is Some && r.unwrap() as int == n && final(out)@ == old(out)@ + b
                && spare(*final(out)) >= spare(*old(out)) - (n - i),
            None => r is None && final(out)@ == old(out)@,
        },
{
    let c = s[i];
    if c != 0x5C {
        if c == 0x22 || c < 0x20 {
            return None;
        }
        let ghost o = out@;
        push_spare(out, c);
        assert(out@ =~= o + seq![c]);
        return Some(i + 1);
    }
    if !(i + 1 < s.len()) {
        return None;
    }
    let e = get8(s, i + 1);
    if e != 0x75 {
        return match ex_simple_escape(e) {
            Some(b) => {
                let ghost o = out@;
                push_spare(out, b);
                assert(out@ =~= o + seq![b]);
                Some(i + 2)
            },
            None => None,
        };
    }
    let u = match ex_hex4(s, i + 2) {
        Some(u) => u,
        None => return None,
    };
    if 0xDC00 <= u && u <= 0xDFFF {
        return None;
    }
    if 0xD800 <= u && u <= 0xDBFF {
        if !(s.len() - i > 7 && get8(s, i + 6) == 0x5C && get8(s, i + 7) == 0x75) {
            return None;
        }
        let lo = match ex_hex4(s, i + 8) {
            Some(lo) => lo,
            None => return None,
        };
        if !(0xDC00 <= lo && lo <= 0xDFFF) {
            return None;
        }
        let cp = 0x10000 + (u - 0xD800) * 1024 + (lo - 0xDC00);
        ex_push_utf8_spare(out, cp);
        Some(i + 12)
    } else {
        ex_push_utf8_spare(out, u);
        Some(i + 6)
    }
}

/// Length of the escape sequence at `i` (which holds a backslash), if valid.
/// The common `\uXXXX` outside the surrogates is handled inline; the rest
/// out of line.
#[inline(always)]
pub fn ex_escape_end(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i < s@.len(),
        s@[i as int] == 0x5C,
    ensures
        match string_char(s@, i as int) {
            Some((_, n)) => r is Some && r.unwrap() as int == n,
            None => r is None,
        },
        r matches Some(n) ==> i < n <= s@.len(),
{
    if s.len() - i >= 6 && get8(s, i + 1) == 0x75 {
        let (ok, _) = ex_hex4_raw(s, i + 2);
        if ok && get8(s, i + 2) | 0x20 != 0x64 {
            proof {
                lemma_not_surrogate(s@, i + 2);
            }
            return Some(i + 6);
        }
    }
    ex_escape_slow(s, i)
}

#[inline(never)]
fn ex_escape_slow(s: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i < s@.len(),
        s@[i as int] == 0x5C,
    ensures
        match string_char(s@, i as int) {
            Some((_, n)) => r is Some && r.unwrap() as int == n,
            None => r is None,
        },
        r matches Some(n) ==> i < n <= s@.len(),
{
    if !(s.len() - i > 1) {
        return None;
    }
    let e = get8(s, i + 1);
    if e != 0x75 {
        return match ex_simple_escape(e) {
            Some(_) => Some(i + 2),
            None => None,
        };
    }
    // Most escapes are not surrogates, and their first digit says so
    // without computing the value.
    if s.len() - i >= 6 {
        let (ok, _) = ex_hex4_raw(s, i + 2);
        if !ok {
            return None;
        }
        if get8(s, i + 2) | 0x20 != 0x64 {
            proof {
                lemma_not_surrogate(s@, i + 2);
            }
            return Some(i + 6);
        }
    }
    let u = match ex_hex4(s, i + 2) {
        Some(u) => u,
        None => return None,
    };
    if 0xDC00 <= u && u <= 0xDFFF {
        return None;
    }
    if 0xD800 <= u && u <= 0xDBFF {
        if !(s.len() - i > 7 && get8(s, i + 6) == 0x5C && get8(s, i + 7) == 0x75) {
            return None;
        }
        match ex_hex4(s, i + 8) {
            Some(lo) => if 0xDC00 <= lo && lo <= 0xDFFF {
                Some(i + 12)
            } else {
                None
            },
            None => None,
        }
    } else {
        Some(i + 6)
    }
}

/// A byte that a string body may contain unescaped and that stands for itself.

pub proof fn lemma_plain_step(s: Seq<u8>, j: int, esc: bool)
    requires
        0 <= j < s.len(),
        plain(s[j]),
    ensures
        string_body(s, j, esc) == string_body(s, j + 1, esc),
        string_char(s, j) == Some((seq![s[j]], j + 1)),
{
}

pub proof fn lemma_plain_run(s: Seq<u8>, j: int, k: int, esc: bool)
    requires
        0 <= j <= k <= s.len(),
        forall|m: int| j <= m < k ==> plain(#[trigger] s[m]),
    ensures
        string_body(s, j, esc) == string_body(s, k, esc),
    decreases k - j,
{
    if j < k {
        lemma_plain_step(s, j, esc);
        lemma_plain_run(s, j + 1, k, esc);
    }
}

/// Scans a string whose opening quote is at `i`. Returns the position after
/// the closing quote and whether the body contains an escape.
pub fn ex_string(s: &[u8], i: usize) -> (r: Option<(usize, bool)>)
    requires
        i <= s@.len(),
    ensures
        match string(s@, i as int) {
            Some((n, esc)) => r == Some((n as usize, esc)) && i + 2 <= n <= s@.len(),
            None => r is None,
        },
{
    if !(i < s.len() && s[i] == 0x22) {
        return None;
    }
    let mut j = i + 1;
    let mut esc = false;
    loop
        invariant
            i < j <= s@.len(),
            string(s@, i as int) == string_body(s@, j as int, esc),
        decreases s@.len() - j,
    {
        // Skip plain bytes 16 at a time, stopping at the first other byte.
        let ghost j0 = j;
        while s.len() - j >= 16
            invariant
                i < j <= s@.len(),
                j0 <= j,
                string(s@, i as int) == string_body(s@, j as int, esc),
            decreases s@.len() - j,
        {
            let p = plain_run16(s, j);
            proof {
                lemma_plain_run(s@, j as int, j + p, esc);
            }
            j = j + p;
            if p < 16 {
                break;
            }
        }
        if j >= s.len() {
            return None;
        }
        let c = s[j];
        if c == 0x22 {
            return Some((j + 1, esc));
        }
        if c < 0x20 {
            return None;
        }
        if c != 0x5C {
            proof {
                lemma_plain_step(s@, j as int, esc);
            }
            j = j + 1;
        } else {
            match ex_escape_end(s, j) {
                None => return None,
                Some(n) => {
                    esc = true;
                    j = n;
                },
            }
        }
    }
}

pub proof fn lemma_decode_plain_run(s: Seq<u8>, j: int, k: int, end: int)
    requires
        0 <= j <= k <= end <= s.len(),
        forall|m: int| j <= m < k ==> plain(#[trigger] s[m]),
    ensures
        decode(s, j, end) == s.subrange(j, k) + decode(s, k, end),
    decreases k - j,
{
    if j < k {
        lemma_plain_step(s, j, false);
        lemma_decode_plain_run(s, j + 1, k, end);
        assert(s.subrange(j, k) =~= seq![s[j]] + s.subrange(j + 1, k));
    } else {
        assert(s.subrange(j, k) =~= Seq::<u8>::empty());
    }
}

/// Appends the bytes that the string body `s[start..end)` stands for.
#[verifier::spinoff_prover]
pub fn ex_decode(s: &[u8], start: usize, end: usize, out: &mut Vec<u8>)
    requires
        start <= end <= s@.len(),
    ensures
        final(out)@ == old(out)@ + decode(s@, start as int, end as int),
{
    // Decoding never lengthens the text, so one reservation (with 16 bytes
    // of slack for the wide stores) covers the whole string.
    reserve_spare_plus(out, end - start, 16);
    let mut i = start;
    loop
        invariant
            start <= i <= end <= s@.len(),
            spare(*out) >= (end - i) + 16,
            old(out)@ + decode(s@, start as int, end as int) == out@ + decode(
                s@,
                i as int,
                end as int,
            ),
        decreases end - i,
    {
        let ghost o = out@;
        let k = dec_plain(s, i, end, out);
        if k >= end {
            proof {
                assert(decode(s@, k as int, end as int) == Seq::<u8>::empty());
            }
            assert(out@ =~= old(out)@ + decode(s@, start as int, end as int));
            return;
        }
        let j = dec_u_run(s, k, end, out);
        if j > k {
            i = j;
            continue;
        }
        let ghost before = out@;
        let before_len = out.len();
        match ex_escape_spare(s, k, out) {
            None => {
                assert(decode(s@, k as int, end as int) == Seq::<u8>::empty());
                assert(out@ =~= old(out)@ + decode(s@, start as int, end as int));
                return;
            },
            Some(n) => {
                if n > end {
                    assert(decode(s@, k as int, end as int) == Seq::<u8>::empty());
                    proof {
                        lemma_truncate_back(before, out@, string_char(s@, k as int).unwrap().0);
                    }
                    truncate_spare(out, before_len);
                    assert(out@ =~= old(out)@ + decode(s@, start as int, end as int));
                    return;
                }
                assert(out@ + decode(s@, n as int, end as int) =~= before + decode(
                    s@,
                    k as int,
                    end as int,
                ));
                i = n;
            },
        }
    }
}

/// Copies the run of plain bytes at `i` (up to `end`), 16 at a time where
/// the input allows, and returns its end.
#[verifier::spinoff_prover]
#[inline(always)]
fn dec_plain(s: &[u8], i: usize, end: usize, out: &mut Vec<u8>) -> (k: usize)
    requires
        i <= end <= s@.len(),
        spare(*old(out)) >= (end - i) + 16,
    ensures
        i <= k <= end,
        k < end ==> !plain(s@[k as int]),
        spare(*final(out)) >= (end - k) + 16,
        old(out)@ + decode(s@, i as int, end as int) == final(out)@ + decode(s@, k as int, end as int),
{
    let mut k = i;
    while s.len() - k >= 16
        invariant
            i <= k <= end <= s@.len(),
            spare(*out) >= (end - k) + 16,
            old(out)@ + decode(s@, i as int, end as int) == out@ + decode(s@, k as int, end as int),
        decreases end - k,
    {
        let ghost o = out@;
        let r = copy_plain16(s, k, end, out);
        proof {
            lemma_decode_plain_run(s@, k as int, k + r, end as int);
            assert(o + decode(s@, k as int, end as int) == out@ + decode(s@, k + r, end as int));
        }
        k = k + r;
        if r < 16 {
            return k;
        }
    }
    while k < end && get8(s, k) != 0x22 && get8(s, k) != 0x5C && get8(s, k) >= 0x20
        invariant
            i <= k <= end <= s@.len(),
            spare(*out) >= (end - k) + 16,
            old(out)@ + decode(s@, i as int, end as int) == out@ + decode(s@, k as int, end as int),
        decreases end - k,
    {
        let c = get8(s, k);
        proof {
            lemma_decode_plain_run(s@, k as int, k + 1, end as int);
        }
        let ghost o = out@;
        push_spare(out, c);
        assert(out@ =~= o + s@.subrange(k as int, k + 1));
        k = k + 1;
    }
    k
}

/// Decodes the run of `\uXXXX` escapes outside the surrogates at `i` (as
/// in non-Latin text), and returns its end.
#[verifier::spinoff_prover]
#[inline(never)]
fn dec_u_run(s: &[u8], i: usize, end: usize, out: &mut Vec<u8>) -> (j: usize)
    requires
        i <= end <= s@.len(),
        spare(*old(out)) >= (end - i) + 16,
    ensures
        i <= j <= end,
        spare(*final(out)) >= (end - j) + 16,
        old(out)@ + decode(s@, i as int, end as int) == final(out)@ + decode(s@, j as int, end as int),
{
    let mut j = i;
    while end - j >= 6 && get8(s, j) == 0x5C && get8(s, j + 1) == 0x75
        invariant
            i <= j <= end <= s@.len(),
            spare(*out) >= (end - j) + 16,
            old(out)@ + decode(s@, i as int, end as int) == out@ + decode(s@, j as int, end as int),
        decreases end - j,
    {
        let (ok, u) = ex_hex4_raw(s, j + 2);
        if !(ok && get8(s, j + 2) | 0x20 != 0x64) {
            return j;
        }
        proof {
            lemma_not_surrogate(s@, j + 2);
        }
        let ghost before = out@;
        ex_push_bmp_spare(out, u);
        proof {
            assert(string_char(s@, j as int) == Some((utf8_encode(u), j as int + 6)));
            assert(utf8_encode(u).len() <= 3);
            assert(out@ + decode(s@, j as int + 6, end as int) =~= before + decode(s@, j as int, end as int));
        }
        j = j + 6;
    }
    j
}

proof fn lemma_truncate_back(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        b == a + c,
    ensures
        b.subrange(0, a.len() as int) == a,
{
    assert(b.subrange(0, a.len() as int) =~= a);
}

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

/// Parses a value starting at `i`, appending its tokens to `tape`.
pub fn ex_value<S: Sink>(s: &[u8], i: usize, depth: usize, tape: &mut S) -> (r: Option<usize>)
    requires
        i <= s@.len(),
        s@.len() <= u32::MAX,
        old(tape).inv(s@),
        old(tape).hist().len() <= i,
    ensures
        r is Some ==> final(tape).inv(s@),
        match value(s@, i as int, depth as nat, old(tape).hist()) {
            Some((t, n)) => r is Some && r.unwrap() as int == n && final(tape).hist() == t && i < n
                <= s@.len(),
            None => r is None,
        },
    decreases depth, s@.len() - i, 2nat,
{
    if i >= s.len() {
        tape.fail(i);
        return None;
    }
    let c = s[i];
    if c == 0x22 {
        match ex_string(s, i) {
            Some((n, esc)) => {
                tape.push(Tok { kind: Kind::Str, escaped: esc, a: (i + 1) as u32, b: (n - 1) as u32, x: NO });
                Some(n)
            },
            None => {
                tape.fail(i);
                None
            },
        }
    } else if c == 0x5B || c == 0x7B {
        if depth == 0 {
            tape.fail(i);
            return None;
        }
        let idx = tape.count();
        let r = if c == 0x5B {
            tape.push(tok(Kind::ArrStart));
            ex_array(s, i + 1, depth, tape)
        } else {
            tape.push(tok(Kind::ObjStart));
            ex_object(s, i + 1, depth, tape)
        };
        if r.is_some() {
            proof {
                lemma_container_prefix(s@, i as int, depth as nat, old(tape).hist(), c);
            }
            tape.close(idx);
        }
        r
    } else if c == 0x74 {
        if ex_has_lit(s, i, &[0x74u8, 0x72, 0x75, 0x65]) {
            assert([0x74u8, 0x72, 0x75, 0x65]@ == seq![0x74u8, 0x72, 0x75, 0x65]);
            tape.push(tok(Kind::True));
            Some(i + 4)
        } else {
            assert([0x74u8, 0x72, 0x75, 0x65]@ == seq![0x74u8, 0x72, 0x75, 0x65]);
            tape.fail(i);
            None
        }
    } else if c == 0x66 {
        if ex_has_lit(s, i, &[0x66u8, 0x61, 0x6C, 0x73, 0x65]) {
            assert([0x66u8, 0x61, 0x6C, 0x73, 0x65]@ == seq![0x66u8, 0x61, 0x6C, 0x73, 0x65]);
            tape.push(tok(Kind::False));
            Some(i + 5)
        } else {
            assert([0x66u8, 0x61, 0x6C, 0x73, 0x65]@ == seq![0x66u8, 0x61, 0x6C, 0x73, 0x65]);
            tape.fail(i);
            None
        }
    } else if c == 0x6E {
        if ex_has_lit(s, i, &[0x6Eu8, 0x75, 0x6C, 0x6C]) {
            assert([0x6Eu8, 0x75, 0x6C, 0x6C]@ == seq![0x6Eu8, 0x75, 0x6C, 0x6C]);
            tape.push(tok(Kind::Null));
            Some(i + 4)
        } else {
            assert([0x6Eu8, 0x75, 0x6C, 0x6C]@ == seq![0x6Eu8, 0x75, 0x6C, 0x6C]);
            tape.fail(i);
            None
        }
    } else {
        match ex_number_end(s, i) {
            Some(e) => {
                tape.push(Tok { kind: Kind::Num, escaped: false, a: i as u32, b: e as u32, x: NO });
                Some(e)
            },
            None => {
                tape.fail(i);
                None
            },
        }
    }
}

/// A container's tokens extend the tape it started with, beginning with
/// its (not yet linked) start token, and there are few enough of them to
/// link to.
pub proof fn lemma_container_prefix(s: Seq<u8>, i: int, depth: nat, t0: Seq<STok>, c: u8)
    requires
        0 <= i < s.len(),
        s[i] == c,
        c == 0x5B || c == 0x7B,
        depth > 0,
        t0.len() <= i,
    ensures
        ({
            let x = if c == 0x5B { STok::ArrStart { end: 0 } } else { STok::ObjStart { end: 0 } };
            let r = if c == 0x5B { array(s, i + 1, depth, t0.push(x)) } else { object(s, i + 1, depth, t0.push(x)) };
            r matches Some((t, n)) ==> t.len() > t0.len() && t[t0.len() as int] == x && t.len() <= n
                && n <= s.len()
        }),
{
    let x = if c == 0x5B { STok::ArrStart { end: 0 } } else { STok::ObjStart { end: 0 } };
    if c == 0x5B {
        crate::lemmas::lemma_array_extends(s, i + 1, depth, t0.push(x));
        crate::lemmas::lemma_array_size(s, i + 1, depth, t0.push(x));
        crate::lemmas::lemma_array_advances(s, i + 1, depth, t0.push(x));
        if let Some((t, _)) = array(s, i + 1, depth, t0.push(x)) {
            assert(t.subrange(0, (t0.len() + 1) as int)[t0.len() as int] == t[t0.len() as int]);
            assert(t0.push(x)[t0.len() as int] == x);
        }
    } else {
        crate::lemmas::lemma_object_extends(s, i + 1, depth, t0.push(x));
        crate::lemmas::lemma_object_size(s, i + 1, depth, t0.push(x));
        crate::lemmas::lemma_object_advances(s, i + 1, depth, t0.push(x));
        if let Some((t, _)) = object(s, i + 1, depth, t0.push(x)) {
            assert(t.subrange(0, (t0.len() + 1) as int)[t0.len() as int] == t[t0.len() as int]);
            assert(t0.push(x)[t0.len() as int] == x);
        }
    }
}

fn ex_array<S: Sink>(s: &[u8], i: usize, depth: usize, tape: &mut S) -> (r: Option<usize>)
    requires
        i <= s@.len(),
        s@.len() <= u32::MAX,
        old(tape).inv(s@),
        old(tape).hist().len() <= i,
    ensures
        r is Some ==> final(tape).inv(s@),
        match array(s@, i as int, depth as nat, old(tape).hist()) {
            Some((t, n)) => r is Some && r.unwrap() as int == n && final(tape).hist() == t && i < n
                <= s@.len(),
            None => r is None,
        },
    decreases depth, s@.len() - i, 1nat,
{
    let j = ex_skip_ws(s, i);
    if j < s.len() && s[j] == 0x5D {
        tape.push(tok(Kind::ArrEnd));
        Some(j + 1)
    } else {
        ex_elements(s, i, depth, tape)
    }
}

fn ex_elements<S: Sink>(s: &[u8], i0: usize, depth: usize, tape: &mut S) -> (r: Option<usize>)
    requires
        i0 <= s@.len(),
        s@.len() <= u32::MAX,
        old(tape).inv(s@),
        old(tape).hist().len() <= i0,
    ensures
        r is Some ==> final(tape).inv(s@),
        match elements(s@, i0 as int, depth as nat, old(tape).hist()) {
            Some((t, n)) => r is Some && r.unwrap() as int == n && final(tape).hist() == t && i0 < n
                <= s@.len(),
            None => r is None,
        },
    decreases depth, s@.len() - i0, 0nat,
{
    if depth == 0 {
        return None;
    }
    let ghost t0 = tape.hist();
    let mut i = i0;
    loop
        invariant
            i0 <= i <= s@.len(),
            s@.len() <= u32::MAX,
            depth > 0,
            t0 == old(tape).hist(),
            tape.inv(s@),
            tape.hist().len() <= i,
            elements(s@, i0 as int, depth as nat, t0) == elements(
                s@,
                i as int,
                depth as nat,
                tape.hist(),
            ),
        decreases s@.len() - i,
    {
        let ghost tb = tape.hist();
        let j = ex_skip_ws(s, i);
        let k = match ex_value(s, j, depth - 1, tape) {
            Some(k) => k,
            None => return None,
        };
        let ghost tk = tape.hist();
        proof {
            crate::lemmas::lemma_value_size(s@, j as int, (depth - 1) as nat, tb);
        }
        let k2 = ex_skip_ws(s, k);
        if k2 >= s.len() {
            tape.fail(k2);
            return None;
        }
        if s[k2] == 0x5D {
            tape.push(tok(Kind::ArrEnd));
            return Some(k2 + 1);
        }
        if s[k2] != 0x2C {
            tape.fail(k2);
            return None;
        }
        assert(elements(s@, i as int, depth as nat, tb) == elements(
            s@,
            k2 as int + 1,
            depth as nat,
            tk,
        ));
        i = k2 + 1;
    }
}

fn ex_object<S: Sink>(s: &[u8], i: usize, depth: usize, tape: &mut S) -> (r: Option<usize>)
    requires
        i <= s@.len(),
        s@.len() <= u32::MAX,
        old(tape).inv(s@),
        old(tape).hist().len() <= i,
    ensures
        r is Some ==> final(tape).inv(s@),
        match object(s@, i as int, depth as nat, old(tape).hist()) {
            Some((t, n)) => r is Some && r.unwrap() as int == n && final(tape).hist() == t && i < n
                <= s@.len(),
            None => r is None,
        },
    decreases depth, s@.len() - i, 1nat,
{
    let j = ex_skip_ws(s, i);
    if j < s.len() && s[j] == 0x7D {
        tape.push(tok(Kind::ObjEnd));
        Some(j + 1)
    } else {
        ex_members(s, i, depth, tape)
    }
}

fn ex_members<S: Sink>(s: &[u8], i0: usize, depth: usize, tape: &mut S) -> (r: Option<usize>)
    requires
        i0 <= s@.len(),
        s@.len() <= u32::MAX,
        old(tape).inv(s@),
        old(tape).hist().len() <= i0,
    ensures
        r is Some ==> final(tape).inv(s@),
        match members(s@, i0 as int, depth as nat, old(tape).hist()) {
            Some((t, n)) => r is Some && r.unwrap() as int == n && final(tape).hist() == t && i0 < n
                <= s@.len(),
            None => r is None,
        },
    decreases depth, s@.len() - i0, 0nat,
{
    if depth == 0 {
        return None;
    }
    let ghost t0 = tape.hist();
    let mut i = i0;
    loop
        invariant
            i0 <= i <= s@.len(),
            s@.len() <= u32::MAX,
            depth > 0,
            t0 == old(tape).hist(),
            tape.inv(s@),
            tape.hist().len() <= i,
            members(s@, i0 as int, depth as nat, t0) == members(s@, i as int, depth as nat, tape.hist()),
        decreases s@.len() - i,
    {
        let ghost tb = tape.hist();
        let j = ex_skip_ws(s, i);
        let (k, esc) = match ex_string(s, j) {
            Some(p) => p,
            None => {
                tape.fail(j);
                return None;
            },
        };
        let c = ex_skip_ws(s, k);
        if !(c < s.len() && s[c] == 0x3A) {
            tape.fail(c);
            return None;
        }
        let vstart = ex_skip_ws(s, c + 1);
        tape.push(Tok { kind: Kind::Key, escaped: esc, a: (j + 1) as u32, b: (k - 1) as u32, x: NO });
        let m = match ex_value(s, vstart, depth - 1, tape) {
            Some(m) => m,
            None => return None,
        };
        let ghost tm = tape.hist();
        proof {
            crate::lemmas::lemma_value_size(s@, vstart as int, (depth - 1) as nat, tb.push(
                Tok { kind: Kind::Key, escaped: esc, a: (j + 1) as u32, b: (k - 1) as u32, x: NO }@,
            ));
        }
        let m2 = ex_skip_ws(s, m);
        if m2 >= s.len() {
            tape.fail(m2);
            return None;
        }
        if s[m2] == 0x7D {
            tape.push(tok(Kind::ObjEnd));
            return Some(m2 + 1);
        }
        if s[m2] != 0x2C {
            tape.fail(m2);
            return None;
        }
        assert(members(s@, i as int, depth as nat, tb) == members(
            s@,
            m2 as int + 1,
            depth as nat,
            tm,
        ));
        i = m2 + 1;
    }
}

// ---------------------------------------------------------------------------
// Documents
// ---------------------------------------------------------------------------

/// Parses a complete JSON text into `tape` (whose previous contents are
/// discarded, keeping its allocation). On success returns the end of the
/// top-level value. On failure returns the position of the error, which is
/// only a diagnostic (it is not specified).
pub fn parse_into(s: &[u8], require_end: bool, tape: &mut Tape) -> (r: Result<usize, usize>)
    ensures
        match document(s@, require_end) {
            Some((t, e)) => r is Ok && final(tape)@ == t && r.unwrap() as int == e && e <= s@.len()
                && t.len() <= s@.len() && crate::lemmas::links_from(t, 0),
            None => r is Err,
        },
{
    proof {
        crate::lemmas::lemma_document_size(s@, require_end);
        crate::lemmas::lemma_document_links(s@, require_end);
    }
    tape.clear();
    assert(tape@ =~= Seq::<STok>::empty());
    let r = parse_with(s, require_end, tape);
    match r {
        Ok(k) => Ok(k),
        Err(p) => Err(if p > tape.err_pos { p } else { tape.err_pos }),
    }
}

/// Parses a complete JSON text, pushing its tokens to `sink`, which must
/// start empty. On success returns the end of the top-level value; on
/// failure, `Err(p)` where `p` is a diagnostic position.
pub fn parse_with<S: Sink>(s: &[u8], require_end: bool, tape: &mut S) -> (r: Result<usize, usize>)
    requires
        old(tape).hist() == Seq::<STok>::empty(),
        old(tape).inv(s@),
    ensures
        r is Ok ==> final(tape).inv(s@),
        match document(s@, require_end) {
            Some((t, e)) => r is Ok && final(tape).hist() == t && r.unwrap() as int == e && e
                <= s@.len(),
            None => r is Err,
        },
{
    if s.len() > u32::MAX as usize {
        return Err(0);
    }
    let start = if ex_has_lit(s, 0, &[0xEF, 0xBB, 0xBF]) { 3 } else { 0 };
    proof {
        assert([0xEFu8, 0xBB, 0xBF]@ == seq![0xEFu8, 0xBB, 0xBF]);
    }
    let i = ex_skip_ws(s, start);
    let k = match ex_value(s, i, MAX_DEPTH, tape) {
        Some(k) => k,
        None => return Err(0),
    };
    if require_end {
        let e = ex_skip_ws(s, k);
        if e != s.len() {
            return Err(e);
        }
    } else if 0 < k && k < s.len() && ex_is_digit(s[k - 1]) {
        let c = s[k];
        if ex_is_digit(c) || c == 0x2E || c == 0x45 || c == 0x65 || c == 0x2B || c == 0x2D {
            return Err(k);
        }
    }
    proof {
        crate::lemmas::lemma_skip_ws_bounds(s@, start as int);
        crate::lemmas::lemma_value_advances(s@, i as int, MAX_DEPTH as nat, Seq::empty());
    }
    let end = if require_end { s.len() } else { k };
    if !crate::utf8::utf8_valid_upto(s, start, end) {
        // Past every grammar error position, so the caller can tell the two
        // apart.
        return Err(end);
    }
    Ok(k)
}

/// Parses a complete JSON text. On success returns the tape and the end of
/// the top-level value. On failure returns the position of the error.
pub fn parse_document(s: &[u8], require_end: bool) -> (r: Result<(Tape, usize), usize>)
    ensures
        match document(s@, require_end) {
            Some((t, e)) => r is Ok && r.unwrap().0@ == t && r.unwrap().1 as int == e && e
                <= s@.len() && crate::lemmas::in_bounds(s@.len() as int, t) && crate::lemmas::ends_value(t)
                && t.len() <= s@.len() && crate::lemmas::links_from(t, 0),
            None => r is Err,
        },
{
    proof {
        crate::lemmas::lemma_document_in_bounds(s@, require_end);
        crate::lemmas::lemma_document_links(s@, require_end);
    }
    let mut tape = Tape::with_capacity(s.len() / 8 + 4);
    match parse_into(s, require_end, &mut tape) {
        Ok(k) => Ok((tape, k)),
        Err(e) => Err(e),
    }
}

} // verus!
