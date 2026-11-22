//! The tape the parser writes: one 16-byte `Tok` per item, viewed as the
//! spec's `XTok`.
use crate::spec::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Kind {
    XmlDecl,
    Encoding,
    Doctype,
    DoctypeEnd,
    PubId,
    SysId,
    ElementDecl,
    AttlistDecl,
    AttDef,
    AttDefault,
    EntityDecl,
    EntityValue,
    NData,
    NotationDecl,
    PERef,
    Comment,
    PI,
    PIData,
    STag,
    Attr,
    AttVal,
    ETag,
    Text,
    CData,
    CharRef,
    EntRef,
}

/// One item. `a..b` is the item's span (see `XTok`); `f` is its flag or
/// small code (`sd`, `ty`, `kind`, `pe`, `plain`, `cr`); `c` is a start
/// tag's link to its end, or an attribute default's entity count. A
/// character reference keeps its position in `a` and its character in `b`.
#[derive(Clone, Copy, Debug)]
pub struct Tok {
    pub kind: Kind,
    pub f: u8,
    pub a: usize,
    pub b: usize,
    pub c: usize,
}

impl View for Tok {
    type V = XTok;

    open spec fn view(&self) -> XTok {
        let a = self.a as int;
        let b = self.b as int;
        match self.kind {
            Kind::XmlDecl => XTok::XmlDecl { start: a, end: b, sd: self.f as int },
            Kind::Encoding => XTok::Encoding { start: a, end: b },
            Kind::Doctype => XTok::Doctype { start: a, end: b },
            Kind::DoctypeEnd => XTok::DoctypeEnd,
            Kind::PubId => XTok::PubId { start: a, end: b },
            Kind::SysId => XTok::SysId { start: a, end: b },
            Kind::ElementDecl => XTok::ElementDecl { start: a, end: b },
            Kind::AttlistDecl => XTok::AttlistDecl { start: a, end: b },
            Kind::AttDef => XTok::AttDef { start: a, end: b, ty: self.f as int },
            Kind::AttDefault => XTok::AttDefault { start: a, end: b, kind: self.f as int, nents: self.c as int },
            Kind::EntityDecl => XTok::EntityDecl { start: a, end: b, pe: self.f != 0 },
            Kind::EntityValue => XTok::EntityValue { start: a, end: b },
            Kind::NData => XTok::NData { start: a, end: b },
            Kind::NotationDecl => XTok::NotationDecl { start: a, end: b },
            Kind::PERef => XTok::PERef { start: a, end: b },
            Kind::Comment => XTok::Comment { start: a, end: b },
            Kind::PI => XTok::PI { start: a, end: b },
            Kind::PIData => XTok::PIData { start: a, end: b },
            Kind::STag => XTok::STag { start: a, end: b, close: self.c as int },
            Kind::Attr => XTok::Attr { start: a, end: b },
            Kind::AttVal => XTok::AttVal { start: a, end: b, plain: self.f != 0 },
            Kind::ETag => XTok::ETag,
            Kind::Text => XTok::Text { start: a, end: b, cr: self.f != 0 },
            Kind::CData => XTok::CData { start: a, end: b, cr: self.f != 0 },
            Kind::CharRef => XTok::CharRef { pos: a, cp: b },
            Kind::EntRef => XTok::EntRef { start: a, end: b },
        }
    }
}

/// A slice of bytes is at most `isize::MAX` long: Rust allows no object
/// larger than that (the Reference, "Slice layout"; `slice::from_raw_parts`).
/// Trusted: its body is empty, and Verus assumes its `ensures`.
#[verifier::external_body]
#[inline(always)]
pub fn slice_len_bound(s: &[u8])
    ensures
        s@.len() <= isize::MAX,
{
    let _ = s;
}

/// The kind is `Attr`.
#[inline(always)]
pub fn is_attr(k: Kind) -> (r: bool)
    ensures
        r == (k == Kind::Attr),
{
    match k {
        Kind::Attr => true,
        _ => false,
    }
}

/// The kind is `AttDefault`.
#[inline(always)]
pub fn is_att_default(k: Kind) -> (r: bool)
    ensures
        r == (k == Kind::AttDefault),
{
    match k {
        Kind::AttDefault => true,
        _ => false,
    }
}

/// A token with a span and flag.
#[inline(always)]
pub fn tok(kind: Kind, a: usize, b: usize, f: u8) -> (t: Tok)
    requires
        a <= isize::MAX,
        b <= isize::MAX,
    ensures
        t.kind == kind,
        t.a == a,
        t.b == b,
        t.f == f,
        t.c == 0,
{
    Tok { kind, f, a, b, c: 0 }
}

pub struct Tape {
    pub toks: Vec<Tok>,
    /// The furthest position at which a step failed: for error messages
    /// only, outside the spec.
    pub err: usize,
}

impl View for Tape {
    type V = Seq<XTok>;

    open spec fn view(&self) -> Seq<XTok> {
        self.toks@.map_values(|t: Tok| t@)
    }
}

impl Tape {
    pub fn new() -> (r: Tape)
        ensures
            r@ == Seq::<XTok>::empty(),
    {
        let r = Tape { toks: Vec::new(), err: 0 };
        assert(r@ =~= Seq::<XTok>::empty());
        r
    }

    /// Empties the tape, keeping its allocation.
    pub fn clear(&mut self)
        ensures
            final(self)@ == Seq::<XTok>::empty(),
    {
        self.toks.clear();
        self.err = 0;
        assert(self@ =~= Seq::<XTok>::empty());
    }

    /// Records a failure at `pos` (diagnostic only).
    #[inline(always)]
    pub fn fail(&mut self, pos: usize)
        ensures
            final(self)@ == old(self)@,
    {
        if pos > self.err {
            self.err = pos;
        }
    }

    /// Makes room for `n` more tokens.
    pub fn reserve(&mut self, n: usize)
        ensures
            final(self)@ == old(self)@,
    {
        self.toks.reserve(n);
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
    {
        let ghost tv = t@;
        self.toks.push(t);
        assert(final(self)@ =~= old(self)@.push(tv));
    }

    /// `close_at`: links the start tag at `k` to the last token.
    #[inline(always)]
    pub fn close(&mut self, k: usize)
        requires
            k < old(self)@.len() <= isize::MAX,
            old(self)@[k as int] is STag,
        ensures
            final(self)@ == close_at(old(self)@, k as int),
    {
        let n = self.toks.len();
        let t = self.toks[k];
        let ghost old_v = self@;
        self.toks.set(k, Tok { kind: t.kind, f: t.f, a: t.a, b: t.b, c: n - 1 });
        proof {
            assert(t@ == old_v[k as int]);
            assert(t.kind == Kind::STag);
            assert(final(self)@ =~= close_at(old_v, k as int));
        }
    }
}

} // verus!
