//! The tape the parser writes: one 20-byte `Tok` per item, viewed as the
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

/// The largest position a token holds: 2^48 - 1 (256 TiB), more than any
/// address space gives a process today (x86-64 gives 2^47 bytes, AArch64
/// at most 2^52 in all, which no machine fills with one document). A
/// document longer than this is refused (`ErrorKind::TooLarge`) instead of
/// stored wrong.
pub const MAX_POS: u64 = 0xFFFF_FFFF_FFFF;

/// One item. `a..b` is the item's span (see `XTok`); `f` is its flag or
/// small code (`sd`, `ty`, `kind`, `pe`, `plain`, `cr`); `c` is a start
/// tag's link to its end, or an attribute default's entity count. A
/// character reference keeps its position in `a` and its character in `b`.
///
/// `a`, `b` and `c` are 48 bits each: the low 32 bits in `al`, `bl`, `cl`,
/// the high 16 in `ah`, `bh`, `ch`. That makes the token 20 bytes (4-byte
/// aligned) where three `usize` made it 32 on a 64-bit machine. Read them
/// with `a()`, `b()` and `c()`.
#[derive(Clone, Copy, Debug)]
pub struct Tok {
    pub kind: Kind,
    pub f: u8,
    pub ah: u16,
    pub al: u32,
    pub bl: u32,
    pub bh: u16,
    pub ch: u16,
    pub cl: u32,
}

/// A 48-bit number from its low 32 and high 16 bits.
pub open spec fn wide(lo: u32, hi: u16) -> int {
    lo as int + hi as int * 0x1_0000_0000
}

/// The low and high parts of `v`, which `wide` puts back together.
#[inline(always)]
pub fn split(v: u64) -> (r: (u32, u16))
    requires
        v <= MAX_POS,
    ensures
        wide(r.0, r.1) == v,
{
    let lo = v as u32;
    let hi = (v >> 32u64) as u16;
    assert(lo as int + hi as int * 0x1_0000_0000 == v as int) by (bit_vector)
        requires
            v <= 0xFFFF_FFFF_FFFFu64,
            lo == v as u32,
            hi == (v >> 32u64) as u16,
    ;
    (lo, hi)
}

/// `wide(lo, hi)` as a `u64`.
#[inline(always)]
pub fn join(lo: u32, hi: u16) -> (r: u64)
    ensures
        r == wide(lo, hi),
        r <= MAX_POS,
{
    let r = (lo as u64) | ((hi as u64) << 32u64);
    assert(r as int == lo as int + hi as int * 0x1_0000_0000 && r <= 0xFFFF_FFFF_FFFFu64) by (bit_vector)
        requires
            r == (lo as u64) | ((hi as u64) << 32u64),
    ;
    r
}

/// The low 32 bits of `t`'s span length, `b - a`.
pub open spec fn low_len(t: Tok) -> u32 {
    if t.bl >= t.al {
        (t.bl - t.al) as u32
    } else {
        (t.bl - t.al + 0x1_0000_0000) as u32
    }
}

/// Spans of the same length have the same `low_len`.
pub proof fn lemma_low_len(t: Tok, u: Tok)
    requires
        t.sa() <= t.sb(),
        u.sa() <= u.sb(),
        t.sb() - t.sa() == u.sb() - u.sa(),
    ensures
        low_len(t) == low_len(u),
{
    let d = t.bl as int - t.al as int;
    let e = u.bl as int - u.al as int;
    let k = (u.bh as int - u.ah as int) - (t.bh as int - t.ah as int);
    assert(d - e == k * 0x1_0000_0000) by (nonlinear_arith)
        requires
            t.sb() - t.sa() == u.sb() - u.sa(),
            t.sb() == t.bl as int + t.bh as int * 0x1_0000_0000,
            t.sa() == t.al as int + t.ah as int * 0x1_0000_0000,
            u.sb() == u.bl as int + u.bh as int * 0x1_0000_0000,
            u.sa() == u.al as int + u.ah as int * 0x1_0000_0000,
            d == t.bl as int - t.al as int,
            e == u.bl as int - u.al as int,
            k == (u.bh as int - u.ah as int) - (t.bh as int - t.ah as int),
    ;
    assert(-1 <= k <= 1) by (nonlinear_arith)
        requires
            d - e == k * 0x1_0000_0000,
            -0x1_0000_0000 < d < 0x1_0000_0000,
            -0x1_0000_0000 < e < 0x1_0000_0000,
    ;
}

impl Tok {
    /// `low_len(self)`.
    #[inline(always)]
    pub fn low_len(&self) -> (r: u32)
        ensures
            r == low_len(*self),
    {
        self.bl.wrapping_sub(self.al)
    }

    pub open spec fn sa(&self) -> int {
        wide(self.al, self.ah)
    }

    pub open spec fn sb(&self) -> int {
        wide(self.bl, self.bh)
    }

    pub open spec fn sc(&self) -> int {
        wide(self.cl, self.ch)
    }

    /// The token with these fields.
    #[inline(always)]
    pub fn new(kind: Kind, f: u8, a: usize, b: usize, c: usize) -> (t: Tok)
        requires
            a <= MAX_POS,
            b <= MAX_POS,
            c <= MAX_POS,
        ensures
            t.kind == kind,
            t.f == f,
            t.sa() == a,
            t.sb() == b,
            t.sc() == c,
    {
        let (al, ah) = split(a as u64);
        let (bl, bh) = split(b as u64);
        let (cl, ch) = split(c as u64);
        Tok { kind, f, ah, al, bl, bh, ch, cl }
    }

    /// `a`: the span's start (a character reference's position).
    #[inline(always)]
    pub fn a(&self) -> (r: u64)
        ensures
            r == self.sa(),
    {
        join(self.al, self.ah)
    }

    /// `b`: the span's end (a character reference's character).
    #[inline(always)]
    pub fn b(&self) -> (r: u64)
        ensures
            r == self.sb(),
    {
        join(self.bl, self.bh)
    }

    /// `c`: a start tag's link to its end token, or an attribute
    /// default's entity count; 0 otherwise.
    #[inline(always)]
    pub fn c(&self) -> (r: u64)
        ensures
            r == self.sc(),
    {
        join(self.cl, self.ch)
    }
}

impl View for Tok {
    type V = XTok;

    open spec fn view(&self) -> XTok {
        let a = self.sa();
        let b = self.sb();
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
            Kind::AttDefault => XTok::AttDefault { start: a, end: b, kind: self.f as int, nents: self.sc() },
            Kind::EntityDecl => XTok::EntityDecl { start: a, end: b, pe: self.f != 0 },
            Kind::EntityValue => XTok::EntityValue { start: a, end: b },
            Kind::NData => XTok::NData { start: a, end: b },
            Kind::NotationDecl => XTok::NotationDecl { start: a, end: b },
            Kind::PERef => XTok::PERef { start: a, end: b },
            Kind::Comment => XTok::Comment { start: a, end: b },
            Kind::PI => XTok::PI { start: a, end: b },
            Kind::PIData => XTok::PIData { start: a, end: b },
            Kind::STag => XTok::STag { start: a, end: b, close: self.sc() },
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
        a <= MAX_POS,
        b <= MAX_POS,
    ensures
        t.kind == kind,
        t.sa() == a,
        t.sb() == b,
        t.f == f,
        t.sc() == 0,
{
    Tok::new(kind, f, a, b, 0)
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
            k < old(self)@.len() <= MAX_POS,
            old(self)@[k as int] is STag,
        ensures
            final(self)@ == close_at(old(self)@, k as int),
    {
        let n = self.toks.len();
        let t = self.toks[k];
        let ghost old_v = self@;
        let (cl, ch) = split((n - 1) as u64);
        self.toks.set(k, Tok { kind: t.kind, f: t.f, ah: t.ah, al: t.al, bl: t.bl, bh: t.bh, ch, cl });
        proof {
            assert(t@ == old_v[k as int]);
            assert(t.kind == Kind::STag);
            assert(final(self)@ =~= close_at(old_v, k as int));
        }
    }
}

} // verus!
