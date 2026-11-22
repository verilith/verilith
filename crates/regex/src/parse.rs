//! The pattern parser: RE2's syntax, proven to compute `syntax::parse`.
use crate::ast::*;
use crate::class::*;
use crate::data::*;
use crate::pike::decode;
use crate::spec::*;
use crate::syntax as sx;
use crate::syntax::{Flags, It, Out, Pat, St};
use verilith_core::utf8::*;
use vstd::array::array_as_slice;
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};

verus! {

/// Groups may nest this deep.
pub const MAX_NEST: usize = 250;

pub const MAX_REPEAT: usize = 1000;

/// The longest pattern, in bytes.
pub const MAX_PATTERN: usize = 0x1_0000;

#[derive(Clone, Copy, Debug)]
pub enum Error {
    /// The pattern is not valid UTF-8.
    BadUtf8,
    /// A syntax error at this byte offset.
    Syntax(usize),
    /// The pattern, or the program it compiles to, is too large or too deep.
    TooBig,
}

pub struct Parsed {
    pub ast: Ast,
    pub classes: Vec<Class>,
    /// Number of groups, counting group 0.
    pub ngroups: usize,
    /// Group names: (name, group number).
    pub names: Vec<(Vec<u8>, usize)>,
}

/// What the parser has built up besides the tree.
pub struct Ps {
    pub classes: Vec<Class>,
    pub ngroups: usize,
    pub names: Vec<(Vec<u8>, usize)>,
}

pub open spec fn names_v(v: Seq<(Vec<u8>, usize)>) -> Seq<(Seq<u8>, nat)> {
    Seq::new(v.len(), |k: int| (v[k].0@, v[k].1 as nat))
}

impl Ps {
    pub open spec fn ok(&self) -> bool {
        forall|k: int| 0 <= k < self.classes@.len() ==> (#[trigger] self.classes@[k]).wf()
    }

    pub open spec fn st(&self) -> St {
        St { ng: self.ngroups as nat, names: names_v(self.names@) }
    }
}

/// `c2` is `c1` with more classes.
pub open spec fn ext(c1: Seq<Class>, c2: Seq<Class>) -> bool {
    c1.len() <= c2.len() && forall|k: int| 0 <= k < c1.len() ==> c2[k] == c1[k]
}

/// The parser went from `a` to `b`: it only added classes and groups.
pub open spec fn grows(a: &Ps, b: &Ps) -> bool {
    ext(a.classes@, b.classes@) && a.ngroups <= b.ngroups && b.ok()
}

/// A tree the parser may hold: well-formed, naming only classes and
/// groups that exist.
pub open spec fn good(a: Ast, nc: int, ng: int) -> bool {
    a.wf() && a.bounded(nc, ng) && a.rep <= MAX_REPEAT
}

pub open spec fn itv(a: Ast, cl: Seq<Class>) -> It {
    It { re: a.re(cl), rep: a.rep as nat }
}

pub open spec fn its(v: Seq<Ast>, cl: Seq<Class>) -> Seq<It> {
    Seq::new(v.len(), |k: int| itv(v[k], cl))
}

pub open spec fn all_good(v: Seq<Ast>, nc: int, ng: int) -> bool {
    forall|k: int| 0 <= k < v.len() ==> good(#[trigger] v[k], nc, ng)
}

pub proof fn lemma_its_ext(v: Seq<Ast>, c1: Seq<Class>, c2: Seq<Class>, ng: int, ng2: int)
    requires
        all_good(v, c1.len() as int, ng),
        ext(c1, c2),
        ng <= ng2,
    ensures
        its(v, c2) == its(v, c1),
        all_good(v, c2.len() as int, ng2),
{
    assert forall|k: int| 0 <= k < v.len() implies itv(v[k], c2) == itv(v[k], c1) && good(
        #[trigger] v[k],
        c2.len() as int,
        ng2,
    ) by {
        v[k].lemma_re_ext(c1, c2, ng);
        v[k].lemma_bounded_mono(c1.len() as int, ng, c2.len() as int, ng2);
    }
    assert(its(v, c2) =~= its(v, c1));
}

fn is_at(pat: &[u8], p: usize, b: u8) -> (r: bool)
    ensures
        r == sx::at(pat@, p as int, b),
{
    p < pat.len() && pat[p] == b
}

fn chr_at(pat: &[u8], p: usize) -> (r: (u32, usize))
    requires
        p < pat@.len(),
    ensures
        (r.0, r.1 as int) == sx::chr(pat@, p as int),
        1 <= r.1 <= 4,
        p + r.1 <= pat@.len(),
        r.0 <= MAXCP || r.0 == u32::MAX,
{
    proof {
        if dec(pat@, p as int) is Some {
            verilith_text::utf::spec::lemma_dec8_roundtrip(pat@, p as int);
        }
    }
    decode(pat, p)
}

fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let n = a.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

fn find_b(pat: &[u8], p: usize, b: u8) -> (r: usize)
    requires
        p <= pat@.len(),
    ensures
        r == sx::find(pat@, p as int, b),
        p <= r <= pat@.len(),
{
    let n = pat.len();
    let mut q = p;
    while q < n && pat[q] != b
        invariant
            p <= q <= n,
            n == pat@.len(),
            sx::find(pat@, p as int, b) == sx::find(pat@, q as int, b),
        decreases n - q,
    {
        q += 1;
    }
    q
}

fn hexval(c: u32) -> (r: Option<u32>)
    ensures
        r == sx::hexval(c),
        r matches Some(v) ==> v < 16,
{
    if 0x30 <= c && c <= 0x39 {
        Some(c - 0x30)
    } else if 0x61 <= c && c <= 0x66 {
        Some(c - 0x61 + 10)
    } else if 0x41 <= c && c <= 0x46 {
        Some(c - 0x41 + 10)
    } else {
        None
    }
}

fn is_octal(pat: &[u8], p: usize) -> (r: bool)
    ensures
        r == sx::is_octal(pat@, p as int),
{
    p < pat.len() && 0x30 <= pat[p] && pat[p] <= 0x37
}

fn is_alnum(b: u8) -> (r: bool)
    ensures
        r == sx::is_alnum(b),
{
    (0x30 <= b && b <= 0x39) || (0x61 <= b && b <= 0x7A) || (0x41 <= b && b <= 0x5A)
}

/// An escape at `pos` (which holds the backslash) that denotes one code
/// point.
fn escape(pat: &[u8], pos: usize) -> (r: Result<(u32, usize), Error>)
    requires
        pat@.len() <= MAX_PATTERN,
    ensures
        match r {
            Ok((c, q)) => sx::escape(pat@, pos as int) == Some((c, q as int)) && c <= MAXCP && pos < q <= pat@.len(),
            Err(e) => !(e is TooBig) && sx::escape(pat@, pos as int) is None,
        },
{
    let n = pat.len();
    if pos >= n || pos + 1 >= n {
        return Err(Error::Syntax(pos));
    }
    let (c, l) = chr_at(pat, pos + 1);
    let p = pos + 1 + l;
    let oct = is_octal(pat, p);
    if 0x31 <= c && c <= 0x37 && !oct {
        return Err(Error::Syntax(pos));
    }
    if 0x30 <= c && c <= 0x37 {
        let c0 = c - 0x30;
        if oct {
            let c1 = c0 * 8 + (pat[p] - 0x30) as u32;
            if is_octal(pat, p + 1) {
                return Ok((c1 * 8 + (pat[p + 1] - 0x30) as u32, p + 2));
            }
            return Ok((c1, p + 1));
        }
        return Ok((c0, p));
    }
    if c == 0x78 {
        if p >= n {
            return Err(Error::Syntax(pos));
        }
        let (c1, l1) = chr_at(pat, p);
        let p1 = p + l1;
        if c1 == 0x7B {
            let mut code: u32 = 0;
            let mut nhex: usize = 0;
            let mut q = p1;
            loop
                invariant
                    n == pat@.len(),
                    n <= MAX_PATTERN,
                    pos < q <= n,
                    nhex <= q,
                    code <= MAXCP,
                    sx::escape(pat@, pos as int) == sx::hex_run(pat@, p1 as int, 0, 0),
                    sx::hex_run(pat@, p1 as int, 0, 0) == sx::hex_run(pat@, q as int, code, nhex as nat),
                decreases n - q,
            {
                if q >= n {
                    return Err(Error::Syntax(pos));
                }
                let (d, ld) = chr_at(pat, q);
                match hexval(d) {
                    Some(v) => {
                        if code * 16 + v > MAXCP {
                            return Err(Error::Syntax(pos));
                        }
                        code = code * 16 + v;
                        nhex += 1;
                        q += ld;
                    },
                    None => {
                        if d != 0x7D || nhex == 0 {
                            return Err(Error::Syntax(pos));
                        }
                        return Ok((code, q + ld));
                    },
                }
            }
        }
        if p1 >= n {
            return Err(Error::Syntax(pos));
        }
        let (c2, l2) = chr_at(pat, p1);
        let h1 = hexval(c1);
        let h2 = hexval(c2);
        return match (h1, h2) {
            (Some(a), Some(b)) => Ok((a * 16 + b, p1 + l2)),
            _ => Err(Error::Syntax(pos)),
        };
    }
    if c == 0x6E {
        return Ok((0x0A, p));
    }
    if c == 0x72 {
        return Ok((0x0D, p));
    }
    if c == 0x74 {
        return Ok((0x09, p));
    }
    if c == 0x61 {
        return Ok((0x07, p));
    }
    if c == 0x66 {
        return Ok((0x0C, p));
    }
    if c == 0x76 {
        return Ok((0x0B, p));
    }
    if c < 0x80 && !is_alnum(c as u8) {
        return Ok((c, p));
    }
    Err(Error::Syntax(pos))
}

fn from_ranges(rs: &[(u32, u32)]) -> (c: Class)
    requires
        forall|k: int| 0 <= k < rs@.len() ==> (#[trigger] rs@[k]).1 <= MAXCP,
    ensures
        c.wf(),
        c.set() == cs_ranges(rs@),
{
    let mut c = Class::new();
    c.add_ranges(rs);
    assert(c.set() =~= cs_ranges(rs@));
    c
}

fn range_class(lo: u32, hi: u32) -> (c: Class)
    requires
        hi <= MAXCP,
    ensures
        c.wf(),
        c.set() == cs_range(lo, hi),
{
    let mut c = Class::new();
    c.add(lo, hi);
    assert(c.set() =~= cs_range(lo, hi));
    c
}

/// What a group or class item denotes: `base`, folded if `fold`, then
/// complemented if `neg`.
fn item(base: Class, neg: bool, fold: bool) -> (c: Class)
    requires
        base.wf(),
    ensures
        c.wf(),
        c.set() == sx::item(base.set(), neg, fold),
{
    let c = if fold {
        base.fold()
    } else {
        base
    };
    if neg {
        c.negate()
    } else {
        c
    }
}

fn perl_d() -> (c: Class)
    ensures
        c.wf(),
        c.set() == cs_ranges(sx::perl_d()),
{
    let r = [(0x30u32, 0x39u32)];
    assert(r@ =~= sx::perl_d());
    from_ranges(array_as_slice(&r))
}

fn perl_s() -> (c: Class)
    ensures
        c.wf(),
        c.set() == cs_ranges(sx::perl_s()),
{
    let r = [(0x09u32, 0x0Au32), (0x0Cu32, 0x0Du32), (0x20u32, 0x20u32)];
    assert(r@ =~= sx::perl_s());
    from_ranges(array_as_slice(&r))
}

fn perl_w() -> (c: Class)
    ensures
        c.wf(),
        c.set() == cs_ranges(sx::perl_w()),
{
    let r = [(0x30u32, 0x39u32), (0x41u32, 0x5Au32), (0x5Fu32, 0x5Fu32), (0x61u32, 0x7Au32)];
    assert(r@ =~= sx::perl_w());
    from_ranges(array_as_slice(&r))
}

/// `\d \s \w \D \S \W` at `pos`.
fn perl(pat: &[u8], pos: usize, fl: Flags) -> (r: Option<Class>)
    requires
        pat@.len() <= MAX_PATTERN,
    ensures
        match r {
            Some(c) => c.wf() && sx::perl(pat@, pos as int, fl) == Some(c.set()) && pos + 2 <= pat@.len(),
            None => sx::perl(pat@, pos as int, fl) is None,
        },
{
    if !is_at(pat, pos, 0x5C) || pos + 1 >= pat.len() {
        return None;
    }
    let b = pat[pos + 1];
    if b == 0x64 {
        let r = perl_d();
        return Some(item(r, false, fl.i));
    }
    if b == 0x44 {
        let r = perl_d();
        return Some(item(r, true, fl.i));
    }
    if b == 0x73 {
        let r = perl_s();
        return Some(item(r, false, fl.i));
    }
    if b == 0x53 {
        let r = perl_s();
        return Some(item(r, true, fl.i));
    }
    if b == 0x77 {
        let r = perl_w();
        return Some(item(r, false, fl.i));
    }
    if b == 0x57 {
        let r = perl_w();
        return Some(item(r, true, fl.i));
    }
    None
}

/// The POSIX class `name` (between `[:` and `:]`, without a `^`).
fn posix(name: &[u8]) -> (r: Option<Class>)
    ensures
        match r {
            Some(c) => c.wf() && (sx::posix(name@) matches Some(rs) && c.set() == cs_ranges(rs)),
            None => sx::posix(name@) is None,
        },
{
    // alnum
    let w = [0x61u8, 0x6Cu8, 0x6Eu8, 0x75u8, 0x6Du8];
    assert(w@ =~= seq![0x61u8, 0x6Cu8, 0x6Eu8, 0x75u8, 0x6Du8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x30u32, 0x39u32), (0x41u32, 0x5Au32), (0x61u32, 0x7Au32)];
        assert(r@ =~= seq![(0x30u32, 0x39u32), (0x41u32, 0x5Au32), (0x61u32, 0x7Au32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // alpha
    let w = [0x61u8, 0x6Cu8, 0x70u8, 0x68u8, 0x61u8];
    assert(w@ =~= seq![0x61u8, 0x6Cu8, 0x70u8, 0x68u8, 0x61u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x41u32, 0x5Au32), (0x61u32, 0x7Au32)];
        assert(r@ =~= seq![(0x41u32, 0x5Au32), (0x61u32, 0x7Au32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // ascii
    let w = [0x61u8, 0x73u8, 0x63u8, 0x69u8, 0x69u8];
    assert(w@ =~= seq![0x61u8, 0x73u8, 0x63u8, 0x69u8, 0x69u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x00u32, 0x7Fu32)];
        assert(r@ =~= seq![(0x00u32, 0x7Fu32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // blank
    let w = [0x62u8, 0x6Cu8, 0x61u8, 0x6Eu8, 0x6Bu8];
    assert(w@ =~= seq![0x62u8, 0x6Cu8, 0x61u8, 0x6Eu8, 0x6Bu8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x09u32, 0x09u32), (0x20u32, 0x20u32)];
        assert(r@ =~= seq![(0x09u32, 0x09u32), (0x20u32, 0x20u32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // cntrl
    let w = [0x63u8, 0x6Eu8, 0x74u8, 0x72u8, 0x6Cu8];
    assert(w@ =~= seq![0x63u8, 0x6Eu8, 0x74u8, 0x72u8, 0x6Cu8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x00u32, 0x1Fu32), (0x7Fu32, 0x7Fu32)];
        assert(r@ =~= seq![(0x00u32, 0x1Fu32), (0x7Fu32, 0x7Fu32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // digit
    let w = [0x64u8, 0x69u8, 0x67u8, 0x69u8, 0x74u8];
    assert(w@ =~= seq![0x64u8, 0x69u8, 0x67u8, 0x69u8, 0x74u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x30u32, 0x39u32)];
        assert(r@ =~= seq![(0x30u32, 0x39u32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // graph
    let w = [0x67u8, 0x72u8, 0x61u8, 0x70u8, 0x68u8];
    assert(w@ =~= seq![0x67u8, 0x72u8, 0x61u8, 0x70u8, 0x68u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x21u32, 0x7Eu32)];
        assert(r@ =~= seq![(0x21u32, 0x7Eu32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // lower
    let w = [0x6Cu8, 0x6Fu8, 0x77u8, 0x65u8, 0x72u8];
    assert(w@ =~= seq![0x6Cu8, 0x6Fu8, 0x77u8, 0x65u8, 0x72u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x61u32, 0x7Au32)];
        assert(r@ =~= seq![(0x61u32, 0x7Au32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // print
    let w = [0x70u8, 0x72u8, 0x69u8, 0x6Eu8, 0x74u8];
    assert(w@ =~= seq![0x70u8, 0x72u8, 0x69u8, 0x6Eu8, 0x74u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x20u32, 0x7Eu32)];
        assert(r@ =~= seq![(0x20u32, 0x7Eu32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // punct
    let w = [0x70u8, 0x75u8, 0x6Eu8, 0x63u8, 0x74u8];
    assert(w@ =~= seq![0x70u8, 0x75u8, 0x6Eu8, 0x63u8, 0x74u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x21u32, 0x2Fu32), (0x3Au32, 0x40u32), (0x5Bu32, 0x60u32), (0x7Bu32, 0x7Eu32)];
        assert(r@ =~= seq![(0x21u32, 0x2Fu32), (0x3Au32, 0x40u32), (0x5Bu32, 0x60u32), (0x7Bu32, 0x7Eu32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // space
    let w = [0x73u8, 0x70u8, 0x61u8, 0x63u8, 0x65u8];
    assert(w@ =~= seq![0x73u8, 0x70u8, 0x61u8, 0x63u8, 0x65u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x09u32, 0x0Du32), (0x20u32, 0x20u32)];
        assert(r@ =~= seq![(0x09u32, 0x0Du32), (0x20u32, 0x20u32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // upper
    let w = [0x75u8, 0x70u8, 0x70u8, 0x65u8, 0x72u8];
    assert(w@ =~= seq![0x75u8, 0x70u8, 0x70u8, 0x65u8, 0x72u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x41u32, 0x5Au32)];
        assert(r@ =~= seq![(0x41u32, 0x5Au32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // word
    let w = [0x77u8, 0x6Fu8, 0x72u8, 0x64u8];
    assert(w@ =~= seq![0x77u8, 0x6Fu8, 0x72u8, 0x64u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x30u32, 0x39u32), (0x41u32, 0x5Au32), (0x5Fu32, 0x5Fu32), (0x61u32, 0x7Au32)];
        assert(r@ =~= seq![(0x30u32, 0x39u32), (0x41u32, 0x5Au32), (0x5Fu32, 0x5Fu32), (0x61u32, 0x7Au32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    // xdigit
    let w = [0x78u8, 0x64u8, 0x69u8, 0x67u8, 0x69u8, 0x74u8];
    assert(w@ =~= seq![0x78u8, 0x64u8, 0x69u8, 0x67u8, 0x69u8, 0x74u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        let r = [(0x30u32, 0x39u32), (0x41u32, 0x46u32), (0x61u32, 0x66u32)];
        assert(r@ =~= seq![(0x30u32, 0x39u32), (0x41u32, 0x46u32), (0x61u32, 0x66u32)]);
        return Some(from_ranges(array_as_slice(&r)));
    }
    None
}

/// The Unicode group called `name`.
fn named_set(name: &[u8]) -> (r: Option<Class>)
    ensures
        match r {
            Some(c) => c.wf() && sx::named_set(name@) == Some(c.set()),
            None => sx::named_set(name@) is None,
        },
{
    let w = [0x41u8, 0x6Eu8, 0x79u8];
    assert(w@ =~= seq![0x41u8, 0x6Eu8, 0x79u8]);
    if eq_bytes(name, array_as_slice(&w)) {
        return Some(range_class(0, MAXCP));
    }
    match find_group(name) {
        Some(g) => Some(Class::group(g)),
        None => None,
    }
}

/// `\pN`, `\p{Name}`, `\PN`, `\P{Name}`, `\p{^Name}` at `pos`.
fn unicode(pat: &[u8], pos: usize, fl: Flags) -> (r: Result<(Class, usize), Error>)
    requires
        pat@.len() <= MAX_PATTERN,
    ensures
        match r {
            Ok((c, q)) => c.wf() && sx::unicode(pat@, pos as int, fl) == Some((c.set(), q as int)) && pos < q
                <= pat@.len(),
            Err(e) => !(e is TooBig) && sx::unicode(pat@, pos as int, fl) is None,
        },
{
    let n = pat.len();
    if pos >= n || pos + 2 >= n {
        return Err(Error::Syntax(pos));
    }
    let neg0 = pat[pos + 1] == 0x50;
    let (c, l) = chr_at(pat, pos + 2);
    let q = find_b(pat, pos + 3, 0x7D);
    if c == 0x7B && q >= n {
        return Err(Error::Syntax(pos));
    }
    let a0 = if c == 0x7B {
        pos + 3
    } else {
        pos + 2
    };
    let b = if c == 0x7B {
        q
    } else {
        pos + 2 + l
    };
    let end = if c == 0x7B {
        q + 1
    } else {
        b
    };
    let caret = a0 < b && pat[a0] == 0x5E;
    let a = if caret {
        a0 + 1
    } else {
        a0
    };
    match named_set(slice_subrange(pat, a, b)) {
        Some(base) => Ok((item(base, neg0 != caret, fl.i), end)),
        None => Err(Error::Syntax(pos)),
    }
}

/// One character of a bracketed class at `pos`.
fn cc_char(pat: &[u8], pos: usize) -> (r: Result<(u32, usize), Error>)
    requires
        pat@.len() <= MAX_PATTERN,
    ensures
        match r {
            Ok((c, q)) => sx::cc_char(pat@, pos as int) == Some((c, q as int)) && c <= MAXCP && pos < q <= pat@.len(),
            Err(e) => !(e is TooBig) && sx::cc_char(pat@, pos as int) is None,
        },
{
    if pos >= pat.len() {
        return Err(Error::Syntax(pos));
    }
    if pat[pos] == 0x5C {
        return escape(pat, pos);
    }
    let (c, l) = chr_at(pat, pos);
    if c > MAXCP {
        return Err(Error::Syntax(pos));
    }
    Ok((c, pos + l))
}

fn find_colon(pat: &[u8], p: usize) -> (r: usize)
    requires
        pat@.len() <= MAX_PATTERN,
        p <= MAX_PATTERN + 8,
    ensures
        r == sx::find_colon(pat@, p as int),
        p <= r,
        r <= p || r + 1 <= pat@.len(),
{
    let n = pat.len();
    let mut q = p;
    while q + 1 < n && !(pat[q] == 0x3A && pat[q + 1] == 0x5D)
        invariant
            p <= q,
            q <= MAX_PATTERN + 8,
            q <= p || q + 1 <= n,
            n == pat@.len(),
            n <= MAX_PATTERN,
            sx::find_colon(pat@, p as int) == sx::find_colon(pat@, q as int),
        decreases n - q,
    {
        q += 1;
    }
    q
}

/// A bracketed class; `pos` holds the `[`.
#[verifier::rlimit(100)]
#[verifier::spinoff_prover]
fn bracket(pat: &[u8], pos: usize, fl: Flags) -> (r: Result<(Class, usize), Error>)
    requires
        pat@.len() <= MAX_PATTERN,
        pos < pat@.len(),
    ensures
        match r {
            Ok((c, q)) => c.wf() && sx::bracket(pat@, pos as int, fl) == Some((Re::Char(c.set()), q as int)) && pos
                < q <= pat@.len(),
            Err(e) => !(e is TooBig) && sx::bracket(pat@, pos as int, fl) is None,
        },
{
    let n = pat.len();
    let neg = is_at(pat, pos + 1, 0x5E);
    let p0 = if neg {
        pos + 2
    } else {
        pos + 1
    };
    let mut p = p0;
    let mut cl = Class::new();
    let mut first = true;
    let ghost goal = sx::cc_items(pat@, p0 as int, fl, ISet::<u32>::empty(), true);
    while p < n && (pat[p] != 0x5D || first)
        invariant
            n == pat@.len(),
            n <= MAX_PATTERN,
            pos < p,
            cl.wf(),
            sx::bracket(pat@, pos as int, fl) == (match goal {
                Some((c, r)) => Some((Re::Char(if neg { cs_neg(c) } else { c }), r + 1)),
                None => None,
            }),
            goal == sx::cc_items(pat@, p as int, fl, cl.set(), first),
        decreases n - p,
    {
        let q = find_colon(pat, p + 2);
        if p + 2 < n && pat[p] == 0x5B && pat[p + 1] == 0x3A && q + 1 < n {
            let caret = p + 2 < q && pat[p + 2] == 0x5E;
            let a = if caret {
                p + 3
            } else {
                p + 2
            };
            match posix(slice_subrange(pat, a, q)) {
                Some(base) => {
                    let it = item(base, caret, fl.i);
                    cl.add_class(&it);
                    p = q + 2;
                },
                None => {
                    return Err(Error::Syntax(p));
                },
            }
        } else if p + 2 < n && pat[p] == 0x5C && (pat[p + 1] == 0x70 || pat[p + 1] == 0x50) {
            match unicode(pat, p, fl) {
                Ok((c, r)) => {
                    cl.add_class(&c);
                    p = r;
                },
                Err(e) => {
                    return Err(e);
                },
            }
        } else {
            match perl(pat, p, fl) {
                Some(c) => {
                    cl.add_class(&c);
                    p = p + 2;
                },
                None => {
                    let (lo, r) = match cc_char(pat, p) {
                        Ok(v) => v,
                        Err(e) => {
                            return Err(e);
                        },
                    };
                    if r + 1 < n && pat[r] == 0x2D && pat[r + 1] != 0x5D {
                        let (hi, r2) = match cc_char(pat, r + 1) {
                            Ok(v) => v,
                            Err(e) => {
                                return Err(e);
                            },
                        };
                        if hi < lo {
                            return Err(Error::Syntax(p));
                        }
                        let it = item(range_class(lo, hi), false, fl.i);
                        cl.add_class(&it);
                        p = r2;
                    } else {
                        let it = item(range_class(lo, lo), false, fl.i);
                        cl.add_class(&it);
                        p = r;
                    }
                },
            }
        }
        first = false;
    }
    if p >= n {
        return Err(Error::Syntax(pos));
    }
    let cl = if neg {
        cl.negate()
    } else {
        cl
    };
    Ok((cl, p + 1))
}

fn in_group(name: &[u8], c: u32) -> (r: bool)
    ensures
        r == sx::group_set(name@).contains(c),
{
    match find_group(name) {
        Some(g) => Class::group(g).contains(c),
        None => false,
    }
}

/// Whether `c` may appear in a group name.
fn word_char(c: u32) -> (r: bool)
    ensures
        r == sx::word_char(c),
{
    let w = [0x4Cu8, 0x75u8];
    assert(w@ =~= seq![0x4Cu8, 0x75u8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x4Cu8, 0x6Cu8];
    assert(w@ =~= seq![0x4Cu8, 0x6Cu8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x4Cu8, 0x74u8];
    assert(w@ =~= seq![0x4Cu8, 0x74u8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x4Cu8, 0x6Du8];
    assert(w@ =~= seq![0x4Cu8, 0x6Du8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x4Cu8, 0x6Fu8];
    assert(w@ =~= seq![0x4Cu8, 0x6Fu8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x4Eu8, 0x6Cu8];
    assert(w@ =~= seq![0x4Eu8, 0x6Cu8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x4Du8, 0x6Eu8];
    assert(w@ =~= seq![0x4Du8, 0x6Eu8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x4Du8, 0x63u8];
    assert(w@ =~= seq![0x4Du8, 0x63u8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x4Eu8, 0x64u8];
    assert(w@ =~= seq![0x4Eu8, 0x64u8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    let w = [0x50u8, 0x63u8];
    assert(w@ =~= seq![0x50u8, 0x63u8]);
    if in_group(array_as_slice(&w), c) {
        return true;
    }
    false
}


pub open spec fn on(m: Option<usize>) -> Option<nat> {
    match m {
        Some(v) => Some(v as nat),
        None => None,
    }
}

/// `b` is `a` with more classes; the groups are the same.
pub open spec fn same(a: &Ps, b: &Ps) -> bool {
    ext(a.classes@, b.classes@) && b.ok() && b.ngroups == a.ngroups && b.names == a.names
}

pub proof fn lemma_ext_trans(a: Seq<Class>, b: Seq<Class>, c: Seq<Class>)
    requires
        ext(a, b),
        ext(b, c),
    ensures
        ext(a, c),
{
    assert forall|k: int| 0 <= k < a.len() implies c[k] == a[k] by {
        assert(b[k] == a[k]);
        assert(c[k] == b[k]);
    }
}

pub proof fn lemma_node(a: Ast, cl: Seq<Class>, nc: int, ng: int)
    ensures
        match a.node {
            Node::Empty => a.re(cl) == Re::Empty,
            Node::Char(c) => a.re(cl) == Re::Char(cl[c as int].set()) && a.bounded(nc, ng) == (c < nc),
            Node::Look(k) => a.re(cl) == Re::Look(k),
            Node::Group(k, x) => a.re(cl) == Re::Group(k as nat, Box::new(x.re(cl))) && a.bounded(nc, ng) == (k < ng
                && x.bounded(nc, ng)),
            Node::Cat(x, y) => a.re(cl) == Re::Cat(Box::new(x.re(cl)), Box::new(y.re(cl))) && a.bounded(nc, ng) == (
            x.bounded(nc, ng) && y.bounded(nc, ng)),
            Node::Alt(x, y) => a.re(cl) == Re::Alt(Box::new(x.re(cl)), Box::new(y.re(cl))) && a.bounded(nc, ng) == (
            x.bounded(nc, ng) && y.bounded(nc, ng)),
            Node::Opt(x, g) => a.re(cl) == Re::Opt(Box::new(x.re(cl)), g) && a.bounded(nc, ng) == x.bounded(nc, ng),
            Node::Plus(x, g) => a.re(cl) == Re::Plus(Box::new(x.re(cl)), g) && a.bounded(nc, ng) == x.bounded(nc, ng),
        },
{
}

/// The same for `x*`, which is two nodes.
pub proof fn lemma_star(a: Ast, x: Ast, greedy: bool, cl: Seq<Class>, nc: int, ng: int)
    requires
        a.node matches Node::Opt(p, g) && g == greedy && p.node == Node::Plus(Box::new(x), greedy),
    ensures
        a.re(cl) == Re::Opt(Box::new(Re::Plus(Box::new(x.re(cl)), greedy)), greedy),
        a.bounded(nc, ng) == x.bounded(nc, ng),
{
    match a.node {
        Node::Opt(p, g) => {
            lemma_node(a, cl, nc, ng);
            lemma_node(*p, cl, nc, ng);
        },
        _ => {},
    }
}

fn some(o: Option<Ast>) -> (r: Result<Ast, Error>)
    ensures
        match r {
            Ok(a) => o == Some(a),
            Err(e) => e is TooBig && o is None,
        },
{
    match o {
        Some(a) => Ok(a),
        None => Err(Error::TooBig),
    }
}

/// A count at `pos`.
fn integer(pat: &[u8], pos: usize) -> (r: Option<(usize, usize)>)
    requires
        pat@.len() <= MAX_PATTERN,
    ensures
        match r {
            Some((v, q)) => sx::integer(pat@, pos as int) == Some((v as nat, q as int)) && pos < q <= pat@.len() && v
                <= 1000000000,
            None => sx::integer(pat@, pos as int) is None,
        },
{
    let n = pat.len();
    if pos >= n || !(0x30 <= pat[pos] && pat[pos] <= 0x39) {
        return None;
    }
    if pos + 1 < n && pat[pos] == 0x30 && 0x30 <= pat[pos + 1] && pat[pos + 1] <= 0x39 {
        return None;
    }
    let mut q = pos;
    let mut v: usize = 0;
    while q < n && 0x30 <= pat[q] && pat[q] <= 0x39
        invariant
            n == pat@.len(),
            n <= MAX_PATTERN,
            pos <= q <= n,
            v <= 1000000000,
            q == pos ==> v == 0,
            sx::integer(pat@, pos as int) == sx::digits(pat@, q as int, v as nat),
        decreases n - q,
    {
        if v >= 100000000 {
            return None;
        }
        v = v * 10 + (pat[q] - 0x30) as usize;
        q += 1;
    }
    Some((v, q))
}

/// `{n}`, `{n,}` or `{n,m}` at `pos`.
fn counts(pat: &[u8], pos: usize) -> (r: Option<(usize, Option<usize>, usize)>)
    requires
        pat@.len() <= MAX_PATTERN,
    ensures
        match r {
            Some((lo, hi, q)) => sx::counts(pat@, pos as int) == Some((lo as nat, on(hi), q as int)) && pos < q
                <= pat@.len(),
            None => sx::counts(pat@, pos as int) is None,
        },
{
    if !is_at(pat, pos, 0x7B) {
        return None;
    }
    let (lo, p) = match integer(pat, pos + 1) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    if is_at(pat, p, 0x7D) {
        return Some((lo, Some(lo), p + 1));
    }
    if !is_at(pat, p, 0x2C) {
        return None;
    }
    if is_at(pat, p + 1, 0x7D) {
        return Some((lo, None, p + 2));
    }
    let (hi, q) = match integer(pat, p + 1) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    if is_at(pat, q, 0x7D) {
        Some((lo, Some(hi), q + 1))
    } else {
        None
    }
}

/// A repetition operator at `p`.
fn rep_op(pat: &[u8], p: usize) -> (r: Option<(usize, Option<usize>, usize)>)
    requires
        pat@.len() <= MAX_PATTERN,
        p < pat@.len(),
    ensures
        match r {
            Some((lo, hi, q)) => sx::rep_op(pat@, p as int) == Some((lo as nat, on(hi), q as int)) && p < q
                <= pat@.len(),
            None => sx::rep_op(pat@, p as int) is None,
        },
{
    let b = pat[p];
    if b == 0x2A {
        Some((0, None, p + 1))
    } else if b == 0x2B {
        Some((1, None, p + 1))
    } else if b == 0x3F {
        Some((0, Some(1), p + 1))
    } else {
        counts(pat, p)
    }
}

/// `x{min,max}`.
fn repeat(
    x: &Ast,
    min: usize,
    max: Option<usize>,
    greedy: bool,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
) -> (r: Result<Ast, Error>)
    requires
        x.wf(),
        x.bounded(nc, ng),
        min <= 1000,
        max matches Some(m) ==> min <= m <= 1000,
    ensures
        match r {
            Ok(a) => a.wf() && a.bounded(nc, ng) && a.re(cl) == sx::repeat(x.re(cl), min as nat, on(max), greedy),
            Err(e) => e is TooBig,
        },
{
    let ghost xr = x.re(cl);
    let (acc0, cnt) = match max {
        None => {
            if min == 0 {
                let a = some(Ast::star(x.dup(), greedy))?;
                proof {
                    lemma_star(a, *x, greedy, cl, nc, ng);
                }
                (a, 0)
            } else {
                let a = some(Ast::plus(x.dup(), greedy))?;
                proof {
                    lemma_node(a, cl, nc, ng);
                }
                (a, min - 1)
            }
        },
        Some(m) => {
            let mut acc = Ast::empty();
            let mut k = min;
            while k < m
                invariant
                    min <= k <= m,
                    x.wf(),
                    x.bounded(nc, ng),
                    xr == x.re(cl),
                    acc.wf(),
                    acc.bounded(nc, ng),
                    acc.re(cl) == sx::opt_tail(xr, (k - min) as nat, greedy),
                decreases m - k,
            {
                let c = some(Ast::cat(x.dup(), acc))?;
                proof {
                    lemma_node(c, cl, nc, ng);
                }
                acc = some(Ast::opt(c, greedy))?;
                proof {
                    lemma_node(acc, cl, nc, ng);
                }
                k += 1;
            }
            (acc, min)
        },
    };
    let mut acc = acc0;
    let ghost tail = acc.re(cl);
    let mut j: usize = 0;
    assert(sx::repeat(xr, min as nat, on(max), greedy) == sx::copies(xr, cnt as nat, tail));
    while j < cnt
        invariant
            j <= cnt,
            x.wf(),
            x.bounded(nc, ng),
            xr == x.re(cl),
            acc.wf(),
            acc.bounded(nc, ng),
            acc.re(cl) == sx::copies(xr, j as nat, tail),
        decreases cnt - j,
    {
        acc = some(Ast::cat(x.dup(), acc))?;
        proof {
            lemma_node(acc, cl, nc, ng);
        }
        j += 1;
    }
    Ok(acc)
}

/// The repetition `b` applied to `x`.
fn apply_rep(
    x: Ast,
    b: u8,
    min: usize,
    max: Option<usize>,
    greedy: bool,
    pos: usize,
    Ghost(cl): Ghost<Seq<Class>>,
    Ghost(nc): Ghost<int>,
    Ghost(ng): Ghost<int>,
) -> (r: Result<Ast, Error>)
    requires
        good(x, nc, ng),
    ensures
        match r {
            Ok(a) => good(a, nc, ng) && sx::apply_rep(itv(x, cl), b, min as nat, on(max), greedy) == Some(itv(a, cl)),
            Err(e) => e is TooBig || sx::apply_rep(itv(x, cl), b, min as nat, on(max), greedy) is None,
        },
{
    if b == 0x2A {
        let a = some(Ast::star(x, greedy))?;
        proof {
            lemma_star(a, x, greedy, cl, nc, ng);
        }
        Ok(a)
    } else if b == 0x3F {
        let a = some(Ast::opt(x, greedy))?;
        proof {
            lemma_node(a, cl, nc, ng);
        }
        Ok(a)
    } else if b == 0x2B {
        let a = some(Ast::plus(x, greedy))?;
        proof {
            lemma_node(a, cl, nc, ng);
        }
        Ok(a)
    } else {
        let m = match max {
            Some(m) => m,
            None => min,
        };
        if min > 1000 || m > 1000 || m < min {
            return Err(Error::Syntax(pos));
        }
        assert(x.rep * m <= 1000 * 1000) by (nonlinear_arith)
            requires
                x.rep <= 1000,
                m <= 1000,
        ;
        assert(m == 1 ==> x.rep * m == x.rep) by (nonlinear_arith);
        let rep = if m > 0 {
            x.rep * m
        } else {
            x.rep
        };
        if m >= 2 && rep > 1000 {
            return Err(Error::Syntax(pos));
        }
        let y = repeat(&x, min, max, greedy, Ghost(cl), Ghost(nc), Ghost(ng))?;
        Ok(y.set_rep(rep))
    }
}

/// The pieces joined as a balanced tree.
fn tree(items: Vec<Ast>, alt: bool, Ghost(cl): Ghost<Seq<Class>>, Ghost(nc): Ghost<int>, Ghost(ng): Ghost<int>) -> (r:
    Result<Ast, Error>)
    requires
        all_good(items@, nc, ng),
    ensures
        match r {
            Ok(a) => good(a, nc, ng) && itv(a, cl) == sx::tree(its(items@, cl), alt),
            Err(e) => e is TooBig,
        },
    decreases items@.len(),
{
    let mut items = items;
    let ghost all = items@;
    let len = items.len();
    if len == 0 {
        return Ok(Ast::empty());
    }
    if len == 1 {
        let a = items.pop().unwrap();
        assert(a == all[0]);
        return Ok(a);
    }
    let mid = len / 2;
    let right = items.split_off(mid);
    proof {
        assert(its(items@, cl) =~= its(all, cl).subrange(0, mid as int));
        assert(its(right@, cl) =~= its(all, cl).subrange(mid as int, len as int));
        assert forall|k: int| 0 <= k < items@.len() implies good(#[trigger] items@[k], nc, ng) by {
            assert(items@[k] == all[k]);
        }
        assert forall|k: int| 0 <= k < right@.len() implies good(#[trigger] right@[k], nc, ng) by {
            assert(right@[k] == all[k + mid]);
        }
    }
    let x = tree(items, alt, Ghost(cl), Ghost(nc), Ghost(ng))?;
    let y = tree(right, alt, Ghost(cl), Ghost(nc), Ghost(ng))?;
    let a = if alt {
        some(Ast::alt(x, y))?
    } else {
        some(Ast::cat(x, y))?
    };
    proof {
        lemma_node(a, cl, nc, ng);
    }
    Ok(a)
}

/// The flags of `(?flags)` or `(?flags:` from `q0`.
fn flags(pat: &[u8], q0: usize, fl: Flags) -> (r: Option<(Flags, usize, bool)>)
    requires
        pat@.len() <= MAX_PATTERN,
        q0 <= MAX_PATTERN + 8,
    ensures
        match r {
            Some((nf, q, c)) => sx::flags(pat@, q0 as int, fl, false, false) == Some((nf, q as int, c)) && q0 < q
                <= pat@.len(),
            None => sx::flags(pat@, q0 as int, fl, false, false) is None,
        },
{
    let n = pat.len();
    let mut q = q0;
    let mut nf = fl;
    let mut neg = false;
    let mut saw = false;
    loop
        invariant
            n == pat@.len(),
            n <= MAX_PATTERN,
            q0 <= q,
            sx::flags(pat@, q0 as int, fl, false, false) == sx::flags(pat@, q as int, nf, neg, saw),
        decreases n - q,
    {
        if q >= n {
            return None;
        }
        let b = pat[q];
        if b == 0x69 {
            nf = Flags { i: !neg, ..nf };
            saw = true;
        } else if b == 0x6D {
            nf = Flags { m: !neg, ..nf };
            saw = true;
        } else if b == 0x73 {
            nf = Flags { s: !neg, ..nf };
            saw = true;
        } else if b == 0x55 {
            nf = Flags { u: !neg, ..nf };
            saw = true;
        } else if b == 0x2D {
            if neg {
                return None;
            }
            neg = true;
            saw = false;
        } else if b == 0x3A || b == 0x29 {
            if neg && !saw {
                return None;
            }
            return Some((nf, q + 1, b == 0x3A));
        } else {
            return None;
        }
        q += 1;
    }
}

fn named_start(pat: &[u8], p: usize) -> (r: Option<usize>)
    requires
        pat@.len() <= MAX_PATTERN,
        p < pat@.len(),
    ensures
        match r {
            Some(a) => sx::named_start(pat@, p as int) == Some(a as int) && p < a <= pat@.len(),
            None => sx::named_start(pat@, p as int) is None,
        },
{
    if is_at(pat, p + 2, 0x50) && is_at(pat, p + 3, 0x3C) {
        Some(p + 4)
    } else if is_at(pat, p + 2, 0x3C) && !is_at(pat, p + 3, 0x3D) && !is_at(pat, p + 3, 0x21) {
        Some(p + 3)
    } else {
        None
    }
}

fn name_chars(pat: &[u8], a: usize, b: usize) -> (r: bool)
    requires
        b <= pat@.len(),
        pat@.len() <= MAX_PATTERN,
    ensures
        r == sx::name_chars(pat@, a as int, b as int),
{
    let mut p = a;
    if a >= b {
        return true;
    }
    while p < b
        invariant
            b <= pat@.len(),
            p <= pat@.len(),
            pat@.len() <= MAX_PATTERN,
            sx::name_chars(pat@, a as int, b as int) == sx::name_chars(pat@, p as int, b as int),
        decreases pat@.len() - p,
    {
        let (c, l) = chr_at(pat, p);
        if !word_char(c) {
            return false;
        }
        p += l;
    }
    true
}

fn has_name(names: &Vec<(Vec<u8>, usize)>, name: &[u8]) -> (r: bool)
    ensures
        r == sx::has_name(names_v(names@), name@),
{
    let n = names.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            n == names@.len(),
            forall|k: int| 0 <= k < i ==> (#[trigger] names_v(names@)[k]).0 != name@,
        decreases n - i,
    {
        if eq_bytes(names[i].0.as_slice(), name) {
            assert(names_v(names@)[i as int].0 == name@);
            return true;
        }
        i += 1;
    }
    false
}

/// A new leaf matching the class `c`.
fn leaf(ps: &mut Ps, c: Class) -> (a: Ast)
    requires
        old(ps).ok(),
        c.wf(),
    ensures
        same(old(ps), final(ps)),
        a.wf(),
        a.rep == 1,
        a.bounded(final(ps).classes@.len() as int, final(ps).ngroups as int),
        a.re(final(ps).classes@) == Re::Char(c.set()),
{
    let k = ps.classes.len();
    ps.classes.push(c);
    let a = Ast::chr(k);
    proof {
        lemma_node(a, ps.classes@, ps.classes@.len() as int, ps.ngroups as int);
    }
    a
}

/// One character, class or assertion at `pos`.
fn atom(pat: &[u8], pos: usize, fl: Flags, ps: &mut Ps) -> (r: Result<(Ast, usize), Error>)
    requires
        pat@.len() <= MAX_PATTERN,
        pos < pat@.len(),
        old(ps).ok(),
    ensures
        match r {
            Ok((a, q)) => same(old(ps), final(ps)) && a.wf() && a.rep == 1 && a.bounded(
                final(ps).classes@.len() as int,
                final(ps).ngroups as int,
            ) && pos < q <= pat@.len() && sx::atom(pat@, pos as int, fl) == Some(
                (a.re(final(ps).classes@), q as int),
            ),
            Err(e) => e is TooBig || sx::atom(pat@, pos as int, fl) is None,
        },
{
    let b = pat[pos];
    if b == 0x5B {
        let (c, q) = bracket(pat, pos, fl)?;
        return Ok((leaf(ps, c), q));
    }
    if b == 0x2E {
        let mut c = Class::new();
        if fl.s {
            c.add(0, MAXCP);
            assert(c.set() =~= cs_range(0, MAXCP));
        } else {
            c.add(0, 9);
            c.add(11, MAXCP);
            assert(c.set() =~= cs_union(cs_range(0, 9), cs_range(11, MAXCP)));
        }
        return Ok((leaf(ps, c), pos + 1));
    }
    if b == 0x5E {
        return Ok((Ast::look(if fl.m { Look::StartLine } else { Look::Start }), pos + 1));
    }
    if b == 0x24 {
        return Ok((Ast::look(if fl.m { Look::EndLine } else { Look::End }), pos + 1));
    }
    if b == 0x5C {
        if is_at(pat, pos + 1, 0x62) {
            return Ok((Ast::look(Look::Word), pos + 2));
        }
        if is_at(pat, pos + 1, 0x42) {
            return Ok((Ast::look(Look::NotWord), pos + 2));
        }
        if is_at(pat, pos + 1, 0x41) {
            return Ok((Ast::look(Look::Start), pos + 2));
        }
        if is_at(pat, pos + 1, 0x7A) {
            return Ok((Ast::look(Look::End), pos + 2));
        }
        if is_at(pat, pos + 1, 0x70) || is_at(pat, pos + 1, 0x50) {
            let (c, q) = unicode(pat, pos, fl)?;
            return Ok((leaf(ps, c), q));
        }
        match perl(pat, pos, fl) {
            Some(c) => {
                return Ok((leaf(ps, c), pos + 2));
            },
            None => {
                let (c, q) = escape(pat, pos)?;
                let cls = item(range_class(c, c), false, fl.i);
                return Ok((leaf(ps, cls), q));
            },
        }
    }
    let (c, l) = chr_at(pat, pos);
    if c > MAXCP {
        return Err(Error::Syntax(pos));
    }
    let cls = item(range_class(c, c), false, fl.i);
    Ok((leaf(ps, cls), pos + l))
}

/// The literal characters of `\Q...\E` from `pos`, added to `items`.
fn quote(pat: &[u8], pos: usize, fl: Flags, ps: &mut Ps, items: &mut Vec<Ast>) -> (r: Result<usize, Error>)
    requires
        pat@.len() <= MAX_PATTERN,
        pos <= pat@.len(),
        old(ps).ok(),
        all_good(old(items)@, old(ps).classes@.len() as int, old(ps).ngroups as int),
    ensures
        match r {
            Ok(q) => same(old(ps), final(ps)) && all_good(
                final(items)@,
                final(ps).classes@.len() as int,
                final(ps).ngroups as int,
            ) && pos <= q <= pat@.len() && sx::quote(pat@, pos as int, fl, its(old(items)@, old(ps).classes@))
                == Some((its(final(items)@, final(ps).classes@), q as int)),
            Err(e) => e is TooBig || sx::quote(pat@, pos as int, fl, its(old(items)@, old(ps).classes@)) is None,
        },
{
    let n = pat.len();
    let mut q = pos;
    let ghost goal = sx::quote(pat@, pos as int, fl, its(items@, ps.classes@));
    let ghost cl0 = ps.classes@;
    loop
        invariant
            n == pat@.len(),
            n <= MAX_PATTERN,
            pos <= q <= n,
            cl0 == old(ps).classes@,
            goal == sx::quote(pat@, pos as int, fl, its(old(items)@, old(ps).classes@)),
            ext(cl0, ps.classes@),
            ps.ok(),
            ps.ngroups == old(ps).ngroups,
            ps.names == old(ps).names,
            all_good(items@, ps.classes@.len() as int, ps.ngroups as int),
            goal == sx::quote(pat@, q as int, fl, its(items@, ps.classes@)),
        decreases n - q,
    {
        if q >= n {
            return Ok(q);
        }
        if pat[q] == 0x5C && is_at(pat, q + 1, 0x45) {
            return Ok(q + 2);
        }
        let (c, l) = chr_at(pat, q);
        if c > MAXCP {
            return Err(Error::Syntax(q));
        }
        let ghost c1 = ps.classes@;
        let ghost v1 = items@;
        let cls = item(range_class(c, c), false, fl.i);
        let a = leaf(ps, cls);
        proof {
            lemma_its_ext(v1, c1, ps.classes@, ps.ngroups as int, ps.ngroups as int);
            lemma_ext_trans(cl0, c1, ps.classes@);
        }
        items.push(a);
        assert(its(items@, ps.classes@) =~= its(v1, c1).push(It { re: Re::Char(sx::lit(c, fl)), rep: 1 }));
        q += l;
    }
}

/// Alternatives from `pos` up to the end of the pattern or an unmatched
/// `)`.
fn alt(pat: &[u8], pos: usize, fl: Flags, ps: &mut Ps, depth: usize) -> (r: Result<(Ast, usize, Flags), Error>)
    requires
        pat@.len() <= MAX_PATTERN,
        pos <= pat@.len(),
        old(ps).ok(),
        old(ps).ngroups <= pos + 1,
        depth <= MAX_NEST,
    ensures
        match r {
            Ok((a, q, f)) => grows(old(ps), final(ps)) && good(
                a,
                final(ps).classes@.len() as int,
                final(ps).ngroups as int,
            ) && pos <= q <= pat@.len() && final(ps).ngroups <= q + 1 && sx::alts(
                pat@,
                pos as int,
                fl,
                old(ps).st(),
                Seq::empty(),
            ) == Some(Out { it: itv(a, final(ps).classes@), pos: q as int, fl: f, st: final(ps).st() }),
            Err(e) => e is TooBig || sx::alts(pat@, pos as int, fl, old(ps).st(), Seq::empty()) is None,
        },
    decreases pat@.len() - pos, 3int,
{
    let n = pat.len();
    let ghost goal = sx::alts(pat@, pos as int, fl, ps.st(), Seq::empty());
    let ghost cl0 = ps.classes@;
    let ghost ng0 = ps.ngroups;
    let mut alts: Vec<Ast> = Vec::new();
    let mut p = pos;
    let mut f = fl;
    assert(its(alts@, ps.classes@) =~= Seq::empty());
    loop
        invariant
            n == pat@.len(),
            n <= MAX_PATTERN,
            pos <= p <= n,
            depth <= MAX_NEST,
            ps.ok(),
            cl0 == old(ps).classes@,
            ng0 == old(ps).ngroups,
            goal == sx::alts(pat@, pos as int, fl, old(ps).st(), Seq::empty()),
            ext(cl0, ps.classes@),
            ng0 <= ps.ngroups,
            ps.ngroups <= p + 1,
            all_good(alts@, ps.classes@.len() as int, ps.ngroups as int),
            goal == sx::alts(pat@, p as int, f, ps.st(), its(alts@, ps.classes@)),
        decreases n - p,
    {
        let ghost c1 = ps.classes@;
        let ghost g1 = ps.ngroups;
        let ghost v1 = alts@;
        let (a, q, f2) = cat(pat, p, f, ps, depth)?;
        proof {
            lemma_its_ext(v1, c1, ps.classes@, g1 as int, ps.ngroups as int);
            lemma_ext_trans(cl0, c1, ps.classes@);
        }
        alts.push(a);
        assert(its(alts@, ps.classes@) =~= its(v1, c1).push(itv(a, ps.classes@)));
        if q < n && pat[q] == 0x7C {
            p = q + 1;
            f = f2;
        } else {
            let t = tree(alts, true, Ghost(ps.classes@), Ghost(ps.classes@.len() as int), Ghost(ps.ngroups as int))?;
            return Ok((t, q, f2));
        }
    }
}

/// A concatenation from `pos` up to `|`, `)` or the end.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
fn cat(pat: &[u8], pos: usize, fl: Flags, ps: &mut Ps, depth: usize) -> (r: Result<(Ast, usize, Flags), Error>)
    requires
        pat@.len() <= MAX_PATTERN,
        pos <= pat@.len(),
        old(ps).ok(),
        old(ps).ngroups <= pos + 1,
        depth <= MAX_NEST,
    ensures
        match r {
            Ok((a, q, f)) => grows(old(ps), final(ps)) && good(
                a,
                final(ps).classes@.len() as int,
                final(ps).ngroups as int,
            ) && pos <= q <= pat@.len() && final(ps).ngroups <= q + 1 && sx::items(
                pat@,
                pos as int,
                fl,
                old(ps).st(),
                Seq::empty(),
                false,
            ) == Some(Out { it: itv(a, final(ps).classes@), pos: q as int, fl: f, st: final(ps).st() }),
            Err(e) => e is TooBig || sx::items(pat@, pos as int, fl, old(ps).st(), Seq::empty(), false) is None,
        },
    decreases pat@.len() - pos, 1int,
{
    let n = pat.len();
    let ghost goal = sx::items(pat@, pos as int, fl, ps.st(), Seq::empty(), false);
    let ghost cl0 = ps.classes@;
    let ghost ng0 = ps.ngroups;
    let mut items: Vec<Ast> = Vec::new();
    let mut p = pos;
    let mut f = fl;
    let mut after_rep = false;
    assert(its(items@, ps.classes@) =~= Seq::empty());
    loop
        invariant
            n == pat@.len(),
            n <= MAX_PATTERN,
            pos <= p <= n,
            depth <= MAX_NEST,
            ps.ok(),
            cl0 == old(ps).classes@,
            ng0 == old(ps).ngroups,
            goal == sx::items(pat@, pos as int, fl, old(ps).st(), Seq::empty(), false),
            ext(cl0, ps.classes@),
            ng0 <= ps.ngroups,
            ps.ngroups <= p + 1,
            all_good(items@, ps.classes@.len() as int, ps.ngroups as int),
            goal == sx::items(pat@, p as int, f, ps.st(), its(items@, ps.classes@), after_rep),
        decreases n - p,
    {
        if p >= n || pat[p] == 0x7C || pat[p] == 0x29 {
            let t = tree(items, false, Ghost(ps.classes@), Ghost(ps.classes@.len() as int), Ghost(ps.ngroups as int))?;
            return Ok((t, p, f));
        }
        let b = pat[p];
        let ghost c1 = ps.classes@;
        let ghost g1 = ps.ngroups;
        let ghost v1 = items@;
        match rep_op(pat, p) {
            Some((min, max, q0)) => {
                let lazy = is_at(pat, q0, 0x3F);
                let q = if lazy {
                    q0 + 1
                } else {
                    q0
                };
                let greedy = f.u == lazy;
                if after_rep || items.len() == 0 {
                    return Err(Error::Syntax(p));
                }
                let x = items.pop().unwrap();
                assert(x == v1.last());
                assert(itv(x, c1) == its(v1, c1).last());
                let y = apply_rep(
                    x,
                    b,
                    min,
                    max,
                    greedy,
                    p,
                    Ghost(ps.classes@),
                    Ghost(ps.classes@.len() as int),
                    Ghost(ps.ngroups as int),
                )?;
                items.push(y);
                assert(its(items@, c1) =~= its(v1, c1).drop_last().push(itv(y, c1)));
                p = q;
                after_rep = true;
            },
            None => {
                if b == 0x28 {
                    if is_at(pat, p + 1, 0x3F) {
                        match named_start(pat, p) {
                            Some(a) => {
                                let q = find_b(pat, a, 0x3E);
                                if q >= n || a >= q || !name_chars(pat, a, q) {
                                    return Err(Error::Syntax(p));
                                }
                                let name = slice_subrange(pat, a, q);
                                if has_name(&ps.names, name) {
                                    return Err(Error::Syntax(p));
                                }
                                let ghost nm = ps.names@;
                                let k = ps.ngroups;
                                ps.names.push((slice_to_vec(name), k));
                                assert(names_v(ps.names@) =~= names_v(nm).push((pat@.subrange(a as int, q as int), k as nat)));
                                let (it, r) = group(pat, q + 1, f, ps, true, depth)?;
                                proof {
                                    lemma_its_ext(v1, c1, ps.classes@, g1 as int, ps.ngroups as int);
                                    lemma_ext_trans(cl0, c1, ps.classes@);
                                }
                                items.push(it);
                                assert(its(items@, ps.classes@) =~= its(v1, c1).push(itv(it, ps.classes@)));
                                p = r;
                                after_rep = false;
                            },
                            None => {
                                match flags(pat, p + 2, f) {
                                    None => {
                                        return Err(Error::Syntax(p));
                                    },
                                    Some((nf, q, colon)) => {
                                        if colon {
                                            let (it, r) = group(pat, q, nf, ps, false, depth)?;
                                            proof {
                                                lemma_its_ext(v1, c1, ps.classes@, g1 as int, ps.ngroups as int);
                                                lemma_ext_trans(cl0, c1, ps.classes@);
                                            }
                                            items.push(it);
                                            assert(its(items@, ps.classes@) =~= its(v1, c1).push(itv(it, ps.classes@)));
                                            p = r;
                                        } else {
                                            f = nf;
                                            p = q;
                                        }
                                        after_rep = false;
                                    },
                                }
                            },
                        }
                    } else {
                        let (it, r) = group(pat, p + 1, f, ps, true, depth)?;
                        proof {
                            lemma_its_ext(v1, c1, ps.classes@, g1 as int, ps.ngroups as int);
                            lemma_ext_trans(cl0, c1, ps.classes@);
                        }
                        items.push(it);
                        assert(its(items@, ps.classes@) =~= its(v1, c1).push(itv(it, ps.classes@)));
                        p = r;
                        after_rep = false;
                    }
                } else if b == 0x5C && is_at(pat, p + 1, 0x51) {
                    let r = quote(pat, p + 2, f, ps, &mut items)?;
                    proof {
                        lemma_ext_trans(cl0, c1, ps.classes@);
                    }
                    p = r;
                    after_rep = false;
                } else {
                    let (it, r) = atom(pat, p, f, ps)?;
                    proof {
                        lemma_its_ext(v1, c1, ps.classes@, g1 as int, ps.ngroups as int);
                        lemma_ext_trans(cl0, c1, ps.classes@);
                    }
                    items.push(it);
                    assert(its(items@, ps.classes@) =~= its(v1, c1).push(It { re: it.re(ps.classes@), rep: 1 }));
                    p = r;
                    after_rep = false;
                }
            },
        }
    }
}

/// A group whose content starts at `body`, up to its `)`.
fn group(pat: &[u8], body: usize, fl: Flags, ps: &mut Ps, capture: bool, depth: usize) -> (r: Result<
    (Ast, usize),
    Error,
>)
    requires
        pat@.len() <= MAX_PATTERN,
        body <= pat@.len(),
        old(ps).ok(),
        old(ps).ngroups <= body,
        depth <= MAX_NEST,
    ensures
        match r {
            Ok((a, q)) => grows(old(ps), final(ps)) && good(
                a,
                final(ps).classes@.len() as int,
                final(ps).ngroups as int,
            ) && body < q <= pat@.len() && final(ps).ngroups <= q + 1 && sx::group(
                pat@,
                body as int,
                fl,
                old(ps).st(),
                capture,
            ) == Some((itv(a, final(ps).classes@), q as int, final(ps).st())),
            Err(e) => e is TooBig || sx::group(pat@, body as int, fl, old(ps).st(), capture) is None,
        },
    decreases pat@.len() - body, 4int,
{
    if depth >= MAX_NEST {
        return Err(Error::TooBig);
    }
    let k = ps.ngroups;
    if capture {
        ps.ngroups = k + 1;
    }
    let (a, q, _) = alt(pat, body, fl, ps, depth + 1)?;
    if !is_at(pat, q, 0x29) {
        return Err(Error::Syntax(q));
    }
    let ghost a0 = a;
    let a = if capture {
        some(Ast::group(k, a))?
    } else {
        a
    };
    proof {
        lemma_node(a, ps.classes@, ps.classes@.len() as int, ps.ngroups as int);
    }
    Ok((a, q + 1))
}

/// The pattern's tree, classes and groups.
pub fn parse(pat: &[u8]) -> (r: Result<Parsed, Error>)
    ensures
        match r {
            Ok(p) => p.ast.wf() && p.ast.bounded(p.classes@.len() as int, p.ngroups as int) && (forall|k: int|
                0 <= k < p.classes@.len() ==> (#[trigger] p.classes@[k]).wf()) && 1 <= p.ngroups <= MAX_PATTERN + 1
                && sx::parse(pat@) == Some(
                Pat { re: p.ast.re(p.classes@), ngroups: p.ngroups as nat, names: names_v(p.names@) },
            ),
            Err(e) => e is TooBig || sx::parse(pat@) is None,
        },
{
    if pat.len() > MAX_PATTERN {
        return Err(Error::TooBig);
    }
    if !utf8_valid_scalar(pat, 0) {
        return Err(Error::BadUtf8);
    }
    let fl = Flags { i: false, m: false, s: false, u: false };
    let mut ps = Ps { classes: Vec::new(), ngroups: 1, names: Vec::new() };
    assert(names_v(ps.names@) =~= Seq::empty());
    let (a, q, _) = alt(pat, 0, fl, &mut ps, 0)?;
    if q < pat.len() {
        return Err(Error::Syntax(q));
    }
    let a = some(Ast::group(0, a))?;
    proof {
        lemma_node(a, ps.classes@, ps.classes@.len() as int, ps.ngroups as int);
    }
    Ok(Parsed { ast: a, classes: ps.classes, ngroups: ps.ngroups, names: ps.names })
}

} // verus!
