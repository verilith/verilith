//! Namespaces in XML 1.0 as the expat ABI reports them (`XML_ParserCreateNS`),
//! verified: splitting a qualified name, the bindings in scope, a
//! namespace declaration's constraints, and the expanded name expat passes
//! to the handlers (`URI SEP local`, then `SEP prefix` with triplets).
//!
//! `expand` and `decl_check` are the specs; `ex_expand` and `ex_decl_check`
//! are proven to return what they return. `Bindings` is the stack of
//! declarations in scope, innermost last; `lookup` finds a prefix's
//! innermost binding.
use vstd::prelude::*;

verus! {

/// Why a name or declaration is refused; the ABI maps each to expat's
/// error code.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NsErr {
    /// A qualified name with an empty prefix or local part, or two colons
    /// (`XML_ERROR_INVALID_TOKEN`).
    InvalidToken,
    /// A prefix with no binding in scope (`XML_ERROR_UNBOUND_PREFIX`).
    UnboundPrefix,
    /// `xmlns:xmlns="..."` (`XML_ERROR_RESERVED_PREFIX_XMLNS`).
    ReservedPrefixXmlns,
    /// `xml` bound to another URI (`XML_ERROR_RESERVED_PREFIX_XML`).
    ReservedPrefixXml,
    /// Another prefix bound to the `xml` or `xmlns` URI
    /// (`XML_ERROR_RESERVED_NAMESPACE_URI`).
    ReservedNamespaceUri,
    /// `xmlns:p=""` (`XML_ERROR_UNDECLARING_PREFIX`).
    UndeclaringPrefix,
    /// A URI holding the separator (`XML_ERROR_SYNTAX`).
    Syntax,
}

/// `xml`
pub open spec fn lit_xml() -> Seq<u8> {
    seq![0x78u8, 0x6D, 0x6C]
}

/// `xmlns`
pub open spec fn lit_xmlns() -> Seq<u8> {
    seq![0x78u8, 0x6D, 0x6C, 0x6E, 0x73]
}

/// `http://www.w3.org/XML/1998/namespace`, the `xml` prefix's URI.
pub open spec fn xml_uri() -> Seq<u8> {
    seq![
        0x68u8, 0x74, 0x74, 0x70, 0x3A, 0x2F, 0x2F, 0x77, 0x77, 0x77, 0x2E, 0x77, 0x33, 0x2E, 0x6F, 0x72, 0x67, 0x2F,
        0x58, 0x4D, 0x4C, 0x2F, 0x31, 0x39, 0x39, 0x38, 0x2F, 0x6E, 0x61, 0x6D, 0x65, 0x73, 0x70, 0x61, 0x63, 0x65,
    ]
}

/// `http://www.w3.org/2000/xmlns/`, the URI no prefix may be bound to.
pub open spec fn xmlns_uri() -> Seq<u8> {
    seq![
        0x68u8, 0x74, 0x74, 0x70, 0x3A, 0x2F, 0x2F, 0x77, 0x77, 0x77, 0x2E, 0x77, 0x33, 0x2E, 0x6F, 0x72, 0x67, 0x2F,
        0x32, 0x30, 0x30, 0x30, 0x2F, 0x78, 0x6D, 0x6C, 0x6E, 0x73, 0x2F,
    ]
}

/// The first `:` in `q` at or after `i`.
pub open spec fn colon_from(q: Seq<u8>, i: int) -> Option<int>
    decreases q.len() - i,
{
    if !(0 <= i < q.len()) {
        None
    } else if q[i] == 0x3A {
        Some(i)
    } else {
        colon_from(q, i + 1)
    }
}

/// A qualified name's prefix (empty for none) and local part; `None` when
/// it is not a QName (an empty prefix or local part, or a second colon).
pub open spec fn qname_parts(q: Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)> {
    match colon_from(q, 0) {
        None => Some((Seq::empty(), q)),
        Some(c) => if c == 0 || c + 1 == q.len() || colon_from(q, c + 1) is Some {
            None
        } else {
            Some((q.subrange(0, c), q.subrange(c + 1, q.len() as int)))
        },
    }
}

/// The innermost binding of prefix `p` (the empty prefix: the default
/// namespace) among the declarations `b`, innermost last.
pub open spec fn lookup(b: Seq<(Seq<u8>, Seq<u8>)>, p: Seq<u8>) -> Option<Seq<u8>>
    decreases b.len(),
{
    if b.len() == 0 {
        None
    } else if b.last().0 == p {
        Some(b.last().1)
    } else {
        lookup(b.drop_last(), p)
    }
}

/// The separator as bytes: none when it is NUL.
pub open spec fn sep_seq(sep: u8) -> Seq<u8> {
    if sep != 0 {
        seq![sep]
    } else {
        Seq::empty()
    }
}

/// The name expat reports for the qualified name `q` of an element (or
/// of an attribute, `!element`) with the bindings `b` in scope: `q` itself
/// when it is in no namespace (an unprefixed attribute, or an unprefixed
/// element with no default namespace), else the URI, the separator and
/// the local part, then with `triplets` the separator and the prefix. The
/// `xml` prefix is always bound to its URI.
pub open spec fn expand(b: Seq<(Seq<u8>, Seq<u8>)>, q: Seq<u8>, element: bool, sep: u8, triplets: bool) -> Result<
    Seq<u8>,
    NsErr,
> {
    match qname_parts(q) {
        None => Err(NsErr::InvalidToken),
        Some((p, l)) => if p.len() == 0 && !element {
            Ok(q)
        } else {
            let uri = if p == lit_xml() {
                Some(xml_uri())
            } else {
                lookup(b, p)
            };
            match uri {
                Some(u) if u.len() > 0 => Ok(
                    u + sep_seq(sep) + l + if triplets && p.len() > 0 {
                        sep_seq(sep) + p
                    } else {
                        Seq::empty()
                    },
                ),
                _ => if p.len() == 0 {
                    Ok(q)
                } else {
                    Err(NsErr::UnboundPrefix)
                },
            }
        },
    }
}

/// The prefix an attribute named `n` declares: the empty prefix for
/// `xmlns`, `p` for `xmlns:p` (empty for `xmlns:`, as expat reads it); `None` when it is no declaration.
pub open spec fn decl_prefix(n: Seq<u8>) -> Option<Seq<u8>> {
    if n == lit_xmlns() {
        Some(Seq::empty())
    } else if n.len() >= 6 && n.subrange(0, 5) == lit_xmlns() && n[5] == 0x3A {
        Some(n.subrange(6, n.len() as int))
    } else {
        None
    }
}

/// `s` holds the byte `c`.
pub open spec fn holds(s: Seq<u8>, c: u8) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

/// The constraints on declaring prefix `p` (empty: the default namespace)
/// as `v` (Namespaces in XML 1.0, §3 "Reserved Prefixes and Namespace
/// Names", and Namespace constraint: No Prefix Undeclaring in 1.0), and
/// expat's: a URI may not hold the separator unless it is `:`.
pub open spec fn decl_check(p: Seq<u8>, v: Seq<u8>, sep: u8) -> Result<(), NsErr> {
    if p == lit_xmlns() {
        Err(NsErr::ReservedPrefixXmlns)
    } else if p == lit_xml() && v != xml_uri() {
        Err(NsErr::ReservedPrefixXml)
    } else if p != lit_xml() && (v == xml_uri() || v == xmlns_uri()) {
        Err(NsErr::ReservedNamespaceUri)
    } else if p.len() > 0 && v.len() == 0 {
        Err(NsErr::UndeclaringPrefix)
    } else if sep != 0 && sep != 0x3A && holds(v, sep) {
        Err(NsErr::Syntax)
    } else {
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Verified code
// ---------------------------------------------------------------------------

/// `a@ == b@`.
pub fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// `xml`
fn is_xml(a: &[u8]) -> (r: bool)
    ensures
        r == (a@ == lit_xml()),
{
    let x: [u8; 3] = [0x78u8, 0x6D, 0x6C];
    assert(x@ =~= lit_xml());
    eq_bytes(a, x.as_slice())
}

/// `xmlns`
fn is_xmlns(a: &[u8]) -> (r: bool)
    ensures
        r == (a@ == lit_xmlns()),
{
    let x: [u8; 5] = [0x78u8, 0x6D, 0x6C, 0x6E, 0x73];
    assert(x@ =~= lit_xmlns());
    eq_bytes(a, x.as_slice())
}

/// The `xml` prefix's URI.
pub fn xml_ns_uri() -> (r: [u8; 36])
    ensures
        r@ == xml_uri(),
{
    let x: [u8; 36] = [
        0x68u8, 0x74, 0x74, 0x70, 0x3A, 0x2F, 0x2F, 0x77, 0x77, 0x77, 0x2E, 0x77, 0x33, 0x2E, 0x6F, 0x72, 0x67, 0x2F,
        0x58, 0x4D, 0x4C, 0x2F, 0x31, 0x39, 0x39, 0x38, 0x2F, 0x6E, 0x61, 0x6D, 0x65, 0x73, 0x70, 0x61, 0x63, 0x65,
    ];
    assert(x@ =~= xml_uri());
    x
}

/// The `xmlns` URI.
fn xmlns_ns_uri() -> (r: [u8; 29])
    ensures
        r@ == xmlns_uri(),
{
    let x: [u8; 29] = [
        0x68u8, 0x74, 0x74, 0x70, 0x3A, 0x2F, 0x2F, 0x77, 0x77, 0x77, 0x2E, 0x77, 0x33, 0x2E, 0x6F, 0x72, 0x67, 0x2F,
        0x32, 0x30, 0x30, 0x30, 0x2F, 0x78, 0x6D, 0x6C, 0x6E, 0x73, 0x2F,
    ];
    assert(x@ =~= xmlns_uri());
    x
}

/// `colon_from(q, i)`.
fn ex_colon_from(q: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i <= q@.len(),
    ensures
        match colon_from(q@, i as int) {
            None => r is None,
            Some(c) => r is Some && r->Some_0 == c && i <= c < q@.len(),
        },
{
    let mut k = i;
    while k < q.len()
        invariant
            i <= k <= q@.len(),
            colon_from(q@, i as int) == colon_from(q@, k as int),
        decreases q@.len() - k,
    {
        if q[k] == 0x3A {
            return Some(k);
        }
        k += 1;
    }
    None
}

/// `qname_parts(q)`, as the colon's position (`None`: no prefix).
pub fn ex_qname_parts(q: &[u8]) -> (r: Result<Option<usize>, NsErr>)
    ensures
        match qname_parts(q@) {
            None => r == Err::<Option<usize>, NsErr>(NsErr::InvalidToken),
            Some((p, l)) => match r {
                Ok(None) => p.len() == 0 && l == q@,
                Ok(Some(c)) => c < q@.len() && p == q@.subrange(0, c as int) && l == q@.subrange(c + 1, q@.len() as int)
                    && c > 0,
                Err(_) => false,
            },
        },
{
    match ex_colon_from(q, 0) {
        None => Ok(None),
        Some(c) => {
            assert(colon_from(q@, 0) == Some(c as int));
            assert(c < q@.len());
            if c == 0 || c == q.len() - 1 {
                return Err(NsErr::InvalidToken);
            }
            if ex_colon_from(q, c + 1).is_some() {
                return Err(NsErr::InvalidToken);
            }
            Ok(Some(c))
        },
    }
}

/// The declarations in scope, innermost last: a prefix (empty for the
/// default namespace) and its URI.
pub struct Bindings {
    v: Vec<(Vec<u8>, Vec<u8>)>,
}

/// The bytes of one binding.
pub open spec fn bview(x: (Vec<u8>, Vec<u8>)) -> (Seq<u8>, Seq<u8>) {
    (x.0@, x.1@)
}

impl Bindings {
    /// The declarations, innermost last.
    pub closed spec fn view(&self) -> Seq<(Seq<u8>, Seq<u8>)> {
        self.v@.map_values(|x: (Vec<u8>, Vec<u8>)| bview(x))
    }

    /// None.
    pub fn new() -> (r: Bindings)
        ensures
            r.view() == Seq::<(Seq<u8>, Seq<u8>)>::empty(),
    {
        let r = Bindings { v: Vec::new() };
        assert(r.view() =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
        r
    }

    /// How many.
    pub fn len(&self) -> (r: usize)
        ensures
            r == self.view().len(),
    {
        self.v.len()
    }

    /// The `k`th, from the outermost.
    pub fn get(&self, k: usize) -> (r: (&[u8], &[u8]))
        requires
            k < self.view().len(),
        ensures
            (r.0@, r.1@) == self.view()[k as int],
    {
        let x = &self.v[k];
        (x.0.as_slice(), x.1.as_slice())
    }

    /// Declares `p` as `u`, innermost.
    pub fn push(&mut self, p: Vec<u8>, u: Vec<u8>)
        ensures
            final(self).view() == old(self).view().push((p@, u@)),
    {
        self.v.push((p, u));
        assert(final(self).view() =~= old(self).view().push((p@, u@)));
    }

    /// Ends the innermost declaration's scope.
    pub fn pop(&mut self)
        ensures
            old(self).view().len() > 0 ==> final(self).view() == old(self).view().drop_last(),
            old(self).view().len() == 0 ==> final(self).view() == old(self).view(),
    {
        let _ = self.v.pop();
        assert(old(self).view().len() > 0 ==> final(self).view() =~= old(self).view().drop_last());
    }

    /// A copy.
    pub fn copy(&self) -> (r: Bindings)
        ensures
            r.view() == self.view(),
    {
        let mut v: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
        let mut k = 0;
        while k < self.v.len()
            invariant
                k <= self.v@.len(),
                v@.len() == k,
                forall|j: int| 0 <= j < k ==> bview(#[trigger] v@[j]) == bview(self.v@[j]),
            decreases self.v@.len() - k,
        {
            let x = &self.v[k];
            let p = copy_vec(&x.0);
            let u = copy_vec(&x.1);
            v.push((p, u));
            k += 1;
        }
        let r = Bindings { v };
        assert(r.view() =~= self.view());
        r
    }

    /// `lookup(self, p)`, as the index of the binding.
    pub fn find(&self, p: &[u8]) -> (r: Option<usize>)
        ensures
            match lookup(self.view(), p@) {
                None => r is None,
                Some(u) => r is Some && r->Some_0 < self.view().len() && self.view()[r->Some_0 as int].1 == u,
            },
    {
        let mut k = self.v.len();
        assert(self.view().subrange(0, k as int) =~= self.view());
        while k > 0
            invariant
                k <= self.v@.len(),
                lookup(self.view(), p@) == lookup(self.view().subrange(0, k as int), p@),
            decreases k,
        {
            let ghost s = self.view().subrange(0, k as int);
            assert(s.drop_last() =~= self.view().subrange(0, k - 1));
            assert(s.last() == self.view()[k - 1]);
            if eq_bytes(self.v[k - 1].0.as_slice(), p) {
                return Some(k - 1);
            }
            k -= 1;
        }
        assert(self.view().subrange(0, 0) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
        None
    }
}

fn copy_vec(a: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == a@,
{
    let mut r = Vec::new();
    verilith_core::prims::extend(&mut r, a.as_slice());
    assert(r@ =~= a@);
    r
}

/// `expand(b, q, element, sep, triplets)`.
pub fn ex_expand(b: &Bindings, q: &[u8], element: bool, sep: u8, triplets: bool) -> (r: Result<Vec<u8>, NsErr>)
    ensures
        match expand(b.view(), q@, element, sep, triplets) {
            Ok(s) => r is Ok && r->Ok_0@ == s,
            Err(e) => r == Err::<Vec<u8>, NsErr>(e),
        },
{
    let colon = match ex_qname_parts(q) {
        Err(e) => return Err(e),
        Ok(c) => c,
    };
    let (pa, la) = match colon {
        Some(c) => {
            let n = q.len();
            assert(c < n);
            (c, c + 1)
        },
        None => (0, 0),
    };
    let prefix = vstd::slice::slice_subrange(q, 0, pa);
    let local = vstd::slice::slice_subrange(q, la, q.len());
    proof {
        if colon is None {
            assert(prefix@ =~= Seq::<u8>::empty());
            assert(local@ =~= q@);
        }
    }
    proof {
        assert(qname_parts(q@) == Some((prefix@, local@)));
    }
    if pa == 0 && !element {
        return Ok(copy_vec_s(q));
    }
    let xml = xml_ns_uri();
    let uri: Option<&[u8]> = if is_xml(prefix) {
        let xs = xml.as_slice();
        assert(xs@ =~= xml_uri());
        Some(xs)
    } else {
        match b.find(prefix) {
            Some(k) => Some(b.get(k).1),
            None => None,
        }
    };
    let ghost su = if prefix@ == lit_xml() {
        Some(xml_uri())
    } else {
        lookup(b.view(), prefix@)
    };
    assert(uri is Some <==> su is Some);
    assert(uri is Some ==> uri->Some_0@ == su->Some_0);
    assert(prefix@.len() == pa);
    let u = match uri {
        Some(u) if u.len() > 0 => u,
        _ => {
            if pa == 0 {
                return Ok(copy_vec_s(q));
            }
            return Err(NsErr::UnboundPrefix);
        },
    };
    let mut out: Vec<u8> = Vec::new();
    verilith_core::prims::extend(&mut out, u);
    if sep != 0 {
        out.push(sep);
    }
    verilith_core::prims::extend(&mut out, local);
    if triplets && pa > 0 {
        if sep != 0 {
            out.push(sep);
        }
        verilith_core::prims::extend(&mut out, prefix);
    }
    proof {
        let s = u@ + sep_seq(sep) + local@ + if triplets && prefix@.len() > 0 {
            sep_seq(sep) + prefix@
        } else {
            Seq::empty()
        };
        assert(out@ =~= s);
    }
    Ok(out)
}

fn copy_vec_s(a: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == a@,
{
    let mut r = Vec::new();
    verilith_core::prims::extend(&mut r, a);
    assert(r@ =~= a@);
    r
}

/// `decl_prefix(n)`: the prefix's start in `n`.
pub fn ex_decl_prefix(n: &[u8]) -> (r: Option<usize>)
    ensures
        match decl_prefix(n@) {
            None => r is None,
            Some(p) => r is Some && r->Some_0 <= n@.len() && p == n@.subrange(r->Some_0 as int, n@.len() as int),
        },
{
    if is_xmlns(n) {
        assert(n@.subrange(5, 5) =~= Seq::<u8>::empty());
        return Some(5);
    }
    if n.len() >= 6 && n[5] == 0x3A {
        let head = vstd::slice::slice_subrange(n, 0, 5);
        if is_xmlns(head) {
            return Some(6);
        }
    }
    None
}

/// `decl_check(p, v, sep)`.
pub fn ex_decl_check(p: &[u8], v: &[u8], sep: u8) -> (r: Result<(), NsErr>)
    ensures
        r == decl_check(p@, v@, sep),
{
    let xml = xml_ns_uri();
    let xmlns = xmlns_ns_uri();
    let xs = xml.as_slice();
    let ns = xmlns.as_slice();
    assert(xs@ =~= xml_uri());
    assert(ns@ =~= xmlns_uri());
    if is_xmlns(p) {
        return Err(NsErr::ReservedPrefixXmlns);
    }
    let px = is_xml(p);
    let vx = eq_bytes(v, xs);
    if px && !vx {
        return Err(NsErr::ReservedPrefixXml);
    }
    if !px && (vx || eq_bytes(v, ns)) {
        return Err(NsErr::ReservedNamespaceUri);
    }
    if p.len() > 0 && v.len() == 0 {
        return Err(NsErr::UndeclaringPrefix);
    }
    if sep != 0 && sep != 0x3A {
        let mut i = 0;
        while i < v.len()
            invariant
                i <= v@.len(),
                forall|j: int| 0 <= j < i ==> v@[j] != sep,
                p@ != lit_xmlns(),
                !(p@ == lit_xml() && v@ != xml_uri()),
                !(p@ != lit_xml() && (v@ == xml_uri() || v@ == xmlns_uri())),
                !(p@.len() > 0 && v@.len() == 0),
                sep != 0 && sep != 0x3A,
            decreases v@.len() - i,
        {
            if v[i] == sep {
                assert(0 <= i < v@.len() && v@[i as int] == sep);
                assert(holds(v@, sep));
                return Err(NsErr::Syntax);
            }
            i += 1;
        }
    }
    Ok(())
}

} // verus!
