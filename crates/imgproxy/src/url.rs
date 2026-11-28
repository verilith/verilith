//! imgproxy's URLs and the choice of decoder, proven to compute
//! `spec_url::parse` and `spec_url::kind`. Run-time errors carry
//! imgproxy's messages; the proofs say a request is refused exactly when
//! the specification gives `None`, and what it parses to otherwise.
use crate::fit::Mode;
#[cfg(verus_only)]
use crate::spec_geom::F1;
use crate::spec_geom::{GKind, Gravity};
use crate::spec_url::*;
use vstd::prelude::*;

verus! {

/// Why a request failed, with the status it is answered with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fail {
    /// 400: the URL is not one we understand.
    BadUrl(&'static str),
    /// 403: the signature is wrong.
    Forbidden,
    /// 404: no such source.
    NotFound,
    /// 415: the source is not JPEG, PNG, WebP or GIF.
    Unsupported,
    /// 422: the source does not decode, or is larger than the limits.
    Unprocessable(&'static str),
    /// 502: the origin failed.
    BadGateway(&'static str),
    /// 404: the URL's `expires` has passed.
    Expired,
}

/// Where the image comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    /// `local:///path`, under the configured root: the path after `local://`.
    Local(Vec<u8>),
    /// `http://...` or `https://...`.
    Http(Vec<u8>),
    /// The request body (`POST .../upload`).
    Upload,
}

pub open spec fn src_view(s: Source) -> Src {
    match s {
        Source::Local(p) => Src::Local(p@),
        Source::Http(u) => Src::Http(u@),
        Source::Upload => Src::Upload,
    }
}

/// A parsed path: the signature is `path[1..sig_end]`, the signed part
/// `path[sig_end..]`.
pub struct Parts {
    pub sig_end: usize,
    pub opts: Options,
    pub source: Source,
    /// `filename`, decoded.
    pub filename: Option<Vec<u8>>,
}

pub open spec fn opt_view(v: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match v {
        Some(v) => Some(v@),
        None => None,
    }
}

pub open spec fn views(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    Seq::new(v.len(), |i: int| v[i]@)
}

// ---------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------

pub fn eq(s: &[u8], t: &[u8]) -> (r: bool)
    ensures
        r == (s@ == t@),
{
    if s.len() != t.len() {
        return false;
    }
    let mut i = 0;
    while i < s.len()
        invariant
            s.len() == t.len(),
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] == t@[j],
        decreases s.len() - i,
    {
        if s[i] != t[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(s@ =~= t@);
    }
    true
}

pub fn starts_x(s: &[u8], p: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, p@),
{
    if p.len() > s.len() {
        return false;
    }
    let mut i = 0;
    while i < p.len()
        invariant
            p.len() <= s.len(),
            i <= p.len(),
            forall|j: int| 0 <= j < i ==> s@[j] == p@[j],
        decreases p.len() - i,
    {
        if s[i] != p[i] {
            proof {
                assert(s@.take(p.len() as int)[i as int] != p@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(s@.take(p.len() as int) =~= p@);
    }
    true
}

/// `s[a..b]`, copied.
pub fn sub(s: &[u8], a: usize, b: usize) -> (r: Vec<u8>)
    requires
        a <= b <= s.len(),
    ensures
        r@ == s@.subrange(a as int, b as int),
{
    let mut out: Vec<u8> = Vec::with_capacity(b - a);
    let mut i = a;
    while i < b
        invariant
            a <= i <= b <= s.len(),
            out@ == s@.subrange(a as int, i as int),
        decreases b - i,
    {
        out.push(s[i]);
        proof {
            assert(out@ =~= s@.subrange(a as int, i + 1));
        }
        i += 1;
    }
    out
}

/// Appends `s` to `out`.
pub fn append(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost o = out@;
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == o + s@.take(i as int),
        decreases s.len() - i,
    {
        out.push(s[i]);
        proof {
            assert(out@ =~= o + s@.take(i + 1));
        }
        i += 1;
    }
    proof {
        assert(s@.take(s.len() as int) =~= s@);
    }
}

pub proof fn lemma_find_range(s: Seq<u8>, c: u8, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= find(s, c, i) <= s.len(),
        find(s, c, i) < s.len() ==> s[find(s, c, i)] == c,
        forall|j: int| i <= j < find(s, c, i) ==> s[j] != c,
    decreases s.len() - i,
{
    if i < s.len() && s[i] != c {
        lemma_find_range(s, c, i + 1);
    }
}

pub proof fn lemma_find_skip(s: Seq<u8>, c: u8, i: int, j: int)
    requires
        0 <= i <= s.len(),
        0 <= j,
    ensures
        find(s.skip(i), c, j) == find(s, c, i + j) - i,
    decreases s.len() - i - j,
{
    if i + j < s.len() && s[i + j] != c {
        lemma_find_skip(s, c, i, j + 1);
    }
}

/// `find`.
pub fn find_x(s: &[u8], c: u8, from: usize) -> (r: usize)
    requires
        from <= s.len(),
    ensures
        r == find(s@, c, from as int),
        from <= r <= s.len(),
{
    proof {
        lemma_find_range(s@, c, from as int);
    }
    let mut i = from;
    while i < s.len()
        invariant
            from <= i <= s.len(),
            find(s@, c, from as int) == find(s@, c, i as int),
        decreases s.len() - i,
    {
        if s[i] == c {
            return i;
        }
        i += 1;
    }
    i
}

/// `rfind`, as `Some(i)` or `None` for -1.
pub fn rfind_x(s: &[u8], c: u8) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => rfind(s@, c) == i && i < s.len(),
            None => rfind(s@, c) == -1,
        },
{
    let mut i = s.len();
    proof {
        assert(s@.take(i as int) =~= s@);
    }
    while i > 0
        invariant
            i <= s.len(),
            rfind(s@, c) == rfind(s@.take(i as int), c),
        decreases i,
    {
        if s[i - 1] == c {
            return Some(i - 1);
        }
        proof {
            assert(s@.take(i as int).drop_last() =~= s@.take(i - 1));
        }
        i -= 1;
    }
    None
}

/// `split`.
pub fn split_x(s: &[u8], c: u8) -> (r: Vec<Vec<u8>>)
    ensures
        views(r@) == split(s@, c),
        r@.len() >= 1,
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(views(out@) + split(s@.skip(0), c) =~= split(s@, c)) by {
            assert(s@.skip(0) =~= s@);
        }
    }
    loop
        invariant
            i <= s.len(),
            views(out@) + split(s@.skip(i as int), c) == split(s@, c),
        decreases s.len() - i,
    {
        let j = find_x(s, c, i);
        let ghost t = s@.skip(i as int);
        proof {
            lemma_find_skip(s@, c, i as int, 0);
        }
        let ghost before = views(out@);
        if j >= s.len() {
            let piece = sub(s, i, s.len());
            proof {
                assert(piece@ =~= t);
                assert(split(t, c) == seq![t]);
            }
            out.push(piece);
            proof {
                assert(views(out@) =~= before + seq![t]);
            }
            return out;
        }
        let piece = sub(s, i, j);
        proof {
            assert(t.take(j - i) =~= piece@);
            assert(t.skip(j - i + 1) =~= s@.skip(j + 1));
            assert(split(t, c) == seq![t.take(j - i)] + split(t.skip(j - i + 1), c));
        }
        out.push(piece);
        proof {
            assert(views(out@) =~= before + seq![piece@]);
            assert(before + (seq![piece@] + split(s@.skip(j + 1), c)) =~= (before + seq![piece@]) + split(
                s@.skip(j + 1),
                c,
            ));
        }
        i = j + 1;
    }
}

/// `join` of the pieces from `f` on.
pub fn join_x(p: &Vec<Vec<u8>>, f: usize, c: u8) -> (r: Vec<u8>)
    requires
        f <= p@.len(),
    ensures
        r@ == join(views(p@).skip(f as int), c),
{
    let ghost q = views(p@).skip(f as int);
    let mut out: Vec<u8> = Vec::new();
    let mut k = f;
    proof {
        assert(q.take(0).len() == 0);
    }
    while k < p.len()
        invariant
            f <= k <= p@.len(),
            q == views(p@).skip(f as int),
            out@ == join(q.take(k - f), c),
        decreases p.len() - k,
    {
        let ghost before = out@;
        if k > f {
            out.push(c);
        }
        append(&mut out, p[k].as_slice());
        proof {
            let m = k - f;
            assert(q.take(m + 1).drop_last() =~= q.take(m));
            assert(q.take(m + 1).last() == p@[k as int]@);
            if m == 0 {
                assert(before.len() == 0);
                assert(out@ =~= p@[k as int]@);
            } else {
                assert(out@ =~= before + seq![c] + p@[k as int]@);
            }
        }
        k += 1;
    }
    proof {
        assert(q.take(k - f) =~= q);
    }
    out
}

/// `concat` of the pieces from `f` on.
pub fn concat_x(p: &Vec<Vec<u8>>, f: usize) -> (r: Vec<u8>)
    requires
        f <= p@.len(),
    ensures
        r@ == concat(views(p@).skip(f as int)),
{
    let ghost q = views(p@).skip(f as int);
    let mut out: Vec<u8> = Vec::new();
    let mut k = f;
    proof {
        assert(q.take(0).len() == 0);
    }
    while k < p.len()
        invariant
            f <= k <= p@.len(),
            q == views(p@).skip(f as int),
            out@ == concat(q.take(k - f)),
        decreases p.len() - k,
    {
        append(&mut out, p[k].as_slice());
        proof {
            let m = k - f;
            assert(q.take(m + 1).drop_last() =~= q.take(m));
            assert(q.take(m + 1).last() == p@[k as int]@);
        }
        k += 1;
    }
    proof {
        assert(q.take(k - f) =~= q);
    }
    out
}

// ---------------------------------------------------------------------------
// Literals
// ---------------------------------------------------------------------------

/// Whether `s` is `fit`.
pub fn is_fit(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'i', b't']),
{
    let t: [u8; 3] = [b'f', b'i', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'i', b't']);
    }
    r
}

/// Whether `s` is `fill`.
pub fn is_fill(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'i', b'l', b'l']),
{
    let t: [u8; 4] = [b'f', b'i', b'l', b'l'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'i', b'l', b'l']);
    }
    r
}

/// Whether `s` is `force`.
pub fn is_force(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'o', b'r', b'c', b'e']),
{
    let t: [u8; 5] = [b'f', b'o', b'r', b'c', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'o', b'r', b'c', b'e']);
    }
    r
}

/// Whether `s` is `1`.
pub fn is_1(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'1']),
{
    let t: [u8; 1] = [b'1'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'1']);
    }
    r
}

/// Whether `s` is `t`.
pub fn is_t(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b't']),
{
    let t: [u8; 1] = [b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b't']);
    }
    r
}

/// Whether `s` is `true`.
pub fn is_true(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b't', b'r', b'u', b'e']),
{
    let t: [u8; 4] = [b't', b'r', b'u', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b't', b'r', b'u', b'e']);
    }
    r
}

/// Whether `s` is `0`.
pub fn is_0(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'0']),
{
    let t: [u8; 1] = [b'0'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'0']);
    }
    r
}

/// Whether `s` is `f`.
pub fn is_f(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f']),
{
    let t: [u8; 1] = [b'f'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f']);
    }
    r
}

/// Whether `s` is `false`.
pub fn is_false(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'a', b'l', b's', b'e']),
{
    let t: [u8; 5] = [b'f', b'a', b'l', b's', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'a', b'l', b's', b'e']);
    }
    r
}

/// Whether `s` is `png`.
pub fn is_png(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'p', b'n', b'g']),
{
    let t: [u8; 3] = [b'p', b'n', b'g'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'p', b'n', b'g']);
    }
    r
}

/// Whether `s` is `best`.
pub fn is_best(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'b', b'e', b's', b't']),
{
    let t: [u8; 4] = [b'b', b'e', b's', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'b', b'e', b's', b't']);
    }
    r
}

/// Whether `s` is `jpg`.
pub fn is_jpg(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'j', b'p', b'g']),
{
    let t: [u8; 3] = [b'j', b'p', b'g'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'j', b'p', b'g']);
    }
    r
}

/// Whether `s` is `jpeg`.
pub fn is_jpeg(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'j', b'p', b'e', b'g']),
{
    let t: [u8; 4] = [b'j', b'p', b'e', b'g'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'j', b'p', b'e', b'g']);
    }
    r
}

/// Whether `s` is `lanczos3`.
pub fn is_lanczos3(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'l', b'a', b'n', b'c', b'z', b'o', b's', b'3']),
{
    let t: [u8; 8] = [b'l', b'a', b'n', b'c', b'z', b'o', b's', b'3'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'l', b'a', b'n', b'c', b'z', b'o', b's', b'3']);
    }
    r
}

/// Whether `s` is `lanczos2`.
pub fn is_lanczos2(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'l', b'a', b'n', b'c', b'z', b'o', b's', b'2']),
{
    let t: [u8; 8] = [b'l', b'a', b'n', b'c', b'z', b'o', b's', b'2'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'l', b'a', b'n', b'c', b'z', b'o', b's', b'2']);
    }
    r
}

/// Whether `s` is `cubic`.
pub fn is_cubic(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'c', b'u', b'b', b'i', b'c']),
{
    let t: [u8; 5] = [b'c', b'u', b'b', b'i', b'c'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'c', b'u', b'b', b'i', b'c']);
    }
    r
}

/// Whether `s` is `linear`.
pub fn is_linear(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'l', b'i', b'n', b'e', b'a', b'r']),
{
    let t: [u8; 6] = [b'l', b'i', b'n', b'e', b'a', b'r'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'l', b'i', b'n', b'e', b'a', b'r']);
    }
    r
}

/// Whether `s` is `nearest`.
pub fn is_nearest(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'n', b'e', b'a', b'r', b'e', b's', b't']),
{
    let t: [u8; 7] = [b'n', b'e', b'a', b'r', b'e', b's', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'n', b'e', b'a', b'r', b'e', b's', b't']);
    }
    r
}

/// Whether `s` is `area`.
pub fn is_area(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'a', b'r', b'e', b'a']),
{
    let t: [u8; 4] = [b'a', b'r', b'e', b'a'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'a', b'r', b'e', b'a']);
    }
    r
}

/// Whether `s` is `resize`.
pub fn is_resize(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'e', b's', b'i', b'z', b'e']),
{
    let t: [u8; 6] = [b'r', b'e', b's', b'i', b'z', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'e', b's', b'i', b'z', b'e']);
    }
    r
}

/// Whether `s` is `rs`.
pub fn is_rs(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b's']),
{
    let t: [u8; 2] = [b'r', b's'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b's']);
    }
    r
}

/// Whether `s` is `size`.
pub fn is_size(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'i', b'z', b'e']),
{
    let t: [u8; 4] = [b's', b'i', b'z', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'i', b'z', b'e']);
    }
    r
}

/// Whether `s` is `s`.
pub fn is_s(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's']),
{
    let t: [u8; 1] = [b's'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's']);
    }
    r
}

/// Whether `s` is `resizing_type`.
pub fn is_resizing_type(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'e', b's', b'i', b'z', b'i', b'n', b'g', b'_', b't', b'y', b'p', b'e']),
{
    let t: [u8; 13] = [b'r', b'e', b's', b'i', b'z', b'i', b'n', b'g', b'_', b't', b'y', b'p', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'e', b's', b'i', b'z', b'i', b'n', b'g', b'_', b't', b'y', b'p', b'e']);
    }
    r
}

/// Whether `s` is `rt`.
pub fn is_rt(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b't']),
{
    let t: [u8; 2] = [b'r', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b't']);
    }
    r
}

/// Whether `s` is `width`.
pub fn is_width(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'w', b'i', b'd', b't', b'h']),
{
    let t: [u8; 5] = [b'w', b'i', b'd', b't', b'h'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'w', b'i', b'd', b't', b'h']);
    }
    r
}

/// Whether `s` is `w`.
pub fn is_w(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'w']),
{
    let t: [u8; 1] = [b'w'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'w']);
    }
    r
}

/// Whether `s` is `height`.
pub fn is_height(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'h', b'e', b'i', b'g', b'h', b't']),
{
    let t: [u8; 6] = [b'h', b'e', b'i', b'g', b'h', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'h', b'e', b'i', b'g', b'h', b't']);
    }
    r
}

/// Whether `s` is `h`.
pub fn is_h(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'h']),
{
    let t: [u8; 1] = [b'h'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'h']);
    }
    r
}

/// Whether `s` is `enlarge`.
pub fn is_enlarge(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'e', b'n', b'l', b'a', b'r', b'g', b'e']),
{
    let t: [u8; 7] = [b'e', b'n', b'l', b'a', b'r', b'g', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'e', b'n', b'l', b'a', b'r', b'g', b'e']);
    }
    r
}

/// Whether `s` is `el`.
pub fn is_el(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'e', b'l']),
{
    let t: [u8; 2] = [b'e', b'l'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'e', b'l']);
    }
    r
}

/// Whether `s` is `resizing_algorithm`.
pub fn is_resizing_algorithm(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'e', b's', b'i', b'z', b'i', b'n', b'g', b'_', b'a', b'l', b'g', b'o', b'r', b'i', b't', b'h', b'm']),
{
    let t: [u8; 18] = [b'r', b'e', b's', b'i', b'z', b'i', b'n', b'g', b'_', b'a', b'l', b'g', b'o', b'r', b'i', b't', b'h', b'm'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'e', b's', b'i', b'z', b'i', b'n', b'g', b'_', b'a', b'l', b'g', b'o', b'r', b'i', b't', b'h', b'm']);
    }
    r
}

/// Whether `s` is `ra`.
pub fn is_ra(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'a']),
{
    let t: [u8; 2] = [b'r', b'a'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'a']);
    }
    r
}

/// Whether `s` is `background`.
pub fn is_background(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'b', b'a', b'c', b'k', b'g', b'r', b'o', b'u', b'n', b'd']),
{
    let t: [u8; 10] = [b'b', b'a', b'c', b'k', b'g', b'r', b'o', b'u', b'n', b'd'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'b', b'a', b'c', b'k', b'g', b'r', b'o', b'u', b'n', b'd']);
    }
    r
}

/// Whether `s` is `bg`.
pub fn is_bg(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'b', b'g']),
{
    let t: [u8; 2] = [b'b', b'g'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'b', b'g']);
    }
    r
}

/// Whether `s` is `quality`.
pub fn is_quality(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'q', b'u', b'a', b'l', b'i', b't', b'y']),
{
    let t: [u8; 7] = [b'q', b'u', b'a', b'l', b'i', b't', b'y'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'q', b'u', b'a', b'l', b'i', b't', b'y']);
    }
    r
}

/// Whether `s` is `q`.
pub fn is_q(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'q']),
{
    let t: [u8; 1] = [b'q'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'q']);
    }
    r
}

/// Whether `s` is `strip_metadata`.
pub fn is_strip_metadata(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b't', b'r', b'i', b'p', b'_', b'm', b'e', b't', b'a', b'd', b'a', b't', b'a']),
{
    let t: [u8; 14] = [b's', b't', b'r', b'i', b'p', b'_', b'm', b'e', b't', b'a', b'd', b'a', b't', b'a'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b't', b'r', b'i', b'p', b'_', b'm', b'e', b't', b'a', b'd', b'a', b't', b'a']);
    }
    r
}

/// Whether `s` is `sm`.
pub fn is_sm(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'm']),
{
    let t: [u8; 2] = [b's', b'm'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'm']);
    }
    r
}

/// Whether `s` is `cachebuster`.
pub fn is_cachebuster(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'c', b'a', b'c', b'h', b'e', b'b', b'u', b's', b't', b'e', b'r']),
{
    let t: [u8; 11] = [b'c', b'a', b'c', b'h', b'e', b'b', b'u', b's', b't', b'e', b'r'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'c', b'a', b'c', b'h', b'e', b'b', b'u', b's', b't', b'e', b'r']);
    }
    r
}

/// Whether `s` is `cb`.
pub fn is_cb(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'c', b'b']),
{
    let t: [u8; 2] = [b'c', b'b'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'c', b'b']);
    }
    r
}

/// Whether `s` is `format`.
pub fn is_format(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'o', b'r', b'm', b'a', b't']),
{
    let t: [u8; 6] = [b'f', b'o', b'r', b'm', b'a', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'o', b'r', b'm', b'a', b't']);
    }
    r
}

/// Whether `s` is `ext`.
pub fn is_ext(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'e', b'x', b't']),
{
    let t: [u8; 3] = [b'e', b'x', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'e', b'x', b't']);
    }
    r
}

/// Whether `s` is `gravity`.
pub fn is_gravity(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'g', b'r', b'a', b'v', b'i', b't', b'y']),
{
    let t: [u8; 7] = [b'g', b'r', b'a', b'v', b'i', b't', b'y'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'g', b'r', b'a', b'v', b'i', b't', b'y']);
    }
    r
}

/// Whether `s` is `g`.
pub fn is_g(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'g']),
{
    let t: [u8; 1] = [b'g'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'g']);
    }
    r
}

/// Whether `s` is `ce`.
pub fn is_ce(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'c', b'e']),
{
    let t: [u8; 2] = [b'c', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'c', b'e']);
    }
    r
}

/// Whether `s` is `plain`.
pub fn is_plain(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'p', b'l', b'a', b'i', b'n']),
{
    let t: [u8; 5] = [b'p', b'l', b'a', b'i', b'n'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'p', b'l', b'a', b'i', b'n']);
    }
    r
}

/// Whether `s` is `upload`.
pub fn is_upload(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'u', b'p', b'l', b'o', b'a', b'd']),
{
    let t: [u8; 6] = [b'u', b'p', b'l', b'o', b'a', b'd'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'u', b'p', b'l', b'o', b'a', b'd']);
    }
    r
}

/// Whether `s` is `no`.
pub fn is_no(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'n', b'o']),
{
    let t: [u8; 2] = [b'n', b'o'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'n', b'o']);
    }
    r
}

/// Whether `s` is `so`.
pub fn is_so(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'o']),
{
    let t: [u8; 2] = [b's', b'o'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'o']);
    }
    r
}

/// Whether `s` is `ea`.
pub fn is_ea(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'e', b'a']),
{
    let t: [u8; 2] = [b'e', b'a'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'e', b'a']);
    }
    r
}

/// Whether `s` is `we`.
pub fn is_we(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'w', b'e']),
{
    let t: [u8; 2] = [b'w', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'w', b'e']);
    }
    r
}

/// Whether `s` is `noea`.
pub fn is_noea(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'n', b'o', b'e', b'a']),
{
    let t: [u8; 4] = [b'n', b'o', b'e', b'a'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'n', b'o', b'e', b'a']);
    }
    r
}

/// Whether `s` is `nowe`.
pub fn is_nowe(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'n', b'o', b'w', b'e']),
{
    let t: [u8; 4] = [b'n', b'o', b'w', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'n', b'o', b'w', b'e']);
    }
    r
}

/// Whether `s` is `soea`.
pub fn is_soea(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'o', b'e', b'a']),
{
    let t: [u8; 4] = [b's', b'o', b'e', b'a'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'o', b'e', b'a']);
    }
    r
}

/// Whether `s` is `sowe`.
pub fn is_sowe(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'o', b'w', b'e']),
{
    let t: [u8; 4] = [b's', b'o', b'w', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'o', b'w', b'e']);
    }
    r
}

/// Whether `s` is `fp`.
pub fn is_fp(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'p']),
{
    let t: [u8; 2] = [b'f', b'p'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'p']);
    }
    r
}

/// Whether `s` is `crop`.
pub fn is_crop(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'c', b'r', b'o', b'p']),
{
    let t: [u8; 4] = [b'c', b'r', b'o', b'p'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'c', b'r', b'o', b'p']);
    }
    r
}

/// Whether `s` is `c`.
pub fn is_c(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'c']),
{
    let t: [u8; 1] = [b'c'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'c']);
    }
    r
}

/// Whether `s` is `extend`.
pub fn is_extend(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'e', b'x', b't', b'e', b'n', b'd']),
{
    let t: [u8; 6] = [b'e', b'x', b't', b'e', b'n', b'd'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'e', b'x', b't', b'e', b'n', b'd']);
    }
    r
}

/// Whether `s` is `ex`.
pub fn is_ex(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'e', b'x']),
{
    let t: [u8; 2] = [b'e', b'x'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'e', b'x']);
    }
    r
}

/// Whether `s` is `padding`.
pub fn is_padding(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'p', b'a', b'd', b'd', b'i', b'n', b'g']),
{
    let t: [u8; 7] = [b'p', b'a', b'd', b'd', b'i', b'n', b'g'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'p', b'a', b'd', b'd', b'i', b'n', b'g']);
    }
    r
}

/// Whether `s` is `pd`.
pub fn is_pd(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'p', b'd']),
{
    let t: [u8; 2] = [b'p', b'd'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'p', b'd']);
    }
    r
}

/// Whether `s` is `dpr`.
pub fn is_dpr(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'd', b'p', b'r']),
{
    let t: [u8; 3] = [b'd', b'p', b'r'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'd', b'p', b'r']);
    }
    r
}

/// Whether `s` is `rotate`.
pub fn is_rotate(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'o', b't', b'a', b't', b'e']),
{
    let t: [u8; 6] = [b'r', b'o', b't', b'a', b't', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'o', b't', b'a', b't', b'e']);
    }
    r
}

/// Whether `s` is `rot`.
pub fn is_rot(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'o', b't']),
{
    let t: [u8; 3] = [b'r', b'o', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'o', b't']);
    }
    r
}

/// Whether `s` is `flip`.
pub fn is_flip(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'l', b'i', b'p']),
{
    let t: [u8; 4] = [b'f', b'l', b'i', b'p'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'l', b'i', b'p']);
    }
    r
}

/// Whether `s` is `fl`.
pub fn is_fl(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'l']),
{
    let t: [u8; 2] = [b'f', b'l'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'l']);
    }
    r
}

pub fn starts_http(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'h', b't', b't', b'p']),
{
    let t: [u8; 4] = [b'h', b't', b't', b'p'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'h', b't', b't', b'p']);
    }
    r
}

pub fn starts_local(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'l', b'o', b'c', b'a', b'l']),
{
    let t: [u8; 5] = [b'l', b'o', b'c', b'a', b'l'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'l', b'o', b'c', b'a', b'l']);
    }
    r
}

pub fn starts_local_url(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'l', b'o', b'c', b'a', b'l', b':', b'/', b'/']),
{
    let t: [u8; 8] = [b'l', b'o', b'c', b'a', b'l', b':', b'/', b'/'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'l', b'o', b'c', b'a', b'l', b':', b'/', b'/']);
    }
    r
}

pub fn starts_http_url(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'h', b't', b't', b'p', b':', b'/', b'/']),
{
    let t: [u8; 7] = [b'h', b't', b't', b'p', b':', b'/', b'/'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'h', b't', b't', b'p', b':', b'/', b'/']);
    }
    r
}

pub fn starts_https_url(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'h', b't', b't', b'p', b's', b':', b'/', b'/']),
{
    let t: [u8; 8] = [b'h', b't', b't', b'p', b's', b':', b'/', b'/'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'h', b't', b't', b'p', b's', b':', b'/', b'/']);
    }
    r
}

pub fn starts_upload(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'u', b'p', b'l', b'o', b'a', b'd']),
{
    let t: [u8; 6] = [b'u', b'p', b'l', b'o', b'a', b'd'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'u', b'p', b'l', b'o', b'a', b'd']);
    }
    r
}

pub fn starts_jpeg_soi(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![0xffu8, 0xd8u8, 0xffu8]),
{
    let t: [u8; 3] = [0xffu8, 0xd8u8, 0xffu8];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![0xffu8, 0xd8u8, 0xffu8]);
    }
    r
}

pub fn starts_png_sig(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![0x89u8, 0x50u8, 0x4eu8, 0x47u8, 0x0du8, 0x0au8, 0x1au8, 0x0au8]),
{
    let t: [u8; 8] = [0x89u8, 0x50u8, 0x4eu8, 0x47u8, 0x0du8, 0x0au8, 0x1au8, 0x0au8];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![0x89u8, 0x50u8, 0x4eu8, 0x47u8, 0x0du8, 0x0au8, 0x1au8, 0x0au8]);
    }
    r
}

pub fn starts_gif87(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'G', b'I', b'F', b'8', b'7', b'a']),
{
    let t: [u8; 6] = [b'G', b'I', b'F', b'8', b'7', b'a'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'G', b'I', b'F', b'8', b'7', b'a']);
    }
    r
}

pub fn starts_gif89(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'G', b'I', b'F', b'8', b'9', b'a']),
{
    let t: [u8; 6] = [b'G', b'I', b'F', b'8', b'9', b'a'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'G', b'I', b'F', b'8', b'9', b'a']);
    }
    r
}

pub fn starts_riff(s: &[u8]) -> (r: bool)
    ensures
        r == starts(s@, seq![b'R', b'I', b'F', b'F']),
{
    let t: [u8; 4] = [b'R', b'I', b'F', b'F'];
    let r = starts_x(s, &t);
    proof {
        assert(t@ =~= seq![b'R', b'I', b'F', b'F']);
    }
    r
}

// ---------------------------------------------------------------------------
// Option arguments
// ---------------------------------------------------------------------------

pub proof fn lemma_dec_nonneg(s: Seq<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> is_digit(#[trigger] s[i]),
    ensures
        dec(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        assert forall|i: int| 0 <= i < s.drop_last().len() implies is_digit(#[trigger] s.drop_last()[i]) by {
            assert(s.drop_last()[i] == s[i]);
        }
        lemma_dec_nonneg(s.drop_last());
    }
}

pub proof fn lemma_dec_mono(s: Seq<u8>, k: int)
    requires
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> is_digit(#[trigger] s[i]),
    ensures
        dec(s.take(k)) <= dec(s),
    decreases s.len() - k,
{
    if k == s.len() {
        assert(s.take(k) =~= s);
    } else {
        lemma_dec_mono(s, k + 1);
        let t = s.take(k + 1);
        assert(t.drop_last() =~= s.take(k));
        assert(t.last() == s[k]);
        assert(is_digit(s[k]));
        assert forall|i: int| 0 <= i < s.take(k).len() implies is_digit(#[trigger] s.take(k)[i]) by {
            assert(s.take(k)[i] == s[i]);
        }
        lemma_dec_nonneg(s.take(k));
    }
}

/// `num`.
pub fn num_x(s: &[u8]) -> (r: Result<u32, Fail>)
    ensures
        r is Ok <==> num(s@) is Some,
        r is Ok ==> num(s@) == Some(r->Ok_0),
        r is Ok ==> r->Ok_0 <= 65535,
{
    let mut v: u32 = 0;
    let mut i = 0;
    proof {
        assert(s@.take(0) =~= Seq::<u8>::empty());
    }
    while i < s.len()
        invariant
            i <= s.len(),
            v == dec(s@.take(i as int)),
            v <= 65535,
            forall|j: int| 0 <= j < i ==> is_digit(#[trigger] s@[j]),
        decreases s.len() - i,
    {
        let c = s[i];
        if c < b'0' || c > b'9' {
            proof {
                assert(!is_digit(s@[i as int]));
            }
            return Err(Fail::BadUrl("Invalid number"));
        }
        proof {
            assert(s@.take(i + 1).drop_last() =~= s@.take(i as int));
            assert(s@.take(i + 1).last() == c);
        }
        let nv = v * 10 + (c - b'0') as u32;
        if nv > 65535 {
            proof {
                if forall|j: int| 0 <= j < s@.len() ==> is_digit(#[trigger] s@[j]) {
                    lemma_dec_mono(s@, i + 1);
                }
            }
            return Err(Fail::BadUrl("Size too large"));
        }
        v = nv;
        i += 1;
    }
    proof {
        assert(s@.take(i as int) =~= s@);
    }
    Ok(v)
}

/// `boolean`.
pub fn boolean_x(s: &[u8]) -> (r: Result<bool, Fail>)
    ensures
        r is Ok <==> boolean(s@) is Some,
        r is Ok ==> boolean(s@) == Some(r->Ok_0),
{
    if is_1(s) || is_t(s) || is_true(s) {
        Ok(true)
    } else if s.len() == 0 || is_0(s) || is_f(s) || is_false(s) {
        Ok(false)
    } else {
        Err(Fail::BadUrl("Invalid boolean"))
    }
}

/// `mode`.
pub fn mode_x(s: &[u8]) -> (r: Result<Mode, Fail>)
    ensures
        r is Ok <==> mode(s@) is Some,
        r is Ok ==> mode(s@) == Some(r->Ok_0),
{
    if is_fit(s) {
        Ok(Mode::Fit)
    } else if is_fill(s) {
        Ok(Mode::Fill)
    } else if is_force(s) {
        Ok(Mode::Force)
    } else {
        Err(Fail::BadUrl("Unsupported resizing type"))
    }
}

/// `format`.
pub fn format_x(f: Format, s: &[u8]) -> (r: Result<Format, Fail>)
    ensures
        r is Ok <==> format(f, s@) is Some,
        r is Ok ==> format(f, s@) == Some(r->Ok_0),
{
    if s.len() == 0 {
        Ok(f)
    } else if is_png(s) || is_best(s) {
        Ok(Format::Png)
    } else if is_jpg(s) || is_jpeg(s) {
        Ok(Format::Jpeg)
    } else if is_webp(s) {
        Ok(Format::Webp)
    } else {
        Err(Fail::Unprocessable("Only PNG, JPEG and WebP output are supported"))
    }
}

/// `filter`.
pub fn filter_x(s: &[u8]) -> (r: Result<Filter, Fail>)
    ensures
        r is Ok <==> filter(s@) is Some,
        r is Ok ==> filter(s@) == Some(r->Ok_0),
{
    if is_lanczos3(s) {
        Ok(Filter::Lanczos3)
    } else if is_lanczos2(s) {
        Ok(Filter::Lanczos2)
    } else if is_cubic(s) {
        Ok(Filter::Cubic)
    } else if is_linear(s) {
        Ok(Filter::Linear)
    } else if is_nearest(s) {
        Ok(Filter::Nearest)
    } else if is_area(s) {
        Ok(Filter::Area)
    } else {
        Err(Fail::BadUrl("Invalid resizing algorithm"))
    }
}

/// `hexv`.
pub fn hexv_x(c: u8) -> (r: i32)
    ensures
        r == hexv(c),
{
    if b'0' <= c && c <= b'9' {
        (c - b'0') as i32
    } else if b'a' <= c && c <= b'f' {
        (c - b'a') as i32 + 10
    } else if b'A' <= c && c <= b'F' {
        (c - b'A') as i32 + 10
    } else {
        -1
    }
}

/// `comp`.
pub fn comp_x(s: &[u8]) -> (r: Result<u8, Fail>)
    ensures
        r is Ok <==> comp(s@) is Some,
        r is Ok ==> comp(s@) == Some(r->Ok_0),
{
    let bad = Fail::BadUrl("Invalid background");
    match num_x(s) {
        Ok(v) => if s.len() > 0 && v <= 255 {
            Ok(v as u8)
        } else {
            Err(bad)
        },
        Err(_) => Err(bad),
    }
}

/// Argument `i` of an option split into `p` (its name and arguments).
pub fn arg_x(p: &Vec<Vec<u8>>, i: usize) -> (r: Vec<u8>)
    requires
        p@.len() >= 1,
        i < 8,
    ensures
        r@ == arg(views(p@).skip(1), i as int),
{
    if i + 1 < p.len() {
        p[i + 1].clone()
    } else {
        Vec::new()
    }
}

/// `background` of the arguments of `p`.
pub fn background_x(p: &Vec<Vec<u8>>) -> (r: Result<Option<[u8; 3]>, Fail>)
    requires
        p@.len() >= 1,
    ensures
        r is Ok <==> background(views(p@).skip(1)) is Some,
        r is Ok ==> background(views(p@).skip(1)) == Some(r->Ok_0),
{
    let ghost a = views(p@).skip(1);
    let n = p.len() - 1;
    let bad = Fail::BadUrl("Invalid background");
    if n == 0 || (n == 1 && p[1].len() == 0) {
        Ok(None)
    } else if n == 1 && p[1].len() == 6 {
        let h = p[1].as_slice();
        proof {
            assert(a.len() == 1);
            assert(a[0] == h@);
        }
        let mut i = 0;
        while i < 6
            invariant
                a == views(p@).skip(1),
                a.len() == 1,
                h@ == a[0],
                h@.len() == 6,
                i <= 6,
                forall|j: int| 0 <= j < i ==> hexv(#[trigger] a[0][j]) >= 0,
            decreases 6 - i,
        {
            if hexv_x(h[i]) < 0 {
                proof {
                    assert(hexv(a[0][i as int]) < 0);
                    assert(!(forall|j: int| 0 <= j < 6 ==> hexv(#[trigger] a[0][j]) >= 0));
                    assert(a.len() == 1 && a[0].len() == 6);
                    assert(background(a) is None);
                }
                return Err(bad);
            }
            i += 1;
        }
        let r = (16 * hexv_x(h[0]) + hexv_x(h[1])) as u8;
        let g = (16 * hexv_x(h[2]) + hexv_x(h[3])) as u8;
        let b = (16 * hexv_x(h[4]) + hexv_x(h[5])) as u8;
        Ok(Some([r, g, b]))
    } else if n == 3 {
        let r = comp_x(p[1].as_slice());
        let g = comp_x(p[2].as_slice());
        let b = comp_x(p[3].as_slice());
        match (r, g, b) {
            (Ok(r), Ok(g), Ok(b)) => Ok(Some([r, g, b])),
            _ => Err(bad),
        }
    } else {
        Err(bad)
    }
}

// ---------------------------------------------------------------------------
// Options
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Geometry option arguments
// ---------------------------------------------------------------------------

pub open spec fn pw(n: int) -> int
    decreases n,
{
    if n <= 0 {
        1
    } else {
        10 * pw(n - 1)
    }
}

pub proof fn lemma_dec_bound(s: Seq<u8>)
    requires
        all_digits(s),
    ensures
        0 <= dec(s) < pw(s.len() as int),
    decreases s.len(),
{
    if s.len() > 0 {
        assert(all_digits(s.drop_last())) by {
            assert forall|i: int| 0 <= i < s.drop_last().len() implies is_digit(#[trigger] s.drop_last()[i]) by {
                assert(s.drop_last()[i] == s[i]);
            }
        }
        lemma_dec_bound(s.drop_last());
        assert(is_digit(s[s.len() - 1]));
    }
}

/// `fixed4`, as an `F1`-unit number.
pub fn fixed4_x(s: &[u8]) -> (r: Result<u32, Fail>)
    ensures
        r is Ok <==> fixed4(s@) is Some,
        r is Ok ==> fixed4(s@) == Some(r->Ok_0 as int),
        r is Ok ==> r->Ok_0 <= 655359999,
{
    let bad = Fail::BadUrl("Invalid number");
    let d = find_x(s, b'.', 0);
    let ip = sub(s, 0, d);
    let fp = if d < s.len() {
        sub(s, d + 1, s.len())
    } else {
        Vec::new()
    };
    proof {
        assert(ip@ =~= s@.take(d as int));
        if d < s.len() {
            assert(fp@ =~= s@.skip(d + 1));
        } else {
            assert(fp@ =~= Seq::<u8>::empty());
        }
    }
    if s.len() == 0 || (ip.len() == 0 && fp.len() == 0) || fp.len() > 4 {
        return Err(bad);
    }
    let iv = match num_x(ip.as_slice()) {
        Ok(v) => v,
        Err(_) => {
            return Err(bad);
        },
    };
    proof {
        if all_digits(fp@) {
            lemma_dec_bound(fp@);
            assert(pw(fp@.len() as int) <= 10000) by {
                assert(pw(0) == 1 && pw(1) == 10 && pw(2) == 100 && pw(3) == 1000 && pw(4) == 10000) by {
                    reveal_with_fuel(pw, 5);
                }
            }
        }
    }
    let fv = match num_x(fp.as_slice()) {
        Ok(v) => v,
        Err(_) => {
            return Err(bad);
        },
    };
    let m: u32 = if fp.len() == 0 {
        10000
    } else if fp.len() == 1 {
        1000
    } else if fp.len() == 2 {
        100
    } else if fp.len() == 3 {
        10
    } else {
        1
    };
    proof {
        assert(iv <= 65535);
        assert(iv * 10000 <= 655350000) by (nonlinear_arith)
            requires
                iv <= 65535,
        ;
        assert(m == pow10(4 - fp@.len()));
        assert(pw(fp@.len() as int) * m == 10000) by {
            reveal_with_fuel(pw, 5);
            if fp@.len() == 0 {
            } else if fp@.len() == 1 {
            } else if fp@.len() == 2 {
            } else if fp@.len() == 3 {
            } else {
                assert(fp@.len() == 4);
            }
        }
        assert(fv * m <= 9999) by (nonlinear_arith)
            requires
                fv < pw(fp@.len() as int),
                fp@.len() <= 4,
                m == pow10(4 - fp@.len()),
                pw(fp@.len() as int) * m == 10000,
                fv >= 0,
        ;
        assert(num(ip@) == Some(iv));
        assert(all_digits(ip@));
        lemma_dec_nonneg(ip@);
        assert(dec(ip@) == iv);
        assert(num(fp@) == Some(fv));
        lemma_dec_nonneg(fp@);
        assert(all_digits(fp@) && dec(fp@) == fv);
        let d = find(s@, b'.', 0);
        assert(ip@ == s@.take(d));
        assert(fp@ == (if d < s@.len() { s@.skip(d + 1) } else { Seq::empty() }));
        assert(fixed4(s@) == Some(dec(ip@) * F1 + dec(fp@) * pow10(4 - fp@.len())));
    }
    Ok(iv * 10000 + fv * m)
}

/// `fixed4z`.
pub fn fixed4z_x(s: &[u8]) -> (r: Result<u32, Fail>)
    ensures
        r is Ok <==> fixed4z(s@) is Some,
        r is Ok ==> fixed4z(s@) == Some(r->Ok_0 as int),
        r is Ok ==> r->Ok_0 <= 655359999,
{
    if s.len() == 0 {
        Ok(0)
    } else {
        fixed4_x(s)
    }
}

/// `sint`.
pub fn sint_x(s: &[u8]) -> (r: Result<i32, Fail>)
    ensures
        r is Ok <==> sint(s@) is Some,
        r is Ok ==> sint(s@) == Some(r->Ok_0 as int),
        r is Ok ==> -65535 <= r->Ok_0 <= 65535,
{
    if s.len() > 0 && s[0] == b'-' {
        let t = sub(s, 1, s.len());
        proof {
            assert(t@ =~= s@.skip(1));
        }
        match num_x(t.as_slice()) {
            Ok(v) => if s.len() > 1 {
                Ok(-(v as i32))
            } else {
                Err(Fail::BadUrl("Invalid offset"))
            },
            Err(e) => Err(e),
        }
    } else {
        match num_x(s) {
            Ok(v) => Ok(v as i32),
            Err(e) => Err(e),
        }
    }
}

/// `gkind`.
pub fn gkind_x(s: &[u8]) -> (r: Result<GKind, Fail>)
    ensures
        r is Ok <==> gkind(s@) is Some,
        r is Ok ==> gkind(s@) == Some(r->Ok_0),
{
    if s.len() == 0 || is_ce(s) {
        Ok(GKind::Ce)
    } else if is_no(s) {
        Ok(GKind::No)
    } else if is_so(s) {
        Ok(GKind::So)
    } else if is_ea(s) {
        Ok(GKind::Ea)
    } else if is_we(s) {
        Ok(GKind::We)
    } else if is_noea(s) {
        Ok(GKind::NoEa)
    } else if is_nowe(s) {
        Ok(GKind::NoWe)
    } else if is_soea(s) {
        Ok(GKind::SoEa)
    } else if is_sowe(s) {
        Ok(GKind::SoWe)
    } else if is_fp(s) {
        Ok(GKind::Fp)
    } else if is_sm(s) {
        Ok(GKind::Sm)
    } else {
        Err(Fail::BadUrl("Invalid gravity"))
    }
}

/// What `geo_ok` needs of a gravity.
pub open spec fn grav_ok(g: Gravity) -> bool {
    -65535 <= g.x <= 65535 && -65535 <= g.y <= 65535
}

/// `gravity` from argument `i` of the option split into `p`.
pub fn gravity_x(p: &Vec<Vec<u8>>, i: usize) -> (r: Result<Gravity, Fail>)
    requires
        p@.len() >= 1,
        i < 6,
    ensures
        r is Ok <==> gravity(views(p@).skip(1), i as int) is Some,
        r is Ok ==> gravity(views(p@).skip(1), i as int) == Some(r->Ok_0),
        r is Ok ==> grav_ok(r->Ok_0),
{
    let k = gkind_x(arg_x(p, i).as_slice())?;
    match k {
        GKind::Fp => {
            let x = fixed4_x(arg_x(p, i + 1).as_slice())?;
            let y = fixed4_x(arg_x(p, i + 2).as_slice())?;
            if x > 10000 || y > 10000 {
                return Err(Fail::BadUrl("Invalid focus point"));
            }
            Ok(Gravity { kind: GKind::Fp, x: x as i32, y: y as i32 })
        },
        _ => {
            let x = sint_x(arg_x(p, i + 1).as_slice())?;
            let y = sint_x(arg_x(p, i + 2).as_slice())?;
            Ok(Gravity { kind: k, x, y })
        },
    }
}

/// `ogravity`.
pub fn ogravity_x(p: &Vec<Vec<u8>>, i: usize) -> (r: Result<Option<Gravity>, Fail>)
    requires
        p@.len() >= 1,
        i < 6,
    ensures
        r is Ok <==> ogravity(views(p@).skip(1), i as int) is Some,
        r is Ok ==> ogravity(views(p@).skip(1), i as int) == Some(r->Ok_0),
        r matches Ok(Some(g)) ==> grav_ok(g),
{
    if arg_x(p, i).len() == 0 {
        Ok(None)
    } else {
        let g = gravity_x(p, i)?;
        Ok(Some(g))
    }
}

/// `ext`: `extend`'s arguments at the end of `resize` and `size`.
pub fn ext_x(o: Options, p: &Vec<Vec<u8>>, i: usize) -> (r: Result<Options, Fail>)
    requires
        p@.len() >= 1,
        i < 5,
    ensures
        r is Ok <==> ext(o, views(p@).skip(1), i as int) is Some,
        r is Ok ==> ext(o, views(p@).skip(1), i as int) == Some(r->Ok_0),
        r matches Ok(v) ==> v.extend_g == o.extend_g || v.extend_g is None || grav_ok(v.extend_g->Some_0),
{
    let a = arg_x(p, i);
    if a.len() == 0 {
        Ok(o)
    } else {
        let e = boolean_x(a.as_slice())?;
        let g = ogravity_x(p, i + 1)?;
        Ok(Options { extend: e, extend_g: g, ..o })
    }
}

/// `padding`.
pub fn padding_x(p: &Vec<Vec<u8>>) -> (r: Result<[u32; 4], Fail>)
    requires
        p@.len() >= 1,
    ensures
        r is Ok <==> padding(views(p@).skip(1)) is Some,
        r is Ok ==> padding(views(p@).skip(1)) == Some(r->Ok_0),
        r is Ok ==> forall|i: int| 0 <= i < 4 ==> #[trigger] r->Ok_0[i] <= 65535,
{
    if p.len() > 5 {
        return Err(Fail::BadUrl("Invalid padding"));
    }
    let t = num_x(arg_x(p, 0).as_slice());
    let a1 = arg_x(p, 1);
    let r = if a1.len() == 0 {
        t.clone()
    } else {
        num_x(a1.as_slice())
    };
    let a2 = arg_x(p, 2);
    let b = if a2.len() == 0 {
        t.clone()
    } else {
        num_x(a2.as_slice())
    };
    let a3 = arg_x(p, 3);
    let l = if a3.len() == 0 {
        r.clone()
    } else {
        num_x(a3.as_slice())
    };
    match (t, r, b, l) {
        (Ok(t), Ok(r), Ok(b), Ok(l)) => {
            let out = [t, r, b, l];
            proof {
                assert(out[0] == t && out[1] == r && out[2] == b && out[3] == l);
                assert forall|i: int| 0 <= i < 4 implies #[trigger] out[i] <= 65535 by {
                    if i == 0 {
                    } else if i == 1 {
                    } else if i == 2 {
                    } else {
                    }
                }
            }
            Ok(out)
        },
        _ => Err(Fail::BadUrl("Invalid padding")),
    }
}

/// `apply`.
#[verifier::rlimit(400)]
pub fn apply_x(o: Options, seg: &[u8]) -> (r: Result<Options, Fail>)
    ensures
        r is Ok <==> apply(o, seg@) is Some,
        r is Ok ==> apply(o, seg@) == Some(r->Ok_0),
{
    let p = split_x(seg, b':');
    let n = p[0].as_slice();
    proof {
        assert(views(p@)[0] == n@);
    }
    if is_resize(n) || is_rs(n) {
        let a0 = arg_x(&p, 0);
        let m = if a0.len() == 0 {
            o.mode
        } else {
            mode_x(a0.as_slice())?
        };
        let w = num_x(arg_x(&p, 1).as_slice())?;
        let h = num_x(arg_x(&p, 2).as_slice())?;
        let e = boolean_x(arg_x(&p, 3).as_slice())?;
        ext_x(Options { mode: m, w, h, enlarge: e, ..o }, &p, 4)
    } else if is_size(n) || is_s(n) {
        let w = num_x(arg_x(&p, 0).as_slice())?;
        let h = num_x(arg_x(&p, 1).as_slice())?;
        let e = boolean_x(arg_x(&p, 2).as_slice())?;
        ext_x(Options { w, h, enlarge: e, ..o }, &p, 3)
    } else if is_resizing_type(n) || is_rt(n) {
        let m = mode_x(arg_x(&p, 0).as_slice())?;
        Ok(Options { mode: m, ..o })
    } else if is_width(n) || is_w(n) {
        let w = num_x(arg_x(&p, 0).as_slice())?;
        Ok(Options { w, ..o })
    } else if is_height(n) || is_h(n) {
        let h = num_x(arg_x(&p, 0).as_slice())?;
        Ok(Options { h, ..o })
    } else if is_enlarge(n) || is_el(n) {
        let e = boolean_x(arg_x(&p, 0).as_slice())?;
        Ok(Options { enlarge: e, ..o })
    } else if is_resizing_algorithm(n) || is_ra(n) {
        let f = filter_x(arg_x(&p, 0).as_slice())?;
        Ok(Options { filter: f, ..o })
    } else if is_background(n) || is_bg(n) {
        let b = background_x(&p)?;
        Ok(Options { background: b, ..o })
    } else if is_quality(n) || is_q(n) {
        let q = num_x(arg_x(&p, 0).as_slice())?;
        if q > 100 {
            return Err(Fail::BadUrl("Invalid quality"));
        }
        Ok(Options { quality: q, ..o })
    } else if is_strip_metadata(n) || is_sm(n) || is_cachebuster(n) || is_cb(n) {
        Ok(o)
    } else if is_format(n) || is_f(n) || is_ext(n) {
        let f = format_x(o.format, arg_x(&p, 0).as_slice())?;
        Ok(Options { format: f, ..o })
    } else if is_gravity(n) || is_g(n) {
        let g = gravity_x(&p, 0)?;
        Ok(Options { gravity: g, ..o })
    } else if is_crop(n) || is_c(n) {
        let w = fixed4z_x(arg_x(&p, 0).as_slice())?;
        let h = fixed4z_x(arg_x(&p, 1).as_slice())?;
        let g = ogravity_x(&p, 2)?;
        Ok(Options { crop_w: w, crop_h: h, crop_g: g, ..o })
    } else if is_extend(n) || is_ex(n) {
        let e = boolean_x(arg_x(&p, 0).as_slice())?;
        let g = ogravity_x(&p, 1)?;
        Ok(Options { extend: e, extend_g: g, ..o })
    } else if is_padding(n) || is_pd(n) {
        let pd = padding_x(&p)?;
        Ok(Options { pad: pd, ..o })
    } else if is_dpr(n) {
        let d = fixed4_x(arg_x(&p, 0).as_slice())?;
        if d < 1 || d > 80000 {
            return Err(Fail::BadUrl("Invalid dpr"));
        }
        Ok(Options { dpr: d, ..o })
    } else if is_rotate(n) || is_rot(n) {
        let r = num_x(arg_x(&p, 0).as_slice())?;
        if r % 90 != 0 {
            return Err(Fail::BadUrl("Rotation angle must be a multiple of 90"));
        }
        Ok(Options { rotate: (r / 90) % 4, ..o })
    } else if is_flip(n) || is_fl(n) {
        let h = boolean_x(arg_x(&p, 0).as_slice())?;
        let v = boolean_x(arg_x(&p, 1).as_slice())?;
        Ok(Options { flip_h: h, flip_v: v, ..o })
    } else {
        apply2_x(o, &p)
    }
}

/// Whether `s` is `filename`.
pub fn is_filename(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'i', b'l', b'e', b'n', b'a', b'm', b'e']),
{
    let t: [u8; 8] = [b'f', b'i', b'l', b'e', b'n', b'a', b'm', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'i', b'l', b'e', b'n', b'a', b'm', b'e']);
    }
    r
}

/// Whether `s` is `fn`.
pub fn is_fn(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'f', b'n']),
{
    let t: [u8; 2] = [b'f', b'n'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'f', b'n']);
    }
    r
}

/// Whether `s` is `expires`.
pub fn is_expires(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'e', b'x', b'p', b'i', b'r', b'e', b's']),
{
    let t: [u8; 7] = [b'e', b'x', b'p', b'i', b'r', b'e', b's'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'e', b'x', b'p', b'i', b'r', b'e', b's']);
    }
    r
}

/// Whether `s` is `exp`.
pub fn is_exp(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'e', b'x', b'p']),
{
    let t: [u8; 3] = [b'e', b'x', b'p'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'e', b'x', b'p']);
    }
    r
}

/// Whether `s` is `return_attachment`.
pub fn is_return_attachment(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'e', b't', b'u', b'r', b'n', b'_', b'a', b't', b't', b'a', b'c', b'h', b'm', b'e', b'n', b't']),
{
    let t: [u8; 17] = [b'r', b'e', b't', b'u', b'r', b'n', b'_', b'a', b't', b't', b'a', b'c', b'h', b'm', b'e', b'n', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'e', b't', b'u', b'r', b'n', b'_', b'a', b't', b't', b'a', b'c', b'h', b'm', b'e', b'n', b't']);
    }
    r
}

/// Whether `s` is `att`.
pub fn is_att(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'a', b't', b't']),
{
    let t: [u8; 3] = [b'a', b't', b't'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'a', b't', b't']);
    }
    r
}

/// Whether `s` is `auto_rotate`.
pub fn is_auto_rotate(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'a', b'u', b't', b'o', b'_', b'r', b'o', b't', b'a', b't', b'e']),
{
    let t: [u8; 11] = [b'a', b'u', b't', b'o', b'_', b'r', b'o', b't', b'a', b't', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'a', b'u', b't', b'o', b'_', b'r', b'o', b't', b'a', b't', b'e']);
    }
    r
}

/// Whether `s` is `ar`.
pub fn is_ar(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'a', b'r']),
{
    let t: [u8; 2] = [b'a', b'r'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'a', b'r']);
    }
    r
}

/// Whether `s` is `raw`.
pub fn is_raw(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'a', b'w']),
{
    let t: [u8; 3] = [b'r', b'a', b'w'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'a', b'w']);
    }
    r
}

/// Whether `s` is `skip_processing`.
pub fn is_skip_processing(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'k', b'i', b'p', b'_', b'p', b'r', b'o', b'c', b'e', b's', b's', b'i', b'n', b'g']),
{
    let t: [u8; 15] = [b's', b'k', b'i', b'p', b'_', b'p', b'r', b'o', b'c', b'e', b's', b's', b'i', b'n', b'g'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'k', b'i', b'p', b'_', b'p', b'r', b'o', b'c', b'e', b's', b's', b'i', b'n', b'g']);
    }
    r
}

/// Whether `s` is `skp`.
pub fn is_skp(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'k', b'p']),
{
    let t: [u8; 3] = [b's', b'k', b'p'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'k', b'p']);
    }
    r
}

/// Whether `s` is `webp`.
pub fn is_webp(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'w', b'e', b'b', b'p']),
{
    let t: [u8; 4] = [b'w', b'e', b'b', b'p'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'w', b'e', b'b', b'p']);
    }
    r
}

/// Whether `s` is `gif`.
pub fn is_gif(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'g', b'i', b'f']),
{
    let t: [u8; 3] = [b'g', b'i', b'f'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'g', b'i', b'f']);
    }
    r
}

/// Whether `s` is `blur`.
pub fn is_blur(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'b', b'l', b'u', b'r']),
{
    let t: [u8; 4] = [b'b', b'l', b'u', b'r'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'b', b'l', b'u', b'r']);
    }
    r
}

/// Whether `s` is `bl`.
pub fn is_bl(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'b', b'l']),
{
    let t: [u8; 2] = [b'b', b'l'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'b', b'l']);
    }
    r
}

/// Whether `s` is `sharpen`.
pub fn is_sharpen(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'h', b'a', b'r', b'p', b'e', b'n']),
{
    let t: [u8; 7] = [b's', b'h', b'a', b'r', b'p', b'e', b'n'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'h', b'a', b'r', b'p', b'e', b'n']);
    }
    r
}

/// Whether `s` is `sh`.
pub fn is_sh(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b's', b'h']),
{
    let t: [u8; 2] = [b's', b'h'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b's', b'h']);
    }
    r
}

/// Whether `s` is `watermark`.
pub fn is_watermark(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'w', b'a', b't', b'e', b'r', b'm', b'a', b'r', b'k']),
{
    let t: [u8; 9] = [b'w', b'a', b't', b'e', b'r', b'm', b'a', b'r', b'k'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'w', b'a', b't', b'e', b'r', b'm', b'a', b'r', b'k']);
    }
    r
}

/// Whether `s` is `wm`.
pub fn is_wm(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'w', b'm']),
{
    let t: [u8; 2] = [b'w', b'm'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'w', b'm']);
    }
    r
}

/// Whether `s` is `re`.
pub fn is_re(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == seq![b'r', b'e']),
{
    let t: [u8; 2] = [b'r', b'e'];
    let r = eq(s, &t);
    proof {
        assert(t@ =~= seq![b'r', b'e']);
    }
    r
}

/// `watermark_opt` of the arguments of `p`.
pub fn watermark_opt_x(p: &Vec<Vec<u8>>) -> (r: Result<(u32, Gravity, bool, u32), Fail>)
    requires
        p@.len() >= 1,
    ensures
        r is Ok <==> watermark_opt(views(p@).skip(1)) is Some,
        r is Ok ==> watermark_opt(views(p@).skip(1)) == Some(r->Ok_0),
        r is Ok ==> grav_ok(r->Ok_0.1),
{
    let tile = is_re(arg_x(p, 1).as_slice());
    let g = if tile {
        let x = sint_x(arg_x(p, 2).as_slice())?;
        let y = sint_x(arg_x(p, 3).as_slice())?;
        Gravity { kind: GKind::Ce, x, y }
    } else {
        gravity_x(p, 1)?
    };
    let op = fixed4_x(arg_x(p, 0).as_slice())?;
    let sc = fixed4z_x(arg_x(p, 4).as_slice())?;
    if op > 10000 {
        return Err(Fail::BadUrl("Invalid watermark opacity"));
    }
    Ok((op, g, tile, sc))
}

/// `num64`.
pub fn num64_x(s: &[u8]) -> (r: Result<u64, Fail>)
    ensures
        r is Ok <==> num64(s@) is Some,
        r is Ok ==> num64(s@) == Some(r->Ok_0),
{
    if s.len() == 0 {
        return Err(Fail::BadUrl("Invalid number"));
    }
    let mut v: u64 = 0;
    let mut i = 0;
    proof {
        assert(s@.take(0) =~= Seq::<u8>::empty());
    }
    while i < s.len()
        invariant
            i <= s.len(),
            v == dec(s@.take(i as int)),
            v <= 0x7fff_ffff_ffff_ffff,
            forall|j: int| 0 <= j < i ==> is_digit(#[trigger] s@[j]),
        decreases s.len() - i,
    {
        let c = s[i];
        if c < b'0' || c > b'9' {
            proof {
                assert(!is_digit(s@[i as int]));
            }
            return Err(Fail::BadUrl("Invalid number"));
        }
        proof {
            assert(s@.take(i + 1).drop_last() =~= s@.take(i as int));
            assert(s@.take(i + 1).last() == c);
        }
        let nv = v as u128 * 10 + (c - b'0') as u128;
        if nv > 0x7fff_ffff_ffff_ffff {
            proof {
                if all_digits(s@) {
                    lemma_dec_mono(s@, i + 1);
                }
            }
            return Err(Fail::BadUrl("Number too large"));
        }
        v = nv as u64;
        i += 1;
    }
    proof {
        assert(s@.take(i as int) =~= s@);
    }
    Ok(v)
}

/// `kind_name`.
pub fn kind_name_x(s: &[u8]) -> (r: Option<Kind>)
    ensures
        r == kind_name(s@),
{
    if is_jpg(s) || is_jpeg(s) {
        Some(Kind::Jpeg)
    } else if is_png(s) {
        Some(Kind::Png)
    } else if is_webp(s) {
        Some(Kind::Webp)
    } else if is_gif(s) {
        Some(Kind::Gif)
    } else {
        None
    }
}

/// `kind_bit`.
pub fn kind_bit_x(k: Kind) -> (r: u32)
    ensures
        r == kind_bit(k),
{
    match k {
        Kind::Jpeg => 1,
        Kind::Png => 2,
        Kind::Webp => 4,
        Kind::Gif => 8,
    }
}

/// `kinds` of all the arguments of `p`.
pub fn kinds_x(p: &Vec<Vec<u8>>) -> (r: Result<u32, Fail>)
    requires
        p@.len() >= 1,
    ensures
        r is Ok <==> kinds(views(p@).skip(1), p@.len() - 1) is Some,
        r is Ok ==> kinds(views(p@).skip(1), p@.len() - 1) == Some(r->Ok_0),
{
    let ghost a = views(p@).skip(1);
    let mut m: u32 = 0;
    let mut j: usize = 1;
    while j < p.len()
        invariant
            1 <= j <= p@.len(),
            a == views(p@).skip(1),
            a.len() == p@.len() - 1,
            kinds(a, j - 1) == Some(m),
        decreases p.len() - j,
    {
        proof {
            assert(a[j - 1] == p@[j as int]@);
        }
        match kind_name_x(p[j].as_slice()) {
            Some(k) => {
                m = m | kind_bit_x(k);
            },
            None => {
                proof {
                    lemma_kinds_none(a, j as int, a.len() as int);
                }
                return Err(Fail::BadUrl("Invalid image format in skip processing"));
            },
        }
        j += 1;
    }
    Ok(m)
}

pub proof fn lemma_kinds_none(a: Seq<Seq<u8>>, i: int, n: int)
    requires
        1 <= i <= n,
        kinds(a, i) is None,
    ensures
        kinds(a, n) is None,
    decreases n - i,
{
    if i < n {
        lemma_kinds_none(a, i, n - 1);
    }
}

/// `unb64`.
pub fn unb64_x(body: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r is Some <==> unb64(body@) is Some,
        r is Some ==> unb64(body@) == Some(r->Some_0@),
{
    let unpadded = if body.len() > 0 && body[body.len() - 1] == b'=' {
        let x = sub(body, 0, body.len() - 1);
        proof {
            assert(x@ =~= body@.drop_last());
        }
        x
    } else {
        let x = sub(body, 0, body.len());
        proof {
            assert(x@ =~= body@);
        }
        x
    };
    match b64_x(true, false, unpadded.as_slice()) {
        Some(u) => Some(u),
        None => b64_x(true, true, body),
    }
}

/// `fname_arg` of the arguments of `p`.
pub fn fname_arg_x(p: &Vec<Vec<u8>>) -> (r: Result<Vec<u8>, Fail>)
    requires
        p@.len() >= 1,
    ensures
        r is Ok <==> fname_arg(views(p@).skip(1)) is Some,
        r is Ok ==> fname_arg(views(p@).skip(1)) == Some(r->Ok_0@),
{
    let enc = boolean_x(arg_x(p, 1).as_slice())?;
    let a0 = arg_x(p, 0);
    if enc {
        match unb64_x(a0.as_slice()) {
            Some(v) => Ok(v),
            None => Err(Fail::BadUrl("Invalid filename encoding")),
        }
    } else {
        let mut d: Vec<u8> = Vec::new();
        verilith_text::percent::decode_to(a0.as_slice(), &mut d);
        proof {
            assert(d@ =~= verilith_text::percent::decode(a0@));
        }
        Ok(d)
    }
}

/// `apply2`, for a segment split into `p`.
#[verifier::rlimit(100)]
pub fn apply2_x(o: Options, p: &Vec<Vec<u8>>) -> (r: Result<Options, Fail>)
    requires
        p@.len() >= 1,
    ensures
        r is Ok <==> apply2(o, views(p@)[0], views(p@).skip(1)) is Some,
        r is Ok ==> apply2(o, views(p@)[0], views(p@).skip(1)) == Some(r->Ok_0),
{
    let n = p[0].as_slice();
    proof {
        assert(views(p@)[0] == n@);
    }
    if is_auto_rotate(n) || is_ar(n) {
        let v = boolean_x(arg_x(p, 0).as_slice())?;
        Ok(Options { auto_rotate: v, ..o })
    } else if is_expires(n) || is_exp(n) {
        let t = num64_x(arg_x(p, 0).as_slice())?;
        Ok(Options { expires: t, ..o })
    } else if is_return_attachment(n) || is_att(n) {
        let v = boolean_x(arg_x(p, 0).as_slice())?;
        Ok(Options { attachment: v, ..o })
    } else if is_raw(n) {
        let v = boolean_x(arg_x(p, 0).as_slice())?;
        Ok(Options { raw: v, ..o })
    } else if is_skip_processing(n) || is_skp(n) {
        let m = kinds_x(p)?;
        Ok(Options { skip: m, ..o })
    } else if is_watermark(n) || is_wm(n) {
        let (op, g, t, sc) = watermark_opt_x(p)?;
        Ok(Options { wm_op: op, wm_g: g, wm_tile: t, wm_scale: sc, ..o })
    } else if is_blur(n) || is_bl(n) {
        let v = fixed4z_x(arg_x(p, 0).as_slice())?;
        Ok(Options { blur: v, ..o })
    } else if is_sharpen(n) || is_sh(n) {
        let v = fixed4z_x(arg_x(p, 0).as_slice())?;
        Ok(Options { sharpen: v, ..o })
    } else if is_filename(n) || is_fn(n) {
        let _ = fname_arg_x(p)?;
        Ok(o)
    } else {
        Err(Fail::BadUrl("Unknown processing option"))
    }
}

/// `fname_of`.
pub fn fname_of_x(seg: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r is Some <==> fname_of(seg@) is Some,
        r is Some ==> fname_of(seg@) == Some(r->Some_0@),
{
    let p = split_x(seg, b':');
    let n = p[0].as_slice();
    proof {
        assert(views(p@)[0] == n@);
    }
    if is_filename(n) || is_fn(n) {
        match fname_arg_x(&p) {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    } else {
        None
    }
}

/// `last_fname(segs, n)`.
pub fn last_fname_x(segs: &Vec<Vec<u8>>, n: usize) -> (r: Option<Vec<u8>>)
    requires
        n <= segs@.len(),
    ensures
        r is Some <==> last_fname(views(segs@), n as int) is Some,
        r is Some ==> last_fname(views(segs@), n as int) == Some(r->Some_0@),
{
    let ghost sv = views(segs@);
    let mut i = n;
    while i > 0
        invariant
            i <= n <= segs@.len(),
            sv == views(segs@),
            last_fname(sv, n as int) == last_fname(sv, i as int),
        decreases i,
    {
        proof {
            assert(sv[i - 1] == segs@[i - 1]@);
        }
        match fname_of_x(segs[i - 1].as_slice()) {
            Some(v) => {
                return Some(v);
            },
            None => {},
        }
        i -= 1;
    }
    None
}

/// `is_option`.
pub fn is_option_x(seg: &[u8]) -> (r: bool)
    ensures
        r == is_option(seg@),
{
    find_x(seg, b':', 0) < seg.len() && !starts_http(seg) && !starts_local(seg)
}

pub proof fn lemma_nopts(segs: Seq<Seq<u8>>, i: int)
    requires
        0 <= i <= segs.len(),
    ensures
        i <= nopts(segs, i) <= segs.len(),
    decreases segs.len() - i,
{
    if i < segs.len() && is_option(segs[i]) {
        lemma_nopts(segs, i + 1);
    }
}

pub proof fn lemma_apply_none(segs: Seq<Seq<u8>>, m: int, n: int)
    requires
        0 <= m <= n,
        apply_all(segs, m) is None,
    ensures
        apply_all(segs, n) is None,
    decreases n - m,
{
    if n > m {
        lemma_apply_none(segs, m, n - 1);
    }
}

pub fn defaults_x() -> (r: Options)
    ensures
        r == defaults(),
{
    Options {
        mode: Mode::Fit,
        w: 0,
        h: 0,
        enlarge: false,
        background: None,
        format: Format::Png,
        quality: 0,
        filter: Filter::Lanczos3,
        gravity: Gravity { kind: GKind::Ce, x: 0, y: 0 },
        crop_w: 0,
        crop_h: 0,
        crop_g: None,
        extend: false,
        extend_g: None,
        pad: [0, 0, 0, 0],
        dpr: 10000,
        rotate: 0,
        flip_h: false,
        flip_v: false,
        auto_rotate: true,
        expires: 0,
        attachment: false,
        raw: false,
        skip: 0,
        blur: 0,
        sharpen: 0,
        wm_op: 0,
        wm_g: Gravity { kind: GKind::Ce, x: 0, y: 0 },
        wm_tile: false,
        wm_scale: 0,
    }
}

// ---------------------------------------------------------------------------
// Sources
// ---------------------------------------------------------------------------

/// `source`.
pub fn source_x(u: Vec<u8>) -> (r: Result<Source, Fail>)
    ensures
        r is Ok <==> source(u@) is Some,
        r is Ok ==> source(u@) == Some(src_view(r->Ok_0)),
{
    if starts_local_url(u.as_slice()) {
        let p = sub(u.as_slice(), 8, u.len());
        proof {
            assert(p@ =~= u@.skip(8));
        }
        Ok(Source::Local(p))
    } else if starts_http_url(u.as_slice()) || starts_https_url(u.as_slice()) {
        Ok(Source::Http(u))
    } else {
        Err(Fail::BadUrl("Unsupported source URL scheme"))
    }
}

/// `plain` of the segments from `f` on.
pub fn plain_x(o: Options, segs: &Vec<Vec<u8>>, f: usize) -> (r: Result<(Options, Source), Fail>)
    requires
        f <= segs@.len(),
    ensures
        r is Ok <==> plain(o, views(segs@).skip(f as int)) is Some,
        r is Ok ==> plain(o, views(segs@).skip(f as int)) == Some((r->Ok_0.0, src_view(r->Ok_0.1))),
{
    let u = join_x(segs, f, b'/');
    let at = rfind_x(u.as_slice(), b'@');
    let (fr, body) = match at {
        Some(a) => {
            let e = sub(u.as_slice(), a + 1, u.len());
            proof {
                assert(e@ =~= u@.skip(a + 1));
            }
            let b = sub(u.as_slice(), 0, a);
            proof {
                assert(b@ =~= u@.take(a as int));
            }
            (format_x(o.format, e.as_slice()), b)
        },
        None => (Ok(o.format), u),
    };
    let mut d: Vec<u8> = Vec::new();
    verilith_text::percent::decode_to(body.as_slice(), &mut d);
    proof {
        assert(d@ =~= verilith_text::percent::decode(body@));
    }
    let s = source_x(d);
    match (fr, s) {
        (Ok(fm), Ok(s)) => Ok((Options { format: fm, ..o }, s)),
        (Err(e), _) => Err(e),
        (_, Err(e)) => Err(e),
    }
}

/// `spec::decode` of base64.
pub fn b64_x(url: bool, pad: bool, s: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r is Some <==> verilith_text::base64::spec::decode(b64(url, pad), s@) is Some,
        r is Some ==> verilith_text::base64::spec::decode(b64(url, pad), s@) == Some(r->Some_0@),
{
    let cfg = verilith_text::base64::spec::Config { url, pad };
    let m = verilith_text::base64::scalar::body_len_exec(cfg, s);
    let n = verilith_text::base64::scalar::dec_len(m);
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            out@.len() == i,
        decreases n - i,
    {
        out.push(0);
        i += 1;
    }
    if verilith_text::base64::scalar::decode_into(cfg, s, out.as_mut_slice()) {
        Some(out)
    } else {
        None
    }
}

/// `encoded` of the segments from `f` on.
pub fn encoded_x(o: Options, segs: &Vec<Vec<u8>>, f: usize) -> (r: Result<(Options, Source), Fail>)
    requires
        f <= segs@.len(),
    ensures
        r is Ok <==> encoded(o, views(segs@).skip(f as int)) is Some,
        r is Ok ==> encoded(o, views(segs@).skip(f as int)) == Some((r->Ok_0.0, src_view(r->Ok_0.1))),
{
    let e = concat_x(segs, f);
    let dot = find_x(e.as_slice(), b'.', 0);
    let fr = if dot < e.len() {
        let x = sub(e.as_slice(), dot + 1, e.len());
        proof {
            assert(x@ =~= e@.skip(dot + 1));
        }
        format_x(o.format, x.as_slice())
    } else {
        Ok(o.format)
    };
    let body = sub(e.as_slice(), 0, dot);
    proof {
        assert(body@ =~= e@.take(dot as int));
    }
    let unpadded = if body.len() > 0 && body[body.len() - 1] == b'=' {
        let x = sub(body.as_slice(), 0, body.len() - 1);
        proof {
            assert(x@ =~= body@.drop_last());
        }
        x
    } else {
        body.clone()
    };
    let u = match b64_x(true, false, unpadded.as_slice()) {
        Some(u) => Some(u),
        None => b64_x(true, true, body.as_slice()),
    };
    match (fr, u) {
        (Ok(fm), Some(u)) => {
            let s = source_x(u)?;
            Ok((Options { format: fm, ..o }, s))
        },
        (Err(e), _) => Err(e),
        (_, None) => Err(Fail::BadUrl("Invalid base64 source URL")),
    }
}

/// `parse`.
#[verifier::rlimit(40)]
pub fn parse_x(path: &[u8]) -> (r: Result<Parts, Fail>)
    ensures
        r is Ok <==> parse(path@) is Some,
        r is Ok ==> ({
            let u = parse(path@)->0;
            &&& 1 <= r->Ok_0.sig_end <= path@.len()
            &&& u.sig_end == r->Ok_0.sig_end
            &&& u.opts == r->Ok_0.opts
            &&& u.src == src_view(r->Ok_0.source)
            &&& u.filename == opt_view(r->Ok_0.filename)
        }),
{
    if path.len() == 0 || path[0] != b'/' {
        return Err(Fail::BadUrl("Invalid path"));
    }
    let ghost rest = path@.skip(1);
    let k = find_x(path, b'/', 1);
    proof {
        lemma_find_skip(path@, b'/', 1, 0);
    }
    if k >= path.len() {
        return Err(Fail::BadUrl("Invalid path"));
    }
    let tail = sub(path, k + 1, path.len());
    proof {
        assert(tail@ =~= rest.skip(k - 1 + 1));
    }
    let segs = split_x(tail.as_slice(), b'/');
    let ghost sv = views(segs@);
    proof {
        assert(sv == split(path@.skip(1).skip(find(path@.skip(1), b'/', 0) + 1), b'/'));
    }
    let mut o = defaults_x();
    let mut i: usize = 0;
    proof {
        lemma_nopts(sv, 0);
    }
    while i < segs.len() && is_option_x(segs[i].as_slice())
        invariant
            sv == views(segs@),
            sv == split(path@.skip(1).skip(find(path@.skip(1), b'/', 0) + 1), b'/'),
            i <= segs@.len(),
            nopts(sv, 0) == nopts(sv, i as int),
            apply_all(sv, i as int) == Some(o),
        decreases segs.len() - i,
    {
        proof {
            assert(sv[i as int] == segs@[i as int]@);
            lemma_nopts(sv, i + 1);
        }
        let r = apply_x(o, segs[i].as_slice());
        match r {
            Ok(o2) => {
                o = o2;
            },
            Err(e) => {
                proof {
                    assert(is_option(sv[i as int]));
                    assert(nopts(sv, i as int) == nopts(sv, i + 1));
                    assert(apply(o, sv[i as int]) is None);
                    assert(apply_all(sv, i + 1) is None);
                    lemma_apply_none(sv, i + 1, nopts(sv, 0));
                    assert(apply_all(sv, nopts(sv, 0)) is None);
                    assert(sv == split(path@.skip(1).skip(find(path@.skip(1), b'/', 0) + 1), b'/'));
                }
                return Err(e);
            },
        }
        i += 1;
    }
    proof {
        if i < segs.len() {
            assert(sv[i as int] == segs@[i as int]@);
        }
        assert(nopts(sv, i as int) == i);
    }
    if i >= segs.len() {
        return Err(Fail::BadUrl("Missing source URL"));
    }
    let first = segs[i].as_slice();
    proof {
        assert(sv[i as int] == first@);
        assert(sv.skip(i + 1) =~= views(segs@).skip(i + 1));
    }
    let r = if is_plain(first) {
        plain_x(o, &segs, i + 1)
    } else if starts_upload(first) && i + 1 == segs.len() {
        if first.len() == 6 {
            proof {
                assert(first@ =~= upload_lit());
            }
            Ok((o, Source::Upload))
        } else if first[6] == b'@' {
            let x = sub(first, 7, first.len());
            proof {
                assert(x@ =~= first@.skip(7));
            }
            match format_x(o.format, x.as_slice()) {
                Ok(fm) => Ok((Options { format: fm, ..o }, Source::Upload)),
                Err(e) => Err(e),
            }
        } else {
            Err(Fail::BadUrl("Invalid upload path"))
        }
    } else {
        encoded_x(o, &segs, i)
    };
    match r {
        Ok((o, s)) => {
            let f = last_fname_x(&segs, i);
            Ok(Parts { sig_end: k, opts: o, source: s, filename: f })
        },
        Err(e) => Err(e),
    }
}

// ---------------------------------------------------------------------------
// Choosing a decoder
// ---------------------------------------------------------------------------

/// `kind`.
pub fn kind_x(d: &[u8]) -> (r: Option<Kind>)
    ensures
        r == kind(d@),
{
    if starts_jpeg_soi(d) {
        Some(Kind::Jpeg)
    } else if starts_png_sig(d) {
        Some(Kind::Png)
    } else if d.len() >= 12 && starts_riff(d) && d[8] == b'W' && d[9] == b'E' && d[10] == b'B' && d[11] == b'P' {
        proof {
            assert(d@.subrange(8, 12) =~= seq![b'W', b'E', b'B', b'P']);
        }
        Some(Kind::Webp)
    } else if starts_gif87(d) || starts_gif89(d) {
        proof {
            if d@.len() >= 12 && starts(d@, seq![b'R', b'I', b'F', b'F']) {
                if d@.subrange(8, 12) == seq![b'W', b'E', b'B', b'P'] {
                    assert(d@.subrange(8, 12)[0] == d@[8]);
                    assert(d@.subrange(8, 12)[1] == d@[9]);
                    assert(d@.subrange(8, 12)[2] == d@[10]);
                    assert(d@.subrange(8, 12)[3] == d@[11]);
                }
            }
        }
        Some(Kind::Gif)
    } else {
        proof {
            if d@.len() >= 12 && starts(d@, seq![b'R', b'I', b'F', b'F']) {
                if d@.subrange(8, 12) == seq![b'W', b'E', b'B', b'P'] {
                    assert(d@.subrange(8, 12)[0] == d@[8]);
                    assert(d@.subrange(8, 12)[1] == d@[9]);
                    assert(d@.subrange(8, 12)[2] == d@[10]);
                    assert(d@.subrange(8, 12)[3] == d@[11]);
                }
            }
        }
        None
    }
}

/// `jpeg_shrink`.
pub fn jpeg_shrink_x(sw: u32, sh: u32, rw: u32, rh: u32) -> (r: u32)
    ensures
        r == jpeg_shrink(sw as int, sh as int, rw as int, rh as int),
{
    let a = sw / if rw < 1 { 1 } else { rw };
    let b = sh / if rh < 1 { 1 } else { rh };
    let s = if a < b { a } else { b };
    if s >= 8 {
        8
    } else if s >= 4 {
        4
    } else if s >= 2 {
        2
    } else {
        1
    }
}

} // verus!
