//! Request paths to file paths, verified (DESIGN.md, "Targets and paths").
//!
//! [`resolve`] is the specification: the path of an origin-form target
//! (`/a/b`, the part before `?`) is split at `/`, each segment is
//! percent-decoded (verilith-text's verified decoder), and the segments are
//! applied in order to a stack: an empty segment or `.` does nothing, `..`
//! pops (and is an error at the root, never a clamp), and any other
//! segment is pushed. A decoded segment holding `/`, `\` or NUL is an
//! error, so `%2f` can never make a separator.
//!
//! The theorem ([`lemma_resolve_safe`]): every component of a resolved path
//! is non-empty, not `.` or `..`, and has no `/`, `\` or NUL. The file
//! opened is the document root followed by those components, so it is
//! inside the root by construction; `openat2(RESOLVE_BENEATH)` (trusted)
//! adds that no symlink leads out. [`resolve_exec`] computes exactly
//! [`resolve`], and [`join`] the bytes handed to the kernel.
use vstd::prelude::*;

use verilith_text::percent::decode_to;
#[cfg(verus_keep_ghost)]
use verilith_text::percent::decode;

verus! {

pub open spec fn bad_byte(b: u8) -> bool {
    b == 0x2f || b == 0x5c || b == 0
}

pub open spec fn is_dot(s: Seq<u8>) -> bool {
    s.len() == 1 && s[0] == 0x2e
}

pub open spec fn is_dotdot(s: Seq<u8>) -> bool {
    s.len() == 2 && s[0] == 0x2e && s[1] == 0x2e
}

/// A component of a file path under the root: the safety property.
pub open spec fn comp_ok(c: Seq<u8>) -> bool {
    c.len() > 0 && !is_dot(c) && !is_dotdot(c) && forall|k: int| 0 <= k < c.len() ==> !bad_byte(#[trigger] c[k])
}

pub open spec fn all_ok(st: Seq<Seq<u8>>) -> bool {
    forall|k: int| 0 <= k < st.len() ==> comp_ok(#[trigger] st[k])
}

/// One decoded segment applied to the stack.
pub open spec fn step(st: Seq<Seq<u8>>, d: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    if exists|k: int| 0 <= k < d.len() && bad_byte(#[trigger] d[k]) {
        None
    } else if d.len() == 0 || is_dot(d) {
        Some(st)
    } else if is_dotdot(d) {
        if st.len() == 0 { None } else { Some(st.drop_last()) }
    } else {
        Some(st.push(d))
    }
}

/// Where the segment starting at `i` ends: the next `/`, or the end.
pub open spec fn seg_end(p: Seq<u8>, i: int) -> int
    decreases p.len() - i,
{
    if i >= p.len() || p[i] == 0x2f { i } else { seg_end(p, i + 1) }
}

/// The segments from `i` (just after a `/`), applied to `st`.
pub open spec fn resolve_from(p: Seq<u8>, i: int, st: Seq<Seq<u8>>) -> Option<Seq<Seq<u8>>>
    decreases p.len() - i, 1int,
{
    if i < 0 || i > p.len() {
        None
    } else {
        let e = seg_end(p, i);
        if e < i || e > p.len() {
            None
        } else {
            match step(st, decode(p.subrange(i, e))) {
                None => None,
                Some(s) => if e >= p.len() { Some(s) } else { resolve_from(p, e + 1, s) },
            }
        }
    }
}

/// The components of the file a request path names, or None (a 404).
pub open spec fn resolve(p: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    if p.len() > 0 && p[0] == 0x2f { resolve_from(p, 1, Seq::empty()) } else { None }
}

/// The components joined by `/`.
pub open spec fn join(st: Seq<Seq<u8>>) -> Seq<u8>
    decreases st.len(),
{
    if st.len() == 0 {
        Seq::empty()
    } else if st.len() == 1 {
        st[0]
    } else {
        join(st.drop_last()) + seq![0x2fu8] + st.last()
    }
}

proof fn lemma_seg_end(p: Seq<u8>, i: int)
    requires 0 <= i <= p.len(),
    ensures
        i <= seg_end(p, i) <= p.len(),
        seg_end(p, i) < p.len() ==> p[seg_end(p, i)] == 0x2f,
        forall|j: int| i <= j < seg_end(p, i) ==> p[j] != 0x2f,
    decreases p.len() - i,
{
    if i < p.len() && p[i] != 0x2f {
        lemma_seg_end(p, i + 1);
    }
}

proof fn lemma_step_safe(st: Seq<Seq<u8>>, d: Seq<u8>)
    requires all_ok(st),
    ensures step(st, d) matches Some(s) ==> all_ok(s),
{
    if let Some(s) = step(st, d) {
        assert forall|k: int| 0 <= k < s.len() implies comp_ok(#[trigger] s[k]) by {
            if k < st.len() as int && s.len() >= st.len() {
                assert(s[k] == st[k]);
            } else if s.len() < st.len() {
                assert(s[k] == st[k]);
            } else {
                assert(s[k] == d);
                assert(forall|j: int| 0 <= j < d.len() ==> !bad_byte(#[trigger] d[j]));
            }
        }
    }
}

proof fn lemma_from_safe(p: Seq<u8>, i: int, st: Seq<Seq<u8>>)
    requires all_ok(st),
    ensures resolve_from(p, i, st) matches Some(s) ==> all_ok(s),
    decreases p.len() - i,
{
    if 0 <= i <= p.len() {
        lemma_seg_end(p, i);
        let e = seg_end(p, i);
        let d = decode(p.subrange(i, e));
        lemma_step_safe(st, d);
        if let Some(s) = step(st, d) {
            if e < p.len() {
                lemma_from_safe(p, e + 1, s);
            }
        }
    }
}

/// The theorem: every component of a resolved path is safe.
pub proof fn lemma_resolve_safe(p: Seq<u8>)
    ensures resolve(p) matches Some(st) ==> all_ok(st),
{
    if p.len() > 0 && p[0] == 0x2f {
        lemma_from_safe(p, 1, Seq::empty());
    }
}

pub open spec fn views(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    v.map_values(|x: Vec<u8>| x@)
}

fn bad_in(d: &Vec<u8>) -> (r: bool)
    ensures r == exists|k: int| 0 <= k < d@.len() && bad_byte(#[trigger] d@[k]),
{
    let mut i: usize = 0;
    while i < d.len()
        invariant
            i <= d@.len(),
            forall|k: int| 0 <= k < i ==> !bad_byte(#[trigger] d@[k]),
        decreases d@.len() - i,
    {
        let b = d[i];
        if b == 0x2f || b == 0x5c || b == 0 {
            assert(bad_byte(d@[i as int]));
            return true;
        }
        i += 1;
    }
    false
}

/// The components of the file `p` names: exactly [`resolve`]; and
/// whether `p` names a directory (its last segment is empty, `.` or `..`),
/// whose index file is then served.
pub fn resolve_exec(p: &[u8]) -> (r: Option<(Vec<Vec<u8>>, bool)>)
    ensures
        r matches Some((v, _)) ==> resolve(p@) == Some(views(v@)),
        r is None ==> resolve(p@) is None,
{
    if p.len() == 0 || p[0] != 0x2f {
        return None;
    }
    let n = p.len();
    let mut st: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 1;
    proof {
        assert(views(st@) =~= Seq::<Seq<u8>>::empty());
    }
    loop
        invariant
            n == p@.len(),
            1 <= i <= n,
            resolve(p@) == resolve_from(p@, i as int, views(st@)),
        decreases n - i,
    {
        let ghost g = views(st@);
        proof {
            lemma_seg_end(p@, i as int);
        }
        let mut e = i;
        while e < n && p[e] != 0x2f
            invariant
                n == p@.len(),
                i <= e <= n,
                seg_end(p@, i as int) == seg_end(p@, e as int),
            decreases n - e,
        {
            e += 1;
        }
        assert(seg_end(p@, e as int) == e);
        let mut d: Vec<u8> = Vec::new();
        let seg = vstd::slice::slice_subrange(p, i, e);
        decode_to(seg, &mut d);
        assert(d@ =~= decode(p@.subrange(i as int, e as int)));
        if bad_in(&d) {
            return None;
        }
        let dl = d.len();
        let dir = dl == 0 || (dl == 1 && d[0] == 0x2e) || (dl == 2 && d[0] == 0x2e && d[1] == 0x2e);
        if dl == 0 || (dl == 1 && d[0] == 0x2e) {
            assert(step(g, d@) == Some(g));
        } else if dl == 2 && d[0] == 0x2e && d[1] == 0x2e {
            if st.len() == 0 {
                return None;
            }
            st.pop();
            assert(views(st@) =~= g.drop_last());
        } else {
            st.push(d);
            assert(views(st@) =~= g.push(d@));
        }
        if e >= n {
            return Some((st, dir));
        }
        i = e + 1;
    }
}

/// `st` joined by `/`, onto `out`.
pub fn join_to(st: &Vec<Vec<u8>>, out: &mut Vec<u8>)
    ensures final(out)@ == old(out)@ + join(views(st@)),
{
    let ghost o = out@;
    let mut k: usize = 0;
    while k < st.len()
        invariant
            k <= st@.len(),
            out@ == o + join(views(st@).subrange(0, k as int)),
        decreases st@.len() - k,
    {
        let ghost before = out@;
        let ghost s = views(st@);
        proof {
            assert(s.subrange(0, k as int + 1).drop_last() =~= s.subrange(0, k as int));
            assert(s.subrange(0, k as int + 1).last() == st@[k as int]@);
        }
        if k > 0 {
            out.push(0x2f);
        } else {
            assert(s.subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
        }
        out.extend_from_slice(st[k].as_slice());
        proof {
            let t = s.subrange(0, k as int + 1);
            if k == 0 {
                assert(join(t) == t[0]);
                assert(out@ =~= o + join(t));
            } else {
                assert(join(t) == join(t.drop_last()) + seq![0x2fu8] + t.last());
                assert(out@ =~= o + join(t));
            }
        }
        k += 1;
    }
    assert(views(st@).subrange(0, st@.len() as int) =~= views(st@));
}

} // verus!

/// Whether a component is hidden (starts with `.`), other than
/// `.well-known` (RFC 8615). Hidden files are not served.
pub fn hidden(c: &[u8]) -> bool {
    c.first() == Some(&b'.') && c != b".well-known"
}
