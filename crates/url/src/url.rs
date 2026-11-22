//! The `Url` type: the serialized URL (href) plus component offsets, tied
//! by its well-formedness predicate to a ghost `UrlRecord`.
use crate::host::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Path segments of a list path never contain "/".
pub open spec fn segments_ok(segs: Seq<Seq<u8>>) -> bool {
    forall|i: int, j: int| 0 <= i < segs.len() && 0 <= j < segs[i].len() ==> #[trigger] segs[i][j] != b'/'
}

pub open spec fn path_ok(path: UrlPath) -> bool {
    match path {
        UrlPath::List(segs) => segments_ok(segs),
        UrlPath::Opaque(_) => true,
    }
}

// Offsets of the components in the serialization without the "/." prefix
// (`core_serialize`); `Url` adds 2 to the path, query and fragment offsets
// when the prefix is present.

/// The serialization without the "/." the serializer inserts before some
/// paths.
pub open spec fn core_serialize(url: UrlRecord) -> Seq<u8> {
    url.scheme + seq![b':'] + authority_serialize(url) + path_serialize(url.path) + query_serialize(
        url,
    ) + fragment_serialize(url)
}

pub open spec fn o_username_end(url: UrlRecord) -> nat {
    match url.host {
        Some(_) => url.scheme.len() + 3 + url.username.len(),
        None => url.scheme.len() + 1,
    }
}

pub open spec fn o_host_start(url: UrlRecord) -> nat {
    match url.host {
        Some(_) => url.scheme.len() + 3 + credentials_serialize(url).len(),
        None => url.scheme.len() + 1,
    }
}

pub open spec fn o_host_end(url: UrlRecord) -> nat {
    match url.host {
        Some(h) => o_host_start(url) + host_serialize(h).len(),
        None => url.scheme.len() + 1,
    }
}

pub open spec fn o_path_start(url: UrlRecord) -> nat {
    url.scheme.len() + 1 + authority_serialize(url).len()
}

pub open spec fn o_query_start(url: UrlRecord) -> nat {
    o_path_start(url) + path_serialize(url.path).len()
}

pub open spec fn o_fragment_start(url: UrlRecord) -> nat {
    o_query_start(url) + query_serialize(url).len()
}

pub open spec fn dot_len(url: UrlRecord) -> nat {
    if needs_dot_slash(url) {
        2
    } else {
        0
    }
}

pub open spec fn host_kind_of(url: UrlRecord) -> Option<HostKind> {
    match url.host {
        Some(h) => Some(kind_of(h)),
        None => None,
    }
}

/// A parsed URL.
#[derive(Clone)]
pub struct Url {
    pub(crate) href: Vec<u8>,
    /// Index of the ":" after the scheme.
    pub(crate) scheme_end: usize,
    pub(crate) username_end: usize,
    pub(crate) host_start: usize,
    pub(crate) host_end: usize,
    pub(crate) port: Option<u16>,
    /// Start of the path (after the "/." prefix, if any).
    pub(crate) path_start: usize,
    /// Index of "?", if the query is non-null.
    pub(crate) query_start: Option<usize>,
    /// Index of "#", if the fragment is non-null.
    pub(crate) fragment_start: Option<usize>,
    pub(crate) host_kind: Option<HostKind>,
    pub(crate) opaque_path: bool,
    pub(crate) special: bool,
    /// The serializer inserted "/." before the path.
    pub(crate) has_dot: bool,
    pub(crate) rec: Ghost<UrlRecord>,
}

impl Url {
    pub(crate) open spec fn view(&self) -> UrlRecord {
        self.rec@
    }

    /// Well-formed, with every component ASCII; every `Url` the parser
    /// returns is `ok`, so its href is ASCII (`lemma_ok_href_ascii`).
    pub(crate) open spec fn ok(&self) -> bool {
        self.wf() && crate::ascii::url_ascii(self.rec@) && crate::creds::creds_ok(self.rec@)
    }

    pub(crate) open spec fn wf(&self) -> bool {
        let url = self.rec@;
        let d = dot_len(url);
        &&& self.href@ == serialize(url, false)
        &&& path_ok(url.path)
        &&& self.scheme_end == url.scheme.len()
        &&& self.username_end == o_username_end(url)
        &&& self.host_start == o_host_start(url)
        &&& self.host_end == o_host_end(url)
        &&& self.port == url.port
        &&& self.path_start == o_path_start(url) + d
        &&& self.query_start == (if url.query is Some {
            Some((o_query_start(url) + d) as usize)
        } else {
            None
        })
        &&& self.fragment_start == (if url.fragment is Some {
            Some((o_fragment_start(url) + d) as usize)
        } else {
            None
        })
        &&& self.host_kind == host_kind_of(url)
        &&& self.opaque_path == (url.path is Opaque)
        &&& self.special == is_special(url)
        &&& self.has_dot == needs_dot_slash(url)
        &&& (is_special(url) ==> url.path is List)
        &&& self.href@.len() <= usize::MAX
    }
}

/// Where the path ends (the query or fragment start, or the end).
pub open spec fn o_path_end(url: UrlRecord) -> nat {
    o_query_start(url)
}

/// The pieces of a serialized URL, by offset.
pub proof fn lemma_serialize_parts(url: UrlRecord)
    ensures
        ({
            let h = serialize(url, false);
            let d = dot_len(url) as int;
            let sl = url.scheme.len() as int;
            let ps = o_path_start(url) + d;
            let qs = o_query_start(url) + d;
            let fs = o_fragment_start(url) + d;
            &&& h.len() == fs + fragment_serialize(url).len()
            &&& h.subrange(0, sl) == url.scheme
            &&& h[sl] == b':'
            &&& h.subrange(0, sl + 1) == url.scheme + seq![b':']
            &&& h.subrange(sl + 1, o_path_start(url) as int) == authority_serialize(url)
            &&& h.subrange(0, o_path_start(url) as int) == url.scheme + seq![b':'] + authority_serialize(url)
            &&& h.subrange(ps, qs) == path_serialize(url.path)
            &&& h.subrange(qs, fs) == query_serialize(url)
            &&& h.subrange(fs, h.len() as int) == fragment_serialize(url)
            &&& h.subrange(ps, fs) == path_serialize(url.path) + query_serialize(url)
        }),
{
    let h = serialize(url, false);
    let dot = if needs_dot_slash(url) {
        seq![b'/', b'.']
    } else {
        Seq::<u8>::empty()
    };
    let a = url.scheme + seq![b':'];
    let au = authority_serialize(url);
    let pa = path_serialize(url.path);
    let q = query_serialize(url);
    let f = fragment_serialize(url);
    assert(h =~= a + au + dot + pa + q + f);
    let sl = url.scheme.len() as int;
    let d = dot_len(url) as int;
    let ps = o_path_start(url) + d;
    let qs = o_query_start(url) + d;
    let fs = o_fragment_start(url) + d;
    assert(h.subrange(0, sl) =~= url.scheme);
    assert(h.subrange(0, sl + 1) =~= a);
    assert(h.subrange(sl + 1, o_path_start(url) as int) =~= au);
    assert(h.subrange(0, o_path_start(url) as int) =~= a + au);
    assert(h.subrange(ps, qs) =~= pa);
    assert(h.subrange(qs, fs) =~= q);
    assert(h.subrange(fs, h.len() as int) =~= f);
    assert(h.subrange(ps, fs) =~= pa + q);
}

/// The pieces of a core serialization, by offset.
pub proof fn lemma_core_parts(url: UrlRecord)
    ensures
        ({
            let h = core_serialize(url);
            let sl = url.scheme.len() as int;
            let ps = o_path_start(url) as int;
            let qs = o_query_start(url) as int;
            let fs = o_fragment_start(url) as int;
            &&& h.len() == fs + fragment_serialize(url).len()
            &&& h.subrange(0, sl) == url.scheme
            &&& h.subrange(0, ps) == url.scheme + seq![b':'] + authority_serialize(url)
            &&& h.subrange(ps, qs) == path_serialize(url.path)
            &&& h.subrange(qs, fs) == query_serialize(url)
            &&& h.subrange(0, qs) == url.scheme + seq![b':'] + authority_serialize(url) + path_serialize(url.path)
            &&& h.subrange(0, fs) == url.scheme + seq![b':'] + authority_serialize(url) + path_serialize(url.path) + query_serialize(url)
        }),
{
    let h = core_serialize(url);
    let a = url.scheme + seq![b':'];
    let au = authority_serialize(url);
    let pa = path_serialize(url.path);
    let q = query_serialize(url);
    let f = fragment_serialize(url);
    assert(h =~= a + au + pa + q + f);
    let sl = url.scheme.len() as int;
    assert(h.subrange(0, sl) =~= url.scheme);
    assert(h.subrange(0, o_path_start(url) as int) =~= a + au);
    assert(h.subrange(o_path_start(url) as int, o_query_start(url) as int) =~= pa);
    assert(h.subrange(o_query_start(url) as int, o_fragment_start(url) as int) =~= q);
    assert(h.subrange(0, o_query_start(url) as int) =~= a + au + pa);
    assert(h.subrange(0, o_fragment_start(url) as int) =~= a + au + pa + q);
}

// ---------------------------------------------------------------------------
// Path serializations
// ---------------------------------------------------------------------------

pub proof fn lemma_segments_len(segs: Seq<Seq<u8>>)
    ensures
        segments_serialize(segs).len() >= segs.len(),
        segs.len() > 0 ==> segments_serialize(segs).len() > 0 && segments_serialize(segs)[0] == b'/',
    decreases segs.len(),
{
    if segs.len() > 0 {
        lemma_segments_len(segs.drop_last());
        let a = segments_serialize(segs.drop_last());
        assert(segments_serialize(segs) =~= a + seq![b'/'] + segs.last());
        if segs.len() > 1 {
            assert(segments_serialize(segs)[0] == a[0]);
        }
    }
}

pub proof fn lemma_segments_push(segs: Seq<Seq<u8>>, seg: Seq<u8>)
    ensures
        segments_serialize(segs.push(seg)) == segments_serialize(segs) + seq![b'/'] + seg,
{
    assert(segs.push(seg).drop_last() =~= segs);
}

pub proof fn lemma_segments_ok_push(segs: Seq<Seq<u8>>, seg: Seq<u8>)
    requires
        segments_ok(segs),
        forall|j: int| 0 <= j < seg.len() ==> seg[j] != b'/',
    ensures
        segments_ok(segs.push(seg)),
{
    assert forall|i: int, j: int| 0 <= i < segs.push(seg).len() && 0 <= j < segs.push(seg)[i].len()
        implies #[trigger] segs.push(seg)[i][j] != b'/' by {
        if i < segs.len() {
            assert(segs.push(seg)[i] == segs[i]);
        }
    }
}

pub proof fn lemma_segments_ok_drop_last(segs: Seq<Seq<u8>>)
    requires
        segments_ok(segs),
        segs.len() > 0,
    ensures
        segments_ok(segs.drop_last()),
{
    assert forall|i: int, j: int| 0 <= i < segs.drop_last().len() && 0 <= j < segs.drop_last()[i].len()
        implies #[trigger] segs.drop_last()[i][j] != b'/' by {
        assert(segs.drop_last()[i] == segs[i]);
    }
}

/// The last "/" of a non-empty list path's serialization starts its last
/// segment.
pub proof fn lemma_segments_last_slash(segs: Seq<Seq<u8>>)
    requires
        segments_ok(segs),
        segs.len() > 0,
    ensures
        ({
            let s = segments_serialize(segs);
            let k = segments_serialize(segs.drop_last()).len() as int;
            &&& 0 <= k < s.len()
            &&& s[k] == b'/'
            &&& forall|j: int| k < j < s.len() ==> s[j] != b'/'
            &&& s.take(k) == segments_serialize(segs.drop_last())
        }),
{
    let a = segments_serialize(segs.drop_last());
    let last = segs.last();
    let s = segments_serialize(segs);
    assert(s =~= a + seq![b'/'] + last);
    assert forall|j: int| a.len() < j < s.len() implies s[j] != b'/' by {
        assert(s[j] == last[j - a.len() - 1]);
        assert(segs[segs.len() - 1] == last);
    }
    assert(s.take(a.len() as int) =~= a);
}

/// A list path is exactly one normalized Windows drive letter iff its
/// serialization is "/" followed by an ASCII alpha and ":".
pub proof fn lemma_segments_drive(segs: Seq<Seq<u8>>)
    requires
        segments_ok(segs),
    ensures
        (segs.len() == 1 && is_normalized_windows_drive_letter(segs[0])) <==> ({
            let s = segments_serialize(segs);
            s.len() == 3 && s[0] == b'/' && is_ascii_alpha(s[1]) && s[2] == b':'
        }),
{
    let s = segments_serialize(segs);
    lemma_segments_len(segs);
    if segs.len() == 1 {
        assert(segs.drop_last() =~= Seq::<Seq<u8>>::empty());
        assert(segments_serialize(Seq::<Seq<u8>>::empty()) =~= Seq::<u8>::empty());
        assert(s =~= seq![b'/'] + segs[0]);
    } else if segs.len() > 1 {
        let a = segments_serialize(segs.drop_last());
        lemma_segments_len(segs.drop_last());
        assert(s =~= a + seq![b'/'] + segs.last());
        // a starts with "/" and has length >= 1, then another "/": if s had
        // length 3, s[1] or s[2] would be "/".
        if s.len() == 3 {
            assert(s[a.len() as int] == b'/');
        }
    }
}

/// A list path's first segment is empty and there is a second iff its
/// serialization starts with "//".
pub proof fn lemma_segments_dot(segs: Seq<Seq<u8>>)
    requires
        segments_ok(segs),
    ensures
        (segs.len() > 1 && segs[0].len() == 0) <==> ({
            let s = segments_serialize(segs);
            s.len() >= 2 && s[0] == b'/' && s[1] == b'/'
        }),
    decreases segs.len(),
{
    let s = segments_serialize(segs);
    lemma_segments_len(segs);
    if segs.len() >= 2 {
        let a = segments_serialize(segs.drop_last());
        assert(s =~= a + seq![b'/'] + segs.last());
        lemma_segments_ok_drop_last(segs);
        lemma_segments_len(segs.drop_last());
        if segs.len() == 2 {
            assert(segs.drop_last().drop_last() =~= Seq::<Seq<u8>>::empty());
            assert(segments_serialize(Seq::<Seq<u8>>::empty()) =~= Seq::<u8>::empty());
            assert(segs.drop_last().last() == segs[0]);
            assert(a =~= seq![b'/'] + segs[0]);
            if segs[0].len() > 0 {
                assert(s[1] == segs[0][0]);
                assert(segs[0][0] != b'/');
            }
        } else {
            lemma_segments_dot(segs.drop_last());
            assert(segs.drop_last()[0] == segs[0]);
            assert(s[0] == a[0]);
            assert(s[1] == a[1]);
        }
    } else if segs.len() == 1 {
        assert(segs.drop_last() =~= Seq::<Seq<u8>>::empty());
        assert(segments_serialize(Seq::<Seq<u8>>::empty()) =~= Seq::<u8>::empty());
        assert(s =~= seq![b'/'] + segs[0]);
        if s.len() >= 2 {
            assert(s[1] == segs[0][0]);
        }
    }
}

/// An `ok` URL's href is ASCII.
pub(crate) proof fn lemma_ok_href_ascii(u: &Url)
    requires
        u.ok(),
    ensures
        is_ascii(u.href@),
{
    crate::ascii::lemma_serialize_ascii(u.rec@);
}

} // verus!
