//! Verified name compression (RFC 1035 §4.1.4).
//!
//! `Message::to_bytes_compressed` writes each name as its leading labels
//! followed by a pointer to an earlier occurrence of the rest, and is proven
//! to produce bytes that parse back to exactly the message. Compression
//! needs no ghost model of "the" compressed form: the proof only uses what
//! the parser reads.
//!
//! Earlier occurrences are kept in a dictionary of (output offset, name
//! suffix) entries. An entry is only ever made for an offset where a label
//! was written, and the invariant `dict_ok` says that parsing the output
//! there gives the suffix. Output is only ever appended to, and parsing
//! reads only bytes already written, so every entry stays valid.
use alloc::vec::Vec;
#[cfg(verus_only)]
use crate::lemmas::*;
#[cfg(verus_only)]
use crate::lemmas_rdata::*;
use crate::message::*;
use crate::parse::append;
use crate::spec::*;
#[allow(unused_imports)]
use crate::spec_rdata::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// Parsing reads only bytes already written
// ---------------------------------------------------------------------------

proof fn lemma_prefix_at(b: Seq<u8>, b2: Seq<u8>, i: int)
    requires
        is_prefix(b, b2),
        0 <= i < b.len(),
    ensures
        b2[i] == b[i],
{
    assert(b2.subrange(0, b.len() as int)[i] == b2[i]);
}

proof fn lemma_prefix_range(b: Seq<u8>, b2: Seq<u8>, i: int, j: int)
    requires
        is_prefix(b, b2),
        0 <= i <= j <= b.len(),
    ensures
        b2.subrange(i, j) == b.subrange(i, j),
{
    assert(b2.subrange(i, j) =~= b.subrange(i, j)) by {
        assert forall|k: int| 0 <= k < j - i implies b2.subrange(i, j)[k] == b.subrange(i, j)[k] by {
            lemma_prefix_at(b, b2, i + k);
        }
    }
}

pub proof fn lemma_labels_ext(b: Seq<u8>, b2: Seq<u8>, pos: int, seg: int)
    requires
        is_prefix(b, b2),
        parse_labels(b, pos, seg) is Some,
    ensures
        parse_labels(b2, pos, seg) == parse_labels(b, pos, seg),
    decreases seg, b.len() - pos,
{
    lemma_prefix_at(b, b2, pos);
    let c = b[pos];
    if c == 0 {
    } else if c >= 192 {
        lemma_prefix_at(b, b2, pos + 1);
        let target = (c as int - 192) * 256 + b[pos + 1] as int;
        lemma_prefix_at(b, b2, target);
        lemma_labels_ext(b, b2, target, target);
    } else {
        lemma_prefix_range(b, b2, pos + 1, pos + 1 + c as int);
        lemma_labels_ext(b, b2, pos + 1 + c as int, seg);
    }
}

pub proof fn lemma_name_ext(b: Seq<u8>, b2: Seq<u8>, pos: int)
    requires
        is_prefix(b, b2),
        parse_name(b, pos) is Some,
    ensures
        parse_name(b2, pos) == parse_name(b, pos),
{
    lemma_labels_ext(b, b2, pos, pos);
}

proof fn lemma_u16_ext(b: Seq<u8>, b2: Seq<u8>, pos: int)
    requires
        is_prefix(b, b2),
        parse_u16(b, pos) is Some,
    ensures
        parse_u16(b2, pos) == parse_u16(b, pos),
{
    lemma_prefix_at(b, b2, pos);
    lemma_prefix_at(b, b2, pos + 1);
}

proof fn lemma_u32_ext(b: Seq<u8>, b2: Seq<u8>, pos: int)
    requires
        is_prefix(b, b2),
        parse_u32(b, pos) is Some,
    ensures
        parse_u32(b2, pos) == parse_u32(b, pos),
{
    lemma_prefix_at(b, b2, pos);
    lemma_prefix_at(b, b2, pos + 1);
    lemma_prefix_at(b, b2, pos + 2);
    lemma_prefix_at(b, b2, pos + 3);
}

pub proof fn lemma_question_ext(b: Seq<u8>, b2: Seq<u8>, pos: int)
    requires
        is_prefix(b, b2),
        parse_question(b, pos) is Some,
    ensures
        parse_question(b2, pos) == parse_question(b, pos),
{
    lemma_name_ext(b, b2, pos);
    let p1 = parse_name(b, pos).unwrap().1;
    lemma_u16_ext(b, b2, p1);
    lemma_u16_ext(b, b2, p1 + 2);
}

pub proof fn lemma_record_ext(b: Seq<u8>, b2: Seq<u8>, pos: int)
    requires
        is_prefix(b, b2),
        parse_record(b, pos) is Some,
    ensures
        parse_record(b2, pos) == parse_record(b, pos),
{
    lemma_name_ext(b, b2, pos);
    let p1 = parse_name(b, pos).unwrap().1;
    lemma_u16_ext(b, b2, p1);
    lemma_u16_ext(b, b2, p1 + 2);
    lemma_u32_ext(b, b2, p1 + 4);
    lemma_u16_ext(b, b2, p1 + 8);
    let t = parse_u16(b, p1).unwrap().0;
    let (s, e) = (p1 + 10, p1 + 10 + parse_u16(b, p1 + 8).unwrap().0 as int);
    lemma_canon_names_ext(b, b2, t, s, e);
}

proof fn lemma_cstring_ext(b: Seq<u8>, b2: Seq<u8>, p: int, e: int)
    requires
        is_prefix(b, b2),
        parse_cstring(b, p, e) is Some,
    ensures
        parse_cstring(b2, p, e) == parse_cstring(b, p, e),
{
    lemma_prefix_at(b, b2, p);
    lemma_prefix_range(b, b2, p + 1, p + 1 + b[p] as int);
}

#[verifier::spinoff_prover]
proof fn lemma_canon_names_ext(b: Seq<u8>, b2: Seq<u8>, t: u16, s: int, e: int)
    requires
        is_prefix(b, b2),
        canon_names(b, t, s, e) is Some,
    ensures
        canon_names(b2, t, s, e) == canon_names(b, t, s, e),
{
    lemma_prefix_range(b, b2, s, e);
    if t == TYPE_NS || t == TYPE_CNAME || t == TYPE_PTR {
        lemma_name_ext(b, b2, s);
    } else if t == TYPE_MX || t == TYPE_SRV {
        let k: int = if t == TYPE_MX { 2 } else { 6 };
        lemma_name_ext(b, b2, s + k);
        lemma_prefix_range(b, b2, s, s + k);
    } else if t == TYPE_SOA {
        lemma_name_ext(b, b2, s);
        let p1 = parse_name(b, s).unwrap().1;
        lemma_name_ext(b, b2, p1);
        let p2 = parse_name(b, p1).unwrap().1;
        lemma_parse_name_valid(b, s);
        lemma_parse_name_valid(b, p1);
        lemma_prefix_range(b, b2, p2, e);
    } else if t == TYPE_SIG {
        lemma_name_ext(b, b2, s + 18);
        let p = parse_name(b, s + 18).unwrap().1;
        lemma_parse_name_valid(b, s + 18);
        lemma_prefix_range(b, b2, s, s + 18);
        lemma_prefix_range(b, b2, p, e);
    } else if t == TYPE_NAPTR {
        lemma_cstring_ext(b, b2, s + 4, e);
        let p1 = parse_cstring(b, s + 4, e).unwrap().1;
        lemma_cstring_ext(b, b2, p1, e);
        let p2 = parse_cstring(b, p1, e).unwrap().1;
        lemma_cstring_ext(b, b2, p2, e);
        let p3 = parse_cstring(b, p2, e).unwrap().1;
        lemma_name_ext(b, b2, p3);
        lemma_prefix_range(b, b2, s, p3);
    }
}

// ---------------------------------------------------------------------------
// Names and their suffixes
// ---------------------------------------------------------------------------

/// The wire form of a name splits after any number of labels.
pub proof fn lemma_name_split(n: SpecName, k: int)
    requires
        0 <= k <= n.len(),
    ensures
        ser_name(n) == ser_labels(n.take(k)) + ser_name(n.skip(k)),
        k < n.len() ==> ser_name(n)[ser_labels(n.take(k)).len() as int] == n[k].len() as u8,
        k < n.len() ==> ser_labels(n.take(k + 1)).len() == ser_labels(n.take(k)).len() + 1
            + n[k].len(),
{
    assert(n =~= n.take(k) + n.skip(k));
    lemma_ser_labels_append(n.take(k), n.skip(k));
    if k < n.len() {
        let rest = n.skip(k);
        assert(rest[0] == n[k]);
        assert(ser_name(rest)[0] == n[k].len() as u8);
        assert(n.take(k + 1) =~= n.take(k).push(n[k]));
        lemma_ser_labels_push(n.take(k), n[k]);
    }
}

/// Suffixes of a well-formed name are well-formed.
pub proof fn lemma_skip_valid(n: SpecName, k: int)
    requires
        valid_name(n),
        0 <= k <= n.len(),
    ensures
        valid_name(n.skip(k)),
{
    lemma_name_split(n, k);
    assert forall|i: int| 0 <= i < n.skip(k).len() implies valid_label(#[trigger] n.skip(k)[i]) by {
        assert(n.skip(k)[i] == n[k + i]);
    }
}

/// A name's wire form determines it.
pub proof fn lemma_ser_name_injective(a: SpecName, b: SpecName)
    requires
        valid_name(a),
        valid_name(b),
        ser_name(a) == ser_name(b),
    ensures
        a == b,
{
    let w = ser_name(a);
    lemma_at_whole(w);
    lemma_name_roundtrip(w, 0, a);
    lemma_name_roundtrip(w, 0, b);
}

/// A non-empty name is at least 3 octets: a length, a label octet, the root.
proof fn lemma_name_len_nonempty(n: SpecName)
    requires
        valid_name(n),
        n.len() > 0,
    ensures
        ser_name(n).len() >= 3,
{
    lemma_name_split(n, 1);
    assert(valid_label(n[0]));
    assert(n.take(1) =~= Seq::<Seq<u8>>::empty().push(n[0]));
    lemma_ser_labels_push(Seq::<Seq<u8>>::empty(), n[0]);
}

/// Literal labels followed by whatever ends the run parse as those labels
/// followed by what the end gives. `seg` does not change along a run.
pub proof fn lemma_literal_run(b: Seq<u8>, pos: int, seg: int, m: SpecName, rest: SpecName, e: int)
    requires
        0 <= seg <= pos,
        at(b, pos, ser_labels(m)),
        forall|i: int| 0 <= i < m.len() ==> valid_label(#[trigger] m[i]),
        parse_labels(b, pos + ser_labels(m).len(), seg) == Some((rest, e)),
    ensures
        parse_labels(b, pos, seg) == Some((m + rest, e)),
    decreases m.len(),
{
    if m.len() == 0 {
        assert(m + rest =~= rest);
    } else {
        let l = m[0];
        let tail = m.drop_first();
        assert(valid_label(l));
        assert(ser_labels(m) == seq![l.len() as u8] + (l + ser_labels(tail)));
        lemma_at_split(b, pos, seq![l.len() as u8], l + ser_labels(tail));
        lemma_at_split(b, pos + 1, l, ser_labels(tail));
        assert(b[pos] == b.subrange(pos, pos + 1)[0]);
        assert forall|i: int| 0 <= i < tail.len() implies valid_label(#[trigger] tail[i]) by {
            assert(tail[i] == m[i + 1]);
        }
        lemma_literal_run(b, pos + 1 + l.len(), seg, tail, rest, e);
        assert(seq![l] + (tail + rest) =~= m + rest);
    }
}

/// The two octets of a compression pointer to `off`.
pub open spec fn ptr_bytes(off: int) -> Seq<u8> {
    seq![(192 + off / 256) as u8, (off % 256) as u8]
}

/// A pointer to `off`, a label length octet before `seg` from which the
/// labels `l` parse, gives `l`.
pub proof fn lemma_ptr_end(b: Seq<u8>, q: int, seg: int, off: int, l: SpecName)
    requires
        0 <= off < seg <= q,
        off <= 0x3FFF,
        at(b, q, ptr_bytes(off)),
        b[off] < 64,
        parse_labels(b, off, off) matches Some((x, _)) && x == l,
    ensures
        parse_labels(b, q, seg) == Some((l, q + 2)),
{
    assert(b[q] == ptr_bytes(off)[0]);
    assert(b[q + 1] == ptr_bytes(off)[1]);
    assert((b[q] as int - 192) * 256 + b[q + 1] as int == off);
}

pub proof fn lemma_root_end(b: Seq<u8>, q: int, seg: int)
    requires
        0 <= seg <= q,
        at(b, q, seq![0u8]),
    ensures
        parse_labels(b, q, seg) == Some((Seq::<Seq<u8>>::empty(), q + 1)),
{
    assert(b[q] == seq![0u8][0]);
}

// ---------------------------------------------------------------------------
// The dictionary
// ---------------------------------------------------------------------------

/// An earlier occurrence of a name suffix: the output offset of its first
/// label, and its uncompressed wire form in the message's arena.
#[derive(Clone, Copy)]
pub struct DictEntry {
    pub off: usize,
    pub name: Span,
    /// The previous entry in the same bucket, plus one (0 if none). Only a
    /// search hint: nothing is assumed about it.
    pub prev: usize,
}

/// Buckets in the dictionary's index.
pub const BUCKETS: usize = 64;

/// The dictionary: its entries, and an index from a key of a suffix's
/// bytes to the newest entry with that key, plus one. The index is only a
/// search hint, so the proofs never depend on it: an entry it misses is
/// just not used as a pointer target.
pub struct Dict {
    pub e: Vec<DictEntry>,
    pub head: [u32; BUCKETS],
}

impl View for Dict {
    type V = Seq<DictEntry>;

    open spec fn view(&self) -> Seq<DictEntry> {
        self.e@
    }
}

impl Dict {
    pub fn new() -> (d: Dict)
        ensures
            d@ == Seq::<DictEntry>::empty(),
    {
        Dict { e: Vec::with_capacity(16), head: [0u32; BUCKETS] }
    }

    /// The newest entry with key `k`, plus one, or 0.
    #[inline(always)]
    fn bucket(&self, k: usize) -> usize {
        if k < BUCKETS {
            self.head[k] as usize
        } else {
            0
        }
    }

    #[inline(always)]
    fn push(&mut self, e: DictEntry, k: usize)
        ensures
            final(self)@ == old(self)@.push(e),
    {
        self.e.push(e);
        let n = self.e.len();
        if k < BUCKETS && n <= u32::MAX as usize {
            self.head.set(k, n as u32);
        }
    }
}

/// The index key of a name suffix in wire form.
#[inline(always)]
fn key(s: &[u8]) -> (k: usize)
    ensures
        k < BUCKETS,
{
    if s.len() < 3 {
        return 0;
    }
    let (a, b) = (s[1] as usize, s[2] as usize);
    (s.len() % 256 + 3 * a + 5 * b) % BUCKETS
}

pub open spec fn entry_ok(out: Seq<u8>, arena: Seq<u8>, e: DictEntry, n: SpecName) -> bool {
    &&& e.off < out.len()
    &&& e.off <= 0x3FFF
    &&& out[e.off as int] < 64
    &&& parse_labels(out, e.off as int, e.off as int) matches Some((l, _)) && l == n
    &&& span_ok(arena, e.name, ser_name(n))
    &&& valid_name(n)
}

pub open spec fn dict_ok(out: Seq<u8>, arena: Seq<u8>, d: Seq<DictEntry>, g: Seq<SpecName>) -> bool {
    &&& d.len() == g.len()
    &&& forall|j: int| 0 <= j < d.len() ==> entry_ok(out, arena, #[trigger] d[j], g[j])
}

pub proof fn lemma_dict_ext(out: Seq<u8>, out2: Seq<u8>, arena: Seq<u8>, d: Seq<DictEntry>, g: Seq<SpecName>)
    requires
        is_prefix(out, out2),
        dict_ok(out, arena, d, g),
    ensures
        dict_ok(out2, arena, d, g),
{
    assert forall|j: int| 0 <= j < d.len() implies entry_ok(out2, arena, #[trigger] d[j], g[j]) by {
        assert(entry_ok(out, arena, d[j], g[j]));
        lemma_prefix_at(out, out2, d[j].off as int);
        lemma_labels_ext(out, out2, d[j].off as int, d[j].off as int);
    }
}

/// How to write a name: its first `k` labels (`cut` octets) literally, then
/// a pointer to dictionary entry `ptr`, or the root octet if there is none.
pub struct Plan {
    pub cut: usize,
    pub ptr: Option<usize>,
    pub k: Ghost<int>,
}

pub open spec fn plan_ok(d: Seq<DictEntry>, g: Seq<SpecName>, n: SpecName, p: Plan) -> bool {
    &&& 0 <= p.k@ <= n.len()
    &&& p.cut == ser_labels(n.take(p.k@)).len()
    &&& match p.ptr {
        Some(j) => j < d.len() && j < g.len() && g[j as int] == n.skip(p.k@) && p.k@ < n.len(),
        None => p.k@ == n.len(),
    }
}

pub open spec fn plan_len(p: Plan) -> int {
    match p.ptr {
        Some(_) => p.cut + 2,
        None => p.cut + 1,
    }
}

proof fn lemma_plan_len(d: Seq<DictEntry>, g: Seq<SpecName>, n: SpecName, p: Plan)
    requires
        plan_ok(d, g, n, p),
        valid_name(n),
    ensures
        plan_len(p) <= ser_name(n).len(),
{
    lemma_name_split(n, p.k@);
    if p.ptr is Some {
        lemma_skip_valid(n, p.k@);
        lemma_name_len_nonempty(n.skip(p.k@));
    }
}

/// Plans stay valid as the dictionary grows.
proof fn lemma_plan_grow(d: Seq<DictEntry>, g: Seq<SpecName>, d2: Seq<DictEntry>, g2: Seq<SpecName>, n: SpecName, p: Plan)
    requires
        plan_ok(d, g, n, p),
        is_prefix(d, d2),
        is_prefix(g, g2),
    ensures
        plan_ok(d2, g2, n, p),
{
    if let Some(j) = p.ptr {
        assert(g2.subrange(0, g.len() as int)[j as int] == g2[j as int]);
    }
}

/// The bytes of `n` written per plan `p` at `p0` in `b`.
pub open spec fn emitted(b: Seq<u8>, p0: int, d: Seq<DictEntry>, n: SpecName, p: Plan) -> bool {
    &&& at(b, p0, ser_labels(n.take(p.k@)))
    &&& match p.ptr {
        Some(j) => at(b, p0 + p.cut, ptr_bytes(d[j as int].off as int)),
        None => at(b, p0 + p.cut, seq![0u8]),
    }
}

/// From the start of any of its literal labels, an emitted name parses as
/// the rest of the name.
proof fn lemma_emitted(
    b: Seq<u8>,
    arena: Seq<u8>,
    p0: int,
    d: Seq<DictEntry>,
    g: Seq<SpecName>,
    n: SpecName,
    p: Plan,
    i: int,
)
    requires
        emitted(b, p0, d, n, p),
        dict_ok(b, arena, d, g),
        plan_ok(d, g, n, p),
        valid_name(n),
        0 <= i <= p.k@,
        0 <= p0,
        p.ptr matches Some(j) ==> d[j as int].off < p0,
    ensures
        ({
            let ci = p0 + ser_labels(n.take(i)).len();
            parse_labels(b, ci, ci) == Some((n.skip(i), p0 + plan_len(p)))
        }),
{
    let k = p.k@;
    let ci = p0 + ser_labels(n.take(i)).len();
    let m = n.subrange(i, k);
    assert(n.take(k) =~= n.take(i) + m);
    lemma_ser_labels_append(n.take(i), m);
    lemma_at_split(b, p0, ser_labels(n.take(i)), ser_labels(m));
    let q = p0 + p.cut;
    assert(q == ci + ser_labels(m).len());
    assert(ser_labels(n.take(i)).len() >= 0);
    match p.ptr {
        Some(j) => {
            assert(entry_ok(b, arena, d[j as int], g[j as int]));
            lemma_ptr_end(b, q, ci, d[j as int].off as int, n.skip(k));
        },
        None => {
            lemma_root_end(b, q, ci);
            assert(n.skip(k) =~= Seq::<Seq<u8>>::empty());
        },
    }
    assert forall|x: int| 0 <= x < m.len() implies valid_label(#[trigger] m[x]) by {
        assert(m[x] == n[i + x]);
    }
    lemma_literal_run(b, ci, ci, m, n.skip(k), p0 + plan_len(p));
    assert(m + n.skip(k) =~= n.skip(i));
}

fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
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
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// Chooses how to write the name `n` (uncompressed in `arena[sp]`): the
/// longest suffix that is already in the dictionary becomes a pointer.
pub fn plan_name(
    dict: &Dict,
    g: Ghost<Seq<SpecName>>,
    out: Ghost<Seq<u8>>,
    arena: &[u8],
    sp: Span,
    n: Ghost<SpecName>,
) -> (p: Plan)
    requires
        dict_ok(out@, arena@, dict@, g@),
        span_ok(arena@, sp, ser_name(n@)),
        valid_name(n@),
    ensures
        plan_ok(dict@, g@, n@, p),
{
    let _ = arena.len();
    let mut c: usize = 0;
    let ghost mut i: int = 0;
    loop
        invariant
            arena@.len() <= usize::MAX,
            dict_ok(out@, arena@, dict@, g@),
            span_ok(arena@, sp, ser_name(n@)),
            valid_name(n@),
            0 <= i <= n@.len(),
            c == ser_labels(n@.take(i)).len(),
        decreases n@.len() - i,
    {
        proof {
            lemma_name_split(n@, i);
            assert(ser_name(n@.skip(i)).len() >= 1);
            assert(c < sp.len);
            assert(span_bytes(arena@, sp)[c as int] == arena@[sp.start + c]);
            assert(arena@[sp.start + c] == ser_name(n@)[c as int]);
            if i == n@.len() {
                assert(n@.skip(i) =~= Seq::<Seq<u8>>::empty());
            } else {
                assert(valid_label(n@[i]));
            }
        }
        let len = arena[sp.start + c];
        if len == 0 {
            proof {
                if i < n@.len() {
                    assert(ser_name(n@)[c as int] == n@[i].len() as u8);
                }
                assert(i == n@.len());
            }
            return Plan { cut: c, ptr: None, k: Ghost(i) };
        }
        let s0 = sp.start + c;
        let suffix = slice_subrange(arena, s0, sp.start + sp.len);
        proof {
            if i == n@.len() {
                assert(n@.skip(i) =~= Seq::<Seq<u8>>::empty());
                assert(ser_name(n@.skip(i))[0] == 0);
            }
            assert(i < n@.len());
            assert(len == n@[i].len());
            assert(suffix@ =~= ser_name(n@.skip(i))) by {
                assert forall|x: int| 0 <= x < suffix@.len() implies suffix@[x] == ser_name(n@.skip(i))[x] by {
                    assert(suffix@[x] == arena@[sp.start + c + x]);
                    assert(span_bytes(arena@, sp)[c + x] == arena@[sp.start + c + x]);
                    assert(arena@[sp.start + c + x] == ser_name(n@)[c + x]);
                }
            }
            lemma_skip_valid(n@, i);
        }
        let mut j1 = dict.bucket(key(suffix));
        while j1 != 0
            invariant
                arena@.len() <= usize::MAX,
                dict_ok(out@, arena@, dict@, g@),
                suffix@ == ser_name(n@.skip(i)),
                valid_name(n@.skip(i)),
                0 <= i < n@.len(),
                c == ser_labels(n@.take(i)).len(),
                suffix@ == arena@.subrange(s0 as int, sp.start + sp.len),
                s0 + suffix@.len() == sp.start + sp.len,
            decreases j1,
        {
            let j = j1 - 1;
            if j >= dict.e.len() {
                break;
            }
            let de = dict.e[j];
            if de.name.len == suffix.len() {
                proof {
                    assert(entry_ok(out@, arena@, dict@[j as int], g@[j as int]));
                }
                // The same bytes of the arena need no comparing.
                let w = slice_subrange(arena, de.name.start, de.name.start + de.name.len);
                if de.name.start == s0 || bytes_eq(w, suffix) {
                    proof {
                        if de.name.start == s0 {
                            assert(w@ == arena@.subrange(s0 as int, s0 + de.name.len));
                            assert(suffix@ == arena@.subrange(s0 as int, sp.start + sp.len));
                            assert(w@ =~= suffix@);
                        }
                        assert(w@ == span_bytes(arena@, de.name));
                        lemma_ser_name_injective(g@[j as int], n@.skip(i));
                    }
                    return Plan { cut: c, ptr: Some(j), k: Ghost(i) };
                }
            }
            if de.prev >= j1 {
                break;
            }
            j1 = de.prev;
        }
        c = c + 1 + len as usize;
        proof {
            i = i + 1;
        }
    }
}

/// Writes the name `n` per plan `p` and records its literal labels in the
/// dictionary.
#[verifier::spinoff_prover]
pub fn emit_name(
    out: &mut Vec<u8>,
    dict: &mut Dict,
    g: Ghost<Seq<SpecName>>,
    arena: &[u8],
    sp: Span,
    n: Ghost<SpecName>,
    p: &Plan,
) -> (g2: Ghost<Seq<SpecName>>)
    requires
        dict_ok(old(out)@, arena@, old(dict)@, g@),
        span_ok(arena@, sp, ser_name(n@)),
        valid_name(n@),
        plan_ok(old(dict)@, g@, n@, *p),
    ensures
        parse_name(final(out)@, old(out)@.len() as int) == Some((n@, final(out)@.len() as int)),
        final(out)@.len() == old(out)@.len() + plan_len(*p),
        is_prefix(old(out)@, final(out)@),
        is_prefix(old(dict)@, final(dict)@),
        is_prefix(g@, g2@),
        dict_ok(final(out)@, arena@, final(dict)@, g2@),
{
    let ghost o0 = out@;
    let ghost d0 = dict@;
    let p0 = out.len();
    let _ = arena.len();
    proof {
        lemma_name_split(n@, p.k@);
        lemma_plan_len(d0, g@, n@, *p);
        assert(p.cut <= sp.len);
        assert(sp.len <= 255);
    }
    let lit = slice_subrange(arena, sp.start, sp.start + p.cut);
    proof {
        assert(lit@ =~= ser_labels(n@.take(p.k@))) by {
            assert forall|x: int| 0 <= x < lit@.len() implies lit@[x] == ser_labels(n@.take(p.k@))[x] by {
                assert(span_bytes(arena@, sp)[x] == arena@[sp.start + x]);
                assert(arena@[sp.start + x] == ser_name(n@)[x]);
            }
        }
    }
    append(out, lit);
    let ghost o1 = out@;
    match p.ptr {
        Some(j) => {
            proof {
                assert(entry_ok(o0, arena@, d0[j as int], g@[j as int]));
            }
            let off = dict.e[j].off;
            out.push((192 + off / 256) as u8);
            out.push((off % 256) as u8);
            proof {
                assert(out@ =~= o1 + ptr_bytes(off as int));
            }
        },
        None => {
            out.push(0);
            proof {
                assert(out@ =~= o1 + seq![0u8]);
            }
        },
    }
    let ghost b = out@;
    proof {
        lemma_prefix_append(o0, b.subrange(o0.len() as int, b.len() as int));
        assert(o0 + b.subrange(o0.len() as int, b.len() as int) =~= b);
        lemma_dict_ext(o0, b, arena@, d0, g@);
        assert(at(b, p0 as int, ser_labels(n@.take(p.k@)))) by {
            assert(b.subrange(p0 as int, p0 + p.cut) =~= lit@);
        }
        match p.ptr {
            Some(j) => {
                assert(b.subrange(p0 + p.cut, p0 + p.cut + 2) =~= ptr_bytes(d0[j as int].off as int));
            },
            None => {
                assert(b.subrange(p0 + p.cut, p0 + p.cut + 1) =~= seq![0u8]);
            },
        }
        assert(emitted(b, p0 as int, d0, n@, *p));
        lemma_emitted(b, arena@, p0 as int, d0, g@, n@, *p, 0);
        assert(n@.take(0) =~= Seq::<Seq<u8>>::empty());
        assert(n@.skip(0) =~= n@);
    }
    // Every literal label starts a suffix later names can point to.
    let ghost mut g2 = g@;
    let mut c: usize = 0;
    let ghost mut i: int = 0;
    proof {
        lemma_prefix_refl(d0);
        lemma_prefix_refl(g@);
    }
    while c < p.cut
        invariant
            arena@.len() <= usize::MAX,
            out@ == b,
            emitted(b, p0 as int, d0, n@, *p),
            dict_ok(b, arena@, d0, g@),
            dict_ok(b, arena@, dict@, g2),
            is_prefix(d0, dict@),
            is_prefix(g@, g2),
            plan_ok(d0, g@, n@, *p),
            valid_name(n@),
            span_ok(arena@, sp, ser_name(n@)),
            p0 == o0.len(),
            p.ptr matches Some(j) ==> d0[j as int].off < p0,
            0 <= i <= p.k@,
            c == ser_labels(n@.take(i)).len(),
            p.cut == ser_labels(n@.take(p.k@)).len(),
            p.cut <= sp.len,
            sp.len <= 255,
        decreases p.k@ - i,
    {
        proof {
            if i == p.k@ {
                assert(false);
            }
            lemma_name_split(n@, i);
            lemma_name_split(n@, p.k@);
            assert(arena@[sp.start + c] == ser_name(n@)[c as int]);
            assert(n@.take(p.k@).len() == p.k@);
            if i + 1 <= p.k@ {
                assert(n@.take(i + 1).len() <= n@.take(p.k@).len());
            }
            lemma_ser_take_mono(n@, i + 1, p.k@);
            assert(sp.len <= 255);
            assert(c < sp.len);
            assert(span_bytes(arena@, sp)[c as int] == arena@[sp.start + c]);
        }
        let len = arena[sp.start + c];
        // Pointers reach only the first 16 KiB.
        if p0 <= 0x3FFF && c <= 0x3FFF - p0 {
            let o = p0 + c;
            let k = key(slice_subrange(arena, sp.start + c, sp.start + sp.len));
            let e = DictEntry { off: o, name: Span { start: sp.start + c, len: sp.len - c }, prev: dict.bucket(k) };
            let ghost dprev = dict@;
            dict.push(e, k);
            proof {
                lemma_emitted(b, arena@, p0 as int, d0, g@, n@, *p, i);
                lemma_skip_valid(n@, i);
                assert(b[o as int] == ser_labels(n@.take(p.k@))[c as int]) by {
                    assert(b.subrange(p0 as int, p0 + p.cut)[c as int] == b[o as int]);
                }
                lemma_name_split(n@.take(p.k@), i);
                assert(n@.take(p.k@).take(i) =~= n@.take(i));
                assert(n@.take(p.k@)[i] == n@[i]);
                assert(valid_label(n@[i]));
                assert(span_bytes(arena@, e.name) =~= ser_name(n@.skip(i))) by {
                    assert forall|x: int| 0 <= x < e.name.len implies span_bytes(arena@, e.name)[x]
                        == ser_name(n@.skip(i))[x] by {
                        assert(span_bytes(arena@, sp)[c + x] == arena@[sp.start + c + x]);
                        assert(arena@[sp.start + c + x] == ser_name(n@)[c + x]);
                    }
                }
                assert(entry_ok(b, arena@, e, n@.skip(i)));
                let g3 = g2.push(n@.skip(i));
                assert forall|j: int| 0 <= j < dict@.len() implies entry_ok(b, arena@, #[trigger] dict@[j], g3[j]) by {
                    if j < dprev.len() {
                        assert(dict@[j] == dprev[j]);
                        assert(entry_ok(b, arena@, dprev[j], g2[j]));
                    }
                }
                lemma_prefix_push(dprev, e);
                lemma_prefix_trans(d0, dprev, dict@);
                lemma_prefix_push(g2, n@.skip(i));
                lemma_prefix_trans(g@, g2, g3);
                g2 = g3;
            }
        }
        c = c + 1 + len as usize;
        proof {
            i = i + 1;
        }
    }
    Ghost(g2)
}

/// Taking more labels never shortens the wire form.
proof fn lemma_ser_take_mono(n: SpecName, i: int, k: int)
    requires
        0 <= i <= k <= n.len(),
    ensures
        ser_labels(n.take(i)).len() <= ser_labels(n.take(k)).len(),
{
    assert(n.take(k) =~= n.take(i) + n.subrange(i, k));
    lemma_ser_labels_append(n.take(i), n.subrange(i, k));
}

// ---------------------------------------------------------------------------
// Questions and records
// ---------------------------------------------------------------------------

proof fn lemma_at_ext(b: Seq<u8>, b2: Seq<u8>, pos: int, x: Seq<u8>)
    requires
        is_prefix(b, b2),
        at(b, pos, x),
    ensures
        at(b2, pos, x),
{
    lemma_prefix_range(b, b2, pos, pos + x.len());
}

/// Appends `x`; `at` facts about `out` carry over.
fn put(out: &mut Vec<u8>, x: &[u8])
    ensures
        final(out)@ == old(out)@ + x@,
        is_prefix(old(out)@, final(out)@),
        at(final(out)@, old(out)@.len() as int, x@),
{
    append(out, x);
    proof {
        lemma_prefix_append(old(out)@, x@);
        assert(final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int) =~= x@);
    }
}

fn put_u16(out: &mut Vec<u8>, x: u16)
    ensures
        final(out)@ == old(out)@ + ser_u16(x),
        is_prefix(old(out)@, final(out)@),
        at(final(out)@, old(out)@.len() as int, ser_u16(x)),
{
    out.push((x / 256) as u8);
    out.push((x % 256) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + ser_u16(x));
        lemma_prefix_append(old(out)@, ser_u16(x));
        assert(final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int) =~= ser_u16(x));
    }
}

fn put_u32(out: &mut Vec<u8>, x: u32)
    ensures
        final(out)@ == old(out)@ + ser_u32(x),
        is_prefix(old(out)@, final(out)@),
        at(final(out)@, old(out)@.len() as int, ser_u32(x)),
{
    out.push((x / 0x100_0000) as u8);
    out.push(((x / 0x1_0000) % 256) as u8);
    out.push(((x / 256) % 256) as u8);
    out.push((x % 256) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + ser_u32(x));
        lemma_prefix_append(old(out)@, ser_u32(x));
        assert(final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int) =~= ser_u32(x));
    }
}

fn plan_bytes(p: &Plan) -> (r: usize)
    requires
        plan_len(*p) <= 255,
    ensures
        r == plan_len(*p),
{
    match p.ptr {
        Some(_) => p.cut + 2,
        None => p.cut + 1,
    }
}

/// The length of the uncompressed name `n` at `arena[start..]`.
fn name_len(arena: &[u8], start: usize, n: Ghost<SpecName>) -> (r: usize)
    requires
        at(arena@, start as int, ser_name(n@)),
        valid_name(n@),
    ensures
        r == ser_name(n@).len(),
{
    let _ = arena.len();
    let mut c: usize = 0;
    let ghost mut i: int = 0;
    loop
        invariant
            arena@.len() <= usize::MAX,
            at(arena@, start as int, ser_name(n@)),
            valid_name(n@),
            0 <= i <= n@.len(),
            c == ser_labels(n@.take(i)).len(),
        decreases n@.len() - i,
    {
        proof {
            lemma_name_split(n@, i);
            assert(ser_name(n@.skip(i)).len() >= 1);
            assert(c < ser_name(n@).len());
            assert(arena@.subrange(start as int, start + ser_name(n@).len())[c as int] == arena@[start
                + c]);
            if i == n@.len() {
                assert(n@.skip(i) =~= Seq::<Seq<u8>>::empty());
            } else {
                assert(valid_label(n@[i]));
            }
        }
        let len = arena[start + c];
        if len == 0 {
            proof {
                if i < n@.len() {
                    assert(ser_name(n@)[c as int] == n@[i].len() as u8);
                }
                assert(n@.skip(i) =~= Seq::<Seq<u8>>::empty());
            }
            return c + 1;
        }
        proof {
            if i == n@.len() {
                assert(ser_name(n@.skip(i))[0] == 0);
            }
        }
        c = c + 1 + len as usize;
        proof {
            i = i + 1;
        }
    }
}

/// The span of `x` inside the span `sp` that holds `whole`.
proof fn lemma_sub_span(arena: Seq<u8>, sp: Span, whole: Seq<u8>, a: int, x: Seq<u8>)
    requires
        span_ok(arena, sp, whole),
        arena.len() <= usize::MAX,
        0 <= a,
        a + x.len() <= whole.len(),
        whole.subrange(a, a + x.len()) == x,
    ensures
        span_ok(arena, Span { start: (sp.start + a) as usize, len: x.len() as usize }, x),
        at(arena, sp.start + a, x),
{
    assert(arena.subrange(sp.start + a, sp.start + a + x.len()) =~= x) by {
        assert forall|k: int| 0 <= k < x.len() implies arena.subrange(sp.start + a, sp.start + a + x.len())[k] == x[k] by {
            assert(whole[a + k] == x[k]);
            assert(span_bytes(arena, sp)[a + k] == arena[sp.start + a + k]);
        }
    }
}

/// Writes question `q` with its name compressed.
pub fn write_question(
    out: &mut Vec<u8>,
    dict: &mut Dict,
    g: Ghost<Seq<SpecName>>,
    arena: &[u8],
    e: Entry,
    q: Ghost<SpecQuestion>,
) -> (g2: Ghost<Seq<SpecName>>)
    requires
        question_ok(arena@, e, q@),
        valid_question(q@),
        dict_ok(old(out)@, arena@, old(dict)@, g@),
    ensures
        parse_question(final(out)@, old(out)@.len() as int) == Some((q@, final(out)@.len() as int)),
        is_prefix(old(out)@, final(out)@),
        dict_ok(final(out)@, arena@, final(dict)@, g2@),
        final(out)@.len() <= old(out)@.len() + 259,
{
    let ghost o0 = out@;
    let p = plan_name(dict, g, Ghost(o0), arena, e.name, Ghost(q@.qname));
    let g2 = emit_name(out, dict, g, arena, e.name, Ghost(q@.qname), &p);
    let ghost o1 = out@;
    put_u16(out, e.rtype);
    let ghost o2 = out@;
    put_u16(out, e.rclass);
    proof {
        lemma_plan_len(old(dict)@, g@, q@.qname, p);
        lemma_prefix_trans(o1, o2, out@);
        lemma_prefix_trans(o0, o1, out@);
        lemma_dict_ext(o1, out@, arena@, dict@, g2@);
        lemma_name_ext(o1, out@, o0.len() as int);
        lemma_at_ext(o2, out@, o1.len() as int, ser_u16(e.rtype));
        lemma_u16_roundtrip(out@, o1.len() as int, e.rtype);
        lemma_u16_roundtrip(out@, o2.len() as int, e.rclass);
    }
    g2
}

/// `b[p0..]` is an RDLENGTH and RDATA of type `t` that parse as the
/// canonical RDATA `rd`.
pub open spec fn rdata_written(b: Seq<u8>, p0: int, t: u16, rd: Seq<u8>) -> bool {
    &&& 0 <= p0
    &&& p0 + 2 <= b.len()
    &&& b.len() - p0 - 2 <= 65535
    &&& parse_u16(b, p0) == Some(((b.len() - p0 - 2) as u16, p0 + 2))
    &&& canon_rdata(b, t, p0 + 2, b.len() as int) == Some(rd)
}

/// The precondition of every RDATA writer.
pub open spec fn rdata_in(arena: Seq<u8>, sp: Span, t: u16, rd: Seq<u8>) -> bool {
    &&& span_ok(arena, sp, rd)
    &&& arena.len() <= usize::MAX
    &&& rd.len() <= 65535
    &&& canon_rdata(rd, t, 0, rd.len() as int) == Some(rd)
}

proof fn lemma_rdlen(b: Seq<u8>, o1: Seq<u8>, p0: int, l: u16)
    requires
        is_prefix(o1, b),
        p0 + 2 == o1.len(),
        at(o1, p0, ser_u16(l)),
        b.len() - p0 - 2 == l,
        0 <= p0,
    ensures
        parse_u16(b, p0) == Some(((b.len() - p0 - 2) as u16, p0 + 2)),
{
    lemma_at_ext(o1, b, p0, ser_u16(l));
    lemma_u16_roundtrip(b, p0, l);
}

/// NS, CNAME, PTR: one name, compressed.
fn rdata_one_name(
    out: &mut Vec<u8>,
    dict: &mut Dict,
    g: Ghost<Seq<SpecName>>,
    arena: &[u8],
    t: u16,
    sp: Span,
    rd: Ghost<Seq<u8>>,
) -> (g2: Ghost<Seq<SpecName>>)
    requires
        t == 2 || t == 5 || t == 12,
        rdata_in(arena@, sp, t, rd@),
        dict_ok(old(out)@, arena@, old(dict)@, g@),
    ensures
        rdata_written(final(out)@, old(out)@.len() as int, t, rd@),
        is_prefix(old(out)@, final(out)@),
        dict_ok(final(out)@, arena@, final(dict)@, g2@),
{
    let ghost o0 = out@;
    let ghost n = parse_name_exact(rd@, 0, rd@.len() as int).unwrap();
    proof {
        lemma_parse_name_valid(rd@, 0);
        assert(rd@ == ser_name(n));
    }
    let p = plan_name(dict, g, Ghost(o0), arena, sp, Ghost(n));
    proof {
        lemma_plan_len(dict@, g@, n, p);
    }
    let l = plan_bytes(&p);
    put_u16(out, l as u16);
    let ghost o1 = out@;
    proof {
        lemma_dict_ext(o0, o1, arena@, dict@, g@);
    }
    let g2 = emit_name(out, dict, g, arena, sp, Ghost(n), &p);
    proof {
        let b = out@;
        let p0 = o0.len() as int;
        lemma_prefix_trans(o0, o1, b);
        lemma_rdlen(b, o1, p0, l as u16);
        assert(parse_name_exact(b, p0 + 2, b.len() as int) == Some(n));
        assert(canon_names(b, t, p0 + 2, b.len() as int) == Some(ser_name(n)));
    }
    g2
}

/// MX: the preference, then the exchange name, compressed.
fn rdata_mx(
    out: &mut Vec<u8>,
    dict: &mut Dict,
    g: Ghost<Seq<SpecName>>,
    arena: &[u8],
    sp: Span,
    rd: Ghost<Seq<u8>>,
) -> (g2: Ghost<Seq<SpecName>>)
    requires
        rdata_in(arena@, sp, 15, rd@),
        dict_ok(old(out)@, arena@, old(dict)@, g@),
    ensures
        rdata_written(final(out)@, old(out)@.len() as int, 15, rd@),
        is_prefix(old(out)@, final(out)@),
        dict_ok(final(out)@, arena@, final(dict)@, g2@),
{
    let ghost o0 = out@;
    let ghost n = parse_name_exact(rd@, 2, rd@.len() as int).unwrap();
    let ghost pre = rd@.subrange(0, 2);
    proof {
        lemma_parse_name_valid(rd@, 2);
        assert(rd@ == pre + ser_name(n));
        assert(rd@.subrange(2, 2 + ser_name(n).len() as int) =~= ser_name(n));
        lemma_sub_span(arena@, sp, rd@, 2, ser_name(n));
        lemma_sub_span(arena@, sp, rd@, 0, pre);
    }
    let nsp = Span { start: sp.start + 2, len: sp.len - 2 };
    let p = plan_name(dict, g, Ghost(o0), arena, nsp, Ghost(n));
    proof {
        lemma_plan_len(dict@, g@, n, p);
    }
    let l = 2 + plan_bytes(&p);
    put_u16(out, l as u16);
    let ghost o1 = out@;
    put(out, slice_subrange(arena, sp.start, sp.start + 2));
    let ghost o2 = out@;
    proof {
        lemma_prefix_trans(o0, o1, o2);
        lemma_dict_ext(o0, o2, arena@, dict@, g@);
    }
    let g2 = emit_name(out, dict, g, arena, nsp, Ghost(n), &p);
    proof {
        let b = out@;
        let p0 = o0.len() as int;
        lemma_prefix_trans(o0, o2, b);
        lemma_prefix_trans(o1, o2, b);
        lemma_rdlen(b, o1, p0, l as u16);
        lemma_at_ext(o2, b, p0 + 2, pre);
        assert(b.subrange(p0 + 2, p0 + 4) == pre);
        assert(parse_name_exact(b, p0 + 4, b.len() as int) == Some(n));
        assert(canon_names(b, 15, p0 + 2, b.len() as int) == Some(pre + ser_name(n)));
    }
    g2
}

proof fn lemma_soa_written(b: Seq<u8>, s: int, n1: SpecName, n2: SpecName, m1: int, q: int, tail: Seq<u8>)
    requires
        0 <= s,
        parse_name(b, s) == Some((n1, m1)),
        parse_name(b, m1) == Some((n2, q)),
        q + 20 == b.len(),
        b.subrange(q, b.len() as int) == tail,
        (ser_name(n1) + ser_name(n2) + tail).len() <= 65535,
    ensures
        canon_rdata(b, 6, s, b.len() as int) == Some(ser_name(n1) + ser_name(n2) + tail),
{
    lemma_parse_name_valid(b, s);
    lemma_parse_name_valid(b, m1);
}

proof fn lemma_record_assembled(b: Seq<u8>, p0: int, r: SpecRecord, q1: int)
    requires
        parse_name(b, p0) == Some((r.name, q1)),
        at(b, q1, ser_u16(r.rtype)),
        at(b, q1 + 2, ser_u16(r.rclass)),
        at(b, q1 + 4, ser_u32(r.ttl)),
        rdata_written(b, q1 + 8, r.rtype, r.rdata),
    ensures
        parse_record(b, p0) == Some((r, b.len() as int)),
{
    hide(canon_rdata);
    lemma_u16_roundtrip(b, q1, r.rtype);
    lemma_u16_roundtrip(b, q1 + 2, r.rclass);
    lemma_u32_roundtrip(b, q1 + 4, r.ttl);
}

proof fn lemma_soa_parts(rd: Seq<u8>)
    requires
        canon_rdata(rd, 6, 0, rd.len() as int) == Some(rd),
    ensures
        ({
            let len = rd.len() as int;
            let (n1, q1) = parse_name_in(rd, 0, len).unwrap();
            let (n2, q2) = parse_name_in(rd, q1, len).unwrap();
            let tail = rd.subrange(q2, len);
            &&& valid_name(n1)
            &&& valid_name(n2)
            &&& rd == ser_name(n1) + ser_name(n2) + tail
            &&& tail.len() == 20
            &&& rd.subrange(0, ser_name(n1).len() as int) == ser_name(n1)
            &&& rd.subrange(ser_name(n1).len() as int, (ser_name(n1).len() + ser_name(n2).len()) as int)
                == ser_name(n2)
            &&& rd.subrange((ser_name(n1).len() + ser_name(n2).len()) as int, len) == tail
        }),
{
    let len = rd.len() as int;
    let (n1, q1) = parse_name_in(rd, 0, len).unwrap();
    let (n2, q2) = parse_name_in(rd, q1, len).unwrap();
    let tail = rd.subrange(q2, len);
    lemma_parse_name_valid(rd, 0);
    lemma_parse_name_valid(rd, q1);
    let (s1, s2) = (ser_name(n1), ser_name(n2));
    assert(rd == s1 + s2 + tail);
    assert(rd.subrange(0, s1.len() as int) =~= s1);
    assert(rd.subrange(s1.len() as int, (s1.len() + s2.len()) as int) =~= s2);
    assert(rd.subrange((s1.len() + s2.len()) as int, len) =~= tail);
}

/// SOA: two names, compressed, then the 20 octets of counters.
#[verifier::spinoff_prover]
fn rdata_soa(
    out: &mut Vec<u8>,
    dict: &mut Dict,
    g: Ghost<Seq<SpecName>>,
    arena: &[u8],
    sp: Span,
    rd: Ghost<Seq<u8>>,
) -> (g3: Ghost<Seq<SpecName>>)
    requires
        rdata_in(arena@, sp, 6, rd@),
        dict_ok(old(out)@, arena@, old(dict)@, g@),
    ensures
        rdata_written(final(out)@, old(out)@.len() as int, 6, rd@),
        is_prefix(old(out)@, final(out)@),
        dict_ok(final(out)@, arena@, final(dict)@, g3@),
{
    hide(canon_rdata);
    hide(canon_names);
    let ghost o0 = out@;
    let ghost len = rd@.len() as int;
    let ghost n1 = parse_name_in(rd@, 0, len).unwrap().0;
    let ghost q1 = parse_name_in(rd@, 0, len).unwrap().1;
    let ghost n2 = parse_name_in(rd@, q1, len).unwrap().0;
    let ghost q2 = parse_name_in(rd@, q1, len).unwrap().1;
    let ghost s1 = ser_name(n1);
    let ghost s2 = ser_name(n2);
    let ghost tail = rd@.subrange(q2, len);
    proof {
        lemma_soa_parts(rd@);
        lemma_sub_span(arena@, sp, rd@, 0, s1);
        lemma_sub_span(arena@, sp, rd@, s1.len() as int, s2);
        lemma_sub_span(arena@, sp, rd@, (s1.len() + s2.len()) as int, tail);
    }
    let a = name_len(arena, sp.start, Ghost(n1));
    let b = name_len(arena, sp.start + a, Ghost(n2));
    let sp1 = Span { start: sp.start, len: a };
    let sp2 = Span { start: sp.start + a, len: b };
    let p1 = plan_name(dict, g, Ghost(o0), arena, sp1, Ghost(n1));
    let p2 = plan_name(dict, g, Ghost(o0), arena, sp2, Ghost(n2));
    proof {
        lemma_plan_len(dict@, g@, n1, p1);
        lemma_plan_len(dict@, g@, n2, p2);
    }
    let l = plan_bytes(&p1) + plan_bytes(&p2) + 20;
    put_u16(out, l as u16);
    let ghost o1 = out@;
    let ghost d0 = dict@;
    proof {
        lemma_dict_ext(o0, o1, arena@, dict@, g@);
    }
    let g2 = emit_name(out, dict, g, arena, sp1, Ghost(n1), &p1);
    let ghost o2 = out@;
    proof {
        lemma_plan_grow(d0, g@, dict@, g2@, n2, p2);
    }
    let g3 = emit_name(out, dict, g2, arena, sp2, Ghost(n2), &p2);
    let ghost o3 = out@;
    put(out, slice_subrange(arena, sp.start + a + b, sp.start + sp.len));
    proof {
        let bb = out@;
        let p0 = o0.len() as int;
        lemma_prefix_trans(o0, o1, o2);
        lemma_prefix_trans(o2, o3, bb);
        lemma_prefix_trans(o0, o2, bb);
        lemma_prefix_trans(o1, o2, bb);
        lemma_dict_ext(o3, bb, arena@, dict@, g3@);
        lemma_rdlen(bb, o1, p0, l as u16);
        lemma_name_ext(o2, bb, p0 + 2);
        lemma_name_ext(o3, bb, o2.len() as int);
        let q = o3.len() as int;
        assert(bb.subrange(q, bb.len() as int) == tail);
        lemma_soa_written(bb, p0 + 2, n1, n2, o2.len() as int, q, tail);
    }
    g3
}

/// Any other type: the canonical RDATA as it is (RFC 3597 §4: only the
/// RFC 1035 types may be compressed).
fn rdata_raw(
    out: &mut Vec<u8>,
    dict: &Dict,
    g: Ghost<Seq<SpecName>>,
    arena: &[u8],
    t: u16,
    sp: Span,
    rd: Ghost<Seq<u8>>,
)
    requires
        rdata_in(arena@, sp, t, rd@),
        dict_ok(old(out)@, arena@, dict@, g@),
    ensures
        rdata_written(final(out)@, old(out)@.len() as int, t, rd@),
        is_prefix(old(out)@, final(out)@),
        dict_ok(final(out)@, arena@, dict@, g@),
{
    let ghost o0 = out@;
    put_u16(out, sp.len as u16);
    let ghost o1 = out@;
    put(out, slice_subrange(arena, sp.start, sp.start + sp.len));
    proof {
        let b = out@;
        let p0 = o0.len() as int;
        lemma_prefix_trans(o0, o1, b);
        lemma_dict_ext(o0, b, arena@, dict@, g@);
        lemma_rdlen(b, o1, p0, sp.len as u16);
        lemma_canon_rdata_moves(rd@, t, 0, rd@.len() as int, b, p0 + 2);
    }
}

/// Writes record `r` with its owner name, and names inside NS, CNAME, SOA,
/// PTR and MX RDATA, compressed.
#[verifier::spinoff_prover]
pub fn write_record(
    out: &mut Vec<u8>,
    dict: &mut Dict,
    g: Ghost<Seq<SpecName>>,
    arena: &[u8],
    e: Entry,
    r: Ghost<SpecRecord>,
) -> (g2: Ghost<Seq<SpecName>>)
    requires
        record_ok(arena@, e, r@),
        valid_record(r@),
        dict_ok(old(out)@, arena@, old(dict)@, g@),
    ensures
        parse_record(final(out)@, old(out)@.len() as int) == Some((r@, final(out)@.len() as int)),
        is_prefix(old(out)@, final(out)@),
        dict_ok(final(out)@, arena@, final(dict)@, g2@),
{
    let _ = arena.len();
    let ghost o0 = out@;
    let p = plan_name(dict, g, Ghost(o0), arena, e.name, Ghost(r@.name));
    let g1 = emit_name(out, dict, g, arena, e.name, Ghost(r@.name), &p);
    let ghost o1 = out@;
    put_u16(out, e.rtype);
    let ghost o2 = out@;
    put_u16(out, e.rclass);
    let ghost o3 = out@;
    put_u32(out, e.ttl);
    let ghost o4 = out@;
    proof {
        lemma_prefix_trans(o1, o2, o3);
        lemma_prefix_trans(o1, o3, o4);
        lemma_dict_ext(o1, o4, arena@, dict@, g1@);
    }
    let t = e.rtype;
    let g2 = if t == 2 || t == 5 || t == 12 {
        rdata_one_name(out, dict, g1, arena, t, e.rdata, Ghost(r@.rdata))
    } else if t == 15 {
        rdata_mx(out, dict, g1, arena, e.rdata, Ghost(r@.rdata))
    } else if t == 6 {
        rdata_soa(out, dict, g1, arena, e.rdata, Ghost(r@.rdata))
    } else {
        rdata_raw(out, dict, g1, arena, t, e.rdata, Ghost(r@.rdata));
        g1
    };
    proof {
        let b = out@;
        let p0 = o0.len() as int;
        lemma_prefix_trans(o2, o3, o4);
        lemma_prefix_trans(o0, o1, o4);
        lemma_prefix_trans(o0, o4, b);
        lemma_prefix_trans(o1, o4, b);
        lemma_prefix_trans(o2, o4, b);
        lemma_prefix_trans(o3, o4, b);
        lemma_name_ext(o1, b, p0);
        lemma_at_ext(o2, b, o1.len() as int, ser_u16(e.rtype));
        lemma_at_ext(o3, b, o2.len() as int, ser_u16(e.rclass));
        lemma_at_ext(o4, b, o3.len() as int, ser_u32(e.ttl));
        lemma_record_assembled(b, p0, r@, o1.len() as int);
    }
    g2
}

// ---------------------------------------------------------------------------
// Sections
// ---------------------------------------------------------------------------

/// The questions `qs` were written one after another at the offsets `ps`.
pub open spec fn qs_at(b: Seq<u8>, ps: Seq<int>, qs: Seq<SpecQuestion>) -> bool {
    &&& ps.len() == qs.len() + 1
    &&& forall|j: int| 0 <= j < qs.len() ==> #[trigger] parse_question(b, ps[j]) == Some((qs[j], ps[j + 1]))
}

pub open spec fn rs_at(b: Seq<u8>, ps: Seq<int>, rs: Seq<SpecRecord>) -> bool {
    &&& ps.len() == rs.len() + 1
    &&& forall|j: int| 0 <= j < rs.len() ==> #[trigger] parse_record(b, ps[j]) == Some((rs[j], ps[j + 1]))
}

pub proof fn lemma_qs_parse(b: Seq<u8>, ps: Seq<int>, qs: Seq<SpecQuestion>)
    requires
        qs_at(b, ps, qs),
    ensures
        parse_questions(b, ps[0], qs.len()) == Some((qs, ps[qs.len() as int])),
    decreases qs.len(),
{
    if qs.len() > 0 {
        assert(parse_question(b, ps[0]) == Some((qs[0], ps[1])));
        let (ps2, qs2) = (ps.drop_first(), qs.drop_first());
        assert forall|j: int| 0 <= j < qs2.len() implies #[trigger] parse_question(b, ps2[j]) == Some((qs2[j], ps2[j + 1])) by {
            assert(parse_question(b, ps[j + 1]) == Some((qs[j + 1], ps[j + 2])));
        }
        lemma_qs_parse(b, ps2, qs2);
        assert(seq![qs[0]] + qs2 =~= qs);
    }
}

pub proof fn lemma_rs_parse(b: Seq<u8>, ps: Seq<int>, rs: Seq<SpecRecord>)
    requires
        rs_at(b, ps, rs),
    ensures
        parse_records(b, ps[0], rs.len()) == Some((rs, ps[rs.len() as int])),
    decreases rs.len(),
{
    if rs.len() > 0 {
        assert(parse_record(b, ps[0]) == Some((rs[0], ps[1])));
        let (ps2, rs2) = (ps.drop_first(), rs.drop_first());
        assert forall|j: int| 0 <= j < rs2.len() implies #[trigger] parse_record(b, ps2[j]) == Some((rs2[j], ps2[j + 1])) by {
            assert(parse_record(b, ps[j + 1]) == Some((rs[j + 1], ps[j + 2])));
        }
        lemma_rs_parse(b, ps2, rs2);
        assert(seq![rs[0]] + rs2 =~= rs);
    }
}

pub proof fn lemma_qs_ext(b: Seq<u8>, b2: Seq<u8>, ps: Seq<int>, qs: Seq<SpecQuestion>)
    requires
        is_prefix(b, b2),
        qs_at(b, ps, qs),
    ensures
        qs_at(b2, ps, qs),
{
    assert forall|j: int| 0 <= j < qs.len() implies #[trigger] parse_question(b2, ps[j]) == Some((qs[j], ps[j + 1])) by {
        assert(parse_question(b, ps[j]) == Some((qs[j], ps[j + 1])));
        lemma_question_ext(b, b2, ps[j]);
    }
}

pub proof fn lemma_rs_ext(b: Seq<u8>, b2: Seq<u8>, ps: Seq<int>, rs: Seq<SpecRecord>)
    requires
        is_prefix(b, b2),
        rs_at(b, ps, rs),
    ensures
        rs_at(b2, ps, rs),
{
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] parse_record(b2, ps[j]) == Some((rs[j], ps[j + 1])) by {
        assert(parse_record(b, ps[j]) == Some((rs[j], ps[j + 1])));
        lemma_record_ext(b, b2, ps[j]);
    }
}

/// One more question, written at the end.
pub proof fn lemma_qs_push(b: Seq<u8>, b2: Seq<u8>, ps: Seq<int>, qs: Seq<SpecQuestion>, q: SpecQuestion)
    requires
        is_prefix(b, b2),
        qs_at(b, ps, qs),
        ps[qs.len() as int] == b.len(),
        parse_question(b2, b.len() as int) == Some((q, b2.len() as int)),
    ensures
        qs_at(b2, ps.push(b2.len() as int), qs.push(q)),
{
    lemma_qs_ext(b, b2, ps, qs);
    let (ps2, qs2) = (ps.push(b2.len() as int), qs.push(q));
    assert forall|j: int| 0 <= j < qs2.len() implies #[trigger] parse_question(b2, ps2[j]) == Some((qs2[j], ps2[j + 1])) by {
        if j < qs.len() {
            assert(parse_question(b2, ps[j]) == Some((qs[j], ps[j + 1])));
        }
    }
}

pub proof fn lemma_rs_push(b: Seq<u8>, b2: Seq<u8>, ps: Seq<int>, rs: Seq<SpecRecord>, r: SpecRecord)
    requires
        is_prefix(b, b2),
        rs_at(b, ps, rs),
        ps[rs.len() as int] == b.len(),
        parse_record(b2, b.len() as int) == Some((r, b2.len() as int)),
    ensures
        rs_at(b2, ps.push(b2.len() as int), rs.push(r)),
{
    lemma_rs_ext(b, b2, ps, rs);
    let (ps2, rs2) = (ps.push(b2.len() as int), rs.push(r));
    assert forall|j: int| 0 <= j < rs2.len() implies #[trigger] parse_record(b2, ps2[j]) == Some((rs2[j], ps2[j + 1])) by {
        if j < rs.len() {
            assert(parse_record(b2, ps[j]) == Some((rs[j], ps[j + 1])));
        }
    }
}

} // verus!
