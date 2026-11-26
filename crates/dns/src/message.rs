//! The message type. Every name and RDATA lives in one byte arena and every
//! question and record in one entry table, so a parsed message costs two
//! allocations however many labels and records it has (zero when a
//! `Message` is reused with `parse_into`).
//!
//! A `Message` is well-formed by construction: its type invariant ties the
//! arena and entry table to a ghost `SpecMessage` that satisfies
//! `valid_message`. Every way to obtain a `Message` (parsing, building)
//! establishes it, so every `Message` serializes to bytes that parse back to
//! itself.
use alloc::vec::Vec;
#[cfg(verus_only)]
use crate::lemmas::*;
use crate::parse::{append, read_name_into};
use crate::compress::*;
use crate::rdata::canon_into;
#[cfg(verus_only)]
use crate::lemmas_rdata::*;
#[allow(unused_imports)]
use crate::spec_rdata::*;
use crate::spec::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// A range of a message's arena.
#[derive(Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub len: usize,
}

/// One question or record. For a question, `rtype`/`rclass` hold QTYPE and
/// QCLASS, and `ttl` and `rdata` are unused.
#[derive(Clone, Copy)]
pub struct Entry {
    pub name: Span,
    pub rtype: u16,
    pub rclass: u16,
    pub ttl: u32,
    pub rdata: Span,
}

pub open spec fn span_bytes(arena: Seq<u8>, s: Span) -> Seq<u8> {
    arena.subrange(s.start as int, s.start + s.len)
}

pub open spec fn span_ok(arena: Seq<u8>, s: Span, x: Seq<u8>) -> bool {
    s.start + s.len <= arena.len() && span_bytes(arena, s) == x
}

pub open spec fn question_ok(arena: Seq<u8>, e: Entry, q: SpecQuestion) -> bool {
    &&& span_ok(arena, e.name, ser_name(q.qname))
    &&& e.rtype == q.qtype
    &&& e.rclass == q.qclass
}

pub open spec fn record_ok(arena: Seq<u8>, e: Entry, r: SpecRecord) -> bool {
    &&& span_ok(arena, e.name, ser_name(r.name))
    &&& e.rtype == r.rtype
    &&& e.rclass == r.rclass
    &&& e.ttl == r.ttl
    &&& span_ok(arena, e.rdata, r.rdata)
}

/// Entries `v[off..off + s.len()]` hold the questions `s`.
pub open spec fn questions_at(arena: Seq<u8>, v: Seq<Entry>, off: int, s: Seq<SpecQuestion>) -> bool {
    &&& 0 <= off
    &&& off + s.len() <= v.len()
    &&& forall|i: int| 0 <= i < s.len() ==> question_ok(arena, #[trigger] v[off + i], s[i])
}

/// Entries `v[off..off + s.len()]` hold the records `s`.
pub open spec fn records_at(arena: Seq<u8>, v: Seq<Entry>, off: int, s: Seq<SpecRecord>) -> bool {
    &&& 0 <= off
    &&& off + s.len() <= v.len()
    &&& forall|i: int| 0 <= i < s.len() ==> record_ok(arena, #[trigger] v[off + i], s[i])
}

pub open spec fn is_prefix<T>(a: Seq<T>, b: Seq<T>) -> bool {
    a.len() <= b.len() && b.subrange(0, a.len() as int) == a
}

pub proof fn lemma_span_ok_grow(a: Seq<u8>, b: Seq<u8>, s: Span, x: Seq<u8>)
    requires
        is_prefix(a, b),
        span_ok(a, s, x),
    ensures
        span_ok(b, s, x),
{
    assert(span_bytes(b, s) =~= span_bytes(a, s)) by {
        assert forall|i: int| 0 <= i < s.len implies span_bytes(b, s)[i] == span_bytes(a, s)[i] by {
            assert(b.subrange(0, a.len() as int)[s.start + i] == b[s.start + i]);
        }
    }
}

/// Growing the arena or the entry table keeps existing entries valid.
pub proof fn lemma_questions_at_grow(
    a: Seq<u8>,
    b: Seq<u8>,
    v: Seq<Entry>,
    w: Seq<Entry>,
    off: int,
    s: Seq<SpecQuestion>,
)
    requires
        is_prefix(a, b),
        is_prefix(v, w),
        questions_at(a, v, off, s),
    ensures
        questions_at(b, w, off, s),
{
    assert forall|i: int| 0 <= i < s.len() implies question_ok(b, #[trigger] w[off + i], s[i]) by {
        assert(w.subrange(0, v.len() as int)[off + i] == w[off + i]);
        assert(question_ok(a, v[off + i], s[i]));
        lemma_span_ok_grow(a, b, w[off + i].name, ser_name(s[i].qname));
    }
}

pub proof fn lemma_records_at_grow(
    a: Seq<u8>,
    b: Seq<u8>,
    v: Seq<Entry>,
    w: Seq<Entry>,
    off: int,
    s: Seq<SpecRecord>,
)
    requires
        is_prefix(a, b),
        is_prefix(v, w),
        records_at(a, v, off, s),
    ensures
        records_at(b, w, off, s),
{
    assert forall|i: int| 0 <= i < s.len() implies record_ok(b, #[trigger] w[off + i], s[i]) by {
        assert(w.subrange(0, v.len() as int)[off + i] == w[off + i]);
        assert(record_ok(a, v[off + i], s[i]));
        lemma_span_ok_grow(a, b, w[off + i].name, ser_name(s[i].name));
        lemma_span_ok_grow(a, b, w[off + i].rdata, s[i].rdata);
    }
}

pub proof fn lemma_prefix_refl<T>(a: Seq<T>)
    ensures
        is_prefix(a, a),
{
    assert(a.subrange(0, a.len() as int) =~= a);
}

pub proof fn lemma_prefix_append<T>(a: Seq<T>, x: Seq<T>)
    ensures
        is_prefix(a, a + x),
{
    assert((a + x).subrange(0, a.len() as int) =~= a);
}

pub proof fn lemma_prefix_push<T>(a: Seq<T>, x: T)
    ensures
        is_prefix(a, a.push(x)),
{
    assert(a.push(x).subrange(0, a.len() as int) =~= a);
}

pub proof fn lemma_prefix_trans<T>(a: Seq<T>, b: Seq<T>, c: Seq<T>)
    requires
        is_prefix(a, b),
        is_prefix(b, c),
    ensures
        is_prefix(a, c),
{
    assert(c.subrange(0, a.len() as int) =~= b.subrange(0, a.len() as int)) by {
        assert forall|i: int| 0 <= i < a.len() implies c.subrange(0, a.len() as int)[i]
            == b.subrange(0, a.len() as int)[i] by {
            assert(c.subrange(0, b.len() as int)[i] == c[i]);
        }
    }
}

/// The section a record belongs to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Section {
    Answer,
    Authority,
    Additional,
}

/// A parsed or built DNS message.
pub struct Message {
    id: u16,
    flags: u16,
    arena: Vec<u8>,
    /// Questions, then answers, then authorities, then additionals.
    entries: Vec<Entry>,
    qd: usize,
    an: usize,
    ns: usize,
    /// For a parsed message, the arena starts with a copy of the message,
    /// `arena[..wire]` (the context typed RDATA is decoded in); 0 otherwise.
    wire: usize,
    spec: Ghost<SpecMessage>,
}

/// The invariant, stated over a message's parts.
pub open spec fn parts_ok(
    id: u16,
    flags: u16,
    arena: Seq<u8>,
    entries: Seq<Entry>,
    qd: usize,
    an: usize,
    ns: usize,
    m: SpecMessage,
) -> bool {
    &&& m.id == id
    &&& m.flags == flags
    &&& valid_message(m)
    &&& qd == m.questions.len()
    &&& an == m.answers.len()
    &&& ns == m.authorities.len()
    &&& entries.len() == qd + an + ns + m.additionals.len()
    &&& questions_at(arena, entries, 0, m.questions)
    &&& records_at(arena, entries, qd as int, m.answers)
    &&& records_at(arena, entries, qd + an, m.authorities)
    &&& records_at(arena, entries, qd + an + ns, m.additionals)
}

impl Message {
    pub closed spec fn wf(self) -> bool {
        parts_ok(
            self.id,
            self.flags,
            self.arena@,
            self.entries@,
            self.qd,
            self.an,
            self.ns,
            self.spec@,
        )
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        self.wf() && self.wire <= self.arena@.len()
    }

    /// The message this was parsed from (empty for a built message).
    pub closed spec fn wire_bytes(self) -> Seq<u8> {
        self.arena@.subrange(0, self.wire as int)
    }

    /// Assembles a message from parts that satisfy the invariant.
    pub(crate) fn from_parts(
        id: u16,
        flags: u16,
        arena: Vec<u8>,
        entries: Vec<Entry>,
        qd: usize,
        an: usize,
        ns: usize,
        wire: usize,
        spec: Ghost<SpecMessage>,
    ) -> (m: Message)
        requires
            parts_ok(id, flags, arena@, entries@, qd, an, ns, spec@),
            wire <= arena@.len(),
        ensures
            m@ == spec@,
            m.wire_bytes() == arena@.subrange(0, wire as int),
    {
        Message { id, flags, arena, entries, qd, an, ns, wire, spec }
    }

    /// Takes the message apart, to reuse its buffers.
    pub(crate) fn into_buffers(self) -> (r: (Vec<u8>, Vec<Entry>)) {
        (self.arena, self.entries)
    }

    /// An empty message (no questions or records).
    pub fn new(id: u16, flags: u16) -> (m: Message)
        ensures
            m@ == (SpecMessage {
                id,
                flags,
                questions: Seq::empty(),
                answers: Seq::empty(),
                authorities: Seq::empty(),
                additionals: Seq::empty(),
            }),
    {
        Message::empty_with(Vec::new(), Vec::new()).with_header(id, flags)
    }

    pub(crate) fn empty_with(arena: Vec<u8>, entries: Vec<Entry>) -> (m: Message)
        requires
            entries@.len() == 0,
        ensures
            m@ == (SpecMessage {
                id: 0,
                flags: 0,
                questions: Seq::empty(),
                answers: Seq::empty(),
                authorities: Seq::empty(),
                additionals: Seq::empty(),
            }),
    {
        Message {
            id: 0,
            flags: 0,
            arena,
            entries,
            qd: 0,
            an: 0,
            ns: 0,
            wire: 0,
            spec: Ghost(
                SpecMessage {
                    id: 0,
                    flags: 0,
                    questions: Seq::empty(),
                    answers: Seq::empty(),
                    authorities: Seq::empty(),
                    additionals: Seq::empty(),
                },
            ),
        }
    }

    /// Sets the ID and flags.
    pub fn with_header(self, id: u16, flags: u16) -> (m: Message)
        ensures
            m@ == (SpecMessage { id, flags, ..self@ }),
    {
        proof {
            use_type_invariant(&self);
        }
        let Message { arena, entries, qd, an, ns, wire, spec, .. } = self;
        Message {
            id,
            flags,
            arena,
            entries,
            qd,
            an,
            ns,
            wire,
            spec: Ghost(SpecMessage { id, flags, ..spec@ }),
        }
    }

    /// Every message is well-formed.
    pub proof fn lemma_valid(tracked &self)
        ensures
            valid_message(self@),
    {
        use_type_invariant(self);
    }
}

impl View for Message {
    type V = SpecMessage;

    closed spec fn view(&self) -> SpecMessage {
        self.spec@
    }
}

} // verus!

verus! {

/// A question of a `Message`. `name` is the uncompressed wire form.
pub struct QuestionRef<'a> {
    pub name: &'a [u8],
    pub qtype: u16,
    pub qclass: u16,
}

/// A record of a `Message`. `name` is the uncompressed wire form.
pub struct RecordRef<'a> {
    pub name: &'a [u8],
    pub rtype: u16,
    pub rclass: u16,
    pub ttl: u32,
    /// The RDATA in canonical form: names inside it are uncompressed, so it
    /// decodes on its own (see `data`).
    pub rdata: &'a [u8],
}

pub open spec fn section_of(m: SpecMessage, s: Section) -> Seq<SpecRecord> {
    match s {
        Section::Answer => m.answers,
        Section::Authority => m.authorities,
        Section::Additional => m.additionals,
    }
}

/// The name an uncompressed wire-form byte string denotes, if it is one.
pub open spec fn wire_name(s: Seq<u8>) -> Option<SpecName> {
    match parse_name(s, 0) {
        Some((n, e)) => if e == s.len() {
            Some(n)
        } else {
            None
        },
        None => None,
    }
}

/// Why a `Message` builder call was refused. The message is unchanged.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BuildError {
    /// The name is not a valid uncompressed wire-form name.
    BadName,
    /// The section already holds 65535 entries.
    SectionFull,
    /// RDATA is longer than 65535 bytes (after decompressing names in it).
    RdataTooLong,
    /// RDATA of a type with names in it (NS, CNAME, SOA, PTR, MX, SIG, SRV,
    /// NAPTR) that does not decode as that type. Names in RDATA are
    /// resolved against the RDATA alone and stored uncompressed.
    BadRdata,
}

/// Without compression pointers to follow, a decoded name is exactly the
/// bytes it was decoded from.
proof fn lemma_parse_labels_seg0(b: Seq<u8>, pos: int)
    ensures
        parse_labels(b, pos, 0) matches Some((n, e)) ==> pos < e <= b.len() && b.subrange(pos, e)
            == ser_name(n),
    decreases b.len() - pos,
{
    if !(pos < 0 || pos >= b.len()) {
        let c = b[pos];
        if c == 0 {
            assert(b.subrange(pos, pos + 1) =~= ser_name(Seq::empty()));
        } else if 1 <= c < 64 && pos + 1 + c as int <= b.len() {
            let l = b.subrange(pos + 1, pos + 1 + c as int);
            lemma_parse_labels_seg0(b, pos + 1 + c as int);
            if let Some((rest, e)) = parse_labels(b, pos + 1 + c as int, 0) {
                let n = seq![l] + rest;
                assert(n.drop_first() =~= rest);
                assert(ser_name(n) =~= ser_label(l) + ser_name(rest));
                assert(b.subrange(pos, e) =~= ser_label(l) + b.subrange(pos + 1 + c as int, e));
            }
        }
    }
}

proof fn lemma_insert_shift(arena: Seq<u8>, v: Seq<Entry>, i: int, x: Entry, off: int, s: Seq<SpecRecord>)
    requires
        records_at(arena, v, off, s),
        0 <= i <= v.len(),
    ensures
        off + s.len() <= i ==> records_at(arena, v.insert(i, x), off, s),
        i <= off ==> records_at(arena, v.insert(i, x), off + 1, s),
{
    let w = v.insert(i, x);
    if off + s.len() <= i {
        assert forall|k: int| 0 <= k < s.len() implies record_ok(arena, #[trigger] w[off + k], s[k]) by {
            assert(w[off + k] == v[off + k]);
        }
    }
    if i <= off {
        assert forall|k: int| 0 <= k < s.len() implies record_ok(arena, #[trigger] w[off + 1 + k], s[k]) by {
            assert(w[off + 1 + k] == v[off + k]);
        }
    }
}

proof fn lemma_insert_shift_q(arena: Seq<u8>, v: Seq<Entry>, i: int, x: Entry, s: Seq<SpecQuestion>)
    requires
        questions_at(arena, v, 0, s),
        s.len() <= i <= v.len(),
    ensures
        questions_at(arena, v.insert(i, x), 0, s),
{
    let w = v.insert(i, x);
    assert forall|k: int| 0 <= k < s.len() implies question_ok(arena, #[trigger] w[0 + k], s[k]) by {
        assert(w[0 + k] == v[0 + k]);
    }
}

impl Message {
    pub fn id(&self) -> (r: u16)
        ensures
            r == self@.id,
    {
        proof {
            use_type_invariant(self);
        }
        self.id
    }

    pub fn flags(&self) -> (r: u16)
        ensures
            r == self@.flags,
    {
        proof {
            use_type_invariant(self);
        }
        self.flags
    }

    pub fn question_count(&self) -> (n: usize)
        ensures
            n == self@.questions.len(),
    {
        proof {
            use_type_invariant(self);
        }
        self.qd
    }

    pub fn record_count(&self, s: Section) -> (n: usize)
        ensures
            n == section_of(self@, s).len(),
    {
        proof {
            use_type_invariant(self);
        }
        match s {
            Section::Answer => self.an,
            Section::Authority => self.ns,
            Section::Additional => self.entries.len() - self.qd - self.an - self.ns,
        }
    }

    pub fn answer_count(&self) -> (n: usize)
        ensures
            n == self@.answers.len(),
    {
        self.record_count(Section::Answer)
    }

    fn span(&self, s: Span) -> (r: &[u8])
        requires
            s.start + s.len <= self.arena@.len(),
        ensures
            r@ == span_bytes(self.arena@, s),
    {
        let _ = self.arena.len();
        slice_subrange(self.arena.as_slice(), s.start, s.start + s.len)
    }

    /// The `i`th question, or `None` past the end.
    pub fn question(&self, i: usize) -> (r: Option<QuestionRef<'_>>)
        ensures
            i < self@.questions.len() ==> (r matches Some(q) && {
                let sq = self@.questions[i as int];
                &&& q.name@ == ser_name(sq.qname)
                &&& q.qtype == sq.qtype
                &&& q.qclass == sq.qclass
            }),
            i >= self@.questions.len() ==> r is None,
    {
        proof {
            use_type_invariant(self);
        }
        if i >= self.qd {
            return None;
        }
        let e = self.entries[i];
        proof {
            assert(question_ok(self.arena@, self.entries@[0 + i], self.spec@.questions[i as int]));
        }
        Some(QuestionRef { name: self.span(e.name), qtype: e.rtype, qclass: e.rclass })
    }

    fn section_start(&self, s: Section) -> (off: usize)
        ensures
            records_at(self.arena@, self.entries@, off as int, section_of(self@, s)),
            off + section_of(self@, s).len() <= self.entries@.len(),
    {
        proof {
            use_type_invariant(self);
        }
        match s {
            Section::Answer => self.qd,
            Section::Authority => self.qd + self.an,
            Section::Additional => self.qd + self.an + self.ns,
        }
    }

    /// The `i`th record of section `s`, or `None` past the end.
    pub fn record(&self, s: Section, i: usize) -> (r: Option<RecordRef<'_>>)
        ensures
            i < section_of(self@, s).len() ==> (r matches Some(rr) && {
                let sr = section_of(self@, s)[i as int];
                &&& rr.name@ == ser_name(sr.name)
                &&& rr.rtype == sr.rtype
                &&& rr.rclass == sr.rclass
                &&& rr.ttl == sr.ttl
                &&& rr.rdata@ == sr.rdata
            }),
            i >= section_of(self@, s).len() ==> r is None,
    {
        let n = self.record_count(s);
        if i >= n {
            return None;
        }
        let off = self.section_start(s);
        let _ = self.entries.len();
        let e = self.entries[off + i];
        proof {
            use_type_invariant(self);
            assert(record_ok(self.arena@, self.entries@[off + i], section_of(self@, s)[i as int]));
        }
        let rdata = self.span(e.rdata);
        Some(
            RecordRef {
                name: self.span(e.name),
                rtype: e.rtype,
                rclass: e.rclass,
                ttl: e.ttl,
                rdata,
            },
        )
    }

    // -----------------------------------------------------------------------
    // Serialization
    // -----------------------------------------------------------------------

    fn write_section(&self, out: &mut Vec<u8>, off: usize, n: usize, s: Ghost<Seq<SpecRecord>>)
        requires
            records_at(self.arena@, self.entries@, off as int, s@),
            forall|i: int| 0 <= i < s@.len() ==> valid_record(#[trigger] s@[i]),
            n == s@.len(),
        ensures
            final(out)@ == old(out)@ + ser_records(s@),
    {
        let _ = self.entries.len();
        let mut i: usize = 0;
        proof {
            assert(s@.take(0) =~= Seq::<SpecRecord>::empty());
            assert(out@ =~= old(out)@ + ser_records(s@.take(0)));
        }
        while i < n
            invariant
                i <= n,
                n == s@.len(),
                off + n <= self.entries@.len(),
                self.entries@.len() <= usize::MAX,
                forall|i: int| 0 <= i < s@.len() ==> valid_record(#[trigger] s@[i]),
                records_at(self.arena@, self.entries@, off as int, s@),
                out@ == old(out)@ + ser_records(s@.take(i as int)),
            decreases n - i,
        {
            let e = self.entries[off + i];
            let ghost r = s@[i as int];
            proof {
                assert(valid_record(r));
                assert(record_ok(self.arena@, self.entries@[off + i], r));
                assert(s@.take(i + 1) =~= s@.take(i as int).push(r));
                lemma_ser_records_push(s@.take(i as int), r);
            }
            let ghost before = out@;
            append(out, self.span(e.name));
            write_u16(out, e.rtype);
            write_u16(out, e.rclass);
            write_u32(out, e.ttl);
            write_u16(out, e.rdata.len as u16);
            append(out, self.span(e.rdata));
            proof {
                assert(out@ =~= before + ser_record(r));
            }
            i = i + 1;
        }
        proof {
            assert(s@.take(n as int) =~= s@);
        }
    }

    /// Appends the message's wire form (uncompressed) to `out`.
    pub fn write_to(&self, out: &mut Vec<u8>)
        ensures
            final(out)@ == old(out)@ + ser_message(self@),
    {
        proof {
            use_type_invariant(self);
        }
        let ghost m = self.spec@;
        let ar = self.entries.len() - self.qd - self.an - self.ns;
        write_u16(out, self.id);
        write_u16(out, self.flags);
        write_u16(out, self.qd as u16);
        write_u16(out, self.an as u16);
        write_u16(out, self.ns as u16);
        write_u16(out, ar as u16);
        proof {
            assert(out@ =~= old(out)@ + ser_header(m));
        }
        let ghost h = out@;
        let mut i: usize = 0;
        proof {
            assert(m.questions.take(0) =~= Seq::<SpecQuestion>::empty());
            assert(out@ =~= h + ser_questions(m.questions.take(0)));
        }
        while i < self.qd
            invariant
                i <= self.qd,
                self.wf(),
                m == self.spec@,
                out@ == h + ser_questions(m.questions.take(i as int)),
            decreases self.qd - i,
        {
            let e = self.entries[i];
            let ghost q = m.questions[i as int];
            proof {
                assert(question_ok(self.arena@, self.entries@[0 + i], q));
                assert(m.questions.take(i + 1) =~= m.questions.take(i as int).push(q));
                lemma_ser_questions_push(m.questions.take(i as int), q);
            }
            let ghost before = out@;
            append(out, self.span(e.name));
            write_u16(out, e.rtype);
            write_u16(out, e.rclass);
            proof {
                assert(out@ =~= before + ser_question(q));
            }
            i = i + 1;
        }
        proof {
            assert(m.questions.take(self.qd as int) =~= m.questions);
        }
        let ghost q_end = out@;
        self.write_section(out, self.qd, self.an, Ghost(m.answers));
        let ghost an_end = out@;
        self.write_section(out, self.qd + self.an, self.ns, Ghost(m.authorities));
        let ghost ns_end = out@;
        self.write_section(out, self.qd + self.an + self.ns, ar, Ghost(m.additionals));
        proof {
            assert(out@ =~= old(out)@ + ser_message(m));
        }
    }

    fn write_section_compressed(
        &self,
        out: &mut Vec<u8>,
        dict: &mut Dict,
        g: Ghost<Seq<SpecName>>,
        off: usize,
        n: usize,
        s: Ghost<Seq<SpecRecord>>,
    ) -> (r: (Ghost<Seq<int>>, Ghost<Seq<SpecName>>))
        requires
            records_at(self.arena@, self.entries@, off as int, s@),
            forall|i: int| 0 <= i < s@.len() ==> valid_record(#[trigger] s@[i]),
            n == s@.len(),
            dict_ok(old(out)@, self.arena@, old(dict)@, g@),
        ensures
            rs_at(final(out)@, r.0@, s@),
            r.0@[0] == old(out)@.len(),
            r.0@[n as int] == final(out)@.len(),
            is_prefix(old(out)@, final(out)@),
            dict_ok(final(out)@, self.arena@, final(dict)@, r.1@),
    {
        let _ = self.entries.len();
        let mut i: usize = 0;
        let ghost mut ps: Seq<int> = seq![old(out)@.len() as int];
        let ghost mut g2 = g@;
        proof {
            assert(s@.take(0) =~= Seq::<SpecRecord>::empty());
            lemma_prefix_refl(out@);
        }
        while i < n
            invariant
                i <= n,
                n == s@.len(),
                off + n <= self.entries@.len(),
                self.entries@.len() <= usize::MAX,
                forall|i: int| 0 <= i < s@.len() ==> valid_record(#[trigger] s@[i]),
                records_at(self.arena@, self.entries@, off as int, s@),
                rs_at(out@, ps, s@.take(i as int)),
                ps[0] == old(out)@.len(),
                ps[i as int] == out@.len(),
                is_prefix(old(out)@, out@),
                dict_ok(out@, self.arena@, dict@, g2),
            decreases n - i,
        {
            let e = self.entries[off + i];
            let ghost r = s@[i as int];
            proof {
                assert(valid_record(r));
                assert(record_ok(self.arena@, self.entries@[off + i], r));
                assert(s@.take(i + 1) =~= s@.take(i as int).push(r));
            }
            let ghost before = out@;
            let gn = write_record(out, dict, Ghost(g2), self.arena.as_slice(), e, Ghost(r));
            proof {
                lemma_rs_push(before, out@, ps, s@.take(i as int), r);
                lemma_prefix_trans(old(out)@, before, out@);
                ps = ps.push(out@.len() as int);
                g2 = gn@;
            }
            i = i + 1;
        }
        proof {
            assert(s@.take(n as int) =~= s@);
        }
        (Ghost(ps), Ghost(g2))
    }

    /// The message's wire form with name compression (RFC 1035 §4.1.4):
    /// every owner and question name, and the names inside NS, CNAME, SOA,
    /// PTR and MX RDATA (the types RFC 3597 §4 allows to be compressed),
    /// becomes its leading labels plus a pointer to an earlier occurrence
    /// of the rest, wherever one exists in the first 16 KiB. It always
    /// parses back to exactly this message.
    #[verifier::spinoff_prover]
    pub fn to_bytes_compressed(&self) -> (out: Vec<u8>)
        ensures
            parse_message(out@) == Some(self@),
    {
        proof {
            use_type_invariant(self);
        }
        let ghost m = self.spec@;
        // Room for the whole message, which the arena's size bounds in practice.
        let cap = if self.arena.len() < 65536 { self.arena.len() + 64 } else { 65536 };
        let mut out: Vec<u8> = Vec::with_capacity(cap);
        let ar = self.entries.len() - self.qd - self.an - self.ns;
        write_u16(&mut out, self.id);
        write_u16(&mut out, self.flags);
        write_u16(&mut out, self.qd as u16);
        write_u16(&mut out, self.an as u16);
        write_u16(&mut out, self.ns as u16);
        write_u16(&mut out, ar as u16);
        proof {
            assert(out@ =~= ser_header(m));
        }
        let ghost h = out@;
        let mut dict = Dict::new();
        let ghost mut g: Seq<SpecName> = Seq::empty();
        let ghost mut qps: Seq<int> = seq![12int];
        let mut i: usize = 0;
        proof {
            assert(m.questions.take(0) =~= Seq::<SpecQuestion>::empty());
            lemma_prefix_refl(h);
        }
        while i < self.qd
            invariant
                i <= self.qd,
                self.wf(),
                m == self.spec@,
                h == ser_header(m),
                h.len() == 12,
                is_prefix(h, out@),
                qs_at(out@, qps, m.questions.take(i as int)),
                qps[0] == 12,
                qps[i as int] == out@.len(),
                dict_ok(out@, self.arena@, dict@, g),
            decreases self.qd - i,
        {
            let e = self.entries[i];
            let ghost q = m.questions[i as int];
            proof {
                assert(question_ok(self.arena@, self.entries@[0 + i], q));
                assert(valid_question(q));
                assert(m.questions.take(i + 1) =~= m.questions.take(i as int).push(q));
            }
            let ghost before = out@;
            let gn = write_question(&mut out, &mut dict, Ghost(g), self.arena.as_slice(), e, Ghost(q));
            proof {
                lemma_qs_push(before, out@, qps, m.questions.take(i as int), q);
                lemma_prefix_trans(h, before, out@);
                qps = qps.push(out@.len() as int);
                g = gn@;
            }
            i = i + 1;
        }
        proof {
            assert(m.questions.take(self.qd as int) =~= m.questions);
        }
        let ghost o1 = out@;
        let (ps1, g1) = self.write_section_compressed(&mut out, &mut dict, Ghost(g), self.qd, self.an, Ghost(m.answers));
        let ghost o2 = out@;
        let (ps2, g2) = self.write_section_compressed(&mut out, &mut dict, g1, self.qd + self.an, self.ns, Ghost(m.authorities));
        let ghost o3 = out@;
        let (ps3, _g3) = self.write_section_compressed(&mut out, &mut dict, g2, self.qd + self.an + self.ns, ar, Ghost(m.additionals));
        proof {
            let b = out@;
            lemma_prefix_trans(o2, o3, b);
            lemma_prefix_trans(o1, o2, b);
            lemma_prefix_trans(h, o1, b);
            lemma_qs_ext(o1, b, qps, m.questions);
            lemma_rs_ext(o2, b, ps1@, m.answers);
            lemma_rs_ext(o3, b, ps2@, m.authorities);
            lemma_message_assembled(b, m, h, qps, ps1@, ps2@, ps3@);
        }
        out
    }

    /// The message's wire form (uncompressed). It always parses back to
    /// exactly this message.
    pub fn to_bytes(&self) -> (out: Vec<u8>)
        ensures
            out@ == ser_message(self@),
            parse_message(out@) == Some(self@),
    {
        hide(parse_message);
        hide(ser_message);
        proof {
            use_type_invariant(self);
            theorem_roundtrip(self@);
        }
        let mut out = Vec::with_capacity(self.arena.len());
        self.write_to(&mut out);
        proof {
            assert(out@ =~= Seq::empty() + ser_message(self@));
        }
        out
    }

    // -----------------------------------------------------------------------
    // Building
    // -----------------------------------------------------------------------

    /// Appends a name's bytes to the arena after checking it is a valid
    /// uncompressed wire-form name; on failure the arena is unchanged.
    fn push_name(arena: &mut Vec<u8>, name: &[u8]) -> (r: Option<Span>)
        ensures
            r matches Some(sp) ==> (wire_name(name@) matches Some(n) && valid_name(n) && is_prefix(
                old(arena)@,
                final(arena)@,
            ) && span_ok(final(arena)@, sp, ser_name(n))),
            r is None ==> wire_name(name@) is None && final(arena)@ == old(arena)@,
    {
        let start = arena.len();
        match read_name_into(name, 0, arena) {
            Some((end, n)) => {
                if end != name.len() {
                    arena.truncate(start);
                    proof {
                        assert(arena@ =~= old(arena)@);
                    }
                    return None;
                }
                proof {
                    lemma_parse_name_valid(name@, 0);
                    lemma_prefix_append(old(arena)@, ser_name(n@));
                    assert(arena@.subrange(start as int, arena@.len() as int) =~= ser_name(n@));
                }
                Some(Span { start, len: arena.len() - start })
            },
            None => {
                arena.truncate(start);
                proof {
                    assert(arena@ =~= old(arena)@);
                }
                None
            },
        }
    }

    /// Adds a question. `name` is an uncompressed wire-form name, such as
    /// `b"\x07example\x03com\x00"`.
    pub fn add_question(&mut self, name: &[u8], qtype: u16, qclass: u16) -> (r: Result<
        (),
        BuildError,
    >)
        ensures
            r is Ok <==> wire_name(name@) is Some && old(self)@.questions.len() < 65535,
            r is Ok ==> final(self)@ == (SpecMessage {
                questions: old(self)@.questions.push(
                    SpecQuestion { qname: wire_name(name@).unwrap(), qtype, qclass },
                ),
                ..old(self)@
            }),
            r is Err ==> final(self)@ == old(self)@,
    {
        proof {
            use_type_invariant(&*self);
        }
        if self.qd >= 65535 {
            return Err(BuildError::SectionFull);
        }
        let mut taken = Message::new(0, 0);
        core::mem::swap(self, &mut taken);
        let Message { id, flags, mut arena, mut entries, qd, an, ns, wire, spec } = taken;
        let ghost a0 = arena@;
        let sp = match Message::push_name(&mut arena, name) {
            Some(sp) => sp,
            None => {
                *self = Message { id, flags, arena, entries, qd, an, ns, wire, spec };
                return Err(BuildError::BadName);
            },
        };
        let ghost q = SpecQuestion { qname: wire_name(name@).unwrap(), qtype, qclass };
        let e = Entry { name: sp, rtype: qtype, rclass: qclass, ttl: 0, rdata: Span { start: 0, len: 0 } };
        let ghost e0 = entries@;
        let ghost m = spec@;
        proof {
            lemma_prefix_refl(e0);
            lemma_questions_at_grow(a0, arena@, e0, e0, 0, m.questions);
            lemma_records_at_grow(a0, arena@, e0, e0, qd as int, m.answers);
            lemma_records_at_grow(a0, arena@, e0, e0, qd + an, m.authorities);
            lemma_records_at_grow(a0, arena@, e0, e0, qd + an + ns, m.additionals);
        }
        entries.insert(qd, e);
        let ghost m2 = SpecMessage { questions: m.questions.push(q), ..m };
        proof {
            let w = entries@;
            lemma_insert_shift_q(arena@, e0, qd as int, e, m.questions);
            assert forall|k: int| 0 <= k < m2.questions.len() implies question_ok(
                arena@,
                #[trigger] w[0 + k],
                m2.questions[k],
            ) by {
                if k < m.questions.len() {
                    assert(question_ok(arena@, w[0 + k], m.questions[k]));
                }
            }
            lemma_insert_shift(arena@, e0, qd as int, e, qd as int, m.answers);
            lemma_insert_shift(arena@, e0, qd as int, e, qd + an, m.authorities);
            lemma_insert_shift(arena@, e0, qd as int, e, qd + an + ns, m.additionals);
            assert forall|i: int| 0 <= i < m2.questions.len() implies valid_question(
                #[trigger] m2.questions[i],
            ) by {
                if i < m.questions.len() {
                    assert(valid_question(m.questions[i]));
                }
            }
        }
        *self = Message { id, flags, arena, entries, qd: qd + 1, an, ns, wire, spec: Ghost(m2) };
        Ok(())
    }

    /// Adds a record to section `s`. `name` is an uncompressed wire-form
    /// name.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    pub fn add_record(
        &mut self,
        s: Section,
        name: &[u8],
        rtype: u16,
        rclass: u16,
        ttl: u32,
        rdata: &[u8],
    ) -> (r: Result<(), BuildError>)
        ensures
            r is Ok <==> wire_name(name@) is Some && section_of(old(self)@, s).len() < 65535
                && rdata@.len() <= 65535 && canon_rdata(rdata@, rtype, 0, rdata@.len() as int) is Some,
            r is Ok ==> {
                let rec = SpecRecord {
                    name: wire_name(name@).unwrap(),
                    rtype,
                    rclass,
                    ttl,
                    rdata: canon_rdata(rdata@, rtype, 0, rdata@.len() as int).unwrap(),
                };
                final(self)@ == match s {
                    Section::Answer => SpecMessage {
                        answers: old(self)@.answers.push(rec),
                        ..old(self)@
                    },
                    Section::Authority => SpecMessage {
                        authorities: old(self)@.authorities.push(rec),
                        ..old(self)@
                    },
                    Section::Additional => SpecMessage {
                        additionals: old(self)@.additionals.push(rec),
                        ..old(self)@
                    },
                }
            },
            r is Err ==> final(self)@ == old(self)@,
    {
        proof {
            use_type_invariant(&*self);
        }
        let count = self.record_count(s);
        if count >= 65535 {
            return Err(BuildError::SectionFull);
        }
        if rdata.len() > 65535 {
            return Err(BuildError::RdataTooLong);
        }
        let mut canon: Vec<u8> = Vec::new();
        if !canon_into(rdata, rtype, 0, rdata.len(), &mut canon) {
            return Err(BuildError::BadRdata);
        }
        if canon.len() > 65535 {
            return Err(BuildError::RdataTooLong);
        }
        let ghost c = canon@;
        proof {
            assert(canon_rdata(rdata@, rtype, 0, rdata@.len() as int) == Some(c)) by {
                assert(canon@ =~= Seq::<u8>::empty() + c);
            }
            lemma_canon_rdata_idem(rdata@, rtype, 0, rdata@.len() as int);
        }
        let mut taken = Message::new(0, 0);
        core::mem::swap(self, &mut taken);
        let Message { id, flags, mut arena, mut entries, qd, an, ns, wire, spec } = taken;
        let ghost a0 = arena@;
        let sp = match Message::push_name(&mut arena, name) {
            Some(sp) => sp,
            None => {
                *self = Message { id, flags, arena, entries, qd, an, ns, wire, spec };
                return Err(BuildError::BadName);
            },
        };
        let ghost a1 = arena@;
        let rstart = arena.len();
        append(&mut arena, canon.as_slice());
        let _alen = arena.len();
        let rsp = Span { start: rstart, len: canon.len() };
        let ghost rec = SpecRecord { name: wire_name(name@).unwrap(), rtype, rclass, ttl, rdata: c };
        let e = Entry { name: sp, rtype, rclass, ttl, rdata: rsp };
        let ghost e0 = entries@;
        let ghost m = spec@;
        proof {
            lemma_prefix_append(a1, c);
            lemma_prefix_trans(a0, a1, arena@);
            lemma_span_ok_grow(a1, arena@, sp, ser_name(rec.name));
            assert(arena@.subrange(rstart as int, rstart + c.len()) =~= c);
            assert(record_ok(arena@, e, rec));
            lemma_prefix_refl(e0);
            lemma_questions_at_grow(a0, arena@, e0, e0, 0, m.questions);
            lemma_records_at_grow(a0, arena@, e0, e0, qd as int, m.answers);
            lemma_records_at_grow(a0, arena@, e0, e0, qd + an, m.authorities);
            lemma_records_at_grow(a0, arena@, e0, e0, qd + an + ns, m.additionals);
        }
        let at = match s {
            Section::Answer => qd + an,
            Section::Authority => qd + an + ns,
            Section::Additional => entries.len(),
        };
        entries.insert(at, e);
        let ghost m2 = match s {
            Section::Answer => SpecMessage { answers: m.answers.push(rec), ..m },
            Section::Authority => SpecMessage { authorities: m.authorities.push(rec), ..m },
            Section::Additional => SpecMessage { additionals: m.additionals.push(rec), ..m },
        };
        proof {
            let w = entries@;
            lemma_insert_shift_q(arena@, e0, at as int, e, m.questions);
            lemma_insert_shift(arena@, e0, at as int, e, qd as int, m.answers);
            lemma_insert_shift(arena@, e0, at as int, e, qd + an, m.authorities);
            lemma_insert_shift(arena@, e0, at as int, e, qd + an + ns, m.additionals);
            let sec = section_of(m, s);
            let sec2 = sec.push(rec);
            let off: int = match s {
                Section::Answer => qd as int,
                Section::Authority => qd + an,
                Section::Additional => qd + an + ns,
            };
            assert(at == off + sec.len());
            assert forall|k: int| 0 <= k < sec2.len() implies record_ok(
                arena@,
                #[trigger] w[off + k],
                sec2[k],
            ) by {
                if k < sec.len() {
                    assert(record_ok(arena@, w[off + k], sec[k]));
                }
            }
            assert forall|i: int| 0 <= i < sec2.len() implies valid_record(#[trigger] sec2[i]) by {
                if i < sec.len() {
                    assert(valid_record(sec[i]));
                }
            }
            assert(section_of(m2, s) == sec2);
        }
        let (an2, ns2) = match s {
            Section::Answer => (an + 1, ns),
            Section::Authority => (an, ns + 1),
            Section::Additional => (an, ns),
        };
        *self = Message { id, flags, arena, entries, qd, an: an2, ns: ns2, wire, spec: Ghost(m2) };
        Ok(())
    }
}

/// A header followed by the sections, each written where the last ended.
proof fn lemma_message_assembled(
    b: Seq<u8>,
    m: SpecMessage,
    h: Seq<u8>,
    qps: Seq<int>,
    ps1: Seq<int>,
    ps2: Seq<int>,
    ps3: Seq<int>,
)
    requires
        valid_message(m),
        h == ser_header(m),
        is_prefix(h, b),
        qs_at(b, qps, m.questions),
        rs_at(b, ps1, m.answers),
        rs_at(b, ps2, m.authorities),
        rs_at(b, ps3, m.additionals),
        qps[0] == 12,
        qps[m.questions.len() as int] == ps1[0],
        ps1[m.answers.len() as int] == ps2[0],
        ps2[m.authorities.len() as int] == ps3[0],
        ps3[m.additionals.len() as int] == b.len(),
    ensures
        parse_message(b) == Some(m),
{
    hide(parse_questions);
    hide(parse_records);
    lemma_header_at(h, b, m);
    lemma_qs_parse(b, qps, m.questions);
    lemma_rs_parse(b, ps1, m.answers);
    lemma_rs_parse(b, ps2, m.authorities);
    lemma_rs_parse(b, ps3, m.additionals);
}

/// The header, written first, still parses once more is appended.
proof fn lemma_header_at(h: Seq<u8>, b: Seq<u8>, m: SpecMessage)
    requires
        h == ser_header(m),
        is_prefix(h, b),
    ensures
        parse_u16(b, 0) == Some((m.id, 2int)),
        parse_u16(b, 2) == Some((m.flags, 4int)),
        parse_u16(b, 4) == Some((m.questions.len() as u16, 6int)),
        parse_u16(b, 6) == Some((m.answers.len() as u16, 8int)),
        parse_u16(b, 8) == Some((m.authorities.len() as u16, 10int)),
        parse_u16(b, 10) == Some((m.additionals.len() as u16, 12int)),
        b.len() >= 12,
{
    lemma_at_whole(h);
    assert(at(b, 0, h)) by {
        assert(b.subrange(0, h.len() as int) == h);
    }
    lemma_header_roundtrip(b, m);
}

fn write_u16(out: &mut Vec<u8>, x: u16)
    ensures
        final(out)@ == old(out)@ + ser_u16(x),
{
    out.push((x / 256) as u8);
    out.push((x % 256) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + ser_u16(x));
    }
}

fn write_u32(out: &mut Vec<u8>, x: u32)
    ensures
        final(out)@ == old(out)@ + ser_u32(x),
{
    out.push((x / 0x100_0000) as u8);
    out.push(((x / 0x1_0000) % 256) as u8);
    out.push(((x / 256) % 256) as u8);
    out.push((x % 256) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + ser_u32(x));
    }
}

} // verus!

impl core::fmt::Display for BuildError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            BuildError::BadName => "not a valid domain name",
            BuildError::SectionFull => "the section already holds 65535 entries",
            BuildError::RdataTooLong => "RDATA is longer than 65535 bytes",
            BuildError::BadRdata => "RDATA does not decode as its type",
        })
    }
}

impl core::error::Error for BuildError {}
